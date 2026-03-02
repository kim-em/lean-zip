import Zip.Binary
import Zip.Native.XxHash

/-!
  Pure Lean parser and decompressor for Zstandard frames (RFC 8878 §3.1.1).

  Parses the fixed-format header at the start of every Zstd frame:
  magic number, frame header descriptor (bit fields), optional window
  descriptor, optional dictionary ID, and optional frame content size.
  Also parses the block-level structure within a frame: 3-byte block
  headers (Last_Block, Block_Type, Block_Size) and decompresses Raw
  (verbatim copy) and RLE (single byte repeated) blocks.

  Provides frame-level decompression (`decompressFrame`) that wires
  header parsing + block decompression together, and a top-level API
  (`decompressZstd`) that handles multi-frame concatenation and
  skippable frames (RFC 8878 §3.1.2).  Content checksum verification
  uses XXH64 (upper 32 bits).  Compressed blocks (FSE + Huffman)
  are not yet supported.
-/

namespace Zip.Native

/-- Parsed Zstandard frame header. -/
structure ZstdFrameHeader where
  /-- Whether the frame includes a 32-bit content checksum at the end. -/
  contentChecksum : Bool
  /-- Whether the window descriptor is absent (content fits in one segment). -/
  singleSegment : Bool
  /-- Optional dictionary ID used for compression. -/
  dictionaryId : Option UInt32
  /-- Optional uncompressed content size in bytes. -/
  contentSize : Option UInt64
  /-- Window size in bytes (from window descriptor, or content size if single segment). -/
  windowSize : UInt64
  deriving Repr

/-- Zstd magic number: 0xFD2FB528 (little-endian). -/
def zstdMagic : UInt32 := 0xFD2FB528

/-- Compute window size from a Zstd window descriptor byte (RFC 8878 §3.1.1.1.2). -/
def windowSizeFromDescriptor (winDesc : UInt8) : UInt64 :=
  let exponent := (winDesc >>> 3).toNat   -- bits 7-3
  let mantissa := (winDesc &&& 7).toNat   -- bits 2-0
  let windowLog := 10 + exponent
  let windowBase : UInt64 := 1 <<< windowLog.toUInt64
  let windowAdd := (windowBase / 8) * mantissa.toUInt64
  windowBase + windowAdd

/-- Parse a Zstandard frame header starting at `pos` in `data`.
    Returns the parsed header and the position immediately after the header.
    Fails with a descriptive error message if the data is malformed or too short. -/
def parseFrameHeader (data : ByteArray) (pos : Nat) :
    Except String (ZstdFrameHeader × Nat) := do
  -- Magic number (4 bytes)
  if data.size < pos + 4 then
    throw "Zstd: not enough data for magic number"
  let magic := Binary.readUInt32LE data pos
  if magic != zstdMagic then
    throw s!"Zstd: invalid magic number 0x{String.ofList (Nat.toDigits 16 magic.toNat)} (expected 0xFD2FB528)"
  let mut off := pos + 4

  -- Frame_Header_Descriptor (1 byte)
  if data.size < off + 1 then
    throw "Zstd: not enough data for frame header descriptor"
  let desc := data[off]!
  off := off + 1

  let fcsFlag := (desc >>> 6).toNat       -- bits 7-6: Frame_Content_Size_Flag
  let singleSegment := (desc >>> 5) &&& 1 == 1  -- bit 5
  let contentChecksum := (desc >>> 2) &&& 1 == 1 -- bit 2
  let didFlag := (desc &&& 3).toNat       -- bits 1-0: Dictionary_ID_Flag

  -- Window_Descriptor (1 byte, absent if Single_Segment_Flag is set)
  let mut windowSize : UInt64 := 0
  if !singleSegment then
    if data.size < off + 1 then
      throw "Zstd: not enough data for window descriptor"
    windowSize := windowSizeFromDescriptor data[off]!
    off := off + 1

  -- Dictionary_ID (0/1/2/4 bytes)
  let didSize := match didFlag with
    | 1 => 1
    | 2 => 2
    | 3 => 4
    | _ => 0
  if data.size < off + didSize then
    throw "Zstd: not enough data for dictionary ID"
  let dictionaryId : Option UInt32 :=
    match didSize with
    | 1 => some data[off]!.toUInt32
    | 2 => some (Binary.readUInt16LE data off).toUInt32
    | 4 => some (Binary.readUInt32LE data off)
    | _ => none
  off := off + didSize

  -- Frame_Content_Size (0/1/2/4/8 bytes)
  let fcsSize := match fcsFlag with
    | 0 => if singleSegment then 1 else 0
    | 1 => 2
    | 2 => 4
    | _ => 8  -- fcsFlag == 3
  if data.size < off + fcsSize then
    throw "Zstd: not enough data for frame content size"
  let contentSize : Option UInt64 :=
    match fcsSize with
    | 1 => some data[off]!.toUInt64
    | 2 =>
      -- 2-byte FCS has a +256 offset (RFC 8878 §3.1.1.4)
      some ((Binary.readUInt16LE data off).toUInt64 + 256)
    | 4 => some (Binary.readUInt32LE data off).toUInt64
    | 8 => some (Binary.readUInt64LE data off)
    | _ => none
  off := off + fcsSize

  -- If single segment, window size equals content size
  if singleSegment then
    windowSize := contentSize.getD 0

  return ({
    contentChecksum
    singleSegment
    dictionaryId
    contentSize
    windowSize
  }, off)

/-- Zstd block type (RFC 8878 §3.1.1.2): bits 1-2 of the 3-byte block header. -/
inductive ZstdBlockType where
  | raw        -- 0: uncompressed, copied verbatim
  | rle        -- 1: single byte repeated Block_Size times
  | compressed -- 2: Zstd-compressed data (FSE + Huffman)
  | reserved   -- 3: not allowed
  deriving Repr, BEq

/-- Parsed Zstd block header (3 bytes, RFC 8878 §3.1.1.2). -/
structure ZstdBlockHeader where
  /-- True if this is the last block in the frame. -/
  lastBlock : Bool
  /-- Block type: raw, rle, compressed, or reserved. -/
  blockType : ZstdBlockType
  /-- Block content size in bytes (21-bit value). -/
  blockSize : UInt32
  deriving Repr

/-- Parse a 3-byte Zstd block header at `pos`.
    Returns the parsed header and the position after the 3 header bytes. -/
def parseBlockHeader (data : ByteArray) (pos : Nat) :
    Except String (ZstdBlockHeader × Nat) := do
  if data.size < pos + 3 then
    throw "Zstd: not enough data for block header"
  -- Read 3 bytes as little-endian 24-bit value
  let b0 := data[pos]!.toUInt32
  let b1 := data[pos + 1]!.toUInt32
  let b2 := data[pos + 2]!.toUInt32
  let raw24 := b0 ||| (b1 <<< 8) ||| (b2 <<< 16)
  let lastBlock := raw24 &&& 1 == 1       -- bit 0
  let typeVal := (raw24 >>> 1) &&& 3      -- bits 1-2
  let blockSize := raw24 >>> 3            -- bits 3-23
  let blockType ← match typeVal with
    | 0 => pure ZstdBlockType.raw
    | 1 => pure ZstdBlockType.rle
    | 2 => pure ZstdBlockType.compressed
    | _ => throw "Zstd: reserved block type"
  return ({ lastBlock, blockType, blockSize }, pos + 3)

/-- Decompress a raw (verbatim) block: copy `blockSize` bytes from `pos`.
    Returns the copied bytes and the position after the block content. -/
def decompressRawBlock (data : ByteArray) (pos : Nat) (blockSize : UInt32) :
    Except String (ByteArray × Nat) := do
  let sz := blockSize.toNat
  if data.size < pos + sz then
    throw "Zstd: not enough data for raw block"
  return (data.extract pos (pos + sz), pos + sz)

/-- Decompress an RLE block: read 1 byte and repeat it `blockSize` times.
    Returns the repeated bytes and the position after the single source byte. -/
def decompressRLEBlock (data : ByteArray) (pos : Nat) (blockSize : UInt32) :
    Except String (ByteArray × Nat) := do
  if data.size < pos + 1 then
    throw "Zstd: not enough data for RLE block"
  let byte := data[pos]!
  let sz := blockSize.toNat
  let mut result := ByteArray.empty
  for _ in [:sz] do
    result := result.push byte
  return (result, pos + 1)

/-- Parse the Literals_Section_Header and extract literal bytes (RFC 8878 §3.1.1.3.1).
    Returns the literal bytes and the position after the literals section.
    Raw literals are copied verbatim; RLE literals are expanded to `regeneratedSize` copies
    of a single byte. Compressed and treeless literals return an error (not yet implemented). -/
def parseLiteralsSection (data : ByteArray) (pos : Nat) :
    Except String (ByteArray × Nat) := do
  if data.size < pos + 1 then
    throw "Zstd: not enough data for literals section header"
  let byte0 := data[pos]!
  let litType := (byte0 &&& 3).toNat       -- bits 0-1: Literals_Block_Type
  let sizeFormat := ((byte0 >>> 2) &&& 3).toNat  -- bits 2-3: Size_Format
  -- Compressed and treeless literals require Huffman infrastructure
  if litType == 2 then throw "Zstd: compressed literals not yet supported"
  if litType == 3 then throw "Zstd: treeless literals not yet supported"
  if litType > 3 then throw "Zstd: invalid literals block type"
  -- Raw (0) or RLE (1): parse regenerated size using variable-width header
  let (regenSize, headerBytes) ←
    if sizeFormat == 0 || sizeFormat == 2 then
      -- 1-byte header, 5-bit size (bits 3-7 of byte0)
      pure ((byte0 >>> 3).toNat, 1)
    else if sizeFormat == 1 then
      -- 2-byte header, 12-bit size (bits 4-7 of byte0 + all of byte1)
      if data.size < pos + 2 then throw "Zstd: truncated literals section header"
      let byte1 := data[pos + 1]!
      pure ((byte0 >>> 4).toNat ||| (byte1.toNat <<< 4), 2)
    else
      -- 3-byte header, 20-bit size (bits 4-7 of byte0 + byte1 + byte2)
      if data.size < pos + 3 then throw "Zstd: truncated literals section header"
      let byte1 := data[pos + 1]!
      let byte2 := data[pos + 2]!
      pure ((byte0 >>> 4).toNat ||| (byte1.toNat <<< 4) ||| (byte2.toNat <<< 12), 3)
  let afterHeader := pos + headerBytes
  if litType == 0 then
    -- Raw literals: copy regeneratedSize bytes verbatim
    if data.size < afterHeader + regenSize then
      throw "Zstd: not enough data for raw literals"
    pure (data.extract afterHeader (afterHeader + regenSize), afterHeader + regenSize)
  else
    -- RLE literals: read 1 byte, replicate regeneratedSize times
    if data.size < afterHeader + 1 then
      throw "Zstd: not enough data for RLE literal byte"
    let byte := data[afterHeader]!
    let result := ByteArray.mk (Array.replicate regenSize byte)
    pure (result, afterHeader + 1)

/-- Parse the Sequences_Section header (RFC 8878 §3.1.1.3.2).
    Returns (numberOfSequences, position after header including compression modes byte).
    If numberOfSequences is 0, the block has only literals (no sequences to decode). -/
def parseSequencesHeader (data : ByteArray) (pos : Nat) :
    Except String (Nat × Nat) := do
  if data.size < pos + 1 then
    throw "Zstd: not enough data for sequences header"
  let byte0 := data[pos]!.toNat
  if byte0 == 0 then
    -- 0 sequences: no compression modes byte follows
    pure (0, pos + 1)
  else if byte0 < 128 then
    -- 1-byte count + compression modes byte
    if data.size < pos + 2 then
      throw "Zstd: not enough data for sequence compression modes"
    pure (byte0, pos + 2)
  else if byte0 < 255 then
    -- 2-byte count: ((byte0 - 128) << 8) + byte1, then compression modes
    if data.size < pos + 3 then
      throw "Zstd: truncated sequences header"
    let byte1 := data[pos + 1]!.toNat
    let numSeq := ((byte0 - 128) <<< 8) + byte1
    pure (numSeq, pos + 3)
  else
    -- 3-byte count (byte0 == 255): byte1 + (byte2 << 8) + 0x7F00, then compression modes
    if data.size < pos + 4 then
      throw "Zstd: truncated sequences header"
    let byte1 := data[pos + 1]!.toNat
    let byte2 := data[pos + 2]!.toNat
    let numSeq := byte1 + (byte2 <<< 8) + 0x7F00
    pure (numSeq, pos + 4)

/-- Decompress all blocks in a Zstd frame starting at `pos` (after the frame header).
    Loops through block headers, dispatches on block type, and accumulates output.
    Returns the decompressed content and position after the last block.
    Currently returns an error for compressed blocks (not yet implemented). -/
def decompressBlocks (data : ByteArray) (pos : Nat) : Except String (ByteArray × Nat) := do
  let mut off := pos
  let mut output := ByteArray.empty
  let mut done := false
  while !done do
    let (hdr, afterHdr) ← parseBlockHeader data off
    off := afterHdr
    match hdr.blockType with
    | .raw =>
      let (block, afterBlock) ← decompressRawBlock data off hdr.blockSize
      output := output ++ block
      off := afterBlock
    | .rle =>
      let (block, afterByte) ← decompressRLEBlock data off hdr.blockSize
      output := output ++ block
      off := afterByte
    | .compressed =>
      let blockEnd := off + hdr.blockSize.toNat
      let (literals, afterLiterals) ← parseLiteralsSection data off
      let (numSeq, _afterSeqHeader) ← parseSequencesHeader data afterLiterals
      if numSeq == 0 then
        -- No sequences: block is pure literals
        output := output ++ literals
        off := blockEnd
      else
        throw s!"Zstd: sequence decoding not yet implemented ({numSeq} sequences)"
    | .reserved =>
      throw "Zstd: reserved block type"
    if hdr.lastBlock then
      done := true
  return (output, off)

/-- Decompress a single Zstd frame starting at `pos` in `data`.
    Parses the frame header, decompresses all blocks, verifies the optional
    content checksum (upper 32 bits of XXH64 with seed 0), and validates
    content size if specified in the header.
    Returns decompressed data and position after the frame. -/
def decompressFrame (data : ByteArray) (pos : Nat) :
    Except String (ByteArray × Nat) := do
  let (header, afterHeader) ← parseFrameHeader data pos
  let (content, afterBlocks) ← decompressBlocks data afterHeader
  -- Content checksum: upper 32 bits of XXH64 (RFC 8878 §3.1.1) if flagged
  let afterFrame := if header.contentChecksum then afterBlocks + 4 else afterBlocks
  if header.contentChecksum then
    if data.size < afterFrame then
      throw "Zstd: not enough data for content checksum"
    let expected := Binary.readUInt32LE data afterBlocks
    let actual := XxHash64.xxHash64Upper32 content
    if expected != actual then
      throw s!"Zstd: content checksum mismatch: expected 0x{String.ofList (Nat.toDigits 16 expected.toNat)}, got 0x{String.ofList (Nat.toDigits 16 actual.toNat)}"
  -- Validate content size if specified in the header
  if let some expectedSize := header.contentSize then
    if content.size.toUInt64 != expectedSize then
      throw s!"Zstd: content size mismatch: expected {expectedSize}, got {content.size}"
  return (content, afterFrame)

/-- Skip a skippable frame (RFC 8878 §3.1.2) starting at `pos` in `data`.
    Validates that the magic number is in the range 0x184D2A50–0x184D2A5F,
    reads the 4-byte little-endian frame size, and returns the position
    immediately after the frame data.  Errors if insufficient data. -/
def skipSkippableFrame (data : ByteArray) (pos : Nat) : Except String Nat := do
  if data.size < pos + 8 then
    throw "Zstd: not enough data for skippable frame header"
  let magic := Binary.readUInt32LE data pos
  if magic < 0x184D2A50 || magic > 0x184D2A5F then
    throw "Zstd: not a skippable frame"
  let frameSize := (Binary.readUInt32LE data (pos + 4)).toNat
  let afterFrame := pos + 8 + frameSize
  if data.size < afterFrame then
    throw "Zstd: not enough data for skippable frame content"
  return afterFrame

/-- Top-level Zstd decompression: loops through concatenated frames in `data`.
    Zstd frames (magic 0xFD2FB528) are decompressed and their output concatenated.
    Skippable frames (magic 0x184D2A50–0x184D2A5F) are silently skipped.
    Any other magic number or trailing bytes after the last frame produce an error.
    An empty file or a file with only skippable frames returns empty ByteArray. -/
def decompressZstd (data : ByteArray) : Except String ByteArray := do
  let mut pos := 0
  let mut output := ByteArray.empty
  while pos < data.size do
    if data.size < pos + 4 then
      throw "Zstd: trailing bytes too short for frame magic"
    let magic := Binary.readUInt32LE data pos
    if magic >= 0x184D2A50 && magic <= 0x184D2A5F then
      pos ← skipSkippableFrame data pos
    else if magic == zstdMagic then
      let (content, afterFrame) ← decompressFrame data pos
      output := output ++ content
      pos := afterFrame
    else
      throw s!"Zstd: invalid magic number 0x{String.ofList (Nat.toDigits 16 magic.toNat)} (expected 0xFD2FB528 or skippable frame)"
  return output

/-- A decoded Zstd sequence triple (RFC 8878 §3.1.1.4): copy `literalLength` bytes
    from the literals buffer, then copy `matchLength` bytes from `offset` bytes back
    in the already-produced output. -/
structure ZstdSequence where
  /-- Number of literal bytes to copy from the literals buffer before the match. -/
  literalLength : Nat
  /-- Number of bytes to copy from the back-reference in the output. -/
  matchLength : Nat
  /-- Raw offset value (1-3 are repeat offset codes; ≥4 is actual offset minus 3). -/
  offset : Nat
  deriving Repr

/-- Resolve a raw offset value against the 3-entry offset history (RFC 8878 §3.1.1.5).
    Returns the actual byte offset and the updated offset history.
    - Offset values 1, 2, 3 are repeat offset codes (refer to history entries).
    - When `literalLength == 0`, repeat codes are shifted: 1→history[1], 2→history[2],
      3→history[0] - 1.
    - Offset values ≥ 4 are actual offsets (value - 3).
    The history array must have exactly 3 entries. -/
def resolveOffset (rawOffset : Nat) (history : Array Nat) (literalLength : Nat) :
    Nat × Array Nat :=
  if rawOffset > 3 then
    -- Actual offset (subtract 3 to get the real byte offset)
    let offset := rawOffset - 3
    let history' := #[offset, history[0]!, history[1]!]
    (offset, history')
  else if literalLength > 0 then
    -- Normal repeat offset mode
    match rawOffset with
    | 1 =>
      let offset := history[0]!
      (offset, history)  -- history unchanged for code 1
    | 2 =>
      let offset := history[1]!
      let history' := #[offset, history[0]!, history[2]!]
      (offset, history')
    | 3 =>
      let offset := history[2]!
      let history' := #[offset, history[0]!, history[1]!]
      (offset, history')
    | _ => (1, history)  -- unreachable (rawOffset > 0 implied)
  else
    -- Shifted repeat mode when literalLength == 0
    match rawOffset with
    | 1 =>
      let offset := history[1]!
      let history' := #[offset, history[0]!, history[2]!]
      (offset, history')
    | 2 =>
      let offset := history[2]!
      let history' := #[offset, history[0]!, history[1]!]
      (offset, history')
    | 3 =>
      let offset := history[0]! - 1
      let history' := #[offset, history[1]!, history[2]!]
      (offset, history')
    | _ => (1, history)  -- unreachable

/-- Copy `length` bytes from `offset` bytes back in `buf`, handling overlapping matches
    (byte-by-byte copy so that repeated patterns are expanded correctly). -/
private def copyMatch (buf : ByteArray) (offset length : Nat) : ByteArray :=
  let start := buf.size - offset
  let rec loop (b : ByteArray) (k : Nat) : ByteArray :=
    if k < length then
      loop (b.push b[start + (k % offset)]!) (k + 1)
    else b
  termination_by length - k
  loop buf 0

/-- Execute decoded Zstd sequences against a literals buffer to produce decompressed output
    (RFC 8878 §3.1.1.4). Maintains a 3-entry offset history initialized to `[1, 4, 8]`.
    For each sequence: copies `literalLength` bytes from literals, then copies `matchLength`
    bytes from `offset` back in the output (with overlap semantics). After all sequences,
    any remaining literals are appended. Returns the decompressed block or an error. -/
def executeSequences (sequences : Array ZstdSequence) (literals : ByteArray) :
    Except String ByteArray := do
  let mut output := ByteArray.empty
  let mut history : Array Nat := #[1, 4, 8]
  let mut litPos := 0
  for seq in sequences do
    -- Copy literalLength bytes from literals buffer
    if litPos + seq.literalLength > literals.size then
      throw s!"Zstd: sequence requires {litPos + seq.literalLength} literal bytes but only {literals.size} available"
    for i in [:seq.literalLength] do
      output := output.push literals[litPos + i]!
    litPos := litPos + seq.literalLength
    -- Resolve offset
    let (offset, history') := resolveOffset seq.offset history seq.literalLength
    history := history'
    -- Validate offset
    if offset == 0 then
      throw "Zstd: resolved offset is 0"
    if offset > output.size then
      throw s!"Zstd: match offset {offset} exceeds output size {output.size}"
    -- Copy matchLength bytes from output (with overlap semantics)
    output := copyMatch output offset seq.matchLength
  -- Copy any remaining literals after the last sequence
  if litPos < literals.size then
    for i in [litPos:literals.size] do
      output := output.push literals[i]!
  return output

end Zip.Native
