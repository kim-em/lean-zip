import Zip.Binary
import Zip.Native.Fse
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
  (`decompressZstd`) for single-frame inputs.  Content checksum
  verification uses XXH64 (upper 32 bits).  Compressed blocks
  (FSE + Huffman) are not yet supported.
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

/-- Top-level Zstd decompression: validates the magic number, decompresses a
    single frame, and returns the decompressed data.
    Returns an error for skippable frames or multi-frame inputs. -/
def decompressZstd (data : ByteArray) : Except String ByteArray := do
  if data.size < 4 then
    throw "Zstd: input too short for magic number"
  let magic := Binary.readUInt32LE data 0
  -- Check for skippable frame magic (0x184D2A50 to 0x184D2A5F)
  if magic >= 0x184D2A50 && magic <= 0x184D2A5F then
    throw "Zstd: skippable frames not supported"
  if magic != zstdMagic then
    throw s!"Zstd: invalid magic number 0x{String.ofList (Nat.toDigits 16 magic.toNat)} (expected 0xFD2FB528)"
  let (content, _) ← decompressFrame data 0
  return content

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

/-- A single entry in a Zstd Huffman decoding table. -/
structure HuffmanEntry where
  /-- The symbol this entry decodes to. -/
  symbol : UInt8 := 0
  /-- Number of bits consumed by this symbol's code. -/
  numBits : UInt8 := 0
  deriving Repr, Inhabited

/-- A Zstd Huffman decoding table (flat lookup, RFC 8878 §4.2.1). -/
structure ZstdHuffmanTable where
  /-- Maximum code length (log2 of table size). -/
  maxBits : Nat
  /-- Flat lookup table, size = 1 << maxBits. -/
  table : Array HuffmanEntry
  deriving Repr

/-- Unpack 4-bit Huffman weights from a byte array (direct representation, RFC 8878 §4.2.1).
    Each byte packs two 4-bit weights: high nibble first, low nibble second.
    `numWeightBytes` is the header byte value (< 128), giving the number of weight bytes.
    Returns (weights array, new position after weight bytes). -/
def parseHuffmanWeightsDirect (data : ByteArray) (pos : Nat) (numWeightBytes : Nat) :
    Except String (Array UInt8 × Nat) := do
  if data.size < pos + numWeightBytes then
    throw "Zstd Huffman: not enough data for weight bytes"
  let mut weights : Array UInt8 := #[]
  for i in [:numWeightBytes] do
    let byte := data[pos + i]!
    weights := weights.push (byte >>> 4)       -- high nibble
    weights := weights.push (byte &&& 0x0F)    -- low nibble
  return (weights, pos + numWeightBytes)

/-- Derive maxBits from a Huffman weight array (RFC 8878 §4.2.1.1).
    Finds the smallest M such that the sum of 2^(W-1) for all W > 0 equals 2^M.
    The last symbol's weight is implicit: its 2^(W-1) value = 2^M - sum. -/
def weightsToMaxBits (weights : Array UInt8) : Except String Nat := do
  -- Compute sum of 2^(W-1) for each explicit weight W > 0
  let mut weightSum : Nat := 0
  for w in weights do
    if w.toNat > 0 then
      weightSum := weightSum + (1 <<< (w.toNat - 1))
  if weightSum == 0 then
    throw "Zstd Huffman: all weights are zero"
  -- Find maxBits: smallest M such that 2^M >= weightSum
  -- The sum should be a power of 2 or just below one (the implicit last symbol fills the gap)
  let mut maxBits := 0
  let mut power : Nat := 1
  while power < weightSum do
    maxBits := maxBits + 1
    power := power * 2
  -- After adding the last implicit symbol, the total must equal exactly 2^maxBits
  -- If weightSum is already 2^maxBits, we need maxBits+1 (the last symbol gets weight maxBits+1)
  if weightSum == power then
    maxBits := maxBits + 1
  return maxBits

/-- Build a Zstd Huffman decoding table from a weight array (RFC 8878 §4.2.1).
    Adds the implicit last symbol, converts weights to code lengths, and fills
    a flat lookup table of size 2^maxBits. -/
def buildZstdHuffmanTable (weights : Array UInt8) : Except String ZstdHuffmanTable := do
  let maxBits ← weightsToMaxBits weights
  let targetSum := 1 <<< maxBits
  -- Compute sum of 2^(W-1) for explicit weights
  let mut explicitSum : Nat := 0
  for w in weights do
    if w.toNat > 0 then
      explicitSum := explicitSum + (1 <<< (w.toNat - 1))
  let lastWeight2 := targetSum - explicitSum
  if lastWeight2 == 0 then
    throw "Zstd Huffman: implicit last symbol has zero weight"
  -- Derive the last symbol's weight from its 2^(W-1) value
  let mut lastWeight : Nat := 0
  let mut tmp := lastWeight2
  while tmp > 1 do
    lastWeight := lastWeight + 1
    tmp := tmp / 2
  lastWeight := lastWeight + 1
  -- Verify: 2^(lastWeight-1) should equal lastWeight2
  if (1 <<< (lastWeight - 1)) != lastWeight2 then
    throw s!"Zstd Huffman: implicit last symbol weight is not a power of 2 ({lastWeight2})"
  -- Build complete weight array including the implicit last symbol
  let numSymbols := weights.size + 1
  let lastSymbol := weights.size
  let allWeights := weights.push lastWeight.toUInt8
  -- Build the flat lookup table
  let tableSize := 1 <<< maxBits
  let mut table : Array HuffmanEntry := Array.replicate tableSize default
  -- For each symbol with weight W > 0: numberOfBits = maxBits + 1 - W
  -- Each symbol occupies tableSize / 2^W entries (= 2^(maxBits - W) entries if W < maxBits+1,
  -- but more precisely: numberOfBits = maxBits + 1 - W, and the symbol fills
  -- 1 << (maxBits - numberOfBits) = 1 << (W - 1) entries).
  -- Wait — that's the number of distinct codes for this symbol.
  -- Each code prefix occupies 2^(maxBits - numberOfBits) = 2^(W-1) table entries.
  -- Actually: numberOfBits for symbol = maxBits + 1 - W
  -- Number of table entries per code = 2^(maxBits - numberOfBits) = 2^(W-1)
  -- Number of codes for this symbol = count (we have 1 code per symbol in Huffman)
  -- So each symbol with weight W fills 2^(W-1) table entries.

  -- Assign codes: sort symbols by weight (ascending), then assign sequential codes.
  -- Within each weight group, symbols are in ascending order.
  -- We track the next available code for each weight.
  let mut nextCode : Array Nat := Array.replicate (maxBits + 2) 0
  -- Count symbols per weight
  let mut weightCounts : Array Nat := Array.replicate (maxBits + 2) 0
  for i in [:numSymbols] do
    let w := allWeights[i]!.toNat
    if w > 0 && w < weightCounts.size then
      weightCounts := weightCounts.set! w (weightCounts[w]! + 1)
  -- Compute starting codes for each weight (ascending weight = shorter codes = higher codes)
  -- Symbols with weight 1 have numberOfBits = maxBits, so they occupy 1 entry each.
  -- Symbols with weight maxBits have numberOfBits = 1, so they occupy 2^(maxBits-1) entries each.
  -- Start from weight=1: codes start at 0, each code occupies 2^(W-1) entries.
  let mut pos : Nat := 0
  for w in List.range (maxBits + 1) do
    if w > 0 then
      nextCode := nextCode.set! w pos
      pos := pos + weightCounts[w]! * (1 <<< (w - 1))

  -- Fill the table
  for sym in [:numSymbols] do
    let w := allWeights[sym]!.toNat
    if w == 0 then continue
    let numBits := maxBits + 1 - w
    let code := nextCode[w]!
    nextCode := nextCode.set! w (code + (1 <<< (w - 1)))
    let entry : HuffmanEntry := { symbol := sym.toUInt8, numBits := numBits.toUInt8 }
    -- Fill 2^(W-1) entries starting at `code`
    let stride := 1 <<< (w - 1)
    for j in [:stride] do
      let idx := code + j
      if idx < tableSize then
        table := table.set! idx entry
      else if sym != lastSymbol then
        -- Only error for non-last symbols; last symbol might have rounding issues
        throw s!"Zstd Huffman: table index {idx} out of range (tableSize={tableSize})"

  return { maxBits, table }

/-- Parse FSE-compressed Huffman weights (RFC 8878 §4.2.1).
    Header byte `h >= 128` means the compressed weight data occupies `h - 127` bytes.
    Within those bytes: an FSE distribution (maxAccLog=6), then a backward bitstream
    of FSE-encoded weight symbols.
    Returns (weights array, position after compressed weight data). -/
def parseHuffmanWeightsFse (data : ByteArray) (pos : Nat) (compressedSize : Nat) :
    Except String (Array UInt8 × Nat) := do
  let rangeStart := pos + 1  -- after the header byte
  let rangeEnd := rangeStart + compressedSize
  if data.size < rangeEnd then
    throw "Zstd Huffman: not enough data for FSE-compressed weights"
  -- Create a BitReader over the compressed range to decode the FSE distribution
  let br : BitReader := { data := data, pos := rangeStart, bitOff := 0 }
  let (probs, accuracyLog, br) ← decodeFseDistribution br 256 6
  -- Build the FSE table from the decoded distribution
  let table ← buildFseTable probs accuracyLog
  -- Determine where the FSE distribution encoding ends (align to byte boundary)
  let brAligned := br.alignToByte
  let fseDistEnd := brAligned.pos
  -- Create a BackwardBitReader from the remaining bytes up to the end of the compressed range
  let bbr ← BackwardBitReader.init data fseDistEnd rangeEnd
  -- Decode all weight values using the FSE table
  let (weights, _) ← decodeFseSymbolsAll table bbr
  return (weights, rangeEnd)

/-- Parse a Huffman tree descriptor from a Zstd compressed block (RFC 8878 §4.2.1).
    Reads the header byte at `pos`, dispatches to direct mode (< 128) or
    FSE-compressed mode (>= 128).
    Returns (Huffman table, new position after the tree descriptor). -/
def parseHuffmanTreeDescriptor (data : ByteArray) (pos : Nat) :
    Except String (ZstdHuffmanTable × Nat) := do
  if data.size < pos + 1 then
    throw "Zstd Huffman: not enough data for tree descriptor header"
  let headerByte := data[pos]!.toNat
  if headerByte >= 128 then do
    -- FSE-compressed representation: compressed size = headerByte - 127
    let compressedSize := headerByte - 127
    let (weights, afterWeights) ← parseHuffmanWeightsFse data pos compressedSize
    -- Trim trailing zero weights
    let mut trimmed := weights
    while trimmed.size > 0 && trimmed.back! == 0 do
      trimmed := trimmed.pop
    if trimmed.size == 0 then
      throw "Zstd Huffman: FSE-compressed weights are all zero after trimming"
    let table ← buildZstdHuffmanTable trimmed
    return (table, afterWeights)
  -- Direct representation: headerByte = number of weight bytes
  let numWeightBytes := headerByte
  if numWeightBytes == 0 then
    throw "Zstd Huffman: tree descriptor with 0 weight bytes"
  let (weights, afterWeights) ← parseHuffmanWeightsDirect data (pos + 1) numWeightBytes
  -- Trim trailing zero weights (packed bytes may have a padding zero)
  let mut trimmed := weights
  while trimmed.size > 0 && trimmed.back! == 0 do
    trimmed := trimmed.pop
  if trimmed.size == 0 then
    throw "Zstd Huffman: all weights are zero after trimming"
  let table ← buildZstdHuffmanTable trimmed
  return (table, afterWeights)

end Zip.Native
