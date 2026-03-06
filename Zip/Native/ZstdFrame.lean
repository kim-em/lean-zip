import Zip.Binary
import Zip.Native.Fse
import Zip.Native.XxHash
import Zip.Native.ZstdHuffman
import Zip.Native.ZstdSequence

/-!
  Frame-level Zstandard decompression (RFC 8878 §3.1.1).

  Parses the fixed-format header at the start of every Zstd frame:
  magic number, frame header descriptor (bit fields), optional window
  descriptor, optional dictionary ID, and optional frame content size.
  Also parses the block-level structure within a frame: 3-byte block
  headers (Last_Block, Block_Type, Block_Size) and decompresses Raw
  (verbatim copy) and RLE (single byte repeated) blocks.

  Provides frame-level decompression (`decompressFrame`) that wires
  header parsing + block decompression together, and a top-level API
  (`decompressZstd`) that loops over concatenated frames, skipping
  skippable frames (RFC 8878 §3.1.2) and concatenating output from
  multiple Zstd frames.  Content checksum verification uses XXH64
  (upper 32 bits).

  Huffman-compressed literals and sequence decoding are in
  `Zip.Native.ZstdHuffman` and `Zip.Native.ZstdSequence` respectively.
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
  let result := ByteArray.mk (Array.replicate sz byte)
  return (result, pos + 1)

/-- Well-founded recursive inner loop for `decompressBlocks`.
    Processes blocks one at a time until `lastBlock` is seen, threading
    Huffman tables, FSE tables, and offset history between compressed blocks.
    Uses explicit recursion with `termination_by data.size - off` so the
    function is unfoldable in proofs (unlike the opaque `forIn` from `while`). -/
def decompressBlocksWF (data : ByteArray) (off : Nat) (windowSize : UInt64)
    (output : ByteArray) (prevHuffTree : Option ZstdHuffmanTable)
    (prevFseTables : PrevFseTables) (offsetHistory : Array Nat) :
    Except String (ByteArray × Nat) :=
  if hoff : data.size ≤ off then
    .error "Zstd: unexpected end of block data"
  else do
    let (hdr, afterHdr) ← parseBlockHeader data off
    -- Validate block size (RFC 8878 §3.1.1.2: Block_Content ≤ 128KB)
    if hdr.blockSize > 131072 then
      throw s!"Zstd: block size {hdr.blockSize} exceeds maximum (128KB)"
    if windowSize > 0 && hdr.blockSize.toUInt64 > windowSize then
      throw s!"Zstd: block size {hdr.blockSize} exceeds window size {windowSize}"
    -- Process block content based on type
    let (newOutput, newOff, newHuffTree, newFseTables, newHistory) ← match hdr.blockType with
      | .raw => do
        let (block, afterBlock) ← decompressRawBlock data afterHdr hdr.blockSize
        pure (output ++ block, afterBlock, prevHuffTree, prevFseTables, offsetHistory)
      | .rle => do
        let (block, afterByte) ← decompressRLEBlock data afterHdr hdr.blockSize
        pure (output ++ block, afterByte, prevHuffTree, prevFseTables, offsetHistory)
      | .compressed => do
        let blockEnd := afterHdr + hdr.blockSize.toNat
        let (literals, afterLiterals, huffTree) ←
          (parseLiteralsSection data afterHdr prevHuffTree).mapError (· ++ " [in parseLiteralsSection]")
        let newHuff := if let some ht := huffTree then some ht else prevHuffTree
        let (numSeq, modes, afterSeqHeader) ← parseSequencesHeader data afterLiterals
        if numSeq == 0 then
          pure (output ++ literals, blockEnd, newHuff, prevFseTables, offsetHistory)
        else
          let (llTable, ofTable, mlTable, afterTables) ←
            resolveSequenceFseTables modes data afterSeqHeader prevFseTables
          let newFse : PrevFseTables :=
            { litLen := some llTable, offset := some ofTable, matchLen := some mlTable }
          let bbr ← BackwardBitReader.init data afterTables blockEnd
          let sequences ← (decodeSequences llTable ofTable mlTable bbr numSeq).mapError
            (· ++ " [in decodeSequences]")
          let windowPrefix := if windowSize > 0 && output.size > windowSize.toNat
            then output.extract (output.size - windowSize.toNat) output.size
            else output
          let (blockOutput, newHist) ← executeSequences sequences literals
            windowPrefix offsetHistory windowSize.toNat
          pure (output ++ blockOutput, blockEnd, newHuff, newFse, newHist)
      | .reserved =>
        throw "Zstd: reserved block type"
    if hdr.lastBlock then
      return (newOutput, newOff)
    else
      -- Position must advance for termination. This always holds: parseBlockHeader
      -- reads 3 bytes (afterHdr = off + 3), and block processing advances further.
      if hadv : newOff ≤ off then
        throw "Zstd: block did not advance position"
      else
        have : data.size - newOff < data.size - off := by omega
        decompressBlocksWF data newOff windowSize newOutput newHuffTree newFseTables newHistory
termination_by data.size - off

/-- Decompress all blocks in a Zstd frame starting at `pos` (after the frame header).
    Loops through block headers, dispatches on block type, and accumulates output.
    Threads the Huffman table from compressed literals blocks to support treeless
    literals (litType 3) in subsequent blocks. Threads FSE tables for Repeat mode
    and offset history between compressed blocks.
    Returns the decompressed content and position after the last block. -/
def decompressBlocks (data : ByteArray) (pos : Nat) (windowSize : UInt64 := 0) :
    Except String (ByteArray × Nat) :=
  decompressBlocksWF data pos windowSize ByteArray.empty none {} #[1, 4, 8]

/-- Decompress a single Zstd frame starting at `pos` in `data`.
    Parses the frame header, decompresses all blocks, verifies the optional
    content checksum (upper 32 bits of XXH64 with seed 0), and validates
    content size if specified in the header.
    Returns decompressed data and position after the frame. -/
def decompressFrame (data : ByteArray) (pos : Nat) :
    Except String (ByteArray × Nat) := do
  let (header, afterHeader) ← parseFrameHeader data pos
  -- Reject dictionary-compressed frames (lean-zip does not support dictionaries)
  if let some dictId := header.dictionaryId then
    if dictId != 0 then
      throw s!"Zstd: dictionary decompression not supported (dictionary ID: {dictId})"
  let (content, afterBlocks) ← decompressBlocks data afterHeader header.windowSize
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

/-- Skip a skippable frame starting at `pos` (RFC 8878 §3.1.2).
    Validates that the magic number is in the range 0x184D2A50–0x184D2A5F,
    reads the 4-byte little-endian frame data size, and returns the position
    immediately after the frame data.  Errors if there is insufficient data. -/
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

/-- Well-founded recursive frame loop for `decompressZstd`.
    Processes concatenated Zstd frames one at a time, dispatching on the
    4-byte magic number to either skip skippable frames or decompress
    standard Zstd frames.  Uses explicit recursion with
    `termination_by data.size - pos` so the function is unfoldable in proofs
    (unlike the opaque `forIn` from `while`). -/
def decompressZstdWF (data : ByteArray) (pos : Nat) (output : ByteArray) :
    Except String ByteArray :=
  if hpos : pos ≥ data.size then
    return output
  else do
    if data.size < pos + 4 then
      throw "Zstd: trailing data too short for frame magic number"
    let magic := Binary.readUInt32LE data pos
    if magic >= 0x184D2A50 && magic <= 0x184D2A5F then
      let afterFrame ← skipSkippableFrame data pos
      if hadv : afterFrame ≤ pos then
        throw "Zstd: skippable frame did not advance position"
      else
        have : data.size - afterFrame < data.size - pos := by omega
        decompressZstdWF data afterFrame output
    else if magic == zstdMagic then
      let (content, afterFrame) ← decompressFrame data pos
      if hadv : afterFrame ≤ pos then
        throw "Zstd: frame did not advance position"
      else
        have : data.size - afterFrame < data.size - pos := by omega
        decompressZstdWF data afterFrame (output ++ content)
    else
      throw s!"Zstd: invalid magic number 0x{String.ofList (Nat.toDigits 16 magic.toNat)} at offset {pos} (expected 0xFD2FB528 or skippable frame)"
termination_by data.size - pos

/-- Top-level Zstd decompression: loops over all frames in the input,
    decompressing Zstd frames and skipping skippable frames (RFC 8878 §3.1).
    Returns the concatenated decompressed content from all Zstd frames.
    An input containing only skippable frames (or empty) returns an empty ByteArray.
    Trailing bytes that are neither a valid Zstd frame nor a skippable frame
    produce an error. -/
def decompressZstd (data : ByteArray) : Except String ByteArray :=
  decompressZstdWF data 0 ByteArray.empty

end Zip.Native
