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
  verification uses XXH64 (upper 32 bits).  Huffman-compressed literals
  (type 2) are decoded using flat table lookup with `BackwardBitReader`;
  sequence decoding (FSE) is not yet supported.
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

/-- A single entry in a Zstd Huffman decoding table.
    `symbol` is the decoded byte value, `numBits` is the code length. -/
structure HuffmanEntry where
  symbol : UInt8 := 0
  numBits : UInt8 := 0
  deriving Repr, Inhabited

/-- Flat Huffman decoding table for Zstd compressed literals.
    The table has `1 << maxBits` entries, indexed by the next `maxBits` bits of input.
    Each entry gives the decoded symbol and how many bits to actually consume. -/
structure ZstdHuffmanTable where
  maxBits : Nat
  entries : Array HuffmanEntry
  deriving Repr

/-- Parse a direct-representation Huffman weight table (headerByte < 128).
    Reads weights packed two per byte (4 bits each) from `data[off..off+numBytes)`.
    Returns weights as an array of Nats and the position after the weight data. -/
def parseHuffmanWeightsDirect (data : ByteArray) (off numBytes : Nat) :
    Except String (Array Nat × Nat) := do
  if data.size < off + numBytes then
    throw "Zstd: not enough data for Huffman weight table"
  let mut weights : Array Nat := #[]
  for i in [:numBytes] do
    let b := data[off + i]!
    weights := weights.push (b >>> 4).toNat
    weights := weights.push (b &&& 0x0F).toNat
  return (weights, off + numBytes)

/-- Compute the maximum code length from the weights array.
    Weight w means code length = maxBits + 1 - w; weight 0 means unused.
    maxBits is the smallest n such that 2^n >= sum of 2^(w-1) for nonzero weights. -/
def weightsToMaxBits (weights : Array Nat) : Nat :=
  -- Sum 2^(w-1) for nonzero w
  let sum := weights.foldl (fun acc w =>
    if w > 0 then acc + (1 <<< (w - 1)) else acc) 0
  -- maxBits = ceil(log2(sum)) — but more precisely, smallest n with 2^n >= sum
  -- Since sum should be a power of 2, log2 works
  if sum == 0 then 1 else Nat.log2 sum + 1

/-- Build a flat Huffman decoding table from an array of weights.
    Each symbol `s` has weight `weights[s]`; weight 0 means unused.
    The actual code length for symbol `s` is `maxBits + 1 - weights[s]`.
    The last symbol (not in the weights array) gets weight derived from the
    power-of-2 constraint. -/
def buildZstdHuffmanTable (weights : Array Nat) : Except String ZstdHuffmanTable := do
  -- Determine maxBits from existing weights
  let sum := weights.foldl (fun acc w =>
    if w > 0 then acc + (1 <<< (w - 1)) else acc) 0
  if sum == 0 then
    throw "Zstd: Huffman table has no symbols"
  -- maxBits is the smallest n where 2^n >= sum
  let mut maxBits := 0
  let mut powerOf2 := 1
  while powerOf2 <= sum do
    maxBits := maxBits + 1
    powerOf2 := powerOf2 * 2
  -- The remaining capacity goes to the last symbol (index = weights.size)
  let lastWeight_capacity := powerOf2 - sum
  -- lastWeight_capacity should be a power of 2: 2^(lastWeight-1)
  let mut lastWeight := 0
  let mut tmp := lastWeight_capacity
  while tmp > 1 do
    lastWeight := lastWeight + 1
    tmp := tmp / 2
  lastWeight := lastWeight + 1
  -- Build the full weights array including the last symbol
  let allWeights := weights.push lastWeight
  -- Build the flat table (1 << maxBits entries)
  let tableSize := 1 <<< maxBits
  let mut entries := Array.replicate tableSize default
  -- Assign codes: symbols are assigned in order of code length (longest first)
  -- For each code length, fill table entries
  let mut code := 0
  for bits in List.range (maxBits + 1) |>.reverse do
    let codeBits := bits + 1  -- actual bit length
    if codeBits > maxBits + 1 then continue
    let weight := maxBits + 1 - codeBits
    if weight == 0 then continue
    for sym in [:allWeights.size] do
      if allWeights[sym]! == weight then
        -- Fill 2^(maxBits - codeBits) entries for this symbol
        let numEntries := 1 <<< (maxBits - codeBits)
        for j in [:numEntries] do
          let idx := code + j
          if idx < tableSize then
            entries := entries.set! idx { symbol := sym.toUInt8, numBits := codeBits.toUInt8 }
        code := code + numEntries
  return { maxBits, entries }

/-- Parse a Huffman tree descriptor from the bitstream (RFC 8878 §4.2.1).
    Currently supports direct representation only (header byte < 128).
    Returns the Huffman table and position after the tree descriptor. -/
def parseHuffmanTreeDescriptor (data : ByteArray) (pos : Nat) :
    Except String (ZstdHuffmanTable × Nat) := do
  if data.size < pos + 1 then
    throw "Zstd: not enough data for Huffman tree descriptor"
  let headerByte := data[pos]!.toNat
  if headerByte >= 128 then
    -- FSE-compressed weights (future work)
    throw "Zstd: FSE-compressed Huffman weights not yet supported"
  -- Direct representation: headerByte = number of bytes of weight data
  let numBytes := headerByte
  if numBytes == 0 then
    throw "Zstd: Huffman tree descriptor with 0 weight bytes"
  let (weights, afterWeights) ← parseHuffmanWeightsDirect data (pos + 1) numBytes
  -- Strip trailing zero weights (they're padding from the 2-per-byte packing)
  let mut trimmed := weights
  while trimmed.size > 0 && trimmed.back! == 0 do
    trimmed := trimmed.pop
  let table ← buildZstdHuffmanTable trimmed
  return (table, afterWeights)

/-- Decode a single Huffman symbol from a backward bitstream using a flat table.
    Reads `maxBits` bits, looks up the table entry, and advances only `numBits`. -/
def decodeHuffmanSymbol (table : ZstdHuffmanTable) (br : BackwardBitReader) :
    Except String (UInt8 × BackwardBitReader) := do
  -- Peek maxBits bits for the table lookup
  let (bits, _) ← br.readBits table.maxBits
  let entry := table.entries[bits.toNat]!
  -- We read maxBits but only needed numBits; "put back" the extra bits.
  -- Since BackwardBitReader doesn't support putting bits back, re-read
  -- only numBits from the original position.
  let (bits2, br2) ← br.readBits entry.numBits.toNat
  let entry2 := table.entries[bits2.toNat <<< (table.maxBits - entry.numBits.toNat)]!
  return (entry2.symbol, br2)

/-- Decode `count` Huffman symbols from a backward bitstream.
    Returns the decoded bytes as a ByteArray. -/
def decodeHuffmanStream (table : ZstdHuffmanTable) (br : BackwardBitReader) (count : Nat) :
    Except String ByteArray := do
  let mut br := br
  let mut result := ByteArray.empty
  for _ in [:count] do
    let (sym, br') ← decodeHuffmanSymbol table br
    br := br'
    result := result.push sym
  return result

/-- Decode 4 Huffman streams as specified in RFC 8878 §3.1.1.3.1.6.
    The first 6 bytes are a jump table (3 × 2-byte LE sizes for streams 1-3).
    Stream 4's size is the remainder. Each stream decodes ceil(regenSize/4) symbols
    (last stream may decode fewer to reach exactly regenSize total). -/
def decodeFourHuffmanStreams (table : ZstdHuffmanTable) (data : ByteArray)
    (streamStart streamDataSize regenSize : Nat) :
    Except String ByteArray := do
  -- Need at least 6 bytes for the jump table
  if streamDataSize < 6 then
    throw "Zstd: 4-stream Huffman data too small for jump table"
  let jumpOff := streamStart
  if data.size < jumpOff + 6 then
    throw "Zstd: not enough data for Huffman jump table"
  let s1Size := (Binary.readUInt16LE data jumpOff).toNat
  let s2Size := (Binary.readUInt16LE data (jumpOff + 2)).toNat
  let s3Size := (Binary.readUInt16LE data (jumpOff + 4)).toNat
  let afterJump := jumpOff + 6
  let totalStreamBytes := streamDataSize - 6
  if s1Size + s2Size + s3Size > totalStreamBytes then
    throw "Zstd: Huffman stream sizes exceed available data"
  let s4Size := totalStreamBytes - s1Size - s2Size - s3Size
  -- Compute per-stream symbol counts
  let perStream := (regenSize + 3) / 4
  let s1Count := perStream
  let s2Count := perStream
  let s3Count := perStream
  let s4Count := regenSize - s1Count - s2Count - s3Count
  -- Decode each stream
  let s1Start := afterJump
  let s2Start := s1Start + s1Size
  let s3Start := s2Start + s2Size
  let s4Start := s3Start + s3Size
  let br1 ← BackwardBitReader.init data s1Start (s1Start + s1Size)
  let r1 ← decodeHuffmanStream table br1 s1Count
  let br2 ← BackwardBitReader.init data s2Start (s2Start + s2Size)
  let r2 ← decodeHuffmanStream table br2 s2Count
  let br3 ← BackwardBitReader.init data s3Start (s3Start + s3Size)
  let r3 ← decodeHuffmanStream table br3 s3Count
  let br4 ← BackwardBitReader.init data s4Start (s4Start + s4Size)
  let r4 ← decodeHuffmanStream table br4 s4Count
  return r1 ++ r2 ++ r3 ++ r4

/-- Parse the Literals_Section_Header and extract literal bytes (RFC 8878 §3.1.1.3.1).
    Returns the literal bytes and the position after the literals section.
    Raw literals are copied verbatim; RLE literals are expanded to `regeneratedSize` copies
    of a single byte. Compressed literals (type 2) are decoded using Huffman tables.
    Treeless literals (type 3) return an error (requires cross-block state). -/
def parseLiteralsSection (data : ByteArray) (pos : Nat) :
    Except String (ByteArray × Nat) := do
  if data.size < pos + 1 then
    throw "Zstd: not enough data for literals section header"
  let byte0 := data[pos]!
  let litType := (byte0 &&& 3).toNat       -- bits 0-1: Literals_Block_Type
  let sizeFormat := ((byte0 >>> 2) &&& 3).toNat  -- bits 2-3: Size_Format
  -- Treeless literals require cross-block Huffman table state (future issue)
  if litType == 3 then throw "Zstd: treeless literals not yet supported"
  if litType > 3 then throw "Zstd: invalid literals block type"
  -- Compressed literals (type 2): both regeneratedSize and compressedSize in header
  if litType == 2 then do
    -- Parse the extended header for compressed literals (RFC 8878 §3.1.1.3.1.1).
    -- The header is packed as a little-endian bitfield:
    --   bits [1:0]  = litType, bits [3:2] = sizeFormat
    --   sizeFormat 0,1: 3-byte header, 10-bit sizes, single stream
    --   sizeFormat 2:   4-byte header, 14-bit sizes, 4 streams
    --   sizeFormat 3:   5-byte header, 18-bit sizes, 4 streams
    let (regenSize, compSize, headerBytes, fourStreams) ←
      if sizeFormat <= 1 then do
        if data.size < pos + 3 then throw "Zstd: truncated compressed literals header"
        let b0 := data[pos]!.toNat
        let b1 := data[pos + 1]!.toNat
        let b2 := data[pos + 2]!.toNat
        let raw := b0 ||| (b1 <<< 8) ||| (b2 <<< 16)
        let regen := (raw >>> 4) &&& 0x3FF
        let comp := (raw >>> 14) &&& 0x3FF
        pure (regen, comp, 3, false)
      else if sizeFormat == 2 then do
        if data.size < pos + 4 then throw "Zstd: truncated compressed literals header"
        let b0 := data[pos]!.toNat
        let b1 := data[pos + 1]!.toNat
        let b2 := data[pos + 2]!.toNat
        let b3 := data[pos + 3]!.toNat
        let raw := b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24)
        let regen := (raw >>> 4) &&& 0x3FFF
        let comp := (raw >>> 18) &&& 0x3FFF
        pure (regen, comp, 4, true)
      else do
        if data.size < pos + 5 then throw "Zstd: truncated compressed literals header"
        let b0 := data[pos]!.toNat
        let b1 := data[pos + 1]!.toNat
        let b2 := data[pos + 2]!.toNat
        let b3 := data[pos + 3]!.toNat
        let b4 := data[pos + 4]!.toNat
        let raw := b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24) ||| (b4 <<< 32)
        let regen := (raw >>> 4) &&& 0x3FFFF
        let comp := (raw >>> 22) &&& 0x3FFFF
        pure (regen, comp, 5, true)
    let afterHeader := pos + headerBytes
    if data.size < afterHeader + compSize then
      throw "Zstd: not enough data for compressed literals"
    -- Parse Huffman tree descriptor (compSize includes tree + stream data)
    let (huffTable, afterTree) ← parseHuffmanTreeDescriptor data afterHeader
    let treeSize := afterTree - afterHeader
    if treeSize > compSize then
      throw "Zstd: Huffman tree descriptor exceeds compressed literals size"
    let streamDataSize := compSize - treeSize
    -- Decode the Huffman-compressed literal streams
    if fourStreams then do
      let result ← decodeFourHuffmanStreams huffTable data afterTree streamDataSize regenSize
      pure (result, afterHeader + compSize)
    else do
      let br ← BackwardBitReader.init data afterTree (afterTree + streamDataSize)
      let result ← decodeHuffmanStream huffTable br regenSize
      pure (result, afterHeader + compSize)
  else
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

end Zip.Native
