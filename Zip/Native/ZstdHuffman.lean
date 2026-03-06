import Zip.Binary
import Zip.Native.Fse

/-!
  Huffman decoding for Zstandard compressed blocks (RFC 8878 §4.2.1).

  Provides types and functions for parsing Huffman tree descriptors (direct
  and FSE-compressed weight representations), building flat lookup tables,
  and decoding Huffman-encoded literal streams (single-stream and 4-stream
  modes).  Used by `parseLiteralsSection` to decode compressed literals
  (litType 2) and treeless literals (litType 3, reusing the previous
  block's Huffman tree).
-/

namespace Zip.Native

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
    throw "Zstd: not enough data for weight bytes"
  let mut weights : Array UInt8 := #[]
  for i in [:numWeightBytes] do
    let byte := data[pos + i]!
    weights := weights.push (byte >>> 4)       -- high nibble
    weights := weights.push (byte &&& 0x0F)    -- low nibble
  return (weights, pos + numWeightBytes)

/-- Find the smallest `maxBits` such that `2^maxBits ≥ weightSum`, then bump by 1
    if `weightSum` equals `2^maxBits` exactly.  Uses well-founded recursion
    (termination measure: `weightSum - power`) so the loop is unfoldable in proofs. -/
def findMaxBitsWF (weightSum maxBits power : Nat) (hpower : power > 0) : Nat :=
  if h : power < weightSum then
    findMaxBitsWF weightSum (maxBits + 1) (power * 2) (by omega)
  else if weightSum == power then
    maxBits + 1
  else
    maxBits
termination_by weightSum - power

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
    throw "Zstd: all weights are zero"
  return findMaxBitsWF weightSum 0 1 (by omega)

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
    throw "Zstd: implicit last Huffman symbol has zero weight"
  -- Derive the last symbol's weight from its 2^(W-1) value
  let mut lastWeight : Nat := 0
  let mut tmp := lastWeight2
  while tmp > 1 do
    lastWeight := lastWeight + 1
    tmp := tmp / 2
  lastWeight := lastWeight + 1
  -- Verify: 2^(lastWeight-1) should equal lastWeight2
  if (1 <<< (lastWeight - 1)) != lastWeight2 then
    throw s!"Zstd: implicit last Huffman symbol weight is not a power of 2 ({lastWeight2})"
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
        throw s!"Zstd: Huffman table index {idx} out of range (tableSize={tableSize})"

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
    throw "Zstd: not enough data for FSE-compressed Huffman weights"
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
    throw "Zstd: not enough data for Huffman tree descriptor header"
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
      throw "Zstd: FSE-compressed Huffman weights are all zero after trimming"
    let table ← buildZstdHuffmanTable trimmed
    return (table, afterWeights)
  -- Direct representation: headerByte = number of weight bytes
  let numWeightBytes := headerByte
  if numWeightBytes == 0 then
    throw "Zstd: Huffman tree descriptor with 0 weight bytes"
  let (weights, afterWeights) ← parseHuffmanWeightsDirect data (pos + 1) numWeightBytes
  -- Trim trailing zero weights (packed bytes may have a padding zero)
  let mut trimmed := weights
  while trimmed.size > 0 && trimmed.back! == 0 do
    trimmed := trimmed.pop
  if trimmed.size == 0 then
    throw "Zstd: all Huffman weights are zero after trimming"
  let table ← buildZstdHuffmanTable trimmed
  return (table, afterWeights)

/-- Decode a single Huffman symbol from a backward bitstream using a flat table.
    Reads `maxBits` bits, looks up the table entry, and advances only `numBits`. -/
def decodeHuffmanSymbol (htable : ZstdHuffmanTable) (br : BackwardBitReader) :
    Except String (UInt8 × BackwardBitReader) := do
  -- Peek maxBits bits for the table lookup
  let (bits, _) ← br.readBits htable.maxBits
  let entry := htable.table[bits.toNat]!
  -- We read maxBits but only needed numBits; "put back" the extra bits.
  -- Since BackwardBitReader doesn't support putting bits back, re-read
  -- only numBits from the original position.
  let (bits2, br2) ← br.readBits entry.numBits.toNat
  let entry2 := htable.table[bits2.toNat <<< (htable.maxBits - entry.numBits.toNat)]!
  return (entry2.symbol, br2)

/-- Decode `count` Huffman symbols from a backward bitstream.
    Returns the decoded bytes as a ByteArray. -/
def decodeHuffmanStream (htable : ZstdHuffmanTable) (br : BackwardBitReader) (count : Nat) :
    Except String ByteArray := do
  let mut br := br
  let mut result := ByteArray.empty
  for _ in [:count] do
    let (sym, br') ← decodeHuffmanSymbol htable br
    br := br'
    result := result.push sym
  return result

/-- Decode 4 Huffman streams as specified in RFC 8878 §3.1.1.3.1.6.
    The first 6 bytes are a jump table (3 × 2-byte LE sizes for streams 1-3).
    Stream 4's size is the remainder. Each stream decodes ceil(regenSize/4) symbols
    (last stream may decode fewer to reach exactly regenSize total). -/
def decodeFourHuffmanStreams (htable : ZstdHuffmanTable) (data : ByteArray)
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
  let r1 ← decodeHuffmanStream htable br1 s1Count
  let br2 ← BackwardBitReader.init data s2Start (s2Start + s2Size)
  let r2 ← decodeHuffmanStream htable br2 s2Count
  let br3 ← BackwardBitReader.init data s3Start (s3Start + s3Size)
  let r3 ← decodeHuffmanStream htable br3 s3Count
  let br4 ← BackwardBitReader.init data s4Start (s4Start + s4Size)
  let r4 ← decodeHuffmanStream htable br4 s4Count
  return r1 ++ r2 ++ r3 ++ r4

/-- Parse compressed/treeless literals header sizes (RFC 8878 §3.1.1.3.1.1).
    Both litType 2 and 3 use the same header layout for regeneratedSize and compressedSize.
    Returns `(regenSize, compSize, headerBytes, fourStreams)`. -/
private def parseCompressedLiteralsHeader (data : ByteArray) (pos : Nat) (sizeFormat : Nat) :
    Except String (Nat × Nat × Nat × Bool) := do
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

/-- Decode Huffman-compressed literal streams using the given table.
    Returns the decoded literals. -/
private def decodeHuffmanLiterals (huffTable : ZstdHuffmanTable) (data : ByteArray)
    (streamStart streamDataSize regenSize : Nat) (fourStreams : Bool) :
    Except String ByteArray := do
  if fourStreams then
    decodeFourHuffmanStreams huffTable data streamStart streamDataSize regenSize
  else do
    let br ← BackwardBitReader.init data streamStart (streamStart + streamDataSize)
    decodeHuffmanStream huffTable br regenSize

/-- Parse the Literals_Section_Header and extract literal bytes (RFC 8878 §3.1.1.3.1).
    Returns `(literals, posAfter, huffmanTable)`: the literal bytes, the position after
    the literals section, and the Huffman table used (if any — `some` for litType 2/3,
    `none` for raw/RLE).
    `prevHuffTree` is the Huffman table from the previous compressed block in this frame
    (needed for treeless literals, litType 3). -/
def parseLiteralsSection (data : ByteArray) (pos : Nat)
    (prevHuffTree : Option ZstdHuffmanTable := none) :
    Except String (ByteArray × Nat × Option ZstdHuffmanTable) := do
  if data.size < pos + 1 then
    throw "Zstd: not enough data for literals section header"
  let byte0 := data[pos]!
  let litType := (byte0 &&& 3).toNat       -- bits 0-1: Literals_Block_Type
  let sizeFormat := ((byte0 >>> 2) &&& 3).toNat  -- bits 2-3: Size_Format
  if litType > 3 then throw "Zstd: invalid literals block type"
  -- Compressed (type 2) or treeless (type 3) literals
  if litType == 2 || litType == 3 then do
    let (regenSize, compSize, headerBytes, fourStreams) ←
      parseCompressedLiteralsHeader data pos sizeFormat
    let afterHeader := pos + headerBytes
    if litType == 3 then do
      -- Treeless: reuse previous Huffman table, all compressedSize bytes are stream data
      let huffTable ← match prevHuffTree with
        | some t => pure t
        | none => throw "Zstd: treeless literals (type 3) but no previous Huffman tree"
      if data.size < afterHeader + compSize then
        throw "Zstd: not enough data for treeless literals"
      let result ← decodeHuffmanLiterals huffTable data afterHeader compSize regenSize fourStreams
      pure (result, afterHeader + compSize, some huffTable)
    else do
      -- Compressed: parse fresh Huffman tree from the data
      if data.size < afterHeader + compSize then
        throw "Zstd: not enough data for compressed literals"
      let (huffTable, afterTree) ← parseHuffmanTreeDescriptor data afterHeader
      let treeSize := afterTree - afterHeader
      if treeSize > compSize then
        throw "Zstd: Huffman tree descriptor exceeds compressed literals size"
      let streamDataSize := compSize - treeSize
      let result ← decodeHuffmanLiterals huffTable data afterTree streamDataSize regenSize fourStreams
      pure (result, afterHeader + compSize, some huffTable)
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
    pure (data.extract afterHeader (afterHeader + regenSize), afterHeader + regenSize, none)
  else
    -- RLE literals: read 1 byte, replicate regeneratedSize times
    if data.size < afterHeader + 1 then
      throw "Zstd: not enough data for RLE literal byte"
    let byte := data[afterHeader]!
    let result := ByteArray.mk (Array.replicate regenSize byte)
    pure (result, afterHeader + 1, none)

end Zip.Native
