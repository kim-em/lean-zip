import Zip.Native.Fse

/-!
  Zstandard sequence decoding (RFC 8878 §3.1.1.3.2, §3.1.1.4, §4.1.1).

  Provides types and functions for parsing the sequences section header,
  decoding interleaved FSE-encoded sequences from a backward bitstream,
  resolving repeat offsets, executing sequences (literal copy + match copy),
  and resolving FSE tables from their compression modes (predefined, RLE,
  FSE-compressed, repeat).

  The extra bits tables (RFC 8878 Tables 14–15) for literal length and
  match length codes are also defined here.
-/

namespace Zip.Native

/-- Compression mode for one of the three sequence symbol types
    (RFC 8878 §3.1.1.3.2). -/
inductive SequenceCompressionMode where
  | predefined   -- 0: use default distribution
  | rle           -- 1: single repeated symbol
  | fseCompressed -- 2: custom FSE distribution in bitstream
  | repeat        -- 3: reuse previous block's table
  deriving Repr, BEq

/-- Parsed compression modes for the three sequence symbol types. -/
structure SequenceCompressionModes where
  /-- How literal length codes are encoded. -/
  litLenMode  : SequenceCompressionMode
  /-- How offset codes are encoded. -/
  offsetMode  : SequenceCompressionMode
  /-- How match length codes are encoded. -/
  matchLenMode : SequenceCompressionMode
  deriving Repr

/-- Convert a 2-bit mode value to `SequenceCompressionMode`. -/
private def modeFromBits (bits : UInt8) : SequenceCompressionMode :=
  match bits.toNat with
  | 0 => .predefined
  | 1 => .rle
  | 2 => .fseCompressed
  | _ => .repeat

/-- Parse the Sequences_Section header (RFC 8878 §3.1.1.3.2).
    Returns (numberOfSequences, compressionModes, position after header).
    If numberOfSequences is 0, compression modes are all `predefined` (no modes
    byte present) and the block has only literals. -/
def parseSequencesHeader (data : ByteArray) (pos : Nat) :
    Except String (Nat × SequenceCompressionModes × Nat) := do
  if data.size < pos + 1 then
    throw "Zstd: not enough data for sequences header"
  let byte0 := data[pos]!.toNat
  let defaultModes : SequenceCompressionModes :=
    { litLenMode := .predefined, offsetMode := .predefined, matchLenMode := .predefined }
  if byte0 == 0 then
    -- 0 sequences: no compression modes byte follows
    pure (0, defaultModes, pos + 1)
  else if byte0 < 128 then
    -- 1-byte count + compression modes byte
    if data.size < pos + 2 then
      throw "Zstd: not enough data for sequence compression modes"
    let modesByte := data[pos + 1]!
    let modes : SequenceCompressionModes := {
      litLenMode := modeFromBits ((modesByte >>> 6) &&& 3)
      offsetMode := modeFromBits ((modesByte >>> 4) &&& 3)
      matchLenMode := modeFromBits ((modesByte >>> 2) &&& 3)
    }
    pure (byte0, modes, pos + 2)
  else if byte0 < 255 then
    -- 2-byte count: ((byte0 - 128) << 8) + byte1, then compression modes
    if data.size < pos + 3 then
      throw "Zstd: truncated sequences header"
    let byte1 := data[pos + 1]!.toNat
    let numSeq := ((byte0 - 128) <<< 8) + byte1
    let modesByte := data[pos + 2]!
    let modes : SequenceCompressionModes := {
      litLenMode := modeFromBits ((modesByte >>> 6) &&& 3)
      offsetMode := modeFromBits ((modesByte >>> 4) &&& 3)
      matchLenMode := modeFromBits ((modesByte >>> 2) &&& 3)
    }
    pure (numSeq, modes, pos + 3)
  else
    -- 3-byte count (byte0 == 255): byte1 + (byte2 << 8) + 0x7F00, then compression modes
    if data.size < pos + 4 then
      throw "Zstd: truncated sequences header"
    let byte1 := data[pos + 1]!.toNat
    let byte2 := data[pos + 2]!.toNat
    let numSeq := byte1 + (byte2 <<< 8) + 0x7F00
    let modesByte := data[pos + 3]!
    let modes : SequenceCompressionModes := {
      litLenMode := modeFromBits ((modesByte >>> 6) &&& 3)
      offsetMode := modeFromBits ((modesByte >>> 4) &&& 3)
      matchLenMode := modeFromBits ((modesByte >>> 2) &&& 3)
    }
    pure (numSeq, modes, pos + 4)

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
  deriving Repr, Inhabited

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

/-- Copy `count` bytes from `src` starting at `srcPos`, appending each byte to `dst`.
    Equivalent to `for i in [:count] do dst := dst.push src[srcPos + i]!`, but uses
    explicit recursion for proof-friendliness (Range.forIn cannot be unfolded by name). -/
def copyBytes (dst : ByteArray) (src : ByteArray) (srcPos count : Nat) : ByteArray :=
  if count = 0 then dst
  else copyBytes (dst.push src[srcPos]!) src (srcPos + 1) (count - 1)
termination_by count

/-- Copy `length` bytes from `offset` bytes back in `buf`, handling overlapping matches
    (byte-by-byte copy so that repeated patterns are expanded correctly). -/
def copyMatch (buf : ByteArray) (offset length : Nat) : ByteArray :=
  let start := buf.size - offset
  let rec loop (b : ByteArray) (k : Nat) : ByteArray :=
    if k < length then
      loop (b.push b[start + (k % offset)]!) (k + 1)
    else b
  termination_by length - k
  loop buf 0

/-- Process sequences recursively. This is the inner loop of `executeSequences`:
    for each sequence, copy literal bytes then match bytes, threading state through.
    Written in applicative style (no `do`) for proof-friendliness. -/
def executeSequences.loop (seqs : List ZstdSequence) (literals : ByteArray)
    (output : ByteArray) (history : Array Nat) (litPos : Nat) (windowSize : Nat) :
    Except String (ByteArray × Array Nat × Nat) :=
  match seqs with
  | [] => .ok (output, history, litPos)
  | seq :: rest =>
    if litPos + seq.literalLength > literals.size then
      .error s!"Zstd: sequence requires {litPos + seq.literalLength} literal bytes but only {literals.size} available"
    else
      let output := copyBytes output literals litPos seq.literalLength
      let litPos := litPos + seq.literalLength
      let (offset, history') := resolveOffset seq.offset history seq.literalLength
      if offset == 0 then
        .error "Zstd: resolved offset is 0"
      else if offset > output.size then
        .error s!"Zstd: match offset {offset} exceeds output size {output.size}"
      else if windowSize > 0 && offset > windowSize then
        .error s!"Zstd: sequence offset {offset} exceeds window size {windowSize}"
      else
        let output := copyMatch output offset seq.matchLength
        executeSequences.loop rest literals output history' litPos windowSize

/-- Execute decoded Zstd sequences against a literals buffer to produce decompressed output
    (RFC 8878 §3.1.1.4). For each sequence: copies `literalLength` bytes from literals, then
    copies `matchLength` bytes from `offset` back in the output (with overlap semantics).
    After all sequences, any remaining literals are appended.

    For multi-block frames (RFC 8878 §3.1.1.5):
    - `windowPrefix`: previous blocks' output (last `windowSize` bytes) for cross-block
      back-references. Match offsets can reach into the prefix.
    - `offsetHistory`: 3-entry offset history from the previous block.

    Returns the decompressed block output (excluding prefix) and the updated offset history
    for the next block. -/
def executeSequences (sequences : Array ZstdSequence) (literals : ByteArray)
    (windowPrefix : ByteArray := ByteArray.empty)
    (offsetHistory : Array Nat := #[1, 4, 8])
    (windowSize : Nat := 0) :
    Except String (ByteArray × Array Nat) := do
  let (output, history, litPos) ←
    executeSequences.loop sequences.toList literals windowPrefix offsetHistory 0 windowSize
  let output := copyBytes output literals litPos (literals.size - litPos)
  let blockOutput := output.extract windowPrefix.size output.size
  return (blockOutput, history)

/-- Extra bits table for literal length codes 0-35 (RFC 8878 Table 14).
    Each entry is `(baseline, numExtraBits)`. For codes 0-15 the literal
    length is the code itself (0 extra bits). -/
def litLenExtraBits : Array (Nat × Nat) := #[
  (0, 0), (1, 0), (2, 0), (3, 0), (4, 0), (5, 0), (6, 0), (7, 0),       -- 0-7
  (8, 0), (9, 0), (10, 0), (11, 0), (12, 0), (13, 0), (14, 0), (15, 0),  -- 8-15
  (16, 1), (18, 1), (20, 1), (22, 1),                                      -- 16-19
  (24, 2), (28, 2),                                                         -- 20-21
  (32, 3), (40, 3),                                                         -- 22-23
  (48, 4), (64, 6), (128, 7), (256, 8), (512, 9),                          -- 24-28
  (1024, 10), (2048, 11), (4096, 12), (8192, 13),                          -- 29-32
  (16384, 14), (32768, 15), (65536, 16)                                     -- 33-35
]

/-- Extra bits table for match length codes 0-52 (RFC 8878 Table 15).
    Each entry is `(baseline, numExtraBits)`. For codes 0-31 the match
    length is `code + 3` (0 extra bits). -/
def matchLenExtraBits : Array (Nat × Nat) := #[
  (3, 0), (4, 0), (5, 0), (6, 0), (7, 0), (8, 0), (9, 0), (10, 0),      -- 0-7
  (11, 0), (12, 0), (13, 0), (14, 0), (15, 0), (16, 0), (17, 0), (18, 0),-- 8-15
  (19, 0), (20, 0), (21, 0), (22, 0), (23, 0), (24, 0), (25, 0), (26, 0),-- 16-23
  (27, 0), (28, 0), (29, 0), (30, 0), (31, 0), (32, 0), (33, 0), (34, 0),-- 24-31
  (35, 1), (37, 1), (39, 1), (41, 1),                                      -- 32-35
  (43, 2), (47, 2),                                                         -- 36-37
  (51, 3), (59, 3),                                                         -- 38-39
  (67, 4), (83, 4),                                                         -- 40-41
  (99, 5), (131, 7), (259, 8), (515, 9), (1027, 10),                       -- 42-46
  (2051, 11), (4099, 12), (8195, 13),                                       -- 47-49
  (16387, 14), (32771, 15), (65539, 16)                                     -- 50-52
]

/-- Decode a literal length FSE symbol code into an actual literal length value
    (RFC 8878 §3.1.1.3.2.1.1). Looks up the code in `litLenExtraBits` and
    returns `baseline + extraBits`. -/
def decodeLitLenValue (code : Nat) (extraBits : UInt32) : Except String Nat := do
  if h : code < litLenExtraBits.size then
    let (baseline, _) := litLenExtraBits[code]
    pure (baseline + extraBits.toNat)
  else
    throw s!"Zstd: literal length code {code} out of range (max 35)"

/-- Decode a match length FSE symbol code into an actual match length value
    (RFC 8878 §3.1.1.3.2.1.2). Looks up the code in `matchLenExtraBits` and
    returns `baseline + extraBits`. -/
def decodeMatchLenValue (code : Nat) (extraBits : UInt32) : Except String Nat := do
  if h : code < matchLenExtraBits.size then
    let (baseline, _) := matchLenExtraBits[code]
    pure (baseline + extraBits.toNat)
  else
    throw s!"Zstd: match length code {code} out of range (max 52)"

/-- Decode an offset FSE symbol code into an offset value (RFC 8878 §3.1.1.4).
    Offset_Value = (1 <<< code) + extraBits, where extraBits has `code` bits.
    The formula applies uniformly to all codes including 0:
    code 0 → (1 << 0) + 0 = 1 (repeat offset 1). -/
def decodeOffsetValue (code : Nat) (extraBits : UInt32) : Nat :=
  (1 <<< code) + extraBits.toNat

/-- Decode interleaved FSE sequences from a backward bitstream (RFC 8878 §4.1.1).
    Takes three FSE tables (litLen, offset, matchLen), a `BackwardBitReader`
    positioned at the start of the encoded sequence data, and `numSeq`.
    Returns the decoded sequence array.

    Interleaving order per RFC 8878 §4.1.1:
    - Symbol lookup: offset, matchLen, litLen
    - Extra bits reading: offset, matchLen, litLen
    - State update (not on last sequence): litLen, matchLen, offset -/
def decodeSequences (litLenTable offsetTable matchLenTable : FseTable)
    (br : BackwardBitReader) (numSeq : Nat) :
    Except String (Array ZstdSequence) := do
  if numSeq == 0 then return #[]
  -- Initialize three FSE states
  let (litLenInit, br) ← br.readBits litLenTable.accuracyLog
  let (offsetInit, br) ← br.readBits offsetTable.accuracyLog
  let (matchLenInit, br) ← br.readBits matchLenTable.accuracyLog
  let mut litLenState := litLenInit.toNat
  let mut offsetState := offsetInit.toNat
  let mut matchLenState := matchLenInit.toNat
  let mut br := br
  let mut result : Array ZstdSequence := Array.mkEmpty numSeq
  let litLenTableSize := 1 <<< litLenTable.accuracyLog
  let offsetTableSize := 1 <<< offsetTable.accuracyLog
  let matchLenTableSize := 1 <<< matchLenTable.accuracyLog
  for i in [:numSeq] do
    -- Bounds check states
    if offsetState >= offsetTableSize then
      throw s!"Zstd: offset FSE state {offsetState} out of range (table size {offsetTableSize})"
    if matchLenState >= matchLenTableSize then
      throw s!"Zstd: matchLen FSE state {matchLenState} out of range (table size {matchLenTableSize})"
    if litLenState >= litLenTableSize then
      throw s!"Zstd: litLen FSE state {litLenState} out of range (table size {litLenTableSize})"
    -- Symbol lookup order: offset, matchLen, litLen
    let offsetCell := offsetTable.cells[offsetState]!
    let matchLenCell := matchLenTable.cells[matchLenState]!
    let litLenCell := litLenTable.cells[litLenState]!
    let offsetCode := offsetCell.symbol.toNat
    let matchLenCode := matchLenCell.symbol.toNat
    let litLenCode := litLenCell.symbol.toNat
    -- Read extra bits order: offset, matchLen, litLen
    -- Offset extra bits: offsetCode bits (code IS the number of extra bits)
    let (offsetExtra, br') ← br.readBits offsetCode
    br := br'
    -- MatchLen extra bits: look up in matchLenExtraBits table
    if h : matchLenCode < matchLenExtraBits.size then
      let (_, matchExtraBitCount) := matchLenExtraBits[matchLenCode]
      let (matchExtra, br') ← br.readBits matchExtraBitCount
      br := br'
      -- LitLen extra bits: look up in litLenExtraBits table
      if h2 : litLenCode < litLenExtraBits.size then
        let (_, litExtraBitCount) := litLenExtraBits[litLenCode]
        let (litExtra, br') ← br.readBits litExtraBitCount
        br := br'
        -- Convert codes + extra bits to actual values
        let offsetVal := decodeOffsetValue offsetCode offsetExtra
        let matchLenVal ← decodeMatchLenValue matchLenCode matchExtra
        let litLenVal ← decodeLitLenValue litLenCode litExtra
        result := result.push { literalLength := litLenVal, matchLength := matchLenVal, offset := offsetVal }
        -- State update (not on last sequence): litLen, matchLen, offset order
        if i + 1 < numSeq then
          let (litBits, br') ← br.readBits litLenCell.numBits.toNat
          br := br'
          litLenState := litLenCell.newState.toNat + litBits.toNat
          let (matchBits, br') ← br.readBits matchLenCell.numBits.toNat
          br := br'
          matchLenState := matchLenCell.newState.toNat + matchBits.toNat
          let (offBits, br') ← br.readBits offsetCell.numBits.toNat
          br := br'
          offsetState := offsetCell.newState.toNat + offBits.toNat
      else
        throw s!"Zstd: literal length code {litLenCode} out of range (max 35)"
    else
      throw s!"Zstd: match length code {matchLenCode} out of range (max 52)"
  return result

/-- Build an FSE table for RLE mode: a single-cell table where every state maps
    to the given symbol with 0 extra bits (RFC 8878 §3.1.1.3.2.1, mode 1). -/
def buildRleFseTable (symbol : UInt8) : FseTable :=
  { accuracyLog := 0,
    cells := #[{ symbol := symbol.toUInt16, numBits := 0, newState := 0 }] }

/-- Resolve a single FSE table from its compression mode (RFC 8878 §3.1.1.3.2.1).
    Reads any necessary data from `data` at `pos` and returns the table and updated position.
    - Mode 0 (Predefined): build from predefined distribution and accuracy log.
    - Mode 1 (RLE): read 1 byte, build single-symbol table.
    - Mode 2 (FSE_Compressed): decode distribution from bitstream, build table.
    - Mode 3 (Repeat): reuse previous block's table (requires `prevTable`). -/
def resolveSingleFseTable (mode : SequenceCompressionMode) (maxSymbols : Nat)
    (maxAccLog : Nat) (data : ByteArray) (pos : Nat)
    (predefinedDist : Array Int32) (predefinedAccLog : Nat)
    (prevTable : Option FseTable := none) :
    Except String (FseTable × Nat) := do
  match mode with
  | .predefined =>
    let table ← buildFseTable predefinedDist predefinedAccLog
    return (table, pos)
  | .rle =>
    if data.size < pos + 1 then
      throw "Zstd: not enough data for RLE FSE table symbol"
    let symbol := data[pos]!
    return (buildRleFseTable symbol, pos + 1)
  | .fseCompressed =>
    let br : BitReader := { data, pos, bitOff := 0 }
    let (probs, accLog, br') ← decodeFseDistribution br maxSymbols maxAccLog
    let table ← buildFseTable probs accLog
    -- Advance to byte boundary after the consumed bits
    let afterPos := if br'.bitOff == 0 then br'.pos else br'.pos + 1
    return (table, afterPos)
  | .repeat =>
    match prevTable with
    | some table => return (table, pos)
    | none => throw "Zstd: Repeat mode (3) used but no previous FSE table available"

/-- Previous block's FSE tables for Repeat mode (mode 3). -/
structure PrevFseTables where
  /-- Previous block's literal length FSE table. -/
  litLen : Option FseTable := none
  /-- Previous block's offset FSE table. -/
  offset : Option FseTable := none
  /-- Previous block's match length FSE table. -/
  matchLen : Option FseTable := none

/-- Resolve all three FSE tables for sequence decoding from their compression modes
    (RFC 8878 §3.1.1.3.2.1). Tables are resolved in order: literal lengths, offsets,
    match lengths. Each may read data from `data` starting at `pos`.
    Accepts optional previous tables for Repeat mode support.
    Returns (litLenTable, offsetTable, matchLenTable, posAfterTables). -/
def resolveSequenceFseTables (modes : SequenceCompressionModes)
    (data : ByteArray) (pos : Nat)
    (prev : PrevFseTables := {}) :
    Except String (FseTable × FseTable × FseTable × Nat) := do
  let (litLenTable, pos) ← resolveSingleFseTable modes.litLenMode
    36 9 data pos predefinedLitLenDistribution 6 prev.litLen
  let (offsetTable, pos) ← resolveSingleFseTable modes.offsetMode
    32 8 data pos predefinedOffsetDistribution 5 prev.offset
  let (matchLenTable, pos) ← resolveSingleFseTable modes.matchLenMode
    53 9 data pos predefinedMatchLenDistribution 6 prev.matchLen
  return (litLenTable, offsetTable, matchLenTable, pos)

end Zip.Native
