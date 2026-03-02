import Zip.Native.BitReader

/-!
  Finite State Entropy (FSE) distribution decoder and table builder (RFC 8878 §4.1.1).

  FSE is the core entropy coding used in Zstandard compressed blocks. This module
  implements two steps:
  1. **Distribution decoding**: read a compact probability distribution from the
     bitstream, producing an array of normalized counts (one per symbol).
  2. **Table construction**: build the FSE decoding table from the distribution,
     using the position-stepping algorithm specified in RFC 8878 §4.1.1.

  The decoding table has `1 << accuracyLog` cells. Each cell stores the symbol
  it decodes to, plus the number of bits to read and the baseline for computing
  the next state during decoding.

  Also provides the three predefined distribution arrays from RFC 8878 §6 and
  a function to build them into ready-to-use FSE decoding tables.
-/

namespace Zip.Native

/-- A single cell in an FSE decoding table. -/
structure FseCell where
  /-- The symbol this cell decodes to. -/
  symbol : UInt16 := 0
  /-- Number of additional bits to read from the bitstream. -/
  numBits : UInt8 := 0
  /-- Baseline value added to the read bits to compute the next state. -/
  newState : UInt16 := 0
  deriving Repr, Inhabited

/-- An FSE decoding table with its accuracy log and cell array. -/
structure FseTable where
  /-- Log2 of the table size. -/
  accuracyLog : Nat
  /-- Decoding cells, length = 1 << accuracyLog. -/
  cells : Array FseCell
  deriving Repr

/-- Convert Int32 to Nat, clamping negative values to 0. -/
private def int32ToNat (x : Int32) : Nat :=
  if x.toInt < 0 then 0 else x.toInt.toNat

/-- Decode an FSE distribution (normalized probabilities) from a bitstream.
    `maxSymbols` is the maximum number of symbols allowed (e.g. 256 for literals,
    52 for match lengths, 36 for literals lengths).
    Returns (probability array, accuracy log, updated BitReader).
    Probabilities: positive = count, -1 = "less than 1" (occupies 1 cell),
    0 = symbol not present. -/
def decodeFseDistribution (br : Zip.Native.BitReader) (maxSymbols : Nat)
    (maxAccLog : Nat := 11) :
    Except String (Array Int32 × Nat × Zip.Native.BitReader) := do
  -- Read accuracy log: 4 bits, value + 5
  let (accRaw, br) ← br.readBits 4
  let accuracyLog := accRaw.toNat + 5
  if accuracyLog > maxAccLog then
    throw s!"FSE: accuracy log {accuracyLog} exceeds maximum {maxAccLog}"
  let tableSize := 1 <<< accuracyLog
  let mut remaining := tableSize
  let mut probs : Array Int32 := #[]
  let mut symbolNum := 0
  let mut br := br
  while remaining > 0 && symbolNum < maxSymbols do
    -- Determine how many bits to read for this probability value.
    -- We need to represent values in [0, remaining + 1] (inclusive).
    -- The value 0 maps to probability -1, value 1 maps to probability 0, etc.
    -- So maximum encodable value = remaining + 1.
    let maxVal := remaining + 1
    -- Number of bits needed: ceil(log2(maxVal + 1))
    let bitsNeeded := Nat.log2 maxVal + 1
    -- The "small" threshold: values below this use (bitsNeeded - 1) bits
    let lowThreshold := (1 <<< bitsNeeded) - 1 - maxVal
    let (rawBits, br') ← br.readBits (bitsNeeded - 1)
    br := br'
    let val ← if rawBits.toNat < lowThreshold then
      pure rawBits.toNat
    else
      -- Read one more bit
      let (extraBit, br') ← br.readBits 1
      br := br'
      let combined := rawBits.toNat * 2 + extraBit.toNat
      if combined >= lowThreshold then
        pure (combined - lowThreshold)
      else
        pure rawBits.toNat
    -- Convert value to probability: value 0 → prob -1, value n → prob (n - 1)
    let prob : Int32 := Int32.ofNat val - 1
    if prob == 0 then
      -- Zero probability: read 2-bit repeat count for consecutive zeros
      probs := probs.push 0
      symbolNum := symbolNum + 1
      let mut doRepeat := true
      while doRepeat do
        let (repeatBits, br') ← br.readBits 2
        br := br'
        let repeatCount := repeatBits.toNat
        for _ in [:repeatCount] do
          if symbolNum < maxSymbols then
            probs := probs.push 0
            symbolNum := symbolNum + 1
        doRepeat := repeatCount == 3
    else
      probs := probs.push prob
      symbolNum := symbolNum + 1
      if prob == -1 then
        remaining := remaining - 1
      else
        let probNat := int32ToNat prob
        if probNat > remaining then
          throw s!"FSE: probability {prob} exceeds remaining {remaining}"
        remaining := remaining - probNat
  if remaining != 0 then
    throw s!"FSE: probabilities don't sum to table size: {remaining} remaining"
  return (probs, accuracyLog, br)

/-- Build an FSE decoding table from a probability distribution.
    `probs` is the array from `decodeFseDistribution`.
    `accuracyLog` determines the table size (1 << accuracyLog cells). -/
def buildFseTable (probs : Array Int32) (accuracyLog : Nat) :
    Except String FseTable := do
  let tableSize := 1 <<< accuracyLog
  let tableMask := tableSize - 1
  -- Step constant: (tableSize >> 1) + (tableSize >> 3) + 3
  let step := (tableSize >>> 1) + (tableSize >>> 3) + 3
  let mut cells : Array FseCell := Array.replicate tableSize default
  -- Track which positions are occupied (for -1 probability symbols placed at end)
  let mut occupied := Array.replicate tableSize false
  -- First pass: place "less than 1" probability symbols at end of table
  let mut highPos := tableSize - 1
  for sym in [:probs.size] do
    if probs[sym]! == -1 then
      cells := cells.set! highPos { symbol := sym.toUInt16 }
      occupied := occupied.set! highPos true
      highPos := highPos - 1
  -- Second pass: distribute remaining symbols using stepping algorithm
  let mut position := 0
  for sym in [:probs.size] do
    let prob := probs[sym]!
    if prob <= 0 then continue
    for _ in [:int32ToNat prob] do
      -- Skip occupied positions (from -1 symbols)
      while occupied[position]! do
        position := (position + step) &&& tableMask
      cells := cells.set! position { symbol := sym.toUInt16 }
      position := (position + step) &&& tableMask
  -- Third pass: compute numBits and newState for each cell
  -- For each symbol, count how many cells it has
  let mut symbolCounts := Array.replicate probs.size (0 : Nat)
  for i in [:tableSize] do
    let sym := cells[i]!.symbol.toNat
    if sym < symbolCounts.size then
      symbolCounts := symbolCounts.set! sym (symbolCounts[sym]! + 1)
  -- For each symbol, compute the number of bits and assign states
  let mut symbolStateIndex := Array.replicate probs.size (0 : Nat)
  for i in [:tableSize] do
    let sym := cells[i]!.symbol.toNat
    if sym >= probs.size then continue
    let count := symbolCounts[sym]!
    if count == 0 then continue
    -- highBit = floor(log2(count))
    let highBit := Nat.log2 count
    -- Number of states that need an extra bit
    let doubleCells := (1 <<< (highBit + 1)) - count
    let stateIdx := symbolStateIndex[sym]!
    let (numBits, baseline) :=
      if stateIdx < doubleCells then
        (accuracyLog - highBit,
         (stateIdx + doubleCells) <<< (accuracyLog - highBit))
      else
        (accuracyLog - highBit - 1,
         (stateIdx - doubleCells) <<< (accuracyLog - highBit - 1))
    cells := cells.set! i
      { symbol := cells[i]!.symbol, numBits := numBits.toUInt8, newState := baseline.toUInt16 }
    symbolStateIndex := symbolStateIndex.set! sym (stateIdx + 1)
  return { accuracyLog, cells }

-- ============================================================================
-- Predefined FSE distribution tables (RFC 8878 §6)
-- ============================================================================

/-- Predefined literal length distribution (RFC 8878 §6, Table 15).
    36 symbols (0–35), accuracyLog = 6, table size = 64. -/
def predefinedLitLenDistribution : Array Int32 :=
  #[ 4,  3,  2,  2,  2,  2,  2,  2,  2,  2,  2,  2,  2,  1,  1,  1,
     2,  2,  2,  2,  2,  2,  2,  2,  2,  3,  2,  1,  1,  1,  1,  1,
    -1, -1, -1, -1]

/-- Predefined match length distribution (RFC 8878 §6, Table 16).
    53 symbols (0–52), accuracyLog = 6, table size = 64. -/
def predefinedMatchLenDistribution : Array Int32 :=
  #[ 1,  4,  3,  2,  2,  2,  2,  2,  2,  1,  1,  1,  1,  1,  1,  1,
     1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,
     1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1, -1, -1,
    -1, -1, -1, -1, -1]

/-- Predefined offset distribution (RFC 8878 §6, Table 17).
    29 symbols (0–28), accuracyLog = 5, table size = 32. -/
def predefinedOffsetDistribution : Array Int32 :=
  #[ 1,  1,  1,  1,  1,  1,  2,  2,  2,  1,  1,  1,  1,  1,  1,  1,
     1,  1,  1,  1,  1,  1,  1,  1, -1, -1, -1, -1, -1]

/-- Build the three predefined FSE decoding tables from the hardcoded
    distributions in RFC 8878 §6. Returns (litLenTable, matchLenTable, offsetTable). -/
def buildPredefinedFseTables : Except String (FseTable × FseTable × FseTable) := do
  let llTable ← buildFseTable predefinedLitLenDistribution 6
  let mlTable ← buildFseTable predefinedMatchLenDistribution 6
  let ofTable ← buildFseTable predefinedOffsetDistribution 5
  return (llTable, mlTable, ofTable)

end Zip.Native
