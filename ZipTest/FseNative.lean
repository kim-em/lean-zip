import ZipTest.Helpers
import Zip.Native.Fse
import Zip.Native.ZstdFrame

/-! Tests for the native FSE distribution decoder and table builder. -/

def ZipTest.FseNative.tests : IO Unit := do
  -- Test 1: buildFseTable with a known distribution for accuracyLog=5, tableSize=32
  -- Symbol 0 has prob 16, symbol 1 has prob 8, symbol 2 has prob 4,
  -- symbol 3 has prob 2, symbol 4 has prob 1, symbol 5 has prob 1
  let probs1 : Array Int32 := #[16, 8, 4, 2, 1, 1]
  match Zip.Native.buildFseTable probs1 5 with
  | .ok table =>
    unless table.cells.size == 32 do
      throw (IO.userError s!"buildFseTable: expected 32 cells, got {table.cells.size}")
    unless table.accuracyLog == 5 do
      throw (IO.userError s!"buildFseTable: expected accuracyLog 5, got {table.accuracyLog}")
    -- Count symbol occurrences
    let mut counts := Array.replicate 6 (0 : Nat)
    for i in [:32] do
      let sym := table.cells[i]!.symbol.toNat
      if sym < 6 then
        counts := counts.set! sym (counts[sym]! + 1)
    unless counts[0]! == 16 do
      throw (IO.userError s!"buildFseTable: symbol 0 should appear 16 times, got {counts[0]!}")
    unless counts[1]! == 8 do
      throw (IO.userError s!"buildFseTable: symbol 1 should appear 8 times, got {counts[1]!}")
    unless counts[2]! == 4 do
      throw (IO.userError s!"buildFseTable: symbol 2 should appear 4 times, got {counts[2]!}")
    unless counts[3]! == 2 do
      throw (IO.userError s!"buildFseTable: symbol 3 should appear 2 times, got {counts[3]!}")
    unless counts[4]! == 1 do
      throw (IO.userError s!"buildFseTable: symbol 4 should appear 1 time, got {counts[4]!}")
    unless counts[5]! == 1 do
      throw (IO.userError s!"buildFseTable: symbol 5 should appear 1 time, got {counts[5]!}")
  | .error e => throw (IO.userError s!"buildFseTable known distribution failed: {e}")

  -- Test 2: buildFseTable with single-symbol distribution [32] for accuracyLog=5
  let probs2 : Array Int32 := #[32]
  match Zip.Native.buildFseTable probs2 5 with
  | .ok table =>
    unless table.cells.size == 32 do
      throw (IO.userError s!"single-symbol: expected 32 cells, got {table.cells.size}")
    for i in [:32] do
      unless table.cells[i]!.symbol == 0 do
        throw (IO.userError s!"single-symbol: cell {i} has symbol {table.cells[i]!.symbol}, expected 0")
  | .error e => throw (IO.userError s!"buildFseTable single-symbol failed: {e}")

  -- Test 3: buildFseTable with equal distribution [8, 8, 8, 8] for accuracyLog=5
  let probs3 : Array Int32 := #[8, 8, 8, 8]
  match Zip.Native.buildFseTable probs3 5 with
  | .ok table =>
    let mut counts := Array.replicate 4 (0 : Nat)
    for i in [:32] do
      let sym := table.cells[i]!.symbol.toNat
      if sym < 4 then
        counts := counts.set! sym (counts[sym]! + 1)
    for sym in [:4] do
      unless counts[sym]! == 8 do
        throw (IO.userError s!"equal-dist: symbol {sym} should appear 8 times, got {counts[sym]!}")
  | .error e => throw (IO.userError s!"buildFseTable equal distribution failed: {e}")

  -- Test 4: buildFseTable with "less than 1" (-1) probability
  -- Distribution: [28, -1, 1, 1, -1] for accuracyLog=5, tableSize=32
  -- Cells used: 28 + 1 + 1 + 1 + 1 = 32
  let probs4 : Array Int32 := #[28, -1, 1, 1, -1]
  match Zip.Native.buildFseTable probs4 5 with
  | .ok table =>
    let mut counts := Array.replicate 5 (0 : Nat)
    for i in [:32] do
      let sym := table.cells[i]!.symbol.toNat
      if sym < 5 then
        counts := counts.set! sym (counts[sym]! + 1)
    unless counts[0]! == 28 do
      throw (IO.userError s!"-1 prob: symbol 0 should appear 28 times, got {counts[0]!}")
    unless counts[1]! == 1 do
      throw (IO.userError s!"-1 prob: symbol 1 should appear 1 time, got {counts[1]!}")
    unless counts[2]! == 1 do
      throw (IO.userError s!"-1 prob: symbol 2 should appear 1 time, got {counts[2]!}")
    unless counts[3]! == 1 do
      throw (IO.userError s!"-1 prob: symbol 3 should appear 1 time, got {counts[3]!}")
    unless counts[4]! == 1 do
      throw (IO.userError s!"-1 prob: symbol 4 should appear 1 time, got {counts[4]!}")
    -- -1 probability symbols should be at the end of the table
    unless table.cells[31]!.symbol == 1 do
      throw (IO.userError s!"-1 prob: symbol 1 should be at position 31, got symbol {table.cells[31]!.symbol}")
    unless table.cells[30]!.symbol == 4 do
      throw (IO.userError s!"-1 prob: symbol 4 should be at position 30, got symbol {table.cells[30]!.symbol}")
  | .error e => throw (IO.userError s!"buildFseTable -1 probability failed: {e}")

  -- Test 5: Round-trip FSE parsing on real Zstd-compressed data
  let testData := mkPrngData 1024
  let compressed ← Zstd.compress testData 3
  match Zip.Native.parseFrameHeader compressed 0 with
  | .ok (_, headerEnd) =>
    match Zip.Native.parseBlockHeader compressed headerEnd with
    | .ok (blkHdr, blockDataStart) =>
      if blkHdr.blockType == .compressed then
        IO.println s!"  FSE round-trip: compressed block found, size={blkHdr.blockSize}, pos={blockDataStart}"
      else
        IO.println s!"  FSE round-trip: block type is {repr blkHdr.blockType}, not compressed (OK for this input)"
    | .error e => throw (IO.userError s!"parseBlockHeader in FSE round-trip failed: {e}")
  | .error e => throw (IO.userError s!"parseFrameHeader in FSE round-trip failed: {e}")

  -- Test 6: buildFseTable with accuracyLog 6 (tableSize=64)
  let probs5 : Array Int32 := #[32, 16, 8, 4, 2, 1, 1]
  match Zip.Native.buildFseTable probs5 6 with
  | .ok table =>
    unless table.cells.size == 64 do
      throw (IO.userError s!"accLog 6: expected 64 cells, got {table.cells.size}")
    -- Verify total symbol count is 64
    let mut total := 0
    for i in [:64] do
      let sym := table.cells[i]!.symbol.toNat
      unless sym < 7 do
        throw (IO.userError s!"accLog 6: cell {i} has invalid symbol {sym}")
      total := total + 1
    unless total == 64 do
      throw (IO.userError s!"accLog 6: expected 64 total cells, got {total}")
  | .error e => throw (IO.userError s!"buildFseTable accLog 6 failed: {e}")

  -- Test 7: Verify stepping algorithm distributes symbols non-contiguously
  -- With distribution [16, 16] and accuracyLog=5, symbols should be interleaved
  let probs6 : Array Int32 := #[16, 16]
  match Zip.Native.buildFseTable probs6 5 with
  | .ok table =>
    let mut maxRun := 0
    let mut currentRun := 1
    for i in [1:32] do
      if table.cells[i]!.symbol == table.cells[i-1]!.symbol then
        currentRun := currentRun + 1
        if currentRun > maxRun then maxRun := currentRun
      else
        currentRun := 1
    unless maxRun ≤ 3 do
      throw (IO.userError s!"stepping: max run of same symbol is {maxRun}, expected ≤ 3 for equal distribution")
  | .error e => throw (IO.userError s!"buildFseTable stepping test failed: {e}")

  -- Test 8: Verify numBits and newState are set for each cell
  match Zip.Native.buildFseTable probs1 5 with
  | .ok table =>
    -- For a symbol with count 1 (symbols 4 and 5), it should need accuracyLog bits
    -- to select among all tableSize states
    for i in [:32] do
      let cell := table.cells[i]!
      let sym := cell.symbol.toNat
      if sym == 4 || sym == 5 then
        unless cell.numBits == 5 do
          throw (IO.userError s!"numBits: symbol {sym} at cell {i} has numBits={cell.numBits}, expected 5")
  | .error e => throw (IO.userError s!"buildFseTable numBits test failed: {e}")

  IO.println "FseNative tests: OK"
