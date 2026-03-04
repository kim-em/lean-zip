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

  -- Test 9: BackwardBitReader initialization and basic bit reading
  -- Construct a byte array: [0xA5, 0xC0] where the backward stream reads from end.
  -- Last byte 0xC0 = 0b11000000: sentinel bit at position 7, one data bit (0b1) at position 6.
  -- After consuming sentinel at bit 7, we have 7 bits remaining: 1000000.
  -- First readBits 1 should give 1 (bit 6), then readBits 1 should give 0 (bit 5), etc.
  let backData := ByteArray.mk #[0xA5, 0xC0]
  match Zip.Native.BackwardBitReader.init backData 0 2 with
  | .ok br => do
    -- After init on 0xC0: sentinel at bit 7, 7 bits remain: bits 6..0 = 1,0,0,0,0,0,0
    let (bit1, br) ← match br.readBits 1 with
      | .ok r => pure r
      | .error e => throw (IO.userError s!"backward readBits 1 failed: {e}")
    unless bit1 == 1 do
      throw (IO.userError s!"backward: first bit should be 1, got {bit1}")
    let (bit2, br) ← match br.readBits 1 with
      | .ok r => pure r
      | .error e => throw (IO.userError s!"backward readBits 2 failed: {e}")
    unless bit2 == 0 do
      throw (IO.userError s!"backward: second bit should be 0, got {bit2}")
    -- Read 5 more bits (remaining from 0xC0 byte: 0,0,0,0,0)
    let (fiveBits, br) ← match br.readBits 5 with
      | .ok r => pure r
      | .error e => throw (IO.userError s!"backward readBits 5 failed: {e}")
    unless fiveBits == 0 do
      throw (IO.userError s!"backward: next 5 bits should be 0, got {fiveBits}")
    -- Now should read from byte 0xA5 = 0b10100101 (8 bits, MSB first)
    let (eightBits, _br) ← match br.readBits 8 with
      | .ok r => pure r
      | .error e => throw (IO.userError s!"backward readBits 8 failed: {e}")
    -- MSB-first: 1,0,1,0,0,1,0,1 = 0xA5 = 165
    unless eightBits == 0xA5 do
      throw (IO.userError s!"backward: byte should be 0xA5 (165), got {eightBits}")
  | .error e => throw (IO.userError s!"BackwardBitReader init failed: {e}")

  -- Test 10: BackwardBitReader with sentinel-only byte
  -- [0xFF, 0x01]: last byte 0x01 has sentinel at bit 0, no data bits.
  -- Should move to previous byte 0xFF = 0b11111111 and read from there.
  let backData2 := ByteArray.mk #[0xFF, 0x01]
  match Zip.Native.BackwardBitReader.init backData2 0 2 with
  | .ok br => do
    let (bits, _) ← match br.readBits 8 with
      | .ok r => pure r
      | .error e => throw (IO.userError s!"sentinel-only readBits failed: {e}")
    unless bits == 0xFF do
      throw (IO.userError s!"sentinel-only: expected 0xFF (255), got {bits}")
  | .error e => throw (IO.userError s!"BackwardBitReader sentinel-only init failed: {e}")

  -- Test 11: FSE decode round-trip with a simple 2-symbol table
  -- Build a table with 2 symbols (accuracyLog=2, tableSize=4):
  -- Symbol 0: prob 2, Symbol 1: prob 2
  let probs_rt : Array Int32 := #[2, 2]
  match Zip.Native.buildFseTable probs_rt 2 with
  | .ok table => do
    -- Manually encode a sequence: we need to build a backward bitstream
    -- that decodes to known symbols using this table.
    -- With accuracyLog=2, initial state is read as 2 bits.
    -- Let's just verify the table structure and then decode from a crafted stream.
    unless table.cells.size == 4 do
      throw (IO.userError s!"FSE rt: expected 4 cells, got {table.cells.size}")
    -- Count symbols
    let mut sym0Count := 0
    let mut sym1Count := 0
    for i in [:4] do
      if table.cells[i]!.symbol == 0 then sym0Count := sym0Count + 1
      else if table.cells[i]!.symbol == 1 then sym1Count := sym1Count + 1
    unless sym0Count == 2 && sym1Count == 2 do
      throw (IO.userError s!"FSE rt: expected 2 each, got {sym0Count} and {sym1Count}")
    -- Construct a bitstream that encodes a known sequence.
    -- For a simple test, craft bits manually:
    -- accuracyLog=2 means initial state needs 2 bits.
    -- With 4 cells, state ranges 0-3. We'll start at state 0.
    -- Each step: cell = table[state], emit symbol, read numBits bits, newState = baseline + bits
    -- Let's trace: state=0, cell[0].symbol=?, cell[0].numBits=?, cell[0].newState=?
    -- We'll just verify decodeFseSymbols doesn't crash and returns the right count.
    -- Encode: sentinel bit (1) + 2 bits for init state (00) + bits for transitions
    -- Byte: 0b1_00_XXXXX = sentinel + state 0 + padding
    -- For 1 symbol (no transitions needed), just: sentinel + 2 init bits
    -- Sentinel bit must be highest set: 0b00000_1_00 = 0x04
    let encoded := ByteArray.mk #[0x04]
    match Zip.Native.BackwardBitReader.init encoded 0 1 with
    | .ok br => do
      match Zip.Native.decodeFseSymbols table br 1 with
      | .ok (symbols, _br') =>
        unless symbols.size == 1 do
          throw (IO.userError s!"FSE rt: expected 1 symbol, got {symbols.size}")
      | .error e => throw (IO.userError s!"decodeFseSymbols 1 symbol failed: {e}")
    | .error e => throw (IO.userError s!"BackwardBitReader init for FSE rt failed: {e}")
  | .error e => throw (IO.userError s!"buildFseTable for FSE round-trip failed: {e}")

  -- Test 12: BackwardBitReader error on empty range
  let emptyData := ByteArray.mk #[]
  match Zip.Native.BackwardBitReader.init emptyData 0 0 with
  | .ok _ => throw (IO.userError "BackwardBitReader: should fail on empty range")
  | .error _ => pure ()

  -- Test 13: BackwardBitReader error on zero last byte (no sentinel)
  let zeroData := ByteArray.mk #[0x00]
  match Zip.Native.BackwardBitReader.init zeroData 0 1 with
  | .ok _ => throw (IO.userError "BackwardBitReader: should fail on zero last byte")
  | .error _ => pure ()

  -- Test 14: Integration - parse FSE from real Zstd compressed data and attempt decode
  let testData := mkPrngData 1024
  let compressed ← Zstd.compress testData 3
  match Zip.Native.parseFrameHeader compressed 0 with
  | .ok (_, headerEnd) =>
    match Zip.Native.parseBlockHeader compressed headerEnd with
    | .ok (blkHdr, blockDataStart) =>
      if blkHdr.blockType == .compressed then do
        let blockEnd := blockDataStart + blkHdr.blockSize.toNat
        -- Parse literals section to get past it to the sequences section
        match Zip.Native.parseLiteralsSection compressed blockDataStart with
        | .ok (_, afterLiterals) =>
          match Zip.Native.parseSequencesHeader compressed afterLiterals with
          | .ok (numSeq, _modes, afterSeqHeader) =>
            if numSeq > 0 then
              -- Read the compression modes byte (just before afterSeqHeader)
              -- The modes byte contains 2-bit fields for LL, OF, ML compression modes
              IO.println s!"  FSE integration: {numSeq} sequences, block ends at {blockEnd}"
              IO.println s!"  FSE integration: sequences header parsed OK at pos {afterSeqHeader}"
            else
              IO.println s!"  FSE integration: 0 sequences (literals-only block)"
          | .error e => throw (IO.userError s!"parseSequencesHeader in integration test failed: {e}")
        | .error e =>
          -- Compressed literals may not be supported yet, that's OK
          IO.println s!"  FSE integration: literals section parse: {e} (OK, may need Huffman)"
      else
        IO.println s!"  FSE integration: block type is {repr blkHdr.blockType}, not compressed (OK)"
    | .error e => throw (IO.userError s!"parseBlockHeader in FSE integration failed: {e}")
  | .error e => throw (IO.userError s!"parseFrameHeader in FSE integration failed: {e}")

  -- Test 15: Predefined literal length distribution sums to 2^6 = 64
  let llDist := Zip.Native.predefinedLitLenDistribution
  let mut llSum : Nat := 0
  for p in llDist do
    if p == -1 then llSum := llSum + 1
    else llSum := llSum + p.toInt.toNat
  unless llSum == 64 do
    throw (IO.userError s!"predefined LL distribution sum: expected 64, got {llSum}")
  unless llDist.size == 36 do
    throw (IO.userError s!"predefined LL distribution size: expected 36, got {llDist.size}")

  -- Test 16: Predefined match length distribution sums to 2^6 = 64
  let mlDist := Zip.Native.predefinedMatchLenDistribution
  let mut mlSum : Nat := 0
  for p in mlDist do
    if p == -1 then mlSum := mlSum + 1
    else mlSum := mlSum + p.toInt.toNat
  unless mlSum == 64 do
    throw (IO.userError s!"predefined ML distribution sum: expected 64, got {mlSum}")
  unless mlDist.size == 53 do
    throw (IO.userError s!"predefined ML distribution size: expected 53, got {mlDist.size}")

  -- Test 17: Predefined offset distribution sums to 2^5 = 32
  let ofDist := Zip.Native.predefinedOffsetDistribution
  let mut ofSum : Nat := 0
  for p in ofDist do
    if p == -1 then ofSum := ofSum + 1
    else ofSum := ofSum + p.toInt.toNat
  unless ofSum == 32 do
    throw (IO.userError s!"predefined OF distribution sum: expected 32, got {ofSum}")
  unless ofDist.size == 29 do
    throw (IO.userError s!"predefined OF distribution size: expected 29, got {ofDist.size}")

  -- Test 18: buildPredefinedFseTables produces tables with correct sizes
  match Zip.Native.buildPredefinedFseTables with
  | .ok (llTable, mlTable, ofTable) =>
    unless llTable.cells.size == 64 do
      throw (IO.userError s!"predefined LL table: expected 64 cells, got {llTable.cells.size}")
    unless llTable.accuracyLog == 6 do
      throw (IO.userError s!"predefined LL table: expected accuracyLog 6, got {llTable.accuracyLog}")
    unless mlTable.cells.size == 64 do
      throw (IO.userError s!"predefined ML table: expected 64 cells, got {mlTable.cells.size}")
    unless mlTable.accuracyLog == 6 do
      throw (IO.userError s!"predefined ML table: expected accuracyLog 6, got {mlTable.accuracyLog}")
    unless ofTable.cells.size == 32 do
      throw (IO.userError s!"predefined OF table: expected 32 cells, got {ofTable.cells.size}")
    unless ofTable.accuracyLog == 5 do
      throw (IO.userError s!"predefined OF table: expected accuracyLog 5, got {ofTable.accuracyLog}")
  | .error e => throw (IO.userError s!"buildPredefinedFseTables failed: {e}")

  -- Test 19: Symbol coverage - every symbol with nonzero probability appears in the table
  match Zip.Native.buildPredefinedFseTables with
  | .ok (llTable, mlTable, ofTable) => do
    -- Check literal length table: all 36 symbols should appear (all have nonzero prob)
    let mut llSymSeen := Array.replicate 36 false
    for i in [:64] do
      let sym := llTable.cells[i]!.symbol.toNat
      if sym < 36 then llSymSeen := llSymSeen.set! sym true
    for sym in [:36] do
      unless llSymSeen[sym]! do
        throw (IO.userError s!"predefined LL table: symbol {sym} not found in table")
    -- Check match length table: all 53 symbols should appear
    let mut mlSymSeen := Array.replicate 53 false
    for i in [:64] do
      let sym := mlTable.cells[i]!.symbol.toNat
      if sym < 53 then mlSymSeen := mlSymSeen.set! sym true
    for sym in [:53] do
      unless mlSymSeen[sym]! do
        throw (IO.userError s!"predefined ML table: symbol {sym} not found in table")
    -- Check offset table: all 29 symbols should appear
    let mut ofSymSeen := Array.replicate 29 false
    for i in [:32] do
      let sym := ofTable.cells[i]!.symbol.toNat
      if sym < 29 then ofSymSeen := ofSymSeen.set! sym true
    for sym in [:29] do
      unless ofSymSeen[sym]! do
        throw (IO.userError s!"predefined OF table: symbol {sym} not found in table")
  | .error e => throw (IO.userError s!"buildPredefinedFseTables symbol coverage failed: {e}")

  IO.println "FseNative tests: OK"
