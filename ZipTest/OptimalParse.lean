import ZipTest.Helpers
import Zip.Native.DeflateParse

/-! Tests for the near-optimal parsing support (#2496): candidate cache and
    cost model. The cache and cost tables are pure heuristics (they never
    enter correctness proofs), so these tests pin down their *intended*
    behaviour: recorded candidates are genuine matches with strictly
    increasing lengths, and cost tables price symbols per RFC 1951 fixed
    codes. -/

namespace ZipTest.OptimalParse

open Zip.Native.Deflate

/-- Build the whole-input candidate cache (single region). -/
private def cacheFor (data : ByteArray) : Array Nat × Array Nat :=
  let (lens, dists, _, _) := buildCache data
    (Array.replicate 65536 data.size) (Array.replicate data.size data.size)
    optChainDepth optCacheSlots 0 data.size 0
    (Array.replicate (optCacheSlots * data.size) 0)
    (Array.replicate (optCacheSlots * data.size) 0)
  (lens, dists)

/-- Check every recorded candidate at every position: genuine in-window
    backward match of the recorded length, encodable ranges, strictly
    increasing lengths across a position's slots. -/
private def checkCache (data : ByteArray) : IO Unit := do
  let (lens, dists) := cacheFor data
  for j in [0:data.size] do
    let mut prevLen := 0
    for k in [0:optCacheSlots] do
      let len := lens[optCacheSlots * j + k]!
      if len ≠ 0 then
        let dist := dists[optCacheSlots * j + k]!
        unless 3 ≤ len ∧ len ≤ 258 do
          throw (IO.userError s!"cache: bad len {len} at pos {j} slot {k}")
        unless 1 ≤ dist ∧ dist ≤ j ∧ dist ≤ 32768 do
          throw (IO.userError s!"cache: bad dist {dist} at pos {j} slot {k}")
        unless j + len ≤ data.size do
          throw (IO.userError s!"cache: overlong match at pos {j} slot {k}")
        unless prevLen < len do
          throw (IO.userError s!"cache: non-increasing len {len} after {prevLen} at pos {j}")
        for i in [0:len] do
          unless data[j + i]! == data[j - dist + i]! do
            throw (IO.userError s!"cache: byte mismatch at pos {j} slot {k} offset {i}")
        prevLen := len

def tests : IO Unit := do
  IO.println "  OptimalParse tests..."

  -- Candidate cache: genuine matches on assorted shapes.
  checkCache ("abcabcabcabcabcXabcabc".toUTF8)
  checkCache (mkConstantData 1024)        -- all-equal: 258-length matches, early stop
  checkCache (mkPrngData 2048)            -- incompressible: few/no candidates
  checkCache (mkCyclicData 4096)          -- 16-byte cycle
  checkCache (ByteArray.mk #[1, 2])       -- below minimum match size
  checkCache (ByteArray.empty)

  -- A position with multiple candidates must exist on text-like repetitive
  -- input (frontier has > 1 point): "aXab" then "ab" repeated gives both a
  -- short near match and longer farther ones at later positions.
  let s := "the quick brown fox the quick brown dog the quick brown fox".toUTF8
  let (lens, _) := cacheFor s
  let mut sawTwo := false
  for j in [0:s.size] do
    if lens[optCacheSlots * j + 1]! ≠ 0 then
      sawTwo := true
  unless sawTwo do
    throw (IO.userError "cache: expected some position with ≥ 2 candidates")

  -- Static (fixed-Huffman) cost tables, RFC 1951 §3.2.5–3.2.6 spot checks.
  let (litCost, lenCost, distCost) := staticCostTables
  assert! litCost.size == 256 && lenCost.size == 259 && distCost.size == 32769
  assert! litCost[65]! == 8        -- literals 0–143: 8 bits
  assert! litCost[200]! == 9       -- literals 144–255: 9 bits
  assert! lenCost[0]! == badCost && lenCost[2]! == badCost
  assert! lenCost[3]! == 7         -- sym 257 (7 bits) + 0 extra
  assert! lenCost[13]! == 8        -- sym 266 (7 bits) + 1 extra
  assert! lenCost[258]! == 8       -- sym 285 (8 bits) + 0 extra
  assert! distCost[0]! == badCost
  assert! distCost[1]! == 5        -- code 0 (5 bits) + 0 extra
  assert! distCost[5]! == 6        -- code 4 (5 bits) + 1 extra
  assert! distCost[32768]! == 18   -- code 29 (5 bits) + 13 extra

  -- Fitted tables: an unseen symbol costs the zero-frequency fallback, a
  -- frequent one costs its real (short) code, never 0 anywhere.
  let toks := #[LZ77Token.literal 97, .literal 97, .literal 97, .literal 98]
  let (flit, flen, fdist) := fittedCostTables toks
  assert! flit[97]! ≥ 1 && flit[97]! ≤ 15
  assert! flit[99]! == zeroFreqCodeLen      -- 'c' never seen
  assert! flit[97]! < flit[99]!
  for c in flit do assert! c ≥ 1
  assert! flen[3]! ≥ 1 && fdist[1]! ≥ 1

  IO.println "  OptimalParse tests passed"

end ZipTest.OptimalParse
