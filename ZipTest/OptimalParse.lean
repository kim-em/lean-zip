import ZipTest.Helpers
import Zip.Native.DeflateParse
import Zip.Native.DeflateDynamic
import Zip.Native.Inflate

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

/-- Reference LZ77 resolution (byte-at-a-time copy, overlapping matches
    repeat naturally). -/
private def resolveTokens (label : String) (tokens : Array LZ77Token) :
    IO ByteArray := do
  let mut out := ByteArray.empty
  for t in tokens do
    match t with
    | .literal b => out := out.push b
    | .reference len dist =>
      unless 1 ≤ dist ∧ dist ≤ out.size do
        throw (IO.userError s!"{label}: bad dist {dist} at out size {out.size}")
      unless 3 ≤ len ∧ len ≤ 258 do
        throw (IO.userError s!"{label}: bad len {len}")
      for _ in [0:len] do
        out := out.push out[out.size - dist]!
  return out

/-- Full pipeline check for the optimal parser on one input: token stream
    resolves back to the data, and a dynamic Huffman block built from it
    inflates back to the data (native verified decoder). -/
private def checkParse (label : String) (data : ByteArray) : IO Unit := do
  let toks := lz77OptimalIter data
  let back ← resolveTokens label toks
  unless back == data do
    throw (IO.userError s!"{label}: token resolution mismatch ({back.size} vs {data.size})")
  let blk := deflateDynamicBlock data toks
  match Zip.Native.Inflate.inflate blk with
  | .ok r =>
    unless r == data do
      throw (IO.userError s!"{label}: dynamic block roundtrip mismatch")
  | .error e => throw (IO.userError s!"{label}: inflate failed: {e}")

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

  -- Full parser: token resolution + dynamic-block roundtrip.
  checkParse "empty" ByteArray.empty
  checkParse "one" (ByteArray.mk #[42])
  checkParse "two" (ByteArray.mk #[42, 42])
  checkParse "three" (ByteArray.mk #[7, 7, 7])
  checkParse "hello" ("hello hello hello, world world!".toUTF8)
  checkParse "constant" (mkConstantData 1024)        -- dist-1 overlapping 258s
  checkParse "cyclic" (mkCyclicData 4096)
  checkParse "prng" (mkPrngData 4096)                -- incompressible: literals
  checkParse "text64k" (mkTextData 65536)
  -- Region boundary: sizes regionSize − 1 / exact / + 1, and matches that
  -- want to cross the boundary (cyclic data spanning multiple regions).
  checkParse "region-1" (mkConstantData (optRegionSize - 1))
  checkParse "region" (mkConstantData optRegionSize)
  checkParse "region+1" (mkConstantData (optRegionSize + 1))
  checkParse "region-cross" (mkCyclicData (optRegionSize + 1000))
  -- Adversarial perf shape: large all-equal input (early-stop + niceLen)
  -- across several regions.
  checkParse "constant-2M" (mkConstantData 2000000)

  -- Ratio canary on real text (catches cost-model degeneration, which all
  -- proofs would happily certify): the optimal parse must beat the level-9
  -- lazy/greedy parse when both are emitted as a single dynamic block.
  let alice ← IO.FS.readBinFile "bench/corpora/canterbury/alice29.txt"
  let sizeOpt := (deflateDynamicBlock alice (lz77OptimalIter alice)).size
  let sizeLazy := (deflateDynamicBlock alice (lzMatch alice 9)).size
  IO.println s!"    alice29.txt single-block: optimal {sizeOpt} vs lazy-9 {sizeLazy}"
  unless sizeOpt < sizeLazy do
    throw (IO.userError s!"ratio canary: optimal {sizeOpt} ≥ lazy-9 {sizeLazy}")

  -- Level-9 dispatch: the optimal candidate joins via pickSmaller. Verify
  -- the full deflateRaw output through the native (verified) decoder AND the
  -- zlib FFI (cross-implementation conformance), and that level 9 improves
  -- on level 8 on real text (the whole point of the feature).
  for (label, payload) in [("alice", alice), ("text", mkTextData 65536),
      ("prng", mkPrngData 65536), ("constant", mkConstantData 65536),
      ("cyclic", mkCyclicData 65536), ("tiny", ByteArray.mk #[1, 2, 3])] do
    let out := deflateRaw payload 9
    match Zip.Native.Inflate.inflate out with
    | .ok r =>
      unless r == payload do
        throw (IO.userError s!"deflateRaw-9 {label}: native roundtrip mismatch")
    | .error e => throw (IO.userError s!"deflateRaw-9 {label}: inflate failed: {e}")
    let ffi ← RawDeflate.decompress out
    unless ffi == payload do
      throw (IO.userError s!"deflateRaw-9 {label}: FFI conformance mismatch")
  let raw9 := (deflateRaw alice 9).size
  let raw8 := (deflateRaw alice 8).size
  IO.println s!"    alice29.txt deflateRaw: level 9 {raw9} vs level 8 {raw8}"
  unless raw9 < raw8 do
    throw (IO.userError s!"deflateRaw: level 9 {raw9} did not beat level 8 {raw8}")
  -- Incompressible input must still fall back to the stored block.
  let prng := mkPrngData 65536
  unless (deflateRaw prng 9).size ≤ prng.size + 600 do
    throw (IO.userError "deflateRaw-9: incompressible input expanded past stored bound")
  -- Inputs above the memory gate skip the optimal candidate but roundtrip.
  let big := mkConstantData (optimalMaxSize + 1)
  match Zip.Native.Inflate.inflate (deflateRaw big 9) (big.size + 1) with
  | .ok r =>
    unless r == big do
      throw (IO.userError "deflateRaw-9 above-gate: roundtrip mismatch")
  | .error e => throw (IO.userError s!"deflateRaw-9 above-gate: inflate failed: {e}")

  IO.println "  OptimalParse tests passed"

end ZipTest.OptimalParse
