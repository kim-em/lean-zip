import ZipTest.Helpers
import Zip.Native.DeflateDynamic

/-! Conformance tests for the chainless 2-way-bucket L1 matcher (`htMatch`,
    #2738). The roundtrip is already a theorem (`inflate_deflateRaw` covers
    level 1) and `PackedTokens` checks `lzMatchP.map unpackTok == lzMatch` at
    level 1, so this file targets the matcher's *distinctive* runtime
    properties on the compiled binary:

    - the three twins agree token-for-token (`htMatch = htMatchIter`,
      `htMatchIterP.map unpackTok = htMatchIter`) on the edge shapes;
    - every emitted reference honours **min match 4** and the encoder bounds;
    - the token stream resolves back to the input (native inflate roundtrip),
      including the empty / sub-3-byte / all-same / cyclic edge cases where
      the bucket table and interior insertion behave specially. -/

namespace ZipTest.HtMatch

open Zip.Native.Deflate

/-- The three matcher twins must agree, references must be encodable with
    length ≥ 4, and level-1 deflate must roundtrip through native inflate. -/
private def checkOne (label : String) (data : ByteArray) : IO Unit := do
  -- Twin agreement: recursive reference = iterative boxed.
  let boxed := htMatch data 32768
  let iter := htMatchIter data 32768
  unless boxed == iter do
    throw (IO.userError s!"{label}: htMatch ({boxed.size}) ≠ htMatchIter ({iter.size})")
  -- Packed twin agreement (compiled `@[inline]` packing / accumulator reuse).
  let packed := htMatchIterP data 32768
  unless packed.size == iter.size do
    throw (IO.userError s!"{label}: htMatchIterP size {packed.size} ≠ htMatchIter {iter.size}")
  for i in [0:iter.size] do
    unless unpackTok packed[i]! == iter[i]! do
      throw (IO.userError s!"{label}: packed token {i} ≠ boxed")
  -- Min-match-4 and encoder bounds on every reference.
  for tok in iter do
    match tok with
    | .literal _ => pure ()
    | .reference len dist =>
      unless 4 ≤ len ∧ len ≤ 258 ∧ 1 ≤ dist ∧ dist ≤ 32768 do
        throw (IO.userError s!"{label}: reference (len={len}, dist={dist}) out of bounds")
  -- Level-1 roundtrip through native inflate (exercises the wired dispatch).
  let compressed := deflateRaw data 1
  match Zip.Native.Inflate.inflate compressed with
  | .ok result =>
    unless result == data do
      throw (IO.userError s!"{label}: L1 roundtrip mismatch ({result.size} vs {data.size})")
  | .error e => throw (IO.userError s!"{label}: L1 inflate failed: {e}")

def tests : IO Unit := do
  IO.println "  HtMatch (chainless L1 matcher) tests..."
  -- Edge cases: empty, sub-3-byte (below the hash guard), exactly the
  -- min-match boundary, all-same (long matches → interior-insertion heavy),
  -- cyclic (period-3 references), random (mostly literals), real text.
  checkOne "empty" ByteArray.empty
  checkOne "one byte" (ByteArray.mk #[65])
  checkOne "two bytes" (ByteArray.mk #[65, 66])
  checkOne "three bytes" (ByteArray.mk #[65, 66, 67])
  checkOne "four same" (ByteArray.mk #[65, 65, 65, 65])
  checkOne "all same 4KB" (mkConstantData 4096)
  checkOne "cyclic 4KB" (mkCyclicData 4096)
  checkOne "random 4KB" (mkRandomData 4096)
  checkOne "text 64KB" (mkTextData 65536)
  checkOne "prng 32KB" (mkPrngData 32768)
  IO.println "  HtMatch tests passed."

end ZipTest.HtMatch
