import ZipTest.Helpers
import Zip.Native.ZstdFrame

/-! End-to-end Zstd conformance tests: FFI compress → native decompress roundtrip
    across compression levels, data patterns, and input sizes. Validates that the
    native decompressor correctly handles real-world Zstd frames produced by the
    reference implementation. -/

/-- Generate sequential bytes (0, 1, 2, ..., 255, 0, 1, ...) of the given size. -/
private def mkSequentialData (size : Nat) : ByteArray := Id.run do
  let mut result := ByteArray.empty
  for i in [:size] do
    result := result.push (i % 256).toUInt8
  return result

/-- Test a single FFI compress → native decompress roundtrip. -/
private def testRoundtrip (input : ByteArray) (level : UInt8)
    (label : String) : IO Bool := do
  let compressed ← Zstd.compress input level
  match Zip.Native.decompressZstd compressed with
  | .ok result =>
    if result.data == input.data then
      return true
    else
      IO.eprintln s!"  FAIL {label}: content mismatch (expected {input.size}, got {result.size})"
      return false
  | .error e =>
      IO.eprintln s!"  FAIL {label}: {e}"
      return false

def ZipTest.ZstdConformance.tests : IO Unit := do
  -- === Conformance test matrix ===
  -- 4 levels × 4 patterns × 3 sizes = 48 combinations
  let levels : Array UInt8 := #[1, 3, 9, 19]
  let sizes : Array Nat := #[100, 10240, 102400]
  let patternNames := #["zeros", "sequential", "text", "prng"]

  let mut passed : Nat := 0
  let mut failed : Nat := 0

  for level in levels do
    for patIdx in [:patternNames.size] do
      let patName := patternNames[patIdx]!
      for size in sizes do
        let input := match patIdx with
          | 0 => mkConstantData size
          | 1 => mkSequentialData size
          | 2 => mkTextData size
          | _ => mkPrngData size
        let label := s!"level={level} pattern={patName} size={sizeName size}"
        if ← testRoundtrip input level label then
          passed := passed + 1
        else
          failed := failed + 1

  let total := passed + failed
  IO.println s!"Conformance matrix: {passed}/{total} passed, {failed} failures"
  if failed > 0 then
    throw (IO.userError s!"Zstd conformance: {failed} test failures")

  -- === Multi-block frame tests ===
  -- 1MB input forces multiple blocks at most compression levels
  let bigSize := 1048576
  let bigInput := mkTextData bigSize
  for level in #[(1 : UInt8), 3] do
    let label := s!"multi-block level={level} size=1MB"
    if ← testRoundtrip bigInput level label then
      IO.println s!"  Multi-block {label}: OK"
    else
      throw (IO.userError s!"Multi-block test failed: {label}")

  IO.println "ZstdConformance tests: OK"
