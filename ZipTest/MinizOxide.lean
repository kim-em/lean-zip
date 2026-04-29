import ZipTest.Helpers

/-! Smoke tests for the Track D Phase 0c miniz_oxide comparator.

When the project is built without cargo+rustc the FFI raises an
`IO.userError` containing `"miniz_oxide: not built with Rust support"`;
we treat that as a clean skip so CI on minimal toolchains keeps
passing. With the Rust shim available the tests exercise:

* miniz_oxide compress + miniz_oxide decompress roundtrip,
* miniz_oxide compress + zlib FFI decompress (ecosystem cross-check),
* zlib FFI compress + miniz_oxide decompress (the other direction),
* the decompression-limit cap (`maxDecompressedSize`).
-/

namespace ZipTest.MinizOxide

private def disabledMarker : String := "miniz_oxide: not built with Rust support"

/-- Either the action succeeds (and we run the continuation), or it
    fails with the disabled-marker substring (in which case we skip the
    rest with a noisy console line). Any other error is propagated. -/
private def withMiniz (description : String) (action : IO α) (k : α → IO Unit) : IO Unit := do
  let result ← action.toBaseIO
  match result with
  | .ok x => k x
  | .error e =>
    let msg := toString e
    if msg.contains disabledMarker then
      IO.println s!"MinizOxide tests skipped ({description}): comparator disabled"
    else
      throw e

def tests : IO Unit := do
  let big ← mkTestData
  let prng := mkPrngData 4096
  let constant := mkConstantData 8192

  -- Whole-buffer roundtrip via miniz_oxide.
  withMiniz "compress(big)" (MinizOxide.compress big) fun mz => do
    let back ← MinizOxide.decompress mz
    assert! back.beq big

    -- miniz output must decompress with the zlib FFI as well — both
    -- libraries claim to speak raw DEFLATE.
    let viaZlib ← RawDeflate.decompress mz
    assert! viaZlib.beq big

    -- And the other direction: zlib output decompresses via miniz.
    let zout ← RawDeflate.compress big
    let viaMiniz ← MinizOxide.decompress zout
    assert! viaMiniz.beq big

    -- PRNG payload (less compressible) — same checks.
    let mzPrng ← MinizOxide.compress prng
    let backPrng ← MinizOxide.decompress mzPrng
    assert! backPrng.beq prng
    let viaZlibPrng ← RawDeflate.decompress mzPrng
    assert! viaZlibPrng.beq prng

    -- Maximally compressible payload at level 0 (stored blocks).
    let mzConst0 ← MinizOxide.compress constant 0
    let backConst0 ← MinizOxide.decompress mzConst0
    assert! backConst0.beq constant

    -- Level clamp: values above 9 must be clamped to 9 before reaching
    -- the Rust shim (otherwise miniz_oxide silently treats them as 0 or
    -- 10). All three of these must produce byte-identical output.
    let mzLevel9   ← MinizOxide.compress prng 9
    let mzLevel10  ← MinizOxide.compress prng 10
    let mzLevel255 ← MinizOxide.compress prng 255
    assert! mzLevel10.beq mzLevel9
    assert! mzLevel255.beq mzLevel9

    -- Empty input roundtrip.
    let mzEmpty ← MinizOxide.compress ByteArray.empty
    let backEmpty ← MinizOxide.decompress mzEmpty
    assert! backEmpty.beq ByteArray.empty

    -- Decompression-limit cap: a one-byte-under-cap should fail with
    -- "exceeds limit" matching the wording shared with RawDeflate.
    let limitResult ← (MinizOxide.decompress mz
        (maxDecompressedSize := (big.size - 1).toUInt64)).toBaseIO
    match limitResult with
    | .ok _ => throw (IO.userError "MinizOxide.decompress should reject under-cap input")
    | .error e =>
      unless (toString e).contains "exceeds limit" do
        throw (IO.userError s!"MinizOxide.decompress wrong limit error: {e}")

    -- Exact-fit cap should succeed.
    let exact ← MinizOxide.decompress mz
      (maxDecompressedSize := big.size.toUInt64)
    assert! exact.beq big

    IO.println "MinizOxide tests: OK"

end ZipTest.MinizOxide
