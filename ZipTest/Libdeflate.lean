import ZipTest.Helpers

/-! Smoke tests for the Track D libdeflate comparator.

When the project is built without libdeflate the FFI raises an `IO.userError`
containing `"libdeflate: not built with"`; we treat that as a clean skip so CI
on minimal toolchains keeps passing. With libdeflate available the tests
exercise:

* libdeflate compress + libdeflate decompress roundtrip,
* libdeflate compress + zlib FFI decompress (ecosystem cross-check),
* libdeflate compress + native inflate decompress (the verified decoder),
* the decompression-limit cap (`maxDecompressedSize`).
-/

namespace ZipTest.Libdeflate

private def disabledMarker : String := "libdeflate: not built with"

private def withLib (description : String) (action : IO α) (k : α → IO Unit) : IO Unit := do
  match (← action.toBaseIO) with
  | .ok x => k x
  | .error e =>
    if (toString e).contains disabledMarker then
      IO.println s!"Libdeflate tests skipped ({description}): comparator disabled"
    else
      throw e

def tests : IO Unit := do
  let big ← mkTestData
  let prng := mkPrngData 4096
  let constant := mkConstantData 8192

  withLib "compress(big)" (Libdeflate.compress big) fun ld => do
    -- Whole-buffer roundtrip via libdeflate.
    let back ← Libdeflate.decompress ld
    assert! back.beq big

    -- libdeflate output is raw DEFLATE — decodes via zlib FFI and our native
    -- (verified) inflate too.
    let viaZlib ← RawDeflate.decompress ld
    assert! viaZlib.beq big
    match Zip.Native.Inflate.inflate ld with
    | .ok viaNative => assert! viaNative.beq big
    | .error e => throw (IO.userError s!"native inflate rejected libdeflate output: {e}")

    -- And the other direction: zlib output decompresses via libdeflate.
    let zout ← RawDeflate.compress big
    let viaLib ← Libdeflate.decompress zout
    assert! viaLib.beq big

    -- PRNG payload (less compressible).
    let ldPrng ← Libdeflate.compress prng
    assert! (← Libdeflate.decompress ldPrng).beq prng

    -- Maximally compressible payload, and empty input.
    let ldConst ← Libdeflate.compress constant
    assert! (← Libdeflate.decompress ldConst).beq constant
    let ldEmpty ← Libdeflate.compress ByteArray.empty
    assert! (← Libdeflate.decompress ldEmpty).beq ByteArray.empty

    -- Decompression-limit cap: one byte under the true size must fail.
    match (← (Libdeflate.decompress ld
        (maxDecompressedSize := (big.size - 1).toUInt64)).toBaseIO) with
    | .ok _ => throw (IO.userError "Libdeflate.decompress should reject under-cap input")
    | .error _ => pure ()
    -- Exact-fit cap should succeed.
    assert! (← Libdeflate.decompress ld (maxDecompressedSize := big.size.toUInt64)).beq big

    IO.println "Libdeflate tests: OK"

end ZipTest.Libdeflate
