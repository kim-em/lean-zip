import ZipTest.Helpers

/-! Smoke tests for the libdeflate FFI comparator (Track D Phase 0a).

    libdeflate is unverified; these checks are conformance against zlib /
    the native inflate decoder, not correctness proofs. The point is that
    libdeflate emits valid raw DEFLATE that the rest of the pipeline can
    decode, so it can be used as a runtime/ratio reference. -/

-- Compile-time probe: FFI default is 1 GiB (mirrors the `RawDeflate` probe).
example (d : ByteArray) : Libdeflate.decompress d = @Libdeflate.decompress d (1024 * 1024 * 1024) := rfl

def ZipTest.Libdeflate.tests : IO Unit := do
  let big ← mkTestData

  -- Whole-buffer roundtrip via libdeflate alone.
  let ldCompressed ← Libdeflate.compress big
  let ldDecompressed ← Libdeflate.decompress ldCompressed
  assert! ldDecompressed.beq big

  -- Cross-check: libdeflate compress + zlib FFI inflate decodes correctly.
  let zlibDecomp ← RawDeflate.decompress ldCompressed
  assert! zlibDecomp.beq big

  -- Cross-check: libdeflate compress + native inflate decodes correctly.
  match Zip.Native.Inflate.inflate ldCompressed with
  | .ok bytes => assert! bytes.beq big
  | .error e => throw (IO.userError s!"native inflate of libdeflate output failed: {e}")

  -- Empty input edge case.
  let ldCE ← Libdeflate.compress ByteArray.empty
  let ldDE ← Libdeflate.decompress ldCE
  assert! ldDE.beq ByteArray.empty

  -- Single byte edge case.
  let one := ByteArray.mk #[0x42]
  let ldC1 ← Libdeflate.compress one
  let ldD1 ← Libdeflate.decompress ldC1
  assert! ldD1.beq one

  -- Decompression limit: rejected with the shared "exceeds limit" wording.
  assertThrows "libdeflate decompress limit"
    (do let _ ← Libdeflate.decompress ldCompressed (maxDecompressedSize := 10); pure ())
    "exceeds limit"

  -- Bad data is rejected.
  assertThrows "libdeflate bad data"
    (do let _ ← Libdeflate.decompress (ByteArray.mk #[0xFF, 0xFF, 0xFF, 0xFF]); pure ())
    "libdeflate decompress"

  -- Higher levels (10-12) are libdeflate-only and must succeed.
  let ldC12 ← Libdeflate.compress big 12
  let ldD12 ← Libdeflate.decompress ldC12
  assert! ldD12.beq big

  IO.println "Libdeflate tests: OK"
