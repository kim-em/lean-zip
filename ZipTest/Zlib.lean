import ZipTest.Helpers

/-! Tests for zlib compression/decompression with decompression size limits and roundtrip verification. -/

def ZipTest.Zlib.tests : IO Unit := do
  let big ← mkTestData

  -- Zlib compress/decompress roundtrip
  let compressed ← Zlib.compress big
  let decompressed ← Zlib.decompress compressed
  assert! decompressed.beq big

  -- Decompression limit
  let zlibLimitResult ← (Zlib.decompress compressed (maxDecompressedSize := 10)).toBaseIO
  match zlibLimitResult with
  | .ok _ => throw (IO.userError "decompress limit should have been rejected")
  | .error e =>
    unless (toString e).contains "exceeds limit" do
      throw (IO.userError s!"decompress limit wrong error: {e}")

  -- Near-limit boundary: exact-fit must succeed; one-byte-under must fail.
  -- Exercises the cap check at c/zlib_ffi.c:191 (`total > max_output`).
  let zExactFit ← Zlib.decompress compressed (maxDecompressedSize := big.size.toUInt64)
  assert! zExactFit.beq big
  let zUnderResult ← (Zlib.decompress compressed
      (maxDecompressedSize := (big.size - 1).toUInt64)).toBaseIO
  match zUnderResult with
  | .ok _ => throw (IO.userError "zlib decompress near-limit (n-1) should have been rejected")
  | .error e =>
    unless (toString e).contains "exceeds limit" do
      throw (IO.userError s!"zlib decompress near-limit wrong error: {e}")

  -- Empty input roundtrip
  let empty := ByteArray.empty
  let ce ← Zlib.compress empty
  let de ← Zlib.decompress ce
  assert! de.beq empty

  -- Truncated input rejection (FFI)
  let trailerTrunc := compressed.extract 0 (compressed.size - 4)
  match ← (Zlib.decompress trailerTrunc).toBaseIO with
  | .ok _ => throw (IO.userError "zlib decompress should reject trailer-truncated stream")
  | .error _ => pure ()
  let bodyTrunc := compressed.extract 0 8
  match ← (Zlib.decompress bodyTrunc).toBaseIO with
  | .ok _ => throw (IO.userError "zlib decompress should reject body-truncated stream")
  | .error _ => pure ()
  IO.println "Zlib tests: OK"
