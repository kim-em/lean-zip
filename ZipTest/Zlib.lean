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

  -- Empty input roundtrip
  let empty := ByteArray.empty
  let ce ← Zlib.compress empty
  let de ← Zlib.decompress ce
  assert! de.beq empty
  IO.println "Zlib tests: OK"
