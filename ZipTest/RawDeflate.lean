import ZipTest.Helpers

/-! Tests for raw DEFLATE compression/decompression with streaming roundtrip verification. -/

def ZipTest.RawDeflate.tests : IO Unit := do
  let big ← mkTestData

  -- Whole-buffer roundtrip
  let rawCompressed ← RawDeflate.compress big
  let rawDecompressed ← RawDeflate.decompress rawCompressed
  assert! rawDecompressed.beq big

  -- Decompression limit (bomb)
  let rawLimitResult ← (RawDeflate.decompress rawCompressed (maxDecompressedSize := 10)).toBaseIO
  match rawLimitResult with
  | .ok _ => throw (IO.userError "raw deflate decompress limit should have been rejected")
  | .error e =>
    unless (toString e).contains "exceeds limit" do
      throw (IO.userError s!"raw deflate decompress limit wrong error: {e}")

  -- Near-limit boundary: exact-fit must succeed; one-byte-under must fail.
  -- Exercises the cap check at c/zlib_ffi.c:191 (`total > max_output`).
  let rawExactFit ← RawDeflate.decompress rawCompressed
    (maxDecompressedSize := big.size.toUInt64)
  assert! rawExactFit.beq big
  let rawUnderResult ← (RawDeflate.decompress rawCompressed
      (maxDecompressedSize := (big.size - 1).toUInt64)).toBaseIO
  match rawUnderResult with
  | .ok _ => throw (IO.userError "raw deflate decompress near-limit (n-1) should have been rejected")
  | .error e =>
    unless (toString e).contains "exceeds limit" do
      throw (IO.userError s!"raw deflate decompress near-limit wrong error: {e}")

  -- Streaming roundtrip
  let rawState ← RawDeflate.DeflateState.new
  let mut rawChunks := ByteArray.empty
  let mut offset := 0
  while offset < big.size do
    let end_ := min (offset + 500) big.size
    let out ← rawState.push (big.extract offset end_)
    rawChunks := rawChunks ++ out
    offset := offset + 500
  let rawFinal ← rawState.finish
  rawChunks := rawChunks ++ rawFinal
  let rawStreamDecomp ← RawDeflate.decompress rawChunks
  assert! rawStreamDecomp.beq big

  -- Empty raw deflate
  let rawCE ← RawDeflate.compress ByteArray.empty
  let rawDE ← RawDeflate.decompress rawCE
  assert! rawDE.beq ByteArray.empty

  -- Truncated input rejection (FFI)
  -- Stored-block header claiming 5 data bytes but no NLEN + no data.
  let storedTrunc := ByteArray.mk #[0x01, 0x05, 0x00]
  match ← (RawDeflate.decompress storedTrunc).toBaseIO with
  | .ok _ => throw (IO.userError "raw deflate should reject truncated stored block")
  | .error _ => pure ()
  let compTrunc := rawCompressed.extract 0 (rawCompressed.size - 2)
  match ← (RawDeflate.decompress compTrunc).toBaseIO with
  | .ok _ => throw (IO.userError "raw deflate should reject truncated compressed stream")
  | .error _ => pure ()
  IO.println "RawDeflate tests: OK"
