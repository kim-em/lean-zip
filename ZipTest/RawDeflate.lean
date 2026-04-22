import ZipTest.Helpers

/-! Tests for raw DEFLATE compression/decompression with streaming roundtrip verification. -/

-- Compile-time probe: FFI whole-buffer default is 1 GiB (SECURITY_INVENTORY Rec. 1).
example (d : ByteArray) : RawDeflate.decompress d = @RawDeflate.decompress d (1024 * 1024 * 1024) := rfl

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

  -- Streaming decompress with a non-zero limit larger than the decompressed
  -- size: happy path, output matches input.
  let mkWriteStream : IO (IO.Ref ByteArray × IO.FS.Stream) := do
    let ref ← IO.mkRef ByteArray.empty
    let stream : IO.FS.Stream := {
      flush := pure (), read := fun _ => pure ByteArray.empty
      write := fun c => ref.modify (· ++ c)
      getLine := pure "", putStr := fun _ => pure (), isTty := pure false
    }
    return (ref, stream)
  let smallInput := "raw deflate streaming happy path".toUTF8
  let rdSmall ← RawDeflate.compress smallInput
  let rdInOk ← byteArrayReadStream rdSmall
  let (rdOutRefOk, rdOutOk) ← mkWriteStream
  RawDeflate.decompressStream rdInOk rdOutOk (maxDecompressedSize := 1024)
  let rdOkBytes ← rdOutRefOk.get
  assert! rdOkBytes.beq smallInput

  -- Streaming decompress with a limit smaller than the decompressed size:
  -- must abort mid-stream with `"exceeds limit"`, and the partial output
  -- must be at most `maxDecompressedSize` bytes.
  let rdInBomb ← byteArrayReadStream rawCompressed
  let (rdOutRefBomb, rdOutBomb) ← mkWriteStream
  let rdStreamLimit : UInt64 := 10
  match ← (RawDeflate.decompressStream rdInBomb rdOutBomb
      (maxDecompressedSize := rdStreamLimit)).toBaseIO with
  | .ok _ =>
    throw (IO.userError "raw deflate decompressStream limit should have been rejected")
  | .error e =>
    unless (toString e).contains "exceeds limit" do
      throw (IO.userError s!"raw deflate decompressStream limit wrong error: {e}")
  let rdPartial ← rdOutRefBomb.get
  assert! rdPartial.size.toUInt64 ≤ rdStreamLimit
  IO.println "RawDeflate tests: OK"
