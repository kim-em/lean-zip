import ZipTest.Helpers

/-! Tests for gzip compression/decompression: streaming, file I/O, compression levels,
    and concatenated streams. -/

def ZipTest.Gzip.tests : IO Unit := do
  let big ← mkTestData

  -- Gzip roundtrip
  let gzipped ← Gzip.compress big
  let gunzipped ← Gzip.decompress gzipped
  assert! gunzipped.beq big

  -- Decompression limit (bomb)
  let gzipLimitResult ← (Gzip.decompress gzipped (maxDecompressedSize := 10)).toBaseIO
  match gzipLimitResult with
  | .ok _ => throw (IO.userError "gzip decompress limit should have been rejected")
  | .error e =>
    unless (toString e).contains "exceeds limit" do
      throw (IO.userError s!"gzip decompress limit wrong error: {e}")

  -- Near-limit boundary: exact-fit must succeed; one-byte-under must fail.
  -- Exercises the cap check at c/zlib_ffi.c:191 (`total > max_output`).
  let gzExactFit ← Gzip.decompress gzipped (maxDecompressedSize := big.size.toUInt64)
  assert! gzExactFit.beq big
  let gzUnderResult ← (Gzip.decompress gzipped
      (maxDecompressedSize := (big.size - 1).toUInt64)).toBaseIO
  match gzUnderResult with
  | .ok _ => throw (IO.userError "gzip decompress near-limit (n-1) should have been rejected")
  | .error e =>
    unless (toString e).contains "exceeds limit" do
      throw (IO.userError s!"gzip decompress near-limit wrong error: {e}")

  -- Compression levels
  let fast ← Gzip.compress big (level := 1)
  let best ← Gzip.compress big (level := 9)
  assert! best.size ≤ fast.size

  -- Empty input
  let ge ← Gzip.compress ByteArray.empty
  let gde ← Gzip.decompress ge
  assert! gde.beq ByteArray.empty

  -- Truncated input rejection (FFI)
  let trailerTrunc := gzipped.extract 0 (gzipped.size - 4)
  match ← (Gzip.decompress trailerTrunc).toBaseIO with
  | .ok _ => throw (IO.userError "gzip decompress should reject trailer-truncated stream")
  | .error _ => pure ()
  let bodyTrunc := gzipped.extract 0 8
  match ← (Gzip.decompress bodyTrunc).toBaseIO with
  | .ok _ => throw (IO.userError "gzip decompress should reject body-truncated stream")
  | .error _ => pure ()

  -- Concatenated gzip streams
  let part1 := "First gzip member. ".toUTF8
  let part2 := "Second gzip member. ".toUTF8
  let gz1 ← Gzip.compress part1
  let gz2 ← Gzip.compress part2
  let concatenated := gz1 ++ gz2
  let decoded ← Gzip.decompress concatenated
  assert! decoded.beq (part1 ++ part2)

  -- maxDecompressedSize crosses concatenated-member boundary
  let memA := "0123456789".toUTF8  -- 10 bytes
  let memB := "abcdefghij".toUTF8  -- 10 bytes
  let gzA ← Gzip.compress memA
  let gzB ← Gzip.compress memB
  let concatLimitResult ← (Gzip.decompress (gzA ++ gzB) (maxDecompressedSize := 5)).toBaseIO
  match concatLimitResult with
  | .ok _ => throw (IO.userError "concat gzip decompress limit should have been rejected")
  | .error e =>
    unless (toString e).contains "exceeds limit" do
      throw (IO.userError s!"concat gzip decompress limit wrong error: {e}")

  -- Streaming compression roundtrip
  let state ← Gzip.DeflateState.new
  let mut compressedChunks := ByteArray.empty
  let chunkSize := 500
  let mut offset := 0
  while offset < big.size do
    let end_ := min (offset + chunkSize) big.size
    let chunk := big.extract offset end_
    let out ← state.push chunk
    compressedChunks := compressedChunks ++ out
    offset := offset + chunkSize
  let final ← state.finish
  compressedChunks := compressedChunks ++ final
  -- Decompress with whole-buffer API (interop test)
  let streamDecompressed ← Gzip.decompress compressedChunks
  assert! streamDecompressed.beq big

  -- Streaming decompression
  let istate ← Gzip.InflateState.new
  let mut decompressedChunks := ByteArray.empty
  offset := 0
  while offset < compressedChunks.size do
    let end_ := min (offset + 50) compressedChunks.size
    let chunk := compressedChunks.extract offset end_
    let out ← istate.push chunk
    decompressedChunks := decompressedChunks ++ out
    offset := offset + 50
  let ifinal ← istate.finish
  decompressedChunks := decompressedChunks ++ ifinal
  assert! decompressedChunks.beq big

  -- Repeated inflateReset across four concatenated gzip members (streaming).
  -- Exercises the `inflateReset` branch at c/zlib_ffi.c:505 three times in
  -- one `push` call; four distinct payloads make loop-accumulated-state bugs
  -- visible in the final diagnostic.
  let rr1 ← Gzip.compress "a".toUTF8
  let rr2 ← Gzip.compress "bb".toUTF8
  let rr3 ← Gzip.compress "ccc".toUTF8
  let rr4 ← Gzip.compress "dddd".toUTF8
  let rrConcat := rr1 ++ rr2 ++ rr3 ++ rr4
  let rrState ← Gzip.InflateState.new
  let rrPush ← rrState.push rrConcat
  let rrFin ← rrState.finish
  assert! (rrPush ++ rrFin).beq "abbcccdddd".toUTF8

  -- Zero-length chunk through streaming decompressor (empty chunk is a no-op)
  let zigzip ← Gzip.compress big
  let zistate ← Gzip.InflateState.new
  let zo1 ← zistate.push ByteArray.empty
  let zo2 ← zistate.push zigzip
  let zof ← zistate.finish
  assert! (zo1 ++ zo2 ++ zof).beq big

  -- Zero-length chunk through streaming compressor (empty chunk is a no-op)
  let zdstate ← Gzip.DeflateState.new
  let zd1 ← zdstate.push ByteArray.empty
  let zd2 ← zdstate.push big
  let zdf ← zdstate.finish
  let zdRoundtrip ← Gzip.decompress (zd1 ++ zd2 ++ zdf)
  assert! zdRoundtrip.beq big

  -- File compress/decompress roundtrip
  let tmpFile : System.FilePath := "/tmp/lean-zlib-test-data.bin"
  IO.FS.writeBinFile tmpFile big
  let gzPath ← Gzip.compressFile tmpFile
  assert! gzPath.toString == "/tmp/lean-zlib-test-data.bin.gz"
  let outPath ← Gzip.decompressFile gzPath
  assert! outPath.toString == "/tmp/lean-zlib-test-data.bin"
  let roundtripped ← IO.FS.readBinFile outPath
  assert! roundtripped.beq big

  -- File decompress with explicit output path
  let customOut : System.FilePath := "/tmp/lean-zlib-test-custom.bin"
  let outPath2 ← Gzip.decompressFile gzPath (outPath := customOut)
  assert! outPath2.toString == "/tmp/lean-zlib-test-custom.bin"
  let roundtripped2 ← IO.FS.readBinFile customOut
  assert! roundtripped2.beq big

  -- Streaming decompress with a non-zero limit that is larger than the
  -- decompressed size: happy path, full output reconstructed.
  let mkWriteStream : IO (IO.Ref ByteArray × IO.FS.Stream) := do
    let ref ← IO.mkRef ByteArray.empty
    let stream : IO.FS.Stream := {
      flush := pure (), read := fun _ => pure ByteArray.empty
      write := fun c => ref.modify (· ++ c)
      getLine := pure "", putStr := fun _ => pure (), isTty := pure false
    }
    return (ref, stream)
  let smallInput := "hello, streaming world!".toUTF8
  let gzSmall ← Gzip.compress smallInput
  let inStreamOk ← byteArrayReadStream gzSmall
  let (outRefOk, outStreamOk) ← mkWriteStream
  Gzip.decompressStream inStreamOk outStreamOk (maxDecompressedSize := 1024)
  let outOk ← outRefOk.get
  assert! outOk.beq smallInput

  -- Streaming decompress with a limit smaller than the decompressed size:
  -- must abort mid-stream with the shared `"exceeds limit"` substring, and
  -- the partial output must be at most `maxDecompressedSize` bytes.
  let bombInput ← mkTestData  -- 6200 bytes of redundant text
  let gzBomb ← Gzip.compress bombInput
  let inStreamBomb ← byteArrayReadStream gzBomb
  let (outRefBomb, outStreamBomb) ← mkWriteStream
  let streamLimit : UInt64 := 10
  match ← (Gzip.decompressStream inStreamBomb outStreamBomb
      (maxDecompressedSize := streamLimit)).toBaseIO with
  | .ok _ => throw (IO.userError "gzip decompressStream limit should have been rejected")
  | .error e =>
    unless (toString e).contains "exceeds limit" do
      throw (IO.userError s!"gzip decompressStream limit wrong error: {e}")
  let partial_ ← outRefBomb.get
  assert! partial_.size.toUInt64 ≤ streamLimit

  -- decompressFile with a generous non-zero limit: happy path.
  let fileLimitTmp : System.FilePath := "/tmp/lean-zlib-test-filelimit.bin"
  IO.FS.writeBinFile fileLimitTmp big
  let fileLimitGz ← Gzip.compressFile fileLimitTmp
  let fileLimitOut ← Gzip.decompressFile fileLimitGz
    (maxDecompressedSize := (big.size * 2).toUInt64)
  let fileLimitRoundtripped ← IO.FS.readBinFile fileLimitOut
  assert! fileLimitRoundtripped.beq big
  for f in #["/tmp/lean-zlib-test-filelimit.bin", "/tmp/lean-zlib-test-filelimit.bin.gz"] do
    let _ ← IO.Process.run { cmd := "rm", args := #["-f", f] }

  -- Large data via streaming
  let large ← mkLargeData
  let largeTmp : System.FilePath := "/tmp/lean-zlib-test-large.bin"
  IO.FS.writeBinFile largeTmp large
  let largeGz ← Gzip.compressFile largeTmp
  let largeOut ← Gzip.decompressFile largeGz
  let largeRoundtripped ← IO.FS.readBinFile largeOut
  assert! largeRoundtripped.beq large
  -- Clean up temp files
  for f in #["/tmp/lean-zlib-test-data.bin", "/tmp/lean-zlib-test-data.bin.gz",
             "/tmp/lean-zlib-test-custom.bin",
             "/tmp/lean-zlib-test-large.bin", "/tmp/lean-zlib-test-large.bin.gz"] do
    let _ ← IO.Process.run { cmd := "rm", args := #["-f", f] }
  IO.println "Gzip tests: OK"
