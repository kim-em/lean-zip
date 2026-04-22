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

  -- Compression levels
  let fast ← Gzip.compress big (level := 1)
  let best ← Gzip.compress big (level := 9)
  assert! best.size ≤ fast.size

  -- Empty input
  let ge ← Gzip.compress ByteArray.empty
  let gde ← Gzip.decompress ge
  assert! gde.beq ByteArray.empty

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
