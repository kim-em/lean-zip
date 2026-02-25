import ZipTest.Helpers

/-! Tests for zstd compression/decompression: streaming, file I/O, compression levels,
    and large data handling. -/

def ZipTest.Zstd.tests : IO Unit := do
  let big ← mkTestData

  -- Whole-buffer roundtrip
  let zstdCompressed ← Zstd.compress big
  let zstdDecompressed ← Zstd.decompress zstdCompressed
  unless zstdDecompressed.beq big do throw (IO.userError "zstd roundtrip")

  -- Decompression limit
  let zstdLimitResult ← (Zstd.decompress zstdCompressed (maxDecompressedSize := 10)).toBaseIO
  match zstdLimitResult with
  | .ok _ => throw (IO.userError "zstd decompress limit should have been rejected")
  | .error e =>
    unless (toString e).contains "exceeds limit" do
      throw (IO.userError s!"zstd decompress limit wrong error: {e}")

  -- Different compression levels
  let zstdFast ← Zstd.compress big 1
  let zstdBest ← Zstd.compress big 19
  let zstdFastDec ← Zstd.decompress zstdFast
  unless zstdFastDec.beq big do throw (IO.userError "zstd level 1 roundtrip")
  let zstdBestDec ← Zstd.decompress zstdBest
  unless zstdBestDec.beq big do throw (IO.userError "zstd level 19 roundtrip")

  -- Empty input
  let zstdEmpty ← Zstd.compress ByteArray.empty
  let zstdEmptyDec ← Zstd.decompress zstdEmpty
  unless zstdEmptyDec.size == 0 do throw (IO.userError "zstd empty roundtrip")

  -- File compress/decompress
  let zstdStreamTestFile : System.FilePath := "/tmp/lean-zlib-zstd-test-input"
  let zstdStreamCompFile : System.FilePath := "/tmp/lean-zlib-zstd-test-input.zst"
  IO.FS.writeBinFile zstdStreamTestFile big
  Zstd.compressFile zstdStreamTestFile
  Zstd.decompressFile zstdStreamCompFile
  let zstdStreamDec ← IO.FS.readBinFile zstdStreamTestFile
  unless zstdStreamDec.beq big do throw (IO.userError "zstd file roundtrip")
  let _ ← IO.Process.run { cmd := "rm", args := #["-f", zstdStreamTestFile.toString, zstdStreamCompFile.toString] }

  -- Streaming with small chunks
  let zstdStreamComp ← Zstd.CompressState.new 3
  let mut zstdStreamBuf := ByteArray.empty
  let chunkSize := 1000
  let mut zstdOff := 0
  while zstdOff < big.size do
    let end_ := min (zstdOff + chunkSize) big.size
    let chunk := big.extract zstdOff end_
    let out ← zstdStreamComp.push chunk
    zstdStreamBuf := zstdStreamBuf ++ out
    zstdOff := end_
  let zstdFinal ← zstdStreamComp.finish
  zstdStreamBuf := zstdStreamBuf ++ zstdFinal
  -- Decompress with streaming
  let zstdStreamDecomp ← Zstd.DecompressState.new
  let mut zstdDecBuf := ByteArray.empty
  zstdOff := 0
  while zstdOff < zstdStreamBuf.size do
    let end_ := min (zstdOff + chunkSize) zstdStreamBuf.size
    let chunk := zstdStreamBuf.extract zstdOff end_
    let out ← zstdStreamDecomp.push chunk
    zstdDecBuf := zstdDecBuf ++ out
    zstdOff := end_
  let zstdDecFinal ← zstdStreamDecomp.finish
  zstdDecBuf := zstdDecBuf ++ zstdDecFinal
  unless zstdDecBuf.beq big do throw (IO.userError "zstd streaming roundtrip")

  -- Large data
  let large ← mkLargeData
  let zstdLargeComp ← Zstd.compress large
  let zstdLargeDec ← Zstd.decompress zstdLargeComp
  unless zstdLargeDec.beq large do throw (IO.userError "zstd large roundtrip")
  IO.println "Zstd tests: OK"
