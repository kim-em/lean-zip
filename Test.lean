import Zlib

/-- Check that two byte arrays are equal. -/
def ByteArray.beq (a b : ByteArray) : Bool :=
  a.data == b.data

def main : IO Unit := do
  let original := "Hello, world! This is a test of zlib compression from Lean 4. ".toUTF8
  -- Repeat to make compression worthwhile
  let mut big := ByteArray.empty
  for _ in List.range 100 do
    big := big ++ original

  IO.println s!"Original size: {big.size}"

  -- Test zlib compress/decompress
  let compressed ← Zlib.compress big
  IO.println s!"Zlib compressed size: {compressed.size}"
  let decompressed ← Zlib.decompress compressed
  IO.println s!"Zlib decompressed size: {decompressed.size}"
  assert! decompressed.beq big
  IO.println "Zlib roundtrip: OK"

  -- Test gzip compress/decompress
  let gzipped ← Gzip.compress big
  IO.println s!"Gzip compressed size: {gzipped.size}"
  let gunzipped ← Gzip.decompress gzipped
  IO.println s!"Gzip decompressed size: {gunzipped.size}"
  assert! gunzipped.beq big
  IO.println "Gzip roundtrip: OK"

  -- Test compression levels
  let fast ← Gzip.compress big (level := 1)
  let best ← Gzip.compress big (level := 9)
  IO.println s!"Gzip level 1: {fast.size}, level 9: {best.size}"
  assert! best.size ≤ fast.size

  -- Test empty input
  let empty := ByteArray.empty
  let ce ← Zlib.compress empty
  let de ← Zlib.decompress ce
  assert! de.beq empty
  let ge ← Gzip.compress empty
  let gde ← Gzip.decompress ge
  assert! gde.beq empty
  IO.println "Empty input roundtrip: OK"

  -- Test concatenated gzip streams
  let part1 := "First gzip member. ".toUTF8
  let part2 := "Second gzip member. ".toUTF8
  let gz1 ← Gzip.compress part1
  let gz2 ← Gzip.compress part2
  let concatenated := gz1 ++ gz2
  let decoded ← Gzip.decompress concatenated
  assert! decoded.beq (part1 ++ part2)
  IO.println "Concatenated gzip roundtrip: OK"

  -- Test streaming compression roundtrip
  let state ← Gzip.DeflateState.new
  let mut compressedChunks := ByteArray.empty
  -- Feed data in small chunks
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
  IO.println s!"Streaming compressed size: {compressedChunks.size}"
  -- Decompress with whole-buffer API (interop test)
  let streamDecompressed ← Gzip.decompress compressedChunks
  assert! streamDecompressed.beq big
  IO.println "Streaming compress + whole-buffer decompress: OK"

  -- Test streaming decompression
  let istate ← Gzip.InflateState.new
  let mut decompressedChunks := ByteArray.empty
  -- Feed compressed data in small chunks
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
  IO.println "Streaming decompress: OK"

  -- Test compressStream / decompressStream via files
  let tmpFile : System.FilePath := "/tmp/lean-zlib-test-data.bin"
  IO.FS.writeBinFile tmpFile big
  let gzPath ← Gzip.compressFile tmpFile
  assert! gzPath.toString == "/tmp/lean-zlib-test-data.bin.gz"
  let outPath ← Gzip.decompressFile gzPath
  assert! outPath.toString == "/tmp/lean-zlib-test-data.bin"
  let roundtripped ← IO.FS.readBinFile outPath
  assert! roundtripped.beq big
  IO.println "File compress/decompress roundtrip: OK"

  -- Test decompressFile with explicit output path
  let customOut : System.FilePath := "/tmp/lean-zlib-test-custom.bin"
  let outPath2 ← Gzip.decompressFile gzPath (outPath := customOut)
  assert! outPath2.toString == "/tmp/lean-zlib-test-custom.bin"
  let roundtripped2 ← IO.FS.readBinFile customOut
  assert! roundtripped2.beq big
  IO.println "File decompress (custom output): OK"

  -- Test large data (> 64KB chunk size) via streaming
  let mut large := ByteArray.empty
  for _ in List.range 2000 do
    large := large ++ original
  IO.println s!"Large data size: {large.size}"
  let largeTmp : System.FilePath := "/tmp/lean-zlib-test-large.bin"
  IO.FS.writeBinFile largeTmp large
  let largeGz ← Gzip.compressFile largeTmp
  let largeOut ← Gzip.decompressFile largeGz
  let largeRoundtripped ← IO.FS.readBinFile largeOut
  assert! largeRoundtripped.beq large
  IO.println "Large file roundtrip: OK"

  IO.println "All tests passed!"
