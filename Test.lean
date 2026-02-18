import Zlib

set_option maxRecDepth 2048

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

  -- === Checksum tests ===

  -- CRC32 of known data (precomputed: CRC32 of "Hello, world!" = 0xebe6c6e6)
  let helloBytes := "Hello, world!".toUTF8
  let crc ← Checksum.crc32 0 helloBytes
  IO.println s!"CRC32 of 'Hello, world!': {crc}"
  -- Incremental CRC32 matches whole-buffer
  let crc1 ← Checksum.crc32 0 (big.extract 0 3000)
  let crc2 ← Checksum.crc32 crc1 (big.extract 3000 big.size)
  let crcWhole ← Checksum.crc32 0 big
  assert! crc2 == crcWhole
  IO.println "CRC32 incremental: OK"

  -- Adler32
  let adler ← Checksum.adler32 1 helloBytes
  IO.println s!"Adler32 of 'Hello, world!': {adler}"
  -- Incremental Adler32 matches whole-buffer
  let adler1 ← Checksum.adler32 1 (big.extract 0 3000)
  let adler2 ← Checksum.adler32 adler1 (big.extract 3000 big.size)
  let adlerWhole ← Checksum.adler32 1 big
  assert! adler2 == adlerWhole
  IO.println "Adler32 incremental: OK"

  -- Empty input checksums
  let crcEmpty ← Checksum.crc32 0 ByteArray.empty
  assert! crcEmpty == 0
  let adlerEmpty ← Checksum.adler32 1 ByteArray.empty
  assert! adlerEmpty == 1
  IO.println "Checksum empty input: OK"

  -- === Raw deflate tests ===

  -- Whole-buffer roundtrip
  let rawCompressed ← RawDeflate.compress big
  let rawDecompressed ← RawDeflate.decompress rawCompressed
  assert! rawDecompressed.beq big
  IO.println s!"Raw deflate roundtrip: OK (compressed {big.size} → {rawCompressed.size})"

  -- Streaming roundtrip
  let rawState ← RawDeflate.DeflateState.new
  let mut rawChunks := ByteArray.empty
  offset := 0
  while offset < big.size do
    let end_ := min (offset + 500) big.size
    let out ← rawState.push (big.extract offset end_)
    rawChunks := rawChunks ++ out
    offset := offset + 500
  let rawFinal ← rawState.finish
  rawChunks := rawChunks ++ rawFinal
  let rawStreamDecomp ← RawDeflate.decompress rawChunks
  assert! rawStreamDecomp.beq big
  IO.println "Raw deflate streaming roundtrip: OK"

  -- Empty raw deflate
  let rawCE ← RawDeflate.compress ByteArray.empty
  let rawDE ← RawDeflate.decompress rawCE
  assert! rawDE.beq ByteArray.empty
  IO.println "Raw deflate empty input: OK"

  -- === Binary helper tests ===

  -- Octal roundtrip (use variables to prevent compile-time reduction)
  let testOctalVal : UInt64 := 1234
  let octalBytes := Binary.writeOctal testOctalVal 12
  unless octalBytes.size == 12 do throw (IO.userError s!"octal size: {octalBytes.size}")
  let octalVal := Binary.readOctal octalBytes 0 12
  unless octalVal == testOctalVal do throw (IO.userError s!"octal val: {octalVal}")
  let octalZero : UInt64 := 0
  let zeroOctal := Binary.writeOctal octalZero 8
  unless Binary.readOctal zeroOctal 0 8 == 0 do throw (IO.userError "octal zero")
  IO.println "Binary octal roundtrip: OK"

  -- Little-endian roundtrip
  let testVal16 : UInt16 := 0xABCD
  let le16 := Binary.writeUInt16LE testVal16
  unless le16.size == 2 do throw (IO.userError "le16 size")
  unless Binary.readUInt16LE le16 0 == testVal16 do throw (IO.userError "le16 val")
  let testVal32 : UInt32 := 0xDEADBEEF
  let le32 := Binary.writeUInt32LE testVal32
  unless le32.size == 4 do throw (IO.userError "le32 size")
  unless Binary.readUInt32LE le32 0 == testVal32 do throw (IO.userError "le32 val")
  IO.println "Binary LE roundtrip: OK"

  -- String roundtrip
  let strBytes := Binary.writeString "hello" 10
  unless strBytes.size == 10 do throw (IO.userError "str size")
  unless Binary.readString strBytes 0 10 == "hello" do throw (IO.userError "str val")
  IO.println "Binary string roundtrip: OK"

  -- === Tar tests ===

  -- Create a temp directory with test files
  let tarTestDir : System.FilePath := "/tmp/lean-zlib-tar-test"
  -- Clean up from previous runs
  if ← tarTestDir.pathExists then
    let _ ← IO.Process.run { cmd := "rm", args := #["-rf", tarTestDir.toString] }
  IO.FS.createDirAll (tarTestDir / "subdir")
  IO.FS.writeFile (tarTestDir / "hello.txt") "Hello from tar!"
  IO.FS.writeFile (tarTestDir / "subdir" / "nested.txt") "Nested file content here."
  IO.FS.writeFile (tarTestDir / "empty.txt") ""

  -- Create tar archive to ByteArray via stream
  let tarPath : System.FilePath := "/tmp/lean-zlib-test.tar"
  IO.FS.withFile tarPath .write fun h => do
    let stream := IO.FS.Stream.ofHandle h
    Tar.createFromDir stream tarTestDir
  IO.println "Tar create: OK"

  -- List entries
  let entries ← IO.FS.withFile tarPath .read fun h => do
    let stream := IO.FS.Stream.ofHandle h
    Tar.list stream
  IO.println s!"Tar entries: {entries.size}"
  -- Should have 3 files + 1 subdirectory = 4 entries
  unless entries.size == 4 do throw (IO.userError s!"tar list: expected 4 entries, got {entries.size}")
  -- Check that we can find our files
  let paths := entries.map (·.path)
  let strContains (haystack needle : String) : Bool :=
    (haystack.splitOn needle).length > 1
  let hasHello := paths.any (strContains · "hello.txt")
  let hasNested := paths.any (strContains · "nested.txt")
  let hasEmpty := paths.any (strContains · "empty.txt")
  let hasSubdir := paths.any (strContains · "subdir")
  unless hasHello && hasNested && hasEmpty && hasSubdir do
    throw (IO.userError s!"tar list: missing expected entries, got: {paths}")
  IO.println "Tar list: OK"

  -- Extract and verify roundtrip
  let extractDir : System.FilePath := "/tmp/lean-zlib-tar-extract"
  if ← extractDir.pathExists then
    let _ ← IO.Process.run { cmd := "rm", args := #["-rf", extractDir.toString] }
  IO.FS.createDirAll extractDir
  IO.FS.withFile tarPath .read fun h => do
    let stream := IO.FS.Stream.ofHandle h
    Tar.extract stream extractDir
  -- Verify extracted files
  let hello ← IO.FS.readFile (extractDir / "hello.txt")
  unless hello == "Hello from tar!" do throw (IO.userError s!"tar extract hello: {hello}")
  let nested ← IO.FS.readFile (extractDir / "subdir" / "nested.txt")
  unless nested == "Nested file content here." do throw (IO.userError s!"tar extract nested: {nested}")
  let emptyContent ← IO.FS.readFile (extractDir / "empty.txt")
  unless emptyContent == "" do throw (IO.userError "tar extract empty")
  IO.println "Tar extract roundtrip: OK"

  -- Test .tar.gz roundtrip
  let tarGzPath : System.FilePath := "/tmp/lean-zlib-test.tar.gz"
  Tar.createTarGz tarGzPath tarTestDir
  let tarGzMeta ← tarGzPath.metadata
  let tarGzSize := tarGzMeta.byteSize
  IO.println s!"Tar.gz size: {tarGzSize}"
  let extractGzDir : System.FilePath := "/tmp/lean-zlib-targz-extract"
  if ← extractGzDir.pathExists then
    let _ ← IO.Process.run { cmd := "rm", args := #["-rf", extractGzDir.toString] }
  IO.FS.createDirAll extractGzDir
  Tar.extractTarGz tarGzPath extractGzDir
  let helloGz ← IO.FS.readFile (extractGzDir / "hello.txt")
  unless helloGz == "Hello from tar!" do throw (IO.userError s!"tar.gz extract hello: {helloGz}")
  let nestedGz ← IO.FS.readFile (extractGzDir / "subdir" / "nested.txt")
  unless nestedGz == "Nested file content here." do throw (IO.userError s!"tar.gz extract nested: {nestedGz}")
  IO.println "Tar.gz roundtrip: OK"

  -- Test splitPath
  let some (pfx1, name1) := Tar.splitPath "short.txt" | throw (IO.userError "splitPath short")
  unless pfx1 == "" && name1 == "short.txt" do throw (IO.userError "splitPath short values")
  let longPath := "a/very/long/path/that/exceeds/one/hundred/characters/in/the/name/field/so/we/need/prefix/splitting/file.txt"
  let some (pfx2, _) := Tar.splitPath longPath | throw (IO.userError "splitPath long")
  unless !pfx2.isEmpty do throw (IO.userError "splitPath long should have prefix")
  IO.println "Tar splitPath: OK"

  -- Clean up
  let _ ← IO.Process.run { cmd := "rm", args := #["-rf", tarTestDir.toString] }
  let _ ← IO.Process.run { cmd := "rm", args := #["-rf", extractDir.toString] }
  let _ ← IO.Process.run { cmd := "rm", args := #["-rf", extractGzDir.toString] }
  let _ ← IO.Process.run { cmd := "rm", args := #["-f", tarPath.toString] }
  let _ ← IO.Process.run { cmd := "rm", args := #["-f", tarGzPath.toString] }

  IO.println "All tests passed!"
