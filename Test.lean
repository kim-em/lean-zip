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

  -- Clean up tar temps
  let _ ← IO.Process.run { cmd := "rm", args := #["-rf", tarTestDir.toString] }
  let _ ← IO.Process.run { cmd := "rm", args := #["-rf", extractDir.toString] }
  let _ ← IO.Process.run { cmd := "rm", args := #["-rf", extractGzDir.toString] }
  let _ ← IO.Process.run { cmd := "rm", args := #["-f", tarPath.toString] }
  let _ ← IO.Process.run { cmd := "rm", args := #["-f", tarGzPath.toString] }

  -- === ZIP tests ===

  -- Create test files
  let zipTestDir : System.FilePath := "/tmp/lean-zlib-zip-test"
  if ← zipTestDir.pathExists then
    let _ ← IO.Process.run { cmd := "rm", args := #["-rf", zipTestDir.toString] }
  IO.FS.createDirAll (zipTestDir / "sub")
  IO.FS.writeFile (zipTestDir / "hello.txt") "Hello from ZIP!"
  IO.FS.writeFile (zipTestDir / "sub" / "data.txt") "Some nested data for compression testing."
  -- Compressible data (should use deflate method 8)
  let mut compressible := ByteArray.empty
  for _ in List.range 100 do
    compressible := compressible ++ "Repeated text for compression. ".toUTF8
  IO.FS.writeBinFile (zipTestDir / "big.bin") compressible
  -- Empty file
  IO.FS.writeFile (zipTestDir / "empty.txt") ""

  -- Create ZIP from explicit file list
  let zipPath : System.FilePath := "/tmp/lean-zlib-test.zip"
  Zip.create zipPath #[
    ("hello.txt", zipTestDir / "hello.txt"),
    ("sub/data.txt", zipTestDir / "sub" / "data.txt"),
    ("big.bin", zipTestDir / "big.bin"),
    ("empty.txt", zipTestDir / "empty.txt")
  ]
  IO.println "ZIP create: OK"

  -- List entries
  let zipEntries ← Zip.list zipPath
  IO.println s!"ZIP entries: {zipEntries.size}"
  unless zipEntries.size == 4 do throw (IO.userError s!"zip list: expected 4, got {zipEntries.size}")
  -- Check method selection: big.bin should be deflated (method 8)
  let bigEntry := zipEntries.find? (·.path == "big.bin")
  match bigEntry with
  | some e =>
    unless e.method == 8 do throw (IO.userError s!"zip: big.bin should be deflated, got method {e.method}")
    unless e.compressedSize < e.uncompressedSize do
      throw (IO.userError "zip: big.bin compressed should be smaller")
    IO.println s!"ZIP method selection: big.bin deflated {e.uncompressedSize} → {e.compressedSize}"
  | none => throw (IO.userError "zip: big.bin not found in listing")
  IO.println "ZIP list: OK"

  -- Extract and verify roundtrip
  let zipExtractDir : System.FilePath := "/tmp/lean-zlib-zip-extract"
  if ← zipExtractDir.pathExists then
    let _ ← IO.Process.run { cmd := "rm", args := #["-rf", zipExtractDir.toString] }
  IO.FS.createDirAll zipExtractDir
  Zip.extract zipPath zipExtractDir
  let zHello ← IO.FS.readFile (zipExtractDir / "hello.txt")
  unless zHello == "Hello from ZIP!" do throw (IO.userError s!"zip extract hello: {zHello}")
  let zData ← IO.FS.readFile (zipExtractDir / "sub" / "data.txt")
  unless zData == "Some nested data for compression testing." do
    throw (IO.userError s!"zip extract data: {zData}")
  let zBig ← IO.FS.readBinFile (zipExtractDir / "big.bin")
  unless zBig.size == compressible.size do
    throw (IO.userError s!"zip extract big: size {zBig.size} != {compressible.size}")
  let zEmpty ← IO.FS.readFile (zipExtractDir / "empty.txt")
  unless zEmpty == "" do throw (IO.userError "zip extract empty")
  IO.println "ZIP extract roundtrip: OK"

  -- extractFile by name
  let singleFile ← Zip.extractFile zipPath "hello.txt"
  unless String.fromUTF8! singleFile == "Hello from ZIP!" do
    throw (IO.userError "zip extractFile")
  IO.println "ZIP extractFile: OK"

  -- createFromDir roundtrip
  let zipFromDirPath : System.FilePath := "/tmp/lean-zlib-test-fromdir.zip"
  Zip.createFromDir zipFromDirPath zipTestDir
  let dirEntries ← Zip.list zipFromDirPath
  IO.println s!"ZIP createFromDir entries: {dirEntries.size}"
  unless dirEntries.size == 4 do
    throw (IO.userError s!"zip createFromDir: expected 4, got {dirEntries.size}")
  let zipFromDirExtract : System.FilePath := "/tmp/lean-zlib-zip-fromdir-extract"
  if ← zipFromDirExtract.pathExists then
    let _ ← IO.Process.run { cmd := "rm", args := #["-rf", zipFromDirExtract.toString] }
  IO.FS.createDirAll zipFromDirExtract
  Zip.extract zipFromDirPath zipFromDirExtract
  let zHello2 ← IO.FS.readFile (zipFromDirExtract / "hello.txt")
  unless zHello2 == "Hello from ZIP!" do throw (IO.userError "zip fromDir hello")
  IO.println "ZIP createFromDir roundtrip: OK"

  -- Clean up zip temps
  let _ ← IO.Process.run { cmd := "rm", args := #["-rf", zipTestDir.toString] }
  let _ ← IO.Process.run { cmd := "rm", args := #["-rf", zipExtractDir.toString] }
  let _ ← IO.Process.run { cmd := "rm", args := #["-rf", zipFromDirExtract.toString] }
  let _ ← IO.Process.run { cmd := "rm", args := #["-f", zipPath.toString] }
  let _ ← IO.Process.run { cmd := "rm", args := #["-f", zipFromDirPath.toString] }

  -- ===== PAX/GNU tar tests =====

  -- Test PAX record parsing
  let paxData := "12 path=abc\n10 uid=42\n".toUTF8
  let records := Tar.parsePaxRecords paxData
  unless records.size == 2 do throw (IO.userError s!"pax parse: expected 2 records, got {records.size}")
  unless records[0]! == ("path", "abc") do throw (IO.userError "pax parse: record 0")
  unless records[1]! == ("uid", "42") do throw (IO.userError "pax parse: record 1")
  IO.println "PAX record parsing: OK"

  -- Test GNU base-256 numeric decode
  -- Encode 0x12345678 in base-256: 0x80 | high byte, then remaining bytes
  -- For a 12-byte field: 0x80 0x00 0x00 0x00 0x00 0x00 0x00 0x00 0x12 0x34 0x56 0x78
  let mut base256Field := ByteArray.empty
  base256Field := base256Field.push 0x80
  for _ in [:7] do base256Field := base256Field.push 0x00
  base256Field := base256Field.push 0x12
  base256Field := base256Field.push 0x34
  base256Field := base256Field.push 0x56
  base256Field := base256Field.push 0x78
  let decoded := Tar.readNumeric base256Field 0 12
  unless decoded == 0x12345678 do
    throw (IO.userError s!"gnu base-256: expected {0x12345678}, got {decoded}")
  IO.println "GNU base-256 decode: OK"

  -- Test PAX long path roundtrip
  let paxTestDir : System.FilePath := "/tmp/lean-zlib-pax-test"
  if ← paxTestDir.pathExists then
    let _ ← IO.Process.run { cmd := "rm", args := #["-rf", paxTestDir.toString] }
  IO.FS.createDirAll paxTestDir
  -- Create a deeply nested file with path > 255 chars
  let longDir := String.join (List.replicate 10 "a_long_directory_name" |>.intersperse "/")
  let longPath := s!"{longDir}/test_file.txt"
  IO.println s!"PAX long path length: {longPath.utf8ByteSize}"
  let fullDiskDir := paxTestDir / longDir
  IO.FS.createDirAll fullDiskDir
  IO.FS.writeFile (paxTestDir / longPath) "Long path content"
  -- Create tar
  let paxTarPath : System.FilePath := "/tmp/lean-zlib-pax-test.tar"
  IO.FS.withFile paxTarPath .write fun h => do
    let stream := IO.FS.Stream.ofHandle h
    Tar.createFromDir stream paxTestDir
  -- List and verify
  let paxEntries ← IO.FS.withFile paxTarPath .read fun h => do
    Tar.list (IO.FS.Stream.ofHandle h)
  let mut foundLong := false
  for e in paxEntries do
    if e.path == longPath then foundLong := true
  unless foundLong do
    throw (IO.userError s!"pax roundtrip: long path not found in listing")
  IO.println "PAX long path list: OK"
  -- Extract and verify
  let paxExtractDir : System.FilePath := "/tmp/lean-zlib-pax-extract"
  if ← paxExtractDir.pathExists then
    let _ ← IO.Process.run { cmd := "rm", args := #["-rf", paxExtractDir.toString] }
  IO.FS.createDirAll paxExtractDir
  IO.FS.withFile paxTarPath .read fun h => do
    Tar.extract (IO.FS.Stream.ofHandle h) paxExtractDir
  let paxContent ← IO.FS.readFile (paxExtractDir / longPath)
  unless paxContent == "Long path content" do
    throw (IO.userError "pax roundtrip: content mismatch")
  IO.println "PAX long path roundtrip: OK"
  -- Clean up PAX temps
  let _ ← IO.Process.run { cmd := "rm", args := #["-rf", paxTestDir.toString] }
  let _ ← IO.Process.run { cmd := "rm", args := #["-rf", paxExtractDir.toString] }
  let _ ← IO.Process.run { cmd := "rm", args := #["-f", paxTarPath.toString] }

  -- Test PAX apply overrides
  let baseEntry : Tar.Entry := { path := "short.txt", size := 100 }
  let overridden := Tar.applyPaxOverrides baseEntry #[("path", "very/long/path.txt"), ("size", "99999")]
  unless overridden.path == "very/long/path.txt" do
    throw (IO.userError "pax override: path")
  unless overridden.size == 99999 do
    throw (IO.userError "pax override: size")
  IO.println "PAX apply overrides: OK"

  -- ===== Zstd tests =====

  -- Whole-buffer roundtrip
  let zstdCompressed ← Zstd.compress big
  IO.println s!"Zstd compressed size: {zstdCompressed.size}"
  let zstdDecompressed ← Zstd.decompress zstdCompressed
  unless zstdDecompressed.beq big do throw (IO.userError "zstd roundtrip")
  IO.println "Zstd roundtrip: OK"

  -- Different compression levels
  let zstdFast ← Zstd.compress big 1
  let zstdBest ← Zstd.compress big 19
  IO.println s!"Zstd level 1: {zstdFast.size}, level 19: {zstdBest.size}"
  let zstdFastDec ← Zstd.decompress zstdFast
  unless zstdFastDec.beq big do throw (IO.userError "zstd level 1 roundtrip")
  let zstdBestDec ← Zstd.decompress zstdBest
  unless zstdBestDec.beq big do throw (IO.userError "zstd level 19 roundtrip")
  IO.println "Zstd compression levels: OK"

  -- Empty input
  let zstdEmpty ← Zstd.compress ByteArray.empty
  let zstdEmptyDec ← Zstd.decompress zstdEmpty
  unless zstdEmptyDec.size == 0 do throw (IO.userError "zstd empty roundtrip")
  IO.println "Zstd empty input: OK"

  -- Streaming roundtrip
  let zstdStreamTestFile : System.FilePath := "/tmp/lean-zlib-zstd-test-input"
  let zstdStreamCompFile : System.FilePath := "/tmp/lean-zlib-zstd-test-input.zst"
  IO.FS.writeBinFile zstdStreamTestFile big
  Zstd.compressFile zstdStreamTestFile
  Zstd.decompressFile zstdStreamCompFile
  let zstdStreamDec ← IO.FS.readBinFile zstdStreamTestFile
  unless zstdStreamDec.beq big do throw (IO.userError "zstd file roundtrip")
  IO.println "Zstd file compress/decompress: OK"
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
  IO.println s!"Zstd streaming compressed size: {zstdStreamBuf.size}"
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
  IO.println "Zstd streaming roundtrip: OK"

  -- Large data
  let mut zstdLarge := ByteArray.empty
  for _ in List.range 2000 do
    zstdLarge := zstdLarge ++ original
  let zstdLargeComp ← Zstd.compress zstdLarge
  IO.println s!"Zstd large data: {zstdLarge.size} → {zstdLargeComp.size}"
  let zstdLargeDec ← Zstd.decompress zstdLargeComp
  unless zstdLargeDec.beq zstdLarge do throw (IO.userError "zstd large roundtrip")
  IO.println "Zstd large data roundtrip: OK"

  IO.println "All tests passed!"
