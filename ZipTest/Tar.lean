import ZipTest.Helpers

/-! Tests for tar archive creation, listing, extraction, tar.gz roundtrips, and PAX record parsing. -/

/-- maxTotalSize whole-archive bomb regression (SECURITY_INVENTORY Rec. 4):
    a three-entry tar whose per-entry sizes pass the `maxEntrySize` check
    individually must still be rejected by the running-sum check when the
    cumulative uncompressed bytes exceed `maxTotalSize`. Per-entry payloads
    are 100 bytes each (total 300); at `maxTotalSize := 299` the cap trips
    on the third entry; at `maxTotalSize := 300` all three entries fit
    exactly. Both the streaming .tar.gz and the native .tar.gz extractors
    forward the cap to `Tar.extract`. Extracted as a top-level helper to
    keep `ZipTest.Tar.tests`'s single `do` block under the elaborator's
    recursion limit. -/
private def runMaxTotalSizeBombTest : IO Unit := do
  let totSrcDir : System.FilePath := "/tmp/lean-zip-tar-total-src"
  let totTarPath : System.FilePath := "/tmp/lean-zip-tar-total.tar"
  let totTarGzPath : System.FilePath := "/tmp/lean-zip-tar-total.tar.gz"
  let totExtractDir : System.FilePath := "/tmp/lean-zip-tar-total-extract"
  if ← totSrcDir.pathExists then
    let _ ← IO.Process.run { cmd := "rm", args := #["-rf", totSrcDir.toString] }
  IO.FS.createDirAll totSrcDir
  let totPayload : ByteArray := ByteArray.mk (Array.replicate 100 (0x41 : UInt8))
  IO.FS.writeBinFile (totSrcDir / "a.txt") totPayload
  IO.FS.writeBinFile (totSrcDir / "b.txt") totPayload
  IO.FS.writeBinFile (totSrcDir / "c.txt") totPayload
  IO.FS.withFile totTarPath .write fun h =>
    Tar.create (IO.FS.Stream.ofHandle h) totSrcDir
      #[totSrcDir / "a.txt", totSrcDir / "b.txt", totSrcDir / "c.txt"]
  Tar.createTarGz totTarGzPath totSrcDir
  -- Tar.extract: cap trips on third entry.
  if ← totExtractDir.pathExists then
    let _ ← IO.Process.run { cmd := "rm", args := #["-rf", totExtractDir.toString] }
  IO.FS.createDirAll totExtractDir
  let totOverResult ← (IO.FS.withFile totTarPath .read fun h =>
    Tar.extract (IO.FS.Stream.ofHandle h) totExtractDir (maxTotalSize := 299)).toBaseIO
  match totOverResult with
  | .ok _ => throw (IO.userError "tar: maxTotalSize bomb should have been rejected by extract")
  | .error e =>
    unless (toString e).contains "exceeds whole-archive limit" do
      throw (IO.userError s!"tar: maxTotalSize bomb wrong error from extract: {e}")
  -- Tar.extract: exact-fit succeeds.
  let _ ← IO.Process.run { cmd := "rm", args := #["-rf", totExtractDir.toString] }
  IO.FS.createDirAll totExtractDir
  IO.FS.withFile totTarPath .read fun h =>
    Tar.extract (IO.FS.Stream.ofHandle h) totExtractDir (maxTotalSize := 300)
  -- Tar.extractTarGz: streaming .tar.gz, same bomb.
  let _ ← IO.Process.run { cmd := "rm", args := #["-rf", totExtractDir.toString] }
  IO.FS.createDirAll totExtractDir
  let totGzOverResult ←
    (Tar.extractTarGz totTarGzPath totExtractDir (maxTotalSize := 299)).toBaseIO
  match totGzOverResult with
  | .ok _ => throw (IO.userError "tar.gz: maxTotalSize bomb should have been rejected by extractTarGz")
  | .error e =>
    unless (toString e).contains "exceeds whole-archive limit" do
      throw (IO.userError s!"tar.gz: maxTotalSize bomb wrong error from extractTarGz: {e}")
  let _ ← IO.Process.run { cmd := "rm", args := #["-rf", totExtractDir.toString] }
  IO.FS.createDirAll totExtractDir
  Tar.extractTarGz totTarGzPath totExtractDir (maxTotalSize := 300)
  -- Tar.extractTarGzNative: whole-buffer .tar.gz, same bomb.
  let _ ← IO.Process.run { cmd := "rm", args := #["-rf", totExtractDir.toString] }
  IO.FS.createDirAll totExtractDir
  let totGzNatOverResult ←
    (Tar.extractTarGzNative totTarGzPath totExtractDir (maxTotalSize := 299)).toBaseIO
  match totGzNatOverResult with
  | .ok _ => throw (IO.userError "tar.gz native: maxTotalSize bomb should have been rejected by extractTarGzNative")
  | .error e =>
    unless (toString e).contains "exceeds whole-archive limit" do
      throw (IO.userError s!"tar.gz native: maxTotalSize bomb wrong error from extractTarGzNative: {e}")
  let _ ← IO.Process.run { cmd := "rm", args := #["-rf", totExtractDir.toString] }
  IO.FS.createDirAll totExtractDir
  Tar.extractTarGzNative totTarGzPath totExtractDir (maxTotalSize := 300)
  let _ ← IO.Process.run { cmd := "rm", args := #["-rf", totSrcDir.toString] }
  let _ ← IO.Process.run { cmd := "rm", args := #["-rf", totExtractDir.toString] }
  let _ ← IO.Process.run { cmd := "rm", args := #["-f", totTarPath.toString] }
  let _ ← IO.Process.run { cmd := "rm", args := #["-f", totTarGzPath.toString] }

def ZipTest.Tar.tests : IO Unit := do
  -- Create a temp directory with test files
  let tarTestDir : System.FilePath := "/tmp/lean-zlib-tar-test"
  if ← tarTestDir.pathExists then
    let _ ← IO.Process.run { cmd := "rm", args := #["-rf", tarTestDir.toString] }
  IO.FS.createDirAll (tarTestDir / "subdir")
  IO.FS.writeFile (tarTestDir / "hello.txt") "Hello from tar!"
  IO.FS.writeFile (tarTestDir / "subdir" / "nested.txt") "Nested file content here."
  IO.FS.writeFile (tarTestDir / "empty.txt") ""

  -- Create tar archive
  let tarPath : System.FilePath := "/tmp/lean-zlib-test.tar"
  IO.FS.withFile tarPath .write fun h => do
    let stream := IO.FS.Stream.ofHandle h
    Tar.createFromDir stream tarTestDir

  -- List entries
  let entries ← IO.FS.withFile tarPath .read fun h => do
    let stream := IO.FS.Stream.ofHandle h
    Tar.list stream
  unless entries.size == 4 do throw (IO.userError s!"tar list: expected 4 entries, got {entries.size}")
  let paths := entries.map (·.path)
  let strContains (haystack needle : String) : Bool :=
    (haystack.splitOn needle).length > 1
  let hasHello := paths.any (strContains · "hello.txt")
  let hasNested := paths.any (strContains · "nested.txt")
  let hasEmpty := paths.any (strContains · "empty.txt")
  let hasSubdir := paths.any (strContains · "subdir")
  unless hasHello && hasNested && hasEmpty && hasSubdir do
    throw (IO.userError s!"tar list: missing expected entries, got: {paths}")

  -- Extract and verify roundtrip
  let extractDir : System.FilePath := "/tmp/lean-zlib-tar-extract"
  if ← extractDir.pathExists then
    let _ ← IO.Process.run { cmd := "rm", args := #["-rf", extractDir.toString] }
  IO.FS.createDirAll extractDir
  IO.FS.withFile tarPath .read fun h => do
    let stream := IO.FS.Stream.ofHandle h
    Tar.extract stream extractDir
  let hello ← IO.FS.readFile (extractDir / "hello.txt")
  unless hello == "Hello from tar!" do throw (IO.userError s!"tar extract hello: {hello}")
  let nested ← IO.FS.readFile (extractDir / "subdir" / "nested.txt")
  unless nested == "Nested file content here." do throw (IO.userError s!"tar extract nested: {nested}")
  let emptyContent ← IO.FS.readFile (extractDir / "empty.txt")
  unless emptyContent == "" do throw (IO.userError "tar extract empty")

  -- Test .tar.gz roundtrip
  let tarGzPath : System.FilePath := "/tmp/lean-zlib-test.tar.gz"
  Tar.createTarGz tarGzPath tarTestDir
  let extractGzDir : System.FilePath := "/tmp/lean-zlib-targz-extract"
  if ← extractGzDir.pathExists then
    let _ ← IO.Process.run { cmd := "rm", args := #["-rf", extractGzDir.toString] }
  IO.FS.createDirAll extractGzDir
  Tar.extractTarGz tarGzPath extractGzDir
  let helloGz ← IO.FS.readFile (extractGzDir / "hello.txt")
  unless helloGz == "Hello from tar!" do throw (IO.userError s!"tar.gz extract hello: {helloGz}")
  let nestedGz ← IO.FS.readFile (extractGzDir / "subdir" / "nested.txt")
  unless nestedGz == "Nested file content here." do throw (IO.userError s!"tar.gz extract nested: {nestedGz}")

  -- maxEntrySize bomb regression: a tar entry whose declared size exceeds
  -- the limit must be rejected before any payload is read (Zip/Tar.lean:565-566).
  let bombSrcDir : System.FilePath := "/tmp/lean-zip-tar-bomb-src"
  let bombTarPath : System.FilePath := "/tmp/lean-zip-tar-bomb.tar"
  let bombExtractDir : System.FilePath := "/tmp/lean-zip-tar-bomb-extract"
  if ← bombSrcDir.pathExists then
    let _ ← IO.Process.run { cmd := "rm", args := #["-rf", bombSrcDir.toString] }
  IO.FS.createDirAll bombSrcDir
  let bombPayload ← mkTestData  -- 6200 bytes, well above the 100-byte threshold
  IO.FS.writeBinFile (bombSrcDir / "bomb.txt") bombPayload
  IO.FS.withFile bombTarPath .write fun h =>
    Tar.create (IO.FS.Stream.ofHandle h) bombSrcDir #[bombSrcDir / "bomb.txt"]
  if ← bombExtractDir.pathExists then
    let _ ← IO.Process.run { cmd := "rm", args := #["-rf", bombExtractDir.toString] }
  IO.FS.createDirAll bombExtractDir
  let tarBombResult ← (IO.FS.withFile bombTarPath .read fun h =>
    Tar.extract (IO.FS.Stream.ofHandle h) bombExtractDir (maxEntrySize := 10)).toBaseIO
  match tarBombResult with
  | .ok _ => throw (IO.userError "tar: maxEntrySize bomb should have been rejected by extract")
  | .error e =>
    unless (toString e).contains "exceeds limit" do
      throw (IO.userError s!"tar: maxEntrySize bomb wrong error: {e}")

  -- maxOutputSize bomb regression for Tar.extractTarGzNative: gzip the bomb
  -- tar and confirm the native gzip decoder rejects it before any tar parsing.
  -- The substring "exceeds maximum size" is what `Inflate.inflateRaw` actually
  -- emits (Zip/Native/Inflate.lean:269,285,321) when the per-member budget
  -- passed in by `GzipDecode.decompress` is exhausted.
  let bombTarBytes ← IO.FS.readBinFile bombTarPath
  let bombGzPath : System.FilePath := "/tmp/lean-zip-tar-bomb.tar.gz"
  let bombGz ← Gzip.compress bombTarBytes
  IO.FS.writeBinFile bombGzPath bombGz
  let gzBombResult ← (Tar.extractTarGzNative bombGzPath bombExtractDir
    (maxEntrySize := 0) (maxOutputSize := 10)).toBaseIO
  match gzBombResult with
  | .ok _ => throw (IO.userError "tar.gz: maxOutputSize bomb should have been rejected")
  | .error e =>
    unless (toString e).contains "exceeds maximum size" do
      throw (IO.userError s!"tar.gz: maxOutputSize bomb wrong error: {e}")
  let _ ← IO.Process.run { cmd := "rm", args := #["-rf", bombSrcDir.toString] }
  let _ ← IO.Process.run { cmd := "rm", args := #["-rf", bombExtractDir.toString] }
  let _ ← IO.Process.run { cmd := "rm", args := #["-f", bombTarPath.toString] }
  let _ ← IO.Process.run { cmd := "rm", args := #["-f", bombGzPath.toString] }

  runMaxTotalSizeBombTest

  -- Test splitPath
  let some (pfx1, name1) := Tar.splitPath "short.txt" | throw (IO.userError "splitPath short")
  unless pfx1 == "" && name1 == "short.txt" do throw (IO.userError "splitPath short values")
  let longPath := "a/very/long/path/that/exceeds/one/hundred/characters/in/the/name/field/so/we/need/prefix/splitting/file.txt"
  let some (pfx2, _) := Tar.splitPath longPath | throw (IO.userError "splitPath long")
  unless !pfx2.isEmpty do throw (IO.userError "splitPath long should have prefix")

  -- Clean up tar temps
  let _ ← IO.Process.run { cmd := "rm", args := #["-rf", tarTestDir.toString] }
  let _ ← IO.Process.run { cmd := "rm", args := #["-rf", extractDir.toString] }
  let _ ← IO.Process.run { cmd := "rm", args := #["-rf", extractGzDir.toString] }
  let _ ← IO.Process.run { cmd := "rm", args := #["-f", tarPath.toString] }
  let _ ← IO.Process.run { cmd := "rm", args := #["-f", tarGzPath.toString] }

  -- PAX record parsing
  let paxData := "12 path=abc\n10 uid=42\n".toUTF8
  let records ← IO.ofExcept (Tar.parsePaxRecords paxData)
  unless records.size == 2 do throw (IO.userError s!"pax parse: expected 2 records, got {records.size}")
  unless records[0]! == ("path", "abc") do throw (IO.userError "pax parse: record 0")
  unless records[1]! == ("uid", "42") do throw (IO.userError "pax parse: record 1")

  -- GNU base-256 numeric decode
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

  -- PAX long path roundtrip
  let paxTestDir : System.FilePath := "/tmp/lean-zlib-pax-test"
  if ← paxTestDir.pathExists then
    let _ ← IO.Process.run { cmd := "rm", args := #["-rf", paxTestDir.toString] }
  IO.FS.createDirAll paxTestDir
  let longDir := String.join (List.replicate 10 "a_long_directory_name" |>.intersperse "/")
  let longPath := s!"{longDir}/test_file.txt"
  let fullDiskDir := paxTestDir / longDir
  IO.FS.createDirAll fullDiskDir
  IO.FS.writeFile (paxTestDir / longPath) "Long path content"
  let paxTarPath : System.FilePath := "/tmp/lean-zlib-pax-test.tar"
  IO.FS.withFile paxTarPath .write fun h => do
    let stream := IO.FS.Stream.ofHandle h
    Tar.createFromDir stream paxTestDir
  let paxEntries ← IO.FS.withFile paxTarPath .read fun h => do
    Tar.list (IO.FS.Stream.ofHandle h)
  let mut foundLong := false
  for e in paxEntries do
    if e.path == longPath then foundLong := true
  unless foundLong do
    throw (IO.userError s!"pax roundtrip: long path not found in listing")
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
  -- Clean up PAX temps
  let _ ← IO.Process.run { cmd := "rm", args := #["-rf", paxTestDir.toString] }
  let _ ← IO.Process.run { cmd := "rm", args := #["-rf", paxExtractDir.toString] }
  let _ ← IO.Process.run { cmd := "rm", args := #["-f", paxTarPath.toString] }

  -- Tar extraction with fragmenting stream (Bug #2: padding short read robustness)
  -- Create a tar with files whose sizes induce padding (not multiples of 512)
  let fragTestDir : System.FilePath := "/tmp/lean-zip-tar-frag-test"
  if ← fragTestDir.pathExists then
    let _ ← IO.Process.run { cmd := "rm", args := #["-rf", fragTestDir.toString] }
  IO.FS.createDirAll fragTestDir
  -- 15 bytes → 497 bytes padding; 300 bytes → 212 bytes padding
  IO.FS.writeFile (fragTestDir / "small.txt") "fifteen chars!!"
  IO.FS.writeBinFile (fragTestDir / "medium.bin") (ByteArray.mk (Array.replicate 300 42))
  let fragTarPath : System.FilePath := "/tmp/lean-zip-tar-frag.tar"
  IO.FS.withFile fragTarPath .write fun h =>
    Tar.createFromDir (IO.FS.Stream.ofHandle h) fragTestDir
  -- Read tar into memory, wrap in fragmenting stream (1 byte at a time)
  let tarBytes ← IO.FS.readBinFile fragTarPath
  let fragStream := fragmentingStream (← byteArrayReadStream tarBytes) 1
  let fragExtractDir : System.FilePath := "/tmp/lean-zip-tar-frag-extract"
  if ← fragExtractDir.pathExists then
    let _ ← IO.Process.run { cmd := "rm", args := #["-rf", fragExtractDir.toString] }
  IO.FS.createDirAll fragExtractDir
  Tar.extract fragStream fragExtractDir
  -- Verify extracted content
  let fragSmall ← IO.FS.readFile (fragExtractDir / "small.txt")
  unless fragSmall == "fifteen chars!!" do
    throw (IO.userError s!"tar fragmenting extract small: got '{fragSmall}'")
  let fragMedium ← IO.FS.readBinFile (fragExtractDir / "medium.bin")
  unless fragMedium.size == 300 do
    throw (IO.userError s!"tar fragmenting extract medium: size {fragMedium.size} != 300")
  -- Clean up
  let _ ← IO.Process.run { cmd := "rm", args := #["-rf", fragTestDir.toString] }
  let _ ← IO.Process.run { cmd := "rm", args := #["-rf", fragExtractDir.toString] }
  let _ ← IO.Process.run { cmd := "rm", args := #["-f", fragTarPath.toString] }

  -- PAX apply overrides
  let baseEntry : Tar.Entry := { path := "short.txt", size := 100 }
  let overridden := Tar.applyPaxOverrides baseEntry #[("path", "very/long/path.txt"), ("size", "99999")]
  unless overridden.path == "very/long/path.txt" do
    throw (IO.userError "pax override: path")
  unless overridden.size == 99999 do
    throw (IO.userError "pax override: size")
  IO.println "Tar tests: OK"
