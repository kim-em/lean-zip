import ZipTest.Helpers

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
  let records := Tar.parsePaxRecords paxData
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
