import ZipTest.Helpers

def ZipTest.ZipFixtures.tests : IO Unit := do
  -- go-test.zip: 2 entries (test.txt deflated, gophercolor16x16.png stored)
  let goTestData ← readFixture "zip/interop/go-test.zip"
  let goTestPath ← writeFixtureTmp "go-test.zip" goTestData
  let goTestEntries ← Archive.list goTestPath
  unless goTestEntries.size == 2 do
    throw (IO.userError s!"go-test.zip: expected 2 entries, got {goTestEntries.size}")
  let goTestTxt := goTestEntries.find? (·.path == "test.txt")
  match goTestTxt with
  | some e =>
    unless e.method == 8 do throw (IO.userError s!"go-test.zip: test.txt expected method 8, got {e.method}")
    unless e.uncompressedSize == 26 do
      throw (IO.userError s!"go-test.zip: test.txt expected size 26, got {e.uncompressedSize}")
  | none => throw (IO.userError "go-test.zip: test.txt not found")
  let goTestContent ← Archive.extractFile goTestPath "test.txt"
  unless String.fromUTF8! goTestContent == "This is a test text file.\n" do
    throw (IO.userError "go-test.zip: test.txt content mismatch")

  -- go-zip64.zip: 1 entry, ZIP64 format
  let goZip64Data ← readFixture "zip/interop/go-zip64.zip"
  let goZip64Path ← writeFixtureTmp "go-zip64.zip" goZip64Data
  let goZip64Entries ← Archive.list goZip64Path
  unless goZip64Entries.size == 1 do
    throw (IO.userError s!"go-zip64.zip: expected 1 entry, got {goZip64Entries.size}")
  let goZip64Content ← Archive.extractFile goZip64Path "README"
  unless String.fromUTF8! goZip64Content == "This small file is in ZIP64 format.\n" do
    throw (IO.userError "go-zip64.zip: README content mismatch")

  -- go-unix.zip: 4 entries from Info-ZIP on Linux
  let goUnixData ← readFixture "zip/interop/go-unix.zip"
  let goUnixPath ← writeFixtureTmp "go-unix.zip" goUnixData
  let goUnixEntries ← Archive.list goUnixPath
  unless goUnixEntries.size == 4 do
    throw (IO.userError s!"go-unix.zip: expected 4 entries, got {goUnixEntries.size}")
  let goUnixExtractDir : System.FilePath := "/tmp/lean-zip-fixture-go-unix-extract"
  if ← goUnixExtractDir.pathExists then
    let _ ← IO.Process.run { cmd := "rm", args := #["-rf", goUnixExtractDir.toString] }
  IO.FS.createDirAll goUnixExtractDir
  Archive.extract goUnixPath goUnixExtractDir
  let goUnixHello ← IO.FS.readFile (goUnixExtractDir / "hello")
  unless goUnixHello == "world \r\n" do
    throw (IO.userError s!"go-unix.zip: hello content mismatch: {repr goUnixHello}")
  let goUnixBar ← IO.FS.readFile (goUnixExtractDir / "dir" / "bar")
  unless goUnixBar == "foo \r\n" do
    throw (IO.userError s!"go-unix.zip: dir/bar content mismatch: {repr goUnixBar}")
  let _ ← IO.Process.run { cmd := "rm", args := #["-rf", goUnixExtractDir.toString] }

  -- go-crc32-not-streamed.zip: 2 entries, CRC in local header
  let goCrc32Data ← readFixture "zip/interop/go-crc32-not-streamed.zip"
  let goCrc32Path ← writeFixtureTmp "go-crc32-not-streamed.zip" goCrc32Data
  let goCrc32Foo ← Archive.extractFile goCrc32Path "foo.txt"
  unless String.fromUTF8! goCrc32Foo == "foo\n" do
    throw (IO.userError "go-crc32-not-streamed.zip: foo.txt content mismatch")
  let goCrc32Bar ← Archive.extractFile goCrc32Path "bar.txt"
  unless String.fromUTF8! goCrc32Bar == "bar\n" do
    throw (IO.userError "go-crc32-not-streamed.zip: bar.txt content mismatch")

  -- === ZIP malformed fixtures ===

  let tooShortData ← readFixture "zip/malformed/too-short.zip"
  let tooShortPath ← writeFixtureTmp "too-short.zip" tooShortData
  assertThrows "ZIP malformed (too-short.zip)"
    (do let _ ← Archive.list tooShortPath; pure ())
    "end of central directory"

  let noEocdData ← readFixture "zip/malformed/no-eocd.zip"
  let noEocdPath ← writeFixtureTmp "no-eocd.zip" noEocdData
  assertThrows "ZIP malformed (no-eocd.zip)"
    (do let _ ← Archive.list noEocdPath; pure ())
    "end of central directory"

  let cdPastData ← readFixture "zip/malformed/cd-past-eof.zip"
  let cdPastPath ← writeFixtureTmp "cd-past-eof.zip" cdPastData
  assertThrows "ZIP malformed (cd-past-eof.zip)"
    (do let _ ← Archive.list cdPastPath; pure ())
    "central directory"

  let badCrcZipData ← readFixture "zip/malformed/bad-crc.zip"
  let badCrcZipPath ← writeFixtureTmp "bad-crc.zip" badCrcZipData
  let badCrcExtractDir : System.FilePath := "/tmp/lean-zip-fixture-bad-crc-extract"
  IO.FS.createDirAll badCrcExtractDir
  assertThrows "ZIP malformed (bad-crc.zip)"
    (Archive.extract badCrcZipPath badCrcExtractDir)
    "CRC32 mismatch"

  let badMethodData ← readFixture "zip/malformed/bad-method.zip"
  let badMethodPath ← writeFixtureTmp "bad-method.zip" badMethodData
  let badMethodExtractDir : System.FilePath := "/tmp/lean-zip-fixture-bad-method-extract"
  IO.FS.createDirAll badMethodExtractDir
  assertThrows "ZIP malformed (bad-method.zip)"
    (Archive.extract badMethodPath badMethodExtractDir)
    "unsupported method"

  -- === ZIP security fixtures ===

  let zipSlipData ← readFixture "zip/security/zip-slip.zip"
  let zipSlipPath ← writeFixtureTmp "zip-slip.zip" zipSlipData
  let zipSlipExtractDir : System.FilePath := "/tmp/lean-zip-fixture-zip-slip-extract"
  IO.FS.createDirAll zipSlipExtractDir
  assertThrows "ZIP security (zip-slip.zip)"
    (Archive.extract zipSlipPath zipSlipExtractDir)
    "unsafe path"

  let absPathData ← readFixture "zip/security/absolute-path.zip"
  let absPathPath ← writeFixtureTmp "absolute-path.zip" absPathData
  let absPathExtractDir : System.FilePath := "/tmp/lean-zip-fixture-abs-path-extract"
  IO.FS.createDirAll absPathExtractDir
  assertThrows "ZIP security (absolute-path.zip)"
    (Archive.extract absPathPath absPathExtractDir)
    "unsafe path"
  -- Clean up temp files
  for f in #["go-test.zip", "go-zip64.zip", "go-unix.zip", "go-crc32-not-streamed.zip",
             "too-short.zip", "no-eocd.zip", "cd-past-eof.zip", "bad-crc.zip",
             "bad-method.zip", "zip-slip.zip", "absolute-path.zip"] do
    let _ ← IO.Process.run { cmd := "rm", args := #["-f", s!"/tmp/lean-zip-fixture-{f}"] }
  for d in #["/tmp/lean-zip-fixture-bad-crc-extract", "/tmp/lean-zip-fixture-bad-method-extract",
             "/tmp/lean-zip-fixture-zip-slip-extract", "/tmp/lean-zip-fixture-abs-path-extract"] do
    let _ ← IO.Process.run { cmd := "rm", args := #["-rf", d] }
  IO.println "ZIP fixture tests: OK"
