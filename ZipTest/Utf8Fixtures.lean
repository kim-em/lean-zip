import ZipTest.Helpers

def ZipTest.Utf8Fixtures.tests : IO Unit := do
  -- backslash-slip.zip: Windows path traversal via ..\
  let bsSlipZipData ← readFixture "zip/security/backslash-slip.zip"
  let bsSlipZipPath ← writeFixtureTmp "backslash-slip.zip" bsSlipZipData
  let bsSlipZipExtract : System.FilePath := "/tmp/lean-zip-fixture-bs-slip-zip-extract"
  IO.FS.createDirAll bsSlipZipExtract
  assertThrows "ZIP security (backslash-slip.zip)"
    (Archive.extract bsSlipZipPath bsSlipZipExtract)
    "unsafe path"

  -- backslash-slip.tar: Windows path traversal via ..\
  let bsSlipTarData ← readFixture "tar/security/backslash-slip.tar"
  let bsSlipTarPath ← writeFixtureTmp "backslash-slip.tar" bsSlipTarData
  let bsSlipTarExtract : System.FilePath := "/tmp/lean-zip-fixture-bs-slip-tar-extract"
  IO.FS.createDirAll bsSlipTarExtract
  assertThrows "TAR security (backslash-slip.tar)"
    (IO.FS.withFile bsSlipTarPath .read fun h =>
      Tar.extract (IO.FS.Stream.ofHandle h) bsSlipTarExtract)
    "unsafe path"

  -- utf8-flag.zip: ZIP with UTF-8 flag (bit 11) and Unicode filename
  let utf8FlagData ← readFixture "zip/interop/utf8-flag.zip"
  let utf8FlagPath ← writeFixtureTmp "utf8-flag.zip" utf8FlagData
  let utf8FlagEntries ← Archive.list utf8FlagPath
  unless utf8FlagEntries.size == 1 do
    throw (IO.userError s!"utf8-flag.zip: expected 1 entry, got {utf8FlagEntries.size}")
  unless utf8FlagEntries[0]!.path == "café.txt" do
    throw (IO.userError s!"utf8-flag.zip: expected 'café.txt', got '{utf8FlagEntries[0]!.path}'")
  let utf8FlagContent ← Archive.extractFile utf8FlagPath "café.txt"
  unless String.fromUTF8! utf8FlagContent == "hello unicode" do
    throw (IO.userError "utf8-flag.zip: content mismatch")

  -- latin1-name.zip: ZIP without UTF-8 flag, Latin-1 encoded filename
  let latin1Data ← readFixture "zip/interop/latin1-name.zip"
  let latin1Path ← writeFixtureTmp "latin1-name.zip" latin1Data
  let latin1Entries ← Archive.list latin1Path
  unless latin1Entries.size == 1 do
    throw (IO.userError s!"latin1-name.zip: expected 1 entry, got {latin1Entries.size}")
  unless latin1Entries[0]!.path == "café.txt" do
    throw (IO.userError s!"latin1-name.zip: expected 'café.txt', got '{latin1Entries[0]!.path}'")

  -- invalid-utf8-with-flag.zip: UTF-8 flag set but name contains invalid UTF-8
  let invalidUtf8Data ← readFixture "zip/malformed/invalid-utf8-with-flag.zip"
  let invalidUtf8Path ← writeFixtureTmp "invalid-utf8-with-flag.zip" invalidUtf8Data
  assertThrows "ZIP malformed (invalid-utf8-with-flag.zip)"
    (do let _ ← Archive.list invalidUtf8Path; pure ())
    "invalid UTF-8"
  -- Clean up temp files
  for f in #["backslash-slip.zip", "backslash-slip.tar", "utf8-flag.zip",
             "latin1-name.zip", "invalid-utf8-with-flag.zip"] do
    let _ ← IO.Process.run { cmd := "rm", args := #["-f", s!"/tmp/lean-zip-fixture-{f}"] }
  for d in #["/tmp/lean-zip-fixture-bs-slip-zip-extract", "/tmp/lean-zip-fixture-bs-slip-tar-extract"] do
    let _ ← IO.Process.run { cmd := "rm", args := #["-rf", d] }
  IO.println "UTF-8 fixture tests: OK"
