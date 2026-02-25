import ZipTest.Helpers

/-! Tests for tar interop: UStar, GNU, PAX formats, long paths, and malformed/security fixtures. -/

def ZipTest.TarFixtures.tests : IO Unit := do
  -- go-ustar.tar: UStar format with prefix/name path splitting
  let goUstarData ← readFixture "tar/interop/go-ustar.tar"
  let goUstarPath ← writeFixtureTmp "go-ustar.tar" goUstarData
  let goUstarEntries ← IO.FS.withFile goUstarPath .read fun h =>
    Tar.list (IO.FS.Stream.ofHandle h)
  unless goUstarEntries.size == 1 do
    throw (IO.userError s!"go-ustar.tar: expected 1 entry, got {goUstarEntries.size}")
  let goUstarEntry := goUstarEntries[0]!
  let expectedUstarPath := String.join (List.replicate 15 "longname/") ++ "file.txt"
  unless goUstarEntry.path == expectedUstarPath do
    throw (IO.userError s!"go-ustar.tar: expected exact path '{expectedUstarPath}', got '{goUstarEntry.path}'")
  unless goUstarEntry.size == 6 do
    throw (IO.userError s!"go-ustar.tar: expected size 6, got {goUstarEntry.size}")
  let goUstarExtract : System.FilePath := "/tmp/lean-zip-fixture-go-ustar-extract"
  if ← goUstarExtract.pathExists then
    let _ ← IO.Process.run { cmd := "rm", args := #["-rf", goUstarExtract.toString] }
  IO.FS.createDirAll goUstarExtract
  IO.FS.withFile goUstarPath .read fun h =>
    Tar.extract (IO.FS.Stream.ofHandle h) goUstarExtract
  let goUstarContent ← IO.FS.readFile (goUstarExtract / goUstarEntry.path)
  unless goUstarContent == "hello\n" do
    throw (IO.userError s!"go-ustar.tar: content mismatch: {repr goUstarContent}")
  let _ ← IO.Process.run { cmd := "rm", args := #["-rf", goUstarExtract.toString] }

  -- go-gnu.tar: GNU format (tests magic field compatibility)
  let goGnuData ← readFixture "tar/interop/go-gnu.tar"
  let goGnuPath ← writeFixtureTmp "go-gnu.tar" goGnuData
  let goGnuEntries ← IO.FS.withFile goGnuPath .read fun h =>
    Tar.list (IO.FS.Stream.ofHandle h)
  unless goGnuEntries.size == 2 do
    throw (IO.userError s!"go-gnu.tar: expected 2 entries, got {goGnuEntries.size}")
  let goGnuSmall := goGnuEntries.find? (·.path == "small.txt")
  match goGnuSmall with
  | some e => unless e.size == 5 do throw (IO.userError s!"go-gnu.tar: small.txt size {e.size}")
  | none => throw (IO.userError "go-gnu.tar: small.txt not found")

  -- go-pax.tar: PAX format with long path and symlink
  let goPaxData ← readFixture "tar/interop/go-pax.tar"
  let goPaxPath ← writeFixtureTmp "go-pax.tar" goPaxData
  let goPaxEntries ← IO.FS.withFile goPaxPath .read fun h =>
    Tar.list (IO.FS.Stream.ofHandle h)
  unless goPaxEntries.size == 2 do
    throw (IO.userError s!"go-pax.tar: expected 2 entries, got {goPaxEntries.size}")
  let goPaxFirst := goPaxEntries[0]!
  unless goPaxFirst.path.startsWith "a/" do
    throw (IO.userError s!"go-pax.tar: expected path starting with 'a/', got {goPaxFirst.path}")
  unless goPaxFirst.path.length > 100 do
    throw (IO.userError s!"go-pax.tar: expected long path (>100 chars), got {goPaxFirst.path.length}")
  unless goPaxFirst.size == 7 do
    throw (IO.userError s!"go-pax.tar: expected size 7, got {goPaxFirst.size}")
  let goPaxSecond := goPaxEntries[1]!
  unless goPaxSecond.path == "a/b" do
    throw (IO.userError s!"go-pax.tar: expected symlink path 'a/b', got '{goPaxSecond.path}'")
  unless goPaxSecond.typeflag == 0x32 do
    throw (IO.userError s!"go-pax.tar: expected symlink typeflag '2', got {goPaxSecond.typeflag}")
  unless goPaxSecond.linkname.length > 100 do
    throw (IO.userError s!"go-pax.tar: expected long linkname (>100 chars), got {goPaxSecond.linkname.length}")

  -- system-tar.tar: tar from system GNU tar
  let sysTarData ← readFixture "tar/interop/system-tar.tar"
  let sysTarPath ← writeFixtureTmp "system-tar.tar" sysTarData
  let sysTarEntries ← IO.FS.withFile sysTarPath .read fun h =>
    Tar.list (IO.FS.Stream.ofHandle h)
  unless sysTarEntries.size > 0 do
    throw (IO.userError "system-tar.tar: expected at least 1 entry")
  let sysTarExtract : System.FilePath := "/tmp/lean-zip-fixture-system-tar-extract"
  if ← sysTarExtract.pathExists then
    let _ ← IO.Process.run { cmd := "rm", args := #["-rf", sysTarExtract.toString] }
  IO.FS.createDirAll sysTarExtract
  IO.FS.withFile sysTarPath .read fun h =>
    Tar.extract (IO.FS.Stream.ofHandle h) sysTarExtract
  let sysTarHello ← IO.FS.readFile (sysTarExtract / "tar-fixture-dir" / "hello.txt")
  unless sysTarHello == "Hello from system tar\n" do
    throw (IO.userError s!"system-tar.tar: hello.txt content mismatch: {repr sysTarHello}")
  let _ ← IO.Process.run { cmd := "rm", args := #["-rf", sysTarExtract.toString] }

  -- gnu-longname.tar: GNU long name extension (typeflag 'L')
  let gnuLnData ← readFixture "tar/interop/gnu-longname.tar"
  let gnuLnPath ← writeFixtureTmp "gnu-longname.tar" gnuLnData
  let gnuLnEntries ← IO.FS.withFile gnuLnPath .read fun h =>
    Tar.list (IO.FS.Stream.ofHandle h)
  let gnuLnFile := gnuLnEntries.find? (·.path.contains "file_with_a_really_long_name")
  match gnuLnFile with
  | some e =>
    unless e.size == 18 do throw (IO.userError s!"gnu-longname.tar: file size {e.size}")
    unless e.path.length > 100 do throw (IO.userError "gnu-longname.tar: path should be >100 chars")
  | none => throw (IO.userError "gnu-longname.tar: long-named file not found in listing")
  let gnuLnExtract : System.FilePath := "/tmp/lean-zip-fixture-gnu-longname-extract"
  if ← gnuLnExtract.pathExists then
    let _ ← IO.Process.run { cmd := "rm", args := #["-rf", gnuLnExtract.toString] }
  IO.FS.createDirAll gnuLnExtract
  IO.FS.withFile gnuLnPath .read fun h =>
    Tar.extract (IO.FS.Stream.ofHandle h) gnuLnExtract
  let gnuLnContent ← IO.FS.readFile (gnuLnExtract / (gnuLnFile.get!).path)
  unless gnuLnContent == "Long name content\n" do
    throw (IO.userError s!"gnu-longname.tar: content mismatch: {repr gnuLnContent}")
  let _ ← IO.Process.run { cmd := "rm", args := #["-rf", gnuLnExtract.toString] }

  -- === TAR malformed fixtures ===

  let truncTarData ← readFixture "tar/malformed/truncated.tar"
  let truncTarPath ← writeFixtureTmp "truncated.tar" truncTarData
  let truncTarExtract : System.FilePath := "/tmp/lean-zip-fixture-truncated-tar-extract"
  IO.FS.createDirAll truncTarExtract
  assertThrows "TAR malformed (truncated.tar)"
    (IO.FS.withFile truncTarPath .read fun h =>
      Tar.extract (IO.FS.Stream.ofHandle h) truncTarExtract)
    "unexpected end of archive"

  let badChkData ← readFixture "tar/malformed/bad-checksum.tar"
  let badChkPath ← writeFixtureTmp "bad-checksum.tar" badChkData
  assertThrows "TAR malformed (bad-checksum.tar)"
    (IO.FS.withFile badChkPath .read fun h => do
      let _ ← Tar.list (IO.FS.Stream.ofHandle h)
      pure ())
    "checksum"

  let noMagicData ← readFixture "tar/malformed/no-magic.tar"
  let noMagicPath ← writeFixtureTmp "no-magic.tar" noMagicData
  assertThrows "TAR malformed (no-magic.tar)"
    (IO.FS.withFile noMagicPath .read fun h => do
      let _ ← Tar.list (IO.FS.Stream.ofHandle h)
      pure ())
    "unsupported format"

  -- === TAR security fixtures ===

  let tarSlipData ← readFixture "tar/security/tar-slip.tar"
  let tarSlipPath ← writeFixtureTmp "tar-slip.tar" tarSlipData
  let tarSlipExtract : System.FilePath := "/tmp/lean-zip-fixture-tar-slip-extract"
  IO.FS.createDirAll tarSlipExtract
  assertThrows "TAR security (tar-slip.tar)"
    (IO.FS.withFile tarSlipPath .read fun h =>
      Tar.extract (IO.FS.Stream.ofHandle h) tarSlipExtract)
    "unsafe path"

  let tarAbsData ← readFixture "tar/security/tar-absolute.tar"
  let tarAbsPath ← writeFixtureTmp "tar-absolute.tar" tarAbsData
  let tarAbsExtract : System.FilePath := "/tmp/lean-zip-fixture-tar-abs-extract"
  IO.FS.createDirAll tarAbsExtract
  assertThrows "TAR security (tar-absolute.tar)"
    (IO.FS.withFile tarAbsPath .read fun h =>
      Tar.extract (IO.FS.Stream.ofHandle h) tarAbsExtract)
    "unsafe path"

  let symlinkSlipData ← readFixture "tar/security/symlink-slip.tar"
  let symlinkSlipPath ← writeFixtureTmp "symlink-slip.tar" symlinkSlipData
  let symlinkSlipExtract : System.FilePath := "/tmp/lean-zip-fixture-symlink-slip-extract"
  IO.FS.createDirAll symlinkSlipExtract
  assertThrows "TAR security (symlink-slip.tar)"
    (IO.FS.withFile symlinkSlipPath .read fun h =>
      Tar.extract (IO.FS.Stream.ofHandle h) symlinkSlipExtract)
    "unsafe symlink"
  -- Clean up temp files
  for f in #["go-ustar.tar", "go-gnu.tar", "go-pax.tar", "system-tar.tar",
             "gnu-longname.tar", "truncated.tar", "bad-checksum.tar", "no-magic.tar",
             "tar-slip.tar", "tar-absolute.tar", "symlink-slip.tar"] do
    let _ ← IO.Process.run { cmd := "rm", args := #["-f", s!"/tmp/lean-zip-fixture-{f}"] }
  for d in #["/tmp/lean-zip-fixture-truncated-tar-extract", "/tmp/lean-zip-fixture-tar-slip-extract",
             "/tmp/lean-zip-fixture-tar-abs-extract", "/tmp/lean-zip-fixture-symlink-slip-extract"] do
    let _ ← IO.Process.run { cmd := "rm", args := #["-rf", d] }
  IO.println "TAR fixture tests: OK"
