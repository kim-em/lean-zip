import ZipTest.Helpers

/-! Tests for ZIP interop: stored/deflated methods, ZIP64, multi-entry archives,
    and malformed/security fixtures. -/

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

  -- oversized-compressed-size.zip: 122-byte archive whose entry's
  -- central-directory `compressedSize` claims 2 MiB of payload. The local
  -- header mirrors the same oversized claim. `Archive.extract` must reject
  -- this before any `Handle.read` is driven by the bogus size.
  -- Regenerate (if ever lost): see the Python recipe under
  -- `scripts/make-oversized-compressed-size.py` — or inline, build a valid
  -- 122-byte archive storing `hello\n` and overwrite the `compressedSize`
  -- fields at local offset 18 and CD offset (cd_offset + 20) with 0x00200000.
  let oversizedData ← readFixture "zip/malformed/oversized-compressed-size.zip"
  let oversizedPath ← writeFixtureTmp "oversized-compressed-size.zip" oversizedData
  let oversizedExtractDir : System.FilePath :=
    "/tmp/lean-zip-fixture-oversized-compressed-size-extract"
  IO.FS.createDirAll oversizedExtractDir
  assertThrows "ZIP malformed (oversized-compressed-size.zip)"
    (Archive.extract oversizedPath oversizedExtractDir)
    "local data span"

  -- oversized-zip64-compressed-size.zip: 134-byte ZIP64 archive whose
  -- central-directory entry sets the 32-bit `compressedSize` to
  -- 0xFFFFFFFF (ZIP64 marker) and places the actual exabyte-scale u64
  -- `compressedSize = 0x1000000000000000` (≈ 1.15 EiB) in the ZIP64
  -- extra field (header id 0x0001). `uncompressedSize` and `localOffset`
  -- fit in 32 bits so are absent from the ZIP64 extra — see
  -- `parseZip64Extra`'s conditional parse order. `Archive.extract` must
  -- reject this at the `local data span` check in `readEntryData`
  -- (after the fixed local-header and name+extra spans both pass).
  -- Regenerate (if ever lost) with:
  --   python3 -c 'import struct,zlib
  --   p=b"hello\n"; n=b"hello.txt"; c=zlib.crc32(p); big=1<<60
  --   lh=struct.pack("<IHHHHHIIIHH",0x04034b50,20,0,0,0,0,c,0xFFFFFFFF,len(p),len(n),0)
  --   ex=struct.pack("<HHQ",1,8,big)
  --   cd=struct.pack("<IHHHHHHIIIHHHHHII",0x02014b50,30,20,0,0,0,0,c,0xFFFFFFFF,
  --       len(p),len(n),len(ex),0,0,0,0,0)
  --   lhe=lh+n+p; cde=cd+n+ex
  --   eocd=struct.pack("<IHHHHIIH",0x06054b50,0,0,1,1,len(cde),len(lhe),0)
  --   open("oversized-zip64-compressed-size.zip","wb").write(lhe+cde+eocd)'
  let oversizedZ64Data ← readFixture "zip/malformed/oversized-zip64-compressed-size.zip"
  let oversizedZ64Path ← writeFixtureTmp "oversized-zip64-compressed-size.zip" oversizedZ64Data
  let oversizedZ64ExtractDir : System.FilePath :=
    "/tmp/lean-zip-fixture-oversized-zip64-compressed-size-extract"
  IO.FS.createDirAll oversizedZ64ExtractDir
  assertThrows "ZIP malformed (oversized-zip64-compressed-size.zip)"
    (Archive.extract oversizedZ64Path oversizedZ64ExtractDir)
    "local data span"

  -- oversized-zip64-uncompressed-size.zip: 134-byte ZIP64 archive whose
  -- central-directory entry sets the 32-bit `uncompressedSize` to
  -- 0xFFFFFFFF (ZIP64 marker) and places the actual exabyte-scale u64
  -- `uncompressedSize = 0x1000000000000000` (≈ 1.15 EiB) in the ZIP64
  -- extra field (header id 0x0001). `compressedSize` and `localOffset`
  -- fit in 32 bits so are absent from the ZIP64 extra — see
  -- `parseZip64Extra`'s conditional parse order. The local header sets
  -- `uncompressedSize = 0xFFFFFFFF` but, intentionally, omits the
  -- ZIP64 local extra block — so the strict LH ZIP64 parse in
  -- `readEntryData` rejects the archive at the `truncated ZIP64 local
  -- extra field` check before any `Handle.read` of the payload.
  -- Regenerate (if ever lost) with:
  --   python3 -c 'import struct,zlib
  --   p=b"hello\n"; n=b"hello.txt"; c=zlib.crc32(p); big=1<<60
  --   lh=struct.pack("<IHHHHHIIIHH",0x04034b50,20,0,0,0,0,c,len(p),0xFFFFFFFF,len(n),0)
  --   ex=struct.pack("<HHQ",1,8,big)
  --   cd=struct.pack("<IHHHHHHIIIHHHHHII",0x02014b50,30,20,0,0,0,0,c,len(p),
  --       0xFFFFFFFF,len(n),len(ex),0,0,0,0,0)
  --   lhe=lh+n+p; cde=cd+n+ex
  --   eocd=struct.pack("<IHHHHIIH",0x06054b50,0,0,1,1,len(cde),len(lhe),0)
  --   open("oversized-zip64-uncompressed-size.zip","wb").write(lhe+cde+eocd)'
  let oversizedZ64UData ← readFixture "zip/malformed/oversized-zip64-uncompressed-size.zip"
  let oversizedZ64UPath ← writeFixtureTmp "oversized-zip64-uncompressed-size.zip" oversizedZ64UData
  let oversizedZ64UExtractDir : System.FilePath :=
    "/tmp/lean-zip-fixture-oversized-zip64-uncompressed-size-extract"
  IO.FS.createDirAll oversizedZ64UExtractDir
  assertThrows "ZIP malformed (oversized-zip64-uncompressed-size.zip)"
    (Archive.extract oversizedZ64UPath oversizedZ64UExtractDir)
    "truncated ZIP64 local extra field"

  -- cd-lh-method-mismatch.zip: 122-byte stored ZIP whose CD advertises
  -- method=8 (deflate) while the local header advertises method=0
  -- (stored).  `Archive.extract` must reject this with a
  -- `method mismatch between CD and local header` error before the
  -- compressed payload is decompressed (the payload is raw `hello\n`,
  -- which would otherwise fail deflate decoding much later).
  -- Regenerate (if ever lost): see `make_lh` / `make_cd` in
  -- `scripts/build-cd-lh-mismatch.py` or this 2026 inline recipe:
  --   python3 -c 'import struct,zlib; p=b"hello\n"; n=b"hello.txt"
  --   c=zlib.crc32(p); CD_M,LH_M=8,0
  --   lh=struct.pack("<IHHHHHIIIHH",0x04034b50,20,0,LH_M,0,0,c,len(p),len(p),len(n),0)
  --   cd=struct.pack("<IHHHHHHIIIHHHHHII",0x02014b50,20,20,0,CD_M,0,0,c,len(p),len(p),
  --       len(n),0,0,0,0,0,0)
  --   lhe=lh+n+p; cde=cd+n
  --   eocd=struct.pack("<IHHHHIIH",0x06054b50,0,0,1,1,len(cde),len(lhe),0)
  --   open("cd-lh-method-mismatch.zip","wb").write(lhe+cde+eocd)'
  let cdLhMethodData ← readFixture "zip/malformed/cd-lh-method-mismatch.zip"
  let cdLhMethodPath ← writeFixtureTmp "cd-lh-method-mismatch.zip" cdLhMethodData
  let cdLhMethodExtractDir : System.FilePath :=
    "/tmp/lean-zip-fixture-cd-lh-method-mismatch-extract"
  IO.FS.createDirAll cdLhMethodExtractDir
  assertThrows "ZIP malformed (cd-lh-method-mismatch.zip)"
    (Archive.extract cdLhMethodPath cdLhMethodExtractDir)
    "method mismatch between CD and local header"

  -- cd-lh-size-mismatch.zip: 122-byte stored ZIP whose CD advertises
  -- compressedSize=6 while the local header advertises
  -- compressedSize=7.  Both headers report method=0 (stored) so the
  -- CD/LH consistency check is reached.  `Archive.extract` must reject
  -- this with a `compressedSize mismatch between CD and local header`
  -- error.
  -- Regenerate (if ever lost): see `make_lh` / `make_cd` in
  -- `scripts/build-cd-lh-mismatch.py` or this 2026 inline recipe:
  --   python3 -c 'import struct,zlib; p=b"hello\n"; n=b"hello.txt"
  --   c=zlib.crc32(p); CD_C,LH_C=len(p),len(p)+1
  --   lh=struct.pack("<IHHHHHIIIHH",0x04034b50,20,0,0,0,0,c,LH_C,len(p),len(n),0)
  --   cd=struct.pack("<IHHHHHHIIIHHHHHII",0x02014b50,20,20,0,0,0,0,c,CD_C,len(p),
  --       len(n),0,0,0,0,0,0)
  --   lhe=lh+n+p; cde=cd+n
  --   eocd=struct.pack("<IHHHHIIH",0x06054b50,0,0,1,1,len(cde),len(lhe),0)
  --   open("cd-lh-size-mismatch.zip","wb").write(lhe+cde+eocd)'
  let cdLhSizeData ← readFixture "zip/malformed/cd-lh-size-mismatch.zip"
  let cdLhSizePath ← writeFixtureTmp "cd-lh-size-mismatch.zip" cdLhSizeData
  let cdLhSizeExtractDir : System.FilePath :=
    "/tmp/lean-zip-fixture-cd-lh-size-mismatch-extract"
  IO.FS.createDirAll cdLhSizeExtractDir
  assertThrows "ZIP malformed (cd-lh-size-mismatch.zip)"
    (Archive.extract cdLhSizePath cdLhSizeExtractDir)
    "compressedSize mismatch between CD and local header"

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
             "bad-method.zip", "oversized-compressed-size.zip",
             "oversized-zip64-compressed-size.zip",
             "oversized-zip64-uncompressed-size.zip",
             "cd-lh-method-mismatch.zip", "cd-lh-size-mismatch.zip",
             "zip-slip.zip", "absolute-path.zip"] do
    let _ ← IO.Process.run { cmd := "rm", args := #["-f", s!"/tmp/lean-zip-fixture-{f}"] }
  for d in #["/tmp/lean-zip-fixture-bad-crc-extract", "/tmp/lean-zip-fixture-bad-method-extract",
             "/tmp/lean-zip-fixture-oversized-compressed-size-extract",
             "/tmp/lean-zip-fixture-oversized-zip64-compressed-size-extract",
             "/tmp/lean-zip-fixture-oversized-zip64-uncompressed-size-extract",
             "/tmp/lean-zip-fixture-cd-lh-method-mismatch-extract",
             "/tmp/lean-zip-fixture-cd-lh-size-mismatch-extract",
             "/tmp/lean-zip-fixture-zip-slip-extract", "/tmp/lean-zip-fixture-abs-path-extract"] do
    let _ ← IO.Process.run { cmd := "rm", args := #["-rf", d] }
  IO.println "ZIP fixture tests: OK"
