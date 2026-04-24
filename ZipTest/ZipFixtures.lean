import ZipTest.Helpers

/-! Tests for ZIP interop: stored/deflated methods, ZIP64, multi-entry archives,
    and malformed/security fixtures. -/

set_option maxRecDepth 2048

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
  -- Opt out of the per-entry cap (default 1 GiB) so the 1-EiB uncompressedSize
  -- does not trip "exceeds limit" before the LH ZIP64 parse — this fixture
  -- specifically exercises the `truncated ZIP64 local extra field` path.
  assertThrows "ZIP malformed (oversized-zip64-uncompressed-size.zip)"
    (Archive.extract oversizedZ64UPath oversizedZ64UExtractDir (maxEntrySize := 0))
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

  -- cd-lh-flags-mismatch.zip: 122-byte stored ZIP whose CD advertises
  -- flags=0x0800 (UTF-8 name flag bit 11 set) while the local header
  -- advertises flags=0x0000 (bit 11 clear).  Both headers share the
  -- same ASCII name `hello.txt` so the CD-vs-LH consistency check is
  -- reached; `Archive.extract` must reject this with a
  -- `flags mismatch between CD and local header` error before the
  -- stored payload is delivered.  This exercises a known ZIP-smuggling
  -- vector: a CD-only UTF-8 flag tricks downstream LH re-parsers into
  -- decoding the name under the Latin-1 fallback path.
  -- Regenerate (if ever lost) with:
  --   python3 -c 'import struct,zlib; p=b"hello\n"; n=b"hello.txt"
  --   c=zlib.crc32(p); CD_F,LH_F=0x0800,0x0000
  --   lh=struct.pack("<IHHHHHIIIHH",0x04034b50,20,LH_F,0,0,0,c,len(p),len(p),len(n),0)
  --   cd=struct.pack("<IHHHHHHIIIHHHHHII",0x02014b50,20,20,CD_F,0,0,0,c,len(p),len(p),
  --       len(n),0,0,0,0,0,0)
  --   lhe=lh+n+p; cde=cd+n
  --   eocd=struct.pack("<IHHHHIIH",0x06054b50,0,0,1,1,len(cde),len(lhe),0)
  --   open("cd-lh-flags-mismatch.zip","wb").write(lhe+cde+eocd)'
  let cdLhFlagsData ← readFixture "zip/malformed/cd-lh-flags-mismatch.zip"
  let cdLhFlagsPath ← writeFixtureTmp "cd-lh-flags-mismatch.zip" cdLhFlagsData
  let cdLhFlagsExtractDir : System.FilePath :=
    "/tmp/lean-zip-fixture-cd-lh-flags-mismatch-extract"
  IO.FS.createDirAll cdLhFlagsExtractDir
  assertThrows "ZIP malformed (cd-lh-flags-mismatch.zip)"
    (Archive.extract cdLhFlagsPath cdLhFlagsExtractDir)
    "flags mismatch between CD and local header"

  -- cd-lh-uncompsize-mismatch.zip: 122-byte stored ZIP whose CD advertises
  -- uncompressedSize=6 while the local header advertises
  -- uncompressedSize=7.  Both headers report method=0 (stored) and matching
  -- compressedSize=6, so the earlier method/compressedSize CD/LH guards do
  -- not fire first.  `Archive.extract` must reject this with an
  -- `uncompressedSize mismatch between CD and local header` error.
  -- Regenerate (if ever lost): see `make_lh` / `make_cd` in
  -- `scripts/build-cd-lh-mismatch.py` or this 2026 inline recipe:
  --   python3 -c 'import struct,zlib; p=b"hello\n"; n=b"hello.txt"
  --   c=zlib.crc32(p); CD_U,LH_U=len(p),len(p)+1
  --   lh=struct.pack("<IHHHHHIIIHH",0x04034b50,20,0,0,0,0,c,len(p),LH_U,len(n),0)
  --   cd=struct.pack("<IHHHHHHIIIHHHHHII",0x02014b50,20,20,0,0,0,0,c,len(p),CD_U,
  --       len(n),0,0,0,0,0,0)
  --   lhe=lh+n+p; cde=cd+n
  --   eocd=struct.pack("<IHHHHIIH",0x06054b50,0,0,1,1,len(cde),len(lhe),0)
  --   open("cd-lh-uncompsize-mismatch.zip","wb").write(lhe+cde+eocd)'
  let cdLhUncompData ← readFixture "zip/malformed/cd-lh-uncompsize-mismatch.zip"
  let cdLhUncompPath ← writeFixtureTmp "cd-lh-uncompsize-mismatch.zip" cdLhUncompData
  let cdLhUncompExtractDir : System.FilePath :=
    "/tmp/lean-zip-fixture-cd-lh-uncompsize-mismatch-extract"
  IO.FS.createDirAll cdLhUncompExtractDir
  assertThrows "ZIP malformed (cd-lh-uncompsize-mismatch.zip)"
    (Archive.extract cdLhUncompPath cdLhUncompExtractDir)
    "uncompressedSize mismatch between CD and local header"

  -- cd-lh-crc-mismatch.zip: 122-byte stored ZIP whose CD advertises the
  -- correct CRC32 of `hello\n` while the local header advertises
  -- `CRC ^ 0xFF`.  Both headers report method=0 (stored) and matching
  -- compressed/uncompressed sizes, so the earlier method/size CD/LH
  -- guards do not fire first.  `Archive.extract` must reject this with a
  -- `crc32 mismatch between CD and local header` error before the
  -- post-extract CRC32 verification (which would otherwise also fail).
  -- Regenerate (if ever lost): see `make_lh` / `make_cd` in
  -- `scripts/build-cd-lh-mismatch.py` or this 2026 inline recipe:
  --   python3 -c 'import struct,zlib; p=b"hello\n"; n=b"hello.txt"
  --   c=zlib.crc32(p); LH_C=c^0xFF
  --   lh=struct.pack("<IHHHHHIIIHH",0x04034b50,20,0,0,0,0,LH_C,len(p),len(p),len(n),0)
  --   cd=struct.pack("<IHHHHHHIIIHHHHHII",0x02014b50,20,20,0,0,0,0,c,len(p),len(p),
  --       len(n),0,0,0,0,0,0)
  --   lhe=lh+n+p; cde=cd+n
  --   eocd=struct.pack("<IHHHHIIH",0x06054b50,0,0,1,1,len(cde),len(lhe),0)
  --   open("cd-lh-crc-mismatch.zip","wb").write(lhe+cde+eocd)'
  let cdLhCrcData ← readFixture "zip/malformed/cd-lh-crc-mismatch.zip"
  let cdLhCrcPath ← writeFixtureTmp "cd-lh-crc-mismatch.zip" cdLhCrcData
  let cdLhCrcExtractDir : System.FilePath :=
    "/tmp/lean-zip-fixture-cd-lh-crc-mismatch-extract"
  IO.FS.createDirAll cdLhCrcExtractDir
  assertThrows "ZIP malformed (cd-lh-crc-mismatch.zip)"
    (Archive.extract cdLhCrcPath cdLhCrcExtractDir)
    "crc32 mismatch between CD and local header"

  -- cd-lh-version-mismatch.zip: 122-byte stored ZIP whose LH advertises
  -- `versionNeededToExtract=45` while the CD advertises `20`.  The CD/LH
  -- `versionNeededToExtract` check is deliberately **one-sided** — `LH > CD`
  -- is a capability-smuggle (LH claims "ZIP64 features required" while a
  -- reader that feature-gates on CD sees `20` and proceeds); the converse
  -- (`CD > LH`) is **legitimate** per Go's `archive/zip` and CPython's
  -- `zipfile` when LH sizes fit in 32 bits, as exercised by
  -- `testdata/zip/interop/go-zip64.zip` (LH=20, CD=45).
  -- `Archive.extract` must reject this fixture with an
  -- `LH versionNeededToExtract` error.
  -- Regenerate (if ever lost): see `make_lh` / `make_cd` in
  -- `scripts/build-cd-lh-mismatch.py` or this 2026 inline recipe:
  --   python3 -c 'import struct,zlib; p=b"hello\n"; n=b"hello.txt"
  --   c=zlib.crc32(p); CD_V,LH_V=20,45
  --   lh=struct.pack("<IHHHHHIIIHH",0x04034b50,LH_V,0,0,0,0,c,len(p),len(p),len(n),0)
  --   cd=struct.pack("<IHHHHHHIIIHHHHHII",0x02014b50,20,CD_V,0,0,0,0,c,len(p),len(p),
  --       len(n),0,0,0,0,0,0)
  --   lhe=lh+n+p; cde=cd+n
  --   eocd=struct.pack("<IHHHHIIH",0x06054b50,0,0,1,1,len(cde),len(lhe),0)
  --   open("cd-lh-version-mismatch.zip","wb").write(lhe+cde+eocd)'
  let cdLhVersionData ← readFixture "zip/malformed/cd-lh-version-mismatch.zip"
  let cdLhVersionPath ← writeFixtureTmp "cd-lh-version-mismatch.zip" cdLhVersionData
  let cdLhVersionExtractDir : System.FilePath :=
    "/tmp/lean-zip-fixture-cd-lh-version-mismatch-extract"
  IO.FS.createDirAll cdLhVersionExtractDir
  assertThrows "ZIP malformed (cd-lh-version-mismatch.zip)"
    (Archive.extract cdLhVersionPath cdLhVersionExtractDir)
    "LH versionNeededToExtract"

  -- eocd-numentries-mismatch.zip: 122-byte stored ZIP whose EOCD declares
  -- totalEntries=2 while only one CD entry is actually present.  This is a
  -- CD-vs-EOCD anomaly (orthogonal to the CD/LH consistency family above):
  -- the reader walks the CD until the trailing signature stops matching and
  -- would otherwise silently accept the single parsed entry.  `parseCentralDir`
  -- asserts `entries.size == declaredEntries` at its tail and must reject
  -- this with an `EOCD totalEntries mismatch` error before the caller sees
  -- the truncated entry list.
  -- Regenerate (if ever lost) with:
  --   python3 -c 'import struct,zlib; p=b"hello\n"; n=b"hello.txt"
  --   c=zlib.crc32(p)
  --   lh=struct.pack("<IHHHHHIIIHH",0x04034b50,20,0,0,0,0,c,len(p),len(p),len(n),0)
  --   cd=struct.pack("<IHHHHHHIIIHHHHHII",0x02014b50,20,20,0,0,0,0,c,len(p),len(p),
  --       len(n),0,0,0,0,0,0)
  --   lhe=lh+n+p; cde=cd+n
  --   eocd=struct.pack("<IHHHHIIH",0x06054b50,0,0,2,2,len(cde),len(lhe),0)
  --   open("eocd-numentries-mismatch.zip","wb").write(lhe+cde+eocd)'
  let eocdNumEntriesData ← readFixture "zip/malformed/eocd-numentries-mismatch.zip"
  let eocdNumEntriesPath ← writeFixtureTmp "eocd-numentries-mismatch.zip" eocdNumEntriesData
  let eocdNumEntriesExtractDir : System.FilePath :=
    "/tmp/lean-zip-fixture-eocd-numentries-mismatch-extract"
  IO.FS.createDirAll eocdNumEntriesExtractDir
  assertThrows "ZIP malformed (eocd-numentries-mismatch.zip)"
    (Archive.extract eocdNumEntriesPath eocdNumEntriesExtractDir)
    "EOCD totalEntries mismatch"

  -- eocd-disknum-mismatch.zip: 122-byte stored ZIP whose EOCD
  -- `diskWhereCDStarts` is 1 instead of 0.  lean-zip supports
  -- single-disk archives only; both disk-number fields are
  -- zero-checked (post-ZIP64-override) so cross-disk smuggling is
  -- rejected before the CD is walked.  Generated by
  -- `scripts/build-cd-lh-mismatch.py`.
  let eocdDisknumData ← readFixture "zip/malformed/eocd-disknum-mismatch.zip"
  let eocdDisknumPath ← writeFixtureTmp "eocd-disknum-mismatch.zip" eocdDisknumData
  let eocdDisknumExtractDir : System.FilePath :=
    "/tmp/lean-zip-fixture-eocd-disknum-mismatch-extract"
  IO.FS.createDirAll eocdDisknumExtractDir
  assertThrows "ZIP malformed (eocd-disknum-mismatch.zip)"
    (Archive.extract eocdDisknumPath eocdDisknumExtractDir)
    "EOCD disk-number mismatch"

  -- eocd-numentries-thisdisk-mismatch.zip: 122-byte stored ZIP whose EOCD
  -- declares `numEntriesThisDisk=2` while `totalEntries=1` and exactly one
  -- CD entry is present.  This is the sibling of
  -- `eocd-numentries-mismatch.zip`: that fixture targets the
  -- `totalEntries` vs. parsed-CD count, this one targets the
  -- EOCD-internal agreement between the two entry-count fields.
  -- `parseCentralDir` rejects with `EOCD numEntriesThisDisk mismatch`
  -- before the (passing) `totalEntries` check at the tail.  Generated
  -- by `scripts/build-cd-lh-mismatch.py`.
  let eocdNumEntriesThisDiskData ←
    readFixture "zip/malformed/eocd-numentries-thisdisk-mismatch.zip"
  let eocdNumEntriesThisDiskPath ←
    writeFixtureTmp "eocd-numentries-thisdisk-mismatch.zip" eocdNumEntriesThisDiskData
  let eocdNumEntriesThisDiskExtractDir : System.FilePath :=
    "/tmp/lean-zip-fixture-eocd-numentries-thisdisk-mismatch-extract"
  IO.FS.createDirAll eocdNumEntriesThisDiskExtractDir
  assertThrows "ZIP malformed (eocd-numentries-thisdisk-mismatch.zip)"
    (Archive.extract eocdNumEntriesThisDiskPath eocdNumEntriesThisDiskExtractDir)
    "EOCD numEntriesThisDisk mismatch"

  -- cd-entry-disknum-mismatch.zip: 122-byte stored ZIP whose sole CD
  -- entry carries `diskNumberStart=7` at CD offset +34.  Per APPNOTE
  -- §4.4.11 single-disk archives — the only shape lean-zip supports —
  -- must have this field at `0`.  `parseCentralDir` rejects with
  -- `CD entry diskNumberStart mismatch` early in the iteration loop,
  -- before any name decode or ZIP64 extra parsing.  Companion to
  -- `eocd-disknum-mismatch.zip` (archive-level disk-number); together
  -- they close the per-entry and EOCD-level disk-number smuggling
  -- vectors.  Generated by `scripts/build-cd-lh-mismatch.py`.
  let cdEntryDisknumData ←
    readFixture "zip/malformed/cd-entry-disknum-mismatch.zip"
  let cdEntryDisknumPath ←
    writeFixtureTmp "cd-entry-disknum-mismatch.zip" cdEntryDisknumData
  let cdEntryDisknumExtractDir : System.FilePath :=
    "/tmp/lean-zip-fixture-cd-entry-disknum-mismatch-extract"
  IO.FS.createDirAll cdEntryDisknumExtractDir
  assertThrows "ZIP malformed (cd-entry-disknum-mismatch.zip)"
    (Archive.extract cdEntryDisknumPath cdEntryDisknumExtractDir)
    "CD entry diskNumberStart mismatch"

  -- eocd-zip64-override-nosentinel.zip: 198-byte archive with a valid
  -- ZIP64 EOCD64 + Locator pair and a standard EOCD whose `cdOffset`
  -- field carries the real value 42 instead of the APPNOTE §4.3.16
  -- sentinel `0xFFFFFFFF`.  The ZIP64 record supplies cdOffset=45, so
  -- the reader's "sentinel or numeric match" check (relaxed to
  -- accommodate Go's `archive/zip` producer behaviour — see
  -- `testdata/zip/interop/go-zip64.zip`, which emits real zeros in
  -- the standard EOCD's disk-number fields when ZIP64 is used) fires
  -- on the cdOffset slot: the standard value is neither the sentinel
  -- nor numerically equal to the ZIP64 override.  Closes the
  -- ZIP64/standard-EOCD parser-differential smuggling vector.
  -- Generated by `scripts/build-zip64-malformed-fixtures.py`.
  let eocdZ64OverrideData ← readFixture "zip/malformed/eocd-zip64-override-nosentinel.zip"
  let eocdZ64OverridePath ← writeFixtureTmp "eocd-zip64-override-nosentinel.zip" eocdZ64OverrideData
  let eocdZ64OverrideExtractDir : System.FilePath :=
    "/tmp/lean-zip-fixture-eocd-zip64-override-nosentinel-extract"
  IO.FS.createDirAll eocdZ64OverrideExtractDir
  assertThrows "ZIP malformed (eocd-zip64-override-nosentinel.zip)"
    (Archive.extract eocdZ64OverridePath eocdZ64OverrideExtractDir)
    "EOCD ZIP64-override mismatch"

  -- zip64-eocd64-version-low.zip: 242-byte ZIP64 archive derived from
  -- `testdata/zip/interop/go-zip64.zip` by overwriting the two bytes at
  -- absolute offset 158 (EOCD64 `bufPos + 14`, the
  -- `versionNeededToExtract` field) from `\x2d\x00` (45) to `\x14\x00`
  -- (20).  APPNOTE §4.3.14.1 requires the EOCD64 `versionNeededToExtract`
  -- field to be `≥ 45` whenever a ZIP64 EOCD64 record is present;
  -- `findEndOfCentralDir`'s ZIP64 branch rejects the archive with a
  -- `ZIP64 EOCD64 versionNeededToExtract` error at
  -- `Archive.list`/`Archive.extract` time, before the ZIP64 overrides are
  -- read (so the smuggled values are not revealed by the error message).
  -- This closes the parser-differential smuggling vector where a
  -- capability-gated extractor feature-checks on the version field and
  -- decodes the archive as plain ZIP (mis-reading `cdOffset`/`cdSize`
  -- from the standard EOCD) while a permissive reader processes the
  -- ZIP64 overrides.
  let z64VersionLowData ← readFixture "zip/malformed/zip64-eocd64-version-low.zip"
  let z64VersionLowPath ← writeFixtureTmp "zip64-eocd64-version-low.zip" z64VersionLowData
  assertThrows "ZIP malformed (zip64-eocd64-version-low.zip)"
    (do let _ ← Archive.list z64VersionLowPath; pure ())
    "ZIP64 EOCD64 versionNeededToExtract"

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
             "cd-lh-flags-mismatch.zip",
             "cd-lh-uncompsize-mismatch.zip", "cd-lh-crc-mismatch.zip",
             "cd-lh-version-mismatch.zip",
             "eocd-numentries-mismatch.zip",
             "eocd-disknum-mismatch.zip",
             "eocd-numentries-thisdisk-mismatch.zip",
             "cd-entry-disknum-mismatch.zip",
             "eocd-zip64-override-nosentinel.zip",
             "zip64-eocd64-version-low.zip",
             "zip-slip.zip", "absolute-path.zip"] do
    let _ ← IO.Process.run { cmd := "rm", args := #["-f", s!"/tmp/lean-zip-fixture-{f}"] }
  for d in #["/tmp/lean-zip-fixture-bad-crc-extract", "/tmp/lean-zip-fixture-bad-method-extract",
             "/tmp/lean-zip-fixture-oversized-compressed-size-extract",
             "/tmp/lean-zip-fixture-oversized-zip64-compressed-size-extract",
             "/tmp/lean-zip-fixture-oversized-zip64-uncompressed-size-extract",
             "/tmp/lean-zip-fixture-cd-lh-method-mismatch-extract",
             "/tmp/lean-zip-fixture-cd-lh-size-mismatch-extract",
             "/tmp/lean-zip-fixture-cd-lh-flags-mismatch-extract",
             "/tmp/lean-zip-fixture-cd-lh-uncompsize-mismatch-extract",
             "/tmp/lean-zip-fixture-cd-lh-crc-mismatch-extract",
             "/tmp/lean-zip-fixture-cd-lh-version-mismatch-extract",
             "/tmp/lean-zip-fixture-eocd-numentries-mismatch-extract",
             "/tmp/lean-zip-fixture-eocd-disknum-mismatch-extract",
             "/tmp/lean-zip-fixture-eocd-numentries-thisdisk-mismatch-extract",
             "/tmp/lean-zip-fixture-cd-entry-disknum-mismatch-extract",
             "/tmp/lean-zip-fixture-eocd-zip64-override-nosentinel-extract",
             "/tmp/lean-zip-fixture-zip-slip-extract", "/tmp/lean-zip-fixture-abs-path-extract"] do
    let _ ← IO.Process.run { cmd := "rm", args := #["-rf", d] }
  IO.println "ZIP fixture tests: OK"
