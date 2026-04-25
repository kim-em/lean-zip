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
  -- This fixture has CD/LH method=14 (LZMA), outside lean-zip's `{0, 8}`
  -- allowlist. `parseCentralDir` now rejects at CD parse time (PR #1791)
  -- with `"unsupported compression method"`, earlier than the late
  -- `"unsupported method"` dispatch in `readEntryData` that historically
  -- caught the fault. The late guard remains in place as
  -- defense-in-depth (unreachable for CD-parseable archives via the
  -- public API). Companion to `cd-bad-method-early.zip` (CD/LH method=6,
  -- imploded), which trips the same CD-parse guard with a distinct
  -- value for paired-review attribution.
  assertThrows "ZIP malformed (bad-method.zip)"
    (Archive.extract badMethodPath badMethodExtractDir)
    "unsupported compression method"

  -- cd-bad-method-early.zip: 122-byte archive with CD/LH method=6
  -- (imploded — deprecated in PKZIP 2.0, 1993). Rejected at CD parse
  -- time by `parseCentralDir`'s allowlist guard with
  -- `"unsupported compression method"`. Companion to `bad-method.zip`
  -- (CD/LH method=14, LZMA): both fixtures trip the same guard, but
  -- distinct method values let the paired-review distinguish which
  -- fixture fired. Built deterministically by
  -- `scripts/build-cd-lh-mismatch.py`.
  let cdBadMethodEarlyData ← readFixture "zip/malformed/cd-bad-method-early.zip"
  let cdBadMethodEarlyPath ← writeFixtureTmp "cd-bad-method-early.zip" cdBadMethodEarlyData
  let cdBadMethodEarlyExtractDir : System.FilePath :=
    "/tmp/lean-zip-fixture-cd-bad-method-early-extract"
  IO.FS.createDirAll cdBadMethodEarlyExtractDir
  assertThrows "ZIP malformed (cd-bad-method-early.zip)"
    (Archive.extract cdBadMethodEarlyPath cdBadMethodEarlyExtractDir)
    "unsupported compression method"

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
  -- This fixture has method=0 with CD compSize=2 MiB and uncompSize=6 —
  -- a stored-method size-invariant violation that `parseCentralDir` now
  -- rejects at CD parse time (PR #1773), earlier than the `local data
  -- span` check in `readEntryData` that historically caught the fault.
  -- Kept in-corpus for regression coverage at the earlier layer.
  assertThrows "ZIP malformed (oversized-compressed-size.zip)"
    (Archive.extract oversizedPath oversizedExtractDir)
    "stored-method size mismatch"

  -- cd-version-needed-too-high.zip: 122-byte stored ZIP whose CD and LH
  -- both advertise `versionNeededToExtract=51` (AES per APPNOTE §4.4.3.2).
  -- lean-zip handles only `20` (stored/deflate) and `45` (ZIP64); any
  -- higher value indicates an unsupported feature (Deflate64, BZIP2,
  -- AES, LZMA/PPMd/XZ). `parseCentralDir` rejects at CD parse time with
  -- `"unsupported versionNeededToExtract"` — distinct from the one-sided
  -- CD/LH downgrade check (`"LH versionNeededToExtract exceeds CD"`,
  -- PR #1736), which only catches LH > CD and lets CD=LH=51 through.
  -- Generated by `scripts/build-cd-lh-mismatch.py`.
  let cdVersionHighData ←
    readFixture "zip/malformed/cd-version-needed-too-high.zip"
  let cdVersionHighPath ←
    writeFixtureTmp "cd-version-needed-too-high.zip" cdVersionHighData
  let cdVersionHighExtractDir : System.FilePath :=
    "/tmp/lean-zip-fixture-cd-version-needed-too-high-extract"
  IO.FS.createDirAll cdVersionHighExtractDir
  assertThrows "ZIP malformed (cd-version-needed-too-high.zip)"
    (Archive.extract cdVersionHighPath cdVersionHighExtractDir)
    "unsupported versionNeededToExtract"

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
  -- This fixture has method=0 with ZIP64-resolved compSize=1<<60 and
  -- uncompSize=6 — a stored-method size-invariant violation that
  -- `parseCentralDir` now rejects at CD parse time (PR #1773, post-
  -- ZIP64-resolution), earlier than the `local data span` check in
  -- `readEntryData` that historically caught the fault.  Kept in-corpus
  -- for regression coverage at the earlier layer.
  assertThrows "ZIP malformed (oversized-zip64-compressed-size.zip)"
    (Archive.extract oversizedZ64Path oversizedZ64ExtractDir)
    "stored-method size mismatch"

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
  -- does not trip "exceeds limit" before the CD-parse stored-method check.
  -- This fixture has method=0 with compSize=6 and ZIP64-resolved
  -- uncompSize=1<<60 — a stored-method size-invariant violation that
  -- `parseCentralDir` now rejects at CD parse time (PR #1773, post-
  -- ZIP64-resolution), earlier than the `truncated ZIP64 local extra
  -- field` check in `readEntryData` that historically caught the fault.
  -- Kept in-corpus for regression coverage at the earlier layer.
  assertThrows "ZIP malformed (oversized-zip64-uncompressed-size.zip)"
    (Archive.extract oversizedZ64UPath oversizedZ64UExtractDir (maxEntrySize := 0))
    "stored-method size mismatch"

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

  -- cd-lh-modtime-mismatch.zip: 122-byte stored ZIP whose LH advertises
  -- `lastModTime=0x1234` while the CD advertises `0` (writer-side
  -- default).  The CD/LH `lastModTime`/`lastModDate` check is ungated
  -- (unlike crc/compSize/uncompSize — APPNOTE §4.4.6 restricts bit 3 of
  -- the flags to those three fields only, so the timestamp pair is
  -- always carried in the LH and legitimate data-descriptor archives
  -- still agree on the two UInt16 slots).  `Archive.extract` must
  -- reject this fixture with a `lastModTime/Date mismatch` error.
  -- Generated by `scripts/build-cd-lh-mismatch.py`.
  let cdLhModtimeData ← readFixture "zip/malformed/cd-lh-modtime-mismatch.zip"
  let cdLhModtimePath ← writeFixtureTmp "cd-lh-modtime-mismatch.zip" cdLhModtimeData
  let cdLhModtimeExtractDir : System.FilePath :=
    "/tmp/lean-zip-fixture-cd-lh-modtime-mismatch-extract"
  IO.FS.createDirAll cdLhModtimeExtractDir
  assertThrows "ZIP malformed (cd-lh-modtime-mismatch.zip)"
    (Archive.extract cdLhModtimePath cdLhModtimeExtractDir)
    "lastModTime/Date mismatch"

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

  -- cd-entry-internal-attrs-reserved.zip: 122-byte stored ZIP whose sole
  -- CD entry carries `internalFileAttributes=0x0080` at CD offset +36
  -- (bit 7 set, reserved per APPNOTE §4.4.10 — only bit 0
  -- "apparent ASCII/text data" is defined).  lean-zip's writer emits
  -- zero here (writer-zero invariant), and Info-ZIP/Go/Python interop
  -- archives use only `0x0000` or `0x0001`, so `internalAttrs & 0xFFFE
  -- == 0` is a safe reject while preserving bit-0 text-flag interop.
  -- `parseCentralDir` rejects with `"internalAttrs reserved bits set"`
  -- early in the iteration loop (after `diskNumberStart`, before
  -- `entryEnd`).  Companion to `cd-entry-disknum-mismatch.zip` (CD +34
  -- writer-zero field): both fixtures close writer-invariant single
  -- `UInt16` fields at contiguous CD offsets.  Generated by
  -- `scripts/build-cd-lh-mismatch.py`.
  let cdEntryIAData ←
    readFixture "zip/malformed/cd-entry-internal-attrs-reserved.zip"
  let cdEntryIAPath ←
    writeFixtureTmp "cd-entry-internal-attrs-reserved.zip" cdEntryIAData
  let cdEntryIAExtractDir : System.FilePath :=
    "/tmp/lean-zip-fixture-cd-entry-internal-attrs-reserved-extract"
  IO.FS.createDirAll cdEntryIAExtractDir
  assertThrows "ZIP malformed (cd-entry-internal-attrs-reserved.zip)"
    (Archive.extract cdEntryIAPath cdEntryIAExtractDir)
    "internalAttrs reserved bits set"

  -- cd-nul-in-name.zip: 118-byte stored ZIP whose sole CD and LH entries
  -- carry the raw name bytes `b"a\x00b.txt"` (7 bytes, NUL at index 1).
  -- APPNOTE §4.4.17 is silent on permissible byte values in the filename
  -- field, but a NUL byte in the name is a classic parser-differential /
  -- filesystem-truncation smuggling vector: POSIX `open`/`stat` and many
  -- runtime layers treat `evil.txt\x00.zip` as `evil.txt`, while
  -- `Archive.list` callers and strict peer readers see the full
  -- NUL-embedded string.  `parseCentralDir` now rejects at CD parse time
  -- with `"CD entry name contains NUL byte"` — guarding on the raw
  -- `ByteArray` before UTF-8 decode so the error message never
  -- re-introduces NUL into logs and so both the UTF-8 and Latin-1
  -- decode branches are closed uniformly.  Closes both `Archive.list`
  -- (which previously returned the full NUL-containing path verbatim)
  -- and `Archive.extract` (whose POSIX `open` layer would have
  -- truncated at NUL and deposited the extracted file at the short-form
  -- prefix) simultaneously.  Generated by
  -- `scripts/build-cd-lh-mismatch.py`.
  let cdNulInNameData ←
    readFixture "zip/malformed/cd-nul-in-name.zip"
  let cdNulInNamePath ←
    writeFixtureTmp "cd-nul-in-name.zip" cdNulInNameData
  let cdNulInNameExtractDir : System.FilePath :=
    "/tmp/lean-zip-fixture-cd-nul-in-name-extract"
  IO.FS.createDirAll cdNulInNameExtractDir
  assertThrows "ZIP malformed (cd-nul-in-name.zip)"
    (Archive.extract cdNulInNamePath cdNulInNameExtractDir)
    "name contains NUL byte"

  -- cd-empty-name.zip: 104-byte stored ZIP whose sole CD and LH
  -- entries carry `name_bytes=b""` (length 0), so the `name length`
  -- UInt16 at CD +28 (and LH +26) reads as `0`.  APPNOTE §4.4.10
  -- defines the filename-length field; every legitimate ZIP entry —
  -- file or directory — has at least one byte of name, so
  -- `nameLen == 0` is structurally pathological and a parser-
  -- differential smuggling vector (lenient readers emit
  -- `entry.path = ""` — an `Entry` with no useful identity; strict
  -- readers reject).  `parseCentralDir` now rejects at CD parse time
  -- with `"CD entry has empty filename"` immediately after the
  -- `nameLen` read, before the `entryEnd > cdEnd` overrun check and
  -- before the sibling path-safety / NUL-byte filename guards so the
  -- failure attribution pins to the structural anomaly rather than
  -- the path-safety predicate (which would otherwise catch the empty
  -- string via its empty-component rejection, but only if the decode
  -- succeeds).  Closes both `Archive.list` (pre-PR returned the
  -- `Entry` with `path = ""`) and `Archive.extract` (pre-PR resolved
  -- `outDir / ""` to either `outDir` or a path with a trailing
  -- separator, surfacing as an unrelated `writeBinFile` / `createDir`
  -- error) dimensions simultaneously.  Sibling of `cd-nul-in-name.zip`
  -- (PR #1831, byte-content dimension) and `cd-path-unsafe.zip`
  -- (PR #1840, path-shape dimension): together they close the
  -- smuggled-name attack class (zero-length, NUL-embedded, and
  -- path-traversal forms all rejected at CD parse).  Generated by
  -- `scripts/build-cd-lh-mismatch.py`.
  let cdEmptyNameData ←
    readFixture "zip/malformed/cd-empty-name.zip"
  let cdEmptyNamePath ←
    writeFixtureTmp "cd-empty-name.zip" cdEmptyNameData
  let cdEmptyNameExtractDir : System.FilePath :=
    "/tmp/lean-zip-fixture-cd-empty-name-extract"
  IO.FS.createDirAll cdEmptyNameExtractDir
  assertThrows "ZIP malformed (cd-empty-name.zip)"
    (Archive.extract cdEmptyNamePath cdEmptyNameExtractDir)
    "CD entry has empty filename"

  -- cd-empty-entry-crc-nonzero.zip: 116-byte stored ZIP whose sole CD and LH
  -- entries advertise a zero-byte stored entry (`method=0, compSize=0,
  -- uncompSize=0`) but carry a crafted nonzero CRC (`0xDEADBEEF`).
  -- APPNOTE §4.4.7 defines the CRC32 field as the ANSI-CRC-32 of the
  -- uncompressed payload; the empty byte string has CRC32 `0x00000000`
  -- by the start-state `0xFFFFFFFF` + final-complement identity, so
  -- `uncompSize == 0 → crc == 0` is a universal mathematical invariant
  -- that every correct writer (Info-ZIP, Go `archive/zip`, CPython
  -- `zipfile`, 7-Zip, lean-zip's own `create`) obeys.  `parseCentralDir`
  -- now rejects at CD parse time with
  -- `"CD entry CRC must be zero when uncompressedSize is zero"`,
  -- placed after the stored-method size invariant — so the resolved
  -- `uncompSize : UInt64` is checked (post-ZIP64) rather than the
  -- `0xFFFFFFFF` sentinel, and attribution pins on the empty-file
  -- premise rather than a generic CRC check.  LH and CD carry the same
  -- crafted CRC so the CD/LH `crc32` consistency check
  -- (`cd-lh-crc-mismatch.zip`, PR #1728) does not fire first.
  -- Closes both `Archive.list` (pre-PR propagated the crafted CRC into
  -- `Entry.crc32` verbatim — callers routing on `entry.crc32` saw the
  -- smuggled value) and `Archive.extract` (pre-PR caught the mismatch
  -- only post-extraction via the `"CRC32 mismatch"` guard at
  -- Zip/Archive.lean:1088, after any I/O work had been performed)
  -- dimensions simultaneously.  Sibling of PR #1773 (stored-method
  -- size invariant) at the CD-parse mathematical-invariant family:
  -- #1773 closes the `compSize == uncompSize` column; this fixture
  -- closes the `uncompSize == 0 → crc == 0` column.  Generated by
  -- `scripts/build-cd-lh-mismatch.py`.
  let cdEmptyEntryCrcNonzeroData ←
    readFixture "zip/malformed/cd-empty-entry-crc-nonzero.zip"
  let cdEmptyEntryCrcNonzeroPath ←
    writeFixtureTmp "cd-empty-entry-crc-nonzero.zip" cdEmptyEntryCrcNonzeroData
  let cdEmptyEntryCrcNonzeroExtractDir : System.FilePath :=
    "/tmp/lean-zip-fixture-cd-empty-entry-crc-nonzero-extract"
  IO.FS.createDirAll cdEmptyEntryCrcNonzeroExtractDir
  assertThrows "ZIP malformed (cd-empty-entry-crc-nonzero.zip)"
    (Archive.extract cdEmptyEntryCrcNonzeroPath cdEmptyEntryCrcNonzeroExtractDir)
    "CD entry CRC must be zero when uncompressedSize is zero"

  -- cd-deflate-zero-compsize.zip: 116-byte ZIP whose sole CD and LH
  -- entries advertise `method=8` (deflate) with `compressedSize=0` and
  -- `uncompressedSize=42`.  APPNOTE §4.4.8 / §4.4.9 define the size
  -- fields; every ZIP compression method produces at least one
  -- compressed byte from non-empty input (method 0 has `compSize ==
  -- uncompSize`; method 8 has a 2-byte minimum block-header encoding
  -- per RFC 1951 — the `03 00` empty-stored-block marker).  So
  -- `compSize == 0 ∧ uncompSize > 0` is structurally impossible
  -- regardless of method — a universal mathematical invariant every
  -- correct writer obeys.  `parseCentralDir` now rejects at CD parse
  -- time with `"zero compressedSize"` before `entries.push`,
  -- post-ZIP64-resolution.  Closes the method=8 residual of the
  -- per-entry math-invariant family at CD parse: sibling #1773
  -- (`cd-stored-size-mismatch.zip`) catches this shape only when
  -- `method == 0` (via the equality mismatch), and sibling #1857
  -- (`cd-empty-entry-crc-nonzero.zip`) covers `uncompSize == 0`
  -- entries.  Pre-PR, `Archive.list` propagated the smuggled values
  -- verbatim — callers routing on `entry.compressedSize == 0` as a
  -- short-circuit saw them — and `Archive.extract` failed later inside
  -- the inflate backend with an undescriptive decompression error
  -- whose attribution did not pin the structural anomaly.  CRC is `0`
  -- so sibling #1857 does not interact (its guard only fires on
  -- `uncompSize == 0`); LH and CD fields match byte-for-byte so no
  -- CD/LH skew guard fires first.  Generated by
  -- `scripts/build-cd-lh-mismatch.py`.
  let cdDeflateZeroCompData ←
    readFixture "zip/malformed/cd-deflate-zero-compsize.zip"
  let cdDeflateZeroCompPath ←
    writeFixtureTmp "cd-deflate-zero-compsize.zip" cdDeflateZeroCompData
  let cdDeflateZeroCompExtractDir : System.FilePath :=
    "/tmp/lean-zip-fixture-cd-deflate-zero-compsize-extract"
  IO.FS.createDirAll cdDeflateZeroCompExtractDir
  assertThrows "ZIP malformed (cd-deflate-zero-compsize.zip)"
    (Archive.extract cdDeflateZeroCompPath cdDeflateZeroCompExtractDir)
    "zero compressedSize"

  -- cd-path-unsafe.zip: 126-byte stored ZIP whose CD and LH entries
  -- both carry the raw name bytes `b"../evil.txt"` (11 bytes — a
  -- classic `..`-traversal archive-slip smuggle).  APPNOTE §4.4.17
  -- does not constrain path shape, but `Binary.isPathSafe` (the
  -- canonical lean-zip-common path-safety filter, shared with the Tar
  -- extractor) rejects absolute paths, `\`, `..`/`.` components,
  -- empty components, and Windows drive letters.  `parseCentralDir`
  -- now rejects at CD parse time with `"CD entry has unsafe path"`
  -- — closing the path-traversal / archive-slip smuggling dimension
  -- on the `Archive.list` path, which pre-PR returned the `Entry`
  -- with the unsafe `path = "../evil.txt"` verbatim (exposing the
  -- full smuggled form to callers that route on `entry.path` before
  -- any filesystem I/O).  The extract-time `Binary.isPathSafe` calls
  -- at Zip/Archive.lean:1070 / :1074 remain in place as defense-in-
  -- depth but are now unreachable for CD-parseable archives via the
  -- public API.  LH and CD name bytes match byte-for-byte, keeping
  -- the CD/LH name-bytes consistency invariant (issue #1722) intact.
  -- Sibling of `cd-nul-in-name.zip` (PR #1831): together they close
  -- the "smuggled name" attack class — NUL-byte content (PR #1831)
  -- and path-shape (PR #1840).  Generated by
  -- `scripts/build-cd-lh-mismatch.py`.
  let cdPathUnsafeData ←
    readFixture "zip/malformed/cd-path-unsafe.zip"
  let cdPathUnsafePath ←
    writeFixtureTmp "cd-path-unsafe.zip" cdPathUnsafeData
  let cdPathUnsafeExtractDir : System.FilePath :=
    "/tmp/lean-zip-fixture-cd-path-unsafe-extract"
  IO.FS.createDirAll cdPathUnsafeExtractDir
  assertThrows "ZIP malformed (cd-path-unsafe.zip)"
    (Archive.extract cdPathUnsafePath cdPathUnsafeExtractDir)
    "CD entry has unsafe path"

  -- cd-patched-data-flag.zip: 122-byte stored ZIP whose CD and LH both
  -- advertise `flags = 0x0020` (APPNOTE §4.4.4 bit 5 — compressed
  -- patched data).  lean-zip has zero support for PKWARE's proprietary
  -- binary-delta format (§4.6); the writer emits `flags = 0x0800`
  -- (bit 11 UTF-8 names) only.  `parseCentralDir` rejects at CD parse
  -- time with `"patched-data flag bit 5 set"` before any payload
  -- decode — closing a parser-differential smuggling vector where a
  -- crafted archive would otherwise be silently extracted as if the
  -- payload were plain Deflate/stored data.  CD and LH flags agree
  -- (`lh_flags = cd_flags = 0x0020`) so the CD-vs-LH bit-3-masked
  -- flags check (PR #1715) does not fire first.  Generated by
  -- `scripts/build-cd-lh-mismatch.py`.
  let cdPatchedDataData ←
    readFixture "zip/malformed/cd-patched-data-flag.zip"
  let cdPatchedDataPath ←
    writeFixtureTmp "cd-patched-data-flag.zip" cdPatchedDataData
  let cdPatchedDataExtractDir : System.FilePath :=
    "/tmp/lean-zip-fixture-cd-patched-data-flag-extract"
  IO.FS.createDirAll cdPatchedDataExtractDir
  assertThrows "ZIP malformed (cd-patched-data-flag.zip)"
    (Archive.extract cdPatchedDataPath cdPatchedDataExtractDir)
    "patched-data flag bit 5 set"

  -- cd-stored-size-mismatch.zip: 122-byte stored ZIP whose CD and LH
  -- both advertise `method=0` (stored), `compressedSize=6`, and
  -- `uncompressedSize=7`.  Both sides agree (no CD/LH divergence — the
  -- CD/LH `uncompressedSize` consistency check does not fire), but
  -- APPNOTE §4.4.5 defines method 0 as *no compression*, so
  -- `compSize == uncompSize` is tautological.  `parseCentralDir`
  -- rejects this at CD parse time (post-ZIP64-resolution), before any
  -- LH read, with a `stored-method size mismatch` error.  Companion to
  -- `cd-lh-uncompsize-mismatch.zip` (CD-vs-LH skew); together they
  -- close the stored-method size-invariant dimension from both angles.
  -- Generated by `scripts/build-cd-lh-mismatch.py`.
  let cdStoredSizeData ←
    readFixture "zip/malformed/cd-stored-size-mismatch.zip"
  let cdStoredSizePath ←
    writeFixtureTmp "cd-stored-size-mismatch.zip" cdStoredSizeData
  let cdStoredSizeExtractDir : System.FilePath :=
    "/tmp/lean-zip-fixture-cd-stored-size-mismatch-extract"
  IO.FS.createDirAll cdStoredSizeExtractDir
  assertThrows "ZIP malformed (cd-stored-size-mismatch.zip)"
    (Archive.extract cdStoredSizePath cdStoredSizeExtractDir)
    "stored-method size mismatch"

  -- cd-entry-localoffset-past-cdstart.zip: 122-byte stored ZIP with an
  -- LH at file offset 0 (length 45 = 30 + 9-byte name + 6-byte payload)
  -- and CD starting at offset 45.  The CD entry's `localOffset` field
  -- (CD +42, UInt32) is crafted to 50 — past `cdOffset - 30 = 15`, so
  -- the per-entry archive-layout guard `localOff + 30 <= cdOffset`
  -- (50+30=80 > 45) fires at CD parse time.  The late `assertSpanInFile`
  -- check in `readEntryData` would accept this (80 <= fileSize=122), so
  -- the new CD-parse guard is the only gate that catches this
  -- construction on the `Archive.list` path and is what attributes the
  -- fault to CD parse on the extract path.  Companion to the
  -- archive-level sibling `cd-extends-past-eocd.zip` (cdOffset + cdSize
  -- past EOCD): together they close the archive-layout invariant
  -- surface — macro (CD fits before EOCD) and micro (LH fits before
  -- CD).  Generated by `scripts/build-cd-lh-mismatch.py`.
  let cdLocalOffsetPastData ←
    readFixture "zip/malformed/cd-entry-localoffset-past-cdstart.zip"
  let cdLocalOffsetPastPath ←
    writeFixtureTmp "cd-entry-localoffset-past-cdstart.zip" cdLocalOffsetPastData
  let cdLocalOffsetPastExtractDir : System.FilePath :=
    "/tmp/lean-zip-fixture-cd-entry-localoffset-past-cdstart-extract"
  IO.FS.createDirAll cdLocalOffsetPastExtractDir
  assertThrows "ZIP malformed (cd-entry-localoffset-past-cdstart.zip)"
    (Archive.extract cdLocalOffsetPastPath cdLocalOffsetPastExtractDir)
    "entry local offset overlaps central directory"

  -- cd-bad-lh-signature.zip: 122-byte stock single-entry stored
  -- `hello.txt` archive (LH at file offset 0, CD at offset 45, EOCD at
  -- offset 100) where the LH's first 4 bytes are overwritten with
  -- `0xCAFEBABE` instead of the APPNOTE §4.3.7 `sigLocal = 0x04034b50`.
  -- All CD-parse guards pass (CD itself is byte-identical to the stock
  -- baseline; `localOffset = 0`, `localOffset + 30 ≤ cdOffset = 45`,
  -- `entryEnd = 45 ≤ cdEnd = 100`, method ∈ {0, 8}, stored-method
  -- `compSize == uncompSize`, etc.) and `assertSpanInFile` /
  -- `readBoundedSpanFromHandle` clear the LH span (30 B at offset 0 ≤
  -- fileSize 122).  The 4-byte mismatch trips the late LH-signature
  -- guard at [Zip/Archive.lean:1081](/home/kim/lean-zip/Zip/Archive.lean:1081)
  -- — *"bad local header signature for {label}"* — which is
  -- `Archive.extract`'s defense-in-depth catch for archives that slip
  -- past every CD-parse and span guard.  `Archive.list` never reads the
  -- LH and lists the fixture cleanly; only `Archive.extract` throws,
  -- pinning the precedence story.  Sibling of
  -- `cd-entry-localoffset-past-cdstart.zip` (PR #1813, fires the
  -- per-entry `localOffset + 30 ≤ cdOffset` CD-parse guard before the
  -- LH read) and `cd-entry-past-cdend.zip` (in-flight issue #1885,
  -- fires the `entryEnd > cdEnd` CD-parse guard before the LH read):
  -- together the trio pins all three precedence levels of the
  -- local-offset → local-header validation chain at CD-parse +
  -- late-extract.  Generated by `scripts/build-cd-lh-mismatch.py`.
  let cdBadLHSigData ← readFixture "zip/malformed/cd-bad-lh-signature.zip"
  let cdBadLHSigPath ← writeFixtureTmp "cd-bad-lh-signature.zip" cdBadLHSigData
  let cdBadLHSigExtractDir : System.FilePath :=
    "/tmp/lean-zip-fixture-cd-bad-lh-signature-extract"
  IO.FS.createDirAll cdBadLHSigExtractDir
  assertThrows "ZIP malformed (cd-bad-lh-signature.zip)"
    (Archive.extract cdBadLHSigPath cdBadLHSigExtractDir)
    "bad local header signature"

  -- cd-entry-past-cdend.zip: 122-byte stock single-entry stored
  -- `hello.txt` archive (LH at file offset 0, CD at offset 45, EOCD at
  -- offset 100) where the sole CD entry's `commentLen` field at CD +32
  -- (UInt16) is set to `16` while the physical CD bytes carry no
  -- comment payload — the EOCD's `cdSize` is the natural
  -- `len(cde) = 46 + 9 = 55` (header + name only).  At CD parse time
  -- `entryEnd = pos + 46 + nameLen + extraLen + commentLen
  --           = 45 + 46 + 9 + 0 + 16 = 116` — strictly past
  -- `cdEnd = cdOffset + cdSize = 45 + 55 = 100`, so the per-entry
  -- footprint guard at
  -- [Zip/Archive.lean:615](/home/kim/lean-zip/Zip/Archive.lean:615)
  -- — `"central directory entry extends past end of central directory"`
  -- — fires.  All earlier CD-parse guards pass: the loop entry
  -- condition `pos + 46 ≤ cdEnd` (91 ≤ 100) holds, the CD signature
  -- matches, `nameLen = 9 > 0`, `diskNumberStart = 0`,
  -- `internalAttrs = 0`; the :615 guard is the first to fire.  This
  -- fixture is regression coverage for an existing guard — no new
  -- code in `parseCentralDir` lands with it.  Companion to the
  -- in-flight `cd-trailing-garbage.zip` (issue #1775, trailing bytes
  -- AFTER the last entry inside `[lastEntryEnd, cdEnd)`) and
  -- `cd-extends-past-eocd.zip` (issue #1799, archive-level
  -- `cdOffset + cdSize ≤ eocdPos`): the trio closes the three
  -- CD-region overrun shapes — per-entry footprint past `cdEnd`,
  -- trailing garbage inside the declared region, and macro `cdSize`
  -- past EOCD.  Pre-:615 (counterfactual), `Archive.list` would have
  -- decoded the `nameBytes` slice at `[pos + 46, pos + 46 + nameLen)`
  -- — which still fits inside the CD buffer for this construction —
  -- but with crafted `nameLen` / `extraLen` combinations a lenient
  -- parser could overread into the EOCD bytes.  Sibling of
  -- `cd-bad-lh-signature.zip` (PR #1903, late LH-signature guard) and
  -- `cd-entry-localoffset-past-cdstart.zip` (PR #1813, per-entry
  -- `localOffset + 30 ≤ cdOffset`): together the trio pins all three
  -- precedence levels of the local-offset → local-header validation
  -- chain at CD parse + late extract.  Generated by
  -- `scripts/build-cd-lh-mismatch.py`.
  let cdEntryPastCdEndData ← readFixture "zip/malformed/cd-entry-past-cdend.zip"
  let cdEntryPastCdEndPath ← writeFixtureTmp "cd-entry-past-cdend.zip" cdEntryPastCdEndData
  let cdEntryPastCdEndExtractDir : System.FilePath :=
    "/tmp/lean-zip-fixture-cd-entry-past-cdend-extract"
  IO.FS.createDirAll cdEntryPastCdEndExtractDir
  assertThrows "ZIP malformed (cd-entry-past-cdend.zip)"
    (Archive.extract cdEntryPastCdEndPath cdEntryPastCdEndExtractDir)
    "central directory entry extends past end of central directory"

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

  -- eocd-zip64-override-cdsize-mismatch.zip: 198-byte archive with a
  -- valid ZIP64 EOCD64 + Locator pair and a standard EOCD whose
  -- `cdSize` field carries the real value 99 instead of the APPNOTE
  -- §4.3.16 sentinel `0xFFFFFFFF`.  The ZIP64 record supplies
  -- `cdSize=55` (the actual CD length), so the reader's "sentinel or
  -- numeric match" check fires on the `cdSize` slot at
  -- [Zip/Archive.lean:396](/home/kim/lean-zip/Zip/Archive.lean:396)
  -- — the standard value is neither the sentinel nor numerically
  -- equal to the ZIP64 override.  All other slots remain at their
  -- sentinels so the relaxed sentinel arm passes for the `cdOffset`
  -- / `totalEntries` / `numberOfThisDisk` / `diskWhereCDStarts` /
  -- `numEntriesThisDisk` checks at lines 399 / 402 / 405 / 408 / 411,
  -- and the `cdSize` sub-check at line 396 is the one that trips.
  -- Per-slot sibling of `eocd-zip64-override-nosentinel.zip` (PR
  -- #1745 — `cdOffset` slot at line 399).  Generated by
  -- `scripts/build-zip64-malformed-fixtures.py`.
  let eocdZ64CdSizeData ← readFixture "zip/malformed/eocd-zip64-override-cdsize-mismatch.zip"
  let eocdZ64CdSizePath ← writeFixtureTmp "eocd-zip64-override-cdsize-mismatch.zip" eocdZ64CdSizeData
  let eocdZ64CdSizeExtractDir : System.FilePath :=
    "/tmp/lean-zip-fixture-eocd-zip64-override-cdsize-mismatch-extract"
  IO.FS.createDirAll eocdZ64CdSizeExtractDir
  assertThrows "ZIP malformed (eocd-zip64-override-cdsize-mismatch.zip)"
    (Archive.extract eocdZ64CdSizePath eocdZ64CdSizeExtractDir)
    "EOCD ZIP64-override mismatch"

  -- eocd-zip64-override-totalentries-mismatch.zip: 198-byte archive
  -- with a valid ZIP64 EOCD64 + Locator pair and a standard EOCD whose
  -- `totalEntries` field carries the real value 99 instead of the
  -- APPNOTE §4.3.16 sentinel `0xFFFF`.  The ZIP64 record supplies
  -- `totalEntries=1` (the actual entry count), so the reader's
  -- "sentinel or numeric match" check fires on the `totalEntries`
  -- slot at [Zip/Archive.lean:402](/home/kim/lean-zip/Zip/Archive.lean:402)
  -- — the standard value is neither the sentinel nor numerically
  -- equal to the ZIP64 override.  All other slots remain at their
  -- sentinels so the relaxed sentinel arm passes for the `cdSize`
  -- / `cdOffset` / `numberOfThisDisk` / `diskWhereCDStarts` /
  -- `numEntriesThisDisk` checks at lines 396 / 399 / 405 / 408 / 411,
  -- and the `totalEntries` sub-check at line 402 is the one that
  -- trips.  Per-slot sibling of `eocd-zip64-override-nosentinel.zip`
  -- (PR #1745 — `cdOffset` slot at line 399) and
  -- `eocd-zip64-override-cdsize-mismatch.zip` (PR #1900 — `cdSize`
  -- slot at line 396).  `totalEntries` is a particularly notable
  -- smuggling vector because it controls the entry-iteration loop of
  -- the CD walker — a relaxed reader that trusts a smuggled value
  -- walks more or fewer CD entries than the strict reader, opening
  -- entry-injection / entry-hiding attacks.  Generated by
  -- `scripts/build-zip64-malformed-fixtures.py`.
  let eocdZ64TotalEntriesData ← readFixture "zip/malformed/eocd-zip64-override-totalentries-mismatch.zip"
  let eocdZ64TotalEntriesPath ← writeFixtureTmp "eocd-zip64-override-totalentries-mismatch.zip" eocdZ64TotalEntriesData
  let eocdZ64TotalEntriesExtractDir : System.FilePath :=
    "/tmp/lean-zip-fixture-eocd-zip64-override-totalentries-mismatch-extract"
  IO.FS.createDirAll eocdZ64TotalEntriesExtractDir
  assertThrows "ZIP malformed (eocd-zip64-override-totalentries-mismatch.zip)"
    (Archive.extract eocdZ64TotalEntriesPath eocdZ64TotalEntriesExtractDir)
    "EOCD ZIP64-override mismatch"

  -- eocd-zip64-override-diskcd-mismatch.zip: 198-byte archive with a
  -- valid ZIP64 EOCD64 + Locator pair and a standard EOCD whose
  -- `diskWhereCDStarts` field carries the real value 99 instead of the
  -- APPNOTE §4.3.16 sentinel `0xFFFF`.  The ZIP64 record supplies
  -- `diskWhereCDStarts=0` (the actual single-disk archive's CD-disk
  -- number), so the reader's "sentinel or numeric match" check fires
  -- on the `diskWhereCDStarts` slot at
  -- [Zip/Archive.lean:408](/home/kim/lean-zip/Zip/Archive.lean:408)
  -- — the standard value is neither the sentinel nor numerically
  -- equal to the ZIP64 override.  All other slots remain at their
  -- sentinels so the relaxed sentinel arm passes for the `cdSize`
  -- / `cdOffset` / `totalEntries` / `numberOfThisDisk` /
  -- `numEntriesThisDisk` checks at lines 396 / 399 / 402 / 405 / 411,
  -- and the `diskWhereCDStarts` sub-check at line 408 is the one
  -- that trips.  Per-slot sibling of `eocd-zip64-override-nosentinel.zip`
  -- (PR #1745 — `cdOffset` slot at line 399),
  -- `eocd-zip64-override-cdsize-mismatch.zip` (PR #1900 — `cdSize`
  -- slot at line 396), and `eocd-zip64-override-totalentries-mismatch.zip`
  -- (PR #1901 — `totalEntries` slot at line 402).
  -- `diskWhereCDStarts` is the cross-disk dispatch dual of the
  -- `numberOfThisDisk` smuggling vector: standard EOCD declares "the CD
  -- lives on disk N" while the ZIP64 EOCD64 declares "the CD lives on
  -- disk M", letting an attacker present two different archives to
  -- two different parsers from the same byte sequence.  The downstream
  -- EOCD-level disk-number sanity check at
  -- [Zip/Archive.lean:521](/home/kim/lean-zip/Zip/Archive.lean:521)
  -- (`numberOfThisDisk == 0 && diskWhereCDStarts == 0`) cannot be
  -- reached when the ZIP64-override sub-check at line 408 fires first;
  -- this fixture exercises the upstream override-mismatch arm
  -- specifically.  Generated by
  -- `scripts/build-zip64-malformed-fixtures.py`.
  let eocdZ64DiskCdData ← readFixture "zip/malformed/eocd-zip64-override-diskcd-mismatch.zip"
  let eocdZ64DiskCdPath ← writeFixtureTmp "eocd-zip64-override-diskcd-mismatch.zip" eocdZ64DiskCdData
  let eocdZ64DiskCdExtractDir : System.FilePath :=
    "/tmp/lean-zip-fixture-eocd-zip64-override-diskcd-mismatch-extract"
  IO.FS.createDirAll eocdZ64DiskCdExtractDir
  assertThrows "ZIP malformed (eocd-zip64-override-diskcd-mismatch.zip)"
    (Archive.extract eocdZ64DiskCdPath eocdZ64DiskCdExtractDir)
    "EOCD ZIP64-override mismatch"

  -- zip64-eocd64-bad-recsize.zip: 198-byte archive with a valid ZIP64
  -- EOCD64 + Locator pair whose EOCD64 `size of this record` field
  -- (APPNOTE §4.3.14, at `bufPos + 4`) carries the value `0` instead
  -- of the required `44` for a v1 EOCD64.  lean-zip uses a fixed
  -- 56-byte layout and per-field offsets to read the EOCD64 contents;
  -- a stricter parser that trusts the self-declared length reads past
  -- or short of the expected 56 bytes, yielding a parser-differential
  -- smuggling vector.  Closes the EOCD64 record-size smuggling vector.
  -- Generated by `scripts/build-zip64-malformed-fixtures.py`.
  let eocd64BadRecsizeData ← readFixture "zip/malformed/zip64-eocd64-bad-recsize.zip"
  let eocd64BadRecsizePath ← writeFixtureTmp "zip64-eocd64-bad-recsize.zip" eocd64BadRecsizeData
  let eocd64BadRecsizeExtractDir : System.FilePath :=
    "/tmp/lean-zip-fixture-zip64-eocd64-bad-recsize-extract"
  IO.FS.createDirAll eocd64BadRecsizeExtractDir
  assertThrows "ZIP malformed (zip64-eocd64-bad-recsize.zip)"
    (Archive.extract eocd64BadRecsizePath eocd64BadRecsizeExtractDir)
    "ZIP64 EOCD64 record-size mismatch"

  -- zip64-eocd64-v2-record.zip: 214-byte archive with an
  -- internally-consistent APPNOTE §4.3.14.2 v2-shape EOCD64 record —
  -- `recSize=60` at `bufPos + 4` declares the 60-byte body
  -- (v1 44 + 16-byte extensible data sector for `compositeSize` +
  -- `encryptionAlgID` fields per the strong-encryption extension),
  -- and the physical record is exactly `4 + 8 + 60 = 72` bytes long.
  -- lean-zip does not implement strong encryption and accepts only the
  -- v1 shape (`recSize == 44`); the same record-size guard that rejects
  -- `zip64-eocd64-bad-recsize.zip`'s `recSize=0` boundary also rejects
  -- this `recSize=60` v2 shape.  Sibling fixture of
  -- `zip64-eocd64-bad-recsize.zip` at the specific APPNOTE-documented
  -- v2-record angle: the existing `recSize=0` fixture tests the
  -- non-44 boundary in general, this fixture pins the rejection
  -- behaviour against the v2 shape lean-zip explicitly does not
  -- implement.  The archive-layout invariant (PR #1856,
  -- `bufPos + 56 ≤ pos - 20`) passes because the 72-byte physical
  -- record places the Locator at `bufPos + 72`, so the record-size
  -- guard is the one that rejects.  Generated by
  -- `scripts/build-zip64-malformed-fixtures.py`.
  let eocd64V2Data ← readFixture "zip/malformed/zip64-eocd64-v2-record.zip"
  let eocd64V2Path ← writeFixtureTmp "zip64-eocd64-v2-record.zip" eocd64V2Data
  let eocd64V2ExtractDir : System.FilePath :=
    "/tmp/lean-zip-fixture-zip64-eocd64-v2-record-extract"
  IO.FS.createDirAll eocd64V2ExtractDir
  assertThrows "ZIP malformed (zip64-eocd64-v2-record.zip)"
    (Archive.extract eocd64V2Path eocd64V2ExtractDir)
    "ZIP64 EOCD64 record-size mismatch"

  -- zip64-eocd64-versionmadeby-too-high.zip: 198-byte archive with a
  -- valid ZIP64 EOCD64 + Locator pair whose EOCD64 `versionMadeBy`
  -- field (APPNOTE §4.4.2.1 / §4.4.2.2, at `bufPos + 12`) carries
  -- `0x0340` — low byte `0x40 = 64`, one past the APPNOTE-defined
  -- maximum spec version of `63` (6.3).  High byte `3` matches
  -- lean-zip's writer (Unix host OS).  A `versionMadeBy` with a
  -- lower byte exceeding the APPNOTE cap is either a forward-looking
  -- extension lean-zip does not support or a crafted smuggle against
  -- strict readers — a parser-differential vector when paired with a
  -- peer reader that validates the field.  Closes the archive-level
  -- EOCD64 `versionMadeBy` upper-bound dimension; per-entry sibling
  -- at CD+4 (`cd-entry-versionmadeby-too-high.zip`, issue #1812).
  -- Generated by `scripts/build-zip64-malformed-fixtures.py`.
  let eocd64VmbData ← readFixture "zip/malformed/zip64-eocd64-versionmadeby-too-high.zip"
  let eocd64VmbPath ← writeFixtureTmp "zip64-eocd64-versionmadeby-too-high.zip" eocd64VmbData
  let eocd64VmbExtractDir : System.FilePath :=
    "/tmp/lean-zip-fixture-zip64-eocd64-versionmadeby-too-high-extract"
  IO.FS.createDirAll eocd64VmbExtractDir
  assertThrows "ZIP malformed (zip64-eocd64-versionmadeby-too-high.zip)"
    (Archive.extract eocd64VmbPath eocd64VmbExtractDir)
    "ZIP64 EOCD64 versionMadeBy spec-version byte too high"

  -- zip64-eocd64-versionneeded-too-high.zip: 198-byte archive with a
  -- valid ZIP64 EOCD64 + Locator pair whose EOCD64
  -- `versionNeededToExtract` field (APPNOTE §4.4.3.2, at `bufPos + 14`)
  -- carries `0x00FF` — spec version 25.5, well above the APPNOTE-
  -- defined maximum of `63` (spec version 6.3).  A
  -- `versionNeededToExtract` exceeding the APPNOTE cap is either a
  -- forward-looking extension lean-zip does not support or a crafted
  -- smuggle against strict readers — a parser-differential vector when
  -- paired with a peer reader that validates the field.  Closes the
  -- archive-level EOCD64 `versionNeededToExtract` upper-bound dimension;
  -- paired with the lower-bound `≥ 45` sibling (issue #1758) and the
  -- per-entry CD +6 upper-bound precedent (PR #1807).  Generated by
  -- `scripts/build-zip64-malformed-fixtures.py`.
  let eocd64VneData ← readFixture "zip/malformed/zip64-eocd64-versionneeded-too-high.zip"
  let eocd64VnePath ← writeFixtureTmp "zip64-eocd64-versionneeded-too-high.zip" eocd64VneData
  let eocd64VneExtractDir : System.FilePath :=
    "/tmp/lean-zip-fixture-zip64-eocd64-versionneeded-too-high-extract"
  IO.FS.createDirAll eocd64VneExtractDir
  assertThrows "ZIP malformed (zip64-eocd64-versionneeded-too-high.zip)"
    (Archive.extract eocd64VnePath eocd64VneExtractDir)
    "ZIP64 EOCD64 versionNeededToExtract too high"

  -- zip64-eocd64-overlap-locator.zip: 190-byte archive whose Locator's
  -- `zip64EOCDOffset` points to a synthetic 48-byte EOCD64 record that
  -- ends 8 bytes *inside* the Locator — `eocd64Offset + 56 = locatorPos
  -- + 8 > locatorPos`, violating the APPNOTE §4.3.6 archive-layout
  -- invariant `[CD] [EOCD64] [Locator] [EOCD]`.  A pre-guard reader
  -- silently reads the trailing 8 bytes of the "EOCD64" from the
  -- Locator's first 8 bytes (sigLocator64 + disk), conflating the two
  -- records' field interpretations — classic parser-differential /
  -- layout-smuggling vector.  CPython's `zipfile._EndRecData64`
  -- independently rejects this archive with the same invariant
  -- (`if reloff > offset: raise BadZipFile("Corrupt zip64 end of
  -- central directory locator")`), so a strict peer reader has already
  -- been enforcing this guard; lean-zip's pre-PR reader was the
  -- outlier.  Closes the ZIP64-layer archive-layout-invariant dimension
  -- alongside the archive-level macro sibling (issue #1799 / in-flight
  -- PR #1809, `cdOffset + cdSize <= eocdPos`) and the per-entry micro
  -- sibling (PR #1813, `localOffset + 30 <= cdOffset`).  Generated by
  -- `scripts/build-zip64-malformed-fixtures.py`.
  let eocd64OverlapData ← readFixture "zip/malformed/zip64-eocd64-overlap-locator.zip"
  let eocd64OverlapPath ← writeFixtureTmp "zip64-eocd64-overlap-locator.zip" eocd64OverlapData
  let eocd64OverlapExtractDir : System.FilePath :=
    "/tmp/lean-zip-fixture-zip64-eocd64-overlap-locator-extract"
  IO.FS.createDirAll eocd64OverlapExtractDir
  assertThrows "ZIP malformed (zip64-eocd64-overlap-locator.zip)"
    (Archive.extract eocd64OverlapPath eocd64OverlapExtractDir)
    "ZIP64 EOCD64 record overlaps locator"

  -- zip64-extra-oversized-datasize.zip: 162-byte archive whose CD entry
  -- sets `stdCompSize = 0xFFFFFFFF` (ZIP64 marker) but places a ZIP64
  -- extra field (headerId 0x0001) with `dataSize = 16` — claiming two
  -- 8-byte slots — while only one standard 32-bit field is a sentinel
  -- (so APPNOTE §4.5.3 requires exactly `8 * 1 = 8` bytes).  The first
  -- 8 bytes carry the legitimate `compSize = 6` UInt64; the trailing
  -- 8 bytes are attacker-chosen slack (`0xDEADBEEFCAFEBABE`) that a
  -- lenient parser silently discards.  `parseZip64Extra` rejects with
  -- `malformed ZIP64 extra field` once `fpos != fieldEnd` after
  -- consuming the single sentinel-gated field.  Closes the ZIP64
  -- extra-field dataSize parser-differential smuggling vector — sibling
  -- of `zip64-eocd64-bad-recsize.zip`, which validates the outer EOCD64
  -- record-size field for the same attack class.  Generated by
  -- `scripts/build-zip64-malformed-fixtures.py`.
  let zip64ExtraOversizedData ← readFixture "zip/malformed/zip64-extra-oversized-datasize.zip"
  let zip64ExtraOversizedPath ←
    writeFixtureTmp "zip64-extra-oversized-datasize.zip" zip64ExtraOversizedData
  let zip64ExtraOversizedExtractDir : System.FilePath :=
    "/tmp/lean-zip-fixture-zip64-extra-oversized-datasize-extract"
  IO.FS.createDirAll zip64ExtraOversizedExtractDir
  assertThrows "ZIP malformed (zip64-extra-oversized-datasize.zip)"
    (Archive.extract zip64ExtraOversizedPath zip64ExtraOversizedExtractDir)
    "malformed ZIP64 extra field"

  -- cd-extra-overrun-datasize.zip: 138-byte archive whose CD/LH extra-data
  -- carries a single sub-field with `headerId = 0x5455` (extended-timestamp)
  -- but declared `dataSize = 0xFF`, far exceeding the 4-byte remaining
  -- payload.  No ZIP64 sentinel is set, so pre-PR `parseCentralDir` would
  -- skip `parseZip64Extra` entirely and the anomaly would be entirely
  -- invisible — a parser-differential smuggling vector independent of ZIP64
  -- (APPNOTE §4.5).  `validateExtraFieldStructure` runs unconditionally on
  -- the extra-data before the sentinel guard and rejects with
  -- `malformed extra field`.  Sibling of `zip64-extra-oversized-datasize.zip`,
  -- which addresses the *inner* 0x0001-block invariant; this fixture
  -- addresses the *outer* sub-field iteration layer.  Generated by
  -- `scripts/build-zip64-malformed-fixtures.py`.
  let cdExtraOverrunData ← readFixture "zip/malformed/cd-extra-overrun-datasize.zip"
  let cdExtraOverrunPath ← writeFixtureTmp "cd-extra-overrun-datasize.zip" cdExtraOverrunData
  let cdExtraOverrunExtractDir : System.FilePath :=
    "/tmp/lean-zip-fixture-cd-extra-overrun-datasize-extract"
  IO.FS.createDirAll cdExtraOverrunExtractDir
  assertThrows "ZIP malformed (cd-extra-overrun-datasize.zip)"
    (Archive.extract cdExtraOverrunPath cdExtraOverrunExtractDir)
    "malformed extra field"

  -- cd-zip64-extra-duplicate.zip: 158-byte archive whose CD entry
  -- supplies two ZIP64 (headerId 0x0001) blocks back-to-back in the
  -- extra-data area while only `stdUncompSize` is the ZIP64 sentinel.
  -- APPNOTE §4.5 forbids more than one instance of a registered header
  -- ID per entry's extra-data; lean-zip's pre-fix `parseZip64Extra`
  -- silently used the first 0x0001 block (`uncompSize = 6`) while a
  -- "last-wins" parser would have used the second (`uncompSize = 106`)
  -- — a parser-differential smuggling vector.  The LH carries a single
  -- valid 0x0001 block so the CD-side `hasDuplicateZip64Extra` guard
  -- (which fires before the LH read) attributes the fault.  Generated
  -- by `scripts/build-zip64-malformed-fixtures.py`.
  let cdZ64DupData ← readFixture "zip/malformed/cd-zip64-extra-duplicate.zip"
  let cdZ64DupPath ← writeFixtureTmp "cd-zip64-extra-duplicate.zip" cdZ64DupData
  let cdZ64DupExtractDir : System.FilePath :=
    "/tmp/lean-zip-fixture-cd-zip64-extra-duplicate-extract"
  IO.FS.createDirAll cdZ64DupExtractDir
  assertThrows "ZIP malformed (cd-zip64-extra-duplicate.zip)"
    (Archive.extract cdZ64DupPath cdZ64DupExtractDir)
    "duplicate ZIP64 extra field"

  -- lh-zip64-extra-duplicate.zip: 158-byte archive whose CD entry has a
  -- single valid ZIP64 (headerId 0x0001) extra block (so CD parse
  -- passes), but the LH carries duplicate 0x0001 blocks.  The LH-side
  -- `hasDuplicateZip64Extra` guard fires inside `readEntryData` before
  -- any CD/LH consistency check.  Sibling of `cd-zip64-extra-duplicate.zip`
  -- — the LH error wording (`duplicate ZIP64 local extra field`) is
  -- distinct so a regression in attribution is loud.  Generated by
  -- `scripts/build-zip64-malformed-fixtures.py`.
  let lhZ64DupData ← readFixture "zip/malformed/lh-zip64-extra-duplicate.zip"
  let lhZ64DupPath ← writeFixtureTmp "lh-zip64-extra-duplicate.zip" lhZ64DupData
  let lhZ64DupExtractDir : System.FilePath :=
    "/tmp/lean-zip-fixture-lh-zip64-extra-duplicate-extract"
  IO.FS.createDirAll lhZ64DupExtractDir
  assertThrows "ZIP malformed (lh-zip64-extra-duplicate.zip)"
    (Archive.extract lhZ64DupPath lhZ64DupExtractDir)
    "duplicate ZIP64 local extra field"

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
             "cd-lh-modtime-mismatch.zip",
             "eocd-numentries-mismatch.zip",
             "eocd-disknum-mismatch.zip",
             "eocd-numentries-thisdisk-mismatch.zip",
             "cd-entry-disknum-mismatch.zip",
             "cd-entry-internal-attrs-reserved.zip",
             "cd-nul-in-name.zip",
             "cd-empty-name.zip",
             "cd-empty-entry-crc-nonzero.zip",
             "cd-deflate-zero-compsize.zip",
             "cd-path-unsafe.zip",
             "cd-patched-data-flag.zip",
             "cd-stored-size-mismatch.zip",
             "cd-bad-method-early.zip",
             "cd-version-needed-too-high.zip",
             "cd-entry-localoffset-past-cdstart.zip",
             "cd-bad-lh-signature.zip",
             "cd-entry-past-cdend.zip",
             "eocd-zip64-override-nosentinel.zip",
             "eocd-zip64-override-cdsize-mismatch.zip",
             "eocd-zip64-override-totalentries-mismatch.zip",
             "eocd-zip64-override-diskcd-mismatch.zip",
             "zip64-eocd64-bad-recsize.zip",
             "zip64-eocd64-v2-record.zip",
             "zip64-eocd64-versionmadeby-too-high.zip",
             "zip64-eocd64-versionneeded-too-high.zip",
             "zip64-eocd64-overlap-locator.zip",
             "zip64-extra-oversized-datasize.zip",
             "cd-extra-overrun-datasize.zip",
             "cd-zip64-extra-duplicate.zip",
             "lh-zip64-extra-duplicate.zip",
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
             "/tmp/lean-zip-fixture-cd-lh-modtime-mismatch-extract",
             "/tmp/lean-zip-fixture-eocd-numentries-mismatch-extract",
             "/tmp/lean-zip-fixture-eocd-disknum-mismatch-extract",
             "/tmp/lean-zip-fixture-eocd-numentries-thisdisk-mismatch-extract",
             "/tmp/lean-zip-fixture-cd-entry-disknum-mismatch-extract",
             "/tmp/lean-zip-fixture-cd-entry-internal-attrs-reserved-extract",
             "/tmp/lean-zip-fixture-cd-nul-in-name-extract",
             "/tmp/lean-zip-fixture-cd-empty-name-extract",
             "/tmp/lean-zip-fixture-cd-empty-entry-crc-nonzero-extract",
             "/tmp/lean-zip-fixture-cd-deflate-zero-compsize-extract",
             "/tmp/lean-zip-fixture-cd-path-unsafe-extract",
             "/tmp/lean-zip-fixture-cd-patched-data-flag-extract",
             "/tmp/lean-zip-fixture-cd-stored-size-mismatch-extract",
             "/tmp/lean-zip-fixture-cd-bad-method-early-extract",
             "/tmp/lean-zip-fixture-cd-version-needed-too-high-extract",
             "/tmp/lean-zip-fixture-cd-entry-localoffset-past-cdstart-extract",
             "/tmp/lean-zip-fixture-cd-bad-lh-signature-extract",
             "/tmp/lean-zip-fixture-cd-entry-past-cdend-extract",
             "/tmp/lean-zip-fixture-eocd-zip64-override-nosentinel-extract",
             "/tmp/lean-zip-fixture-eocd-zip64-override-cdsize-mismatch-extract",
             "/tmp/lean-zip-fixture-eocd-zip64-override-totalentries-mismatch-extract",
             "/tmp/lean-zip-fixture-eocd-zip64-override-diskcd-mismatch-extract",
             "/tmp/lean-zip-fixture-zip64-eocd64-bad-recsize-extract",
             "/tmp/lean-zip-fixture-zip64-eocd64-v2-record-extract",
             "/tmp/lean-zip-fixture-zip64-eocd64-versionmadeby-too-high-extract",
             "/tmp/lean-zip-fixture-zip64-eocd64-versionneeded-too-high-extract",
             "/tmp/lean-zip-fixture-zip64-eocd64-overlap-locator-extract",
             "/tmp/lean-zip-fixture-zip64-extra-oversized-datasize-extract",
             "/tmp/lean-zip-fixture-cd-extra-overrun-datasize-extract",
             "/tmp/lean-zip-fixture-cd-zip64-extra-duplicate-extract",
             "/tmp/lean-zip-fixture-lh-zip64-extra-duplicate-extract",
             "/tmp/lean-zip-fixture-zip-slip-extract", "/tmp/lean-zip-fixture-abs-path-extract"] do
    let _ ← IO.Process.run { cmd := "rm", args := #["-rf", d] }
  IO.println "ZIP fixture tests: OK"
