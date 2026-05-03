import ZipTest.Helpers

set_option maxRecDepth 1024

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

  -- === TAR malformed PAX fixtures ===
  -- Each fixture pairs a malformed PAX extended header with a regular
  -- "hello.txt" entry. Existing guards in `parsePaxRecords` silently
  -- skip the PAX block; listing should return just the regular entry.
  -- `pax-path-nul-in-value.tar` (PR #1866, `path` slot) and
  -- `pax-linkpath-nul-in-value.tar` (PR #1979, `linkpath` slot)
  -- exercise the NUL-byte guard on `valueBytes`;
  -- `pax-nul-in-key.tar` (this PR, `keyBytes` arm) closes the
  -- third per-arm position of `parsePaxRecords`'s NUL-byte guard
  -- family at 3/3 (1 keyBytes + 2 valueBytes). The keyBytes arm is
  -- defense-in-depth — `applyPaxOverrides`'s case match drops any
  -- NUL-bearing key regardless of the guard — so the loop's
  -- `entries[0]!.path == "hello.txt"` assertion is sufficient for
  -- the keyBytes fixture; no per-slot follow-up needed. The
  -- `linkpath` arm still requires an additional per-slot check on
  -- `entries[0]!.linkname` (added immediately after the loop).
  for fixture in #["pax-oversized-length.tar", "pax-truncated-record.tar",
                    "pax-invalid-utf8-key.tar", "pax-invalid-utf8-value.tar",
                    "pax-inconsistent-length.tar",
                    "pax-path-nul-in-value.tar",
                    "pax-linkpath-nul-in-value.tar",
                    "pax-nul-in-key.tar"] do
    let paxData ← readFixture s!"tar/malformed/{fixture}"
    let paxPath ← writeFixtureTmp fixture paxData
    let entries ← IO.FS.withFile paxPath .read fun h =>
      Tar.list (IO.FS.Stream.ofHandle h)
    unless entries.size == 1 do
      throw (IO.userError s!"TAR malformed ({fixture}): expected 1 entry, got {entries.size}")
    unless entries[0]!.path == "hello.txt" do
      throw (IO.userError s!"TAR malformed ({fixture}): expected regular entry 'hello.txt', got '{entries[0]!.path}'")

  -- Per-slot assertion for pax-linkpath-nul-in-value.tar:
  -- the linkpath= override must have been dropped, so the trailing
  -- regular-file entry's linkname stays at "" (its declared default
  -- for typeRegular). Without the guard, entry.linkname would be
  -- "a\x00b/c" — a symlink(2) truncation smuggle vector. The loop's
  -- `path == "hello.txt"` check alone does not prove that the
  -- `linkpath` override was dropped, since `path` would also be
  -- unaffected by an unrelated `linkpath` override.
  let linkpathData ← readFixture "tar/malformed/pax-linkpath-nul-in-value.tar"
  let linkpathPath ← writeFixtureTmp "pax-linkpath-nul-in-value.tar" linkpathData
  let linkpathEntries ← IO.FS.withFile linkpathPath .read fun h =>
    Tar.list (IO.FS.Stream.ofHandle h)
  unless linkpathEntries[0]!.linkname == "" do
    throw (IO.userError s!"pax-linkpath-nul-in-value.tar: expected linkname='', got {linkpathEntries[0]!.linkname.quote}")

  -- Duplicate-key smuggle in PAX extended header: two `path=` records
  -- (`safe.txt` then `../etc/passwd`) must be rejected by the new
  -- `parsePaxRecords` duplicate-key guard, closing the last
  -- parser-differential dimension on the PAX-record validation surface
  -- (sibling of PR #1866's NUL-byte key/value silent-skip on the same
  -- loop). POSIX SUSv4 §pax leaves record order unspecified, so a
  -- lenient (first-wins) reader would take `"safe.txt"` while a strict
  -- (last-wins) reader would take `"../etc/passwd"` — rejecting at
  -- parse time ensures neither listing nor extract callers diverge
  -- from any peer parser on this input.
  let paxDupData ← readFixture "tar/malformed/pax-duplicate-path.tar"
  let paxDupPath ← writeFixtureTmp "pax-duplicate-path.tar" paxDupData
  assertThrows "TAR malformed (pax-duplicate-path.tar)"
    (IO.FS.withFile paxDupPath .read fun h => do
      let _ ← Tar.list (IO.FS.Stream.ofHandle h)
      pure ())
    "duplicate"

  -- === TAR malformed GNU long-name / long-link fixtures ===
  -- Truncated long-name and long-link payloads must surface as a clean
  -- end-of-archive error rather than a panic.
  let gnuLnTruncData ← readFixture "tar/malformed/gnu-longname-truncated.tar"
  let gnuLnTruncPath ← writeFixtureTmp "gnu-longname-truncated.tar" gnuLnTruncData
  assertThrows "TAR malformed (gnu-longname-truncated.tar)"
    (IO.FS.withFile gnuLnTruncPath .read fun h => do
      let _ ← Tar.list (IO.FS.Stream.ofHandle h)
      pure ())
    "end of archive"

  let gnuLkTruncData ← readFixture "tar/malformed/gnu-longlink-truncated.tar"
  let gnuLkTruncPath ← writeFixtureTmp "gnu-longlink-truncated.tar" gnuLkTruncData
  assertThrows "TAR malformed (gnu-longlink-truncated.tar)"
    (IO.FS.withFile gnuLkTruncPath .read fun h => do
      let _ ← Tar.list (IO.FS.Stream.ofHandle h)
      pure ())
    "end of archive"

  -- NUL-byte smuggle in GNU long-name payload: must be rejected by the
  -- new raw-bytes guard before UTF-8 / Latin-1 decode runs. Sibling of
  -- the ZIP CD-parse NUL-byte guard (PR #1831).
  let gnuLnNulData ← readFixture "tar/malformed/gnu-longname-nul-in-name.tar"
  let gnuLnNulPath ← writeFixtureTmp "gnu-longname-nul-in-name.tar" gnuLnNulData
  assertThrows "TAR malformed (gnu-longname-nul-in-name.tar)"
    (IO.FS.withFile gnuLnNulPath .read fun h => do
      let _ ← Tar.list (IO.FS.Stream.ofHandle h)
      pure ())
    "GNU long-name contains NUL byte"

  -- NUL-byte smuggle in GNU long-link payload: per-slot sibling of
  -- the long-name fixture above, covering the long-link arm of the
  -- 2-slot forEntries interior-NUL guard. Substring includes
  -- `"long-link"` to keep per-slot distinction — the bare
  -- `"GNU long-"` prefix would also match the long-name arm.
  let gnuLkNulData ← readFixture "tar/malformed/gnu-longlink-nul-in-link.tar"
  let gnuLkNulPath ← writeFixtureTmp "gnu-longlink-nul-in-link.tar" gnuLkNulData
  assertThrows "TAR malformed (gnu-longlink-nul-in-link.tar)"
    (IO.FS.withFile gnuLkNulPath .read fun h => do
      let _ ← Tar.list (IO.FS.Stream.ofHandle h)
      pure ())
    "GNU long-link contains NUL byte"

  -- NUL-byte smuggle in UStar `name` field: must be rejected by the
  -- `hasInteriorNul` guard in `parseHeader` before
  -- `Binary.readString` truncates the payload at the embedded NUL.
  -- The `linkname` (offset 157) and `prefix` (offset 345) arms share
  -- the same guard and the same `Binary.readString` truncation path;
  -- each is now pinned by its own dedicated sibling fixture below.
  -- Closes the UStar layer of the smuggled-NUL attack class
  -- — sibling of PR #1831 (ZIP CD), PR #1865 (GNU long-name /
  -- long-link), and PR #1866 (PAX key/value).
  let ustarNameNulData ← readFixture "tar/malformed/ustar-name-nul-in-name.tar"
  let ustarNameNulPath ← writeFixtureTmp "ustar-name-nul-in-name.tar" ustarNameNulData
  assertThrows "TAR malformed (ustar-name-nul-in-name.tar)"
    (IO.FS.withFile ustarNameNulPath .read fun h => do
      let _ ← Tar.list (IO.FS.Stream.ofHandle h)
      pure ())
    "UStar name contains NUL byte"

  -- NUL-byte smuggle in UStar `linkname` field: must be rejected by
  -- the `hasInteriorNul` guard in `parseHeader` at line 517, the
  -- middle of the three-slot per-field arm. The fixture's `path` is
  -- `"safe"` (no NUL) so the `name`-arm guard at line 515 cannot
  -- fire first — attribution pins on the `linkname` arm. Substring
  -- includes `"linkname"` to keep per-slot distinction (the bare
  -- `"UStar"` prefix would also match the `name` and `prefix` arms).
  let ustarLnNulData ← readFixture "tar/malformed/ustar-linkname-nul-in-name.tar"
  let ustarLnNulPath ← writeFixtureTmp "ustar-linkname-nul-in-name.tar" ustarLnNulData
  assertThrows "TAR malformed (ustar-linkname-nul-in-name.tar)"
    (IO.FS.withFile ustarLnNulPath .read fun h => do
      let _ ← Tar.list (IO.FS.Stream.ofHandle h)
      pure ())
    "UStar linkname contains NUL byte"

  -- NUL-byte smuggle in UStar `prefix` field: must be rejected by
  -- the `hasInteriorNul` guard in `parseHeader` at line 519, the
  -- last of the three-slot per-field arm. The fixture's `name`
  -- slot carries the clean `"name.txt"` so the `name`-arm guard at
  -- line 515 cannot fire first — attribution pins on the `prefix`
  -- arm. Substring includes `"prefix"` to keep per-slot distinction
  -- (the bare `"UStar"` prefix would also match the `name` and
  -- `linkname` arms). Closes the 3-slot UStar interior-NUL family
  -- (`name` / `linkname` / `prefix`).
  let ustarPfxNulData ← readFixture "tar/malformed/ustar-prefix-nul-in-name.tar"
  let ustarPfxNulPath ← writeFixtureTmp "ustar-prefix-nul-in-name.tar" ustarPfxNulData
  assertThrows "TAR malformed (ustar-prefix-nul-in-name.tar)"
    (IO.FS.withFile ustarPfxNulPath .read fun h => do
      let _ ← Tar.list (IO.FS.Stream.ofHandle h)
      pure ())
    "UStar prefix contains NUL byte"

  -- NUL-byte smuggle in UStar `uname` field: must be rejected by the
  -- 4th-slot `hasInteriorNul` guard in `parseHeader`, the
  -- defense-in-depth extension of the closed 3-slot
  -- `name`/`linkname`/`prefix` family. The fixture's `path` is `"safe"`
  -- (no NUL) and `linkname`/`prefix` are clean so none of the three
  -- earlier arms can fire first — attribution pins on the `uname` arm.
  -- Substring includes `"uname"` to keep per-slot distinction (the bare
  -- `"UStar"` prefix would also match the `name` / `linkname` /
  -- `prefix` arms). Unlike the 3-slot family, `uname` does not reach
  -- the filesystem in `Tar.extract` — the guard is defense-in-depth
  -- against a `Tar.list` caller routing on `entry.uname` for a trust
  -- decision and seeing only the truncated prefix while peer parsers
  -- preserve the full bytes. The `gname` slot is the final (5-slot)
  -- sibling deferred to a follow-up planner cycle.
  let ustarUnameNulData ← readFixture "tar/malformed/ustar-uname-nul-in-uname.tar"
  let ustarUnameNulPath ← writeFixtureTmp "ustar-uname-nul-in-uname.tar" ustarUnameNulData
  assertThrows "TAR malformed (ustar-uname-nul-in-uname.tar)"
    (IO.FS.withFile ustarUnameNulPath .read fun h => do
      let _ ← Tar.list (IO.FS.Stream.ofHandle h)
      pure ())
    "UStar uname contains NUL byte"

  -- NUL-byte smuggle in UStar `gname` field: must be rejected by the
  -- 5th-slot `hasInteriorNul` guard in `parseHeader`, the second
  -- defense-in-depth extension closing the 5-slot UStar interior-NUL
  -- family (3-slot filesystem-reaching arm `name` / `linkname` /
  -- `prefix` plus 2-slot defense-in-depth arm `uname` / `gname`). The
  -- fixture's `path` is `"safe"` (no NUL) and `linkname` / `prefix` /
  -- `uname` are clean so none of the four earlier arms can fire first
  -- — attribution pins on the `gname` arm. Substring includes
  -- `"gname"` to keep per-slot distinction (the bare `"UStar"` prefix
  -- would also match the `name` / `linkname` / `prefix` / `uname`
  -- arms). Like `uname`, `gname` does not reach the filesystem in
  -- `Tar.extract` — the guard is defense-in-depth against a
  -- `Tar.list` caller routing on `entry.gname` for a trust decision
  -- and seeing only the truncated prefix while peer parsers preserve
  -- the full bytes.
  let ustarGnameNulData ← readFixture "tar/malformed/ustar-gname-nul-in-gname.tar"
  let ustarGnameNulPath ← writeFixtureTmp "ustar-gname-nul-in-gname.tar" ustarGnameNulData
  assertThrows "TAR malformed (ustar-gname-nul-in-gname.tar)"
    (IO.FS.withFile ustarGnameNulPath .read fun h => do
      let _ ← Tar.list (IO.FS.Stream.ofHandle h)
      pure ())
    "UStar gname contains NUL byte"

  -- Non-throwing variants: payloads with no trailing NUL and with
  -- invalid UTF-8 must each apply a predictable name to the next entry.
  let gnuLnNoTermData ← readFixture "tar/malformed/gnu-longname-no-terminator.tar"
  let gnuLnNoTermPath ← writeFixtureTmp "gnu-longname-no-terminator.tar" gnuLnNoTermData
  let gnuLnNoTermEntries ← IO.FS.withFile gnuLnNoTermPath .read fun h =>
    Tar.list (IO.FS.Stream.ofHandle h)
  unless gnuLnNoTermEntries.size == 1 do
    throw (IO.userError s!"gnu-longname-no-terminator.tar: expected 1 entry, got {gnuLnNoTermEntries.size}")
  let expectedNoTermPath := String.ofList (List.replicate 100 'a')
  unless gnuLnNoTermEntries[0]!.path == expectedNoTermPath do
    throw (IO.userError s!"gnu-longname-no-terminator.tar: path mismatch: {repr gnuLnNoTermEntries[0]!.path}")

  let gnuLnUtf8Data ← readFixture "tar/malformed/gnu-longname-invalid-utf8.tar"
  let gnuLnUtf8Path ← writeFixtureTmp "gnu-longname-invalid-utf8.tar" gnuLnUtf8Data
  let gnuLnUtf8Entries ← IO.FS.withFile gnuLnUtf8Path .read fun h =>
    Tar.list (IO.FS.Stream.ofHandle h)
  unless gnuLnUtf8Entries.size == 1 do
    throw (IO.userError s!"gnu-longname-invalid-utf8.tar: expected 1 entry, got {gnuLnUtf8Entries.size}")
  let expectedUtf8Path := Binary.fromLatin1 (ByteArray.mk #[0xFF, 0xFF, 0xFF])
  unless gnuLnUtf8Entries[0]!.path == expectedUtf8Path do
    throw (IO.userError s!"gnu-longname-invalid-utf8.tar: path mismatch: {repr gnuLnUtf8Entries[0]!.path}")

  -- === TAR malformed header-oversized fixtures ===
  -- A crafted GNU long-name (typeflag 'L') / PAX extended-header
  -- (typeflag 'x') pseudo-entry whose `size` field decodes to ≈ 8 GiB
  -- must be rejected by the `maxHeaderSize` cap in `readEntryData`
  -- before any allocation runs. Each fixture is a single 512-byte
  -- header — no payload required, since the cap fires before the read
  -- loop.
  let gnuLnOverData ← readFixture "tar/malformed/gnu-longname-oversized-size.tar"
  let gnuLnOverPath ← writeFixtureTmp "gnu-longname-oversized-size.tar" gnuLnOverData
  assertThrows "TAR malformed (gnu-longname-oversized-size.tar)"
    (IO.FS.withFile gnuLnOverPath .read fun h => do
      let _ ← Tar.list (IO.FS.Stream.ofHandle h)
      pure ())
    "exceeds maximum"

  let paxExtOverData ← readFixture "tar/malformed/pax-extended-oversized-size.tar"
  let paxExtOverPath ← writeFixtureTmp "pax-extended-oversized-size.tar" paxExtOverData
  assertThrows "TAR malformed (pax-extended-oversized-size.tar)"
    (IO.FS.withFile paxExtOverPath .read fun h => do
      let _ ← Tar.list (IO.FS.Stream.ofHandle h)
      pure ())
    "exceeds maximum"

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

  -- backslash-slip.tar: regular-file path "..\evil.txt".
  -- `Binary.isPathSafe` rejects `\` before any traversal check fires,
  -- so the error reads "unsafe path".
  let backslashSlipData ← readFixture "tar/security/backslash-slip.tar"
  let backslashSlipPath ← writeFixtureTmp "backslash-slip.tar" backslashSlipData
  let backslashSlipExtract : System.FilePath := "/tmp/lean-zip-fixture-backslash-slip-extract"
  IO.FS.createDirAll backslashSlipExtract
  assertThrows "TAR security (backslash-slip.tar)"
    (IO.FS.withFile backslashSlipPath .read fun h =>
      Tar.extract (IO.FS.Stream.ofHandle h) backslashSlipExtract)
    "unsafe path"

  -- symlink-absolute.tar: typeflag '2' with linkname "/etc/passwd".
  -- Must be rejected before `Handle.createSymlink` is called.
  let symAbsData ← readFixture "tar/security/symlink-absolute.tar"
  let symAbsPath ← writeFixtureTmp "symlink-absolute.tar" symAbsData
  let symAbsExtract : System.FilePath := "/tmp/lean-zip-fixture-symlink-abs-extract"
  IO.FS.createDirAll symAbsExtract
  assertThrows "TAR security (symlink-absolute.tar)"
    (IO.FS.withFile symAbsPath .read fun h =>
      Tar.extract (IO.FS.Stream.ofHandle h) symAbsExtract)
    "unsafe symlink"

  -- hardlink-outside.tar: typeflag '1' (typeHardlink) with linkname
  -- "../outside". Policy: silently skip — no filesystem entry created,
  -- so the extract dir must remain empty. This doubles as a
  -- regression against accidentally promoting hardlinks to a live
  -- `createHardlink` call.
  let hlData ← readFixture "tar/security/hardlink-outside.tar"
  let hlPath ← writeFixtureTmp "hardlink-outside.tar" hlData
  let hlExtract : System.FilePath := "/tmp/lean-zip-fixture-hardlink-outside-extract"
  if ← hlExtract.pathExists then
    let _ ← IO.Process.run { cmd := "rm", args := #["-rf", hlExtract.toString] }
  IO.FS.createDirAll hlExtract
  IO.FS.withFile hlPath .read fun h =>
    Tar.extract (IO.FS.Stream.ofHandle h) hlExtract
  let hlEntries ← hlExtract.readDir
  unless hlEntries.isEmpty do
    let names := hlEntries.map (·.fileName)
    throw (IO.userError s!"hardlink-outside.tar: extract dir should be empty, got {names}")

  -- tar-fifo-skipped.tar: typeflag '6' (POSIX UStar FIFO, 0x36).
  -- Policy: silent skip — no filesystem entry created, so the extract
  -- dir must remain empty. This pins the silent-skip policy's FIFO arm
  -- as a second sibling alongside hardlink-outside.tar (typeflag '1');
  -- together they pin two distinct typeflag values against the shared
  -- `else` fallback in `Tar.extract`, so a future refactor that drops
  -- the fallback for one arm cannot escape detection by both fixtures.
  let fifoData ← readFixture "tar/security/tar-fifo-skipped.tar"
  let fifoPath ← writeFixtureTmp "tar-fifo-skipped.tar" fifoData
  let fifoExtract : System.FilePath :=
    "/tmp/lean-zip-fixture-tar-fifo-skipped-extract"
  if ← fifoExtract.pathExists then
    let _ ← IO.Process.run { cmd := "rm", args := #["-rf", fifoExtract.toString] }
  IO.FS.createDirAll fifoExtract
  IO.FS.withFile fifoPath .read fun h =>
    Tar.extract (IO.FS.Stream.ofHandle h) fifoExtract
  let fifoEntries ← fifoExtract.readDir
  unless fifoEntries.isEmpty do
    let names := fifoEntries.map (·.fileName)
    throw (IO.userError s!"tar-fifo-skipped.tar: extract dir should be empty, got {names}")

  -- tar-chardev-skipped.tar: typeflag '3' (POSIX UStar character
  -- device). Policy: silent skip — no filesystem entry created, so
  -- the extract dir must remain empty. This pins the silent-skip
  -- policy's character-device arm as a third sibling alongside
  -- hardlink-outside.tar (typeflag '1') and tar-fifo-skipped.tar
  -- (typeflag '6'); together they pin three distinct typeflag
  -- values against the shared `else` fallback in `Tar.extract`.
  let cdData ← readFixture "tar/security/tar-chardev-skipped.tar"
  let cdPath ← writeFixtureTmp "tar-chardev-skipped.tar" cdData
  let cdExtract : System.FilePath :=
    "/tmp/lean-zip-fixture-tar-chardev-skipped-extract"
  if ← cdExtract.pathExists then
    let _ ← IO.Process.run { cmd := "rm", args := #["-rf", cdExtract.toString] }
  IO.FS.createDirAll cdExtract
  IO.FS.withFile cdPath .read fun h =>
    Tar.extract (IO.FS.Stream.ofHandle h) cdExtract
  let cdEntries ← cdExtract.readDir
  unless cdEntries.isEmpty do
    let names := cdEntries.map (·.fileName)
    throw (IO.userError s!"tar-chardev-skipped.tar: extract dir should be empty, got {names}")

  -- tar-blockdev-skipped.tar: typeflag '4' (POSIX UStar block device).
  -- Policy: silent skip — no filesystem entry created, so the extract
  -- dir must remain empty. This pins the silent-skip policy's
  -- block-device arm as a fourth sibling alongside
  -- hardlink-outside.tar (typeflag '1'), tar-fifo-skipped.tar
  -- (typeflag '6'), and tar-chardev-skipped.tar (typeflag '3');
  -- together they pin four distinct typeflag values against the
  -- shared `else` fallback in `Tar.extract`.
  let bdData ← readFixture "tar/security/tar-blockdev-skipped.tar"
  let bdPath ← writeFixtureTmp "tar-blockdev-skipped.tar" bdData
  let bdExtract : System.FilePath :=
    "/tmp/lean-zip-fixture-tar-blockdev-skipped-extract"
  if ← bdExtract.pathExists then
    let _ ← IO.Process.run { cmd := "rm", args := #["-rf", bdExtract.toString] }
  IO.FS.createDirAll bdExtract
  IO.FS.withFile bdPath .read fun h =>
    Tar.extract (IO.FS.Stream.ofHandle h) bdExtract
  let bdEntries ← bdExtract.readDir
  unless bdEntries.isEmpty do
    let names := bdEntries.map (·.fileName)
    throw (IO.userError s!"tar-blockdev-skipped.tar: extract dir should be empty, got {names}")

  -- tar-contiguous-skipped.tar: typeflag '7' (POSIX UStar contiguous
  -- file). Policy: silent skip — no filesystem entry created, so the
  -- extract dir must remain empty. This pins the silent-skip policy's
  -- contiguous-file arm as a fifth sibling alongside
  -- hardlink-outside.tar (typeflag '1'), tar-fifo-skipped.tar
  -- (typeflag '6'), tar-chardev-skipped.tar (typeflag '3'), and
  -- tar-blockdev-skipped.tar (typeflag '4'); together they pin five
  -- distinct typeflag values against the shared `else` fallback in
  -- `Tar.extract`. The strict-vs-lenient choice — lean-zip rejects '7'
  -- rather than aliasing it to '0' (regular file) as some lenient peer
  -- extractors do — is the security-relevant behaviour this fixture
  -- pins. With this fixture landing, the POSIX UStar '0'–'7' numeric
  -- range is fully fixtured (every value '0' through '7' has either a
  -- typed branch in `Tar.extract` or a silent-skip regression
  -- fixture).
  let cgData ← readFixture "tar/security/tar-contiguous-skipped.tar"
  let cgPath ← writeFixtureTmp "tar-contiguous-skipped.tar" cgData
  let cgExtract : System.FilePath :=
    "/tmp/lean-zip-fixture-tar-contiguous-skipped-extract"
  if ← cgExtract.pathExists then
    let _ ← IO.Process.run { cmd := "rm", args := #["-rf", cgExtract.toString] }
  IO.FS.createDirAll cgExtract
  IO.FS.withFile cgPath .read fun h =>
    Tar.extract (IO.FS.Stream.ofHandle h) cgExtract
  let cgEntries ← cgExtract.readDir
  unless cgEntries.isEmpty do
    let names := cgEntries.map (·.fileName)
    throw (IO.userError s!"tar-contiguous-skipped.tar: extract dir should be empty, got {names}")

  -- tar-volumeheader-skipped.tar: typeflag 'V' (GNU multi-volume archive
  -- label marker, 0x56). Policy: silent skip — no filesystem entry
  -- created, so the extract dir must remain empty. This pins the
  -- silent-skip policy's GNU volume-header arm as the **first
  -- GNU-typeflag** sibling alongside the POSIX UStar siblings
  -- hardlink-outside.tar (typeflag '1'), tar-fifo-skipped.tar
  -- (typeflag '6'), tar-chardev-skipped.tar (typeflag '3'),
  -- tar-blockdev-skipped.tar (typeflag '4'), and
  -- tar-contiguous-skipped.tar (typeflag '7'); together they pin six
  -- distinct typeflag values against the shared `else` fallback in
  -- `Tar.extract`, opening a GNU-typeflag sub-ladder distinct from the
  -- POSIX UStar '0'–'7' numeric range. The strict-vs-lenient distinction
  -- is the security-relevant policy choice this fixture pins: a
  -- malicious archive could ship a 'V' entry with a volume label
  -- crafted to look like a filesystem path (e.g. "../../../etc/passwd"),
  -- expecting a lenient extractor to materialise the marker as a
  -- regular file — lean-zip's policy of never materialising 'V' entries
  -- (regardless of `path` / payload) is the correct conservative
  -- choice. The optional `Tar.list` assertion below confirms the entry
  -- is preserved through `list` with `typeflag = 0x56` even though
  -- `extract` skips it, pinning the callers-routing-on-typeflag
  -- invariant.
  let vhData ← readFixture "tar/security/tar-volumeheader-skipped.tar"
  let vhPath ← writeFixtureTmp "tar-volumeheader-skipped.tar" vhData
  let vhExtract : System.FilePath :=
    "/tmp/lean-zip-fixture-tar-volumeheader-skipped-extract"
  if ← vhExtract.pathExists then
    let _ ← IO.Process.run { cmd := "rm", args := #["-rf", vhExtract.toString] }
  IO.FS.createDirAll vhExtract
  IO.FS.withFile vhPath .read fun h =>
    Tar.extract (IO.FS.Stream.ofHandle h) vhExtract
  let vhEntries ← vhExtract.readDir
  unless vhEntries.isEmpty do
    let names := vhEntries.map (·.fileName)
    throw (IO.userError s!"tar-volumeheader-skipped.tar: extract dir should be empty, got {names}")
  let vhListed ← IO.FS.withFile vhPath .read fun h =>
    Tar.list (IO.FS.Stream.ofHandle h)
  unless vhListed.size == 1 do
    throw (IO.userError s!"tar-volumeheader-skipped.tar: expected 1 entry from Tar.list, got {vhListed.size}")
  unless vhListed[0]!.typeflag == 0x56 do
    throw (IO.userError s!"tar-volumeheader-skipped.tar: expected Tar.list typeflag = 0x56, got {vhListed[0]!.typeflag}")

  -- tar-multivol-skipped.tar: typeflag 'M' (GNU multi-volume continuation
  -- marker, 0x4D). Policy: silent skip — no filesystem entry created, so
  -- the extract dir must remain empty. This pins the silent-skip policy's
  -- GNU multi-volume-continuation arm as the **second GNU-typeflag**
  -- sibling alongside tar-volumeheader-skipped.tar (typeflag 'V', 0x56),
  -- extending the GNU-typeflag sub-ladder distinct from the POSIX UStar
  -- '0'–'7' numeric range covered by hardlink-outside.tar (typeflag '1'),
  -- tar-fifo-skipped.tar (typeflag '6'), tar-chardev-skipped.tar
  -- (typeflag '3'), tar-blockdev-skipped.tar (typeflag '4'), and
  -- tar-contiguous-skipped.tar (typeflag '7'); together the seven pin
  -- seven distinct typeflag values against the shared `else` fallback in
  -- `Tar.extract`. The strict-vs-lenient distinction is the
  -- security-relevant policy choice this fixture pins: a malicious
  -- single-volume archive could ship a 'M' entry as a top-level record
  -- (without a preceding multi-volume context) with a crafted `path`
  -- field (e.g. "../../../etc/passwd") and a non-zero `size` declaring a
  -- fake "remaining payload", expecting a lenient extractor to
  -- materialise the marker as a regular file — lean-zip's policy of
  -- never materialising 'M' entries (regardless of `path` / declared
  -- `size` / actual payload) is the correct conservative choice. The
  -- 'M' typeflag is otherwise interpreted purely as a multi-volume
  -- continuation cue in GNU tar's multi-volume workflow. The optional
  -- `Tar.list` assertion below confirms the entry is preserved through
  -- `list` with `typeflag = 0x4D` even though `extract` skips it,
  -- pinning the callers-routing-on-typeflag invariant.
  let mvData ← readFixture "tar/security/tar-multivol-skipped.tar"
  let mvPath ← writeFixtureTmp "tar-multivol-skipped.tar" mvData
  let mvExtract : System.FilePath :=
    "/tmp/lean-zip-fixture-tar-multivol-skipped-extract"
  if ← mvExtract.pathExists then
    let _ ← IO.Process.run { cmd := "rm", args := #["-rf", mvExtract.toString] }
  IO.FS.createDirAll mvExtract
  IO.FS.withFile mvPath .read fun h =>
    Tar.extract (IO.FS.Stream.ofHandle h) mvExtract
  let mvEntries ← mvExtract.readDir
  unless mvEntries.isEmpty do
    let names := mvEntries.map (·.fileName)
    throw (IO.userError s!"tar-multivol-skipped.tar: extract dir should be empty, got {names}")
  let mvListed ← IO.FS.withFile mvPath .read fun h =>
    Tar.list (IO.FS.Stream.ofHandle h)
  unless mvListed.size == 1 do
    throw (IO.userError s!"tar-multivol-skipped.tar: expected 1 entry from Tar.list, got {mvListed.size}")
  unless mvListed[0]!.typeflag == 0x4D do
    throw (IO.userError s!"tar-multivol-skipped.tar: expected Tar.list typeflag = 0x4D, got {mvListed[0]!.typeflag}")

  -- tar-sparse-skipped.tar: typeflag 'S' (GNU sparse file, 0x53). Policy:
  -- silent skip — no filesystem entry created, so the extract dir must
  -- remain empty. This pins the silent-skip policy's GNU sparse-file arm
  -- as the **third GNU-typeflag** sibling alongside
  -- tar-volumeheader-skipped.tar (typeflag 'V', 0x56) and
  -- tar-multivol-skipped.tar (typeflag 'M', 0x4D), extending the
  -- GNU-typeflag sub-ladder distinct from the POSIX UStar '0'–'7' numeric
  -- range covered by hardlink-outside.tar (typeflag '1'),
  -- tar-fifo-skipped.tar (typeflag '6'), tar-chardev-skipped.tar
  -- (typeflag '3'), tar-blockdev-skipped.tar (typeflag '4'), and
  -- tar-contiguous-skipped.tar (typeflag '7'); together the eight pin
  -- eight distinct typeflag values against the shared `else` fallback in
  -- `Tar.extract`. The strict-vs-lenient distinction is the
  -- security-relevant policy choice this fixture pins: a malicious
  -- archive could ship a 'S' entry with a crafted sparse map (the GNU
  -- sparse format itself has multiple parser-differential variants:
  -- 0.0, 0.1, 1.0) declaring zero-fill segments that overlap or exceed
  -- the entry's declared `size`, expecting a lenient extractor to
  -- allocate a large output file (zero-fill amplification) or
  -- miscompute the payload offset and corrupt subsequent entries —
  -- lean-zip's policy of never materialising 'S' entries (regardless of
  -- `path` / sparse map / declared `size` / actual payload) is the
  -- correct conservative choice. The 'S' typeflag is otherwise
  -- interpreted purely as a sparse-file reconstruction cue in GNU tar's
  -- sparse workflow. The optional `Tar.list` assertion below confirms
  -- the entry is preserved through `list` with `typeflag = 0x53` even
  -- though `extract` skips it, pinning the callers-routing-on-typeflag
  -- invariant.
  let spData ← readFixture "tar/security/tar-sparse-skipped.tar"
  let spPath ← writeFixtureTmp "tar-sparse-skipped.tar" spData
  let spExtract : System.FilePath :=
    "/tmp/lean-zip-fixture-tar-sparse-skipped-extract"
  if ← spExtract.pathExists then
    let _ ← IO.Process.run { cmd := "rm", args := #["-rf", spExtract.toString] }
  IO.FS.createDirAll spExtract
  IO.FS.withFile spPath .read fun h =>
    Tar.extract (IO.FS.Stream.ofHandle h) spExtract
  let spEntries ← spExtract.readDir
  unless spEntries.isEmpty do
    let names := spEntries.map (·.fileName)
    throw (IO.userError s!"tar-sparse-skipped.tar: extract dir should be empty, got {names}")
  let spListed ← IO.FS.withFile spPath .read fun h =>
    Tar.list (IO.FS.Stream.ofHandle h)
  unless spListed.size == 1 do
    throw (IO.userError s!"tar-sparse-skipped.tar: expected 1 entry from Tar.list, got {spListed.size}")
  unless spListed[0]!.typeflag == 0x53 do
    throw (IO.userError s!"tar-sparse-skipped.tar: expected Tar.list typeflag = 0x53, got {spListed[0]!.typeflag}")

  -- tar-incremental-skipped.tar: typeflag 'D' (GNU directory-dump for
  -- incremental backups, 0x44). Policy: silent skip — no filesystem
  -- entry created, so the extract dir must remain empty. This pins the
  -- silent-skip policy's GNU incremental-backup arm as the **fourth
  -- GNU-typeflag** sibling alongside tar-volumeheader-skipped.tar
  -- (typeflag 'V', 0x56), tar-multivol-skipped.tar (typeflag 'M', 0x4D),
  -- and tar-sparse-skipped.tar (typeflag 'S', 0x53), extending the
  -- GNU-typeflag sub-ladder distinct from the POSIX UStar '0'–'7'
  -- numeric range covered by hardlink-outside.tar (typeflag '1'),
  -- tar-fifo-skipped.tar (typeflag '6'), tar-chardev-skipped.tar
  -- (typeflag '3'), tar-blockdev-skipped.tar (typeflag '4'), and
  -- tar-contiguous-skipped.tar (typeflag '7'); together the nine pin
  -- nine distinct typeflag values against the shared `else` fallback
  -- in `Tar.extract`. The strict-vs-lenient distinction is the
  -- security-relevant policy choice this fixture pins: a malicious
  -- archive could ship a 'D' entry with a crafted directory-listing
  -- payload that an incremental-aware extractor would interpret as
  -- instructions to delete files outside `outDir` (the GNU incremental
  -- format allows the listing to mark files for *removal* during
  -- restore), expecting a lenient extractor to honour those removal
  -- cues — lean-zip's policy of never materialising 'D' entries (and
  -- never interpreting the listing payload at all) is the correct
  -- conservative choice. The 'D' typeflag is otherwise interpreted
  -- purely as an incremental-backup directory-dump cue in GNU tar's
  -- incremental workflow. The optional `Tar.list` assertion below
  -- confirms the entry is preserved through `list` with `typeflag =
  -- 0x44` even though `extract` skips it, pinning the
  -- callers-routing-on-typeflag invariant.
  let inData ← readFixture "tar/security/tar-incremental-skipped.tar"
  let inPath ← writeFixtureTmp "tar-incremental-skipped.tar" inData
  let inExtract : System.FilePath :=
    "/tmp/lean-zip-fixture-tar-incremental-skipped-extract"
  if ← inExtract.pathExists then
    let _ ← IO.Process.run { cmd := "rm", args := #["-rf", inExtract.toString] }
  IO.FS.createDirAll inExtract
  IO.FS.withFile inPath .read fun h =>
    Tar.extract (IO.FS.Stream.ofHandle h) inExtract
  let inEntries ← inExtract.readDir
  unless inEntries.isEmpty do
    let names := inEntries.map (·.fileName)
    throw (IO.userError s!"tar-incremental-skipped.tar: extract dir should be empty, got {names}")
  let inListed ← IO.FS.withFile inPath .read fun h =>
    Tar.list (IO.FS.Stream.ofHandle h)
  unless inListed.size == 1 do
    throw (IO.userError s!"tar-incremental-skipped.tar: expected 1 entry from Tar.list, got {inListed.size}")
  unless inListed[0]!.typeflag == 0x44 do
    throw (IO.userError s!"tar-incremental-skipped.tar: expected Tar.list typeflag = 0x44, got {inListed[0]!.typeflag}")

  -- tar-longnames-skipped.tar: typeflag 'N' (GNU LF_NAMES old-long-name
  -- extension, 0x4E). Policy: silent skip — no filesystem entry created,
  -- so the extract dir must remain empty. This pins the silent-skip
  -- policy's GNU long-names-old arm as the **fifth GNU-typeflag**
  -- sibling alongside tar-volumeheader-skipped.tar (typeflag 'V', 0x56),
  -- tar-multivol-skipped.tar (typeflag 'M', 0x4D),
  -- tar-sparse-skipped.tar (typeflag 'S', 0x53), and
  -- tar-incremental-skipped.tar (typeflag 'D', 0x44), extending the
  -- GNU-typeflag sub-ladder distinct from the POSIX UStar '0'–'7'
  -- numeric range covered by hardlink-outside.tar (typeflag '1'),
  -- tar-fifo-skipped.tar (typeflag '6'), tar-chardev-skipped.tar
  -- (typeflag '3'), tar-blockdev-skipped.tar (typeflag '4'), and
  -- tar-contiguous-skipped.tar (typeflag '7'); together the ten pin
  -- ten distinct typeflag values against the shared `else` fallback
  -- in `Tar.extract`. The strict-vs-lenient distinction is the
  -- security-relevant policy choice this fixture pins: 'N' is the
  -- deprecated precursor to the modern 'L'/'K' long-name encoding —
  -- a malicious archive could ship an 'N' entry whose payload encodes
  -- a list of filenames containing `../etc/passwd` or absolute paths,
  -- expecting a lenient extractor to apply those names to the next
  -- regular-file entry (parser-differential archive-slip via deprecated
  -- long-name rewriting) — lean-zip's policy of *never* materialising
  -- 'N' entries and never interpreting the payload as a name-rewrite
  -- directive is the correct conservative choice. `forEntries`
  -- recognises only the modern 'L'/'K' (and PAX 'x'/'g') long-name
  -- typeflags; 'N' is *not* aliased to 'L'. The optional `Tar.list`
  -- assertion below confirms the entry is preserved through `list`
  -- with `typeflag = 0x4E` even though `extract` skips it, pinning
  -- the callers-routing-on-typeflag invariant.
  let lnNamesData ← readFixture "tar/security/tar-longnames-skipped.tar"
  let lnNamesPath ← writeFixtureTmp "tar-longnames-skipped.tar" lnNamesData
  let lnNamesExtract : System.FilePath :=
    "/tmp/lean-zip-fixture-tar-longnames-skipped-extract"
  if ← lnNamesExtract.pathExists then
    let _ ← IO.Process.run { cmd := "rm", args := #["-rf", lnNamesExtract.toString] }
  IO.FS.createDirAll lnNamesExtract
  IO.FS.withFile lnNamesPath .read fun h =>
    Tar.extract (IO.FS.Stream.ofHandle h) lnNamesExtract
  let lnNamesEntries ← lnNamesExtract.readDir
  unless lnNamesEntries.isEmpty do
    let names := lnNamesEntries.map (·.fileName)
    throw (IO.userError s!"tar-longnames-skipped.tar: extract dir should be empty, got {names}")
  let lnNamesListed ← IO.FS.withFile lnNamesPath .read fun h =>
    Tar.list (IO.FS.Stream.ofHandle h)
  unless lnNamesListed.size == 1 do
    throw (IO.userError s!"tar-longnames-skipped.tar: expected 1 entry from Tar.list, got {lnNamesListed.size}")
  unless lnNamesListed[0]!.typeflag == 0x4E do
    throw (IO.userError s!"tar-longnames-skipped.tar: expected Tar.list typeflag = 0x4E, got {lnNamesListed[0]!.typeflag}")

  -- tar-mixed-skipped.tar: three-entry archive (regular before.txt →
  -- typeflag '6' FIFO silent-skip → regular after.txt). Sibling-class
  -- fixture (not an eleventh per-typeflag arm) covering the post-skip
  -- *extract-continuation* invariant that none of the ten single-entry
  -- per-typeflag silent-skip siblings exercises: that the `else` branch's
  -- `skipEntryData input e.size` call leaves the input stream positioned
  -- exactly at the next 512-byte block boundary so a subsequent
  -- regular-file entry still extracts cleanly. A regression that broke
  -- `skipEntryData` by, say, advancing the stream by `e.size` bytes
  -- without padding to a 512-byte block boundary would not fire any of
  -- the existing ten fixtures (each ends at EOF after the skipped entry)
  -- but would silently corrupt the offset of any following entry — this
  -- arm asserts both content and count: extraction yields *exactly* two
  -- files (`before.txt` and `after.txt`) with the declared payloads.
  let mixedData ← readFixture "tar/security/tar-mixed-skipped.tar"
  let mixedPath ← writeFixtureTmp "tar-mixed-skipped.tar" mixedData
  let mixedExtract : System.FilePath :=
    "/tmp/lean-zip-fixture-tar-mixed-skipped-extract"
  if ← mixedExtract.pathExists then
    let _ ← IO.Process.run { cmd := "rm", args := #["-rf", mixedExtract.toString] }
  IO.FS.createDirAll mixedExtract
  IO.FS.withFile mixedPath .read fun h =>
    Tar.extract (IO.FS.Stream.ofHandle h) mixedExtract
  let mixedBefore ← IO.FS.readFile (mixedExtract / "before.txt")
  unless mixedBefore == "BEFORE\n" do
    throw (IO.userError s!"tar-mixed-skipped.tar: before.txt content mismatch: {repr mixedBefore}")
  let mixedAfter ← IO.FS.readFile (mixedExtract / "after.txt")
  unless mixedAfter == "AFTER\n" do
    throw (IO.userError s!"tar-mixed-skipped.tar: after.txt content mismatch: {repr mixedAfter}")
  let mixedEntries ← mixedExtract.readDir
  unless mixedEntries.size == 2 do
    let names := mixedEntries.map (·.fileName)
    throw (IO.userError s!"tar-mixed-skipped.tar: expected exactly 2 files in extract dir, got {mixedEntries.size}: {names}")

  -- tar-skipped-payload.tar: three-entry archive (regular before.txt →
  -- typeflag '6' FIFO with non-zero size 512 silent-skip → regular
  -- after.txt). Second sibling-class fixture alongside
  -- `tar-mixed-skipped.tar`, but with a non-zero declared payload on
  -- the silent-skipped middle entry — pinning the *data-advance
  -- arithmetic* of the silent-skip `else` branch's `skipEntryData
  -- input e.size` call for non-zero `e.size`. The eleven existing
  -- silent-skip fixtures (the ten per-typeflag arms and
  -- `tar-mixed-skipped.tar`) all use `size == 0` for the skipped
  -- entry, so `skipEntryData input 0` is a no-op except for the
  -- trailing 512-byte alignment after the header. A regression that
  -- broke `skipEntryData` by ignoring `e.size` and advancing only by
  -- the header padding would leave the stream positioned at the start
  -- of the FIFO payload; the next `readExact` would consume 512 zero
  -- bytes, `parseHeader` would interpret the zero block as
  -- end-of-archive, and `forEntries` would terminate without
  -- extracting `after.txt` — caught by the extract-dir size == 2
  -- assertion below.
  let skippedPayloadData ← readFixture "tar/security/tar-skipped-payload.tar"
  let skippedPayloadPath ← writeFixtureTmp "tar-skipped-payload.tar" skippedPayloadData
  let skippedPayloadExtract : System.FilePath :=
    "/tmp/lean-zip-fixture-tar-skipped-payload-extract"
  if ← skippedPayloadExtract.pathExists then
    let _ ← IO.Process.run { cmd := "rm", args := #["-rf", skippedPayloadExtract.toString] }
  IO.FS.createDirAll skippedPayloadExtract
  IO.FS.withFile skippedPayloadPath .read fun h =>
    Tar.extract (IO.FS.Stream.ofHandle h) skippedPayloadExtract
  let skippedPayloadBefore ← IO.FS.readFile (skippedPayloadExtract / "before.txt")
  unless skippedPayloadBefore == "BEFORE\n" do
    throw (IO.userError s!"tar-skipped-payload.tar: before.txt content mismatch: {repr skippedPayloadBefore}")
  let skippedPayloadAfter ← IO.FS.readFile (skippedPayloadExtract / "after.txt")
  unless skippedPayloadAfter == "AFTER\n" do
    throw (IO.userError s!"tar-skipped-payload.tar: after.txt content mismatch: {repr skippedPayloadAfter}")
  let skippedPayloadEntries ← skippedPayloadExtract.readDir
  unless skippedPayloadEntries.size == 2 do
    let names := skippedPayloadEntries.map (·.fileName)
    throw (IO.userError s!"tar-skipped-payload.tar: expected exactly 2 files in extract dir, got {skippedPayloadEntries.size}: {names}")

  -- tar-skipped-padded.tar: three-entry archive (regular before.txt →
  -- typeflag '6' FIFO with non-multiple-of-512 size 100 + 412-byte zero
  -- padding silent-skip → regular after.txt). Third sibling-class fixture
  -- alongside `tar-mixed-skipped.tar` and `tar-skipped-payload.tar`, but
  -- with a *non-multiple-of-512* declared payload on the silent-skipped
  -- middle entry — pinning the *padding round-up arithmetic* of the
  -- silent-skip `else` branch's `skipEntryData input e.size` call's
  -- `paddingFor` summand for `size mod 512 ≠ 0`. The twelve existing
  -- silent-skip fixtures (the ten per-typeflag arms +
  -- `tar-mixed-skipped.tar` (size 0) + `tar-skipped-payload.tar` (size
  -- 512, multiple of 512)) all use sizes for which `paddingFor` evaluates
  -- to `0`, so a regression that broke `paddingFor` by, say, returning
  -- `0` unconditionally would not fire any of the twelve preceding
  -- fixtures but would silently corrupt the offset of any entry following
  -- a non-multiple-of-512 silent-skipped payload — `skipEntryData` would
  -- consume only the 100 declared bytes without the 412-byte padding,
  -- leaving the stream positioned 412 bytes inside the `after.txt`
  -- header, and the subsequent `forEntries` `readExact 512` would parse a
  -- header straddling the `after.txt` header / payload boundary with a
  -- bogus checksum. Caught by the extract-dir size == 2 assertion below.
  let skippedPaddedData ← readFixture "tar/security/tar-skipped-padded.tar"
  let skippedPaddedPath ← writeFixtureTmp "tar-skipped-padded.tar" skippedPaddedData
  let skippedPaddedExtract : System.FilePath :=
    "/tmp/lean-zip-fixture-tar-skipped-padded-extract"
  if ← skippedPaddedExtract.pathExists then
    let _ ← IO.Process.run { cmd := "rm", args := #["-rf", skippedPaddedExtract.toString] }
  IO.FS.createDirAll skippedPaddedExtract
  IO.FS.withFile skippedPaddedPath .read fun h =>
    Tar.extract (IO.FS.Stream.ofHandle h) skippedPaddedExtract
  let skippedPaddedBefore ← IO.FS.readFile (skippedPaddedExtract / "before.txt")
  unless skippedPaddedBefore == "BEFORE\n" do
    throw (IO.userError s!"tar-skipped-padded.tar: before.txt content mismatch: {repr skippedPaddedBefore}")
  let skippedPaddedAfter ← IO.FS.readFile (skippedPaddedExtract / "after.txt")
  unless skippedPaddedAfter == "AFTER\n" do
    throw (IO.userError s!"tar-skipped-padded.tar: after.txt content mismatch: {repr skippedPaddedAfter}")
  let skippedPaddedEntries ← skippedPaddedExtract.readDir
  unless skippedPaddedEntries.size == 2 do
    let names := skippedPaddedEntries.map (·.fileName)
    throw (IO.userError s!"tar-skipped-padded.tar: expected exactly 2 files in extract dir, got {skippedPaddedEntries.size}: {names}")

  -- Clean up temp files
  for f in #["go-ustar.tar", "go-gnu.tar", "go-pax.tar", "system-tar.tar",
             "gnu-longname.tar", "truncated.tar", "bad-checksum.tar", "no-magic.tar",
             "pax-oversized-length.tar", "pax-truncated-record.tar",
             "pax-invalid-utf8-key.tar", "pax-invalid-utf8-value.tar",
             "pax-inconsistent-length.tar",
             "pax-linkpath-nul-in-value.tar",
             "pax-path-nul-in-value.tar",
             "pax-nul-in-key.tar",
             "pax-duplicate-path.tar",
             "gnu-longname-truncated.tar", "gnu-longlink-truncated.tar",
             "gnu-longname-no-terminator.tar", "gnu-longname-invalid-utf8.tar",
             "gnu-longname-nul-in-name.tar", "gnu-longlink-nul-in-link.tar",
             "ustar-name-nul-in-name.tar",
             "ustar-linkname-nul-in-name.tar",
             "ustar-prefix-nul-in-name.tar",
             "ustar-uname-nul-in-uname.tar",
             "ustar-gname-nul-in-gname.tar",
             "gnu-longname-oversized-size.tar", "pax-extended-oversized-size.tar",
             "tar-slip.tar", "tar-absolute.tar", "symlink-slip.tar",
             "backslash-slip.tar", "symlink-absolute.tar",
             "hardlink-outside.tar", "tar-fifo-skipped.tar",
             "tar-chardev-skipped.tar", "tar-blockdev-skipped.tar",
             "tar-contiguous-skipped.tar",
             "tar-volumeheader-skipped.tar",
             "tar-multivol-skipped.tar",
             "tar-sparse-skipped.tar",
             "tar-incremental-skipped.tar",
             "tar-longnames-skipped.tar",
             "tar-mixed-skipped.tar",
             "tar-skipped-payload.tar",
             "tar-skipped-padded.tar"] do
    let _ ← IO.Process.run { cmd := "rm", args := #["-f", s!"/tmp/lean-zip-fixture-{f}"] }
  for d in #["/tmp/lean-zip-fixture-truncated-tar-extract", "/tmp/lean-zip-fixture-tar-slip-extract",
             "/tmp/lean-zip-fixture-tar-abs-extract", "/tmp/lean-zip-fixture-symlink-slip-extract",
             "/tmp/lean-zip-fixture-backslash-slip-extract",
             "/tmp/lean-zip-fixture-symlink-abs-extract",
             "/tmp/lean-zip-fixture-hardlink-outside-extract",
             "/tmp/lean-zip-fixture-tar-fifo-skipped-extract",
             "/tmp/lean-zip-fixture-tar-chardev-skipped-extract",
             "/tmp/lean-zip-fixture-tar-blockdev-skipped-extract",
             "/tmp/lean-zip-fixture-tar-contiguous-skipped-extract",
             "/tmp/lean-zip-fixture-tar-volumeheader-skipped-extract",
             "/tmp/lean-zip-fixture-tar-multivol-skipped-extract",
             "/tmp/lean-zip-fixture-tar-sparse-skipped-extract",
             "/tmp/lean-zip-fixture-tar-incremental-skipped-extract",
             "/tmp/lean-zip-fixture-tar-longnames-skipped-extract",
             "/tmp/lean-zip-fixture-tar-mixed-skipped-extract",
             "/tmp/lean-zip-fixture-tar-skipped-payload-extract",
             "/tmp/lean-zip-fixture-tar-skipped-padded-extract"] do
    let _ ← IO.Process.run { cmd := "rm", args := #["-rf", d] }
  IO.println "TAR fixture tests: OK"
