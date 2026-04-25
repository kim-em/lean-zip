import Zip

/-! Build malformed UStar header regression fixtures for Track E.

Each fixture is a minimal UStar tar archive whose first entry is a
regular-file header carrying a smuggled NUL byte in one of the four
guarded UStar string fields (`name`, `linkname`, `prefix`, `uname`).
The `Tar.parseHeader` `hasInteriorNul` guard at `Zip/Tar.lean` rejects
on the raw 512-byte block before any `Binary.readString` call, so none
of the four fields can leak its NUL-truncated form into `Tar.list` /
`Tar.extract` callers. The four fixtures together pin the per-slot
guards (`name` / `linkname` / `prefix` / `uname`) — closing the
filesystem-reaching 3-slot family and extending coverage to the 4th
(`uname`) defense-in-depth slot. The `gname` slot is the final
(5-slot) sibling deferred to a follow-up planner cycle.

Run once at development time:

    lake env lean --run scripts/build-ustar-malformed-fixtures.lean

Output (byte-deterministic):
- testdata/tar/malformed/ustar-name-nul-in-name.tar
- testdata/tar/malformed/ustar-linkname-nul-in-name.tar
- testdata/tar/malformed/ustar-prefix-nul-in-name.tar
- testdata/tar/malformed/ustar-uname-nul-in-uname.tar
-/

/-- Fixture: ustar-name-nul-in-name.tar
    UStar header for a zero-byte regular file whose `name` field at
    offset 0 carries `"evil.txt\x00.tar"` (13 bytes: an embedded NUL
    after `"evil.txt"`, then `".tar"` smuggled past the NUL terminator).
    `Tar.buildHeader` routes through `Binary.writeString`, which copies
    each UTF-8 byte of the path verbatim — including the U+0000
    codepoint — and pads the remaining 87 bytes with NUL. The new
    `Tar.parseHeader` guard rejects on the raw block before
    `Binary.readString` would otherwise truncate the payload to
    `"evil.txt"` (the parser-differential / filesystem-truncation
    smuggle vector). Two trailing zero blocks (1024 B) form a
    well-formed end-of-archive that strict peer parsers accept; the
    guard fires during header parse, so the trailing blocks are only
    exercised by the no-guard regression baseline. -/
def buildUstarNameNulInName : IO ByteArray := do
  let hdr ← Tar.buildHeader
    { path     := "evil.txt\x00.tar"
      size     := 0
      mode     := 0o644
      typeflag := Tar.typeRegular }
  let endOfArchive := Binary.zeros 1024
  return hdr ++ endOfArchive

/-- Fixture: ustar-linkname-nul-in-name.tar
    UStar header for a zero-byte regular file whose `linkname` field
    at offset 157 carries `"evil.lnk\x00.tar"` (13 bytes: an embedded
    NUL after `"evil.lnk"`, then `".tar"` smuggled past the NUL
    terminator). `Tar.buildHeader` routes through `Binary.writeString`,
    which copies each UTF-8 byte verbatim — including U+0000 — and
    pads the remaining 87 bytes with NUL. The `Tar.parseHeader` guard
    at line 517 rejects on the raw block before `Binary.readString`
    would otherwise truncate the linkname to `"evil.lnk"`. The `path`
    is `"safe"` so the `name`-arm guard at line 515 cannot fire first
    — attribution pins on the `linkname` arm specifically. Two
    trailing zero blocks (1024 B) form a well-formed end-of-archive
    matching the `name`-slot sibling fixture. -/
def buildUstarLinknameNulInName : IO ByteArray := do
  let hdr ← Tar.buildHeader
    { path     := "safe"
      linkname := "evil.lnk\x00.tar"
      size     := 0
      mode     := 0o644
      typeflag := Tar.typeRegular }
  let endOfArchive := Binary.zeros 1024
  return hdr ++ endOfArchive

/-- Fixture: ustar-prefix-nul-in-name.tar
    UStar header for a zero-byte regular file whose `prefix` field at
    offset 345 carries `"badpfx\x00bad"` (10 bytes: an embedded NUL
    after `"badpfx"`, then `"bad"` smuggled past the NUL terminator).
    The `pathOverride := some ("badpfx\x00bad", "name.txt")` argument
    routes those bytes directly to `writeField hdr hdrPrefix.1
    (Binary.writeString "badpfx\x00bad" hdrPrefix.2)` at
    [Zip/Tar.lean:389], bypassing the auto-`splitPath` logic.
    `Binary.writeString` copies UTF-8 bytes verbatim — including
    U+0000 — and pads the remaining 145 bytes with NUL. The
    `Tar.parseHeader` guard at line 519 rejects on the raw block
    before `Binary.readString` would otherwise truncate the prefix
    to `"badpfx"`, after which `pfx ++ "/" ++ name` at
    [Zip/Tar.lean:522] would yield `"badpfx/name.txt"` (parser
    sees short form) while POSIX `open(2)` truncates at the same
    NUL on `Tar.extract`. The `name` slot carries the clean
    `"name.txt"` so the `name`-arm guard at line 515 cannot fire
    first — attribution pins on the `prefix` arm specifically.
    Two trailing zero blocks (1024 B) match the sibling fixtures'
    well-formed end-of-archive. -/
def buildUstarPrefixNulInName : IO ByteArray := do
  let hdr ← Tar.buildHeader
    (pathOverride := some ("badpfx\x00bad", "name.txt"))
    { path     := "name.txt"
      size     := 0
      mode     := 0o644
      typeflag := Tar.typeRegular }
  let endOfArchive := Binary.zeros 1024
  return hdr ++ endOfArchive

/-- Fixture: ustar-uname-nul-in-uname.tar
    UStar header for a zero-byte regular file whose `uname` field at
    offset 265 carries `"trusted\x00rogue"` (12 bytes: an embedded NUL
    after `"trusted"`, then `"rogue"` smuggled past the NUL terminator).
    `Tar.buildHeader` routes through `Binary.writeString`, which copies
    each UTF-8 byte of `entry.uname` verbatim — including U+0000 — and
    pads the remaining 20 bytes with NUL. The new `Tar.parseHeader`
    guard rejects on the raw block before `Binary.readString` would
    otherwise truncate the payload to `"trusted"` (the parser-
    differential smuggle vector for any caller routing on
    `entry.uname` for a trust decision). The `path` is `"safe"` so
    the `name`-arm guard at the start of the four-slot chain cannot
    fire first — attribution pins on the `uname` arm specifically.
    The `linkname` and `prefix` slots are clean for the same reason.
    Two trailing zero blocks (1024 B) form a well-formed end-of-archive
    matching the per-slot sibling fixtures. Per-slot family extension:
    the closed 3-slot filesystem-reaching family
    (`ustar-name-nul-in-name.tar` / `ustar-linkname-nul-in-name.tar` /
    `ustar-prefix-nul-in-name.tar`) covers offsets 0 / 157 / 345; this
    fixture covers offset 265 / 32 B (the 4th slot). The `gname` slot
    at offset 297 / 32 B is the final (5-slot) sibling deferred to a
    follow-up planner cycle. -/
def buildUstarUnameNulInUname : IO ByteArray := do
  let hdr ← Tar.buildHeader
    { path     := "safe"
      uname    := "trusted\x00rogue"
      size     := 0
      mode     := 0o644
      typeflag := Tar.typeRegular }
  let endOfArchive := Binary.zeros 1024
  return hdr ++ endOfArchive

def main : IO Unit := do
  let outDir : System.FilePath := "testdata/tar/malformed"
  IO.FS.writeBinFile (outDir / "ustar-name-nul-in-name.tar")
    (← buildUstarNameNulInName)
  IO.FS.writeBinFile (outDir / "ustar-linkname-nul-in-name.tar")
    (← buildUstarLinknameNulInName)
  IO.FS.writeBinFile (outDir / "ustar-prefix-nul-in-name.tar")
    (← buildUstarPrefixNulInName)
  IO.FS.writeBinFile (outDir / "ustar-uname-nul-in-uname.tar")
    (← buildUstarUnameNulInUname)
  IO.println "Built 4 malformed UStar fixtures under testdata/tar/malformed/."
