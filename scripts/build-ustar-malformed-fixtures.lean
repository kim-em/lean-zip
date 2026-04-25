import Zip

/-! Build malformed UStar header regression fixtures for Track E.

Each fixture is a minimal UStar tar archive whose first entry is a
regular-file header carrying a smuggled NUL byte in one of the three
UStar string fields (`name`, `linkname`, `prefix`). The new
`Tar.parseHeader` `hasInteriorNul` guard at
`Zip/Tar.lean` rejects on the raw 512-byte block before any
`Binary.readString` call, so neither the name nor the linkname/prefix
NUL-truncation can leak into `Tar.list` / `Tar.extract` callers.

Run once at development time:

    lake env lean --run scripts/build-ustar-malformed-fixtures.lean

Output (byte-deterministic):
- testdata/tar/malformed/ustar-name-nul-in-name.tar
- testdata/tar/malformed/ustar-linkname-nul-in-name.tar
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

def main : IO Unit := do
  let outDir : System.FilePath := "testdata/tar/malformed"
  IO.FS.writeBinFile (outDir / "ustar-name-nul-in-name.tar")
    (← buildUstarNameNulInName)
  IO.FS.writeBinFile (outDir / "ustar-linkname-nul-in-name.tar")
    (← buildUstarLinknameNulInName)
  IO.println "Built 2 malformed UStar fixtures under testdata/tar/malformed/."
