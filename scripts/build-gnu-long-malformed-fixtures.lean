import Zip

/-! Build malformed GNU long-name / long-link regression fixtures
    for Track E Priority 1.

Each fixture is a minimal UStar tar archive whose first entry is a GNU
long-name pseudo-entry (typeflag `'L'`) or a GNU long-link pseudo-entry
(typeflag `'K'`). Three of the four fixtures are followed by a
zero-length regular-file entry that should inherit the long name (or
long link) from the preceding pseudo-entry.

Run once at development time:

    lake env lean --run scripts/build-gnu-long-malformed-fixtures.lean

Output (byte-deterministic):
- testdata/tar/malformed/gnu-longname-truncated.tar
- testdata/tar/malformed/gnu-longname-no-terminator.tar
- testdata/tar/malformed/gnu-longname-invalid-utf8.tar
- testdata/tar/malformed/gnu-longlink-truncated.tar
- testdata/tar/malformed/gnu-longname-nul-in-name.tar
-/

/-- Build the 512-byte UStar header for a GNU long-name / long-link
    pseudo-entry.  GNU tar conventionally uses `././@LongLink` as the
    on-disk name; we follow that convention so the fixture is recognisable
    by a hex dump. -/
def buildLongPseudoHeader (typeflag : UInt8) (payloadSize : UInt64) : IO ByteArray :=
  Tar.buildHeader
    { path     := "././@LongLink"
      size     := payloadSize
      mode     := 0o644
      typeflag := typeflag }

/-- Build the 512-byte UStar header for the trailing regular-file entry
    that consumes the preceding GNU long-name / long-link override.
    `size := 0` so the entry has no data block. -/
def buildTrailingRegularHeader : IO ByteArray :=
  Tar.buildHeader
    { path     := "next.txt"
      size     := 0
      mode     := 0o644
      typeflag := Tar.typeRegular }

/-- Fixture 1: gnu-longname-truncated.tar
    Long-name header declares `size = 200` but only 100 bytes of payload
    follow before EOF.  `readEntryData` should throw "tar: unexpected end
    of archive reading entry data". -/
def buildGnuLongnameTruncated : IO ByteArray := do
  let hdr ← buildLongPseudoHeader Tar.typeGnuLongName 200
  -- Only 100 bytes of payload (all 'a'), then archive EOF.
  let truncPayload : ByteArray :=
    ByteArray.mk (Array.replicate 100 (0x61 : UInt8))   -- 'a' = 0x61
  return hdr ++ truncPayload

/-- Fixture 2: gnu-longname-no-terminator.tar
    Long-name payload is exactly 100 bytes of `'a'` with NO trailing NUL.
    `stripTrailingNuls` returns all 100 bytes; `String.fromUTF8?` succeeds;
    the next entry's path is overridden to the 100-character string. -/
def buildGnuLongnameNoTerminator : IO ByteArray := do
  let payload : ByteArray :=
    ByteArray.mk (Array.replicate 100 (0x61 : UInt8))   -- 100 'a's, no NUL
  let lnHdr  ← buildLongPseudoHeader Tar.typeGnuLongName 100
  let lnPad  := Tar.paddingFor 100   -- 412 bytes
  let regHdr ← buildTrailingRegularHeader
  return lnHdr ++ payload ++ Binary.zeros lnPad ++ regHdr

/-- Fixture 3: gnu-longname-invalid-utf8.tar
    Long-name payload is `0xFF 0xFF 0xFF` followed by a single NUL
    (size = 4).  `stripTrailingNuls` yields three `0xFF` bytes;
    `String.fromUTF8?` returns `none`; `Binary.fromLatin1` produces a
    3-character string of U+00FF codepoints. -/
def buildGnuLongnameInvalidUtf8 : IO ByteArray := do
  let payload : ByteArray := ByteArray.mk #[0xFF, 0xFF, 0xFF, 0x00]
  let lnHdr  ← buildLongPseudoHeader Tar.typeGnuLongName 4
  let lnPad  := Tar.paddingFor 4   -- 508 bytes
  let regHdr ← buildTrailingRegularHeader
  return lnHdr ++ payload ++ Binary.zeros lnPad ++ regHdr

/-- Fixture 4: gnu-longlink-truncated.tar
    Same geometry as fixture 1 but with typeflag `'K'` (long link).
    Exercises the structurally-identical long-link arm of `forEntries`. -/
def buildGnuLonglinkTruncated : IO ByteArray := do
  let hdr ← buildLongPseudoHeader Tar.typeGnuLongLink 200
  let truncPayload : ByteArray :=
    ByteArray.mk (Array.replicate 100 (0x61 : UInt8))
  return hdr ++ truncPayload

/-- Fixture 5: gnu-longname-nul-in-name.tar
    Long-name payload is `"evil.txt\x00.tar"` (13 bytes, NUL in middle)
    followed by a single NUL terminator (size = 14). `stripTrailingNuls`
    strips the terminator; the interior NUL remains. The new NUL-byte
    guard at `forEntries` must reject the payload before
    `String.fromUTF8?` / `Binary.fromLatin1` runs — POSIX `open` would
    truncate `"evil.txt\x00.tar"` to `"evil.txt"` on extract while
    `Tar.list` callers see the full NUL-embedded string (classic
    parser-differential / filesystem-truncation smuggle).

    A trailing regular-file entry (`size := 0`, `path := "_"`) is
    appended so the fixture exercises the override application path
    fully — but the guard fires on the long-name pseudo-entry itself,
    so the trailing entry is only reached by the no-guard regression
    baseline. -/
def buildGnuLongnameNulInName : IO ByteArray := do
  -- 13 bytes: "evil.txt" (8) ++ 0x00 ++ ".tar" (4); then 0x00 terminator.
  let payload : ByteArray := ByteArray.mk #[
    0x65, 0x76, 0x69, 0x6C, 0x2E, 0x74, 0x78, 0x74,   -- "evil.txt"
    0x00,                                             -- embedded NUL
    0x2E, 0x74, 0x61, 0x72,                           -- ".tar"
    0x00]                                             -- trailing NUL
  let lnHdr  ← buildLongPseudoHeader Tar.typeGnuLongName 14
  let lnPad  := Tar.paddingFor 14   -- 498 bytes
  let regHdr ← Tar.buildHeader
    { path     := "_"
      size     := 0
      mode     := 0o644
      typeflag := Tar.typeRegular }
  return lnHdr ++ payload ++ Binary.zeros lnPad ++ regHdr

def main : IO Unit := do
  let outDir : System.FilePath := "testdata/tar/malformed"
  IO.FS.writeBinFile (outDir / "gnu-longname-truncated.tar")
    (← buildGnuLongnameTruncated)
  IO.FS.writeBinFile (outDir / "gnu-longname-no-terminator.tar")
    (← buildGnuLongnameNoTerminator)
  IO.FS.writeBinFile (outDir / "gnu-longname-invalid-utf8.tar")
    (← buildGnuLongnameInvalidUtf8)
  IO.FS.writeBinFile (outDir / "gnu-longlink-truncated.tar")
    (← buildGnuLonglinkTruncated)
  IO.FS.writeBinFile (outDir / "gnu-longname-nul-in-name.tar")
    (← buildGnuLongnameNulInName)
  IO.println "Built 5 malformed GNU long-name/long-link fixtures under testdata/tar/malformed/."
