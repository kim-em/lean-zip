import Zip

/-! Build malformed PAX regression fixtures for Track E Priority 1.

Each fixture is a minimal UStar tar archive whose first entry is a
PAX extended header (typeflag `'x'`) with a malformed PAX data block,
followed by one regular-file entry carrying `"hello\n"`.  The existing
`parsePaxRecords` guards in `Zip/Tar.lean` should silently skip the
malformed PAX block; the regular entry should still list successfully.

Run once at development time:

    lake env lean --run scripts/build-pax-malformed-fixtures.lean

Output (byte-deterministic):
- testdata/tar/malformed/pax-oversized-length.tar
- testdata/tar/malformed/pax-truncated-record.tar
- testdata/tar/malformed/pax-invalid-utf8-key.tar
- testdata/tar/malformed/pax-invalid-utf8-value.tar
- testdata/tar/malformed/pax-inconsistent-length.tar
- testdata/tar/malformed/pax-path-nul-in-value.tar
- testdata/tar/malformed/pax-duplicate-path.tar
-/

/-- Build a fixture whose PAX header carries `paxData` (verbatim),
    followed by a regular-file entry with path `hello.txt` and contents
    `"hello\n"`. No end-of-archive zero blocks (`parseHeader` / `readExact`
    already terminate on short read; matches the geometry of the existing
    2048-byte malformed fixtures). -/
def buildPaxMalformedFixture (paxData : ByteArray) (outPath : System.FilePath) : IO Unit := do
  let paxEntry : Tar.Entry :=
    { path     := "PaxHeader/hello.txt"
      size     := paxData.size.toUInt64
      mode     := 0o644
      typeflag := Tar.typePaxExtended }
  let paxHdr ← Tar.buildHeader paxEntry
  let paxPad := Tar.paddingFor paxData.size.toUInt64
  let regularData : ByteArray := "hello\n".toUTF8
  let regularEntry : Tar.Entry :=
    { path     := "hello.txt"
      size     := regularData.size.toUInt64
      mode     := 0o644
      typeflag := Tar.typeRegular }
  let regularHdr ← Tar.buildHeader regularEntry
  let regularPad := Tar.paddingFor regularData.size.toUInt64
  let out :=
    paxHdr ++ paxData ++ Binary.zeros paxPad
      ++ regularHdr ++ regularData ++ Binary.zeros regularPad
  IO.FS.writeBinFile outPath out

/-- PAX data with a 29-digit decimal length prefix; exceeds the
    `digitCount > 20` guard in `parsePaxRecords`, so the outer loop
    breaks without pushing any record. -/
def fixtureOversizedLength : ByteArray :=
  "12345678901234567890123456789 path=foo\n".toUTF8

/-- PAX data that declares `length = 100` but the tar-reported record
    size is only 50 bytes, so `recordEnd > data.size` fires and the
    record is skipped. -/
def fixtureTruncatedRecord : ByteArray := Id.run do
  let mut bytes : ByteArray := "100 path=foo\n".toUTF8
  while bytes.size < 50 do
    bytes := bytes.push 0
  return bytes

/-- PAX record whose key is the lone UTF-8 continuation byte `0xC3`;
    `String.fromUTF8?` returns `none` so the record is dropped.
    Record = `'6' ' ' 0xC3 '=' 'v' '\n'` (6 bytes, consistent length). -/
def fixtureInvalidUtf8Key : ByteArray :=
  "6 ".toUTF8 ++ ByteArray.mk #[0xC3] ++ "=v\n".toUTF8

/-- PAX record whose value encodes a UTF-16 surrogate
    (`0xED 0xA0 0x80`, i.e. U+D800 — invalid in UTF-8 per RFC 3629).
    Record = `'8' ' ' 'k' '=' 0xED 0xA0 0x80 '\n'` (8 bytes). -/
def fixtureInvalidUtf8Value : ByteArray :=
  "8 k=".toUTF8 ++ ByteArray.mk #[0xED, 0xA0, 0x80] ++ "\n".toUTF8

/-- PAX record declaring `length = 10` without a `=` separator within
    those 10 bytes (`10 abcdef\n`). `parsePaxRecords` finds `eqPos ==
    recordEnd` and skips the record. -/
def fixtureInconsistentLength : ByteArray :=
  "10 abcdef\n".toUTF8

/-- PAX record `"14 path=a\x00b/c\n"` — a `path` override whose value
    carries an embedded NUL byte. `String.fromUTF8?` accepts U+0000 as
    valid UTF-8, so without the NUL guard on `keyBytes` / `valueBytes`
    at [Zip/Tar.lean:122] the override would reach `applyPaxOverrides`
    and set `entry.path := "a\x00b/c"` — a filesystem-truncation smuggle
    that POSIX `open` reduces to `a`. With the guard, the record is
    silently dropped (matching the existing invalid-UTF-8 precedent)
    and the follow-on regular-file entry keeps its declared name.
    Record size 14 = 2 digit-prefix + 1 space + 4 `"path"` + 1 `"="`
    + 5 `"a\x00b/c"` + 1 newline. -/
def fixturePathNulInValue : ByteArray :=
  "14 path=a".toUTF8 ++ ByteArray.mk #[0x00] ++ "b/c\n".toUTF8

/-- PAX data with two well-formed `path=` records — a parser-differential
    smuggling vector where a lenient (first-wins) reader takes
    `"safe.txt"` while a strict (last-wins, APPNOTE-silent on order)
    reader takes `"../etc/passwd"`. `parsePaxRecords` must reject at
    parse time with an error containing `"duplicate"` so that neither
    listing nor extract callers see a divergence from any peer parser.
    Record 1: `"17 path=safe.txt\n"` —
      2 (digits `"17"`) + 1 (space) + 4 (`"path"`) + 1 (`"="`)
      + 8 (`"safe.txt"`) + 1 (newline) = 17 ✓.
    Record 2: `"22 path=../etc/passwd\n"` —
      2 (digits `"22"`) + 1 (space) + 4 (`"path"`) + 1 (`"="`)
      + 13 (`"../etc/passwd"`) + 1 (newline) = 22 ✓. -/
def fixtureDuplicatePath : ByteArray :=
  "17 path=safe.txt\n22 path=../etc/passwd\n".toUTF8

def main : IO Unit := do
  let outDir : System.FilePath := "testdata/tar/malformed"
  buildPaxMalformedFixture fixtureOversizedLength (outDir / "pax-oversized-length.tar")
  buildPaxMalformedFixture fixtureTruncatedRecord (outDir / "pax-truncated-record.tar")
  buildPaxMalformedFixture fixtureInvalidUtf8Key (outDir / "pax-invalid-utf8-key.tar")
  buildPaxMalformedFixture fixtureInvalidUtf8Value (outDir / "pax-invalid-utf8-value.tar")
  buildPaxMalformedFixture fixtureInconsistentLength (outDir / "pax-inconsistent-length.tar")
  buildPaxMalformedFixture fixturePathNulInValue (outDir / "pax-path-nul-in-value.tar")
  buildPaxMalformedFixture fixtureDuplicatePath (outDir / "pax-duplicate-path.tar")
  IO.println "Built 7 malformed PAX fixtures under testdata/tar/malformed/."
