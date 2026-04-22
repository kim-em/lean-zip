import Zip

/-! Build malformed tar fixtures whose GNU long-name and PAX extended
    header pseudo-entries declare a `size` field far above
    `Tar.defaultMaxHeaderSize` (8 MiB).

Each fixture is a single 512-byte tar header block — no payload, no
trailing zero blocks. Parsing reaches `readEntryData` with the crafted
`entry.size`; the size cap fires before any allocation, so the body is
never required for the regression to trip.

Run once at development time:

    lake env lean --run scripts/build-header-oversized-malformed-fixtures.lean

Output (byte-deterministic):
- testdata/tar/malformed/gnu-longname-oversized-size.tar
- testdata/tar/malformed/pax-extended-oversized-size.tar
-/

/-- Build a 512-byte UStar header for a header-only pseudo-entry whose
    declared `size` overflows `Tar.defaultMaxHeaderSize`. The size field
    is written as the largest representable 11-digit octal value
    (`0o77777777777` ≈ 8 GiB), which is three orders of magnitude above
    the 8 MiB cap. -/
def buildOversizedHeader (typeflag : UInt8) : IO ByteArray :=
  Tar.buildHeader
    { path     := "././@LongLink"
      size     := 0o77777777777   -- ≈ 8 GiB, well above the 8 MiB cap
      mode     := 0o644
      typeflag := typeflag }

/-- Fixture 1: gnu-longname-oversized-size.tar
    Single 512-byte header with typeflag `'L'` and `size ≈ 8 GiB`.
    `readEntryData` rejects with `"exceeds maximum header size"`
    before any allocation. -/
def buildGnuLongnameOversized : IO ByteArray :=
  buildOversizedHeader Tar.typeGnuLongName

/-- Fixture 2: pax-extended-oversized-size.tar
    Single 512-byte header with typeflag `'x'` and `size ≈ 8 GiB`.
    Exercises the structurally-identical PAX extended-header arm of
    `forEntries`. -/
def buildPaxExtendedOversized : IO ByteArray :=
  buildOversizedHeader Tar.typePaxExtended

def main : IO Unit := do
  let outDir : System.FilePath := "testdata/tar/malformed"
  IO.FS.writeBinFile (outDir / "gnu-longname-oversized-size.tar")
    (← buildGnuLongnameOversized)
  IO.FS.writeBinFile (outDir / "pax-extended-oversized-size.tar")
    (← buildPaxExtendedOversized)
  IO.println "Built 2 malformed oversized-header fixtures under testdata/tar/malformed/."
