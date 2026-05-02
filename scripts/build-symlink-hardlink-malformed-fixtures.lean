import Zip

/-! Build per-typeflag-policy regression fixtures for Track E Priority 1.

Each fixture is a minimal one-entry UStar tar archive with `size == 0`,
exercising the `Tar.extract` per-typeflag policy:

* `symlink-absolute.tar` — `typeflag == typeSymlink`, `linkname ==
  "/etc/passwd"`, `path == "escape"`.  `Tar.extract` must reject this
  with `"unsafe symlink target"` before any `Handle.createSymlink` call.
* `hardlink-outside.tar` — `typeflag == typeHardlink`, `linkname ==
  "../outside"`, `path == "entry"`.  `Tar.extract` must silently skip
  the entry; no file named `outside` may appear next to the extract
  directory.
* `tar-fifo-skipped.tar` — `typeflag == 0x36` (POSIX UStar `'6'`,
  FIFO), `linkname == ""`, `path == "fifo-entry"`.  `Tar.extract` must
  silently skip the entry; no FIFO is materialised, so the extract dir
  remains empty.  Sibling of `hardlink-outside.tar` for the silent-skip
  `else` fallback in `Tar.extract`: together they pin two distinct
  typeflag values against the shared fallback, so a future refactor
  cannot drop one arm without breaking at least one of the two
  fixtures.
* `tar-chardev-skipped.tar` — `typeflag == 0x33` (POSIX UStar `'3'`,
  character device), `linkname == ""`, `path == "chardev-entry"`.
  `Tar.extract` must silently skip the entry; no character-device node
  is materialised, so the extract dir remains empty.  Third sibling of
  the silent-skip `else` fallback family alongside `hardlink-outside.tar`
  (typeflag `'1'`) and `tar-fifo-skipped.tar` (typeflag `'6'`); together
  the three pin three distinct typeflag values against the shared
  fallback.
* `tar-blockdev-skipped.tar` — `typeflag == 0x34` (POSIX UStar `'4'`,
  block device), `linkname == ""`, `path == "blockdev-entry"`.
  `Tar.extract` must silently skip the entry; no block-device node is
  materialised, so the extract dir remains empty.  Fourth sibling of
  the silent-skip `else` fallback family alongside `hardlink-outside.tar`
  (typeflag `'1'`), `tar-fifo-skipped.tar` (typeflag `'6'`), and
  `tar-chardev-skipped.tar` (typeflag `'3'`); together the four pin
  four distinct typeflag values against the shared fallback.
* `tar-contiguous-skipped.tar` — `typeflag == 0x37` (POSIX UStar `'7'`,
  contiguous file), `linkname == ""`, `path == "contiguous-entry"`.
  `Tar.extract` must silently skip the entry; lean-zip's strict `==`
  chain rejects `'7'` rather than aliasing it to `'0'` (regular file)
  as some lenient peer extractors do, so the extract dir remains empty.
  Fifth sibling of the silent-skip `else` fallback family alongside
  `hardlink-outside.tar` (typeflag `'1'`), `tar-fifo-skipped.tar`
  (typeflag `'6'`), `tar-chardev-skipped.tar` (typeflag `'3'`), and
  `tar-blockdev-skipped.tar` (typeflag `'4'`); together the five pin
  five distinct typeflag values against the shared fallback, fully
  fixturing the POSIX UStar `'0'`–`'7'` numeric range.
* `tar-volumeheader-skipped.tar` — `typeflag == 0x56` (GNU `'V'`,
  multi-volume archive label marker), `linkname == ""`, `path ==
  "volume-label-entry"`. `Tar.extract` must silently skip the entry;
  lean-zip's strict `==` chain does not match `'V'` against the typed
  branches, so the entry falls through to the `else` arm and no
  filesystem entry is created. First GNU-typeflag sibling of the
  silent-skip `else` fallback family alongside the POSIX UStar
  siblings `hardlink-outside.tar` (typeflag `'1'`), `tar-fifo-skipped.tar`
  (typeflag `'6'`), `tar-chardev-skipped.tar` (typeflag `'3'`),
  `tar-blockdev-skipped.tar` (typeflag `'4'`), and
  `tar-contiguous-skipped.tar` (typeflag `'7'`); together the six pin
  six distinct typeflag values against the shared fallback, spanning
  the POSIX UStar `'1'`/`'3'`/`'4'`/`'6'`/`'7'` numeric range and the
  GNU-typeflag `'V'` extension (a sub-ladder distinct from the POSIX
  UStar `'0'`–`'7'` range).
* `tar-multivol-skipped.tar` — `typeflag == 0x4D` (GNU `'M'`,
  multi-volume continuation marker), `linkname == ""`, `path ==
  "multivol-entry"`. `Tar.extract` must silently skip the entry;
  lean-zip's strict `==` chain does not match `'M'` against the typed
  branches, so the entry falls through to the `else` arm and no
  filesystem entry is created. Second GNU-typeflag sibling of the
  silent-skip `else` fallback family alongside `tar-volumeheader-skipped.tar`
  (typeflag `'V'`), extending the GNU-typeflag sub-ladder distinct
  from the POSIX UStar `'0'`–`'7'` range. Together with the five
  POSIX UStar siblings (`hardlink-outside.tar` (typeflag `'1'`),
  `tar-fifo-skipped.tar` (typeflag `'6'`), `tar-chardev-skipped.tar`
  (typeflag `'3'`), `tar-blockdev-skipped.tar` (typeflag `'4'`), and
  `tar-contiguous-skipped.tar` (typeflag `'7'`)) the family pins
  seven distinct typeflag values against the shared fallback.
* `tar-sparse-skipped.tar` — `typeflag == 0x53` (GNU `'S'`, sparse
  file), `linkname == ""`, `path == "sparse-entry"`. `Tar.extract`
  must silently skip the entry; lean-zip's strict `==` chain does
  not match `'S'` against the typed branches, so the entry falls
  through to the `else` arm and no filesystem entry is created.
  Third GNU-typeflag sibling of the silent-skip `else` fallback
  family alongside `tar-volumeheader-skipped.tar` (typeflag `'V'`)
  and `tar-multivol-skipped.tar` (typeflag `'M'`), extending the
  GNU-typeflag sub-ladder distinct from the POSIX UStar `'0'`–`'7'`
  range. Together with the five POSIX UStar siblings the family
  pins eight distinct typeflag values against the shared fallback.
* `tar-incremental-skipped.tar` — `typeflag == 0x44` (GNU `'D'`,
  directory-dump for incremental backups), `linkname == ""`, `path
  == "incremental-entry"`. `Tar.extract` must silently skip the
  entry; lean-zip's strict `==` chain does not match `'D'` against
  the typed branches, so the entry falls through to the `else` arm
  and no filesystem entry is created. Fourth GNU-typeflag sibling of
  the silent-skip `else` fallback family alongside
  `tar-volumeheader-skipped.tar` (typeflag `'V'`),
  `tar-multivol-skipped.tar` (typeflag `'M'`), and
  `tar-sparse-skipped.tar` (typeflag `'S'`), extending the
  GNU-typeflag sub-ladder distinct from the POSIX UStar `'0'`–`'7'`
  range. Together with the five POSIX UStar siblings the family
  pins nine distinct typeflag values against the shared fallback.
* `tar-longnames-skipped.tar` — `typeflag == 0x4E` (GNU `'N'`,
  LF_NAMES old-long-name extension, deprecated precursor to the
  modern `'L'` / `'K'` long-name encoding), `linkname == ""`, `path
  == "longnames-entry"`. `Tar.extract` must silently skip the entry;
  lean-zip's strict `==` chain does not match `'N'` against the typed
  branches, and `forEntries`'s inner dispatch recognises only the
  modern `'L'` / `'K'` long-name typeflags (and the PAX `'x'` / `'g'`
  pair) — `'N'` is *not* aliased to `'L'` despite being the
  historical precursor of the same long-name extension family — so
  the entry falls through to the `else` arm and no filesystem entry
  is created. The header path / linkname is never interpreted as a
  name-rewrite directive for subsequent entries (a peer-parser-
  differential smuggling vector that the silent-skip policy closes).
  Fifth GNU-typeflag sibling of the silent-skip `else` fallback
  family alongside `tar-volumeheader-skipped.tar` (typeflag `'V'`),
  `tar-multivol-skipped.tar` (typeflag `'M'`),
  `tar-sparse-skipped.tar` (typeflag `'S'`), and
  `tar-incremental-skipped.tar` (typeflag `'D'`), extending the
  GNU-typeflag sub-ladder distinct from the POSIX UStar `'0'`–`'7'`
  range. Together with the five POSIX UStar siblings the family
  pins ten distinct typeflag values against the shared fallback.

Run once at development time:

    lake env lean --run scripts/build-symlink-hardlink-malformed-fixtures.lean

Output (byte-deterministic):
- testdata/tar/security/symlink-absolute.tar
- testdata/tar/security/hardlink-outside.tar
- testdata/tar/security/tar-fifo-skipped.tar
- testdata/tar/security/tar-chardev-skipped.tar
- testdata/tar/security/tar-blockdev-skipped.tar
- testdata/tar/security/tar-contiguous-skipped.tar
- testdata/tar/security/tar-volumeheader-skipped.tar
- testdata/tar/security/tar-multivol-skipped.tar
- testdata/tar/security/tar-sparse-skipped.tar
- testdata/tar/security/tar-incremental-skipped.tar
- testdata/tar/security/tar-longnames-skipped.tar
-/

/-- Build a single-entry UStar archive with `size == 0`. The output is
    just the 512-byte header — `Tar.forEntries` terminates on the
    short read at EOF, so no trailing zero-blocks are required (the
    existing `tar-slip.tar` and `symlink-slip.tar` fixtures use the
    same geometry). -/
def buildZeroSizeFixture
    (path linkname : String) (typeflag : UInt8) (outPath : System.FilePath) : IO Unit := do
  let entry : Tar.Entry :=
    { path     := path
      linkname := linkname
      size     := 0
      mode     := 0o644
      typeflag := typeflag }
  let hdr ← Tar.buildHeader entry
  IO.FS.writeBinFile outPath hdr

def main : IO Unit := do
  let outDir : System.FilePath := "testdata/tar/security"
  buildZeroSizeFixture "escape" "/etc/passwd" Tar.typeSymlink
    (outDir / "symlink-absolute.tar")
  buildZeroSizeFixture "entry" "../outside" Tar.typeHardlink
    (outDir / "hardlink-outside.tar")
  -- POSIX UStar typeflag '6' (0x36) = FIFO. No constant in `Tar`
  -- namespace because FIFOs are not a recognised typeflag — they fall
  -- through to the silent-skip `else` fallback in `Tar.extract`
  -- alongside any other unsupported typeflag.
  buildZeroSizeFixture "fifo-entry" "" 0x36
    (outDir / "tar-fifo-skipped.tar")
  -- POSIX UStar typeflag '3' (0x33) = character special device. Same
  -- silent-skip `else` fallback as the FIFO arm above; no constant in
  -- `Tar` namespace.
  buildZeroSizeFixture "chardev-entry" "" 0x33
    (outDir / "tar-chardev-skipped.tar")
  -- POSIX UStar typeflag '4' (0x34) = block special device. Same
  -- silent-skip `else` fallback as the FIFO and chardev arms above; no
  -- constant in `Tar` namespace.
  buildZeroSizeFixture "blockdev-entry" "" 0x34
    (outDir / "tar-blockdev-skipped.tar")
  -- POSIX UStar typeflag '7' (0x37) = contiguous file. Same silent-skip
  -- `else` fallback as the FIFO / chardev / blockdev arms above; no
  -- constant in `Tar` namespace. lean-zip's strict `==` chain rejects
  -- `'7'` rather than aliasing it to `'0'` (regular file) as some
  -- lenient peer extractors do.
  buildZeroSizeFixture "contiguous-entry" "" 0x37
    (outDir / "tar-contiguous-skipped.tar")
  -- GNU typeflag 'V' (0x56) = multi-volume archive label marker. First
  -- GNU-typeflag sibling of the silent-skip `else` fallback family
  -- (sub-ladder distinct from the POSIX UStar '0'–'7' range above); no
  -- constant in `Tar` namespace. The path "volume-label-entry" reads as
  -- a synthetic GNU volume label without colliding with the device-node
  -- naming pattern used by the chardev / blockdev / FIFO arms.
  buildZeroSizeFixture "volume-label-entry" "" 0x56
    (outDir / "tar-volumeheader-skipped.tar")
  -- GNU typeflag 'M' (0x4D) = multi-volume continuation marker. Second
  -- GNU-typeflag sibling of the silent-skip `else` fallback family
  -- (sub-ladder distinct from the POSIX UStar '0'–'7' range above);
  -- no constant in `Tar` namespace. GNU tar emits 'M' as the first
  -- record of a continuation volume in a multi-volume archive — a
  -- malicious single-volume archive could ship a top-level 'M' entry
  -- with crafted `path` / `size` fields, expecting a lenient extractor
  -- to materialise the marker as a regular file. lean-zip's strict
  -- `==` chain rejects 'M' and silent-skips.
  buildZeroSizeFixture "multivol-entry" "" 0x4D
    (outDir / "tar-multivol-skipped.tar")
  -- GNU typeflag 'S' (0x53) = sparse file. Third GNU-typeflag sibling
  -- of the silent-skip `else` fallback family (sub-ladder distinct from
  -- the POSIX UStar '0'–'7' range above); no constant in `Tar`
  -- namespace. GNU tar emits 'S' for files stored in GNU's sparse
  -- format: the header carries `path` / `mode` / `mtime` as for a
  -- regular file, but the payload encodes a sparse map instead of raw
  -- file bytes — a malicious archive could ship a 'S' entry with a
  -- crafted sparse map declaring zero-fill segments that overlap or
  -- exceed the entry's declared `size`, expecting a lenient extractor
  -- to allocate a large output file (zero-fill amplification) or
  -- miscompute the payload offset. lean-zip's strict `==` chain rejects
  -- 'S' and silent-skips. The fixture intentionally ships a zero-byte
  -- body with no sparse map: the silent-skip policy applies regardless
  -- of payload shape, and a zero-byte body keeps the fixture geometry
  -- uniform with the other GNU siblings.
  buildZeroSizeFixture "sparse-entry" "" 0x53
    (outDir / "tar-sparse-skipped.tar")
  -- GNU typeflag 'D' (0x44) = directory-dump for incremental backups.
  -- Fourth GNU-typeflag sibling of the silent-skip `else` fallback family
  -- (sub-ladder distinct from the POSIX UStar '0'–'7' range above); no
  -- constant in `Tar` namespace. GNU tar emits 'D' for directory dumps in
  -- incremental backup archives (`-G` / `--listed-incremental`): each
  -- directory is recorded as a 'D' entry whose payload is a
  -- NUL-separated listing of the directory's contents at backup time
  -- (with leading 'Y'/'N' markers indicating whether each entry is
  -- included in this incremental). A malicious archive could ship a
  -- 'D' entry with a crafted directory-listing payload that an
  -- incremental-aware extractor would interpret as instructions to
  -- delete files outside `outDir` (the GNU incremental format allows
  -- the listing to mark files for *removal* during restore), expecting
  -- a lenient extractor to honour those removal cues. lean-zip's
  -- strict `==` chain rejects 'D' and silent-skips, never interpreting
  -- the listing payload at all. The fixture intentionally ships a
  -- zero-byte body with no incremental listing: the silent-skip policy
  -- applies regardless of payload shape, and a zero-byte body keeps
  -- the fixture geometry uniform with the other GNU siblings.
  buildZeroSizeFixture "incremental-entry" "" 0x44
    (outDir / "tar-incremental-skipped.tar")
  -- GNU typeflag 'N' (0x4E) = LF_NAMES old-long-name extension, the
  -- deprecated precursor to the modern 'L' / 'K' long-name encoding.
  -- Fifth GNU-typeflag sibling of the silent-skip `else` fallback
  -- family (sub-ladder distinct from the POSIX UStar '0'–'7' range
  -- above); no constant in `Tar` namespace. GNU tar emitted 'N' for
  -- entries whose names did not fit into the 100-byte UStar `name`
  -- field: the entry payload carried a list of filenames that a peer
  -- parser was expected to apply to the entries that follow. The
  -- format predates PAX ('x') and the modern GNU 'L'/'K' headers,
  -- and is considered obsolete in current GNU tar but is still
  -- recognised by `bsdtar` / `libarchive` in lenient mode. A
  -- malicious archive could ship an 'N' entry whose payload encodes
  -- a list of filenames containing `../etc/passwd` or absolute
  -- paths, expecting a lenient extractor to apply those names to
  -- the next regular-file entry (parser-differential archive-slip
  -- via deprecated long-name rewriting). lean-zip's strict `==`
  -- chain rejects 'N' and silent-skips, never interpreting the
  -- payload as a name-rewrite directive — `forEntries` recognises
  -- only the modern 'L' / 'K' (and PAX 'x' / 'g') long-name
  -- typeflags; 'N' is *not* aliased to 'L'. The fixture
  -- intentionally ships a zero-byte body with no filename listing:
  -- the silent-skip policy applies regardless of payload shape, and
  -- a zero-byte body keeps the fixture geometry uniform with the
  -- other GNU siblings.
  buildZeroSizeFixture "longnames-entry" "" 0x4E
    (outDir / "tar-longnames-skipped.tar")
  IO.println "Built 11 per-typeflag-policy security fixtures under testdata/tar/security/."
