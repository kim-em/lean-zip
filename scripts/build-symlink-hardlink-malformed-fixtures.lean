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

Run once at development time:

    lake env lean --run scripts/build-symlink-hardlink-malformed-fixtures.lean

Output (byte-deterministic):
- testdata/tar/security/symlink-absolute.tar
- testdata/tar/security/hardlink-outside.tar
- testdata/tar/security/tar-fifo-skipped.tar
- testdata/tar/security/tar-chardev-skipped.tar
- testdata/tar/security/tar-blockdev-skipped.tar
- testdata/tar/security/tar-contiguous-skipped.tar
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
  IO.println "Built 6 per-typeflag-policy security fixtures under testdata/tar/security/."
