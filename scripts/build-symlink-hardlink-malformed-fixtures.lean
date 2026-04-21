import Zip

/-! Build symlink/hardlink archive-slip regression fixtures for Track E
    Priority 1.

Each fixture is a minimal one-entry UStar tar archive with `size == 0`,
exercising the `Tar.extract` per-typeflag policy:

* `symlink-absolute.tar` — `typeflag == typeSymlink`, `linkname ==
  "/etc/passwd"`, `path == "escape"`.  `Tar.extract` must reject this
  with `"unsafe symlink target"` before any `Handle.createSymlink` call.
* `hardlink-outside.tar` — `typeflag == typeHardlink`, `linkname ==
  "../outside"`, `path == "entry"`.  `Tar.extract` must silently skip
  the entry; no file named `outside` may appear next to the extract
  directory.

Run once at development time:

    lake env lean --run scripts/build-symlink-hardlink-malformed-fixtures.lean

Output (byte-deterministic):
- testdata/tar/security/symlink-absolute.tar
- testdata/tar/security/hardlink-outside.tar
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
  IO.println "Built 2 symlink/hardlink security fixtures under testdata/tar/security/."
