-- Shims for IO.FS.Handle operations missing from Lean 4 stdlib.
-- Upstream PR: https://github.com/leanprover/lean4/pull/11442
-- Remove this file when seek/tell land in the stdlib.

namespace Handle

/-- Seek to an absolute byte position in a file handle.
    Uses `fseeko` for 64-bit offset support (ZIP64). -/
@[extern "lean_handle_seek"]
opaque seek (h : @& IO.FS.Handle) (pos : UInt64) : IO Unit

/-- Get the byte size of the file underlying a handle.
    Uses `fstat` — does not move the file cursor. -/
@[extern "lean_handle_file_size"]
opaque fileSize (h : @& IO.FS.Handle) : IO UInt64

/-- Create a symbolic link. `target` is the link content, `linkPath` is where to create it. -/
@[extern "lean_create_symlink"]
opaque createSymlink (target : @& String) (linkPath : @& String) : IO Unit

end Handle
