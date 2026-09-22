import Lake
open System Lake DSL

/-! # lean-zip dev-only conformance package

The native↔zlib conformance suite lives here, out of the shipped
`lean-zip` library: these tests compare the pure-Lean codec against
system zlib (via the `lean-zlib` FFI bindings), which the shipped
library itself must not depend on. Lake has no test-only dependencies,
so the extra dependency lives in this sub-package; it requires the
parent via a local path (`require «lean-zip» from ".."`) and `lean-zlib`
from git.

Beyond translation-validation (native and zlib agree), this suite checks
the one property the roundtrip proofs cannot: RFC interop — real zlib
decodes the native encoder's output, and the native decoder accepts real
zlib's. It also carries the deterministic inflate fuzz harness
(`fuzz_inflate`).

Building this package needs system zlib + pkg-config (or
`ZLIB_CFLAGS`/`ZLIB_LDFLAGS`). Run it from the repo root with
`lake -d conformance build && lake -d conformance test`.

This directory deliberately has no `lean-toolchain`. It requires the parent
by path, so it could never correctly build on a different toolchain, and
elan resolves the root's file from here anyway. A second copy could only
ever be redundant or wrong: when it was wrong, `cd conformance && lake -R
build` silently built the whole library on the stale toolchain and CI
reported a pass for a configuration nobody was asking about. -/

/-- Split a shell-style flag string on spaces and drop empties. -/
def splitFlags (s : String) : Array String :=
  s.splitOn " " |>.filter (· ≠ "") |>.toArray

/-- Look `cmd` up on `PATH`, the way a shell would (keep in sync with
    lean-zlib's lakefile). -/
def onPath (cmd : String) : IO Bool := do
  let some path ← IO.getEnv "PATH" | return false
  let sep := if Platform.isWindows then ";" else ":"
  let exts := if Platform.isWindows then #["", ".exe", ".cmd", ".bat"] else #[""]
  for dir in path.splitOn sep do
    if dir.isEmpty then continue
    for ext in exts do
      let candidate : FilePath := dir / (cmd ++ ext)
      if (← candidate.pathExists) && !(← candidate.isDir) then return true
  return false

/-- Run a probe command, reporting `none` if the tool is not installed (keep in
    sync with lean-zlib's lakefile, which explains why a missing executable must
    never reach `IO.Process.output` on the pinned toolchain). -/
def tryOutput (cmd : String) (args : Array String) : IO (Option IO.Process.Output) := do
  unless (← onPath cmd) do return none
  match ← (IO.Process.output { cmd, args }).toBaseIO with
  | .ok out => return some out
  | .error e =>
    IO.eprintln s!"warning: could not run the probe '{cmd}': {e}"
    return none

/-- Run `pkg-config` and split the output into flags. Returns `#[]` on failure. -/
def pkgConfig (pkg : String) (flag : String) : IO (Array String) := do
  let some out ← tryOutput "pkg-config" #[flag, pkg] | return #[]
  if out.exitCode != 0 then return #[]
  return splitFlags out.stdout.trimAscii.toString

/-- Run `xcrun --show-sdk-path` and return the SDK path on Apple platforms. -/
def macSdkPath : IO (Option FilePath) := do
  if !Platform.isOSX then return none
  let some out ← tryOutput "xcrun" #["--show-sdk-path"] | return none
  if out.exitCode != 0 then
    return none
  else
    return some out.stdout.trimAscii.toString

/-- Prefer an explicit linker override when supplied by the environment. -/
def zlibLdFlagsOverride : IO (Option (Array String)) := do
  return (← IO.getEnv "ZLIB_LDFLAGS") |>.map (splitFlags ·.trimAscii.toString)

/-- Extract `-L` library paths from `NIX_LDFLAGS` (set by nix-shell). -/
def nixLdLibPaths : IO (Array String) := do
  let some val := (← IO.getEnv "NIX_LDFLAGS") | return #[]
  return val.splitOn " " |>.filter (·.startsWith "-L") |>.toArray

/-- Get link flags for zlib (keep in sync with lean-zlib's lakefile).
    The `lean-zlib` dependency's own `moreLinkArgs` do not propagate to this
    package's executables, so the link flags are re-supplied here. -/
def zlibLinkFlags : IO (Array String) := do
  if let some flags := (← zlibLdFlagsOverride) then
    return flags
  let libPaths ← nixLdLibPaths
  let zlibFlags ← pkgConfig "zlib" "--libs"
  if !zlibFlags.isEmpty && zlibFlags.any (·.startsWith "-L") then
    return zlibFlags
  if let some sdk := (← macSdkPath) then
    return #["-L", (sdk / "usr/lib").toString, "-lz"]
  if !zlibFlags.isEmpty then
    return libPaths ++ zlibFlags
  -- pkg-config unavailable — try NIX_LDFLAGS for -L paths
  return libPaths ++ #["-lz"]

/-- LTO link flags mirroring the parent lakefile's `ltoLinkFlags` (issue
    #2806, keep in sync with `../lakefile.lean`): on Linux the parent
    library's objects are LLVM bitcode, so this package's executable links
    run the same LTO codegen at `-O3`. `LEAN_ZIP_LTO=0` opts out. -/
def ltoLinkFlags : IO (Array String) := do
  if Platform.isWindows || Platform.isOSX then return #[]
  if (← IO.getEnv "LEAN_ZIP_LTO") == some "0" then return #[]
  return #["-flto", "-fno-semantic-interposition", "-O3"]

package conformance where
  moreLinkArgs := run_io do return (← zlibLinkFlags) ++ (← ltoLinkFlags)

require «lean-zip» from ".."

require «lean-zlib» from git "https://github.com/kim-em/lean-zlib" @ "1179bdc8cfdb1ebf5a7478844526e52d7b789841"

-- The conformance test modules live under the `Conformance.*` module path:
-- a package cannot add modules under a required dependency's library
-- namespace (`ZipTest`), or Lake's `.submodules` glob would steal
-- resolution of the parent's own `ZipTest.Helpers`.
lean_lib Conformance where
  globs := #[.submodules `Conformance]

@[default_target, test_driver]
lean_exe conformance_test where
  root := `Conformance

lean_exe fuzz_inflate where
  root := `FuzzInflateMain
