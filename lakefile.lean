import Lake
open System Lake DSL

/-- Split a shell-style flag string on spaces and drop empties. -/
def splitFlags (s : String) : Array String :=
  s.splitOn " " |>.filter (· ≠ "") |>.toArray

/-- Run `pkg-config` and split the output into flags. Returns `#[]` on failure. -/
def pkgConfig (pkg : String) (flag : String) : IO (Array String) := do
  let out ← IO.Process.output { cmd := "pkg-config", args := #[flag, pkg] }
  if out.exitCode != 0 then return #[]
  return splitFlags out.stdout.trimAscii.toString

/-- Run `xcrun --show-sdk-path` and return the SDK path on Apple platforms. -/
def macSdkPath : IO (Option FilePath) := do
  let out ← IO.Process.output { cmd := "xcrun", args := #["--show-sdk-path"] }
  if out.exitCode != 0 then
    return none
  else
    return some out.stdout.trimAscii.toString

/-- Prefer an explicit linker override when supplied by the environment. -/
def zlibLdFlagsOverride : IO (Option (Array String)) := do
  return (← IO.getEnv "ZLIB_LDFLAGS") |>.map (splitFlags ·.trimAscii.toString)

/-- Get zlib include flags, respecting `ZLIB_CFLAGS` env var override. -/
def zlibCFlags : IO (Array String) := do
  if let some flags := (← IO.getEnv "ZLIB_CFLAGS") then
    return splitFlags flags.trimAscii.toString
  let flags ← pkgConfig "zlib" "--cflags"
  if !flags.isEmpty then
    return flags
  if let some sdk := (← macSdkPath) then
    return #["-I", (sdk / "usr/include").toString]
  return #[]

/-- Extract `-L` library paths from `NIX_LDFLAGS` (set by nix-shell). -/
def nixLdLibPaths : IO (Array String) := do
  let some val := (← IO.getEnv "NIX_LDFLAGS") | return #[]
  return val.splitOn " " |>.filter (·.startsWith "-L") |>.toArray

/-- Get link flags for zlib.
    Tries `ZLIB_LDFLAGS`, then pkg-config, then macOS SDK / Nix fallbacks. -/
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

/-! The shipped package is the verified library plus its genuinely
    load-bearing FFI: zlib (`libzlib_ffi`) and the two project-local
    stopgaps `libcopy_within_ffi` (lean#14158) and `libbytearray_wide_ffi`
    (lean#14053). The Track D benchmarking and comparator apparatus —
    the miniz_oxide / libdeflate / zopfli shims and the bench/sweep/fuzz
    executables — lives in the dev-only `bench/` sub-package, so a
    downstream `require lean-zip` never pulls in the Rust/libdeflate/zopfli
    comparators or triggers a cargo build on (re)configure. -/
package «lean-zip» where
  moreLinkArgs := run_io zlibLinkFlags
  testDriver := "test"

require zipCommon from git "https://github.com/kim-em/lean-zip-common" @ "89204d61227069f5c5d19dc69418ab57f96fe61c"

lean_lib Zip

-- zlib FFI
input_file zlib_ffi.c where
  path := "c" / "zlib_ffi.c"
  text := true

target zlib_ffi.o pkg : FilePath := do
  let srcJob ← zlib_ffi.c.fetch
  let oFile := pkg.buildDir / "c" / "zlib_ffi.o"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString] ++ (← zlibCFlags)
  let hardArgs := if Platform.isWindows then #[] else #["-fPIC"]
  buildO oFile srcJob weakArgs hardArgs "cc"

extern_lib libzlib_ffi pkg := do
  let ffiO ← zlib_ffi.o.fetch
  let name := nameToStaticLib "zlib_ffi"
  buildStaticLib (pkg.staticLibDir / name) #[ffiO]

-- ByteArray.copyWithin primitive (project-local stopgap for lean#14158);
-- no external library, always compiled.
input_file copy_within_ffi.c where
  path := "c" / "copy_within_ffi.c"
  text := true

target copy_within_ffi.o pkg : FilePath := do
  let srcJob ← copy_within_ffi.c.fetch
  let oFile := pkg.buildDir / "c" / "copy_within_ffi.o"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  let hardArgs := if Platform.isWindows then #[] else #["-fPIC"]
  buildO oFile srcJob weakArgs hardArgs "cc"

extern_lib libcopy_within_ffi pkg := do
  let ffiO ← copy_within_ffi.o.fetch
  let name := nameToStaticLib "copy_within_ffi"
  buildStaticLib (pkg.staticLibDir / name) #[ffiO]

-- Word-sized little-endian ByteArray readers (project-local stopgap for
-- lean#14053); no external library, always compiled.
input_file bytearray_wide_ffi.c where
  path := "c" / "bytearray_wide_ffi.c"
  text := true

target bytearray_wide_ffi.o pkg : FilePath := do
  let srcJob ← bytearray_wide_ffi.c.fetch
  let oFile := pkg.buildDir / "c" / "bytearray_wide_ffi.o"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  -- -O2 is essential here: these are single-load/store hot-loop primitives
  -- whose lean.h helpers (lean_sarray_cptr, lean_is_exclusive, ...) only
  -- disappear under optimization; without it each "wide" op is a pile of
  -- outlined helper calls and loses to the runtime's own -O2 push/get.
  -- -DNDEBUG matches how the release Lean runtime itself is built: the
  -- lean.h asserts are debug-only checks, and these externs' bounds are
  -- carried by Lean-side proofs (+ the ZipTest/Wide conformance sweeps).
  let hardArgs := #["-O2", "-DNDEBUG"] ++
    if Platform.isWindows then #[] else #["-fPIC"]
  buildO oFile srcJob weakArgs hardArgs "cc"

extern_lib libbytearray_wide_ffi pkg := do
  let ffiO ← bytearray_wide_ffi.o.fetch
  let name := nameToStaticLib "bytearray_wide_ffi"
  buildStaticLib (pkg.staticLibDir / name) #[ffiO]

lean_lib ZipTest where
  globs := #[.submodules `ZipTest]

@[default_target]
lean_exe test where
  root := `ZipTest

lean_exe perfspike where
  root := `PerfSpike
