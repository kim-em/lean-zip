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

/-- Link-time-optimization flags for the shipped library (issue #2806).

    `-flto` lets the final link inline the project-local stopgap externs
    (`c/bytearray_wide_ffi.c`, `c/extend_within_ffi.c`, `c/copy_within_ffi.c`)
    into the hot matcher/decoder loops instead of leaving per-iteration
    cross-object calls — a measured +2–5% end-to-end compress win with
    byte-identical output (LTO is codegen-only). For the bitcode to merge,
    every object must come from the same LLVM: the Lean-emitted C already
    compiles with the toolchain clang, and the FFI targets below use
    `buildLeanO` (same compiler) instead of the system `cc`.
    `-fno-semantic-interposition` keeps `-fPIC` codegen from pessimizing
    cross-object references. Linux-only: macOS links with the system ld64,
    whose libLTO need not accept the toolchain clang's bitcode, and Windows
    is untested. Set `LEAN_ZIP_LTO=0` to opt out (e.g. to link the static
    libs with a non-LTO-aware toolchain). -/
def ltoFlags : IO (Array String) := do
  if Platform.isWindows || Platform.isOSX then return #[]
  if (← IO.getEnv "LEAN_ZIP_LTO") == some "0" then return #[]
  return #["-flto", "-fno-semantic-interposition"]

/-- Link-side LTO flags: `-flto` marks the link as LTO, `-O3` runs the
    link-time codegen pipeline at the same level as the per-module compiles
    (lld's default is `--lto-O2`). Empty whenever `ltoFlags` is. -/
def ltoLinkFlags : IO (Array String) := do
  let flags ← ltoFlags
  if flags.isEmpty then return #[] else return flags ++ #["-O3"]

/-! The shipped package is the verified library plus its genuinely
    load-bearing FFI: zlib (`libzlib_ffi`) and the project-local primitives
    `libcopy_within_ffi` (lean#14158), `libextend_within_ffi` (overlapping-match
    copy), and `libbytearray_wide_ffi` (lean#14053). The Track D benchmarking
    and comparator apparatus —
    the miniz_oxide / libdeflate / zopfli shims and the bench/sweep/fuzz
    executables — lives in the dev-only `bench/` sub-package, so a
    downstream `require lean-zip` never pulls in the Rust/libdeflate/zopfli
    comparators or triggers a cargo build on (re)configure. -/
package «lean-zip» where
  moreLeancArgs := run_io ltoFlags
  moreLinkArgs := run_io do return (← zlibLinkFlags) ++ (← ltoLinkFlags)
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
  -- -O2/-DNDEBUG for the same reason as bytearray_wide_ffi (and because a
  -- clang -O0 object carries `optnone`, which would block the LTO inlining).
  -- `buildLeanO` compiles with the toolchain clang so the -flto bitcode
  -- matches the Lean-emitted objects' LLVM version (see `ltoFlags`).
  let hardArgs := #["-O2", "-DNDEBUG"] ++ (← ltoFlags) ++
    if Platform.isWindows then #[] else #["-fPIC"]
  buildLeanO oFile srcJob #[] hardArgs

extern_lib libcopy_within_ffi pkg := do
  let ffiO ← copy_within_ffi.o.fetch
  let name := nameToStaticLib "copy_within_ffi"
  buildStaticLib (pkg.staticLibDir / name) #[ffiO]

-- ByteArray.extendWithin primitive (allocation-free overlapping-match copy);
-- no external library, always compiled.
input_file extend_within_ffi.c where
  path := "c" / "extend_within_ffi.c"
  text := true

target extend_within_ffi.o pkg : FilePath := do
  let srcJob ← extend_within_ffi.c.fetch
  let oFile := pkg.buildDir / "c" / "extend_within_ffi.o"
  -- -O2/-DNDEBUG for the same reason as bytearray_wide_ffi: this is a hot fill
  -- loop whose lean.h helpers only inline away under optimization, and its
  -- bounds are carried by the Lean-side reference body (+ conformance sweeps).
  -- `buildLeanO` + `ltoFlags`: see `copy_within_ffi.o`.
  let hardArgs := #["-O2", "-DNDEBUG"] ++ (← ltoFlags) ++
    if Platform.isWindows then #[] else #["-fPIC"]
  buildLeanO oFile srcJob #[] hardArgs

extern_lib libextend_within_ffi pkg := do
  let ffiO ← extend_within_ffi.o.fetch
  let name := nameToStaticLib "extend_within_ffi"
  buildStaticLib (pkg.staticLibDir / name) #[ffiO]

-- Word-sized little-endian ByteArray readers (project-local stopgap for
-- lean#14053); no external library, always compiled.
input_file bytearray_wide_ffi.c where
  path := "c" / "bytearray_wide_ffi.c"
  text := true

target bytearray_wide_ffi.o pkg : FilePath := do
  let srcJob ← bytearray_wide_ffi.c.fetch
  let oFile := pkg.buildDir / "c" / "bytearray_wide_ffi.o"
  -- -O2 is essential here: these are single-load/store hot-loop primitives
  -- whose lean.h helpers (lean_sarray_cptr, lean_is_exclusive, ...) only
  -- disappear under optimization; without it each "wide" op is a pile of
  -- outlined helper calls and loses to the runtime's own -O2 push/get.
  -- -DNDEBUG matches how the release Lean runtime itself is built: the
  -- lean.h asserts are debug-only checks, and these externs' bounds are
  -- carried by Lean-side proofs (+ the ZipTest/Wide conformance sweeps).
  -- `buildLeanO` + `ltoFlags`: see `copy_within_ffi.o` — with LTO these
  -- single-instruction externs inline into `countMatch`/`hash3` themselves.
  let hardArgs := #["-O2", "-DNDEBUG"] ++ (← ltoFlags) ++
    if Platform.isWindows then #[] else #["-fPIC"]
  buildLeanO oFile srcJob #[] hardArgs

extern_lib libbytearray_wide_ffi pkg := do
  let ffiO ← bytearray_wide_ffi.o.fetch
  let name := nameToStaticLib "bytearray_wide_ffi"
  buildStaticLib (pkg.staticLibDir / name) #[ffiO]

lean_lib ZipTest where
  globs := #[.submodules `ZipTest]

@[default_target]
lean_exe test where
  root := `ZipTest
