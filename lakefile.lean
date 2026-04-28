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

/-- Get zopfli include flags, respecting `ZOPFLI_CFLAGS` env var override.
    Zopfli on Nix does not ship a `.pc` file, so we rely on `NIX_CFLAGS_COMPILE`
    being inherited by `cc` for the include path on NixOS. -/
def zopfliCFlags : IO (Array String) := do
  if let some flags := (← IO.getEnv "ZOPFLI_CFLAGS") then
    return splitFlags flags.trimAscii.toString
  let flags ← pkgConfig "zopfli" "--cflags"
  if !flags.isEmpty then
    return flags
  return #[]

/-- Extract `-L` library paths from `NIX_LDFLAGS` (set by nix-shell). -/
def nixLdLibPaths : IO (Array String) := do
  let some val := (← IO.getEnv "NIX_LDFLAGS") | return #[]
  return val.splitOn " " |>.filter (·.startsWith "-L") |>.toArray

/-- Convert `-L<path>` flags into `-Wl,-rpath,<path>` so the linked binary
    can find the dynamic libraries at runtime even outside the nix-shell. -/
def nixLdRpathFlags : IO (Array String) := do
  let paths ← nixLdLibPaths
  return paths.map fun lflag =>
    -- Strip the leading "-L" and re-emit as a runtime rpath.
    let path : String := (lflag.toSubstring.drop 2).toString
    "-Wl,-rpath," ++ path

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

/-- Get link flags for zopfli.
    Tries `ZOPFLI_LDFLAGS`, then pkg-config, then `NIX_LDFLAGS` + `-lzopfli -lm`.
    Zopfli on Nix does not ship a `.pc` file, so the Nix fallback is the
    primary working path on NixOS. We always include `-lm` because libzopfli
    references `log` from libm.

    We pass `-Wl,--allow-shlib-undefined` because Lean's bundled toolchain
    ships an old glibc (only `log@GLIBC_2.2.5`) while a Nix-built libzopfli
    links against `log@GLIBC_2.29`. The strict default of `ld.lld`
    (`--no-allow-shlib-undefined`) refuses such links even though the
    dynamic loader resolves the symbol at runtime via libzopfli's RUNPATH. -/
def zopfliLinkFlags : IO (Array String) := do
  let lazyFlag := #["-Wl,--allow-shlib-undefined"]
  if let some flags := (← IO.getEnv "ZOPFLI_LDFLAGS") then
    return splitFlags flags.trimAscii.toString
  let zopfliFlags ← pkgConfig "zopfli" "--libs"
  if !zopfliFlags.isEmpty && zopfliFlags.any (·.startsWith "-L") then
    return zopfliFlags ++ #["-lm"] ++ lazyFlag
  let libPaths ← nixLdLibPaths
  if !zopfliFlags.isEmpty then
    return libPaths ++ zopfliFlags ++ #["-lm"] ++ lazyFlag
  return libPaths ++ #["-lzopfli", "-lm"] ++ lazyFlag

/-- Combined link flags for the package (zlib + zopfli) plus runtime
    rpath entries so the binary can locate the shared libraries outside of
    nix-shell. -/
def linkFlags : IO (Array String) := do
  return (← zlibLinkFlags) ++ (← zopfliLinkFlags) ++ (← nixLdRpathFlags)

package «lean-zip» where
  moreLinkArgs := run_io linkFlags
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

-- zopfli FFI (encode-only DEFLATE quality ceiling)
input_file zopfli_ffi.c where
  path := "c" / "zopfli_ffi.c"
  text := true

target zopfli_ffi.o pkg : FilePath := do
  let srcJob ← zopfli_ffi.c.fetch
  let oFile := pkg.buildDir / "c" / "zopfli_ffi.o"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString] ++ (← zopfliCFlags)
  let hardArgs := if Platform.isWindows then #[] else #["-fPIC"]
  buildO oFile srcJob weakArgs hardArgs "cc"

extern_lib libzopfli_ffi pkg := do
  let ffiO ← zopfli_ffi.o.fetch
  let name := nameToStaticLib "zopfli_ffi"
  buildStaticLib (pkg.staticLibDir / name) #[ffiO]

lean_lib ZipTest where
  globs := #[.submodules `ZipTest]

@[default_target]
lean_exe test where
  root := `ZipTest

lean_exe bench where
  root := `ZipBench

lean_exe fuzz_inflate where
  root := `ZipFuzzInflate
