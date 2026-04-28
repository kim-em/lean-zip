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

/-- Prefer an explicit libdeflate linker override when supplied by the environment. -/
def libdeflateLdFlagsOverride : IO (Option (Array String)) := do
  return (← IO.getEnv "LIBDEFLATE_LDFLAGS") |>.map (splitFlags ·.trimAscii.toString)

/-- Get libdeflate include flags, respecting `LIBDEFLATE_CFLAGS` env var override. -/
def libdeflateCFlags : IO (Array String) := do
  if let some flags := (← IO.getEnv "LIBDEFLATE_CFLAGS") then
    return splitFlags flags.trimAscii.toString
  let flags ← pkgConfig "libdeflate" "--cflags"
  if !flags.isEmpty then
    return flags
  if let some sdk := (← macSdkPath) then
    return #["-I", (sdk / "usr/include").toString]
  return #[]

/-- Get link flags for zlib.
    Tries `ZLIB_LDFLAGS`, then pkg-config, then macOS SDK / Nix fallbacks. -/
def linkFlags : IO (Array String) := do
  let zFlags ← do
    if let some flags := (← zlibLdFlagsOverride) then
      pure flags
    else
      let libPaths ← nixLdLibPaths
      let zlibFlags ← pkgConfig "zlib" "--libs"
      if !zlibFlags.isEmpty && zlibFlags.any (·.startsWith "-L") then
        pure zlibFlags
      else if let some sdk := (← macSdkPath) then
        pure #["-L", (sdk / "usr/lib").toString, "-lz"]
      else if !zlibFlags.isEmpty then
        pure (libPaths ++ zlibFlags)
      else
        pure (libPaths ++ #["-lz"])
  let dFlags ← do
    if let some flags := (← libdeflateLdFlagsOverride) then
      pure flags
    else
      let libPaths ← nixLdLibPaths
      let dlibFlags ← pkgConfig "libdeflate" "--libs"
      if !dlibFlags.isEmpty && dlibFlags.any (·.startsWith "-L") then
        pure dlibFlags
      else if let some sdk := (← macSdkPath) then
        pure #["-L", (sdk / "usr/lib").toString, "-ldeflate"]
      else if !dlibFlags.isEmpty then
        pure (libPaths ++ dlibFlags)
      else
        pure (libPaths ++ #["-ldeflate"])
  return zFlags ++ dFlags

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

-- libdeflate FFI (Track D Phase 0a comparator)
input_file libdeflate_ffi.c where
  path := "c" / "libdeflate_ffi.c"
  text := true

target libdeflate_ffi.o pkg : FilePath := do
  let srcJob ← libdeflate_ffi.c.fetch
  let oFile := pkg.buildDir / "c" / "libdeflate_ffi.o"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString] ++ (← libdeflateCFlags)
  let hardArgs := if Platform.isWindows then #[] else #["-fPIC"]
  buildO oFile srcJob weakArgs hardArgs "cc"

extern_lib libLibdeflate_ffi pkg := do
  let ffiO ← libdeflate_ffi.o.fetch
  let name := nameToStaticLib "libdeflate_ffi"
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
