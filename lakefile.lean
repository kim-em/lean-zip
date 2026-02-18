import Lake
open System Lake DSL

/-- Run `pkg-config` and split the output into flags. Returns `#[]` on failure. -/
def pkgConfig (pkg : String) (flag : String) : IO (Array String) := do
  let out ← IO.Process.output { cmd := "pkg-config", args := #[flag, pkg] }
  if out.exitCode != 0 then return #[]
  return out.stdout.trimAscii.toString.splitOn " " |>.toArray

/-- Get zlib include flags, respecting `ZLIB_CFLAGS` env var override. -/
def zlibCFlags : IO (Array String) := do
  if let some flags := (← IO.getEnv "ZLIB_CFLAGS") then
    return flags.trimAscii.toString.splitOn " " |>.toArray
  pkgConfig "zlib" "--cflags"

/-- Get zstd include flags, respecting `ZSTD_CFLAGS` env var override. -/
def zstdCFlags : IO (Array String) := do
  if let some flags := (← IO.getEnv "ZSTD_CFLAGS") then
    return flags.trimAscii.toString.splitOn " " |>.toArray
  pkgConfig "libzstd" "--cflags"

/-- Get combined link flags for zlib and zstd.
    Uses pkg-config to find library paths and links zstd statically to avoid
    glibc version issues with Lean's bundled toolchain. -/
def linkFlags : IO (Array String) := do
  -- zlib: dynamic is fine (simple, stable ABI)
  let zlibFlags ← pkgConfig "zlib" "--libs"
  -- zstd: get -L path from pkg-config, then link statically
  let zstdRaw ← pkgConfig "libzstd" "--libs"
  let mut flags := if zlibFlags.isEmpty then #["-lz"] else zlibFlags
  -- Extract -L flags from zstd, then add static linking
  let mut hasZstdPath := false
  for f in zstdRaw do
    if f.startsWith "-L" then
      flags := flags.push f
      hasZstdPath := true
  flags := flags ++ #["-Wl,-Bstatic", "-lzstd", "-Wl,-Bdynamic"]
  -- If no path from pkg-config and no env override, just try -lzstd dynamically
  if !hasZstdPath && zstdRaw.isEmpty then
    flags := flags.pop |>.pop |>.pop |>.push "-lzstd"
  return flags

package «lean-zip» where
  moreLinkArgs := run_io linkFlags

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

-- zstd FFI
input_file zstd_ffi.c where
  path := "c" / "zstd_ffi.c"
  text := true

target zstd_ffi.o pkg : FilePath := do
  let srcJob ← zstd_ffi.c.fetch
  let oFile := pkg.buildDir / "c" / "zstd_ffi.o"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString] ++ (← zstdCFlags)
  let hardArgs := if Platform.isWindows then #[] else #["-fPIC"]
  buildO oFile srcJob weakArgs hardArgs "cc"

extern_lib libzstd_ffi pkg := do
  let ffiO ← zstd_ffi.o.fetch
  let name := nameToStaticLib "zstd_ffi"
  buildStaticLib (pkg.staticLibDir / name) #[ffiO]

@[default_target]
lean_exe test where
  root := `Test
