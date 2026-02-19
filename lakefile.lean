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

/-- Extract `-L` library paths from `NIX_LDFLAGS` (set by nix-shell). -/
def nixLdLibPaths : IO (Array String) := do
  let some val := (← IO.getEnv "NIX_LDFLAGS") | return #[]
  return val.splitOn " " |>.filter (·.startsWith "-L") |>.toArray

/-- Check whether `libzstd.a` exists in any of the given `-L` directories. -/
def hasStaticZstd (libPaths : Array String) : IO Bool := do
  for p in libPaths do
    let dir : System.FilePath := ⟨(p.drop 2).toString⟩  -- strip "-L"
    let path := dir / "libzstd.a"
    if (← path.pathExists) then return true
  return false

/-- Get combined link flags for zlib and zstd.
    Tries pkg-config, then `NIX_LDFLAGS`, then bare `-lz`/`-lzstd`.
    Links zstd statically when possible to avoid glibc version mismatches
    with Lean's bundled toolchain sysroot. -/
def linkFlags : IO (Array String) := do
  let libPaths ← nixLdLibPaths
  let zlibFlags ← pkgConfig "zlib" "--libs"
  let zstdFlags ← pkgConfig "libzstd" "--libs"
  -- Prefer static zstd to avoid glibc version mismatches with Lean's sysroot.
  let allLibPaths := libPaths ++
    (zlibFlags ++ zstdFlags).filter (·.startsWith "-L")
  if (← hasStaticZstd allLibPaths) then
    let zstdLibPaths := zstdFlags.filter (·.startsWith "-L")
    let zlibEffective := if zlibFlags.isEmpty then libPaths ++ #["-lz"] else zlibFlags
    return zlibEffective ++ zstdLibPaths ++
      #["-Wl,-Bstatic", "-lzstd", "-Wl,-Bdynamic"]
  if !zlibFlags.isEmpty && !zstdFlags.isEmpty then
    -- Dynamic zstd may reference newer glibc symbols than Lean's sysroot provides.
    -- Allow unresolved shlib symbols; the system libc provides them at runtime.
    return zlibFlags ++ zstdFlags ++ #["-Wl,--allow-shlib-undefined"]
  -- pkg-config unavailable — try NIX_LDFLAGS for -L paths
  let mut flags := libPaths ++ #["-lz", "-lzstd"]
  flags := flags ++ #["-Wl,--allow-shlib-undefined"]
  return flags

package «lean-zip» where
  moreLinkArgs := run_io linkFlags
  testDriver := "test"

lean_lib ZipForStd where
  globs := #[.submodules `ZipForStd]

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

-- IO FFI (Handle seek/fileSize shims — no external library deps)
input_file io_ffi.c where
  path := "c" / "io_ffi.c"
  text := true

target io_ffi.o pkg : FilePath := do
  let srcJob ← io_ffi.c.fetch
  let oFile := pkg.buildDir / "c" / "io_ffi.o"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  let hardArgs := if Platform.isWindows then #[] else #["-fPIC"]
  buildO oFile srcJob weakArgs hardArgs "cc"

extern_lib libio_ffi pkg := do
  let ffiO ← io_ffi.o.fetch
  let name := nameToStaticLib "io_ffi"
  buildStaticLib (pkg.staticLibDir / name) #[ffiO]

lean_lib ZipTest where
  globs := #[.submodules `ZipTest]

@[default_target]
lean_exe test where
  root := `ZipTest
