import Lake
open System Lake DSL

/-- Run `pkg-config` and split the output into flags. Returns `#[]` on failure. -/
def pkgConfig (pkg : String) (flag : String) : IO (Array String) := do
  let out ← IO.Process.output { cmd := "pkg-config", args := #[flag, pkg] }
  if out.exitCode != 0 then return #[]
  return out.stdout.trimAscii.toString.splitOn " " |>.filter (· ≠ "") |>.toArray

/-- Get zlib include flags, respecting `ZLIB_CFLAGS` env var override. -/
def zlibCFlags : IO (Array String) := do
  if let some flags := (← IO.getEnv "ZLIB_CFLAGS") then
    return flags.trimAscii.toString.splitOn " " |>.filter (· ≠ "") |>.toArray
  pkgConfig "zlib" "--cflags"

/-- Get zstd include flags, respecting `ZSTD_CFLAGS` env var override. -/
def zstdCFlags : IO (Array String) := do
  if let some flags := (← IO.getEnv "ZSTD_CFLAGS") then
    return flags.trimAscii.toString.splitOn " " |>.filter (· ≠ "") |>.toArray
  pkgConfig "libzstd" "--cflags"

/-- Extract `-L` library paths from `NIX_LDFLAGS` (set by nix-shell). -/
def nixLdLibPaths : IO (Array String) := do
  let some val := (← IO.getEnv "NIX_LDFLAGS") | return #[]
  return val.splitOn " " |>.filter (·.startsWith "-L") |>.toArray

/-- Get the library directory for a pkg-config package (e.g. `/usr/lib/x86_64-linux-gnu`). -/
def pkgConfigLibDir (pkg : String) : IO (Option String) := do
  let out ← IO.Process.output { cmd := "pkg-config", args := #["--variable=libdir", pkg] }
  if out.exitCode != 0 then return none
  let dir := out.stdout.trimAscii.toString
  if dir.isEmpty then return none
  return some dir

/-- Find `libzstd.a` in the given `-L` directories, via pkg-config libdir,
    or via common system library directories. Returns the full path if found. -/
def findStaticZstd (libPaths : Array String) : IO (Option System.FilePath) := do
  -- Check -L directories from flags
  for p in libPaths do
    let dir : System.FilePath := ⟨(p.drop 2).toString⟩  -- strip "-L"
    let path := dir / "libzstd.a"
    if (← path.pathExists) then return some path
  -- Check pkg-config reported libdir
  if let some dir := (← pkgConfigLibDir "libzstd") then
    let path := (⟨dir⟩ : System.FilePath) / "libzstd.a"
    if (← path.pathExists) then return some path
  -- Check common system library directories (pkg-config libdir may not match
  -- the actual multiarch path, e.g. returns /usr/lib but lib is in
  -- /usr/lib/x86_64-linux-gnu on Ubuntu)
  for dir in #["/usr/lib/x86_64-linux-gnu", "/usr/lib/aarch64-linux-gnu",
               "/usr/lib64", "/usr/local/lib"] do
    let path := (⟨dir⟩ : System.FilePath) / "libzstd.a"
    if (← path.pathExists) then return some path
  return none

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
  if let some zstdStaticPath := (← findStaticZstd allLibPaths) then
    let zlibEffective := if zlibFlags.isEmpty then libPaths ++ #["-lz"] else zlibFlags
    -- On macOS (lld), -Bstatic/-Bdynamic aren't supported; link dynamically instead.
    -- Also need SDK library path since Lean's sysroot hides system libs.
    if System.Platform.isOSX then
      let sdkPath := (← IO.Process.output {
        cmd := "xcrun", args := #["--show-sdk-path"] }).stdout.trimAscii.toString
      return zlibEffective ++ allLibPaths ++
        #["-lzstd", s!"-L{sdkPath}/usr/lib"]
    else
      -- Pass the full path to libzstd.a directly instead of -L + -lzstd.
      -- Using -L would add the system lib dir to the search path, causing
      -- the linker to find system glibc CRT objects instead of the ones in
      -- Lean's sysroot (leading to __libc_csu_init undefined errors).
      -- Preserve any transitive flags from zstd (e.g. -pthread) but drop
      -- -L and -lzstd since we're linking the static lib directly.
      let zstdExtra := zstdFlags.filter (fun f =>
        !f.startsWith "-L" && !f.startsWith "-lzstd" && f != "-lzstd")
      return zlibEffective ++ #[zstdStaticPath.toString] ++ zstdExtra
  if !zlibFlags.isEmpty && !zstdFlags.isEmpty then
    -- Dynamic zstd may reference newer glibc symbols than Lean's sysroot provides.
    -- Allow unresolved shlib symbols; the system libc provides them at runtime.
    -- Pass full path to the shared lib to avoid -L polluting the search path.
    if let some dir := (← pkgConfigLibDir "libzstd") then
      let soPath := (⟨dir⟩ : System.FilePath) / "libzstd.so"
      if (← soPath.pathExists) then
        return zlibFlags ++ #[soPath.toString, "-Wl,--allow-shlib-undefined"]
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

lean_exe bench where
  root := `ZipBench
