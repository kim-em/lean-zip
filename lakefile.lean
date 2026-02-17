import Lake
open System Lake DSL

/-- Run `pkg-config` and split the output into flags. Returns `#[]` on failure. -/
def pkgConfig (pkg : String) (flag : String) : IO (Array String) := do
  let out ← IO.Process.output { cmd := "pkg-config", args := #[flag, pkg] }
  if out.exitCode != 0 then return #[]
  return out.stdout.trim.splitOn " " |>.toArray

package «lean-zlib» where
  moreLinkArgs := #["-lz"]

lean_lib Zlib

input_file zlib_ffi.c where
  path := "c" / "zlib_ffi.c"
  text := true

target zlib_ffi.o pkg : FilePath := do
  let srcJob ← zlib_ffi.c.fetch
  let oFile := pkg.buildDir / "c" / "zlib_ffi.o"
  let cflags ← pkgConfig "zlib" "--cflags"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString] ++ cflags
  buildO oFile srcJob weakArgs #["-fPIC"] "cc"

extern_lib libzlib_ffi pkg := do
  let ffiO ← zlib_ffi.o.fetch
  let name := nameToStaticLib "zlib_ffi"
  buildStaticLib (pkg.staticLibDir / name) #[ffiO]

@[default_target]
lean_exe test where
  root := `Test
