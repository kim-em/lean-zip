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

/-- Probe whether the C compiler can resolve `#include <header>` (using the
    ambient include paths, e.g. nix-shell's `NIX_CFLAGS_COMPILE`). Used to
    auto-detect optional Track D comparator libraries. Returns `false` on any
    error so a missing library never breaks `lake build`. -/
def cHeaderProbe (header : String) : IO Bool := do
  let probe : FilePath := ⟨"/tmp/lean-zip-probe-" ++ header.replace "/" "-" ++ ".c"⟩
  let src := "#include <" ++ header ++ ">\nint main(void) { return 0; }\n"
  try
    IO.FS.writeFile probe src
    let out ← IO.Process.output { cmd := "cc", args := #["-fsyntax-only", probe.toString] }
    try IO.FS.removeFile probe catch _ => pure ()
    return out.exitCode == 0
  catch _ => return false

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

/-! ### miniz_oxide comparator (Track D Phase 0c)

The Rust shim crate at `rust/miniz_oxide_shim/` is built lazily by an
`extern_lib` (see below). The C shim at `c/miniz_oxide_ffi.c` is always
compiled — when cargo is unavailable it falls back to a stub that raises
`IO.userError`, so plain `lake build` still works without a Rust
toolchain.

We use `MINIZ_OXIDE_DISABLE=1` to opt out, `MINIZ_OXIDE_LDFLAGS` to
override the link flags, and otherwise auto-detect cargo on `PATH`. -/

/-- Path to the Rust shim's expected static-library output. -/
def minizRustLib : FilePath :=
  "rust" / "miniz_oxide_shim" / "target" / "release" / "libminiz_oxide_shim.a"

/-- Honor a `MINIZ_OXIDE_LDFLAGS` env override the same way zlib does. -/
def minizLdFlagsOverride : IO (Option (Array String)) := do
  return (← IO.getEnv "MINIZ_OXIDE_LDFLAGS") |>.map (splitFlags ·.trimAscii.toString)

/-- Decide whether to enable the miniz_oxide comparator. Returns `true` iff
    `MINIZ_OXIDE_DISABLE` is unset and either `MINIZ_OXIDE_LDFLAGS` is
    provided or cargo is on `PATH`. The decision is intentionally cached
    per `lake build` invocation via `IO`-only checks (no extra build
    state). -/
def minizOxideEnabled : IO Bool := do
  if (← IO.getEnv "MINIZ_OXIDE_DISABLE").isSome then return false
  if (← IO.getEnv "MINIZ_OXIDE_LDFLAGS").isSome then return true
  let out ← IO.Process.output { cmd := "cargo", args := #["--version"] }
  return out.exitCode == 0

/-- Build (or refresh) the Rust shim via `cargo build --release`. Returns
    `false` (and prints a warning) if cargo fails. -/
def buildMinizOxideRust : IO Bool := do
  let manifest := ("rust" : FilePath) / "miniz_oxide_shim" / "Cargo.toml"
  unless (← manifest.pathExists) do return false
  let out ← IO.Process.output {
    cmd := "cargo"
    args := #["build", "--release", "--manifest-path", manifest.toString]
  }
  if out.exitCode != 0 then
    IO.eprintln s!"warning: miniz_oxide cargo build failed:\n{out.stderr}\n\
                    miniz_oxide comparator will be disabled."
    return false
  return true

/-! ### libdeflate / zopfli comparators (Track D reference comparators)

Both are plain C libraries (no Rust shim). The C shims at `c/libdeflate_ffi.c`
and `c/zopfli_ffi.c` are always compiled — gated on `HAVE_LIBDEFLATE` /
`HAVE_ZOPFLI` — falling back to `IO.userError` stubs when the library is absent,
so plain `lake build` still works. `*_DISABLE=1` opts out; `*_LDFLAGS` overrides
the link flags; otherwise the header is auto-probed. -/

/-- Enable libdeflate iff `LIBDEFLATE_DISABLE` is unset and either
    `LIBDEFLATE_LDFLAGS` is set or `<libdeflate.h>` is resolvable. -/
def libdeflateEnabled : IO Bool := do
  if (← IO.getEnv "LIBDEFLATE_DISABLE").isSome then return false
  if (← IO.getEnv "LIBDEFLATE_LDFLAGS").isSome then return true
  cHeaderProbe "libdeflate.h"

/-- Enable zopfli iff `ZOPFLI_DISABLE` is unset and either `ZOPFLI_LDFLAGS` is
    set or `<zopfli.h>` is resolvable. -/
def zopfliEnabled : IO Bool := do
  if (← IO.getEnv "ZOPFLI_DISABLE").isSome then return false
  if (← IO.getEnv "ZOPFLI_LDFLAGS").isSome then return true
  cHeaderProbe "zopfli.h"

/-- Link flags for a system C library: an explicit `<NAME>_LDFLAGS` override, or
    the nix `-L` paths plus matching `-rpath` (Lake links with the Lean
    toolchain clang, which does not inject nix's runtime search paths, so the
    store dirs must be baked in as rpath) plus `-l<lib>`. -/
def sysLibLinkFlags (envVar lib : String) : IO (Array String) := do
  if let some explicit := (← IO.getEnv envVar) then
    return splitFlags explicit.trimAscii.toString
  let lpaths ← nixLdLibPaths
  let rpaths := lpaths.filterMap fun s =>
    if s.startsWith "-L" then some ("-Wl,-rpath," ++ s.drop 2) else none
  return lpaths ++ rpaths ++ #["-l" ++ lib]

/-- Compose the full `moreLinkArgs` list — zlib first, then the Track D
    comparators (miniz_oxide, libdeflate, zopfli) when enabled. We run cargo
    here so that the resulting `.a` exists by the time Lake links the
    test/bench executables. -/
def linkFlags : IO (Array String) := do
  let mut args ← zlibLinkFlags
  if (← minizOxideEnabled) then
    if let some explicit := (← minizLdFlagsOverride) then
      args := args ++ explicit
    else if (← buildMinizOxideRust) then
      args := args ++ #[s!"-L{(minizRustLib.parent.getD ".").toString}",
                        "-lminiz_oxide_shim"]
  if (← libdeflateEnabled) then
    args := args ++ (← sysLibLinkFlags "LIBDEFLATE_LDFLAGS" "deflate")
  if (← zopfliEnabled) then
    -- libzopfli.so references `log` from libm but leaves it for the executable
    -- to provide. Force libm into the exe's NEEDED (defeating `--as-needed`)
    -- and relax lld's `--no-allow-shlib-undefined` so the link succeeds.
    args := args ++ (← sysLibLinkFlags "ZOPFLI_LDFLAGS" "zopfli")
            ++ #["-Wl,--no-as-needed", "-lm", "-Wl,--as-needed",
                 "-Wl,--allow-shlib-undefined"]
  return args

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
  let hardArgs := if Platform.isWindows then #[] else #["-fPIC"]
  buildO oFile srcJob weakArgs hardArgs "cc"

extern_lib libbytearray_wide_ffi pkg := do
  let ffiO ← bytearray_wide_ffi.o.fetch
  let name := nameToStaticLib "bytearray_wide_ffi"
  buildStaticLib (pkg.staticLibDir / name) #[ffiO]

-- miniz_oxide FFI (Track D comparator)
input_file miniz_oxide_ffi.c where
  path := "c" / "miniz_oxide_ffi.c"
  text := true

target miniz_oxide_ffi.o pkg : FilePath := do
  let srcJob ← miniz_oxide_ffi.c.fetch
  let oFile := pkg.buildDir / "c" / "miniz_oxide_ffi.o"
  -- Mirror `minizOxideEnabled` so the C shim's `-DHAVE_MINIZ_OXIDE`
  -- decision matches the link step in `linkFlags`. Without this, a
  -- `MINIZ_OXIDE_DISABLE=1` rebuild would compile the shim expecting
  -- the Rust symbols but link without them.
  let cflags := if (← minizOxideEnabled) then #["-DHAVE_MINIZ_OXIDE"] else #[]
  let weakArgs := #["-I", (← getLeanIncludeDir).toString] ++ cflags
  let hardArgs := if Platform.isWindows then #[] else #["-fPIC"]
  buildO oFile srcJob weakArgs hardArgs "cc"

extern_lib libminiz_oxide_ffi pkg := do
  let ffiO ← miniz_oxide_ffi.o.fetch
  let name := nameToStaticLib "miniz_oxide_ffi"
  buildStaticLib (pkg.staticLibDir / name) #[ffiO]

-- libdeflate FFI (Track D comparator)
input_file libdeflate_ffi.c where
  path := "c" / "libdeflate_ffi.c"
  text := true

target libdeflate_ffi.o pkg : FilePath := do
  let srcJob ← libdeflate_ffi.c.fetch
  let oFile := pkg.buildDir / "c" / "libdeflate_ffi.o"
  let cflags := if (← libdeflateEnabled) then #["-DHAVE_LIBDEFLATE"] else #[]
  let weakArgs := #["-I", (← getLeanIncludeDir).toString] ++ cflags
  let hardArgs := if Platform.isWindows then #[] else #["-fPIC"]
  buildO oFile srcJob weakArgs hardArgs "cc"

extern_lib liblibdeflate_ffi pkg := do
  let ffiO ← libdeflate_ffi.o.fetch
  let name := nameToStaticLib "libdeflate_ffi"
  buildStaticLib (pkg.staticLibDir / name) #[ffiO]

-- zopfli FFI (Track D comparator)
input_file zopfli_ffi.c where
  path := "c" / "zopfli_ffi.c"
  text := true

target zopfli_ffi.o pkg : FilePath := do
  let srcJob ← zopfli_ffi.c.fetch
  let oFile := pkg.buildDir / "c" / "zopfli_ffi.o"
  let cflags := if (← zopfliEnabled) then #["-DHAVE_ZOPFLI"] else #[]
  let weakArgs := #["-I", (← getLeanIncludeDir).toString] ++ cflags
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

lean_exe «bench-report» where
  root := `ZipBenchReport

lean_exe «treefree-bench» where
  root := `ZipTreeFreeBench

lean_exe «treefree-decode-bench» where
  root := `ZipTreeFreeDecodeBench

lean_exe «ratio-sweep» where
  root := `ZipRatioSweep

lean_exe «l1-attrib» where
  root := `ZipL1Attrib

lean_exe «l1-sweep» where
  root := `ZipL1Sweep

lean_exe «mid-sweep» where
  root := `ZipMidSweep

lean_exe fuzz_inflate where
  root := `ZipFuzzInflate

lean_exe fuzz_handle_read where
  root := `ZipFuzzHandleRead
