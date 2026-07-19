import Lake
open System Lake DSL

/-! # lean-zip dev-only bench package

The Track D benchmarking and comparator apparatus lives here, out of the
shipped `lean-zip` library. It requires the parent library via a local
path (`require «lean-zip» from ".."`) and carries the comparator C shims
(`c/`), the miniz_oxide Rust crate (`rust/`), the three comparator
`extern_lib`s, and the eleven bench/sweep/fuzz executables plus their
conformance/fuzz test modules.

Building this package needs a Rust toolchain (cargo + rustc) for the
miniz_oxide shim and, optionally, `<libdeflate.h>` / `<zopfli.h>` for the
C-library comparators; each is auto-detected and falls back to a stub, so
`lake build` still works when a comparator toolchain is absent. -/

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
    auto-detect the optional libdeflate / zopfli comparator libraries. Returns
    `false` on any error so a missing library never breaks `lake build`. -/
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

/-! ### miniz_oxide comparator (Track D Phase 0c)

The Rust shim crate at `rust/miniz_oxide_shim/` is built lazily by an
`extern_lib` (see below). The C shim at `c/miniz_oxide_ffi.c` is always
compiled — when cargo is unavailable it falls back to a stub that raises
`IO.userError`, so plain `lake build` still works without a Rust
toolchain.

We use `MINIZ_OXIDE_DISABLE=1` to opt out, `MINIZ_OXIDE_LDFLAGS` to
override the link flags, and otherwise auto-detect cargo on `PATH`. -/

/-- Resolve the miniz_oxide crate directory relative to the process CWD.

    `moreLinkArgs`' `run_io` runs against the *invocation* CWD, which differs
    by how the bench package is driven: `cd bench && lake …` runs with CWD at
    `bench/` (so the crate is `rust/miniz_oxide_shim`), while `lake -d bench …`
    from the repo root leaves CWD there (so the crate is
    `bench/rust/miniz_oxide_shim`). `-d` sets the package dir but does not
    chdir. Probe both so every invocation pattern finds the crate. -/
def minizShimDir : IO FilePath := do
  let candidates : Array FilePath :=
    #["rust" / "miniz_oxide_shim", "bench" / "rust" / "miniz_oxide_shim"]
  for c in candidates do
    if (← (c / "Cargo.toml").pathExists) then return c
  return candidates[0]!

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
  let manifest := (← minizShimDir) / "Cargo.toml"
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

/-- The single miniz_oxide predicate that BOTH the C shim's `-DHAVE_MINIZ_OXIDE`
    compile flag and the executable link step consult, so the two never diverge.
    Returns `some flags` (the `-L`/`-l` flags for the built shim, or the
    explicit `MINIZ_OXIDE_LDFLAGS` override) exactly when the Rust shim is
    actually usable, and `none` when miniz is disabled OR cargo is present but
    the shim could not be built/located (a broken toolchain, a missing crate, or
    an unexpected CWD). Gating the `-D` on this — rather than on the cheaper
    `minizOxideEnabled` (cargo `--version`) — means the C shim only expects the
    Rust symbols when they will really be on the link line, so a failed/absent
    Rust build cleanly falls back to the stub instead of an unresolved-symbol
    link error. -/
def minizLinkFlags : IO (Option (Array String)) := do
  if !(← minizOxideEnabled) then return none
  if let some explicit := (← minizLdFlagsOverride) then return some explicit
  if (← buildMinizOxideRust) then
    let releaseDir := (← minizShimDir) / "target" / "release"
    return some #[s!"-L{releaseDir.toString}", "-lminiz_oxide_shim"]
  return none

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

/-- Compose the full `moreLinkArgs` list — zlib first (the parent library's
    load-bearing FFI, needed by the bench executables that link `Zip`), then
    the Track D comparators (miniz_oxide, libdeflate, zopfli) when enabled. We
    run cargo here so that the resulting `.a` exists by the time Lake links the
    bench executables. -/
def linkFlags : IO (Array String) := do
  let mut args ← zlibLinkFlags
  if let some minizFlags := (← minizLinkFlags) then
    args := args ++ minizFlags
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

/-- LTO link flags mirroring the parent lakefile's `ltoLinkFlags` (issue
    #2806, keep in sync with `../lakefile.lean`): on Linux the parent
    library's objects are LLVM bitcode, so the bench executables' links run
    the same LTO codegen at `-O3` — the bench binaries measure exactly what
    the shipped library's consumers link. `LEAN_ZIP_LTO=0` opts out. -/
def ltoLinkFlags : IO (Array String) := do
  if Platform.isWindows || Platform.isOSX then return #[]
  if (← IO.getEnv "LEAN_ZIP_LTO") == some "0" then return #[]
  return #["-flto", "-fno-semantic-interposition", "-O3"]

package «lean-zip-bench» where
  moreLinkArgs := run_io do return (← linkFlags) ++ (← ltoLinkFlags)

require «lean-zip» from ".."

-- Comparator FFI bindings (out of the `Zip.` namespace — `Zip` belongs to the
-- required parent library).
@[default_target]
lean_lib Bench where
  globs := #[.submodules `Bench]

-- Conformance + fuzz test modules for the comparators (moved out of the root
-- `ZipTest` library, which can no longer build them without the comparator
-- extern_libs). They keep their internal `namespace ZipTest.*` (a Lean
-- namespace, freely shared across packages) but live under the `BenchTests.*`
-- module path: a package cannot add modules under a required dependency's
-- library namespace (`ZipTest`), or Lake's `.submodules` glob would steal
-- resolution of the root's own `ZipTest.Helpers`. Reached transitively by
-- `bench-test` and the fuzz executables.
lean_lib BenchTests where
  globs := #[.submodules `BenchTests]

-- miniz_oxide FFI (Track D comparator)
input_file miniz_oxide_ffi.c where
  path := "c" / "miniz_oxide_ffi.c"
  text := true

target miniz_oxide_ffi.o pkg : FilePath := do
  let srcJob ← miniz_oxide_ffi.c.fetch
  let oFile := pkg.buildDir / "c" / "miniz_oxide_ffi.o"
  -- Gate `-DHAVE_MINIZ_OXIDE` on the SAME predicate the link step uses
  -- (`minizLinkFlags`), so the shim expects the Rust symbols exactly when
  -- they will be on the link line. Consulting only `minizOxideEnabled` here
  -- would let the shim reference Rust symbols that a failed/absent cargo
  -- build never links.
  let cflags := if (← minizLinkFlags).isSome then #["-DHAVE_MINIZ_OXIDE"] else #[]
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

-- Conformance + fuzz-compress test driver for the comparators.
@[default_target, test_driver]
lean_exe «bench-test» where
  root := `BenchTest

@[default_target]
lean_exe bench where
  root := `ZipBench

@[default_target]
lean_exe «bench-report» where
  root := `ZipBenchReport

@[default_target]
lean_exe «treefree-bench» where
  root := `ZipTreeFreeBench

@[default_target]
lean_exe «wide-store-bench» where
  root := `ZipWideStoreBench

@[default_target]
lean_exe «treefree-decode-bench» where
  root := `ZipTreeFreeDecodeBench

@[default_target]
lean_exe «ratio-sweep» where
  root := `ZipRatioSweep

@[default_target]
lean_exe «l1-attrib» where
  root := `ZipL1Attrib

@[default_target]
lean_exe «l1-sweep» where
  root := `ZipL1Sweep

@[default_target]
lean_exe «mid-sweep» where
  root := `ZipMidSweep

@[default_target]
lean_exe «lazy2-sweep» where
  root := `ZipLazy2Sweep

@[default_target]
lean_exe «gate-sweep» where
  root := `ZipGateSweep

@[default_target]
lean_exe «huff-bench» where
  root := `ZipHuffBench

@[default_target]
lean_exe «freq-fusion» where
  root := `ZipFreqFusion

-- Single-decoder inflate profiling driver: `decode` mode runs native inflate
-- alone, so a `perf record` of that process attributes cleanly (see bench/README.md).
@[default_target]
lean_exe «inflate-profile» where
  root := `ZipInflateProfile

@[default_target]
lean_exe fuzz_inflate where
  root := `ZipFuzzInflate

@[default_target]
lean_exe fuzz_handle_read where
  root := `ZipFuzzHandleRead

@[default_target]
lean_exe «csize-file» where
  root := `ZipCsizeFile

@[default_target]
lean_exe «rung4-accept» where
  root := `ZipRung4Accept
