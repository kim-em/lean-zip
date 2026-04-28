# Bench harness — comparator toolchain notes

This file documents the platform requirements and opt-in/opt-out
controls for the Track D bench comparators (PLAN.md §Track D). For the
bench CLI itself see [`ZipBench.lean`](ZipBench.lean) and the
`Operations:` listing in its header docstring.

## Comparator matrix

| Comparator   | Phase | Toolchain required                      | Default in `lake build` | Disable knob              |
|--------------|-------|------------------------------------------|--------------------------|---------------------------|
| zlib         | A     | system zlib + headers (`pkg-config`)     | required                 | n/a (load-bearing)        |
| miniz_oxide  | 0c    | `cargo` + `rustc` (Rust ≥ 1.74)          | auto-on if cargo on PATH | `MINIZ_OXIDE_DISABLE=1`   |
| libdeflate   | 0a    | system `libdeflate` (separate issue)     | tracked separately       | n/a                       |
| zopfli       | 0b    | `zopfli` CLI / library (separate issue)  | tracked separately       | n/a                       |

Only the miniz_oxide column is in scope for this file; the other rows
are placeholders so the matrix is complete when phases 0a/0b land.

## miniz_oxide (Track D Phase 0c)

**Crate:** `rust/miniz_oxide_shim/` — a `staticlib` Cargo crate that
wraps `miniz_oxide` v0.8 with a tiny C-ABI surface
(`lean_miniz_oxide_compress` / `_decompress` / `_free`). The Lean side
calls into this through [`c/miniz_oxide_ffi.c`](c/miniz_oxide_ffi.c)
and exposes [`Zip/MinizOxide.lean`](Zip/MinizOxide.lean).

**Bench operations:** `compress-miniz` and `inflate-miniz`, e.g.

```
lake exe bench compress-miniz 65536 text 6
hyperfine 'lake exe bench inflate-miniz 1048576 prng 6'
```

### Build-time auto-detection

`lakefile.lean` detects cargo at configure time:

* If `MINIZ_OXIDE_DISABLE=1` is set, the comparator is skipped.
* If `MINIZ_OXIDE_LDFLAGS` is set, those flags are appended verbatim
  (overrides cargo auto-detection — useful when packaging against a
  pre-built static library).
* Otherwise `cargo --version` is probed; if it succeeds, the lakefile
  shells out to `cargo build --release --manifest-path
  rust/miniz_oxide_shim/Cargo.toml` and links the resulting
  `libminiz_oxide_shim.a`.

When the comparator is disabled the C shim still compiles, but
`MinizOxide.compress` / `MinizOxide.decompress` raise
`IO.userError` containing `"miniz_oxide: not built with Rust support"`
at runtime. The smoke tests in [`ZipTest/MinizOxide.lean`](ZipTest/MinizOxide.lean)
treat that exact substring as a clean skip, so `lake exe test` keeps
passing on toolchains without Rust.

### Verified platforms

| Platform                         | Status        | Notes                                                  |
|----------------------------------|---------------|--------------------------------------------------------|
| NixOS (`shell.nix` provisioned)  | verified      | `cargo`+`rustc` come from `pkgs.cargo`, `pkgs.rustc`.  |
| Bench machine `chungus`          | verified      | Same NixOS environment via `nix-shell`.                |
| Linux distros with system Rust   | expected OK   | Any cargo ≥ 1.74; not yet smoke-tested in CI.          |
| macOS                            | expected OK   | Requires `rustup` / homebrew Rust on `PATH`.           |
| Windows                          | not tested    | Should work via MSVC + cargo, but untried.             |

If you build on a platform that should be in this matrix and the
comparator works, please update this table in a follow-up PR.

### Re-running cargo manually

The lakefile invokes cargo lazily; if you tweak the Rust shim and want
to force a rebuild without rerunning `lake build`:

```
cargo build --release --manifest-path rust/miniz_oxide_shim/Cargo.toml
```

The resulting `.a` lives at
`rust/miniz_oxide_shim/target/release/libminiz_oxide_shim.a` and is the
exact path Lake links from. `lake clean` does **not** purge cargo's
target directory — use `cargo clean --manifest-path …` for that.
