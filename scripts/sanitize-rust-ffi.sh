#!/usr/bin/env bash
#
# sanitize-rust-ffi.sh -- build and run the lean-zip miniz_oxide
# Rust shim under ASan.  [Skeleton; recipe body is TODO.]
#
# Scope: c/miniz_oxide_ffi.c + libminiz_oxide_shim.a
# (rust/miniz_oxide_shim/) only.  This is a *sibling* recipe to
# scripts/sanitize-ffi.sh (which targets c/zlib_ffi.c) -- the two
# scripts are intentionally split because their toolchain
# requirements differ:
#
#   * sanitize-ffi.sh requires a GCC-family `cc` with libasan.so /
#     libubsan.so resolvable via `cc -print-file-name=libasan.so`
#     (Linux-only in practice).
#   * sanitize-rust-ffi.sh requires a *nightly* Rust toolchain with
#     `RUSTFLAGS="-Zsanitizer=address"` support
#     (`cargo +nightly`).
#
# This script does NOT instrument c/zlib_ffi.c (sanitize-ffi.sh's
# job) and does NOT instrument the Lean runtime (no analogue
# exists; the Lean runtime is the project's *Lean Runtime* TCB
# row, not this row's surface).
#
# UBSan support: explicitly *future*.  Rust nightly's
# `-Zsanitizer=undefined` is less stable than `-Zsanitizer=address`
# (limited platform support, intermittent ABI churn), and a
# clean ASan-led pass matches the precedent set by
# sanitize-ffi.sh (which is also ASan-led, with UBSan layered on
# top once ASan was clean).
#
# This is a *skeleton*: the environment guard is load-bearing and
# returns exit 2 on hosts without nightly Rust on `PATH`, which is
# the entire current macOS-host coordination point.  The body
# (the actual `cargo +nightly build --release` + Lean smoke-driver
# invocation) is a single TODO-marked block that exits 1 with a
# clear "skeleton" message so callers cannot mistake an
# unfilled-recipe run for a clean run.  Filling in the recipe body
# is tracked as a follow-up issue, gated on a Linux + nightly-Rust
# worker host.
#
# See also: SECURITY_INVENTORY.md `miniz_oxide via Rust` ->
# *Missing work* bullet 1, and the precedent recipe shape in
# scripts/sanitize-ffi.sh.

set -euo pipefail

usage() {
  cat <<'EOF'
Usage: scripts/sanitize-rust-ffi.sh [--help]

Build and run the miniz_oxide Rust shim + its C-ABI shim
(rust/miniz_oxide_shim/ + c/miniz_oxide_ffi.c) under ASan.

[Skeleton.] This script is structurally complete but the recipe
body is currently TODO.  The environment guard (nightly Rust on
PATH) is load-bearing: hosts without `cargo +nightly` exit 2
cleanly, so this script can be safely invoked from any host
during scaffolding / coordination phases without producing a
misleading "pass".

Intended recipe shape (filled in by a follow-up issue):

  1. cargo +nightly build --release in rust/miniz_oxide_shim/
     with `RUSTFLAGS="-Zsanitizer=address"`.
  2. Surface the instrumented `libminiz_oxide_shim.a` via
     MINIZ_OXIDE_LDFLAGS so lakefile.lean's miniz_oxide-detection
     picks it up at link time.
  3. lake -R clean && lake -R build (`-R` re-elaborates the
     package configuration so the new MINIZ_OXIDE_LDFLAGS is
     re-read instead of the compiled-config cache).
  4. Run a small Lean driver that exercises the smoke-test
     inputs from ZipTest/MinizOxide.lean (miniz<->miniz,
     miniz->zlib, zlib->miniz, level-0 stored, empty input,
     maxDecompressedSize cap) under
     ASAN_OPTIONS="abort_on_error=1:detect_leaks=0".
  5. Any sanitizer report exits non-zero.

Environment requirements:
  * A nightly Rust toolchain on PATH (`cargo +nightly --version`
    must exit 0).  Install via:
        rustup toolchain install nightly
  * Run from the project root.

UBSan support: explicitly future.  Rust nightly's
`-Zsanitizer=undefined` is less stable than ASan and is not
covered by this skeleton.

Out of scope:
  * `c/zlib_ffi.c` instrumentation (handled by
    scripts/sanitize-ffi.sh).
  * Linking the ASan-instrumented `libminiz_oxide_shim.a` into
    scripts/fuzz-inflate.sh (a separate, third issue).
  * Lean runtime instrumentation (no analogue; tracked under the
    Lean Runtime TCB row, not this one).

Exit codes:
  0  recipe completed cleanly (currently unreachable -- the body
     is TODO; will become reachable once the recipe lands).
  1  skeleton placeholder body fired (env guard passed but
     recipe body is not yet implemented), or sanitizer report.
  2  environment requirements not met (cargo / nightly Rust
     missing) or invalid invocation.
EOF
}

case "${1:-}" in
  -h|--help)
    usage
    exit 0
    ;;
  "")
    ;;
  *)
    echo "error: unknown argument '$1'" >&2
    usage >&2
    exit 2
    ;;
esac

if [[ ! -f lakefile.lean ]]; then
  echo "error: run from the project root (lakefile.lean not found)" >&2
  exit 2
fi

# Environment guard: nightly Rust on PATH.
#
# Mirrors sanitize-ffi.sh's `cc -print-file-name=libasan.so`
# absolute-path check: any host without the required toolchain
# exits 2 cleanly so the skeleton can be safely invoked from any
# worker host during the scaffolding / coordination phase.
if ! command -v cargo >/dev/null 2>&1; then
  echo "error: cargo not found on PATH." >&2
  echo "       Install Rust via rustup (https://rustup.rs/) and add" >&2
  echo "       the nightly toolchain:" >&2
  echo "         rustup toolchain install nightly" >&2
  exit 2
fi

if ! cargo +nightly --version >/dev/null 2>&1; then
  echo "error: nightly Rust toolchain not available." >&2
  echo "       sanitize-rust-ffi.sh requires nightly Rust for" >&2
  echo "       RUSTFLAGS=\"-Zsanitizer=address\" support; stable Rust" >&2
  echo "       does not expose -Zsanitizer.  Install via:" >&2
  echo "         rustup toolchain install nightly" >&2
  exit 2
fi

echo "[sanitize-rust-ffi] nightly cargo available: $(cargo +nightly --version)"

# ----------------------------------------------------------------------
# TODO: recipe body.
#
# The actual ASan build + run is deferred to a sibling follow-up
# issue (gated on a Linux + nightly-Rust worker host).  See the
# usage() block above for the intended recipe shape.
#
# Until the body lands, this skeleton exits 1 with a clear
# "skeleton" message so callers cannot mistake an unfilled-recipe
# run for a clean ASan pass.
# ----------------------------------------------------------------------
echo "error: sanitize-rust-ffi.sh recipe body is TODO." >&2
echo "       This skeleton only validates that nightly Rust is" >&2
echo "       available; the actual ASan build + run is deferred to" >&2
echo "       a sibling follow-up issue.  See SECURITY_INVENTORY.md" >&2
echo "       'miniz_oxide via Rust' -> 'Missing work' bullet 1 for" >&2
echo "       the current state." >&2
exit 1
