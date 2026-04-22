#!/usr/bin/env bash
#
# sanitize-ffi.sh -- build and run lean-zip under ASan + UBSan.
#
# Instruments c/zlib_ffi.c with `-fsanitize=address,undefined` at
# compile time and explicitly links GCC's libasan.so / libubsan.so
# into the final test binary, then runs the test suite so any memory
# or undefined-behaviour error in the FFI surfaces as a runtime trap.
#
# Why libasan is linked explicitly (rather than via `-fsanitize=...`
# on the link line):
#   Lake hard-codes its bundled clang as the final linker, and the
#   Lean toolchain does not ship Clang's compiler-rt asan runtime.
#   Passing `-fsanitize=address,undefined` at link time therefore
#   fails with "cannot open libclang_rt.asan.a". Linking GCC's
#   libasan.so / libubsan.so directly sidesteps the missing runtime:
#   the FFI is compiled by the system `cc` (gcc on NixOS + Ubuntu)
#   which emits calls to `__asan_*` / `__ubsan_*` from the matching
#   GCC sanitizer runtime.
#
# Why LD_PRELOAD at run time:
#   ASan requires its runtime to appear first in the initial library
#   list. When libasan.so is pulled in as a plain DT_NEEDED entry it
#   usually is *not* first (the Lean shared libraries come first),
#   and ASan aborts with "ASan runtime does not come first in initial
#   library list". LD_PRELOAD forces the correct order.
#
# Why `lake -R clean` before building:
#   Lake's per-object trace does not hash the `weakArgs` passed to
#   `buildO` (where the zlib cflags live in lakefile.lean), so
#   switching sanitizer flags on/off does not, by itself, invalidate
#   the cached .o. `-R` additionally re-elaborates the package
#   configuration so the new `ZLIB_CFLAGS` / `ZLIB_LDFLAGS` are
#   re-read instead of the compiled-config cache.
#
# Scope: FFI only. The Lean runtime and generated C are *not*
# re-compiled with sanitizers; the ASan/UBSan runtimes are loaded
# into the final test binary so heap interception still catches
# errors originating in c/zlib_ffi.c or in zlib itself.
#
# See also: Track E Priority 3 item 1 of
# plans/track-e-current-audit-checklist.md.

set -euo pipefail

usage() {
  cat <<'EOF'
Usage: scripts/sanitize-ffi.sh [--help]

Build the lean-zip FFI + test binary with
`-fsanitize=address,undefined -fno-omit-frame-pointer`, explicitly
link GCC's libasan / libubsan, and run `.lake/build/bin/test` under
`LD_PRELOAD` so ASan initialises first. Any sanitizer report or test
failure exits non-zero.

Environment requirements:
  * pkg-config and zlib (NixOS via shell.nix provides both; Ubuntu
    via `libz-dev` and `pkg-config`). When pkg-config cannot find
    zlib and shell.nix is present, the script re-execs under
    nix-shell.
  * A GCC-family `cc` that can locate libasan.so / libubsan.so via
    `cc -print-file-name=libasan.so` (true on NixOS's gcc-wrapper
    and on Ubuntu's default gcc).
  * Run from the project root.

Env vars set by this script (and why):
  ASAN_OPTIONS=...:detect_leaks=0:abort_on_error=1
      Lean's runtime intentionally keeps global state alive past main,
      so LeakSanitizer would be noisy without detect_leaks=0.
  UBSAN_OPTIONS=...:print_stacktrace=1:halt_on_error=1
      Makes UBSan findings visible and fatal.
  ZLIB_CFLAGS, ZLIB_LDFLAGS (consumed by lakefile.lean) are extended
      from the pkg-config output with the sanitizer flags and the
      explicit `-lasan -lubsan` on the link side.
  LD_PRELOAD (scoped to the single test invocation) points at
      libasan.so and libubsan.so so ASan initialises first.

What to do if it fails:
  * Leak report: the most likely first failure. This script already
    sets detect_leaks=0; if a leak still surfaces, capture it as a
    finding -- do not silence it.
  * UBSan report: capture the printed stacktrace and reproducer as
    a finding.
  * ASan heap-report with a symbol inside zlib_ffi.c: fix at the C
    layer. With a symbol inside zlib itself: escalate upstream.
  * Test failure with no sanitizer report: a plain test bug. Re-run
    `lake exe test` without this wrapper to confirm, then debug
    as usual.
  * "ASan runtime does not come first" despite LD_PRELOAD: libasan
    changed ABI. Re-run `cc -print-file-name=libasan.so` and confirm
    the path is readable.
  * "cannot find -lasan" during link: gcc's libasan is missing.
    Install libasan on Ubuntu (ships with gcc on most distros) or
    re-enter nix-shell.
  * "moreLinkArgs didn't change" symptoms (e.g. no ASan symbols in
    the linked binary): the Lake build cache survived `lake clean`.
    Delete `.lake/build` and retry: `rm -rf .lake/build`.

Out of scope: CI integration. Running this wrapper in CI needs a
separate runtime-budget decision and is tracked outside this script.
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

# If pkg-config cannot find zlib, attempt to re-exec under nix-shell.
if ! command -v pkg-config >/dev/null || ! pkg-config --exists zlib 2>/dev/null; then
  if [[ -z "${IN_NIX_SHELL:-}" && -f shell.nix ]] && command -v nix-shell >/dev/null; then
    echo "[sanitize-ffi] re-executing under nix-shell (zlib not found on host)"
    exec nix-shell --run "bash $(pwd)/scripts/sanitize-ffi.sh $*"
  fi
  echo "error: pkg-config cannot find zlib. Install libz-dev (Ubuntu)," >&2
  echo "       enter nix-shell, or provide ZLIB_CFLAGS/ZLIB_LDFLAGS manually." >&2
  exit 2
fi

# Discover libasan.so / libubsan.so via the default cc. Error out if
# the returned string is not an absolute path (which means gcc could
# not locate the library -- usually because the sanitizer runtimes
# are not installed on the host).
LIBASAN_SO="$(cc -print-file-name=libasan.so 2>/dev/null || true)"
LIBUBSAN_SO="$(cc -print-file-name=libubsan.so 2>/dev/null || true)"
if [[ "$LIBASAN_SO" != /* || "$LIBUBSAN_SO" != /* ]]; then
  echo "error: cc could not locate libasan.so / libubsan.so." >&2
  echo "       On Ubuntu the sanitizer runtimes ship with gcc; on" >&2
  echo "       NixOS use the project's nix-shell." >&2
  exit 2
fi
GCC_SAN_LIB_DIR="$(dirname "$LIBASAN_SO")"

SAN_C_FLAGS="-fsanitize=address,undefined -fno-omit-frame-pointer"
# Do NOT pass -fsanitize=... at link time -- Lean's bundled clang has
# no matching compiler-rt asan. Instead link GCC's libasan / libubsan
# directly, with rpath so the runtime is findable without the user
# setting LD_LIBRARY_PATH.
SAN_LINK_FLAGS="-Wl,-rpath,${GCC_SAN_LIB_DIR} -L${GCC_SAN_LIB_DIR} -lasan -lubsan"

ZLIB_CFLAGS_BASE="$(pkg-config --cflags zlib)"
ZLIB_LIBS_BASE="$(pkg-config --libs zlib)"

export ZLIB_CFLAGS="${ZLIB_CFLAGS_BASE} ${SAN_C_FLAGS}"
export ZLIB_LDFLAGS="${ZLIB_LIBS_BASE} ${SAN_LINK_FLAGS}"

# Lean intentionally leaks bootstrap state; focus reports on the FFI.
export ASAN_OPTIONS="${ASAN_OPTIONS:+${ASAN_OPTIONS}:}detect_leaks=0:abort_on_error=1"
export UBSAN_OPTIONS="${UBSAN_OPTIONS:+${UBSAN_OPTIONS}:}print_stacktrace=1:halt_on_error=1"

echo "[sanitize-ffi] libasan=${LIBASAN_SO}"
echo "[sanitize-ffi] libubsan=${LIBUBSAN_SO}"
echo "[sanitize-ffi] ZLIB_CFLAGS=${ZLIB_CFLAGS}"
echo "[sanitize-ffi] ZLIB_LDFLAGS=${ZLIB_LDFLAGS}"
echo "[sanitize-ffi] ASAN_OPTIONS=${ASAN_OPTIONS}"
echo "[sanitize-ffi] UBSAN_OPTIONS=${UBSAN_OPTIONS}"

echo "[sanitize-ffi] lake -R clean"
# -R forces Lake to re-elaborate the configuration files rather than
# reuse the compiled-config cache; otherwise new ZLIB_* env vars are
# ignored.
lake -R clean

echo "[sanitize-ffi] lake -R build"
lake -R build

echo "[sanitize-ffi] running .lake/build/bin/test under LD_PRELOAD"
# LD_PRELOAD keeps ASan first in the initial library list; plain
# DT_NEEDED order trips the "ASan runtime does not come first" abort.
LD_PRELOAD="${LIBASAN_SO} ${LIBUBSAN_SO}${LD_PRELOAD:+ ${LD_PRELOAD}}" \
  .lake/build/bin/test

echo "[sanitize-ffi] OK -- no sanitizer report, tests passed"
