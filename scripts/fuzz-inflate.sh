#!/usr/bin/env bash
#
# fuzz-inflate.sh -- wall-clock budgeted randomized inflate fuzz run.
#
# Builds and invokes the `fuzz_inflate` lake executable (root:
# `ZipFuzzInflate.lean`), which drives every whole-buffer and
# streaming inflate entry point with pseudo-random inputs for a
# configurable time budget. Exit code 0 on clean completion; any
# uncaught exception, panic, or sanitizer trap terminates with
# non-zero status.
#
# Usage:
#   scripts/fuzz-inflate.sh [seconds]          # default 30
#   LEAN_ZIP_FUZZ_SECONDS=60 scripts/fuzz-inflate.sh
#   LEAN_ZIP_FUZZ_SEED=0x1234 scripts/fuzz-inflate.sh 10
#
# Sanitizer coverage:
#   For ASan + UBSan coverage of the FFI path, set
#   ZLIB_CFLAGS / ZLIB_LDFLAGS to the sanitizer flags used by
#   `scripts/sanitize-ffi.sh` and LD_PRELOAD the sanitizer runtimes.
#   The easiest recipe is to invoke this script from within an
#   environment already prepared by `scripts/sanitize-ffi.sh` (export
#   the relevant variables at the top of that script, then re-run
#   this one), or to copy the ZLIB_CFLAGS/ZLIB_LDFLAGS/LD_PRELOAD
#   block from `scripts/sanitize-ffi.sh` into the caller's shell.
#
# Scope: this is a first-cut randomized harness, not a production
# fuzzer. It does not use libFuzzer / AFL++ / coverage-guided
# mutation. See `plans/track-e-current-audit-checklist.md`
# Priority 3 item 3 for context and future work.

set -euo pipefail

usage() {
  cat <<'EOF'
Usage: scripts/fuzz-inflate.sh [seconds]

Arguments:
  seconds   wall-clock budget (default 30, or LEAN_ZIP_FUZZ_SECONDS)

Environment:
  LEAN_ZIP_FUZZ_SECONDS   wall-clock budget in seconds
  LEAN_ZIP_FUZZ_SEED      64-bit PRNG seed (decimal)

Exit codes:
  0    clean completion of the fuzz budget
  non-zero    any exception, panic, or sanitizer trap
EOF
}

case "${1:-}" in
  -h|--help)
    usage
    exit 0
    ;;
esac

if [[ ! -f lakefile.lean ]]; then
  echo "error: run from the project root (lakefile.lean not found)" >&2
  exit 2
fi

# If pkg-config cannot find zlib on this host, re-exec under
# nix-shell (matches scripts/sanitize-ffi.sh behaviour).
if ! command -v pkg-config >/dev/null || ! pkg-config --exists zlib 2>/dev/null; then
  if [[ -z "${IN_NIX_SHELL:-}" && -f shell.nix ]] && command -v nix-shell >/dev/null; then
    echo "[fuzz-inflate] re-executing under nix-shell (zlib not found on host)"
    exec nix-shell --run "bash $(pwd)/scripts/fuzz-inflate.sh $*"
  fi
fi

SECONDS_ARG="${1:-}"
if [[ -n "${SECONDS_ARG}" ]]; then
  export LEAN_ZIP_FUZZ_SECONDS="${SECONDS_ARG}"
fi

echo "[fuzz-inflate] lake build fuzz_inflate"
lake build fuzz_inflate

FUZZ_BIN=".lake/build/bin/fuzz_inflate"
if [[ ! -x "${FUZZ_BIN}" ]]; then
  echo "error: ${FUZZ_BIN} not found after lake build" >&2
  exit 2
fi

echo "[fuzz-inflate] running ${FUZZ_BIN}"
"${FUZZ_BIN}"
echo "[fuzz-inflate] OK"
