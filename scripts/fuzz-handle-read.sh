#!/usr/bin/env bash
#
# fuzz-handle-read.sh -- wall-clock budgeted randomized fuzz run
# for the `Handle.read` / `Stream.read` driven archive-parser
# entry points (`Archive.list`, `Archive.extract`, `Tar.list`,
# `Tar.extract`, `Tar.extractTarGz`, `Tar.extractTarGzNative`,
# `Gzip.decompressStream`, `RawDeflate.decompressStream`,
# `Gzip.decompressFile`).
#
# In-repo regression reconstruction of the original Kiran
# blog-post AFL harness for `lean_io_prim_handle_read`
# (closed upstream by leanprover/lean4#13392, consumed via
# v4.30.0-rc2). Sibling of `scripts/fuzz-inflate.sh`: same shape,
# different surface.
#
# Builds and invokes the `fuzz_handle_read` lake executable
# (root: `ZipFuzzHandleRead.lean`), which drives every
# `Handle.read` / `Stream.read` archive-parser entry point with
# pseudo-random inputs for a configurable time budget. Exit code 0
# on clean completion; any uncaught exception, panic, or
# sanitizer trap terminates with non-zero status.
#
# Usage:
#   scripts/fuzz-handle-read.sh [seconds]          # default 30
#   LEAN_ZIP_FUZZ_HANDLE_READ_SECONDS=60 scripts/fuzz-handle-read.sh
#   LEAN_ZIP_FUZZ_HANDLE_READ_SEED=0x1234 scripts/fuzz-handle-read.sh 10
#
# Sanitizer coverage:
#   For ASan + UBSan coverage of the FFI path, set
#   ZLIB_CFLAGS / ZLIB_LDFLAGS to the sanitizer flags used by
#   `scripts/sanitize-ffi.sh` and LD_PRELOAD the sanitizer runtimes.
#   The easiest recipe is to invoke this script from within an
#   environment already prepared by `scripts/sanitize-ffi.sh`.
#
# Scope: this is a deterministic in-repo regression harness, not a
# coverage-guided fuzzer. The original AFL++ harness from
# kiranandcode/lean-zip remains the historical reference for the
# `lean_io_prim_handle_read` class — see #2380 for the rationale.

set -euo pipefail

usage() {
  cat <<'EOF'
Usage: scripts/fuzz-handle-read.sh [seconds]

Arguments:
  seconds   wall-clock budget (default 30, or LEAN_ZIP_FUZZ_HANDLE_READ_SECONDS)

Environment:
  LEAN_ZIP_FUZZ_HANDLE_READ_SECONDS   wall-clock budget in seconds
  LEAN_ZIP_FUZZ_HANDLE_READ_SEED      64-bit PRNG seed (decimal)

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
# nix-shell (matches scripts/fuzz-inflate.sh / sanitize-ffi.sh
# behaviour).
if ! command -v pkg-config >/dev/null || ! pkg-config --exists zlib 2>/dev/null; then
  if [[ -z "${IN_NIX_SHELL:-}" && -f shell.nix ]] && command -v nix-shell >/dev/null; then
    echo "[fuzz-handle-read] re-executing under nix-shell (zlib not found on host)"
    exec nix-shell --run "bash $(pwd)/scripts/fuzz-handle-read.sh $*"
  fi
fi

SECONDS_ARG="${1:-}"
if [[ -n "${SECONDS_ARG}" ]]; then
  export LEAN_ZIP_FUZZ_HANDLE_READ_SECONDS="${SECONDS_ARG}"
fi

echo "[fuzz-handle-read] lake build fuzz_handle_read"
lake build fuzz_handle_read

FUZZ_BIN=".lake/build/bin/fuzz_handle_read"
if [[ ! -x "${FUZZ_BIN}" ]]; then
  echo "error: ${FUZZ_BIN} not found after lake build" >&2
  exit 2
fi

echo "[fuzz-handle-read] running ${FUZZ_BIN}"
"${FUZZ_BIN}"
echo "[fuzz-handle-read] OK"
