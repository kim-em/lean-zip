#!/usr/bin/env bash
#
# check-c-allocations.sh -- trip wire for new allocation sites in c/zlib_ffi.c.
#
# Advisory only: always exits 0. Prints a warning at PR-review time if
# the count of `malloc`/`realloc`/`calloc` mentions in c/zlib_ffi.c
# drifts from the baseline audited in SECURITY_INVENTORY.md §
# "Allocation site audit (c/zlib_ffi.c)". Drift does not mean "broken";
# it means "re-run the audit and update the table".
#
# This is a trip wire, not a fence. It is not wired into CI — the goal
# is to make accidental new alloc sites visible in a `git diff`, not to
# reject them automatically.

set -u

EXPECTED=10
C_FILE="c/zlib_ffi.c"
INVENTORY="SECURITY_INVENTORY.md"

if [ "${1:-}" = "--help" ] || [ "${1:-}" = "-h" ]; then
    cat <<EOF
check-c-allocations.sh -- count malloc/realloc/calloc mentions in $C_FILE.

Prints a warning if the count differs from the audited baseline
($EXPECTED, see "Allocation site audit (c/zlib_ffi.c)" in $INVENTORY).
Advisory only; always exits 0. Run from the repository root.

Usage:
    bash scripts/check-c-allocations.sh
    bash scripts/check-c-allocations.sh --help
EOF
    exit 0
fi

if [ ! -f "$C_FILE" ]; then
    echo "check-c-allocations.sh: $C_FILE not found (run from repo root)." >&2
    exit 0
fi

actual=$(grep -cE 'malloc|realloc|calloc' "$C_FILE")

if [ "$actual" -eq "$EXPECTED" ]; then
    echo "check-c-allocations.sh: $C_FILE has $actual malloc/realloc/calloc mentions (matches baseline $EXPECTED)."
else
    echo "check-c-allocations.sh: $C_FILE has $actual malloc/realloc/calloc mentions (expected $EXPECTED — DRIFT)."
    echo "  Current call sites:"
    grep -nE 'malloc|realloc|calloc' "$C_FILE" | sed 's/^/    /'
    echo "  --> Re-run the audit in $INVENTORY § \"Allocation site audit (c/zlib_ffi.c)\""
    echo "      and update the EXPECTED baseline at the top of this script."
fi

exit 0
