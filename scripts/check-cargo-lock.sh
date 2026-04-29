#!/usr/bin/env bash
#
# check-cargo-lock.sh -- trip wire for miniz_oxide / adler2 version drift.
#
# Advisory only: always exits 0. Prints a warning at PR-review time if
# the resolved `miniz_oxide` / `adler2` versions in
# rust/miniz_oxide_shim/Cargo.lock have drifted from the snapshot
# audited in SECURITY_INVENTORY.md § "miniz_oxide via Rust" (the
# *"`Cargo.lock` is tracked and treated as security-critical"* bullet
# under *Current local guardrails*).
#
# Drift does not mean "broken"; it means "re-read the *Why trusted*
# paragraph for `miniz_oxide via Rust`, decide whether the new resolved
# versions are acceptable, and update the *Snapshot as of …* line in
# SECURITY_INVENTORY.md to match (or roll back the lockfile change)."
#
# Run before opening a PR that touches `rust/miniz_oxide_shim/`.
#
# This is a trip wire, not a fence. It is not wired into CI — the goal
# is to make accidental Cargo.lock churn visible in a `git diff`, not
# to reject it automatically. Sibling helper to
# scripts/check-c-allocations.sh, which performs the same role for
# c/zlib_ffi.c allocation sites.
#
# Requirements: pure POSIX shell + standard text tools (grep, awk,
# sed). No Cargo or Rust toolchain required.
#
# Manual smoke tests:
#   1. Drift detection: temporarily edit the *Snapshot as of …* line in
#      SECURITY_INVENTORY.md to mention an obviously wrong version
#      (e.g. `miniz_oxide` 9.9.9), re-run this script, expect a single
#      DRIFT WARNING block followed by exit 0, then revert the edit.
#   2. Parser-mismatch diagnostic: temporarily replace the single space
#      between the closing backtick and the version triple with two
#      spaces (e.g. ``` `miniz_oxide`  0.8.9 ```), re-run this script,
#      expect a *parser regex mismatch* WARNING block followed by
#      exit 0 (not a blank-`expected:` DRIFT block), then revert.

set -u

LOCK="rust/miniz_oxide_shim/Cargo.lock"
INVENTORY="SECURITY_INVENTORY.md"

if [ "${1:-}" = "--help" ] || [ "${1:-}" = "-h" ]; then
    cat <<EOF
check-cargo-lock.sh -- compare $LOCK against the audited snapshot in
$INVENTORY § "miniz_oxide via Rust".

Prints a warning if the resolved miniz_oxide / adler2 versions drift
from the snapshot. Advisory only; always exits 0. Run from the
repository root.

Usage:
    bash scripts/check-cargo-lock.sh
    bash scripts/check-cargo-lock.sh --help
EOF
    exit 0
fi

if [ ! -f "$LOCK" ]; then
    echo "check-cargo-lock.sh: $LOCK not found (run from repo root)." >&2
    exit 0
fi

if [ ! -f "$INVENTORY" ]; then
    echo "check-cargo-lock.sh: $INVENTORY not found (run from repo root)." >&2
    exit 0
fi

# Parse the resolved version of a named package out of Cargo.lock.
# Cargo.lock blocks look like:
#   [[package]]
#   name = "miniz_oxide"
#   version = "0.8.9"
#   ...
get_lock_version() {
    awk -v pkg="$1" '
        $0 == "[[package]]" { in_pkg = 1; name = ""; ver = "" }
        in_pkg && $1 == "name" { gsub(/"/, "", $3); name = $3 }
        in_pkg && $1 == "version" { gsub(/"/, "", $3); ver = $3 }
        in_pkg && name == pkg && ver != "" { print ver; exit }
    ' "$LOCK"
}

current_miniz=$(get_lock_version miniz_oxide)
current_adler=$(get_lock_version adler2)

# Pull the inventory snapshot line. The bullet body uses the literal
# prefix "Snapshot as of YYYY-MM-DD: `miniz_oxide` X.Y.Z, `adler2` A.B.C."
snap_line=$(grep -E "Snapshot as of [0-9]{4}-[0-9]{2}-[0-9]{2}: \`miniz_oxide\`" "$INVENTORY" | head -n 1)

if [ -z "$snap_line" ]; then
    echo "check-cargo-lock.sh: WARNING — no \"Snapshot as of …: \`miniz_oxide\` …\" line found in $INVENTORY (expected under § 'miniz_oxide via Rust')."
    exit 0
fi

expected_miniz=$(printf '%s\n' "$snap_line" | sed -nE 's/.*\`miniz_oxide\` ([0-9]+\.[0-9]+\.[0-9]+).*/\1/p')
expected_adler=$(printf '%s\n' "$snap_line" | sed -nE 's/.*\`adler2\` ([0-9]+\.[0-9]+\.[0-9]+).*/\1/p')

# Surface parser failure as an explicit diagnostic instead of letting it
# masquerade as a real version drift with blank `expected:` fields. The
# sed regexes above require exactly one space between the closing
# backtick and the version triple; whitespace or punctuation variations
# in the snapshot line silently produce empty captures.
if [ -z "$expected_miniz" ] || [ -z "$expected_adler" ]; then
    echo "check-cargo-lock.sh: WARNING — snapshot line found in $INVENTORY but could not extract miniz_oxide / adler2 versions (parser regex mismatch — check whitespace / punctuation in the snapshot line)."
    echo "  snapshot line: $snap_line"
    exit 0
fi

if [ "$current_miniz" = "$expected_miniz" ] && [ "$current_adler" = "$expected_adler" ]; then
    echo "check-cargo-lock.sh: $LOCK matches snapshot (miniz_oxide $current_miniz, adler2 $current_adler)."
else
    echo "check-cargo-lock.sh: $LOCK has drifted from snapshot in $INVENTORY (DRIFT)."
    echo "  expected: miniz_oxide $expected_miniz, adler2 $expected_adler"
    echo "  current:  miniz_oxide $current_miniz, adler2 $current_adler"
    echo "  --> Re-read the \"Why trusted\" paragraph for 'miniz_oxide via Rust'"
    echo "      and update the \"Snapshot as of …\" line in $INVENTORY (or roll back $LOCK)."
fi

exit 0
