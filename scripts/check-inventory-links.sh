#!/usr/bin/env bash
#
# check-inventory-links.sh -- verify that SECURITY_INVENTORY.md's
# fixture paths still resolve and flag unresolved placeholder PR refs.
#
# Two passes over SECURITY_INVENTORY.md:
#
#   (b) Fixture-path existence (HARD FAILURE, exit 1).
#       For every `testdata/<...>.<ext>` path mentioned anywhere in
#       the file, verify the file exists. Glob patterns (paths
#       containing `*`) and bare directory references (no extension)
#       are skipped by construction — the regex requires a
#       `.<letters>` suffix.
#
#   (d) Unresolved-placeholder-PR scan (WARNING, not fatal).
#       Scans the inventory line-by-line for `#TBD`, `#N`, `#XXX`,
#       `#NNN`, or the phrase `this PR` and emits a warning for
#       each occurrence. A feature worker does not know the landing
#       PR number at write time (assigned only by
#       `coordination create-pr`) and typically leaves one of these
#       placeholders or `— this PR` / `by this PR` / `See this PR`,
#       expecting a follow-up sweep. Empirically, the sweep is
#       often missed; this pass flags stale placeholders so they
#       can be substituted with the real PR number via `git blame`
#       + `gh pr list --search <sha>`.
#
#       The placeholder tokens `#N`, `#XXX`, `#NNN` are matched at
#       word boundaries (`\b`) so real PR numbers like `#N123` (if
#       ever used) would not false-positive. `#TBD` and `this PR`
#       have no natural-prose ambiguity at word-boundary granularity.
#       The phrase `this PR` is matched case-sensitively and is
#       deliberately false-positive-tolerant: prose like "has this
#       PR" or "in this PR" would also warn. Every observed
#       inventory use of the phrase to date has been a placeholder,
#       so the tolerance is acceptable.
#
#       Pass (d) honours a `<!-- drift-detector: ... -->` opt-out
#       marker on the same inventory line, in case a future
#       legitimate prose use of "this PR" (or one of the placeholder
#       tokens) needs to be exempted.
#
# History: passes (a) line-anchor existence, (c) line-content sanity,
# and (e) inverted-range scan were retired (issue #2345) when the
# project stopped tracking source-line numbers in markdown files.
# Citing by stable identifier (function name, theorem name, fixture
# filename, section header) means anchors do not drift with line
# shifts, so the line-anchor link-checker passes had no work to do.
#
# Why (b) is hard and (d) is soft: (b) is an unambiguous correctness
# failure — either the fixture exists or the audit trail is broken.
# (d) is soft because a stale placeholder is a documentation drift,
# not a correctness failure — the inventory still points at the
# right file, just with a missing PR cross-ref.
#
# The script is opt-in tooling and is NOT wired into `lake exe test`
# or `.github/` workflows. Run it manually after any change that
# touches `testdata/**` or `SECURITY_INVENTORY.md` itself.
#
# Exit codes:
#   0  all hard checks passed (warnings may still be printed).
#   1  at least one hard failure (missing fixture).
#   2  invalid invocation.
#
# Usage:
#   bash scripts/check-inventory-links.sh
#   bash scripts/check-inventory-links.sh --help

set -euo pipefail

INVENTORY="SECURITY_INVENTORY.md"

usage() {
    cat <<'EOF'
Usage: scripts/check-inventory-links.sh [--help]

Validate fixture-path references and flag unresolved PR placeholders
in SECURITY_INVENTORY.md.

Exit codes:
  0 — all hard checks passed (warnings may still be printed).
  1 — at least one hard failure: missing fixture.
  2 — invalid invocation.

Run from the repository root.
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
        echo "error: unexpected argument '$1'" >&2
        usage >&2
        exit 2
        ;;
esac

if [[ ! -f "$INVENTORY" ]]; then
    echo "error: $INVENTORY not found (run from repo root)." >&2
    exit 2
fi

errors=0
warnings=0

# Fixture pattern requires a `.<letters>` extension at the end so
# that glob patterns like `testdata/tar/malformed/pax-*.tar` (which
# the char class cannot cross because of the `*`) and bare directory
# references like `testdata/tar/security/` are not matched.
FIX_RE='testdata/[A-Za-z0-9_/.\-]+\.[A-Za-z]+'

# ---------------------------------------------------------------------------
# Pass (b): fixture-path existence.
# ---------------------------------------------------------------------------
declare -A seen_fix=()
fix_checked=0

while IFS=: read -r srcln path; do
    [[ -z "$srcln" ]] && continue
    if [[ -n "${seen_fix[$path]:-}" ]]; then
        continue
    fi
    seen_fix[$path]="$srcln"
    fix_checked=$((fix_checked + 1))

    if [[ ! -e "$path" ]]; then
        echo "error: $INVENTORY:$srcln references $path but fixture does not exist" >&2
        errors=$((errors + 1))
    fi
done < <(grep -noE "$FIX_RE" "$INVENTORY" || true)

# ---------------------------------------------------------------------------
# Pass (d): unresolved-placeholder-PR scan (warnings only).
# ---------------------------------------------------------------------------
placeholder_checks=0

# Collect every `#TBD`, `#N`, `#XXX`, `#NNN`, and every `this PR`
# occurrence with line number. `grep -no` emits `<lineno>:<match>`
# per occurrence, so a line with two matches (e.g. "filled inline
# in this PR. See this PR.") is flagged twice — the intent is
# zero placeholders. The placeholder tokens `#N`, `#XXX`, `#NNN`
# are anchored at a trailing word boundary (`\b`, GNU-grep
# extension) so real PR numbers like `#N123` do not false-positive.
while IFS=: read -r srcln _; do
    [[ -z "$srcln" ]] && continue
    placeholder_checks=$((placeholder_checks + 1))
    prose=$(awk -v n="$srcln" 'NR==n{print; exit}' "$INVENTORY")
    # Per-line opt-out: a `<!-- drift-detector: ... -->` marker on
    # the inventory line silences pass (d) warnings for that line.
    # Reserved for prose uses of "this PR" (or a `#N` / `#XXX` /
    # `#NNN` / `#TBD` token) that are not placeholders.
    if grep -Fq -- '<!-- drift-detector:' <<< "$prose"; then
        continue
    fi
    prose_trim="${prose:0:140}"
    echo "warning: $INVENTORY:$srcln contains unresolved placeholder-PR reference (\"#TBD\", \"#N\", \"#XXX\", \"#NNN\", or \"this PR\"); substitute with the real PR number via git blame + gh pr list --search. Line: $prose_trim" >&2
    warnings=$((warnings + 1))
done < <(grep -noE '#TBD|#N\b|#XXX\b|#NNN\b|this PR' "$INVENTORY" || true)

# ---------------------------------------------------------------------------
# Summary.
# ---------------------------------------------------------------------------
echo "check-inventory-links.sh: checked $fix_checked unique fixture paths, $placeholder_checks placeholder-PR occurrences (errors=$errors, warnings=$warnings)"

if (( errors > 0 )); then
    exit 1
fi
exit 0
