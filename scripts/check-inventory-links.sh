#!/usr/bin/env bash
#
# check-inventory-links.sh -- verify that SECURITY_INVENTORY.md's code
# and fixture links still resolve to live targets.
#
# Three passes over SECURITY_INVENTORY.md:
#
#   (a) Line-anchor existence (HARD FAILURE, exit 1).
#       For every `Zip/<file>:<line>` or `ZipTest/<file>:<line>`
#       reference (markdown-link URL form or bare in prose), verify
#       that the file exists in the tree and has at least <line>
#       lines. Any missing file or under-length file is fatal.
#
#   (b) Fixture-path existence (HARD FAILURE, exit 1).
#       For every `testdata/<...>.<ext>` path mentioned anywhere in
#       the file, verify the file exists. Glob patterns (paths
#       containing `*`) and bare directory references (no extension)
#       are skipped by construction — the regex requires a
#       `.<letters>` suffix.
#
#   (c) Line-content sanity (WARNING, not fatal).
#       For each line-anchor reference, look on the same inventory
#       source line for a quoted substring — either `"..."` or
#       `` `...` `` — of length 3..80 chars. If any such substring
#       exists, check that at least one appears within the line
#       <line> ± 2 window of the cited source file. If none match,
#       emit a warning (does not affect exit code). The heuristic
#       tolerates prose phrasing drift that is orthogonal to code
#       drift.
#
#       Pass (c) warnings are silenced on any inventory line that
#       contains `<!-- drift-detector: ... -->` — an opt-out
#       intended for quote/anchor mismatches where the quote is
#       structurally unverifiable against the cited file (e.g.,
#       declaration-style quotes with keyword-argument callsites).
#       The marker suppresses the warning at line granularity; it
#       does not affect passes (a) or (b).
#
# Why (a)/(b) are hard and (c) is soft: (a)/(b) are unambiguous
# correctness failures — either the anchor is live or the audit
# trail is broken. (c) is a best-effort detector for stale line
# numbers; false positives happen when the surrounding prose uses
# phrasing that never appeared verbatim in the code.
#
# The script is opt-in tooling and is NOT wired into `lake exe test`
# or `.github/` workflows. Run it manually after any change that
# touches `Zip/**`, `ZipTest/**`, `testdata/**`, or
# `SECURITY_INVENTORY.md` itself.
#
# Exit codes:
#   0  all hard checks passed (warnings may still be printed).
#   1  at least one hard failure (missing file, under-length file,
#      or missing fixture).
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

Validate line-number and fixture-path references in SECURITY_INVENTORY.md.

Exit codes:
  0 — all hard checks passed (warnings may still be printed).
  1 — at least one hard failure: missing file, under-length file,
      or missing fixture.
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

# Pattern covers both `Zip/...` and `ZipTest/...` line anchors. The
# markdown URL prefix `/home/kim/lean-zip/` is worker-specific; since
# the regex does not anchor the left side, it matches the `Zip.../`
# suffix inside URL paths as well as bare mentions in prose.
ZIP_RE='(Zip|ZipTest)/[A-Za-z0-9_-]+(/[A-Za-z0-9_-]+)*\.lean:[0-9]+'

# Fixture pattern requires a `.<letters>` extension at the end so
# that glob patterns like `testdata/tar/malformed/pax-*.tar` (which
# the char class cannot cross because of the `*`) and bare directory
# references like `testdata/tar/security/` are not matched.
FIX_RE='testdata/[A-Za-z0-9_/.\-]+\.[A-Za-z]+'

# ---------------------------------------------------------------------------
# Pass (a): line-anchor existence.
# ---------------------------------------------------------------------------
declare -A seen_zip=()
zip_checked=0

while IFS=: read -r srcln path lineno; do
    [[ -z "$srcln" ]] && continue
    key="$path:$lineno"
    if [[ -n "${seen_zip[$key]:-}" ]]; then
        continue
    fi
    seen_zip[$key]="$srcln"
    zip_checked=$((zip_checked + 1))

    if [[ ! -f "$path" ]]; then
        echo "error: $INVENTORY:$srcln references $path:$lineno but $path does not exist" >&2
        errors=$((errors + 1))
        continue
    fi

    # awk's NR counts all lines, including a final unterminated line;
    # `wc -l` only counts newlines and would under-count by one in
    # that case.
    file_len=$(awk 'END{print NR}' "$path")
    if (( lineno > file_len )); then
        echo "error: $INVENTORY:$srcln references $path:$lineno but $path has only $file_len lines" >&2
        errors=$((errors + 1))
    fi
done < <(grep -noE "$ZIP_RE" "$INVENTORY" || true)

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
# Pass (c): line-content heuristic (warnings only).
# ---------------------------------------------------------------------------
quote_checks=0

# Dedup by full grep -no line: (srcln, path, lineno) triple.
while IFS=: read -r srcln path lineno; do
    [[ -z "$srcln" ]] && continue
    [[ -f "$path" ]] || continue
    file_len=$(awk 'END{print NR}' "$path")
    (( lineno <= file_len )) || continue

    prose=$(awk -v n="$srcln" 'NR==n{print; exit}' "$INVENTORY")

    # Collect quoted substrings (length 3..80) from the prose. The
    # grep invocations may find zero matches, which is not an error.
    quotes=()
    while IFS= read -r q; do
        [[ -z "$q" ]] && continue
        quotes+=("$q")
    done < <(
        {
            grep -oE '"[^"]{3,80}"' <<< "$prose" | sed 's/^"//; s/"$//'
            grep -oE '`[^`]{3,80}`' <<< "$prose" | sed 's/^`//; s/`$//'
        } 2>/dev/null || true
    )

    if (( ${#quotes[@]} == 0 )); then
        continue
    fi
    quote_checks=$((quote_checks + 1))

    start=$(( lineno > 2 ? lineno - 2 : 1 ))
    end=$(( lineno + 2 ))
    window=$(awk -v a="$start" -v b="$end" 'NR>=a && NR<=b{print} NR>b{exit}' "$path")

    found=0
    for q in "${quotes[@]}"; do
        if grep -qF -- "$q" <<< "$window"; then
            found=1
            break
        fi
    done

    if (( !found )); then
        # Per-line opt-out: a `<!-- drift-detector: ... -->` marker on
        # the inventory line silences pass (c) warnings for that line.
        # Reserved for cases where the quote is structurally
        # unverifiable against the cited file (e.g., declaration-style
        # quotes with keyword-argument callsites).
        if grep -Fq -- '<!-- drift-detector:' <<< "$prose"; then
            continue
        fi
        cited=$(awk -v n="$lineno" 'NR==n{print; exit}' "$path")
        # Trim cited line for display.
        cited="${cited:0:120}"
        # Join quotes with " | " for display.
        quote_list=""
        for q in "${quotes[@]}"; do
            if [[ -n "$quote_list" ]]; then
                quote_list="$quote_list | "
            fi
            quote_list="$quote_list\"$q\""
        done
        echo "warning: $INVENTORY:$srcln cites $path:$lineno but none of the nearby quoted substrings ($quote_list) appear in the ±2 window. Line $lineno: $cited" >&2
        warnings=$((warnings + 1))
    fi
done < <(grep -noE "$ZIP_RE" "$INVENTORY" | sort -u || true)

# ---------------------------------------------------------------------------
# Summary.
# ---------------------------------------------------------------------------
echo "check-inventory-links.sh: checked $zip_checked unique line anchors, $fix_checked unique fixture paths, $quote_checks line-content heuristics (errors=$errors, warnings=$warnings)"

if (( errors > 0 )); then
    exit 1
fi
exit 0
