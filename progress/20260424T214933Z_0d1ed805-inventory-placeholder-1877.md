# Session 0d1ed805 — feature, issue #1877 (inventory placeholder-PR substitutions)

- **Date**: 2026-04-24T21:49Z
- **Type**: feature
- **Issue**: #1877 — *Inventory: substitute three `#N` placeholder-PR
  rows in `SECURITY_INVENTORY.md` (:641 -> #1848, :683 -> #1857,
  :1106 -> #1866)*

## Accomplishments

Single doc-only commit touching three `#N` placeholder tokens in
`SECURITY_INVENTORY.md`, zero code churn. Closed exactly the three
drifts the post-#1868 detector flagged:

1. **:641** — `CD-entry empty-filename rejection — PR #N` → `— PR #1848`
   (*CD-entry empty-filename rejection* row; PR #1848 merged
   `b58a8c7`, 2026-04-24T18:04:03Z).
2. **:683** — `CD-entry empty-entry CRC invariant rejection — PR #N`
   → `— PR #1857` (PR #1857 merged `7ee629f`, 2026-04-24T19:22:17Z).
3. **:1106** — `... does not emit PAX extended headers | #N |
   archive-slip |` → `| #1866 |` (`pax-path-nul-in-value.tar` corpus
   row; PR #1866 merged `2dddfa8`, 2026-04-24T20:13:45Z).

All three line numbers matched the issue exactly at claim time (no
line drift since planner snapshot).

## Verification

- `grep -c '#N\b' SECURITY_INVENTORY.md`: **3 → 0** (exact match for
  the issue's expected delta N → N-3).
- `grep -n 'PR #N\b\| #N —\|— PR #N' SECURITY_INVENTORY.md`: zero
  matches post-substitution (was three pre-).
- `bash scripts/check-inventory-links.sh 2>&1 | tail -1`:
  `errors=0, warnings=91` — down from the baseline `errors=0,
  warnings=94` (exact −3 delta). `placeholder-PR occurrences=3 → 0`.
- `git diff --stat SECURITY_INVENTORY.md`: 1 file changed, 3
  insertions(+), 3 deletions(-).
- No other inventory anchors, throw-lines, or range citations
  touched — the detector's remaining 91 warnings are the pre-existing
  prose-substring false-positives catalogued by the summarize
  post-#1843 entry (out of scope per the issue).
- No `lake build` / `lake exe test` run (doc-only change per the
  inventory-PR convention; belt-and-braces `lake exe test` can be run
  in CI but is not required for single-file markdown edits).

## Notes

- Sibling of the PR-attribution-hygiene cluster: #1794, #1796, #1836,
  #1850, #1867, #1868. PR #1867 was the post-#1843 bookkeeping sweep
  (substituted 5 placeholders); this PR closes the three remaining
  drifts that #1867 couldn't reach because the feature PRs (#1848,
  #1857, #1866) hadn't yet merged at #1867's drafting time.
- One-shot → sweep → detector cadence preserved: #1867 was the sweep,
  #1868 added the detector, and this is the minimal per-placeholder
  fix before the detector resumes catching new drifts from the next
  wave.
- The remaining 91 warnings from the detector are prose-substring
  false-positives (e.g. "issue #N" inside anchor blocks, `#N123`-style
  fragments). Out of scope per the issue; file as tooling-refinement
  if motivated.

## Quality metrics

No code changes. Sorry count unaffected (inventory doc only).
