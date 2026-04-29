# Inventory cleanup: drop stale `once #2393 lands` qualifier (issue #2400)

- **UTC timestamp**: 2026-04-29T20:01:01Z
- **Session**: `fb4f25bc-88d8-473b-ba8f-9158d5d68dbf` (`/feature`)
- **Issue**: #2400
- **Branch**: `agent/fb4f25bc`

## What landed

Single-line, prose-only substitution in `SECURITY_INVENTORY.md`
line 853 (the *Paired review of PR #2383* subsection's trailing
parenthetical). Replaces the post-merge stale forward-pointer

> *Scaffold variant sub-section once the follow-up #2393 lands*

with the `inventory-reconciliation` *Executed past-tense one-liner*
shape

> *Scaffold variant sub-section, landed in PR #2399 closing #2393*

PR #2399 merged 2026-04-29 at commit `78954fb`, so the
*"once it lands"* framing was actively misleading: a current
reader following the link to
`.claude/skills/inventory-reconciliation/SKILL.md` already finds
the *Scaffold variant* sub-section in place. The substitution
keeps the SKILL.md link target identical and changes only the
prose immediately following the link.

## Verification

- `grep -nE "once.*lands|when.*lands|#2393" SECURITY_INVENTORY.md`
  returns exactly one match — the new past-tense PR #2399 citation.
  No residual *"once X lands"* / *"when X lands"* / unmerged-#2393
  phrasing anywhere in the inventory.
- `bash scripts/check-inventory-links.sh` →
  `checked 78 unique fixture paths, 8 placeholder-PR occurrences (errors=0, warnings=0)`.
- `lake build` → `Build completed successfully (201 jobs).`
- `lake exe test` → `All tests passed!` (full suite, including
  benchmarks and fuzzers).
- Sorry count: 0 (unchanged).
- `git diff origin/master..HEAD -- SECURITY_INVENTORY.md` (after
  commit) shows exactly one substituted line; no whitespace churn,
  no collateral edits.

## Notes

- The *Scaffold variant* precedent in
  `.claude/skills/inventory-reconciliation/SKILL.md` is now
  self-citing — no inventory back-pointer carries an unmerged-#2393
  qualifier.
- #2392 (the still-open Linux-gated *body fill-in* follow-up) is
  untouched; it is a separate workstream and its qualifier in the
  inventory remains independent of this fix-up.
- Out of scope items per the issue body (no SKILL.md edits, no
  anchor-refresh sweeps, no PLAN.md edits, no broader paragraph
  rewording) all respected — the diff is the single targeted
  substitution.

## Worktree hygiene

The worktree arrived with stale uncommitted modifications to
`.claude/CLAUDE.md` (off-limits) and
`.claude/skills/agent-worker-flow/SKILL.md` left over from a
previous session. No PR existed on the branch, so per the
agent-worker-flow skill's *reuse-with-no-PR* path, those files
were `git restore`d to master before the inventory edit so the
PR would be a clean single-line diff.
