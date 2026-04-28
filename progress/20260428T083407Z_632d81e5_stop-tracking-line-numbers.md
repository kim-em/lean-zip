# Stop tracking line numbers in inventory and skill files (#2345)

**Date**: 2026-04-28 (UTC)
**Session**: 632d81e5-35a5-40f1-b7a5-71cb129cd1e2
**Branch**: agent/632d81e5
**Issue**: #2345 (human-oversight)

## What was accomplished

Closes the structural sources of the anchor-refresh maintenance regime
(~176 of the last 376 master commits at issue-filing time were
inventory anchor refreshes).

### Decision 1 — Strip line-number anchors

- `SECURITY_INVENTORY.md`: 214 line-number anchors stripped
- `.claude/skills/**/*.md`: 56 anchors stripped across 8 skill files
  (excluding pod-bundled skills which are protected)
- `plans/**/*.md`: 25 anchors stripped across 3 plan files
- All `<!-- drift-detector: ... -->` HTML comments removed (the
  opt-out marker has nothing left to suppress once line anchors
  and the line-content / placeholder pass are gone)
- All GitHub `#L42` fragment anchors stripped
- Markdown links collapse from
  `[Foo.lean:N-M](url:N)` → `[Foo.lean](url)`

### Decision 2 — Retire passes (a), (c), (e) of `scripts/check-inventory-links.sh`

- Pass (a) "line-anchor existence" — removed (no anchors to verify)
- Pass (c) "line-content sanity" — removed (no anchors to look up)
- Pass (e) "inverted-range scan" — removed (no ranges to check; the
  issue called out (a)/(c) but (e) is structurally redundant once
  ranges no longer exist)
- Pass (b) "fixture-path existence" — kept (HARD failure)
- Pass (d) "unresolved placeholder PR scan" — kept (warning)

Result: `bash scripts/check-inventory-links.sh` now reports
`78 unique fixture paths, 0 placeholder-PR occurrences (errors=0,
warnings=0)`.

### Decision 3 — Retire `inventory-reconciliation` skill's
one-PR-per-bullet cadence rationale

The "one PR per bullet" rule's stated cost-of-violation was
*"check-inventory-links.sh warnings cannot be attributed to a single
executing PR, and the post-merge line-anchor drift compounds"* —
both reasons disappear once we stop tracking line numbers. The skill
now retains the cadence rule for the legitimate reason (preserving
the bullet-to-PR-number 1:1 mapping in `PROGRESS.md`) and adds a
prominent **"Anchor-refresh PRs are forbidden"** section at the top
naming both the worker action (`coordination skip` with link to
#2345) and the planner action (refuse to create the issue).

The "Line-anchor drift" sub-section is removed entirely.

### Decision 4 — Worker- and planner-side refusal language

The issue's Decision 4 asked for edits to `.claude/commands/plan.md`
and `.claude/skills/agent-worker-flow/SKILL.md`. **Both files are
pod-bundled, hence in `POD_PROTECTED_FILES`**: `coordination create-pr`
rejects PRs touching them. The substantive ask is therefore routed
through `inventory-reconciliation/SKILL.md` (which is project-local
and not pod-protected) — that skill's new top-of-file directive
covers both the worker abort/skip action and the planner refusal.

If pod's bundled skills also need updating, that's a separate
upstream change to the `dev-pod` package, outside this PR's scope.

## Quality metrics

- `lake -R build`: passes (191 jobs, exit 0)
- `bash scripts/check-inventory-links.sh`: passes (errors=0, warnings=0)

## Files changed

13 files, +385 / −556 lines.

## What remains

The 17+ open inventory-anchor-refresh PRs and their backing issues
become obsolete with this PR. They will conflict on `SECURITY_INVENTORY.md`
when merged after this PR. Recommended cleanup: a `/repair` or
follow-up close-out wave that closes those PRs as superseded.
