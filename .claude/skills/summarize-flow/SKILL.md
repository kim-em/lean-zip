---
name: summarize-flow
description: Use when executing a summarize-wave PR — covers the post-issue-creation tail deferral pattern (PRs that land between the planner's issue creation and the wave block's submission stay out of wave scope and roll into the next wave). Sibling skill to `agent-worker-flow` (which covers the generic claim/branch/verify/publish lifecycle) and `inventory-reconciliation` (which shares the issue-body-as-source-of-truth invariant via its *Half-closed two-step* section).
allowed-tools: Bash, Read, Grep
---

# Summarize Flow (lean-zip)

Patterns specific to the *summarize* worker session — i.e. the
PR that appends a wave block to `PROGRESS.md` for a defined
range of merged PRs.

The generic claim/branch/verify/publish lifecycle lives in
[`agent-worker-flow`](../agent-worker-flow/SKILL.md). This file
captures only the patterns that are summarize-specific because
the issue body enumerates a *fixed PR list* — a contract shape
no other worker session has.

## Post-issue-creation tail deferral

**Headline rule**: when writing a summarize-wave PR, PRs that
land **between the planner's issue-creation timestamp and the
wave-block PR's submission timestamp** are **out of wave
scope**. The wave block stays faithful to the issue body's
deliverables enumeration; tail PRs are flagged in a *"What
remains (for the next summarize)"* sub-section of the wave
block and queued for the next wave block.

**Rationale — issue-body-as-source-of-truth invariant**: the
issue body is the contract between the planner and the
summarize-worker. The deliverables enumeration in the body
fixes both the wave's PR list and its title's PR-count number.
Expanding scope retroactively (silently absorbing tail PRs)
breaks that contract: the wave-count audit-trail becomes
non-reproducible (a future reader cannot tell from the issue
alone which PRs the wave block will end up covering), and the
title's stated count drifts from the body's enumeration. The
inventory-reconciliation skill's
[*Half-closed two-step*](../inventory-reconciliation/SKILL.md)
section is the cross-skill analogue of the same invariant for
parameter-flip workstreams.

**Mechanism** — the wave block should:

- close the issue's enumerated PR list at the issue-creation
  timestamp's last in-flight PR (i.e. the tail of the body's
  enumeration as written, not the tail of `git log` at
  PR-submission time);
- call out tail PRs by number in a *"What remains (for the
  next summarize)"* paragraph that names each tail PR and the
  rationale (typically *"queued-at-wave-close cleanup landed
  after issue creation"* or *"meditate skill update landed
  after issue creation"*);
- leave the tail PRs' wave assignment to the next planner —
  the next wave's planning-issue body includes them in the
  *next* wave's enumeration, with the tail PRs absorbed at the
  start of that body's deliverables list.

**Boundary**: this pattern applies only to the *summarize*
workflow. Feature/review/repair/meditate issues have single-PR
scope and no wave aggregation, so there is no tail to defer.
(For those workflows, the analogous "scope creep" failure mode
is adding unrelated changes to a single-issue PR, which is
already covered by the project's PR-scope rule in
`~/.claude/CLAUDE.md`.)

## Worked precedent — post-#1931 wave (issue #1964 → PR #1971 → PR #1990)

The pattern was first explicitly applied at the boundary
between the post-#1931 and post-#1971 waves on 2026-04-25:

- **Issue [#1964](https://github.com/kim-em/lean-zip/issues/1964)**
  was created at **2026-04-25T07:38:48Z**. Its body enumerated
  15 PRs (the 1932–1963 inclusive range, plus the post-#1904
  carryover paired-review #1932).
- **PRs [#1967](https://github.com/kim-em/lean-zip/pull/1967),
  [#1968](https://github.com/kim-em/lean-zip/pull/1968),
  [#1969](https://github.com/kim-em/lean-zip/pull/1969)**
  merged at **07:45:32Z, 07:50:37Z, 08:07:51Z** respectively
  — all between issue creation (07:38Z) and the wave PR's
  submission. Two were queued-at-wave-close cleanups (#1967 a
  test-list registration follow-up to PR #1865; #1968 a
  placeholder-PR substitution for the post-#1957 wave); one
  (#1969) was a meditate skill update.
- **PR [#1971](https://github.com/kim-em/lean-zip/pull/1971)**
  was submitted at **08:23:34Z** and merged at 08:24:42Z. Its
  wave block kept the 15-PR enumeration as written in the
  issue body and explicitly **deferred** #1967 / #1968 /
  #1969 to the next wave, with the rationale recorded at
  [`progress/20260425T082152Z_1f65eccf-summarize-post-1931.md`](/home/kim/lean-zip/progress/20260425T082152Z_1f65eccf-summarize-post-1931.md).
- **PR [#1990](https://github.com/kim-em/lean-zip/pull/1990)**
  (next wave, post-#1971) absorbed the three tail PRs at the
  start of its 11-PR enumeration. The wave-count audit-trail
  is fully reproducible from the two waves' issue bodies plus
  this deferral note.

## Wave-block paragraph templates

When deferring tail PRs, the wave block's *"What remains (for
the next summarize)"* paragraph should follow this template:

> **Post-issue-creation tail** (out of wave scope): PRs #N1,
> #N2, #N3 landed at HH:MMZ–HH:MMZ, after the issue was
> created at HH:MMZ. The wave block calls these out as
> [one-line per-PR rationale] but defers them to the next
> wave block.

The next wave's issue body should absorb the deferred tail at
the start of its enumeration, e.g.:

> *Tail-deferred from prior wave (PRs #N1, #N2, #N3 — landed
> 07:45–08:08Z, deferred by PR #M per
> `progress/.../...md` (search for "tail-deferred" header)).*

Both halves of the deferral are PR-numbered and timestamped,
so the audit trail closes without any silent scope expansion.

## When the cadence is appropriate

Apply post-issue-creation tail deferral when **all** of:

- the issue body enumerates a fixed PR list (every summarize
  issue does), and
- one or more PRs merge to master after issue creation but
  before the wave block PR is submitted, and
- the new PRs would, if absorbed, change the wave's PR-count
  number or its enumeration shape.

If the new PRs were already in the issue body's enumeration
(e.g. an in-flight PR the issue lists as expected), they
belong in the wave — they are not "tail" PRs, just
late-merging in-scope PRs. The deferral pattern applies only
to PRs the issue body did **not** anticipate.

## When it is not — single-issue worker PRs

Feature, review, repair, and meditate issues all have
single-PR scope. There is no enumeration of a fixed PR list,
so no tail to defer. If unrelated changes accumulate during a
single-issue session, the correct response is the project's
PR-scope rule: *create a new branch and PR rather than
expanding the current one*. This is documented in
`~/.claude/CLAUDE.md` under "PR Scope" and is **not** the
same pattern as wave-tail deferral.

## Cross-references

- [`agent-worker-flow`](../agent-worker-flow/SKILL.md) — the
  generic claim/branch/verify/publish lifecycle that wraps
  every summarize session. Read first.
- [`inventory-reconciliation`](../inventory-reconciliation/SKILL.md)
  — *Half-closed two-step* section. The same
  issue-body-as-source-of-truth invariant motivates that
  pattern (the param-add issue's body fixes the param shape;
  the flip lands as a separately-issued PR rather than being
  silently absorbed into the param-add PR).

## Scope — what this skill does not cover

- Does not cover the wave block's *content* shape (PR
  enumeration sub-sections, family-closure tables,
  quality-metrics-at-end-of-wave block) — those follow the
  per-wave precedent of the prior `PROGRESS.md` block being
  appended to.
- Does not cover the *meditate* worker's reflective skill
  updates, which can land at any time and are separately
  enumerated in summarize waves as their own sub-section.
