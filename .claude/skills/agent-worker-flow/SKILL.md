---
name: agent-worker-flow
description: Standard claim/branch/verify/publish workflow for pod agent sessions. Read this skill at the start of any feature, review, summarize, or meditate session.
allowed-tools: Bash, Read, Glob, Grep
---

# Standard Worker Flow for Pod Agent Sessions

This skill covers the shared workflow used by all pod worker agents.
Session-specific commands reference this skill rather than duplicating it.

## Coordination Reference

The `coordination` script handles all GitHub-based multi-agent coordination.
Session UUID is available as `$POD_SESSION_ID` (exported by `pod`).
The `gh` CLI defaults to the current repo, so `--repo` is not needed.

| Command | What it does |
|---------|-------------|
| `coordination orient` | List unclaimed/claimed issues, open PRs, PRs needing attention |
| `coordination plan [--label L] "title"` | Create GitHub issue with agent-plan + optional label; body from stdin |
| `coordination create-pr N [--partial] ["title"]` | Push branch, create PR closing issue #N, enable auto-merge, swap `claimed` → `has-pr`. With `--partial`: adds `replan` label. |
| `coordination claim-fix N` | Comment on failing PR #N claiming fix (30min cooldown) |
| `coordination close-pr N "reason"` | Comment reason and close PR #N |
| `coordination list-unclaimed [--label L]` | List unclaimed agent-plan issues (FIFO order); optional label filter |
| `coordination queue-depth [L]` | Count of unclaimed issues; optional label for per-type count |
| `coordination claim N` | Claim issue #N — adds `claimed` label + comment, detects races |
| `coordination skip N "reason"` | Mark claimed issue as needing replan — removes `claimed`, adds `replan` label |
| `coordination add-dep N M` | Add `depends-on: #M` to issue #N's body; adds `blocked` label if #M is open |
| `coordination check-blocked` | Unblock issues whose `depends-on` dependencies are all closed; remove orphan `blocked` from issues whose body has no `depends-on:` lines |
| `coordination check-has-pr` | Remove orphan `has-pr` from open issues that have no currently-open PR closing them (post audit comment) |
| `coordination release-stale-claims [SECS]` | Release claimed issues with no PR after SECS seconds (default 4h); **manual use only** |
| `coordination release-orphan-claims` | Release claims whose owning session UUID is no longer in `.pod/agents/` (liveness-based, no age threshold); **manual use only** |
| `coordination lock-planner` | Acquire advisory planner lock (20min TTL) |
| `coordination unlock-planner` | Release planner lock early |
| `coordination critical-path-depth [L]` | Count unclaimed critical-path issues; optional label filter |
| `coordination set-target N` | Planner sets recommended target agent count (wind-down use only) |

**Issue lifecycle**: planner creates issue (label: `agent-plan`) →
worker claims it (adds label: `claimed`) → worker creates PR closing it
(label swaps to `has-pr`) → auto-merge squash-merges.
Issues marked `replan` (by skip, partial completion, or worker-led
decomposition) are handled by the next planner. Issues with `has-pr` are
excluded from `list-unclaimed` and `queue-depth`.

**Never apply `has-pr` manually.** The label is set automatically by
`coordination create-pr` (full path) and cleared by GitHub's auto-close
on merge of a `Closes #N` PR. Hand-applying it desynchronises the label
from any actual PR — when the supposed PR closes or merges without
`Closes #N`, the issue stays `has-pr` forever and is silently excluded
from the work queue. If you want to "park" an issue while sub-issues
do the work, use `coordination add-dep <parent> <sub>` for each
sub-issue: the parent becomes `blocked`, and `check-blocked` auto-clears
the label when all subs close. The orphan-label housekeeping cycle
(`check-has-pr`, `check-blocked`) auto-removes mis-applied labels and
posts an audit comment on the issue.

**Partial completion**: worker uses `--partial` → label swaps to
`replan`. A planner creates a new issue for remaining work, then closes
the `replan` issue with a link to the new one.

**Worker-led decomposition**: if the claimed issue is too large for one
session, worker creates sub-issues and `coordination skip`s the parent
with a `Decomposed into #X, #Y` breadcrumb comment. The next planner
either closes the parent (sub-issues fully cover it) or narrows it to the
residual scope. See "Assess Scope" (Step 4b) for the full procedure.

**Dependencies**: Issues can declare `depends-on: #N` in their body.
`coordination plan` auto-adds the `blocked` label if any dependency is
open. `check-blocked` (run by `pod` each loop) removes `blocked` when
all dependencies close. Blocked issues are excluded from
`list-unclaimed` and `queue-depth`.

**Branch naming**: `agent/<first-8-chars-of-UUID>`
**Plan files**: `plans/<UUID-prefix>.md`
**Progress files**: `progress/<UTC-timestamp>_<UUID-prefix>.md`

## Step 1: Claim a Work Item

```
coordination orient
```

**Priority order:**
0. **Directives first**: Check for open `directive` issues before anything else.
   These are direct instructions from the project owner — work flowing *down* from
   the human, not work awaiting human attention — and take absolute precedence over
   all other work:
   ```
   coordination list-unclaimed --label directive
   ```
   If any are open and unclaimed, claim the oldest one immediately.
   **Directives cannot be skipped or refused because you disagree with the approach.**
   The valid exits from a `directive` are (a) completing the deliverables and
   **closing the issue yourself**, (b) opening a partial PR and noting the
   remaining scope so a successor can pick it up, or (c) posting a comment
   explaining a genuine technical blocker (e.g. a missing dependency) and
   `coordination skip` with that reason. Do **not** leave a directive open
   with a "for owner closure" note — if the deliverables are in, close it.
   Do not `skip` because you think a different approach is better — that is
   the owner's call, not yours.
1. **Oldest unclaimed issue** of your type:
   ```
   coordination list-unclaimed --label <your-label>
   ```

**Don't repair PRs from a worker session.** PR health (merge conflicts,
failed CI, stuck CI) is the `repair` agent's responsibility; pod dispatches
`/repair` automatically when `coordination list-pr-repair` reports
candidates, ahead of `/plan` / `/work`. Focus on fresh issue work.

If the queue is empty, write a brief progress note and exit.

```
coordination claim <issue-number>
```

**You MUST check the output.** If it says `CLAIM FAILED`, you MUST NOT work
on that issue — pick a different one. Only proceed if the output says
`Claimed issue #N`. Read the full issue body:
```
coordination read-issue <N> --json body --jq .body
```

## Step 2: Set Up

```bash
git checkout -b agent/<first-8-chars-of-session-UUID>
git rev-parse HEAD      # record starting commit
```

**If the branch already exists** (common in reused worktrees): check for an
open PR on it first (`gh pr list --head agent/<id>`). If a PR exists, create
a new branch with a suffix (`agent/<id>-v2`). If no PR exists, reset it to
master: `git checkout agent/<id> && git reset --hard origin/master`.

Record any project-specific quality metrics (e.g. sorry count, test coverage)
as described in the project's CLAUDE.md.

## Step 3: Codebase Orientation

Read the specific files mentioned in the plan/issue. Understand the current state
of code you'll be modifying. Don't read progress history — the issue body provides
that context.

## Step 4: Verify Assumptions

Check that the plan's assumptions still hold:
- Quality metrics match what the issue says
- Files mentioned in the issue still exist and haven't been restructured
- No recently merged PR invalidates the plan

If stale:
```
coordination skip <issue-number> "reason: <what changed>"
```
Go back to Step 1 and try the next issue.

**PR fix plans**: If the plan asks you to fix a broken PR, use judgement. If the
PR is low quality or not worth salvaging:
```
coordination close-pr <pr-number> "reason: <why not worth fixing>"
```

## Step 4b: Assess Scope

After orienting but **before writing code**, check whether the task fits
in a single session. Warning signs it doesn't:

- Target file is 500+ lines and you need to understand most of it
- The work naturally splits into independent sub-lemmas or sub-tasks
- Difficulty feels higher than the issue says

If the issue is too large, **decomposing it into smaller sub-issues is a
normal success path**, not a failure mode. You have the freshest codebase
context and can usually scope sub-tasks more accurately than a planner could
in advance. A good decomposition is more valuable than a failed heroic
attempt — and far better than overrunning the session trying to salvage it.

You may decompose when any of these is true:
- the claimed issue is too large for one session,
- the work naturally splits into independent sub-tasks,
- you can write self-contained successor issues without further investigation.

```bash
# 1. Create self-contained sub-issues. Use `coordination plan` exactly as a
#    planner would — same body template (Current state / Deliverables /
#    Context / Verification), same label. Note: `coordination plan` does
#    only best-effort title-keyword overlap warnings; it does not hold the
#    planner lock and cannot atomically dedupe against concurrent creators.
#    If you see open issues that look related, link or coordinate
#    explicitly in the sub-issue body rather than relying on the warning.
echo "body..." | coordination plan --label feature "Sub-task 1: ..."
echo "body..." | coordination plan --label feature "Sub-task 2: ..."

# 2. Link ordering dependencies if any sub-task must precede another.
#    Do NOT add `depends-on: #<parent>` — the parent is about to be
#    superseded; depend on real predecessor sub-issues instead.
coordination add-dep <sub2> <sub1>

# 3. Leave a machine-readable breadcrumb on the parent. The planner's
#    replan-triage step keys off this exact `Decomposed into #X, #Y`
#    phrasing — keep it on a single line at the start of the comment.
gh issue comment <parent> --body "Decomposed into #<sub1>, #<sub2>

(reason: <one-line scope assessment>)"

# 4. Release the claim by marking the parent for planner triage. This
#    routes through pod's claim-state machinery and clears the in-process
#    `state.claimed_issue` correctly. Do NOT use `gh issue close` directly:
#    it leaves pod's session-end cleanup thinking the issue is still
#    claimed and will attempt a stray `coordination skip` on a closed
#    issue at exit.
coordination skip <parent> "Decomposed into #<sub1>, #<sub2> — see comment"
```

The planner's next replan-triage cycle picks the parent up and either
closes it (if the sub-issues fully cover it) or narrows the body to the
residual scope (if not).

After decomposing, you have two options:

1. **Continue on one of the sub-issues**: claim it via `coordination claim`,
   then return to Step 2 with the sub-issue. Common case when the parent
   was just two work items glued together.
2. **Stop and exit**: if you've used most of your session orienting, write a
   brief progress entry and exit. The next worker will claim a sub-issue.

If you've already done a coherent subset of the parent's work *before*
deciding to decompose, prefer the partial-PR path:

```bash
# Steps 1-3 above (create sub-issues for the remaining work, leave the
# `Decomposed into #X, #Y` breadcrumb on the parent).

# Then land your coherent subset. `--partial` marks the parent `replan`.
coordination create-pr <parent> --partial "feat: <what landed>"
```

The next planner sees the breadcrumb on the parent and closes it with a
forward link to the sub-issues.

## Step 5: Execute

After each coherent chunk of changes:
- Build and test using the project's build commands (see project CLAUDE.md)
- Commit with conventional prefixes: `feat:`, `fix:`, `refactor:`, `test:`, `doc:`, `chore:`

Each commit must compile. One logical change per commit.

**Commit early, create PRs early.** Sessions can terminate at any time.
Pushed-but-not-PR'd work is effectively lost — nobody will find it.

- Commit after every compiling milestone. Don't wait for the full feature.
- WIP commits are fine: `feat: WIP prove helper_lemma (2/4 sorries remain)`
- If 20+ minutes have passed without a commit, stop and commit now.
- Use `coordination create-pr N --partial` as soon as you have useful
  progress, even if incomplete. This saves the work as a visible PR.

**Failure handling:**
- Build fails on pre-existing issue → log and work around
- Stuck after 3 fundamentally different attempts → decompose into sub-issues (Step 4b)
- 3 consecutive iterations with no commits → end session, document blockers
  (does not apply to review or self-improvement sessions)
- If `/second-opinion` or `/reflect` is unavailable, skip and note in progress entry

## Step 5b: Context Health

**If conversation compaction occurs:**
1. Finish your current sub-task (get to compiling state)
2. Commit what you have
3. Skip remaining deliverables — do NOT start new work
4. Go directly to Step 6 then Step 7 with `--partial`

Commit early and often. Each commit is a checkpoint.

## Step 6: Verify

Build and test the project. Compare quality metrics with the starting values.
Review your diff: `git diff <starting-commit>..HEAD`.
Use `/second-opinion` if available.

## Step 7: Publish

Write a progress entry to `progress/<UTC-timestamp>_<UUID-prefix>.md`:
- Date/time (UTC), session type, what was accomplished
- Decisions made, key patterns discovered
- What remains, quality metric deltas

**Full completion:**
```bash
git push -u origin <branch>
coordination create-pr <issue-number>
```

**Once the PR is created, exit.** Do not poll CI, wait for the merge, or
otherwise spin on the PR. Another session will pick up any follow-up work
(e.g. a "fix PR #N" issue if CI fails). Polling burns context and tokens
for no benefit.

**Partial completion** (did NOT complete all deliverables):
- Progress entry lists: completed deliverables, NOT-completed deliverables and why,
  whether unfinished work needs a new issue
- Use `--partial`:
  ```
  coordination create-pr <N> --partial "feat: what was actually done"
  ```

**If you only closed a bad PR** (no code changes):
```bash
gh issue close <N> --comment "Closed PR #M as not worth salvaging. See progress entry."
```

## Step 8: Reflect

Run `/reflect`. If it suggests improvements to skills or commands, make those
changes and commit before finishing. Do NOT modify the project's top-level
CLAUDE.md or roadmap files — those are off-limits to agents.
