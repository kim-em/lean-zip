---
name: pr-repair-flow
description: Standard PR-repair workflow for pod `repair` agent sessions. Covers claim/diagnose/fix/verify/push lifecycle and the fix-or-abandon principle.
allowed-tools: Bash, Read, Glob, Grep, Edit, Write
---

# PR Repair Flow for Pod Repair Agents

This skill covers the workflow used by `/repair` sessions. Repair agents
work on PRs, not on feature issues. Their job is to salvage unhealthy PRs
(merge conflicts, failed CI, stuck CI) or close them cleanly when salvage
is not worth doing.

## Core Principle: Fix or Abandon

Repair sessions have exactly two terminal outcomes:

1. **Salvaged** — you pushed a green PR and called `coordination mark-pr-salvaged`.
2. **Abandoned** — you called `coordination close-pr-unsalvageable` after a
   bounded number of failed attempts. This removes `has-pr` from the linked
   issue and adds `replan`, so a fresh plan can be produced.

**There is no escalation to `human-oversight`.** Complex conflicts become
re-implementations via `replan`, not human tickets. If verification keeps
failing, abandon.

## Coordination Commands

| Command | Purpose |
|---|---|
| `coordination list-pr-repair` | Read-only list of PRs needing repair, priority-ordered (`conflict` > `failed` > `stuck`). No label writes. |
| `coordination claim-pr-repair N` | Adds `repair-claimed` label + comment; 30 min cooldown. Fails if already claimed. |
| `coordination mark-pr-salvaged N` | Clears `repair-claimed`, comments salvage summary. Call after a successful push. |
| `coordination close-pr-unsalvageable N "reason"` | Closes PR, adds `unsalvageable`, removes `has-pr` on linked issue, adds `replan`. |

PR repair claims live in a namespace distinct from issue claims. Pod's
housekeeping loop runs `check_dead_pr_claimed_prs` every 10 minutes to
release claims whose owning session has died.

## Step 1: Claim a PR

```
coordination list-pr-repair
```

Pick the top line (priority order is conflict > failed > stuck). Parse the
PR number out of `#<num> [<reason>] <title>` and claim it:

```
coordination claim-pr-repair <pr-number>
```

If the claim output says the PR was claimed by another session in the last
30 minutes, move to the next candidate. If all candidates are claimed,
exit — another dispatch will handle the work later.

## Step 2: Check Out the PR Branch

```bash
gh pr checkout <pr-number>
```

Do **not** create a new branch. You are working on the existing PR's head
branch. The PR will be updated by force-push when you're done.

## Step 3: Diagnose

Look at one thing at a time, in this order:

1. `gh pr view <N> --json mergeable,statusCheckRollup,headRefName,baseRefName`
2. If `mergeable == "CONFLICTING"`: `git fetch origin && git merge origin/<base>`
   (or rebase) to surface the conflicting files.
3. If any check conclusion is `FAILURE`: `gh pr checks <N>` then read the
   failing job's log via `gh run view --log-failed`.
4. If "stuck": the CI suite has been running past the configured threshold.
   Usually this means a worker is hung or a runner was lost. Re-running
   from a fresh commit (`git commit --allow-empty -m "kick CI"`) is a
   reasonable first fix.

## Step 4: Apply the Minimal Fix

- **Merge conflicts**: resolve and commit. Prefer the cleaner of `merge` or
  `rebase` — both produce the same end state but `merge` preserves the
  original commits and is less fiddly if history is messy.
- **Failing CI**: make the smallest change that makes the test pass. Do
  **not** expand scope to refactoring or unrelated cleanup — that belongs
  in separate issues.
- **Stuck CI**: empty commit to trigger a re-run is usually enough. If it
  sticks again, that's a signal to abandon.

## Step 5: Verify

Run the project's own verification — the same build/test flow a `/feature`
session would run before opening a PR. See the project's top-level
`CLAUDE.md` for the exact commands.

**Verification is the arbiter.** Do not push until it passes locally.

## Step 6: Push or Abandon

**If verification passes:**
```bash
git push --force-with-lease
coordination mark-pr-salvaged <pr-number>
```
Auto-merge (already set by `coordination create-pr`) will squash-merge the
PR once the remote CI reports green. Exit the session.

**If verification fails after at most 3 fix → verify cycles:**
```
coordination close-pr-unsalvageable <pr-number> "<reason>"
```
Valid reasons to abandon:
- verification keeps failing despite targeted fixes
- the branch is so stale that redoing the work is cheaper than conflict surgery
- the implementation direction is wrong or has been superseded by other merged work
- CI repair would require effectively reimplementing the feature from scratch

Be specific in the reason — it goes on the closing comment and on the
linked issue, and a future planner will read it when producing a replan.

## Step 7: Exit

Don't poll CI. Don't wait for auto-merge. The session ends once you've
either marked salvaged or closed unsalvageable.

## Labels You'll See

- `repair-claimed` — set by `claim-pr-repair`, cleared by `mark-pr-salvaged`
  / `close-pr-unsalvageable`, or by the housekeeping reconciler if the
  claiming session dies.
- `unsalvageable` — set by `close-pr-unsalvageable` on the PR for
  observability. Not functional.

There is intentionally no `needs-repair` label. Repair candidates are
computed on demand by `list-pr-repair`; a label would drift out of sync.

## What You Will Not Do

- Open new issues (except as part of a `replan` comment if genuinely
  helpful context).
- Escalate to `human-oversight`.
- Keep trying the same fix with minor variations past the 3-cycle budget.
- Fight healthy in-progress CI (the stuck threshold already filters for
  checks past the configured age).
- Modify the project's top-level `.claude/CLAUDE.md` or roadmap files.
