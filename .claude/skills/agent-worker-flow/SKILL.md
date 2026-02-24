---
name: agent-worker-flow
description: Standard claim/branch/verify/publish workflow for lean-zip agent sessions. Read this skill at the start of any feature, review, summarize, or meditate session.
allowed-tools: Bash, Read, Glob, Grep
---

# Standard Worker Flow for lean-zip Agent Sessions

This skill covers the shared workflow used by all lean-zip worker agents.
Session-specific commands reference this skill rather than duplicating it.

## Step 1: Claim a Work Item

```
coordination orient
```

**Priority order:**
1. **PRs needing attention first**: merge conflicts or failing CI. Check if any
   unclaimed issue references that PR (title containing "rebase PR #N" or "fix PR #N").
   Claim that first — unblocking broken PRs beats starting new work.
2. **Oldest unclaimed issue** of your type:
   ```
   coordination list-unclaimed --label <your-label>
   ```

If the queue is empty, write a brief progress note and exit.

```
coordination claim <issue-number>
```

If the claim fails (race detected), try the next issue. Read the full issue body:
```
gh issue view <N> --repo kim-em/lean-zip --json body --jq .body
```

## Step 2: Set Up

```bash
git checkout -b agent/<first-8-chars-of-session-UUID>
git rev-parse HEAD      # record starting commit
grep -rc sorry Zip/ || true  # record starting sorry count
```

## Step 3: Codebase Orientation

Read the specific files mentioned in the plan/issue. Understand the current state
of code you'll be modifying. Don't read progress history — the issue body provides
that context.

## Step 4: Verify Assumptions

Check that the plan's assumptions still hold:
- Sorry count matches what the issue says
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

## Step 5: Execute

After each coherent chunk of changes:
- `lake build` (use targeted `lake build Zip.Foo.Bar` for faster iteration)
- `lake exe test` periodically
- Commit: `feat:`, `fix:`, `refactor:`, `test:`, `doc:`, `chore:`

Each commit must compile. One logical change per commit.

**Failure handling:**
- `lake build` fails on pre-existing issue → log and work around
- Proof stuck after 3 fundamentally different attempts → leave as `sorry`, document
- 3 consecutive iterations with no commits → end session, document blockers

## Step 5b: Context Health

**If conversation compaction occurs:**
1. Finish your current sub-task (get to compiling state)
2. Commit what you have
3. Skip remaining deliverables — do NOT start new work
4. Go directly to Step 6 then Step 7 with `--partial`

Commit early and often. Each commit is a checkpoint.

## Step 6: Verify

```bash
lake build && lake exe test
grep -rc sorry Zip/ || true    # compare with start
git diff <starting-commit>..HEAD
```
Use `/second-opinion` if available.

## Step 7: Publish

Write a progress entry to `progress/<UTC-timestamp>_<UUID-prefix>.md`:
- Date/time (UTC), session type, what was accomplished
- Decisions made, key patterns discovered
- What remains, sorry count delta

**Full completion:**
```bash
git push -u origin <branch>
coordination create-pr <issue-number>
```

**Partial completion** (did NOT complete all deliverables):
- Progress entry lists: completed deliverables, NOT-completed deliverables and why,
  whether unfinished work needs a new issue
- Use `--partial`:
  ```
  coordination create-pr <N> --partial "feat: what was actually done"
  ```
  This adds `replan` label so the issue is held until a planner re-scopes.

**If you only closed a bad PR** (no code changes):
```bash
gh issue close <N> --repo kim-em/lean-zip \
    --comment "Closed PR #M as not worth salvaging. See progress entry."
```

## Step 8: Reflect

Run `/reflect`. If it suggests improvements to skills or commands, make those
changes and commit before finishing. Do NOT modify `.claude/CLAUDE.md` or
`VERIFICATION.md` — those are off-limits to agents.
