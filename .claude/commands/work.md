# Execute a Work Item

You are a **worker** session. Your job is to claim a pre-planned work item from
the issue queue and execute it. The plan is in the issue body — you do NOT need
to read progress history or decide what to work on.

**Non-interactive session**: You are running via `claude -p` — there is no human
to answer questions. Never ask for confirmation or approval. Just do the work.

## Step 1: Claim a work item

List unclaimed issues and pick the oldest:
```
coordination list-unclaimed
```

If the queue is empty, write a brief progress note and exit.

Pick the first (oldest) issue. Claim it:
```
coordination claim <issue-number>
```

If the claim fails (already claimed or race detected), try the next issue.

Read the full issue body — this is your plan:
```
gh issue view <issue-number> --repo kim-em/lean-zip --json body --jq .body
```

## Step 2: Set up

Create a branch:
```
git checkout -b agent/<first-8-chars-of-session-UUID>
```

Record the starting commit: `git rev-parse HEAD`
Record the sorry count: `grep -rc sorry Zip/ || true`

## Step 3: Codebase orientation

Read the specific files mentioned in the plan. Understand the current state of
the code you'll be modifying. Don't read progress history — the plan already
provides that context.

## Step 4: Verify assumptions

Check that the plan's assumptions still hold:
- Sorry count matches what the plan says
- Files mentioned in the plan still exist and haven't been restructured
- No recently merged PR invalidates the plan

If assumptions are stale:
```
coordination skip <issue-number> "reason: <what changed>"
```
Then go back to Step 1 and try the next issue.

**PR fix plans**: If the plan asks you to fix a broken PR (merge conflicts,
failing CI), use your judgement. If the PR's changes are low quality, stale,
or not worth salvaging, you can close it instead of fixing it:
```
coordination close-pr <pr-number> "reason: <why it's not worth fixing>"
```
Document the decision in your progress entry.

## Step 5: Execute

Follow the plan's deliverables. After each coherent chunk of changes:
- Run `lake build` (use targeted builds like `lake build Zip.Foo.Bar` for faster iteration)
- Run `lake exe test` periodically
- Commit with conventional prefixes: `feat:`, `fix:`, `refactor:`, `test:`, `doc:`, `chore:`

Each commit must compile and pass tests. One logical change per commit.

Failure handling:
- If `lake build` fails on a pre-existing issue: log and work around it
- If a proof is stuck after 3 fundamentally different attempts: leave as `sorry`,
  document what was tried
- 3 consecutive iterations with no commits: end the session and document blockers
- If conversation compaction has occurred: wrap up immediately (see Step 5b)

## Step 5b: Monitor context health

**Compaction is your signal to wrap up.** If you see a system message about
conversation compaction, or notice that earlier context has been summarized:

1. **Finish your current sub-task** (get to a compiling state)
2. **Commit what you have** — a clean partial commit is valuable
3. **Skip remaining deliverables** — do NOT start new work after compaction
4. **Go directly to Step 6 (Verify)** then Step 7 (Publish) with `--partial`

Compaction means you've used most of your context window. Quality degrades
from here — you're more likely to re-read files you already read, forget
decisions you made, or produce inconsistent code. Wrapping up now and letting
a fresh session continue is strictly better than grinding through.

**Commit early, commit often.** Don't wait until all deliverables are done.
After each deliverable (or coherent sub-unit), commit. These intermediate
commits are checkpoints — if you hit context pressure later, you've already
banked your progress. Each commit must compile (`lake build`).

## Step 6: Verify

- `lake build && lake exe test` one final time
- Check sorry count: `grep -rc sorry Zip/ || true` — compare with start
- Review changes: `git diff <starting-commit>..HEAD`
- Use `/second-opinion` if available

## Step 7: Publish

Write a progress entry to `progress/<UTC-timestamp>_<UUID-prefix>.md` with:
- Date/time (UTC), session type, what was accomplished
- Decisions made, key proof patterns discovered
- What remains, sorry count delta

**Partial completion**: If you did NOT complete all deliverables in the issue:
- In your progress entry, clearly list:
  - Which deliverables were **completed**
  - Which deliverables were **NOT completed** and why (stuck proof, ran out of
    iterations, missing prerequisite, etc.)
  - Whether the unfinished work needs a new issue (so the planner can reschedule)
- Use `--partial` with a PR title describing what was *actually done*:
  ```
  coordination create-pr <N> --partial "feat: prove helper lemmas for inflate_deflateFixed"
  ```
  This uses "Partial progress on #N" instead of "Closes #N" in the PR body,
  and adds a `needs-replan` label so the issue is held out of the unclaimed
  queue until a planner re-scopes the remaining work.

**If you completed all deliverables**, commit, push, and create a PR normally:
```
git push -u origin <branch>
coordination create-pr <issue-number>
```

**If you only closed a bad PR** (no code changes), close the associated
issue instead of creating a PR:
```
gh issue close <issue-number> --repo kim-em/lean-zip \
    --comment "Closed PR #N as not worth salvaging. See progress entry."
```

## Step 8: Reflect

Run `/reflect`. If it suggests improvements to `.claude/CLAUDE.md`, commands,
or skills, make those changes and commit before finishing.
