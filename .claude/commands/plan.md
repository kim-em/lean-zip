# Plan a Work Item

You are a **planner** session. Your job is to create well-scoped, atomic work
items as GitHub issues, then exit. You do NOT execute any code changes.

## Step 1: Orient

1. `git fetch origin master`
2. `coordination orient` — see open issues (claimed and unclaimed), PRs, attention items
3. Read the last 5 files in `progress/` (sorted by filename) to understand recent work
4. Read the project's roadmap document to understand current phase
5. Record quality metrics as described in the project's CLAUDE.md

## Step 1b: Check for human oversight directives

Before creating any new work, check for open `human-oversight` issues:
```
gh issue list --label human-oversight --state open --json number,title,labels \
    --jq '.[] | select(.labels | all(.name != "has-pr")) | "#\(.number) \(.title)"'
```

These are direct instructions from the project owner. Treat them as highest priority:
- **Do not create issues that overlap with or supersede a `human-oversight` issue**
- **Do not close `human-oversight` issues** — only the owner closes them
- **Do not add `replan` to `human-oversight` issues** — they stay open until done
- If a `human-oversight` issue is already claimed, continue to Step 2 (workers are on it)
- If unclaimed, prioritise creating any supporting infrastructure issues first, then exit
  — the next worker will claim the directive itself

## Step 2: Merge ready PRs

Before anything else, merge all open PRs that are mergeable with passing CI:
```bash
gh pr list --state open \
  --json number,mergeable,statusCheckRollup \
  --jq '.[] | select(
    .mergeable == "MERGEABLE" and
    (.statusCheckRollup | length > 0) and
    (.statusCheckRollup | all(.conclusion != "FAILURE" and .conclusion != "CANCELLED"))
  ) | .number' \
| xargs -I{} gh pr merge {} --squash --delete-branch
```

Never skip this step. Downstream agents are blocked on `main` until merged PRs land.

## Step 3: Triage `replan` issues (before creating new work)

Fetch the list:
```
gh issue list --label replan --state open --json number,title,body \
    --jq '.[] | "### #\(.number) \(.title)\n\(.body)\n"'
```

Process **all** replan issues before creating any new issues.
For each, exactly one of:
- **Work already done** (a subsequent PR merged it): close with a note
- **Plan stale / approach changed**: create a corrected replacement issue, close original linking forward
- **Partial progress**: create issue for remaining deliverables, close original linking forward
- **Worker-decomposed**: the worker created sub-issues before releasing
  the claim. Detect via a comment that starts with `Decomposed into #` and
  lists the sub-issue numbers (workers must leave this breadcrumb before
  `coordination skip` or `coordination create-pr --partial`). Read the
  sub-issues and decide:
  - sub-issues fully cover the parent → close the parent with a forward
    link (do NOT re-create the sub-issues);
  - residual scope remains → narrow the body to that residual and remove
    the `replan` label so workers can claim it again.
  In the partial-PR variant the parent will also have a merged or open PR
  reference; treat it the same way and rely on the merged PR to record the
  partial work.
- **Still valid, body still accurate**: remove the `replan` label (`gh issue edit N --remove-label replan`) to re-open for workers
- **Still valid, body stale**: update the issue body with current state, then remove the `replan` label

**Never delegate replan triage to a worker** — that is the planner's job.

## Step 4: Create fix issues for broken PRs

Check for PRs with merge conflicts or failing CI:
```bash
gh pr list --state open --json number,title,mergeable,statusCheckRollup \
  --jq '.[] | select(
    .mergeable == "CONFLICTING" or
    (.statusCheckRollup | any(.conclusion == "FAILURE"))
  ) | "#\(.number) \(.title) \(if .mergeable == "CONFLICTING" then "[CONFLICTS]" else "[CI FAILED]" end)"'
```

For each broken PR, check if a fix issue already exists:
```bash
gh issue list --label agent-plan --state open --json number,title \
  --jq '.[].title' | grep -i "PR #N"
```

If no fix issue exists, **create one immediately** using `coordination plan`.
These fix issues take priority over all new feature work.

## Step 5: Understand existing plans

Read the **full body** of every open `agent-plan` issue:
```
gh issue list --label agent-plan --state open --limit 20 \
    --json number,title,body --jq '.[] | "### #\(.number) \(.title)\n\(.body)\n"'
```

Understand what's already planned at the **deliverable level**, not just the title.
Your work item MUST NOT overlap with any existing issue's deliverables.

## Step 6: Write new issues

Work types: **`feature`**, **`review`**, **`summarize`**.
Target roughly 2:1 feature:review during implementation; 1:1 during cleanup.

**Summarize trigger**: when 10+ PRs merged since last summarize issue closed.

Each issue body MUST be **self-contained**:
- **Current state**, **Deliverables**, **Context**, **Verification**

**Sizing**: max 3 deliverables, ~2 files, ~200 lines. Over 300 lines → split.
When in doubt, split. Each issue must have a single logical concern.

**Stage granularity**: If the project roadmap has "stages" or "phases", **never
create an issue that spans multiple stages**. Each issue belongs to exactly one
stage.

Within a stage, maximise parallelism: if the stage contains independent items
(e.g., "transcribe all pages", "formalise each definition"), create a **separate
issue per item** (or per small batch of items) so workers can execute them
concurrently. If the PLAN.md gives explicit parallelisation instructions for a
stage, follow them. The goal is many small, independent issues — not one large
issue per stage.

If you cannot yet determine the scope of a stage because it depends on earlier
output (e.g., item discovery), it is fine to create the issue for the whole
stage. **Workers are allowed and encouraged to decompose oversized issues
themselves** — they have the freshest codebase context and can usually scope
sub-tasks more accurately than you can in advance. See the `agent-worker-flow`
skill's "Assess Scope" step for the worker-side mechanics.

If you specifically want planner-led decomposition (e.g., the split needs
cross-issue coordination you can see and the worker cannot), include a note in
the body asking the claiming worker to
`coordination skip N 'needs planner decomposition: <reason>'` instead of
splitting it themselves. Default is worker-led decomposition; require
planner-led only when there is a clear reason.

**Critical-path issues**: When you create an issue that blocks all other planned
work (e.g., the first issue in a sequential pipeline, or a bottleneck that many
blocked issues depend on), use `--critical-path` when posting it:
```
coordination plan --label feature --critical-path "title" < plans/body.md
```
This tells the dispatcher to assign a worker immediately, bypassing the normal
queue-size threshold. Use sparingly — only for genuine pipeline bottlenecks where
no other useful work can proceed until this issue is done.

**How many issues to create**: the dispatcher exports `POD_MIN_QUEUE`,
`POD_QUEUE_DEPTH`, and `POD_QUEUE_DEFICIT` (= target unclaimed minus current
unclaimed). Your target for this cycle is roughly `POD_QUEUE_DEFICIT` new
atomic issues, capped at **10** so a single planner doesn't run too long or
exhaust context. If the deficit is 0 or negative, create no new issues and
exit. If the deficit is large, prefer breadth — one small issue per
independent unit — over depth; leftover deficit will be handled by the next
planner cycle. The previous "keep under 3 unclaimed" rule is obsolete: the
dispatcher runs a planner exactly when the queue drops below `min_queue`, so
refilling to that level is the whole job.

No transitive blocking. Keep work types mixed.

After writing, re-fetch open issues to check for overlap:
```
gh issue list --label agent-plan --state open --limit 20 \
    --json number,title --jq '.[].title'
```

## Step 7: Post and exit

For each issue, write the plan body to `plans/<UUID-prefix>-N.md`, then post:
```
coordination plan --label <feature|review|summarize> "title" < plans/<UUID-prefix>-N.md
```

**Agent pool sizing**: By default, do NOT call `coordination set-target`.
The operator configured it; the advisory merge is `min(config, advisory)`,
so calling it can only *shrink* the pool, never grow it — and shrinking
mid-project starves workers.

Use it only when the project is actually winding down. Two cases:

- **Fully converged** (zero unclaimed, zero claimed, zero broken PRs, and
  you created no new issues because there is nothing left to plan):
  `coordination return-to-human`. Verify all three are zero first:
  ```bash
  coordination queue-depth
  gh issue list --label claimed --state open --json number --jq 'length'
  gh pr list --state open --json number,mergeable,statusCheckRollup \
    --jq '[.[] | select(.mergeable == "CONFLICTING" or (.statusCheckRollup | any(.conclusion == "FAILURE")))] | length'
  ```

- **Tail** (only a small number of in-flight streams remain and further
  planning genuinely depends on their outcome): `coordination set-target N`
  where N = currently claimed issues. Narrows the pool as you wrap up.

Any other case — including a cycle where you happened to create few or
zero issues during active development — leave `set-target` alone.

Do **not** call `coordination set-min-queue`. That command is for the
operator, not the planner.

Then exit. Do NOT execute any code changes.

**Note**: The planner lock is managed by `pod` — do NOT call
`coordination lock-planner` or `coordination unlock-planner` yourself.
