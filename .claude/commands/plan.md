# Plan a Work Item

You are a **planner** session. Your job is to create ONE well-scoped work item
as a GitHub issue, then exit. You do NOT execute any code changes.

## Step 1: Orient

1. `git fetch origin master`
2. `coordination orient` — see open issues (claimed and unclaimed), PRs, attention items
3. `coordination close-stale` — clean up abandoned issues
4. Read the last 5 files in `progress/` (sorted by filename) to understand recent work
5. Read `VERIFICATION.md` to understand the current phase and roadmap
6. Record sorry count: `grep -rc sorry Zip/ || true`

## Step 2: Understand existing plans

Read the **full body** of every open `agent-plan` issue:
```
gh issue list --repo kim-em/lean-zip --label agent-plan --state open --limit 20 \
    --json number,title,body --jq '.[] | "### #\(.number) \(.title)\n\(.body)\n"'
```

Understand what's already planned at the **deliverable level**, not just the title.
Your work item MUST NOT overlap with any existing issue's deliverables.

## Step 3: Decide session type

Read the last 5 progress entries and count session types (implementation, review,
self-improvement). Choose the type that restores balance. Default to alternating:
implementation, then review. Self-improvement every 5th session or when needed.

Priority order for implementation work:
1. PRs needing attention (merge conflicts, failing CI) — create a work item
   to rebase, resolve conflicts, and get the PR green again
2. Next deliverable from the current VERIFICATION.md phase

## Step 4: Write the plan

Design one work item scoped to a single session (~few hundred lines of changes).

The issue body MUST be **self-contained** — a worker will use it without reading
progress history. Include:

- **Session type**: implementation / review / self-improvement
- **Current state**: phase, sorry count, relevant recent changes
- **Deliverables**: specific files to create/modify, what "done" looks like
- **Context**: why this work matters, any dependencies or constraints
- **Verification**: how the worker should verify success (e.g., `lake build`,
  specific tests, sorry count check)

## Step 5: Check for overlap (again)

Before posting, re-fetch open issues to catch any created during your planning:
```
gh issue list --repo kim-em/lean-zip --label agent-plan --state open --limit 20 \
    --json number,title --jq '.[].title'
```

If a new issue appeared that overlaps with your plan, adjust your plan or
create a different work item instead.

## Step 6: Post and exit

Write the plan to `plans/<UUID-prefix>.md`, then:
```
coordination plan "title" < plans/<UUID-prefix>.md
```

Then exit. Do NOT execute any code changes.
