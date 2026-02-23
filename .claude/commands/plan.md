# Plan a Work Item

You are a **planner** session. Your job is to create well-scoped, atomic work
items as GitHub issues, then exit. You do NOT execute any code changes.

## Step 1: Orient

1. `git fetch origin master`
2. `coordination orient` — see open issues (claimed and unclaimed), PRs, attention items
3. Read the last 5 files in `progress/` (sorted by filename) to understand recent work
4. Read `VERIFICATION.md` to understand the current phase and roadmap
5. Record sorry count: `grep -rc sorry Zip/ || true`

Note: `close-stale` runs automatically in `./go` before dispatch.

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

Design work items, each scoped to a single session (~few hundred lines of changes).

**Atomicity rule**: each issue must have a single logical concern. All its
deliverables should be tightly related — not independent tasks that happen to
touch the same area of the codebase.

Litmus test: "Could a worker skip deliverable X and still meaningfully complete
the issue?" If yes, X belongs in a separate issue.

Common bundling mistakes:
- Mixing mechanical cleanup (dead code removal) with exploratory work (proof audit)
- Combining review of unrelated modules into one issue
- Pairing a GitHub-level task (close a PR) with code changes

If your orientation reveals multiple orthogonal pieces of work, create
**multiple issues** — one per concern. This is better than one large issue
because workers can claim and execute them in parallel.

Each issue body MUST be **self-contained** — a worker will use it without reading
progress history. Include:

- **Session type**: implementation / review / self-improvement
- **Current state**: phase, sorry count, relevant recent changes
- **Deliverables**: specific files to create/modify, what "done" looks like
- **Context**: why this work matters, any dependencies or constraints
- **Verification**: how the worker should verify success (e.g., `lake build`,
  specific tests, sorry count check)

## Step 5: Atomicity and overlap check

**Atomicity**: re-read each issue's deliverables. Could any deliverable be
removed while the rest still forms a complete, meaningful work item? If so,
that deliverable belongs in its own issue. Split until each issue is atomic.

**Overlap**: re-fetch open issues to catch any created during your planning:
```
gh issue list --repo kim-em/lean-zip --label agent-plan --state open --limit 20 \
    --json number,title --jq '.[].title'
```

If a new issue appeared that overlaps with your plan, adjust or drop the
overlapping issue.

## Step 6: Post and exit

For each issue, write the plan body to `plans/<UUID-prefix>-N.md` (where N
is 1, 2, ... for multiple issues, or omitted for a single issue), then post:
```
coordination plan "title" < plans/<UUID-prefix>-N.md
```

Then exit. Do NOT execute any code changes.

**Note**: The planner lock is managed by `./go` — do NOT call
`coordination lock-planner` or `coordination unlock-planner` yourself.
