# Plan a Work Item

You are a **planner** session. Your job is to create well-scoped, atomic work
items as GitHub issues, then exit. You do NOT execute any code changes.

## Step 1: Orient

1. `git fetch origin master`
2. `coordination orient` — see open issues (claimed and unclaimed), PRs, attention items
3. Read the last 5 files in `progress/` (sorted by filename) to understand recent work
4. Read `VERIFICATION.md` to understand the current phase and roadmap
5. Record sorry count: `grep -rc sorry Zip/ || true`

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

Also check **open unclaimed queue composition**, not just session history.
If the queue is dominated by one work type (especially blocked proofs),
choose a different unblocked type.

Priority order for implementation work:
1. PRs needing attention (merge conflicts, failing CI) — create a work item
   to rebase, resolve conflicts, and get the PR green again
2. Next deliverable from the current VERIFICATION.md phase

## Step 4: Write the plan

Design work items, each scoped to complete well within a single context window.

**Sizing rules:**
- **Max 3 deliverables** per issue. If you have 4+, split into multiple issues.
- **Typically 2 files modified** (excluding progress/plan files). 3-4 is
  fine if they're tightly coupled (e.g. implementation + spec + test for
  one feature). 5+ is almost certainly too big.
- **One theorem per issue** for non-trivial proofs. A theorem and its direct
  helper lemmas (in the same file) are one unit. Two independent theorems
  are two issues — even if they're in the same file.
- **~200 lines of new code** is the target. Over 300 is a yellow flag.
  Over 500 means the issue should almost certainly have been split.

**Estimation heuristic:** count the deliverables, multiply by the hardest
one's estimated difficulty (1=mechanical, 2=moderate, 3=requires exploration).
If the product exceeds 5, split the issue.

**When in doubt, split.** Two small issues that finish cleanly are always
better than one large issue that triggers compaction and produces sloppy
partial work. Workers can always claim the next issue immediately.

**Atomicity rule**: each issue must have a single logical concern. All its
deliverables should be tightly related — not independent tasks that happen to
touch the same area of the codebase.

Litmus test: "Could a worker skip deliverable X and still meaningfully complete
the issue?" If yes, X belongs in a separate issue.

**Statement/proof split**: When proofs are substantial and other agents
could use the lemma statements for downstream work, split into two issues:
1. First issue: write theorem statements proved with `sorry`
2. Second issue: prove the theorems (replace `sorry` with real proofs)

The second issue's body must include `depends-on: #N` (where N is the first
issue's number). The coordination script auto-adds a `blocked` label, and
workers won't see it until the first issue closes. This lets other planners
create downstream work that uses the statements before proofs are ready
(Lean treats `sorry` as an axiom). For quick/straightforward proofs, a
single issue covering both statements and proofs is fine.

**Speculative planning on sorried lemmas**: If you're confident that
sorried lemmas from a recent issue are true and just need proofs, you can
create issues for later theorems that depend on those lemma *statements*
— especially if those later theorems are important and aligned with the
project's major goals. This is how agents build on each other's work
without waiting for every proof to complete.

**Queue health check**: Before creating issues, run `coordination list-unclaimed`.
If there are **<3 unclaimed unblocked issues** and **≥5 blocked issues**,
create unblocked non-proof work before adding new proof dependencies.
Candidates: review, refactor, benchmarks, infra/tooling, self-improvement,
or preliminary scaffolding for later VERIFICATION.md phases.

**No transitive blocking**: Never `depends-on` an issue that is itself
`blocked`. Depend only on unblocked issues.

**Work type diversity**: Keep the open queue mixed. If it's mostly one
type, create a different type.

**Updating dependencies on existing issues**: When you create a new issue that
is a prerequisite for an *existing* open issue, update the existing issue to
add the dependency. The `depends-on` line MUST be in the issue **body** (not
a comment), because `check-blocked` only scans bodies for automatic unblocking.

```
# Add depends-on to body and blocked label in one step
coordination add-dep <existing-issue> <new-issue>
# Add an explanatory comment
gh issue comment <existing-issue> --repo kim-em/lean-zip \
    --body "Blocking on #<new-issue> (<brief reason>)."
```

If the existing issue is already claimed, still add the body dependency and
comment so the worker is aware, but don't add `blocked` (the worker can
decide how to handle it).

**Handling `needs-replan` issues**: When a worker makes partial progress, the
issue gets a `needs-replan` label (excluded from `list-unclaimed`). During
orientation, check for these:
```
gh issue list --repo kim-em/lean-zip --label needs-replan --state open --limit 10 \
    --json number,title --jq '.[] | "#\(.number) \(.title)"'
```
For each `needs-replan` issue:
1. Read the partial PR and progress entry to understand what was done
2. Create a **new issue** for the remaining work, referencing the original:
   - Include "Continues #N" and a link to the partial PR for context
   - Describe only the remaining deliverables (what was NOT done)
   - Add any new context learned from the partial attempt
3. Close the original `needs-replan` issue with a comment linking forward:
   ```
   gh issue close <N> --repo kim-em/lean-zip \
       --comment "Remaining work replanned in #<new-issue>. Partial progress in PR #<partial-pr>."
   ```
4. If other open issues had `depends-on: #<N>`, update them to depend on
   the new issue instead

**Filling gaps from partial completions**: When orientation reveals that a PR
made partial progress on an issue (the issue was closed but deliverables remain
unfinished, or a PR title doesn't match the issue scope):
1. Create a new issue for the remaining work, referencing the original issue
   and the partial PR for context
2. If other existing issues depended on the original (now partially-done) issue,
   update their dependencies to point at the new issue instead

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

**Note**: The planner lock is managed by `pod` — do NOT call
`coordination lock-planner` or `coordination unlock-planner` yourself.
