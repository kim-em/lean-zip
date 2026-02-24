# Execute a Feature Work Item

You are a **feature** (implementation) session. Your job is to claim and execute
a pre-planned implementation work item from the issue queue.

**Non-interactive session**: You are running via `claude -p` — there is no human
to answer questions. Never ask for confirmation or approval. Just do the work.

**First, read `.claude/skills/agent-worker-flow/SKILL.md`** for the standard
claim/branch/verify/publish workflow. This document only covers what is specific
to implementation sessions.

## Claiming Your Issue

Use `coordination list-unclaimed --label feature` to find work for this session type.
The priority order in the worker skill still applies — check for PR-fix issues first.

## Executing Implementation Work

Follow the plan's deliverables. For new native implementations, follow the development
cycle in VERIFICATION.md: type signature → spec theorems → implementation →
conformance tests → proofs.

After each coherent chunk of changes:
- Run `lake build` (use targeted builds like `lake build Zip.Foo.Bar` for faster iteration)
- Run `lake exe test` periodically
- Commit with conventional prefixes: `feat:`, `fix:`, `refactor:`, `test:`, `doc:`, `chore:`

Each commit must compile and pass tests. One logical change per commit.

Failure handling:
- If `lake build` fails on a pre-existing issue: log and work around it
- If a proof is stuck after 3 fundamentally different attempts: leave as `sorry`,
  document what was tried
- 3 consecutive iterations with no commits: end the session and document blockers

## Reflect

Run `/reflect`. If it suggests improvements to skills in `.claude/skills/` or
command files in `.claude/commands/`, make those changes and commit before finishing.
Do NOT modify `.claude/CLAUDE.md` or `VERIFICATION.md` — those are off-limits.
