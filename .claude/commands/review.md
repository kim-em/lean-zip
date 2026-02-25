# Execute a Review Work Item

You are a **review** session. Your job is to claim and execute a pre-planned review
work item from the issue queue.

**Non-interactive session**: You are running via `claude -p` — there is no human
to answer questions. Never ask for confirmation or approval. Just do the work.

**First, read `.claude/skills/agent-worker-flow/SKILL.md`** for the standard
claim/branch/verify/publish workflow. This document only covers what is specific
to review sessions.

## Claiming Your Issue

Use `coordination list-unclaimed --label review` to find work for this session type.

## Review Focus Areas

Each session should pick **one or two** focus areas and go deep, rather than
superficially covering everything. The issue body will specify what to focus on.
Rotate through these areas across sessions:

**Refactoring and proof improvement** (top priority):
- Are proofs minimal? Can steps be combined?
- Would extracting a lemma improve readability or enable reuse?
- Are there generally useful lemmas worth upstreaming to Lean's standard library?

**Slop detection**:
- Dead code, duplicated logic, verbose comments, unused imports
- Other signs of AI-generated bloat

**Lean idioms**:
- Newer APIs, `grind`, `omega`, `mvcgen`, idiomatic style
- Opportunities to replace `partial` or fuel-based implementations with proper
  termination proofs (pays off later during verification)
- Look for xs[i]! runtime bounds checks that could be replaced with proven-bounds
  access when the bound is already in scope (see CLAUDE.md for constraints)

**Toolchain**:
- Check if a newer stable Lean release is available; if so, upgrade lean-toolchain,
  fix breakage, and revert if tests can't be made to pass

**File size and organization**:
- Files over 500 lines are candidates for splitting; never let a file grow past 1000 lines
- Check with `wc -l Zip/**/*.lean`

**Security**:
- Check for new issues in recent code, verify past fixes

## Module Docstrings

Check that source files in `Zip/`, `ZipTest/`, and `ZipForStd/` have module-level
`/-! ... -/` docstrings describing their purpose. Add or update stale ones. These
replace the source layout table in CLAUDE.md — they must stay accurate.

## Updating Skills

When you discover a recurring proof pattern or encounter a situation not covered by
existing skills in `.claude/skills/`, update the relevant skill file or create a new
one. Do NOT modify `.claude/CLAUDE.md` — that file is off-limits to agents.

## Reflect

Run `/reflect`. If it suggests improvements to skills in `.claude/skills/` or
command files in `.claude/commands/`, make those changes and commit before finishing.
Do NOT modify `.claude/CLAUDE.md` or `PLAN.md` — those are off-limits.
