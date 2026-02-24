# Execute a Summarize Work Item

You are a **summarize** session. Your job is to produce an accurate, architectural
summary of project progress that honestly identifies both achievements and limitations.

**Non-interactive session**: You are running via `claude -p` — there is no human
to answer questions. Never ask for confirmation or approval. Just do the work.

**First, read `.claude/skills/agent-worker-flow/SKILL.md`** for the standard
claim/branch/verify/publish workflow. This document only covers what is specific
to summarize sessions.

## Claiming Your Issue

Use `coordination list-unclaimed --label summarize` to find work for this session type.

## The Summary Task

### Step 1: Read the project specification

Find and read the top-level specification document (typically `VERIFICATION.md` or
equivalent) to understand the project's intended goals. This is the ground truth
against which you measure progress.

### Step 2: Read the current PROGRESS.md

Understand what the project currently claims to have achieved.

### Step 3: Survey recent work

- Read the last 15 entries in `progress/` (sorted by filename, most recent last)
- Fetch titles and bodies of PRs merged since the last `summarize` issue was closed:
  ```
  gh pr list --state merged --limit 30 --repo kim-em/lean-zip \
      --json number,title,mergedAt --jq '.[] | "#\(.number) \(.title)"'
  ```

### Step 4: Inspect the codebase

- List source files and read their module-level `/-! ... -/` docstrings to understand
  what exists (don't read full file contents unless needed)
- Read the key top-level **theorem statements** (not proofs) in main verification files
- Note hypothesis lists — these reveal scope restrictions (e.g. fuel bounds, size limits)
- Record the current sorry count: `grep -rc sorry` in source directories

### Step 5: Produce an updated PROGRESS.md

Write an updated `PROGRESS.md` that:

**Accurately reflects:**
- Current sorry count and phase
- What is actually proved vs. what has a sorry placeholder

**Describes the proof architecture structurally** (not just a flat theorem list):
- What are the layers? What bridges what?
- Which theorems are characterizing properties vs. algorithmic correspondence?
  (Be explicit about this distinction — it matters for evaluating what is proved)

**Identifies flaws and limitations honestly:**
- Hypotheses in key theorems that restrict scope beyond what the spec intended
  (size bounds, fuel parameters, partial fuel-independence proofs)
- Remaining sorries and what they block
- Gaps between stated goals and proved results
- Where theorems prove algorithmic correspondence rather than mathematical
  characterization, and whether that matters for the stated goals

**Is honest in its framing:**
- "proved X for inputs < 10MB" not "proved X"
- "proved correspondence between two algorithms" not "proved correctness"
- Identifies what remains to close the gap to the full specification goal

## Constraints

- Do NOT modify any code or proof files
- Commit ONLY `PROGRESS.md` changes
- The progress entry for this session should note what was changed and why

## Reflect

Run `/reflect`. If it suggests improvements to skills in `.claude/skills/` or
command files in `.claude/commands/`, make those changes and commit before finishing.
Do NOT modify `.claude/CLAUDE.md` or `VERIFICATION.md` — those are off-limits.
