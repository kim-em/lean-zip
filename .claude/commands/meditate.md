# Execute a Meditate Work Item

You are a **meditate** (self-improvement) session. Your job is to improve the
agent workflow by updating skills, commands, and tooling based on accumulated
experience.

**Non-interactive session**: You are running via `claude -p` — there is no human
to answer questions. Never ask for confirmation or approval. Just do the work.

**First, read `.claude/skills/agent-worker-flow/SKILL.md`** for the standard
claim/branch/verify/publish workflow. This document only covers what is specific
to meditate sessions.

## Claiming Your Issue

Use `coordination list-unclaimed --label meditate` to find work for this session type.

## The Meditate Task

The issue body will describe the specific focus — common themes include:
- Consolidating frequently-seen struggle patterns into new or updated skills
- Updating workflow commands that have become stale
- Researching better approaches to recurring proof challenges
- Improving the coordination tooling based on pain points in recent progress entries

### Step 1: Survey recent struggles

Read the last 20 entries in `progress/` (sorted by filename, most recent last).
Look for:
- Repeated "tried 3 approaches, left sorry" patterns
- "Couldn't figure out" or "blocked by" notes
- Similar mistakes appearing in multiple sessions
- Complaints or workarounds that suggest missing guidance

### Step 2: Read existing skills

```bash
ls .claude/skills/
```
Read the relevant SKILL.md files to understand what guidance already exists and
where the gaps are.

### Step 3: Update or create skills

Read `.claude/skills/acquiring-skills/SKILL.md` before writing any new skill.

For each gap or recurring struggle:
- If it fits in an existing skill, add a new section to that SKILL.md
- If it's a new topic area, create `.claude/skills/<topic>/SKILL.md`

### Step 4: Update commands if stale

Read `.claude/commands/feature.md`, `review.md`, `summarize.md`, `meditate.md`,
`plan.md`, `work.md`. If any contain guidance that contradicts recent experience
or refers to obsolete workflows, update them.

### Step 5: Commit and publish

Each skill update should be its own commit. Command updates are a separate commit.
Write a clear progress entry documenting what changed and why.

## Constraints

- Do NOT modify `.claude/CLAUDE.md` — agents update skills and commands, not CLAUDE.md
- Do NOT modify `PLAN.md`
- Only commit `.claude/skills/` and `.claude/commands/` changes (plus progress entry)
- No code changes — this is workflow, not implementation

## Reflect

Run `/reflect`. If it suggests further improvements beyond what you already did,
capture them in a meditate issue for the next session rather than attempting them
in this one.
