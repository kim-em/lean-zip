---
name: acquiring-skills
description: Create or update Claude Code skills. Use when creating a new SKILL.md, updating an existing skill, or when the meditate command asks you to write skills.
allowed-tools: Read, Write, Edit, Bash, Glob
---

# Writing Skills

## Practice First

Before writing SKILL.md, perform the workflow manually. If you haven't
actually done the task, do it now before documenting.

Theoretical documentation leads to skills that don't work in practice.
Instructions grounded in real experience capture edge cases and gotchas
that you can't anticipate from the outside.

## YAML Frontmatter

```yaml
---
name: skill-name
description: One-line trigger. Use when [specific situation]. Also use when [other situation].
allowed-tools: Read, Edit, Bash, Glob, Grep
---
```

- **name**: Match the directory name
- **description**: This is the trigger — it determines when the skill
  auto-activates. Write it as conditions, not a summary.
- **allowed-tools**: Comma-separated tools the skill needs

### Writing Good Descriptions

The description must tell Claude *when* to activate, not *what* the skill does.

Good — specific trigger conditions:
- "Use when a Lean 4 tactic fails because this project does not use Mathlib."
- "Use when Lean 4 proofs involve fuel-based recursion or loop invariants."

Bad — vague summaries:
- "A skill for Lean proofs" (when does it fire?)
- "Handles mathlib stuff" (too broad, no trigger)

## Helper Scripts

If the workflow involves repeated commands or multi-step operations,
create helper scripts alongside SKILL.md:

```
.claude/skills/my-skill/
├── SKILL.md
├── helper.sh        # chmod +x, usage comment at top
└── templates/       # Supporting files if needed
```

Reference helpers from SKILL.md with relative paths from the project
root: `.claude/skills/my-skill/helper.sh`.

## Iterate Immediately

After creating a skill, use it on a real task. When you hit friction:

1. Stop and fix the skill now — don't work around the problem
2. Commit the improvement immediately

A skill that gets used and updated beats a "perfect" skill written once.

## Look at Existing Skills

The best reference for skill format is the existing skills in
`.claude/skills/`. Read a few before writing a new one — match the
style and level of detail.
