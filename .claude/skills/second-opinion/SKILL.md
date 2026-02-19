---
name: second-opinion
description: Get a second opinion from OpenAI Codex. Use when the user asks for a second opinion, wants to validate an approach, or says "let's check with Codex". Works for planning, code review, implementation decisions, bug diagnosis, or final review.
allowed-tools: Bash, Read, Grep, Glob
---

# Second Opinion from Codex

Get a second perspective from OpenAI Codex on your current work. Codex can review plans, implementations, bug diagnoses, or provide feedback at any stage.

## Quick Usage

```bash
# Ask Codex for a second opinion with context via stdin
.claude/skills/second-opinion/codex-opinion "What issues might exist in this approach?"

# Pipe in specific context
git diff --staged | .claude/skills/second-opinion/codex-opinion "Review these changes for bugs or issues"

# Review a specific file
cat src/main.ts | .claude/skills/second-opinion/codex-opinion "What could be improved here?"
```

The wrapper script automatically:
- Runs Codex with full tool access (`--full-auto`)
- Points Codex to the current Claude Code conversation log for full context
- Runs from the current working directory so Codex can explore the codebase

## When to Use

Request a second opinion at any stage:

- **Planning**: "Does this architecture make sense? What am I missing?"
- **Mid-implementation**: "I'm stuck on X. What approaches should I consider?"
- **Bug diagnosis**: "Here's the error and what I've tried. What else should I look at?"
- **Code review**: "Review these changes for bugs, security issues, or improvements"
- **Final review**: "Before we ship this, what concerns might a senior engineer raise?"

## Providing Rich Context

**The more context you provide, the better the second opinion.** Include:

1. **Summary of the situation**: What you've been working on, current state
2. **The specific question**: What decision or issue needs input
3. **Relevant code/diffs**: Via stdin or file paths Codex can read
4. **Constraints**: Performance requirements, compatibility needs, deadlines
5. **What you've already considered**: So Codex doesn't repeat your analysis

The wrapper script automatically tells Codex where to find the full conversation log, so it can read the entire session history if needed for deeper context.

## Best Practices for Prompts

Frame prompts to get honest, analytical feedback:

**Good prompts** (encourage analysis):
- "What issues might exist in this implementation?"
- "What would a senior engineer flag in this code?"
- "What edge cases or failure modes should I consider?"
- "Review this for bugs, security issues, and maintainability"

**Avoid** (leading questions that bias response):
- "Is this code correct?" (invites simple yes)
- "This looks good, right?" (suggests expected answer)
- "I think X is the right approach, agree?" (biases toward agreement)

**Request structured output** for actionable feedback:
- "For each issue: severity, location, problem, suggested fix"
- "List concerns in order of importance"

## Interpreting Results

After receiving Codex's response:

1. **Compare perspectives**: Note where Codex agrees/disagrees with your analysis
2. **Investigate disagreements**: Codex questioning your approach is valuable signal
3. **Synthesize**: Combine insights from both perspectives
4. **Report to user**: Present both views, noting areas of agreement and divergence

Remember: The goal is diverse perspectives, not consensus. Disagreement often surfaces important considerations.
