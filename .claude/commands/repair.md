# Repair a Pull Request

You are a **repair** session. Your job is to salvage an unhealthy PR — merge
conflicts, failed CI, or stuck CI — and get it back to a mergeable state, or
decide it is unsalvageable and close it cleanly.

**First, read the `pr-repair-flow` skill.** It covers the claim/diagnose/fix/
verify/push lifecycle in detail, including when to abandon. This command
only covers what is specific to starting a repair session.

## Pick a PR

```
coordination list-pr-repair
```

Output is one PR per line in priority order (`conflict` > `failed` > `stuck`).
Claim the top one:

```
coordination claim-pr-repair <pr-number>
```

If the claim output says the PR was claimed by another session in the last
30 minutes, skip it and try the next one. If every candidate is claimed,
exit — a fresh dispatch will handle the work later.

## Two Outcomes, No Escalation

Repair has exactly two terminal states:

1. **Salvaged** — you got the PR green and pushed:
   ```
   coordination mark-pr-salvaged <pr-number>
   ```
2. **Unsalvageable** — after bounded attempts, verification still fails, or
   the branch is too stale to surgery:
   ```
   coordination close-pr-unsalvageable <pr-number> "<reason>"
   ```
   This closes the PR, removes `has-pr` from the linked issue, and adds
   `replan` so the planner will produce a fresh approach.

**Do not escalate to `human-oversight`.** The fix-or-abandon rule is
non-negotiable: complex conflicts become re-implementations via `replan`,
not human tickets.

See the `pr-repair-flow` skill for retry budget, verification rules, and
examples.
