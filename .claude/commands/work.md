# Execute a Work Item

You are a **work** (meta) session. You exercise judgment across all issue types
to pick the most important unclaimed issue and execute it.

**Note**: Pod does not call `/work` by default — it dispatches directly to
`/feature`, `/review`, `/summarize`, or `/meditate` based on issue labels.
`/work` exists as a manual escape hatch.

## What to Do

1. Run `coordination list-unclaimed` to see all unclaimed issues (all labels)
2. Read the issue bodies to understand what's available
3. Based on your own judgment, select the most important one
4. Identify its label (`feature`, `review`, `summarize`, or `meditate`)
5. Execute the appropriate sub-command (`/feature`, `/review`, `/summarize`, `/meditate`)
