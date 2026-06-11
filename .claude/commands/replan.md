# Triage `replan` Issues

You are a **replan** session. Your job is to triage issues labelled
`replan` — those left behind by PRs closed unsalvageable
(`coordination close-pr-unsalvageable`), worker skips
(`coordination skip --replan`), or partial-completion publishes
(`coordination create-pr --partial`). You do NOT execute any code
changes and you do NOT create fresh planning work. That is `/plan`'s job.

Replan sits between `repair` and `plan` in dispatch priority and shares
the planner lock with `/plan`. The lock is managed by `pod` — do NOT
call `coordination lock-planner` or `coordination unlock-planner`
yourself.

## Step 1: Orient

1. `git fetch origin master`
2. Read the last 5 files in `progress/` (sorted by filename) to
   understand recent work.

## Step 2: Pick up replan candidates

```
coordination list-replan
```

Output is one issue per line: `#<number> <title>`. The list goes
through the same trusted-author gate as `list-unclaimed`. Issues with
`claimed`, `blocked`, or `has-pr` are filtered out. `directive` issues
never appear here: the skip / partial-PR / unsalvageable-close paths
deliberately do not apply the `replan` label to a directive (that
label would strand it — invisible to both this list and
`list-unclaimed`). A stalled directive instead stays claimable via
`list-unclaimed` so a fresh worker picks it up again; its satisfaction
is judgment-laden and is decided by the worker who completes the
deliverables, not by replan triage.

If the list is empty, exit cleanly — pod will release the planner lock.

## Step 3: Triage each candidate

For each issue, read the body and any closing comment (from a closed
PR) to understand why it was abandoned, then apply **exactly one** of
the following:

- **Work already done** (a subsequent PR merged it):
  close with a forward link.
- **Plan stale / approach changed**: create a corrected replacement
  issue via `coordination plan`, close the original linking forward.
- **Partial progress**: create an issue for the remaining deliverables,
  close the original linking forward.
- **Worker-decomposed**: the worker created sub-issues before releasing
  the claim. Detect via a comment that starts with `Decomposed into #`
  and lists the sub-issue numbers. Read the sub-issues and decide:
  - sub-issues fully cover the parent → close the parent with a
    forward link (do **not** re-create the sub-issues);
  - residual scope remains → narrow the body to that residual and
    remove the `replan` label so workers can claim it again.
  In the partial-PR variant the parent will also have a merged or open
  PR reference; treat it the same way and rely on the merged PR to
  record the partial work.
- **Still valid, body still accurate**: remove the `replan` label
  (`gh issue edit N --remove-label replan`) to re-open for workers.
- **Still valid, body stale**: update the issue body with current
  state, then remove the `replan` label.

Process **every** candidate from `list-replan` before exiting.

## Step 4: Exit

This session produces no PR — it edits issues directly. After every
candidate has been disposed of, exit. The harness will release the
planner lock.

Do **not** create new `agent-plan` issues beyond residual sub-issues
required to record narrowed scope. Fresh planning is the next
planner's job, not yours.
