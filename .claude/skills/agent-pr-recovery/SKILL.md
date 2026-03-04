---
name: agent-pr-recovery
description: Use when fixing merge conflicts on agent PRs, rebasing stale branches, or deciding whether to salvage vs. redo a PR. Also use when a rebase/fix-PR plan issue is claimed.
allowed-tools: Read, Bash, Grep, Glob
---

# Agent PR Recovery

Patterns for recovering agent PRs that have merge conflicts, failing CI,
or stale branches — common in high-cadence multi-agent workflows.

## Diagnosing a Conflicted PR

Before attempting a fix, understand what happened:

```bash
# What commits does this PR contain?
gh api repos/OWNER/REPO/pulls/N/commits --jq '.[].sha[:8] + " " + (.[].commit.message | split("\n")[0])'

# What files are in conflict?
git fetch origin pull/N/head:pr-N
git merge-base master pr-N | xargs git diff --name-only master...pr-N

# Was the PR's work already done by another PR?
# Check if the target files are clean on master
grep -n 'simp\b' Zip/Spec/TargetFile.lean | grep -v 'simp only\|simp_all\|simp?'
```

## Decision: Salvage vs. Redo

**Salvage** (cherry-pick rebase) when:
- The PR has 1-2 content commits with clear, focused changes
- The changes are still valid against current master
- The conflict is mechanical (import changes, nearby line edits)

**Redo from scratch** when:
- The PR has accumulated many commits (5+) from a long-running session
- The target file has been substantially changed on master since the PR
- The PR's changes overlap with already-merged work (e.g., bare simps
  already cleaned by a different PR)

**Close without replacement** when:
- Another PR already accomplished the same goal
- The PR's approach was wrong and the issue needs replanning

```bash
# Close a superseded PR
coordination close-pr N "Superseded by PR #M which already cleaned this file"
```

## Cherry-Pick Rebase Pattern

The most reliable recovery pattern for PRs with merge conflicts:

```bash
# 1. Identify the content commit(s) — skip merge commits, CI fixes, etc.
gh api repos/OWNER/REPO/pulls/N/commits \
  --jq '.[].sha[:8] + " " + (.[].commit.message | split("\n")[0])'

# 2. Create a fresh branch from current master
git checkout -b agent/<session-id> master

# 3. Cherry-pick only the content commit(s)
git cherry-pick <commit-sha>

# 4. If cherry-pick has conflicts, resolve them
#    Key: understand what master changed (see global CLAUDE.md merge conflict rules)
git diff --name-only --diff-filter=U  # list conflicted files

# 5. Build and verify
lake build ModuleName

# 6. Push and create new PR, closing the old issue
git push -u origin agent/<session-id>
coordination create-pr <issue-number>
```

**Why cherry-pick instead of rebase?** Feature branches often accumulate
unrelated commits (CI retries, fixups, intermediate states). Cherry-picking
only the meaningful commits produces a cleaner PR. Rebasing preserves all
commits, including noise.

## Detecting Stale/Superseded PRs

When multiple agents work on related files, PRs can become redundant:

```bash
# Check if target file is already clean on master
# (e.g., for a bare simp review PR)
git show master:Zip/Spec/TargetFile.lean | grep -c 'simp\b' | ...

# Compare PR's changes against current master
git diff master...pr-N -- Zip/Spec/TargetFile.lean
```

Signs a PR is superseded:
- The diff against master is empty or trivial
- The target file's metrics are already at/below the PR's target
- Another merged PR's commit message mentions the same file

## Stale Issue Counts

Issue descriptions contain metrics at time of creation (e.g., "61 bare
simps in InflateCorrect.lean"). These go stale quickly when:
- Other PRs clean the same file
- The planner's grep was inaccurate (counted `simp only` as bare simp)

**Always verify before starting work:**
```bash
# Accurate bare simp count
grep -n 'simp\b' Zip/Spec/File.lean | \
  grep -v 'simp only\|simp_all\|simp?\|simp_wf\|dsimp\|simp_rfl\|simp (config'
```

If the actual count is 0 or very different from the issue, use
`coordination skip` with an explanation.

## Manifest File Conflicts (Zip.lean)

`Zip.lean` is a root import manifest — every new module adds a line.
When two PRs both create new files (e.g., two spec files), they both
modify `Zip.lean` and conflict, even though their actual content files
don't overlap at all.

**These conflicts are trivial to resolve** — just add the missing import
line in alphabetical order. They do NOT need a recovery issue. Workers
should simply rebase before pushing:

```bash
git fetch origin && git rebase origin/master
# The conflict in Zip.lean is always "add this import line"
# Accept both sides and ensure alphabetical order
```

**Planners**: Do NOT create recovery issues for Zip.lean-only conflicts.
Note this in the plan if the work creates a new file that will be
imported from `Zip.lean`.

## Large Shared File Conflicts

Files over 500 lines that are actively modified by multiple agents are
the primary source of non-trivial merge conflicts. The canonical example
is `ZstdFrame.lean` (1059 lines), where multiple PRs targeting different
features all touch the same file.

**The conflict cascade pattern**:
1. PR #A modifies large file → develops conflicts as other PRs merge
2. Recovery issue created → PR #B cherry-picks from #A
3. PR #B develops conflicts too (more PRs merged during recovery)
4. Another recovery issue... (the cascade)

**Prevention** (for planners):
- **Split large files first**: Before scheduling concurrent work on a
  >500-line file, create a splitting issue. Review #583 identified
  natural extraction boundaries for ZstdFrame.lean — splitting reduces
  the conflict surface by giving each feature its own file.
- **Serialize modifications**: Don't schedule 3 agents to modify the
  same file concurrently. One agent at a time on a hot file.
- **Prioritize the bottleneck**: If one critical PR (#552) blocks
  others, schedule it first and defer competing modifications.

**Prevention** (for workers):
- **Rebase immediately before pushing**: Even if you just created the
  branch minutes ago. `git fetch origin && git rebase origin/master`
- **Don't create recovery issues for your own recovery PRs**: If your
  recovery PR develops conflicts, rebase your branch — don't ask for
  another recovery issue. The cascade stops with you.

## Rapid Merge Cadence Mitigation

When 8+ PRs merge in a single day, feature branches fall behind quickly.
Patterns that help:

1. **Short-lived branches**: Claim, implement, PR, done. Don't accumulate
   changes over multiple build cycles on a single branch.
2. **Targeted builds**: Build only the affected module (`lake build Module`)
   rather than full project. Submit and let CI do the full build.
3. **Rebase before push**: Always `git fetch origin && git rebase origin/master`
   before pushing, even if you just created the branch minutes ago.
4. **Don't fix conflicts on old PRs**: If a PR has conflicts, cherry-pick
   the content to a new branch rather than trying to rebase the old one.
5. **Check for pending PRs on same files**: Before starting work, check
   if other open PRs modify the same files. If so, consider waiting for
   them to merge first, or coordinate to avoid overlapping changes.
   ```bash
   # List open PRs touching a specific file
   gh pr list --state open --json number,title,files \
     --jq '.[] | select(.files[]?.path == "Zip/Native/ZstdFrame.lean") | "\(.number) \(.title)"'
   ```
