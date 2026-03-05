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

## Avoiding the Recovery-of-Recovery Anti-Pattern

A recovery PR can itself develop merge conflicts, creating a cascade:
original PR → recovery issue → recovery PR → conflicts again. This
happened with PRs #565→#568→#577 and #549→#558→#561.

**Root cause**: Multiple agents modify the same large file (e.g.,
ZstdFrame.lean at 1059 lines) concurrently. Each merge to master
invalidates all outstanding PRs touching that file.

**Prevention rules for recovery workers:**

1. **Rebase immediately before pushing**: After cherry-picking or
   resolving conflicts, always `git fetch origin && git rebase
   origin/master` right before `git push`. Even if you just created
   the branch minutes ago, another PR may have merged in the interim.

2. **Check for pending PRs on the same files**: Before starting
   recovery work, check if other open PRs touch the same files:
   ```bash
   # List files in the PR you're recovering
   gh pr view N --json files --jq '.files[].path'
   # Check open PRs for overlapping files
   gh pr list --json number,title,files --jq '.[] | select(.files | map(.path) | any(. == "Zip/Native/ZstdFrame.lean")) | "\(.number) \(.title)"'
   ```
   If another PR modifies the same hot file and is closer to merging,
   let that one land first.

3. **Never chain recoveries**: If your recovery PR develops conflicts,
   do NOT create another recovery issue. Instead, the next worker who
   picks up the original issue should redo the work from scratch on
   current master. Two levels of recovery means the approach is wrong.

4. **Flag hot files for splitting**: If a file over 500 lines causes
   repeated conflicts across multiple PRs, note this in your progress
   entry. Splitting the file should be prioritized over further feature
   work on it.

## Merge Order for Concurrent Conflicting PRs

When multiple PRs conflict with each other (not just with master),
merge order matters:

1. **Independent PRs first**: PRs that only add new files or touch
   non-overlapping code can merge in any order.
2. **Foundation before consumers**: If PR A provides validation that
   PR B's code depends on, merge A first.
3. **Smallest diff first**: When semantically independent, merge the
   PR with fewer changed lines to minimize rebase work for others.

**Example from Track E**: PR #591 (new spec files only) should merge
before PR #561 (validation) before PR #577 (wiring that uses
validation). Each step reduces the rebase burden for the next.

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

## Guidance for Planners

To prevent conflict cascades at the planning stage:

1. **Avoid concurrent issues targeting the same file**: If an open issue
   already modifies `Zip/Native/ZstdFrame.lean`, don't create another
   issue that also modifies it. Use `depends-on:` to serialize them.
2. **Split large files first**: Files over 500 lines that are actively
   being modified by multiple agents should be split before further
   feature work. Create a splitting issue with higher priority.
3. **Check open PRs before planning**: Run `coordination orient` and
   note which files have open PRs. New issues should avoid those files
   unless they depend on the PR landing first.
