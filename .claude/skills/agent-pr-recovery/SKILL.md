---
name: agent-pr-recovery
description: Use when fixing merge conflicts on agent PRs, rebasing stale branches, or deciding whether to salvage vs. redo a PR. Also use when a rebase/fix-PR plan issue is claimed.
allowed-tools: Read, Bash, Grep, Glob
---

# Agent PR Recovery

Assumes `agent-worker-flow` (claim/branch/verify/publish lifecycle). This skill
adds only the patterns specific to *recovering* conflicted, stale, or
superseded PRs.

## Salvage vs. Redo vs. Close

- **Salvage** (cherry-pick onto fresh master) when: 1-2 focused content commits,
  still valid against master, conflict is mechanical.
- **Redo from scratch** when: many accumulated commits, target file heavily
  changed on master since the PR, or the work overlaps already-merged changes.
- **Close** when another PR already accomplished the goal, or the approach was
  wrong and the issue needs replanning:
  ```bash
  coordination close-pr N "Superseded by PR #M which already cleaned this file"
  ```

## Spec Files: Skip Straight to Manual Insertion

**Cherry-pick and rebase always fail on `Zip/Spec/Zstd.lean` and
`Zip/Spec/ZstdFrame.lean`.** Multiple agents append additive theorems to the
same section markers, producing 6-12 conflict hunks every time. The cherry-pick
attempt wastes time and never succeeds — go directly to manual insertion.

```bash
# 1. Extract the theorem text to preserve
gh pr diff N

# 2. Fresh branch from master
git checkout -b agent/<session-id> origin/master

# 3. Manually insert theorems at the END of the correct section, before the
#    next /-! ## ... -/ section header. The theorems are ALWAYS additive (new
#    defs/theorems, no edits to existing ones), so resolution is always
#    "keep master + insert new theorems in the right section."

# 4. Verify the affected module only
lake build Zip.Spec.Zstd      # or Zip.Spec.ZstdFrame
```

## Cherry-Pick (non-spec files)

For non-spec files, cherry-pick the content commit(s) onto fresh master rather
than rebasing the old branch — feature branches accumulate CI retries and
fixups; cherry-picking only the meaningful commits yields a cleaner PR.

```bash
gh api repos/OWNER/REPO/pulls/N/commits \
  --jq '.[].sha[:8] + " " + (.[].commit.message | split("\n")[0])'   # find content commit(s)
git checkout -b agent/<session-id> master
git cherry-pick <commit-sha>
git diff --name-only --diff-filter=U    # conflicted files, if any
lake build ModuleName
```

## Verify Conflict Scope Before Rebasing a Fix-PR

"Fix PR #N" issue bodies routinely undercount conflicting files (master may
have merged a sibling branch since the issue was written). Treat the live state
as source of truth, not the issue:

```bash
gh pr view N --json mergeable,mergeStateStatus,files \
  --jq '{mergeable, mergeStateStatus, files: [.files[].path]}'

git fetch origin
git checkout pr-N
git rebase origin/master            # let it report conflicts
git diff --name-only --diff-filter=U   # authoritative conflict list
git rebase --abort                  # clean up before committing elsewhere
```

The `--diff-filter=U` list is authoritative.

## Re-verify Stale Issue Details

Issue bodies snapshot metrics and source pointers at creation time; both drift.
Re-check against current master before working — none of these warrant a `skip`
on their own; just fix in your commit and note it in the progress entry.

- **Bare-simp counts.** Use the word-boundary pattern, not `grep -c 'simp[^_]'`
  (which inflates counts 10-100x by matching `simp only`/`simpa`):
  ```bash
  grep -n 'simp\b' Zip/Spec/File.lean | \
    grep -v 'simp only\|simp_all\|simp?\|simp_wf\|dsimp\|simp_rfl\|simp (config'
  ```
  If the real count is 0 or far from the issue's claim, `coordination skip`.
- **Line numbers** in referenced files drift — grep the symbol
  (`readEntryData`, `extractTarGzNative`) instead of trusting line numbers.
- **Function signatures** quoted in issues are often paraphrased — confirm with
  `rg "def <name>" Zip/`.
- **Test file / fixture paths** — `ls ZipTest/*.lean`; the file is often
  `ZipFixtures.lean`, not the `Fixtures.lean` the issue names.
- **Error substrings** — probe the test with a sentinel like `<<PROBE>>` to
  surface the real message rather than trusting the quoted one.

## Detecting Superseded PRs

Signs a PR's work was already done by another:
- `git diff master...pr-N -- path` is empty or trivial.
- The target file's metrics are already at/below the PR's target.
- A recently merged PR's commit message mentions the same file.

## Preventing Conflict Cascades

When several agents touch the same large file, a recovery PR can itself develop
conflicts — original PR → recovery → recovery again.

1. **Rebase immediately before pushing**: `git fetch origin && git rebase
   origin/master` right before `git push`, even if the branch is minutes old.
2. **Check for pending PRs on the same files** before starting; if another PR
   touches the same hot file and is closer to merging, let it land first:
   ```bash
   gh pr list --json number,title,files \
     --jq '.[] | select(.files | map(.path) | any(. == "Zip/Native/ZstdFrame.lean")) | "\(.number) \(.title)"'
   ```
3. **Never chain recoveries**: if your recovery PR conflicts, do NOT open a
   second recovery issue — the next worker redoes the work from scratch on
   current master. Two levels of recovery means the approach is wrong.
4. **Flag hot files for splitting** in your progress entry when a file >500
   lines causes repeated conflicts.

### File splits are the worst cascade source

A PR that splits/renames a large file invalidates every in-flight PR touching
it. Before merging such a PR, list affected open PRs and pick a strategy:

```bash
gh pr list --state open --json number,title,files \
  --jq '.[] | select(.files | map(.path) | any(test("OriginalFile"))) | "\(.number) \(.title)"'
```

- **Split first, rebase in-flight PRs immediately** (one coordinated session) —
  preferred when the split unblocks many future PRs.
- **Wait for in-flight PRs to land, then split** — preferred when only 1-2 PRs
  are in flight and near merge.
- **Planners**: never create concurrent issues targeting a file with a pending
  split; chain them with `depends-on:`.

## Hot File Tracking

Files that cause repeated merge conflicts. Update this table when a file
crosses the threshold.

| File | Size | Status |
|------|------|--------|
| `Zip/Spec/Zstd.lean` | ~6280 lines | **Critical** — every block/frame two-block completeness theorem appends here; 19 sections by block-type pair. Split urgently needed. |
| `Zip/Spec/ZstdFrame.lean` | ~2600 lines | **Critical** — every API-level `decompressZstd` two-block theorem lands here, conflicting with parallel Track E agents. |

Mitigation for hot files: serialize with `depends-on:`, keep additions
append-only at end of file, minimize branch lifetime (claim/implement/push/PR
in one session), and propose a split when a file >800 lines hits 3+ conflicts
in a batch and has natural section boundaries.

## Merge Order for Mutually-Conflicting PRs

When PRs conflict with each other (not just master): independent/new-file PRs
in any order; foundation (validation a PR depends on) before consumers;
smallest diff first among semantically independent PRs to minimize others'
rebase work.

## Progress Entry as a Ride-Along PR

A small rebase-fix PR that also wants its own `progress/` entry should be a
*split PR*: (a) the rebase PR (feature commits + conflict resolution) lands
first, then (b) a one-file `doc: progress entry for #N rebase fix` PR. Empirically
the split path wins; committing the progress entry before pushing the rebase
only beats auto-merge in a ~30-second window (rebase commit already staged, push
within seconds), so plan for the split. Budget one ride-along PR per non-trivial
rebase fix. Do **not** amend an auto-merged commit after the fact —
`--force-with-lease` is pointless once the branch is deleted upstream.

## Fresh-worktree build: `lake build -R`

If a worktree has been idle across a toolchain pin change, the first build can
fail with `compiled configuration is invalid`. This is a *configuration*
rebuild, distinct from the `.lake/` stale-link-flags issue in the project
CLAUDE.md. Fix:

    nix-shell --run "lake build -R"
