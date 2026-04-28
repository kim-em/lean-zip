# Session 20260428T122256Z (293ae374) — feature

**Issue:** #2359 — *Close-out wave: close 15+ obsolete inventory-anchor-refresh
PRs and backing issues superseded by #2345 (post-#2353 cleanup;
planner-led, not /repair).*

## What was accomplished

Executed the planner-led close-out wave for anchor-refresh PRs and
their backing issues, retiring the maintenance class superseded by
#2345 / PR #2353.

### PRs closed (15)

All 15 PRs whose titles match `Inventory: re-anchor` were closed
with the documented superseded-by comment (full text in the issue
body). Per-PR diff verification confirmed every one of them touched
only `SECURITY_INVENTORY.md` (line-number-only edits) plus a single
`progress/*.md` session log — no source, no tests, no spec changes.
Remote branches deleted.

| PR | Title (truncated) |
| --- | --- |
| #1959 | Inventory: re-anchor stale Zip/Tar.lean line citations on three pre-existing UStar interior-NUL rows |
| #2006 | Inventory: re-anchor stale Zip/Tar.lean:639 → :756 anchor across rows 1351 / 1355 / 1356 |
| #2013 | Inventory: re-anchor stale Zip/Tar.lean:230 → :259 anchor across rows 1393 + 1398 |
| #2035 | Inventory: re-anchor Tar.extract + Tar.extractTarGz cluster (rows 1192-1195) |
| #2060 | Inventory: re-anchor Local guard inventory row 1311 (Tar.extract regular-file payload loop) |
| #2073 | Inventory: re-anchor Local guard inventory row 1304 (readExact h cdSize central directory row) |
| #2081 | Inventory: re-anchor Local guard inventory row 1307 (readBoundedSpanFromHandle, terminal row) |
| #2083 | Inventory: re-anchor Minimized Reproducer Corpus row 1429 (cd-entry-internal-attrs-reserved.zip) |
| #2092 | Inventory: re-anchor Minimized Reproducer Corpus row 1447 (eocd-numentries-mismatch.zip) |
| #2144 | Inventory: re-anchor SECURITY_INVENTORY.md row 1412 (testdata/tar/malformed/ustar-name-nul-in-name.tar) |
| #2204 | Inventory: re-anchor Decompression Limit Inventory row 1181 (RawDeflate.decompressStream FFI) |
| #2208 | Inventory: re-anchor Decompression Limit Inventory row 1178 (RawDeflate.decompress FFI bomb-limit cite) |
| #2257 | Inventory: re-anchor Decompression Limit Inventory rows 1227-1229 (Archive.extract three-row cluster) |
| #2260 | Inventory: re-anchor Reproducer Corpus row 1462 (bad-method.zip) primary+parenthetical dual-anchor |
| #2267 | Inventory: re-anchor Minimized Reproducer Corpus EOCD-scan rows 1497 + 1501 (no-eocd.zip + too-short.zip) |

### Issues closed (15)

The corresponding `agent-plan + has-pr` backing issues were closed
with the documented superseded-by comment.

| Issue | PR |
| --- | --- |
| #1955 | #1959 |
| #1995 | #2006 |
| #2004 | #2013 |
| #2027 | #2035 |
| #2055 | #2060 |
| #2065 | #2073 |
| #2067 | #2081 |
| #2077 | #2083 |
| #2085 | #2092 |
| #2135 | #2144 |
| #2196 | #2204 |
| #2202 | #2208 |
| #2247 | #2257 |
| #2250 | #2260 |
| #2253 | #2267 |

### Excluded PRs

None. Every candidate PR's diff was confirmed to be anchor-only
(line-number / range edits in `SECURITY_INVENTORY.md` plus a single
`progress/*.md` session log). No PRs were excluded for non-anchor
content; no follow-up issues need filing.

### Sanity check — `coordination list-pr-repair`

`coordination list-pr-repair | grep -iE 'Inventory: re-anchor'`
returns nothing post-close-out (verified). The repair queue still
reports merge-conflict / failed entries for non-anchor PRs (Track E
fixture + paired-review entries from the #1700s/#1800s run, the two
in-flight Track D Phase 0a/0b human-oversight PRs, and one Summarize
PR), but all of those are out of scope for this wave and remain on
the repair queue for normal `/repair` triage.

The `gh issue list --label agent-plan --state open --jq '...test("Inventory: re-anchor")'`
sanity query also returns 0 — every backing issue is closed.

### `PROGRESS.md` retirement bullet

Appended a single bullet under *Current State* (not under
*Milestones*) recording the maintenance-class retirement, citing the
parent decision (#2345) and the close-out PR. The bullet placeholder
`#TBD-CLOSEOUT-PR` will be replaced by the PR number in a follow-up
commit on the same branch immediately after PR creation.

## Decisions / patterns

- **Two `gh` calls per PR vs. one composite `gh pr close --comment ... --delete-branch`**:
  used the composite form. Both the closing comment and remote-branch
  delete went through cleanly for all 15 PRs in a single shell loop;
  the only stderr note was `"Skipped deleting the local branch since
  current directory is not a git repository"` (gh CLI sees the
  worktree as not-quite-a-git-repo for the local-branch delete path),
  which is fine because the local branches are on the agent worktrees,
  not on this branch.
- **Verification ordering**: verified diff-shape for *all* 15 PRs
  before closing any one of them. This caught the discriminator —
  `SECURITY_INVENTORY.md` ± `progress/*.md` and nothing else — early
  enough that no surprise-content PR could slip in.

## What remains

- After PR creation, replace `#TBD-CLOSEOUT-PR` in `PROGRESS.md`
  with the actual PR number via a follow-up commit on this branch
  (single one-line edit, no rebuild needed; `PROGRESS.md` is
  documentation only).
- The semantic audit of `SECURITY_INVENTORY.md` (#2358) and its
  follow-ups (#2360, #2361, #2362) remain open; this wave is
  strictly the GitHub-housekeeping retirement of the anchor-refresh
  *maintenance* class, not the underlying audit.

## Quality metrics

- `sorry` count unchanged (no source files touched).
- `lake -R build` and `lake exe test`: unaffected (no source / test
  changes; sanity build run before publishing).
- Closed: 15 PRs + 15 issues (planner-led close-out, no `/repair`
  invocations consumed).
