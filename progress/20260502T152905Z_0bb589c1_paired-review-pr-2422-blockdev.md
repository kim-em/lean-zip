# Session 20260502T152905Z (UUID prefix 0bb589c1, /review)

## Issue

[#2423](https://github.com/kim-em/lean-zip/issues/2423) — Review:
paired-review entry for PR #2422 (`tar-blockdev-skipped.tar` —
per-typeflag silent-skip family extension 3 → 4; sibling paired-review
of #2414 / PR #2419 and #2418 / PR #2421).

## Summary

Filed the missing 4-of-N paired-review entry for PR #2422 in
`SECURITY_INVENTORY.md` immediately after the PR #2417 paired-review
entry and before the *Symlink/hardlink extraction policy* fixture
enumeration block. Entry mirrors the chardev (PR #2417) paired-review
shape with the seven required sub-sections: Family-extension claim
fidelity (3 → 4 fixtures), Fixture-builder rename-vs-extend choice,
Reproducer Corpus row prose fidelity, Adversarial check,
Sibling-fixture audit independence, Stable-cite discipline, and
Follow-up gaps. Test-arm placement is folded into the
sibling-independence sub-section per the chardev precedent rather
than a separate top-level bullet.

## SECURITY_INVENTORY.md edits

Added one block of ~210 lines starting after the existing PR #2417
paired-review (which ends at the *No new follow-up issue is filed by
this paired-review.* sentence, just before the
`#### Symlink/hardlink extraction policy` heading). The entry header
follows the precedent format:

> *"- Paired review of PR #2422 (`tar-blockdev-skipped.tar` fixture —
>   per-typeflag silent-skip family extension 3 → 4; this paired-review
>   landed in PR #TBD-VERIFY-PR closing #2423):"*

The `#TBD-VERIFY-PR` placeholder will be substituted to the actual PR
number on the worker branch immediately after `gh pr create`, per the
PR #2364 / PR #2413 / PR #2417 / PR #2422 substitution pattern.

## Verification facts collected

- PR #2422 squash commit: `5f87adf42fe80ad82e884bf6ccdda41447c5190c`
  (short prefix `5f87adf42f`).
- Merged 2026-05-02T14:00:54Z, closes #2416. (Distinct from PR #2417
  which merged 2026-05-02T13:03:33Z — different merge commits and
  different closing-issue numbers.)
- Files touched by PR #2422: `SECURITY_INVENTORY.md` (+10),
  `ZipTest/TarFixtures.lean` (+25/-2),
  `scripts/build-symlink-hardlink-malformed-fixtures.lean` (+16/-2),
  `testdata/tar/security/tar-blockdev-skipped.tar` (new, 512 B,
  binary), and the worker progress entry
  `progress/20260502T135640Z_dc152c31_tar-blockdev-skipped-fixture.md`.
- Fixture SHA-256:
  `9ef6dda29da2529019a62aa905b819f7018a0560cd1d1cf946b3f73714d9bae2`.
- Adversarial check from worker progress: wrapping the `else` body in
  `if e.typeflag == typeHardlink || e.typeflag == 0x36 ||
  e.typeflag == 0x33 then skipEntryData ... else throw ...`; new arm
  fires with `unexpected typeflag 52` (decimal 52 = `0x34` = ASCII
  `'4'`); the three sibling arms continue to pass.
- `git blame` confirms PR #2422's row at the inventory cites `#2422`
  in the closing-PR column (substitution done correctly on the worker
  branch — the PR #2417 self-correction holds across PR #2422).

## Family-ladder snapshot at PR #2422's merge

| Step | Typeflag | Glyph | Fixture                          | Closing PR |
|------|----------|-------|----------------------------------|------------|
| 1/N  | `0x31`   | `'1'` | `hardlink-outside.tar`           | PR #1555   |
| 2/N  | `0x36`   | `'6'` | `tar-fifo-skipped.tar`           | PR #2413   |
| 3/N  | `0x33`   | `'3'` | `tar-chardev-skipped.tar`        | PR #2417   |
| 4/N  | `0x34`   | `'4'` | `tar-blockdev-skipped.tar`       | PR #2422   |

In-flight at PR #2422's merge: typeflag `'7'` contiguous file at
[issue #2420](https://github.com/kim-em/lean-zip/issues/2420). The
GNU typeflags `'L'` long-name, `'K'` long-link, `'V'` volume header,
`'M'` multi-volume continuation, `'x'` PAX extended, and `'g'` PAX
global remain distinct candidates beyond the POSIX UStar `'0'`–`'7'`
numeric range. (Subsequent landing of PR #2425 — typeflag `'7'` —
between PR #2422's merge and this paired-review filing has closed
the POSIX UStar `'0'`–`'7'` range; planner queue now contains
`'V'` (#2424) and `'M'` (#2426) GNU-typeflag fixtures.)

## Warning-count delta

- Pre-PR-#2422 baseline (post-PR-#2417): `errors=0, warnings=2`
  (the fifo + chardev rows' *"during this PR"* prose).
- Post-PR-#2422 (added blockdev row's same prose): `errors=0,
  warnings=3` — the +1 warning is the new
  `tar-blockdev-skipped.tar` row's adversarial-check phrasing,
  inherited from the chardev row template.
- This paired-review (with `#TBD-VERIFY-PR` still in the header):
  `errors=0, warnings=4` (+1 transient placeholder warning that
  resolves on PR-number substitution).
- After substitution `#TBD-VERIFY-PR` → `#NNNN`: `errors=0,
  warnings=3` for the post-PR-#2422 / pre-PR-#2425 tree (which
  matches the warning-count claim in the *Stable-cite discipline*
  sub-section).
- Currently on master (post-PR-#2425): `warnings=4` (4 row-prose
  mentions, no placeholders).

The paired-review entry's *Stable-cite discipline* sub-section
references the post-PR-#2422 / pre-PR-#2425 count of 3 (matching the
PR #2422 merge snapshot), continuing the deferral of
`<!-- drift-detector: -->` opt-outs across the silent-skip family
rows pioneered in the PR #2413 / PR #2417 paired-reviews.

## Verification

- `lake build` clean (201 jobs).
- `lake exe test` — `All tests passed!`. The
  `TAR fixture tests: OK` line confirms the blockdev arm continues
  to pass (no source change).
- `bash scripts/check-inventory-links.sh` reports `errors=0,
  warnings=5` on the worker branch with `#TBD-VERIFY-PR` still
  present; substitution post-PR-creation will return it to
  `warnings=4` (matching the pre-this-paired-review master state).
- Sorry count unchanged at 0.

## Files changed

- `SECURITY_INVENTORY.md` — +210 / -0 lines (new paired-review
  entry block).
- `progress/20260502T152905Z_0bb589c1_paired-review-pr-2422-blockdev.md`
  — this session log.

## Patterns / decisions

- **Test-arm placement folded into Sibling-fixture audit
  independence.** The issue's deliverable list calls out a separate
  *Test-arm placement* sub-section, but the PR #2417 / PR #2413
  paired-review precedents fold that observation into the
  *Sibling-fixture audit independence* sub-section (the four extract
  directories, the cleanup-loop list, the `writeFixtureTmp` list).
  Followed the precedent rather than introducing a new top-level
  bullet, keeping the paired-review entry shape stable across the
  silent-skip family. The test-arm placement claim is still
  load-bearing — explicit prose covers the alphabetical slot
  positioning.
- **Adversarial-check N+1 convention.** The PR #2417 paired-review
  named the *"spare all-but-the-new-arm"* convention; PR #2422's
  wrapper is the natural N=3 spared-arm extension. The
  paired-review records that the PR #2422 wrapper continues the
  convention and notes the expected next-cadence wrapper for
  typeflag `'7'` (issue #2420) would spare four arms — a written
  prediction that became reality when PR #2425 subsequently landed.
- **In-flight phrasing for typeflag `'7'`.** Honored the issue's
  requested *"name (issue #2420) without committing to a specific
  closing-PR number"* close-out style. The paired-review entry
  itself is framed as the snapshot at PR #2422's merge time, so
  citing `'7'` as the next candidate (queued at issue #2420) is
  correct for that snapshot. The in-progress entry above adds the
  observation that PR #2425 has subsequently landed, but the
  inventory entry stays in PR #2422-snapshot framing per the
  precedent style.

## Hand-off

After PR creation:
1. Substitute the `#TBD-VERIFY-PR` placeholder in
   `SECURITY_INVENTORY.md` with the actual PR number.
2. Issue #2420 (`tar-contiguous-skipped.tar` for typeflag `'7'`)
   has subsequently closed via PR #2425 — its paired-review will
   be queued by a future planner cycle on the established cadence
   (per the PR #2419 → PR #2421 → PR #TBD lineage).
3. Open GNU-typeflag fixtures in the queue: #2424
   (`tar-volumeheader-skipped.tar`, `'V'`) and #2426
   (`tar-multivol-skipped.tar`, `'M'`).
