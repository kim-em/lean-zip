# Track E: tar-longnames-skipped.tar fixture (typeflag 'N', 0x4E)

- Date: 2026-05-02 (UTC 19:54)
- Session: f3285fd3-e257-4c8f-9e99-1f766ca40b86
- Type: feature
- Issue: #2438
- Branch: agent/f3285fd3

## What landed

Added `tar-longnames-skipped.tar` (512 bytes, single-block UStar header,
zero-byte payload) pinning `Tar.extract`'s silent-skip `else` fallback
for unsupported GNU typeflag `'N'` (LF_NAMES old-long-name extension,
`0x4E`). Fifth GNU-typeflag sibling alongside `'V'` / `'M'` / `'S'` /
`'D'`; the silent-skip family now stands at ten fixtures spanning the
closed POSIX UStar `'1'`/`'3'`/`'4'`/`'6'`/`'7'` range and the open
GNU-typeflag `'V'`/`'M'`/`'S'`/`'D'`/`'N'` sub-ladder.

Files touched:

- `scripts/build-symlink-hardlink-malformed-fixtures.lean` — added a new
  `buildZeroSizeFixture "longnames-entry" "" 0x4E ...` call, extended the
  module docstring with the `'N'` rationale, and bumped the tail
  `IO.println` count from 10 → 11.
- `testdata/tar/security/tar-longnames-skipped.tar` — regenerated
  byte-deterministically from the script (SHA-256
  `452e2b6b711b98f05370ab5ee25fb75c51c5f258ade275c804c96a1d83a0b8d0`,
  reproduced across two clean rebuilds).
- `ZipTest/TarFixtures.lean` — new test arm extracting into
  `/tmp/lean-zip-fixture-tar-longnames-skipped-extract` and asserting
  the extract dir is observably empty, plus a `Tar.list` check that the
  entry is preserved with `typeflag = 0x4E` (matching the precedent set
  by the `'V'`/`'M'`/`'S'`/`'D'` test arms). Cleanup loops at the end of
  the file extended with the new fixture name and extract directory.
- `SECURITY_INVENTORY.md` — added a new sub-bullet under the silent-skip
  family closing list and a new row under *Minimized Reproducer
  Corpus*. The corpus row uses `#TBD-VERIFY-PR` as the closing-PR
  placeholder; will be substituted with the real PR number in a
  follow-up commit on the same branch immediately after PR creation
  (matches the pattern used by the four sibling GNU-typeflag rows).

## Verification

- `lake env lean --run scripts/build-symlink-hardlink-malformed-fixtures.lean`
  prints "Built 11 per-typeflag-policy security fixtures" and reproduces
  the same SHA-256 across two consecutive runs.
- `lake build` passes (only the pre-existing `Zip.Spec.Deflate`
  unused-simp-arg linter warning, unrelated to this PR).
- `lake exe test` reports `All tests passed!`; the new
  `tar-longnames-skipped.tar` arm extracts to an empty directory and
  the `Tar.list` typeflag assertion fires correctly.
- `bash scripts/check-inventory-links.sh` reports `errors=0` and
  `warnings=10` (baseline `warnings=8` + 2 new placeholder warnings on
  the new row's `#TBD-VERIFY-PR`; both will resolve once the closing
  PR number is substituted).
- Sorry count unchanged at 0 across all `Zip/` modules.

## Patterns / decisions

- Reused the `buildZeroSizeFixture` helper verbatim — no new
  fixture-builder code was needed. The fifth GNU-typeflag fixture is
  a one-line script extension (plus comment) by design; the helper has
  pinned the family geometry across all ten siblings.
- No new typeflag constant in the `Tar` namespace. `'N'` is the
  deprecated precursor to `'L'`/`'K'` and is *not* aliased to `'L'` in
  `forEntries`'s inner dispatch — adding a constant would imply
  recognition. The silent-skip policy keeps the surface minimal.
- The `Tar.list` typeflag preservation assertion mirrors the
  `vhListed`/`mvListed`/`spListed`/`inListed` convention from the
  other GNU siblings — callers routing on `entry.typeflag` for trust
  decisions still observe the LF_NAMES marker even though `extract`
  silent-skips.
- Issue #2438 explicitly noted that PR #2437 (`'D'`) was in flight at
  issue-creation time. PR #2437 has since landed (master at 67481e1),
  so the prose in this PR cites all four GNU-typeflag siblings as
  landed (no in-flight footnote needed).

## Follow-ups

- Solaris/Sun typeflags (`'A'` ACL, `'X'` Sun extended, `'I'` Sun
  inode metadata) remain a candidate vendor sub-ladder per the issue's
  *Out of scope*; can be filed as follow-ups if the family continues to
  expand.
- The paired-review issue for this PR (post-#2438 sibling cadence) is
  expected to file as the next planner cycle picks it up — sibling of
  the per-typeflag paired-review pattern (PRs #2419 / #2421 / #2427 /
  #2433 / #2435 / #2436 / etc.).
