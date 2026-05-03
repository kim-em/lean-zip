# Review #2446 — paired-review entry for PR #2439 (`tar-longnames-skipped.tar`)

## Date
2026-05-03 (UTC)

## Type
Review (paired-review)

## Summary
Filed the per-PR paired-review entry for PR #2439 in
`SECURITY_INVENTORY.md`, immediately after the PR #2437 paired-review.
This is the **fifth and final** GNU-typeflag-arm paired-review for the
`Tar.extract` silent-skip `else` fallback family — extending the count
from 9 → 10 fixtures, **closing the GNU-typeflag sub-ladder** at five
arms (`'V'` / `'M'` / `'S'` / `'D'` / `'N'`).

## Verifications

- **Sub-ladder-extension fidelity**: 9 → 10 extension is faithful, ten
  distinct typeflag values pinned (`0x31`/`0x36`/`0x33`/`0x34`/`0x37` +
  `0x56`/`0x4D`/`0x53`/`0x44`/`0x4E`); GNU sub-ladder closes — `'L'`
  and `'K'` are handled by `forEntries`, not silent-skipped.
- **Adversarial-check fidelity**: `0x4E ↔ 'N' ↔ 78` mapping internally
  consistent; wrapper preserves nine prior arms and exposes only `'N'`.
  Error string per issue: `unexpected typeflag 78`.
- **LF_NAMES framing**: Long-names-old arm distinguished from the
  prior four GNU-arms (volume-header / multi-volume / sparse /
  directory-dump) by the *legacy-format-superseded-by-LF_LONGNAME*
  rationale and the deprecated-extension-aliasing-vs-modern-handler
  distinction (`forEntries` already handles `'L'`/`'K'`).
- **Builder-script docstring**: `Built 11` at PR #2439 land time
  (PR #2437 era was `Built 10`); today's master is `Built 12` after
  PR #2449 added the sibling-class `tar-mixed-skipped.tar` fixture.
  Output list at line 159 enumerates 11 files at PR #2439 land time
  (12 today). Worker chose extend-in-place (rename churn = 0).
- **Test arm**: `lnNamesListed[0]!.typeflag == 0x4E` assertion
  inheriting the GNU sub-ladder convention; chronological PR-merge
  order preserved.
- **Builder determinism**: re-ran
  `scripts/build-symlink-hardlink-malformed-fixtures.lean`,
  `git diff testdata/tar/security/` is empty.
- **Inventory link check**: `errors=0, warnings=9` — same 9 silent-skip
  Reproducer Corpus row warnings on master; my new paired-review entry
  adds zero new warnings (the `#TBD-VERIFY-PR` placeholder in the
  paired-review header line is wrapped in a half-closed-paired-review
  drift-detector opt-out comment so it does not register as stale). The
  in-flight cleanup issue #2447 targets exactly those 9 row warnings
  for opt-out marker insertion.
- **Build/test green**: `lake build` clean, `lake exe test` reports
  *"All tests passed!"*.

## Coordination

In-flight `'D'` paired-review #2442 / PR #2445 has *already landed*
on master (commit `7b5c510`) at the time of this paired-review's
worker branch, so the entry references PR #2445 by number rather than
naming it as in-flight (matches the PR #2444 sequel-style close-out).

The merged-but-unreviewed sibling-class fixture
`tar-mixed-skipped.tar` (PR #2449, in-flight paired-review issue
#2450) is *not* an eleventh per-typeflag arm and is paired-reviewed
separately — out of scope here.

## Quality metrics
- Sorry count: 0 (unchanged)
- New `#TBD-VERIFY-PR` placeholders: 1 (marked with the standard
  half-closed-paired-review opt-out comment, will substitute to
  closing PR number on the worker branch pre-merge per the
  PR #2417 / PR #2422 / PR #2425 / PR #2428 / PR #2431 / PR #2434 /
  PR #2437 self-correction precedent)
- Inventory link warnings: 9 (unchanged from master)

## What remains
- The `#TBD-VERIFY-PR` placeholder in the paired-review header line
  must be substituted to the closing PR number before merge (per the
  established self-correction precedent).
- No further GNU-typeflag silent-skip candidates are queued. Any
  future per-typeflag fixture (e.g. Solaris `'X'` extended attribute,
  `'A'` ACL) should earn its own paired-review entry on the
  established cadence.
