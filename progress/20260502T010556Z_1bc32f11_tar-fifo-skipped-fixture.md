# Session 1bc32f11 — `tar-fifo-skipped.tar` (typeflag '6' silent-skip pin)

- **UTC**: 2026-05-02 01:05Z
- **Type**: feature
- **Issue**: #2412
- **Branch**: agent/1bc32f11

## Summary

Added `tar-fifo-skipped.tar` security fixture pinning `Tar.extract`'s
silent-skip `else` fallback for unsupported typeflag `'6'` (POSIX UStar
FIFO, `0x36`). Second per-typeflag fixture in the silent-skip family
alongside `hardlink-outside.tar` (typeflag `'1'`); together the two
pin two distinct typeflag values against the shared fallback.

## Deliverables

1. Extended `scripts/build-symlink-hardlink-malformed-fixtures.lean`
   with a third `buildZeroSizeFixture` call producing
   `testdata/tar/security/tar-fifo-skipped.tar`. Updated the module
   docstring's per-typeflag policy enumeration to mention the new FIFO
   arm, and renamed the build summary line to "per-typeflag-policy"
   to match the now-broader scope. Did not rename the script file
   itself — the existing path stays stable for paired-review and
   future per-typeflag siblings can extend the same script.
2. New test arm in `ZipTest/TarFixtures.lean` immediately after the
   `hardlink-outside.tar` arm, mirroring its `extract → readDir →
   isEmpty` pattern. Added `tar-fifo-skipped.tar` to the file cleanup
   list and `/tmp/lean-zip-fixture-tar-fifo-skipped-extract` to the
   directory cleanup list.
3. New row in `SECURITY_INVENTORY.md` Reproducer Corpus table, sorted
   alphabetically between `tar-absolute.tar` and `tar-slip.tar`. Cites
   only stable identifiers (function names, fixture filenames) per the
   PR #2353 decision; closing PR cited via `#TBD-VERIFY-PR` placeholder
   per the PR #2364 substitution convention.
4. Added `tar-fifo-skipped.tar` to the *Symlink/hardlink extraction
   policy* fixture enumeration alongside `hardlink-outside.tar`.

## Determinism

Built fixture twice; SHA-256 stable across runs:

    b2e897b74be1264344e508ffd27269f261a08bdaced2f71ded907769155e352a  testdata/tar/security/tar-fifo-skipped.tar

Size: exactly 512 B (single UStar header, no payload, no trailing zero
blocks — matches `hardlink-outside.tar` geometry).

## Adversarial check

Per the issue's verification gate: temporarily replaced the silent-skip
`else` branch in `Tar.extract` (Zip/Tar.lean) with

    if e.typeflag == typeHardlink then
      skipEntryData input e.size
    else
      throw (IO.userError s!"adversarial: unexpected typeflag {e.typeflag}")

and ran `lake exe test`. Confirmed:

- `hardlink-outside.tar` test still passed (its typeflag still routes
  through the preserved `typeHardlink` arm)
- `tar-fifo-skipped.tar` test fired with
  `uncaught exception: adversarial: unexpected typeflag 54` (`0x36 = 54`)

This proves the new fixture independently exercises the FIFO arm and
the existing `hardlink-outside.tar` fixture alone is structurally
insufficient for the silent-skip family. Reverted the change before
commit; `git diff Zip/Tar.lean` is empty post-revert.

## Verification

- `lake build` — green
- `lake exe test` — *All tests passed!* (TAR fixture tests: OK)
- `bash scripts/check-inventory-links.sh` — `errors=0, warnings=2`
  (the 2 new warnings are the `#TBD-VERIFY-PR` placeholders, expected
  per the established substitution-on-merge pattern)
- Sorry count unchanged: `0`

## Out of scope (deferred to future planner cycles)

- No third sibling fixture for character device `'3'`, block device
  `'4'`, or GNU sparse `'S'` — each per-typeflag fixture is its own
  atomic PR per the issue body.
- No paired-review entry — that lands as a sibling paired-review PR
  per the established Track E cadence (PR #2405 paired by PR #2407,
  PR #2399 paired by PR #2403, etc.).
- No PROGRESS.md or PLAN.md edits.
