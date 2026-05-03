# 2026-05-03 Track E silent-skip family — `tar-skipped-padded.tar`

Issue: #2456 — Track E silent-skip family extension. Third
sibling-class fixture alongside `tar-mixed-skipped.tar` (PR #2449,
`size == 0` extract-continuation) and `tar-skipped-payload.tar`
(PR #2454, `size == 512` data-advance arithmetic). Pins the
`paddingFor` round-up arithmetic for non-multiples of 512 inside
the silent-skip `else` branch's `skipEntryData input e.size`
data-advance summation.

Branch: `agent/43f06fe5`. Session UUID `43f06fe5-e000-44c0-8db6-d1fa64a5df49`.

## What landed

1. `scripts/build-symlink-hardlink-malformed-fixtures.lean` —
   added `buildPaddedSkippedFixture` helper plus a wiring call in
   `main`. Updated the file-level docstring's fixture catalogue,
   `Output` list, and the build-summary count from 13 → 14.
2. `testdata/tar/security/tar-skipped-padded.tar` — new
   byte-deterministic 3072-byte fixture.
   SHA-256: `99a9026dad15c2338992001cbb0127b8d57d22a4cdf8123b795ff1a4dd9b9e48`.
   Layout (6 × 512 = 3072 bytes):
   - `0x000-0x1FF`: `before.txt` UStar header (typeflag `'0'`, size 7)
   - `0x200-0x3FF`: `before.txt` payload `"BEFORE\n"` + 505-byte zero pad
   - `0x400-0x5FF`: `fifo-entry` UStar header (typeflag `'6'`, size 100)
   - `0x600-0x663`: 100 ASCII `'X'` bytes (`0x58`)
   - `0x664-0x7FF`: 412 zero padding bytes
   - `0x800-0x9FF`: `after.txt` UStar header (typeflag `'0'`, size 6)
   - `0xA00-0xBFF`: `after.txt` payload `"AFTER\n"` + 506-byte zero pad
3. `ZipTest/TarFixtures.lean` — new test arm immediately after
   the existing `tar-skipped-payload.tar` arm. Asserts
   `before.txt = "BEFORE\n"`, `after.txt = "AFTER\n"`, and extract
   dir size == 2. Cleanup `for f in #[…]` and `for d in #[…]`
   loops updated to include the new fixture filename and extract
   dir.
4. `SECURITY_INVENTORY.md` — appended a new bullet-list row
   immediately after the `tar-skipped-payload.tar` row in the
   silent-skip family section. Names the fixture, typeflag `'6'`,
   geometry (3072 bytes, 6 × 512, with explicit note that the
   middle entry's payload + padding together fill exactly one
   512-byte block), the `paddingFor` round-up arithmetic
   invariant, sibling-class precedents (`tar-mixed-skipped.tar`,
   `tar-skipped-payload.tar`), and the per-typeflag arm PR
   numbers. Closing PR cited via `#TBD-VERIFY-PR` placeholder per
   the inventory-reconciliation skill — substitute with the real
   PR number on the worker branch immediately after PR creation.

## Adversarial check

Temporarily replaced the `else` arm's `skipEntryData`
data-advance summation (`Zip/Tar.lean`):

    let dataSize := size.toNat + paddingFor size

with

    let dataSize := size.toNat  -- ADVERSARIAL: dropped `+ paddingFor size`

Result: `lake exe test` aborted at the new fixture's test arm
with `uncaught exception: tar: header checksum mismatch`. The
412-byte under-skip leaves the stream positioned at offset
`0x664`, 412 bytes inside the `after.txt` header; the next
`forEntries` `readExact 512` parses a 512-byte block straddling
the padding-zero region (`0x664-0x7FF`) and the start of the
`after.txt` header / payload, and parseHeader's checksum
verification fails.

The twelve preceding silent-skip siblings (the ten per-typeflag
arms with `size == 0` and the two sibling-class entries
`tar-mixed-skipped.tar` `size == 0` and `tar-skipped-payload.tar`
`size == 512`) all have `paddingFor size == 0` for their
silent-skipped middle entry, so the `+ paddingFor size` summand
is `0` in both the correct and the perturbed code, and the
perturbation is invisible to them — the test crash happened on
the new arm, not earlier.

Reverted the perturbation: `git diff Zip/Tar.lean` is empty
post-revert. Re-ran `lake exe test` — all tests pass.

## Verification

- `lake env lean --run scripts/build-symlink-hardlink-malformed-fixtures.lean`
  succeeds and emits all 14 fixtures.
- `git diff testdata/tar/security/tar-skipped-padded.tar` is
  empty after a fresh re-run (deterministic).
- `lake build` — clean, 201/201 jobs.
- `lake exe test` — all tests pass (TAR fixture tests: OK).
- `bash scripts/check-inventory-links.sh` — `errors=0,
  warnings=1`. The single warning is the expected
  `#TBD-VERIFY-PR` placeholder on the new row, which is
  substituted with the real PR number on the worker branch
  immediately after PR creation per the inventory-reconciliation
  skill.
- Sorry count unchanged at 0.

## Pattern notes

- The issue body suggested perturbing `paddingFor` to return `0`
  unconditionally as the adversarial check; in practice that
  perturbation also breaks regular-file `Tar.extract` (the
  regular-file path at `Zip/Tar.lean` line 788 uses
  `paddingFor entry.size` to round up *its own* payload's
  padding to a 512-byte block, and `before.txt`'s 7-byte payload
  needs 505 bytes of padding consumed). A `paddingFor`-returns-0
  perturbation breaks `before.txt` extraction first, before the
  test ever reaches the silent-skip middle entry, so it is not a
  per-fixture differential test. The targeted perturbation —
  drop the `+ paddingFor size` summand from `skipEntryData`'s
  `dataSize` only — exercises only the silent-skip code path and
  is differential against all twelve preceding silent-skip
  fixtures (each has `paddingFor size == 0` for its skipped
  entry).
- The Reproducer Corpus *table* at `SECURITY_INVENTORY.md` ~5766
  contains rows for the ten per-typeflag arms and
  `tar-mixed-skipped.tar` (PR #2449), but PR #2454 did not add a
  table row for `tar-skipped-payload.tar`. This PR matches the
  PR #2454 precedent — adds only the bullet-list row in the
  silent-skip family enumeration block, no table row.
