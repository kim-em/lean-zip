# Track E: tar-incremental-skipped.tar fixture

UTC: 2026-05-02T19:31:44Z
Session: 4091559b-9a94-4208-885a-80b218dbbeba
Type: feature
Issue: #2430

## What was accomplished

Closed #2430 — added the fourth GNU-typeflag silent-skip fixture
`tar-incremental-skipped.tar` (typeflag `'D'`, `0x44`, GNU
directory-dump for incremental backups). Extends the per-typeflag
silent-skip family to **9 fixtures** spanning two sub-ladders: POSIX
UStar `'1'`/`'3'`/`'4'`/`'6'`/`'7'` (closed) and GNU-typeflag
`'V'`/`'M'`/`'S'`/`'D'` (extending).

Files touched:

- `scripts/build-symlink-hardlink-malformed-fixtures.lean` — appended
  `buildZeroSizeFixture "incremental-entry" "" 0x44`, bumped the
  closing `IO.println` count from 9 to 10, extended the module
  docstring with a ninth bullet and added the new path to the *Output*
  list.
- `testdata/tar/security/tar-incremental-skipped.tar` — generated 512-byte
  single-block UStar header. SHA-256:
  `db71d06e88ff482c3455f77a2c97e16301f02075cbf2fe71de3f5cb4d620d480`.
  Byte-determinism verified by re-run after delete (identical hash).
- `ZipTest/TarFixtures.lean` — new arm matching the V/M/S sibling
  template. Asserts `Tar.extract` leaves the extract dir empty and
  `Tar.list` preserves the entry with `typeflag == 0x44`. Cleanup
  arrays extended with the new fixture and extract-dir paths.
- `SECURITY_INVENTORY.md` — added two rows: the bullet entry under
  *Symlink/hardlink extraction policy → Regression fixtures* (after the
  sparse bullet) and the table row under *Reproducer Corpus* (after
  the sparse row, before the `tar-slip.tar` row). Both carry the
  `#TBD-VERIFY-PR` placeholder pending PR-number substitution
  immediately after PR creation, mirroring the PR #2425 / #2428 /
  #2431 / #2434 substitution pattern.

## Adversarial check

Replaced the `else` arm's `skipEntryData input e.size` in
`Zip/Tar.lean` with:

```lean
if e.typeflag == typeHardlink || e.typeflag == 0x36 ||
   e.typeflag == 0x33 || e.typeflag == 0x34 || e.typeflag == 0x37 ||
   e.typeflag == 0x56 || e.typeflag == 0x4D || e.typeflag == 0x53
then skipEntryData input e.size
else throw (IO.userError s!"adversarial: unexpected typeflag {e.typeflag}")
```

`lake exe test` outcome:

- Tar tests: OK
- Archive tests: OK
- ZIP fixture tests: OK
- TarFixtures arm progression: hardlink-outside / fifo / chardev /
  blockdev / contiguous / volumeheader / multivol / sparse arms all
  passed (each before the new arm in test order)
- New `tar-incremental-skipped.tar` arm fired
  `uncaught exception: adversarial: unexpected typeflag 68` (`0x44`)

Confirms the new fixture independently exercises the silent-skip
fallback for typeflag `'D'`, and the eight prior siblings remain
independent (each fires only its own typeflag value). Reverted the
`Zip/Tar.lean` edit before staging the commit; `git diff Zip/Tar.lean`
is clean.

## Verification

- `lake build` — no errors, no `sorry` introduced.
- `lake exe test` — all tests pass; `TAR fixture tests: OK`.
- `bash scripts/check-inventory-links.sh` — `errors=0, warnings=10`
  (warnings count increased by 2 from the prior 8: one for the new
  bullet row's `#TBD-VERIFY-PR` placeholder, one for the new table
  row's same placeholder; both substituted to the real PR number
  immediately after PR creation).
- Sorry count unchanged (0).
- Fixture geometry: `wc -c
  testdata/tar/security/tar-incremental-skipped.tar` reports `512`;
  `xxd` shows `path = "incremental-entry"`, `typeflag = 0x44` at the
  expected UStar-header offset.

## Patterns / decisions

- **Extend in place**: matched the PR #2413 / #2417 / #2422 / #2425 /
  #2428 / #2431 / #2434 workers' choices on the same script — no
  rename, no splitting. The script docstring already framed itself as
  *"per-typeflag-policy regression fixtures"* (typeflag-count agnostic).
- **Path naming**: `"incremental-entry"` matches the
  `volume-label-entry` / `multivol-entry` / `sparse-entry` /
  `chardev-entry` / `blockdev-entry` / `fifo-entry` /
  `contiguous-entry` per-typeflag-arm naming convention. `incremental`
  reads cleanly as the arm's distinguishing label without colliding
  with any of the prior eight naming conventions.
- **Arm placement**: the new arm in `ZipTest/TarFixtures.lean` lands
  immediately after the sparse arm, in landing order rather than
  strict alphabetical, matching the existing arm progression
  (V → M → S → D mirrors landing sequence).
- **Inventory bullet placement**: the *Symlink/hardlink extraction
  policy → Regression fixtures* bullet list is also in landing order
  (V → M → S → D), not strict alphabetical-by-fixture-path. Matches
  the table row placement.
- **`#TBD-VERIFY-PR` placeholder**: used for both inventory edits;
  substitution to the real PR number happens on the worker branch
  before merge per the PR #2364 / #2419 / #2421 / #2422 / #2425 /
  #2428 / #2431 / #2434 substitution pattern.

## Quality metric deltas

- Sorry count: 0 → 0 (unchanged).
- TarFixtures.lean: +56 lines (new arm + cleanup-array entries).
- SECURITY_INVENTORY.md: +35 lines (bullet entry) + 1 long table row.
- scripts/build-symlink-hardlink-malformed-fixtures.lean: +37 lines
  (docstring bullet + Output list entry + comment block + invocation
  + count bump).
- New byte-deterministic fixture file: 512 B.

## Reference / context

- PR #1555 — silent-skip family precedent (`hardlink-outside.tar`,
  typeflag `'1'`).
- PR #2413 / #2417 / #2422 / #2425 — POSIX UStar siblings (`'6'` /
  `'3'` / `'4'` / `'7'`).
- PR #2428 / #2431 / #2434 — first three GNU-typeflag siblings (`'V'`
  / `'M'` / `'S'`).
- Issue #2430 — this fixture's planning issue.
- Issue #2426 / #2429 / #2430 — the GNU sub-ladder triplet enumerated
  by the prior workers.

## What remains

- Paired-review issue for this PR is filed by a later planning round
  per project cadence (not in scope for this work item).
- The GNU-typeflag sub-ladder remains open-ended after `'D'` lands —
  future GNU-typeflag candidates (e.g. `'I'` GNU continuation,
  `'X'` Solaris extended header, etc.) can be added by the same
  template; no follow-up issue filed by this work item.
