# 2026-05-02T18:37Z — tar-multivol-skipped.tar fixture (issue #2426)

Session UUID: db8c7be8
Type: feature
Issue: #2426

## Summary

Extended the per-typeflag silent-skip fixture family to its **second
GNU-typeflag sibling**, opening the second rung of the GNU-typeflag
sub-ladder distinct from the POSIX UStar `'0'`–`'7'` range. The fixture
`testdata/tar/security/tar-multivol-skipped.tar` (typeflag `'M'`,
GNU multi-volume continuation marker, `0x4D`) pins the silent-skip
`else` fallback in `Tar.extract` for the GNU multi-volume-continuation
arm. Seven silent-skip siblings now span two sub-ladders: POSIX UStar
`'1'`/`'3'`/`'4'`/`'6'`/`'7'` (closed) plus GNU-typeflag `'V'`/`'M'`
(extending; remaining future GNU-typeflag candidate is `'S'` (sparse
file, `0x53`)).

## Deliverables

- New fixture `testdata/tar/security/tar-multivol-skipped.tar`
  (512 B, byte-deterministic).
  SHA-256: `fb2cbbbeefcc59a0a4d5be02f00d9aaee143d4174e54a2c11163ba651e2b2e1d`.
- `scripts/build-symlink-hardlink-malformed-fixtures.lean`: added an
  eighth `buildZeroSizeFixture` call for `multivol-entry` /
  typeflag `0x4D`; updated module docstring (Output enumeration +
  per-typeflag enumeration); incremented build summary line from
  `Built 7` to `Built 8`.
- `ZipTest/TarFixtures.lean`: added a sibling test arm immediately
  after `tar-volumeheader-skipped.tar` mirroring the volumeheader
  shape (extract dir empty + optional `Tar.list`
  typeflag-preservation assertion). Added the new fixture path and
  extract-dir path to both cleanup loops.
- `SECURITY_INVENTORY.md`: added a *Symlink/hardlink extraction
  policy* fixture-enumeration bullet for the multi-volume-continuation
  arm; added a *Reproducer Corpus* row immediately after the
  `tar-volumeheader-skipped.tar` row carrying the seven required
  prose elements.

## Adversarial check

Per the issue's deliverable 5: temporarily wrapped the `else` body in
`Zip/Tar.lean` with

    if e.typeflag == typeHardlink || e.typeflag == 0x36 ||
       e.typeflag == 0x33 || e.typeflag == 0x34 || e.typeflag == 0x37 ||
       e.typeflag == 0x56
    then skipEntryData input e.size
    else throw (IO.userError s!"adversarial: unexpected typeflag {e.typeflag}")

Ran `lake exe test` — confirmed:

- `tar-multivol-skipped.tar` arm fired with
  `uncaught exception: adversarial: unexpected typeflag 77` (`77 = 0x4D`).
- All six prior siblings (`hardlink-outside.tar`,
  `tar-fifo-skipped.tar`, `tar-chardev-skipped.tar`,
  `tar-blockdev-skipped.tar`, `tar-contiguous-skipped.tar`,
  `tar-volumeheader-skipped.tar`) passed through the explicit guard.

The Tar.lean edit was reverted before staging (verified by
`git diff Zip/Tar.lean` returning empty).

## Verification

- `lake build`: succeeds, no `sorry` introduced (sorry count 0,
  unchanged from baseline).
- `lake exe test`: all tests pass; `TAR fixture tests: OK`.
- Byte-determinism: rebuilt the fixture twice, SHA-256 unchanged
  (`fb2cbbbeefcc59a0a4d5be02f00d9aaee143d4174e54a2c11163ba651e2b2e1d`).
- Fixture geometry: `wc -c` reports 512 B; `xxd | head` confirms
  `path = "multivol-entry"`, `typeflag = 0x4D` (offset 156),
  `size = 0`, UStar magic block.
- `bash scripts/check-inventory-links.sh`: `errors=0, warnings=7`.
  Two added warnings on the new row's prose (`#TBD-VERIFY-PR`
  placeholder and `during this PR` phrase) — both will resolve once
  the closing PR number is substituted post-merge, mirroring the
  per-typeflag sibling pattern from PR #2417 / #2422 / #2425 /
  #2428. Pre-existing warnings (5) on prior siblings unchanged.
  No errors.

## Decisions

- **Sub-ladder extension** in prose: the new row and the
  *Symlink/hardlink extraction policy* bullet both call out this as
  the **second GNU-typeflag** sibling (extending the GNU-typeflag
  sub-ladder opened by `tar-volumeheader-skipped.tar` in PR #2428).
  The `'V'` row's framing of `'M'` as a "future GNU-typeflag
  candidate" is preserved verbatim — its parenthetical remains
  accurate even after this PR lands, since at the time `'V'` was
  first written `'M'` was still future, and the row is a historical
  audit record.
- **Tar.list typeflag-preservation assertion** included (optional in
  the issue): pins the callers-routing-on-typeflag invariant —
  `Tar.list` returns the entry verbatim with `typeflag = 0x4D` even
  though `Tar.extract` skips it. A future refactor that aliases `'M'`
  to `'0'` in `Tar.list` would now fail this assertion. Mirrors the
  `tar-volumeheader-skipped.tar` precedent which added the same
  assertion for `'V'` / `0x56`.
- **Row ordering**: placed the new row immediately after
  `tar-volumeheader-skipped.tar` (PR #2428) — matching the established
  landing-order pattern used by all previous per-typeflag siblings
  (each new sibling appended at the end of the corpus rather than
  inserted in alphabetical-by-fixture-path order).

## Patterns / files touched

- `scripts/build-symlink-hardlink-malformed-fixtures.lean` — eighth
  `buildZeroSizeFixture` call.
- `ZipTest/TarFixtures.lean` — sibling test arm + cleanup-loop
  registration.
- `SECURITY_INVENTORY.md` — fixture-enumeration bullet + Reproducer
  Corpus row (placeholder closing-PR `#TBD-VERIFY-PR`).

## Next steps

- Substitute `#TBD-VERIFY-PR` with the real closing PR number on this
  same branch immediately after PR creation, mirroring the post-#2419
  / post-#2421 / post-#2425 / post-#2428 substitution pattern.
- Future per-typeflag extensions: `'S'` (sparse file, `0x53`) remains
  open as the third candidate for the GNU-typeflag sub-ladder
  (issue #2429 already filed).
- Paired-review issue for this PR will be filed in a later planning
  round once the PR lands (per the issue's *Context* section).
