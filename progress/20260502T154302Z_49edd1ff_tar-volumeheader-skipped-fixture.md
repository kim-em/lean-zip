# 2026-05-02T15:43Z — tar-volumeheader-skipped.tar fixture (issue #2424)

Session UUID: 49edd1ff
Type: feature
Issue: #2424

## Summary

Extended the per-typeflag silent-skip fixture family to its **first
GNU-typeflag sibling**, opening a new sub-ladder distinct from the
POSIX UStar `'0'`–`'7'` range. The fixture
`testdata/tar/security/tar-volumeheader-skipped.tar` (typeflag `'V'`,
GNU multi-volume archive label marker, `0x56`) pins the silent-skip
`else` fallback in `Tar.extract` for the GNU volume-header arm. Six
silent-skip siblings now span two sub-ladders: POSIX UStar
`'1'`/`'3'`/`'4'`/`'6'`/`'7'` (closed) plus GNU-typeflag `'V'`
(opening; future candidates remain `'M'` and `'S'`).

## Deliverables

- New fixture `testdata/tar/security/tar-volumeheader-skipped.tar`
  (512 B, byte-deterministic).
  SHA-256: `2a975d8f64c9f7ce1556d75329c558fb989488cc82a0af8aca74c9d57bd9fdc1`.
- `scripts/build-symlink-hardlink-malformed-fixtures.lean`: added a
  sixth `buildZeroSizeFixture` call for `volume-label-entry` /
  typeflag `0x56`; updated module docstring (Output enumeration +
  per-typeflag enumeration); incremented build summary line from
  `Built 6` to `Built 7`.
- `ZipTest/TarFixtures.lean`: added a sibling test arm immediately
  after `tar-contiguous-skipped.tar` mirroring the chardev / blockdev
  / contiguous shape (extract dir empty + optional `Tar.list`
  typeflag-preservation assertion). Added the new fixture path and
  extract-dir path to both cleanup loops.
- `SECURITY_INVENTORY.md`: added a *Symlink/hardlink extraction
  policy* fixture-enumeration bullet for the volume-header arm; added
  a *Reproducer Corpus* row immediately after the
  `tar-contiguous-skipped.tar` row (alphabetical-by-path tail of the
  `tar-*-skipped.tar` cluster) carrying the seven required prose
  elements.

## Adversarial check

Per the issue's deliverable 5: temporarily wrapped the `else` body in
`Zip/Tar.lean` with

    if e.typeflag == typeHardlink || e.typeflag == 0x36 ||
       e.typeflag == 0x33 || e.typeflag == 0x34 || e.typeflag == 0x37
    then skipEntryData input e.size
    else throw (IO.userError s!"adversarial: unexpected typeflag {e.typeflag}")

Ran `lake exe test` — confirmed:

- `tar-volumeheader-skipped.tar` arm fired with
  `uncaught exception: adversarial: unexpected typeflag 86` (`86 = 0x56`).
- All five prior siblings (`hardlink-outside.tar`,
  `tar-fifo-skipped.tar`, `tar-chardev-skipped.tar`,
  `tar-blockdev-skipped.tar`, `tar-contiguous-skipped.tar`) passed
  through the explicit guard.

The Tar.lean edit was reverted before staging (verified by
`git diff Zip/Tar.lean` returning empty).

## Verification

- `lake build`: succeeds, no `sorry` introduced (sorry count 0,
  unchanged from baseline).
- `lake exe test`: all tests pass; `TAR fixture tests: OK`.
- Byte-determinism: rebuilt the fixture twice, SHA-256 unchanged
  (`2a975d8f64c9f7ce1556d75329c558fb989488cc82a0af8aca74c9d57bd9fdc1`).
- Fixture geometry: `wc -c` reports 512 B; `xxd | head` confirms
  `path = "volume-label-entry"`, `typeflag = 0x56` (offset 156),
  `size = 0`, UStar magic block.
- `bash scripts/check-inventory-links.sh`: `errors=0, warnings=6`.
  Two added warnings on the new row's prose (`#TBD-VERIFY-PR` placeholder
  and `during this PR` phrase) — both will resolve once the closing
  PR number is substituted post-merge, mirroring the per-typeflag
  sibling pattern from PR #2417 / #2422 / #2425. Pre-existing
  warnings (4) on prior siblings unchanged. No errors.

## Decisions

- **Sub-ladder framing** in prose: the new row and the *Symlink/hardlink
  extraction policy* bullet both call out this as the **first
  GNU-typeflag** sibling (sub-ladder distinct from POSIX UStar
  `'0'`–`'7'`), to set up future `'M'` (multi-volume continuation,
  `0x4D`, issue #2426) and `'S'` (sparse file, `0x53`) extensions.
- **Tar.list typeflag-preservation assertion** included (optional in
  the issue): pins the callers-routing-on-typeflag invariant —
  `Tar.list` returns the entry verbatim with `typeflag = 0x56` even
  though `Tar.extract` skips it. A future refactor that aliases `'V'`
  to `'0'` in `Tar.list` would now fail this assertion.
- **Row ordering**: placed the new row immediately after
  `tar-contiguous-skipped.tar` (PR #2425) per the issue's
  alphabetical-by-fixture-path-tail instruction (`v` > `c`).

## Patterns / files touched

- `scripts/build-symlink-hardlink-malformed-fixtures.lean` — sixth
  `buildZeroSizeFixture` call.
- `ZipTest/TarFixtures.lean` — sibling test arm + cleanup-loop
  registration.
- `SECURITY_INVENTORY.md` — fixture-enumeration bullet + Reproducer
  Corpus row (placeholder closing-PR `#TBD-VERIFY-PR`).

## Next steps

- Substitute `#TBD-VERIFY-PR` with the real closing PR number on this
  same branch immediately after PR creation, mirroring the post-#2419
  / post-#2421 / post-#2425 substitution pattern.
- Future per-typeflag extensions: issue #2426 (`'M'` multi-volume
  continuation) is already filed; `'S'` (sparse file, `0x53`) remains
  open as a future candidate.
- Paired-review issue for this PR will be filed in a later planning
  round once the PR lands (per the issue's *Context* section).
