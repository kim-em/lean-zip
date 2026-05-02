# Track E: tar-contiguous-skipped.tar fixture

- **UTC**: 2026-05-02T15:10
- **Session**: `3e31cac5` (feature)
- **Issue**: #2420

## Summary

Added `testdata/tar/security/tar-contiguous-skipped.tar` — a 512-byte
single-block UStar header for a zero-byte entry with `path =
"contiguous-entry"`, empty `linkname`, `typeflag = 0x37` ('7', POSIX
UStar contiguous file), checksum recomputed to match. Pins the
`Tar.extract` silent-skip `else` fallback for typeflag `'7'` as the
fifth sibling of the per-typeflag silent-skip family, alongside
`hardlink-outside.tar` (`'1'`), `tar-fifo-skipped.tar` (`'6'`),
`tar-chardev-skipped.tar` (`'3'`), and `tar-blockdev-skipped.tar`
(`'4'`).

With this fixture landing, the POSIX UStar `'0'`–`'7'` numeric range
is fully fixtured — every value `'0'` through `'7'` has either a typed
branch in `Tar.extract` (`'0'` regular, `'2'` symlink, `'5'`
directory) or a silent-skip regression fixture.

The strict-vs-lenient distinction is the security-relevant policy
choice this fixture pins: POSIX UStar permits lenient extractors to
alias `'7'` to `'0'` (regular file), but lean-zip's strict `==` chain
rejects `'7'` and silent-skips, refusing to materialise a payload that
a malicious archive might ship expecting lenient extraction.

## Files touched

- `scripts/build-symlink-hardlink-malformed-fixtures.lean` — module
  docstring bullet + Output list entry + `buildZeroSizeFixture` call
  for `"contiguous-entry"` / `0x37` / `tar-contiguous-skipped.tar`.
  Bumped trailing `IO.println` count `5 → 6`.
- `testdata/tar/security/tar-contiguous-skipped.tar` — new 512-byte
  fixture. Byte-deterministic across two builder runs.
- `ZipTest/TarFixtures.lean` — new test arm immediately after the
  `tar-blockdev-skipped.tar` arm, asserting the extract dir remains
  empty after `Tar.extract`. Cleanup loops include the new fixture
  filename and the new `/tmp/lean-zip-fixture-tar-contiguous-skipped-extract`
  directory.
- `SECURITY_INVENTORY.md` — new *Recent wins* bullet under
  *Tar Public APIs* and a new *Reproducer Corpus* row immediately
  after the `tar-blockdev-skipped.tar` row, mirroring that row's
  density (~30 lines of prose). Closing-PR placeholder is
  `#TBD-VERIFY-PR` for post-PR substitution.

## Adversarial check

Temporarily replaced the `else` body in `Zip/Tar.lean`'s
`Tar.extract` typeflag chain with:

```lean
if e.typeflag == typeHardlink || e.typeflag == 0x36 ||
    e.typeflag == 0x33 || e.typeflag == 0x34 then
  skipEntryData input e.size
else
  throw (IO.userError s!"adversarial: unexpected typeflag {e.typeflag}")
```

Ran `lake exe test`; outcome:

- `tar-contiguous-skipped.tar` arm fired with
  `uncaught exception: adversarial: unexpected typeflag 55`
  (`55 = 0x37` = `'7'`).
- All other tar fixture arms passed — including
  `hardlink-outside.tar`, `tar-fifo-skipped.tar`,
  `tar-chardev-skipped.tar`, and `tar-blockdev-skipped.tar`, which
  the wrapper preserves explicitly.

Reverted the `Zip/Tar.lean` edit before staging the commit; `git
diff Zip/Tar.lean` is empty.

## Verification

- `lake build` succeeds, no `sorry` introduced (sorry count unchanged
  at 0).
- `lake exe test` passes — including the new arm.
- `bash scripts/check-inventory-links.sh` reports `errors=0,
  warnings=5` (warnings are pre-existing `#TBD-VERIFY-PR` placeholders
  on the sibling fixture rows plus the new placeholder added by this
  PR — substituted post-PR creation).
- Byte-determinism check: two consecutive runs of
  `lake env lean --run scripts/build-symlink-hardlink-malformed-fixtures.lean`
  produce an identical 512-byte
  `testdata/tar/security/tar-contiguous-skipped.tar`.
- Fixture geometry: `wc -c` reports `512`; first 0xa0 bytes show
  `path = "contiguous-entry"`, `typeflag = 0x37` at offset 0x9c
  (the UStar typeflag offset 156).

## Out of scope (deferred)

- Paired-review entry for this PR — filed separately by a future
  planning round once the PR lands.
- Docstring tweak to `Tar.extract` enumeration to name "contiguous
  files" alongside "character and block devices, FIFOs, GNU sparse,
  etc." — issue body explicitly calls this PR fixture-only ("no spec
  changes, no production-code changes"); leave the docstring update
  to a future audit pass if desired.
