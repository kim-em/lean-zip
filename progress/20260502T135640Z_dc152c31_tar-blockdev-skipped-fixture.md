# Session 20260502T135640Z (UUID prefix dc152c31, /feature)

## Issue

[#2416](https://github.com/kim-em/lean-zip/issues/2416) — Track E:
`tar-blockdev-skipped.tar` fixture pinning `Tar.extract` silent-skip
policy for unsupported typeflag `'4'` (POSIX UStar block device,
`0x34`). Sibling per-typeflag fixture extending the silent-skip
family from 3 → 4 alongside `hardlink-outside.tar` (`'1'`),
`tar-fifo-skipped.tar` (`'6'`), and `tar-chardev-skipped.tar` (`'3'`).

## Skip / orient log

- `coordination orient` showed three Linux-only `human-oversight`
  issues (#2348 / #2350 / #2351 — all blocked) and four unclaimed
  `feature` issues. Prior PRs from this branch family had already
  shipped `tar-fifo-skipped` (PR #2413) and `tar-chardev-skipped`
  (PR #2417); the chardev sibling was on master at session start.
- Claimed #2366 first (oldest unclaimed) → skipped: Linux-only
  sanitize-ffi.sh recipe, macOS host cannot satisfy env guard.
  Documented precedent — sessions `cbd9c8a0`, `82c9309b`,
  `d02bf9c1` all skipped for the same reason.
- Claimed #2392 next → skipped: Linux + nightly Rust requirement
  (`sanitize-rust-ffi.sh`); macOS host cannot satisfy env guard.
- Claimed #2416 → matches the macOS-friendly per-typeflag fixture
  pattern (no FFI recipe, just a 512-B UStar header build + Lean
  test + inventory update).

## Deliverables (done)

1. **Builder script extended.** Added a fifth
   `buildZeroSizeFixture "blockdev-entry" "" 0x34
   (outDir / "tar-blockdev-skipped.tar")` call in
   `scripts/build-symlink-hardlink-malformed-fixtures.lean`,
   updated the module docstring's per-fixture enumeration and the
   *"Output (byte-deterministic)"* list, bumped the closing
   `IO.println` count from 4 → 5.
2. **Fixture file generated.** Ran
   `lake env lean --run scripts/build-symlink-hardlink-malformed-fixtures.lean`
   producing `testdata/tar/security/tar-blockdev-skipped.tar`
   (512 B, single UStar header, no payload, no trailing zero blocks
   — matching the `hardlink-outside.tar` / `tar-fifo-skipped.tar`
   / `tar-chardev-skipped.tar` geometry).
3. **Determinism verified.** Built twice, `diff`'d sha256 sums of
   all five tar/security fixtures — empty diff. SHA-256 of the new
   fixture:
   `9ef6dda29da2529019a62aa905b819f7018a0560cd1d1cf946b3f73714d9bae2`.
4. **Test arm added.** Inserted a new block in
   `ZipTest/TarFixtures.lean` immediately after the
   `tar-chardev-skipped.tar` arm, mirroring the chardev arm shape:
   `readFixture` → `writeFixtureTmp` → fresh extract dir → `Tar.extract`
   → `readDir` → `isEmpty` assertion. Added `tar-blockdev-skipped.tar`
   to the temp-file cleanup list and
   `/tmp/lean-zip-fixture-tar-blockdev-skipped-extract` to the
   directory-cleanup loop.
5. **Reproducer Corpus row added.** Inserted in
   `SECURITY_INVENTORY.md` immediately after the
   `tar-chardev-skipped.tar` row, mirroring its prose density and
   structure. Covers: 512-B geometry; `Tar.extract` `else` fallback
   flow with `skipEntryData (size=0)`; `Tar.list` typeflag
   propagation; per-typeflag family extension to 4 arms; adversarial
   check (firing with `unexpected typeflag 52 (0x34)` while the
   three sibling arms still pass); block-device-specific security
   threat (raw-partition / `kmem` / kernel-state node smuggle);
   defense-in-depth fixture-only pattern; writer-side caveat
   (`Tar.create` never emits `'4'`); POSIX cross-reference noting
   `'7'` (contiguous file) as the remaining unfixtured arm. Cited
   `#TBD-VERIFY-PR` per the issue's deferred-substitution
   convention; will substitute on PR creation.
6. **Per-typeflag policy prose updated.** Added a paragraph for
   `tar-blockdev-skipped.tar` in `SECURITY_INVENTORY.md` *Tar
   Parser/Extractor* enumeration, mirroring the sibling chardev
   paragraph.

## Adversarial check

Temporarily wrapped the `Tar.extract` `else` body in
`if e.typeflag == typeHardlink || e.typeflag == 0x36 ||
e.typeflag == 0x33 then skipEntryData input e.size else
throw (IO.userError s!"tar: adversarial check: unexpected
typeflag {e.typeflag}")` and re-ran `lake exe test`. The new
`tar-blockdev-skipped.tar` arm fired with
`uncaught exception: tar: adversarial check: unexpected typeflag 52`
(decimal 52 = `0x34` = POSIX UStar `'4'`). The hardlink, FIFO,
and chardev arms continued to pass — confirming the new fixture
*independently* pins the block-device arm and would catch a
refactor that drops the fallback for typeflag `'4'` while
preserving the other three. Reverted the adversarial wrapper
(`git diff Zip/Tar.lean` empty post-revert).

## Verification

- `lake build` clean (201 jobs).
- `lake exe test` — `All tests passed!`. The
  `TAR fixture tests: OK` line confirms the
  `ZipTest.TarFixtures.tests` block — including the new
  blockdev arm — completed without throwing.
- `bash scripts/check-inventory-links.sh` reports
  `errors=0, warnings=4`. The four warnings are unresolved
  `#TBD` placeholders for `tar-fifo-skipped.tar`,
  `tar-chardev-skipped.tar`, and the new
  `tar-blockdev-skipped.tar` row (which is mine and gets
  substituted post-PR-creation per the issue's convention).
  No new errors.
- Sorry count unchanged: 0.

## Files changed

- `scripts/build-symlink-hardlink-malformed-fixtures.lean` — +16 / -2
  lines (docstring entry, output list, builder call).
- `testdata/tar/security/tar-blockdev-skipped.tar` — new, 512 B,
  SHA-256 `9ef6dda29da2529019a62aa905b819f7018a0560cd1d1cf946b3f73714d9bae2`.
- `ZipTest/TarFixtures.lean` — +25 / -2 lines (test arm + cleanup
  list extensions).
- `SECURITY_INVENTORY.md` — +10 lines (Per-typeflag policy
  paragraph + Reproducer Corpus row).

## Patterns / decisions

- **Adversarial-check selectivity.** The chardev row's adversarial
  recipe wrapped `if typeflag == typeHardlink || typeflag == 0x36`;
  for the blockdev fixture I extended it to `... || typeflag ==
  0x33` so that all three earlier sibling fixtures continue to flow
  through `skipEntryData` while only the new arm throws. This is
  the natural progression as the family grows: each new fixture's
  adversarial recipe excludes all already-fixtured typeflags. The
  next sibling (`'7'` contiguous file, issue #2420) will append
  `... || typeflag == 0x34`.
- **Inventory-row prose density.** Followed the
  `tar-chardev-skipped.tar` row template verbatim; the only
  per-fixture varying elements are the typeflag value, the
  pinned-arm enumeration (now four), the adversarial-check
  recipe (extended above), the block-device-specific security
  threat paragraph (raw-partition / `kmem` smuggle, distinct
  from chardev which mainly threatens TTY-style I/O surfaces),
  and the *"remaining candidates"* sentence trimmed to mention
  only `'7'` (now that `'3'` is closed).
- **Builder-script docstring quartet.** The script's docstring
  now documents five fixtures: the original three
  (`symlink-absolute`, `hardlink-outside`, `tar-fifo-skipped`)
  plus the post-#2417 `tar-chardev-skipped` and the new
  `tar-blockdev-skipped`. Pattern continues to scale to the
  expected `'7'` sibling in #2420.

## Hand-off

After PR creation:
1. Substitute the `#TBD-VERIFY-PR` placeholder in
   `SECURITY_INVENTORY.md` with the actual PR number.
2. The next planner cycle will queue a paired-review issue for
   this PR (matching the cadence of PR #2413 → PR #2419 paired
   review and PR #2417 → its own paired review). Out of scope for
   this PR.
3. Issue #2420 (`tar-contiguous-skipped.tar` for typeflag `'7'`)
   remains unclaimed — it can land in any order relative to this
   PR. Its worker re-reads master to insert after the
   freshly-merged blockdev row in both the script and the
   inventory.

## Stale changes set aside

Pre-existing uncommitted edits to `.claude/CLAUDE.md` and
`.claude/skills/agent-worker-flow/SKILL.md` (off-limits files for
agents) were stashed at session start as
`stale-pre-existing-changes-dc152c31 (off-limits files
.claude/CLAUDE.md + skill)` — matching the prior pattern in the
stash list (`stale-pre-existing-changes-f5ad77c6`,
`stale-pre-existing-changes-cadcc271`,
`stale-pre-2369-session-leftovers`). Did not touch off-limits
files.
