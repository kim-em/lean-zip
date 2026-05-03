# Track E: tar-mixed-skipped.tar fixture (extract-continuation invariant)

- Date: 2026-05-03 (UTC 01:01)
- Session: bd2a9d00-8c77-4e32-8434-d80b15f1ca1e
- Type: feature
- Issue: #2448
- Branch: agent/bd2a9d00

## What landed

Added `tar-mixed-skipped.tar` (2560 bytes — three-entry archive
interleaving a silently-skipped middle entry between two regular files)
pinning `Tar.extract`'s *extract-continuation* invariant: that the
silent-skip `else` branch's `skipEntryData input e.size` call leaves the
input stream positioned exactly at the next 512-byte block boundary so a
subsequent regular-file entry still extracts cleanly. Sibling-class
fixture (not an eleventh per-typeflag arm) — the ten existing
per-typeflag fixtures pin the *existence* of the `else` arm at ten
distinct typeflag values; this fixture pins a *different* invariant
(extract continuation) that none of the ten exercises (each is
single-entry, terminating at EOF after the skipped entry).

Fixture geometry: `before.txt` (typeflag `'0'`, payload `"BEFORE\n"`,
size 7) → `fifo-entry` (typeflag `'6'` = `0x36`, POSIX UStar FIFO,
empty linkname, size 0) → `after.txt` (typeflag `'0'`, payload
`"AFTER\n"`, size 6). 5 × 512 = 2560 bytes (one header+payload pair
per regular entry, one bare header for the FIFO). No trailing zero
blocks. Middle entry reuses typeflag `'6'` to mirror
`tar-fifo-skipped.tar` — pins the same `else` arm without introducing
a new typeflag value.

Files touched:

- `scripts/build-symlink-hardlink-malformed-fixtures.lean` — new
  `buildRegularEntry` + `buildMixedFixture` helpers and a single
  `buildMixedFixture` call from `main`. Extended the module docstring
  with the `tar-mixed-skipped.tar` rationale and bumped the tail
  `IO.println` count from 11 → 12.
- `testdata/tar/security/tar-mixed-skipped.tar` — new fixture,
  byte-deterministic (SHA-256
  `7ed31119d36fc65c80b2c3ff54540c0bba884f925da38fd043d1ddc5524865ef`,
  reproduced across two consecutive runs of the script).
- `ZipTest/TarFixtures.lean` — new test arm extracting into
  `/tmp/lean-zip-fixture-tar-mixed-skipped-extract` and asserting both
  `before.txt` (= `"BEFORE\n"`) and `after.txt` (= `"AFTER\n"`)
  materialise with their declared payloads, plus a count assertion
  (exactly two files in the extract dir). Cleanup loops at the end of
  the test bundle extended with the new fixture name and extract
  directory.
- `SECURITY_INVENTORY.md` — added a new sub-bullet under the
  *Symlink/hardlink extraction policy* fixture enumeration and a new
  row under *Minimized Reproducer Corpus*. The corpus row carries the
  drift-detector suppression marker after the *"during this PR"*
  adversarial-check attribution so the inventory link checker's
  warning count stays at the post-#TBD-VERIFY-PR baseline.
  Closing-PR placeholder is `#TBD-VERIFY-PR`; will be substituted with
  the real PR number in a follow-up commit on the same branch
  immediately after `gh pr create` returns (matches the pattern used
  by PRs #2364 / #2407 / per-typeflag silent-skip rows).

## Verification

- `lake env lean --run scripts/build-symlink-hardlink-malformed-fixtures.lean`
  prints `Built 12 per-typeflag-policy security fixtures under
  testdata/tar/security/.` and reproduces the same SHA-256 across two
  consecutive runs (byte-deterministic).
- `lake build` passes (only the pre-existing `Zip.Spec.Deflate`
  unused-simp-arg linter warning, unrelated to this PR).
- `lake exe test` reports `All tests passed!`; the new
  `tar-mixed-skipped.tar` arm extracts cleanly and asserts both
  `before.txt`/`after.txt` content and the exact file count.
- `bash scripts/check-inventory-links.sh` reports
  `errors=0, warnings=9` — unchanged from the pre-PR baseline (the
  drift-detector marker on the new row suppresses both the
  `#TBD-VERIFY-PR` and the *"this PR"* warnings that would otherwise
  fire on the new corpus row).
- Sorry count unchanged at 0 across all `Zip/` modules.

## Adversarial check

- Perturbation: temporarily replaced the `else` arm's `skipEntryData
  input e.size` with `skipEntryData input (e.size + 1)` in
  `Zip/Tar.lean`.
- `lake build` succeeded under the perturbation; `lake exe test`
  failed mid-`TarFixtures.tests` with `uncaught exception: tar:
  header checksum mismatch`. The trace pins on the
  `tar-mixed-skipped.tar` arm: the 1-byte skip overrun causes
  `forEntries` to consume the `after.txt` header (positions
  0x600–0x7FF) as part of the perturbed FIFO skip, so the
  subsequent `forEntries` `readExact 512` parses the `after.txt`
  *payload* region as a header whose stored checksum cannot match
  the recomputed checksum.
- All ten per-typeflag siblings (`hardlink-outside.tar`,
  `tar-fifo-skipped.tar`, `tar-chardev-skipped.tar`,
  `tar-blockdev-skipped.tar`, `tar-contiguous-skipped.tar`,
  `tar-volumeheader-skipped.tar`, `tar-multivol-skipped.tar`,
  `tar-sparse-skipped.tar`, `tar-incremental-skipped.tar`,
  `tar-longnames-skipped.tar`) ran *before* the mixed arm under the
  perturbation and would have been the first to fail had the
  off-by-one propagated through their single-entry geometry — none
  fired, confirming the issue's analysis that the off-by-one is
  silently absorbed at EOF for single-entry fixtures.
- Reverted the perturbation; `git diff Zip/Tar.lean` is empty
  post-revert; `lake exe test` returns to `All tests passed!`.

## Patterns / decisions

- **Helper extraction over `buildZeroSizeFixture` reuse.** The
  per-typeflag fixtures all use `buildZeroSizeFixture` (one bare
  header, no payload). The mixed fixture needs three entries with
  payloads and padding, so I added a small `buildRegularEntry`
  helper (header + payload + NUL padding to next 512-byte boundary)
  and a `buildMixedFixture` wrapper that emits the three-entry
  byte-string. Extends the script in place — no rename — per the
  PR #2413 paired-review's *Fixture-builder rename-vs-extend choice*
  finding.
- **Typeflag `'6'` reuse.** The middle entry deliberately reuses
  typeflag `'6'` (FIFO, mirroring `tar-fifo-skipped.tar`) rather
  than picking a new typeflag value. This keeps the fixture in the
  `else`-arm sibling family without growing the per-typeflag
  fixture count to eleven; the issue is explicit that this is *not*
  an extension of the per-typeflag ladder.
- **Both content and count assertions in the test arm.** A
  payload-corruption regression that broke `skipEntryData` could
  manifest as either (a) `after.txt` materialising with corrupted
  contents (off-by-one in `skipEntryData` smaller than 512), (b) a
  checksum mismatch on the next header (off-by-one shifts an entire
  block, as the adversarial check confirmed), or (c) `after.txt`
  failing to materialise at all (large skip overrun consumes the
  remaining archive). Asserting both content (`"BEFORE\n"` /
  `"AFTER\n"`) and count (exactly 2 files) covers all three failure
  modes — the count alone would not catch case (a), the content
  alone would not catch case (c), and either alone would not catch
  case (b) decisively.
- **Drift-detector marker placement.** The marker is inline,
  immediately after the `during this PR` phrase in the corpus row,
  matching the precedent placements at SECURITY_INVENTORY.md:2509
  (`during this PR <!-- drift-detector: quote of the
  adversarial-check phrasing in a paired-review finding, not a
  stale placeholder -->`). One marker per row suppresses all `this
  PR` and `#TBD-VERIFY-PR` warnings on that line.

## Follow-ups

- The paired-review issue for this PR is expected to file as the
  next planner cycle picks it up — sibling cadence to the
  per-typeflag paired-review pattern (PRs #2419 / #2421 / #2427 /
  #2433 / #2435 / #2436 / #2441 / #2443 / #2444 / #2445).
- The 9 inventory-link warnings on the per-typeflag silent-skip
  rows (lines 5293–5301) remain in scope for the parallel issue
  #2447, which will retroactively add drift-detector markers; this
  PR does not touch those lines and the baseline warning count is
  unchanged.
- A future audit may decide `Tar.list`'s continuation invariant
  (structurally identical to `Tar.extract`'s via the shared
  `forEntries`) needs its own pin — that would be a separate
  planner-queued issue, scoped *Out of scope* by the current
  issue body.
