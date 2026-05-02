# 2026-05-02T23:45Z — Paired review: PR #2428 (`tar-volumeheader-skipped.tar`)

Session UUID: 57987d90
Type: review
Issue: #2435

## Summary

Filed the paired-review entry for PR #2428 — the **first GNU-typeflag
arm** of the `Tar.extract` silent-skip family, opening the GNU
sub-ladder beyond the now-capped POSIX UStar `'1'`–`'7'` numeric
range. The new entry sits immediately after the PR #2425
paired-review (PR #2433 closing #2432) and immediately before the
*Symlink/hardlink extraction policy* fixture-enumeration block,
matching the position prescribed by the issue body.

## Inventory edit

Single edit, doc-only, +349 lines on `SECURITY_INVENTORY.md`:

- Insertion point: between line 3293 (the closing `paired-review.`
  of the PR #2425 paired-review block) and line 3295 (`####
  Symlink/hardlink extraction policy` heading) on the pre-edit
  tree.
- Block shape mirrors the PR #2433 paired-review (lines 2998–3293,
  ~296 lines). The new block runs to ~349 lines — the additional
  size comes from explicitly reconciling land-time state vs.
  today's master state in the *Fixture-builder rename-vs-extend*,
  *Test-arm placement*, and *Stable-cite discipline* sub-bullets
  (PR #2431 / PR #2434 / PR #2437 / PR #2439 have all landed since
  PR #2428, advancing the build-summary count from 7 to 11 and
  changing the alphabetical-order verdict on the cluster).

## Sub-bullets covered

The seven required claim sub-sections (issue body deliverable 1)
are all present:

1. **Sub-ladder-shift claim fidelity (5 → 6 fixtures, first GNU
   arm)** — enumerates all five POSIX UStar siblings with their
   typeflag glyphs / hex (`0x31` / `0x36` / `0x33` / `0x34` /
   `0x37`) plus the new GNU `'V'` arm at `0x56`; cites the prior
   paired-reviews PR #2419 / PR #2421 / PR #2427 / PR #2433; names
   the GNU candidates `'M'` / `'S'` / `'D'` (with closing PRs
   #2431 / #2434 / #2437 noted as "since landed").
2. **Fixture-builder rename-vs-extend choice** — confirms
   extend-in-place; cites the docstring's seven-output
   enumeration and the `Built 7` summary line at PR #2428 land
   time; explicitly notes the post-merge tree's `Built 11` reflects
   subsequent landings.
3. **Reproducer Corpus row prose fidelity** — verifies all seven
   required elements; explicitly notes the path-name framing
   variance (worker chose `volume-label-entry` rather than the
   issue body's *suggested* `volume-header-entry`, and explains
   why this is faithful per the GNU info-node terminology); the
   capability-boundary framing (multi-volume assembly is
   out-of-TCB) is the arm-specific extension over the chardev /
   FIFO / blockdev / contiguous arms' resource / aliasing prose.
4. **Adversarial-check fidelity** — verifies `0x56` ↔ ASCII `'V'`
   ↔ decimal `86` mapping; verifies the wrapper preserves all
   five POSIX UStar arms and exposes only `'V'`; verifies the
   fired error reads `unexpected typeflag 86`.
5. **Test-arm placement** — verifies tail-of-cluster placement at
   land time (chronological-by-PR-merge-order); explicitly notes
   the alphabetical and chronological tails coincide at land
   time but diverge after the GNU-typeflag successors land
   (PR #2431 / PR #2434 / PR #2437 / PR #2439); verifies the
   arm-specific `Tar.list` typeflag-preservation assertion is an
   **additive** extension, not a substitution for the
   empty-extract-dir check; verifies the assertion shape has
   since been inherited by all four GNU-typeflag successors.
6. **Stable-cite discipline** — verifies `errors=0, warnings=9`
   on the master tree this paired-review branches from
   (unchanged from the pre-edit baseline confirmed via `bash
   scripts/check-inventory-links.sh`). The paired-review entry's
   `#TBD-VERIFY-PR` placeholder header line is wrapped in a
   `<!-- drift-detector: ... -->` opt-out comment so it does not
   register as a stale placeholder warning.
7. **Ladder-progression close-out** — cites the full progression
   PR #1555 → PR #2413 → PR #2417 → PR #2422 → PR #2425 → PR
   #2428 with paired-review siblings PR #2419 / PR #2421 /
   PR #2427 / PR #2433; names the GNU candidates `'M'` / `'S'` /
   `'D'` (with closing PRs since landed) plus possible future
   arms `'X'` / `'A'` / `'N'` (with `'N'` since landed in
   PR #2439); states "no new follow-up issue is filed".

## Closing-PR placeholder

Per the issue body deliverable 2: the paired-review entry header
line carries the `#TBD-VERIFY-PR` placeholder wrapped in a
`<!-- drift-detector: half-closed paired-review placeholder,
substituted to the real PR number on the worker branch before
merge -->` opt-out comment. After PR creation the worker
substitutes `#TBD-VERIFY-PR` → `#NNNN` (the just-created PR
number) on the same branch and force-pushes, mirroring the
PR #2419 / PR #2421 / PR #2427 / PR #2433 substitution pattern.

## Verification

- `lake build`: succeeds (no source changes — inventory edit
  only). 201 jobs built.
- `lake exe test`: all tests pass — `TAR fixture tests: OK`,
  benchmark tests passed, fuzz tests passed, all bounded-read
  helper tests passed, `All tests passed!`.
- `bash scripts/check-inventory-links.sh`: `errors=0, warnings=9`
  — unchanged from the pre-edit master baseline. The paired-review
  block introduces zero new warnings (the `#TBD-VERIFY-PR`
  placeholder line and any prose mentions of `this PR` /
  `#TBD-VERIFY-PR` are wrapped in `<!-- drift-detector: -->`
  opt-outs).
- Sorry count unchanged: `Total sorrys: 0` (`grep -rc sorry Zip/`).

## Decisions

- **Block length**: ~349 lines vs. PR #2433's ~296 lines. The
  extra ~50 lines explicitly reconcile PR #2428 land-time state
  vs. today's master state across the *Fixture-builder*,
  *Test-arm placement*, and *Stable-cite* sub-bullets, since
  multiple GNU-typeflag successors (PR #2431 / PR #2434 / PR
  #2437 / PR #2439) have landed in the interval between PR #2428
  and this paired-review and the audit must be honest about which
  sub-claims are land-time vs. master-time.
- **Path-name variance**: the issue body's *suggested*
  `volume-header-entry` does not match the merged tree's
  `volume-label-entry`. The issue body explicitly admitted either
  was acceptable. The paired-review notes this as a minor framing
  variance with the GNU info-node terminology rationale, not a
  fidelity defect.
- **Tar.list assertion**: the volume-header arm has two
  assertions (empty extract dir + `Tar.list` typeflag = 0x56)
  rather than the FIFO / chardev / blockdev / contiguous shape's
  one assertion. The paired-review notes this as an **additive**
  extension and an arm-specific feature that has since become
  the load-bearing convention for the GNU sub-ladder (PR #2431 /
  PR #2434 / PR #2437 / PR #2439 each carry the same shape).

## Files touched

- `SECURITY_INVENTORY.md` (+349 lines, paired-review block).
- `progress/20260502T234555Z_57987d90_review-pr2428-volumeheader-pairedreview.md` (new session log).

## Next steps

- Push the branch, create the PR (gets a real number).
- Substitute `#TBD-VERIFY-PR` → `#NNNN` on the same branch and
  force-push, per the half-closed placeholder convention.
- Future follow-ups: paired-reviews for PR #2431 / PR #2434 /
  PR #2437 / PR #2439 (each per-PR per the established cadence)
  remain open as planning candidates — separate issues, not
  filed by this paired-review.
