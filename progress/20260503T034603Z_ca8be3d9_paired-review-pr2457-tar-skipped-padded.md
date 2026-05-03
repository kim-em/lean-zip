# 2026-05-03 Paired review of PR #2457 — `tar-skipped-padded.tar`

Issue: #2458 — Paired review for PR #2457 (third sibling-class entry
of the silent-skip family, `tar-skipped-padded.tar`, pinning the
`paddingFor` round-up arithmetic for non-multiples of 512 inside the
silent-skip `else` branch's `skipEntryData input e.size` call's
`let dataSize := size.toNat + paddingFor size` summation).

Branch: `agent/ca8be3d9`. Session UUID `ca8be3d9-bc10-447f-acce-060ace2c05ce`.

## What landed

`SECURITY_INVENTORY.md` — added a new `Paired review of PR #2457`
entry inserted immediately after the PR #2454 paired-review entry,
before the `#### Symlink/hardlink extraction policy` block. Six
sub-sections matching the PR #2454 precedent + a closing
`Sub-category-closure close-out` paragraph (mirroring PR #2449's
`Sub-category-opener close-out`):

1. **Padding-round-up-vs-data-advance-vs-extract-continuation
   invariant framing fidelity.** Verifies the row names the
   *padding round-up arithmetic* invariant explicitly, frames the
   third entry as *closing the load-bearing-invariant ladder of
   `skipEntryData`* (rather than extending it), correctly
   enumerates the twelve all-`paddingFor size == 0` precedents
   (ten per-typeflag arms + first sibling-class with `size == 0`
   + second sibling-class with `size == 512`), and records the
   row's position in the silent-skip enumeration block (ordered
   after `tar-skipped-payload.tar`).
2. **Three-entry geometry + payload-content + non-multiple-of-512
   choice fidelity.** Verifies geometry (3072 bytes, 6 × 512),
   per-entry payloads/sizes/typeflags
   (`"BEFORE\n"`/100×`'X'`+412 zero pad/`"AFTER\n"`,
   sizes 7/100/6, typeflags `'0'`/`'6'`/`'0'`), SHA-256
   `99a9026dad15c2338992001cbb0127b8d57d22a4cdf8123b795ff1a4dd9b9e48`,
   the worker's choice of `size == 100` as the parsimony minimum
   non-multiple-of-512, and the test-arm assertions
   (content + count). Records alternative non-multiples
   (`size == 513`, `size == 1023`) for completeness.
3. **Adversarial-check fidelity + perturbation-choice rationale.**
   Verifies the session log records the targeted perturbation
   (drop `+ paddingFor size` from `skipEntryData`'s `dataSize`
   only), the failure mode (`tar: header checksum mismatch`),
   the twelve-sibling differentiation, and the post-revert empty
   `git diff Zip/Tar.lean`. Records the *Pattern notes*
   divergence from the issue body's suggested perturbation
   (perturb `paddingFor` to return `0` unconditionally — which
   breaks `before.txt` extraction first because the regular-file
   path also calls `paddingFor`, so it is not differential
   between fixtures) and explains why the chosen single-summand
   drop is the unique perturbation that fires only on the new
   silent-skip middle entry.
4. **Reproducer Corpus row prose fidelity.** Verifies the row
   carries (i) three-entry geometry, (ii) padding round-up
   invariant phrasing, (iii) third sibling-class framing,
   (iv) contents + count test-arm description, (v) past-tense
   adversarial-check clause (no drift-detector marker required —
   matches PR #2454's precedent), (vi) `Tar.list` symmetry
   caveat, (vii) stable Zip/Tar.lean anchors. Notes the
   bullet-list-only-no-table-row choice (matching PR #2454's
   precedent rather than the per-typeflag /
   `tar-mixed-skipped.tar` precedent of also adding a
   Reproducer Corpus *table* row).
5. **Stable-cite discipline.** Verifies all cited PRs are real
   merged PRs (PR #1555 / PR #2413 / PR #2417 / PR #2422 /
   PR #2425 / PR #2428 / PR #2431 / PR #2434 / PR #2437 /
   PR #2439 / PR #2449 / PR #2454 / PR #2459 / PR #2461),
   `bash scripts/check-inventory-links.sh` clean
   (`errors=0, warnings=0`), `#TBD-VERIFY-PR` placeholder
   wrapped in opt-out marker.
6. **Sub-category-closure close-out.** The trio
   (`tar-mixed-skipped.tar` PR #2449, `tar-skipped-payload.tar`
   PR #2454, `tar-skipped-padded.tar` PR #2457) collectively
   pins both summands of the `let dataSize := size.toNat +
   paddingFor size` computation. The arithmetic axis of the
   sibling-class sub-category is fully closed: there is no
   fourth arithmetic shape of `size` modulo 512 to fixturise.
   Future sibling-class extensions (if any) would pin
   non-arithmetic invariants such as `Tar.list` continuation
   (the `Tar.list` arm on `tar-mixed-skipped.tar` landed at
   PR #2462, opening a new `Tar.list` axis distinct from this
   `skipEntryData` ladder) or extract-continuation under
   long-name-prefixed silent-skip entries; no such issue is
   in flight. No new follow-up issue is filed by this
   paired-review.

## Verification

- Rebuilt the .lake cache (the worktree had stale olean files
  from the prior session — `lake build` failed initially with
  *"failed to read file '.lake/build/lib/lean/Zip.olean',
  incompatible header"* until `rm -rf .lake && lake build`).
- `lake env lean --run scripts/build-symlink-hardlink-malformed-fixtures.lean`
  succeeds; `git diff testdata/tar/security/tar-skipped-padded.tar`
  is empty (deterministic).
- `shasum -a 256 testdata/tar/security/tar-skipped-padded.tar`
  reports
  `99a9026dad15c2338992001cbb0127b8d57d22a4cdf8123b795ff1a4dd9b9e48`
  matching the issue's recorded sentinel.
- `lake build` — clean, 201/201 jobs.
- `lake exe test` — all tests pass (TAR fixture tests: OK).
- `bash scripts/check-inventory-links.sh` —
  `errors=0, warnings=0` on the worker branch.
- Sorry count unchanged at 0.

## Pattern notes

- Issue body claims `#2450` and `#2455` are *unclaimed at file
  time of this issue*, but both have since landed (PR #2459
  closing #2450, PR #2461 closing #2455 — both visible on
  master at session-claim time). The new paired-review prose
  cites the merged closing-PR numbers throughout, dropping the
  *unclaimed at file time* phrasing and instead positioning
  the new entry as *third in the sibling-class sub-category*
  with both predecessors named by their closing PRs.
- The worktree had stray uncommitted edits to
  `.claude/CLAUDE.md` and `.claude/skills/agent-worker-flow/SKILL.md`
  from a prior session (the modifications are present on origin/master
  too — they appear to be a stale local checkout state, not WIP
  changes). Restored both files via `git restore` before branching;
  agents must not modify the project's top-level CLAUDE.md per
  policy.
- Followed the PR #2454 paired-review's structural template
  (six sub-sections + closing `Sub-category-closure close-out`),
  rather than the PR #2449 paired-review's *Sub-category-opener*
  close-out, to reflect the trio's now-closed status along the
  `skipEntryData` arithmetic axis.
