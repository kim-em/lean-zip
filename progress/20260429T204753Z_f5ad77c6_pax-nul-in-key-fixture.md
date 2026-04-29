# Progress: pax-nul-in-key.tar fixture (issue #2404)

- **Date/time (UTC)**: 2026-04-29T20:47:53Z
- **Session UUID**: f5ad77c6-7655-47dd-8b1c-c96a61577c6e
- **Session type**: feature
- **Closed issue**: #2404
- **Commits**: 5603a9c (fixture builder + fixture + test), 926328c (inventory)

## What was accomplished

Closed the `keyBytes` arm of `parsePaxRecords`'s NUL-byte guard family
at 3/3 (1 keyBytes + 2 valueBytes) by landing
`testdata/tar/malformed/pax-nul-in-key.tar` — a fixture-only,
defense-in-depth, family-closing fixture matching the UStar `gname` slot
(PR #1957) pattern.

Specifically:

1. Added `fixtureKeyNulInKey` definition in
   `scripts/build-pax-malformed-fixtures.lean` carrying the PAX record
   `"8 a\x00b=v\n"` (NUL embedded in a 3-byte key), and registered it
   in `main` so the builder writes
   `testdata/tar/malformed/pax-nul-in-key.tar` (2048 B, SHA-256
   `1cca49c26d13f6cbb91aab7161aa042e619821db88e78ef88f6fd9aadbed80bb`).

2. Generated the fixture via `lake env lean --run scripts/build-pax-malformed-fixtures.lean`.
   Determinism check: built twice; bytes match.

3. Wired the fixture into `ZipTest/TarFixtures.lean`'s existing PAX-fixture
   loop (the `entries[0]!.path == "hello.txt"` assertion suffices — see
   adversarial check below). Updated the loop comment to mention the
   keyBytes-arm closure (3/3). Added the fixture to the cleanup list.

4. Added a Reproducer Corpus row for `pax-nul-in-key.tar`,
   alphabetically positioned between `pax-linkpath-nul-in-value.tar`
   and `pax-oversized-length.tar` in `SECURITY_INVENTORY.md`.

5. Updated the existing `pax-linkpath-nul-in-value.tar` Reproducer
   Corpus row to drop the trailing *"left for a future per-arm
   extension"* deferral phrase, replacing with a forward-pointer to the
   new fixture (`closed by pax-nul-in-key.tar (PR #TBD-VERIFY-PR)`)
   per the inventory-reconciliation skill's *Executed past-tense
   one-liner*.

6. Same deferral phrase removal applied to the parent Recent wins
   paragraph at lines 2014–2078 (the PAX value-side NUL family
   bullet) — the phrase would otherwise become stale on master with
   this PR landing.

## Key decisions

### Fixture digit-prefix correction

The issue body suggested `"9 a\x00b=v\n"` claiming 9 bytes, but the
sum 1 (digit) + 1 (space) + 3 (key incl. NUL) + 1 `=` + 1 (value)
+ 1 (newline) = 8, not 9. The actual byte count of the literal is
also 8. With a wrong length-9 prefix, `parsePaxRecords` would hit
`recordEnd > data.size` and break before evaluating the keyBytes
guard — defeating the fixture's purpose. The issue says "recompute
if the body shape changes" so I used the correct length-8 digit
prefix: `"8 a\x00b=v\n"`.

### Adversarial defense-in-depth check

Per the issue's Verification step, temporarily disabled the keyBytes
arm of `parsePaxRecords`'s NUL guard (replaced
`(keyBytes.findIdx? (· == 0)).isNone &&` with a comment block) and
re-ran the test. The loop assertion still passed: `applyPaxOverrides`'s
case match drops the `a\x00b` key regardless of the guard, since no
known-key string in the case match contains `\x00`. Restored the
guard before committing.

This confirms the keyBytes arm is genuinely defense-in-depth — it
pins the guard's existence rather than catching its single-arm
removal alone. A future fallback like a prefix-match for
namespace-style keys would silently re-open the smuggle without it.

This also means the keyBytes fixture cannot be exercised by a no-guard
regression baseline alone: it must be paired with code review on the
case-match's exhaustiveness invariant. The inventory row records this
explicitly.

## Patterns reused

- **Defense-in-depth fixture-only family closure**: same pattern as
  PR #1957 (UStar `gname` slot) — closing a guard arm whose removal
  alone wouldn't surface as a test failure, because a downstream
  case-match drops the smuggled value anyway. Pinning the guard's
  existence prevents a future case-match expansion from silently
  re-opening the smuggle.
- **`malformed-fixture-builder` skill**: 2048 B PAX malformed
  budget, byte-deterministic builder, no end-of-archive zero
  blocks, NUL injected via `ByteArray.mk #[0x00]` concatenation
  pattern (mirroring `fixturePathNulInValue` /
  `fixtureLinkpathNulInValue`).
- **`inventory-reconciliation` skill**: *Executed past-tense
  one-liner* phrasing for the deferral closure
  (`closed by pax-nul-in-key.tar (PR #TBD-VERIFY-PR)`); both the
  per-fixture Reproducer Corpus row AND the parent Recent wins
  paragraph updated for inventory honesty.

## Quality metrics

- `grep -rc sorry Zip/`: all files at 0 (unchanged).
- `lake build`: green (201 jobs, no errors).
- `lake exe test`: all tests pass.
- `bash scripts/check-inventory-links.sh`: errors=0, warnings=3
  (the 3 placeholder-PR warnings are this PR's `#TBD-VERIFY-PR`
  insertions, expected and substitute-able post-PR-creation).
- Branch-vs-master diff: 4 files changed (3 test/fixture + 1
  inventory).

## What remains

`#TBD-VERIFY-PR` placeholders (3 occurrences) need substitution with
the real PR number once the PR is created, mirroring the pattern from
PR #2364 / `progress/20260428T122256Z_293ae374_anchor-refresh-closeout.md`.
This is a same-branch follow-up the worker performs immediately after
PR creation, before auto-merge.

No new follow-up issues needed: the `parsePaxRecords` NUL-byte guard
family is now **fully closed at 3/3**, terminal closure of the third
per-slot Tar interior-NUL family in the post-#1928 wave (after the
5-slot UStar family closed at PR #1957 and the 2-slot GNU long-name /
long-link family closed at PR #1953).

## Stashed pre-existing changes

The worktree had leftover changes to `.claude/CLAUDE.md` and
`.claude/skills/agent-worker-flow/SKILL.md` from a prior session
(off-limits to feature workers per project policy). Stashed as
`stale-pre-existing-changes-f5ad77c6 (off-limits files .claude/CLAUDE.md + skill)`
before starting work; not included in this PR.
