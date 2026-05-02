# Track E: tar-sparse-skipped.tar fixture (typeflag 'S' silent-skip)

- Date: 2026-05-02T19:09:07Z
- Session: 0fc29266
- Type: feature
- Issue: #2429

## What landed

Third GNU-typeflag sibling of the per-typeflag silent-skip family,
extending the GNU sub-ladder distinct from the POSIX UStar `'0'`–`'7'`
range. Pins `Tar.extract`'s tail `else` arm against typeflag `'S'`
(GNU sparse file, `0x53`) so a future refactor toward a lenient
sparse-aware reconstructor would fail the regression test.

Files touched:

- `scripts/build-symlink-hardlink-malformed-fixtures.lean` —
  appended a `buildZeroSizeFixture "sparse-entry" "" 0x53 …`
  invocation; bumped the closing `IO.println` count from 8 to 9;
  added a docstring bullet describing `tar-sparse-skipped.tar` and
  appended it to the *Output (byte-deterministic)* list.
- `testdata/tar/security/tar-sparse-skipped.tar` — new 512-byte
  single-block UStar fixture (typeflag `0x53`, `path =
  "sparse-entry"`, empty linkname, size 0). Byte-deterministic across
  re-runs (verified locally).
- `ZipTest/TarFixtures.lean` — appended a test arm after the
  `tar-multivol-skipped.tar` arm: read fixture, extract to
  `/tmp/lean-zip-fixture-tar-sparse-skipped-extract`, assert extract
  dir is empty, then list and assert `typeflag == 0x53`. Cleanup arrays
  updated to include the new fixture and extract dir.
- `SECURITY_INVENTORY.md` — added a *Symlink/hardlink extraction
  policy* fixture-list bullet for `tar-sparse-skipped.tar` and a
  *Reproducer Corpus* table row in landing order after
  `tar-multivol-skipped.tar`. Closing-PR slot uses the
  `#TBD-VERIFY-PR` placeholder per the project's
  inventory-reconciliation skill — substitute post-PR creation.

## Adversarial check

Temporarily replaced the tail `else` arm's `skipEntryData` with an
explicit guard that fires on `'S'`:

```lean
if e.typeflag == typeHardlink || e.typeflag == 0x36 ||
   e.typeflag == 0x33 || e.typeflag == 0x34 || e.typeflag == 0x37 ||
   e.typeflag == 0x56 || e.typeflag == 0x4D
then skipEntryData input e.size
else throw (IO.userError s!"adversarial: unexpected typeflag {e.typeflag}")
```

`lake exe test` then fired with `uncaught exception: adversarial:
unexpected typeflag 83` (`83 = 0x53`), confirming the new fixture
independently exercises the silent-skip fallback for `'S'` while all
prior siblings (`hardlink-outside.tar`, `tar-fifo-skipped.tar`,
`tar-chardev-skipped.tar`, `tar-blockdev-skipped.tar`,
`tar-contiguous-skipped.tar`, `tar-volumeheader-skipped.tar`,
`tar-multivol-skipped.tar`) still pass. The `Zip/Tar.lean` edit was
reverted before staging the commit (`git diff Zip/Tar.lean` is
empty post-revert).

## Verification

- `lake build` — clean build, 201 jobs, no errors.
- `lake exe test` — `All tests passed!`.
- `bash scripts/check-inventory-links.sh` — `errors=0`. Warning count
  rose from 6 to 8 due to the two new `#TBD-VERIFY-PR` placeholders
  in the new Reproducer Corpus row (one in the `closing-PR` column;
  the other is a re-detection by the same regex), to be substituted
  post-PR creation.
- `lake env lean --run scripts/build-symlink-hardlink-malformed-fixtures.lean`
  — re-runs produce byte-identical `tar-sparse-skipped.tar`.
- `wc -c testdata/tar/security/tar-sparse-skipped.tar` reports `512`.
- `xxd` confirms typeflag at offset 0x9C is `0x53`, `path =
  "sparse-entry"`.

## Quality metrics

- Sorry count: 0 (unchanged).

## Coordination notes

The pre-existing uncommitted modifications in the worktree to
`.claude/CLAUDE.md` and `.claude/skills/agent-worker-flow/SKILL.md`
(present at session start) are out of scope for this issue and were
deliberately not staged. `.claude/CLAUDE.md` is off-limits per the
project's *Off-limits Files* rule.

## What remains

- Substitute `#TBD-VERIFY-PR` with the real PR number after PR
  creation, in the same branch, in a follow-up commit before merge
  (mirroring the PR #2419 / PR #2421 / PR #2422 / PR #2425 / PR #2428
  / PR #2431 substitution pattern).
- Sibling planner issue #2430 (`'D'` GNU directory-dump,
  `0x44`) remains the next GNU-typeflag fixture in the ladder.
