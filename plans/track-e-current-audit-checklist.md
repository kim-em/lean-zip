# Track E Current Audit Checklist

First-pass, repo-specific checklist for the current attack surface.
This is the concrete queue the orchestrator should keep draining in
parallel with proof work.

## Priority 0: ZIP unchecked-size and local-span audit

Target file: [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean)

- [x] Add a helper that validates `entry.localOffset`, local header size,
  `nameLen`, `extraLen`, and `compressedSize` against actual file size
  before any `readExact` of local metadata or payload.
  (`assertSpanInFile` in `Zip/Archive.lean`.)
- [x] Make `readEntryData` fail before `Handle.read` if the claimed local
  data span extends past EOF. (Span checks wrap the header, name+extra,
  and payload reads; see `readEntryData` in `Zip/Archive.lean`.)
- [x] Add malformed fixtures for ZIP64 entries claiming exabyte-scale
  compressed or uncompressed sizes. (32-bit variant already covered by
  `testdata/zip/malformed/oversized-compressed-size.zip`; ZIP64
  `compressedSize` variant landed by PR #1543 in
  `testdata/zip/malformed/oversized-zip64-compressed-size.zip`; ZIP64
  `uncompressedSize` variant landed by PR #1544 in
  `testdata/zip/malformed/oversized-zip64-uncompressed-size.zip`.)
- [x] Add a regression test that ensures oversized claims fail cleanly
  without panic or OOM.
  (`testdata/zip/malformed/oversized-compressed-size.zip` +
   `ZipTest/ZipFixtures.lean` assertThrows on `"local data span"`.)
- [x] Audit central-directory vs local-header consistency checks and decide
  which mismatches should be hard errors.
  (Landed by PR #1554: `readEntryData` in `Zip/Archive.lean` now parses
  the local header's flags/method/crc/sizes — including the ZIP64 local
  extra block — and hard-errors on method/compressedSize/uncompressedSize/
  crc disagreement with the CD entry, except when local flag bit 3 leaves
  crc/sizes legitimately zero in the LH; regression coverage added in
  `testdata/zip/malformed/cd-lh-method-mismatch.zip` and
  `testdata/zip/malformed/cd-lh-size-mismatch.zip`.)

## Priority 1: Tar partial-decoder audit

Target file: [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean)

- [x] Enumerate all `String.fromUTF8!` callsites reachable from untrusted
  tar bytes and replace them with validated or failure-returning paths
  where needed.
  (Landed by PR #1550: three panicking raw-byte truncations in
  `buildPaxEntry` and `create` replaced by `Tar.truncateUTF8` which rounds
  to the nearest codepoint boundary; the two remaining `fromUTF8!` sites
  in `splitPath` are documented as safe because the split is at an ASCII
  `'/'` byte. Regression coverage in `ZipTest/TarPathTruncation.lean`.)
- [x] Add malformed PAX fixtures:
  invalid UTF-8 keys, invalid UTF-8 values, oversized decimal lengths,
  truncated records, and inconsistent record lengths.
  (Landed by PR #1545:
   `testdata/tar/malformed/pax-oversized-length.tar`,
   `pax-truncated-record.tar`, `pax-invalid-utf8-key.tar`,
   `pax-invalid-utf8-value.tar`, `pax-inconsistent-length.tar`;
   built by `scripts/build-pax-malformed-fixtures.lean`.)
- [x] Add malformed GNU long-name fixtures:
  missing terminator, truncated payload, invalid UTF-8.
  (Landed by PR #1546: `testdata/tar/malformed/gnu-longname-truncated.tar`,
  `gnu-longname-no-terminator.tar`, `gnu-longname-invalid-utf8.tar`,
  `gnu-longlink-truncated.tar`.)
- [x] Document symlink and hardlink extraction policy explicitly and test
  archive-slip variants against it.
  (Landed by PR #1555: per-typeflag policy now in the `Tar.extract`
  docstring and in `SECURITY_INVENTORY.md` § "Tar Parser/Extractor —
  Symlink/hardlink extraction policy"; `typeHardlink` is now a named
  constant in `Zip/Tar.lean`. Fixtures:
  `testdata/tar/security/symlink-absolute.tar`, `hardlink-outside.tar`,
  and the previously orphaned `backslash-slip.tar`, asserted in
  `ZipTest/TarFixtures.lean`; built by
  `scripts/build-symlink-hardlink-malformed-fixtures.lean`.)

## Priority 2: Public decompression limit policy

Targets:

- [Zip/Basic.lean](/home/kim/lean-zip/Zip/Basic.lean)
- [Zip/Gzip.lean](/home/kim/lean-zip/Zip/Gzip.lean)
- [Zip/RawDeflate.lean](/home/kim/lean-zip/Zip/RawDeflate.lean)
- [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean)

- [x] Inventory every public API where `0 = no limit`.
  (See *"Decompression Limit Inventory"* in
  [SECURITY_INVENTORY.md](/home/kim/lean-zip/SECURITY_INVENTORY.md).)
- [x] Decide which APIs should keep that behavior and which should expose
  safer extraction defaults.
  (Proposed direction in the *"Recommended policy"* subsection of
  [SECURITY_INVENTORY.md](/home/kim/lean-zip/SECURITY_INVENTORY.md);
  final numbers and signature changes are deferred to follow-up issues
  so this inventory stays doc-only.)
- [x] Add decompression-bomb tests for:
  raw deflate, gzip, zlib, ZIP extraction, and tar.gz extraction.
  (`ZipTest/{RawDeflate,Gzip,Zlib,Archive,Tar,NativeGzip}.lean` — every
  surface has at least one test asserting the bomb error substring.)
- [x] Make the limit policy explicit in docstrings and user-facing errors.
  (FFI: PR #1573; Archive + Tar: PR #1586; native: this PR for
  `Zip/Native/Inflate.lean` and `Zip/Native/Gzip.lean`.)

## Priority 3: FFI adversarial validation

Target file: [c/zlib_ffi.c](/home/kim/lean-zip/c/zlib_ffi.c)

- [x] Add a dedicated sanitizer script or documented invocation for
  building/running the FFI paths under ASan and UBSan.
  (`scripts/sanitize-ffi.sh` rebuilds `c/zlib_ffi.c` under
  `-fsanitize=address,undefined`, explicitly links GCC's
  libasan/libubsan past Lean's bundled clang, and runs the test
  suite with `LD_PRELOAD` so ASan initialises first. The April 2026
  tree is ASan + UBSan clean; see the PR for the trailing transcript.)
- [x] Add regression coverage for:
  truncated streams, concatenated-member edge cases, repeated `inflateReset`,
  zero-length chunks, and near-limit outputs.
  (Landed by PR #1571 (truncated streams across `Zlib`, `Gzip`, and
  `RawDeflate`), PR #1572 (concatenated-member and zero-length-chunk
  edge cases), and PR #1577 (repeated `inflateReset` across concatenated
  gzip members + exact-fit and n−1 near-limit outputs). Coverage in
  `ZipTest/Gzip.lean`, `ZipTest/Zlib.lean`, and `ZipTest/RawDeflate.lean`.)
- [x] Add a fuzz harness for whole-buffer and streaming inflate entry points.
  ([`ZipTest/FuzzInflate.lean`](/home/kim/lean-zip/ZipTest/FuzzInflate.lean),
  [`ZipFuzzInflate.lean`](/home/kim/lean-zip/ZipFuzzInflate.lean),
  [`scripts/fuzz-inflate.sh`](/home/kim/lean-zip/scripts/fuzz-inflate.sh)
  land a deterministic xorshift-seeded driver that feeds every
  whole-buffer (`Zlib.decompress`, `Gzip.decompress`,
  `RawDeflate.decompress`, and the four native decoders) and the
  streaming `Gzip.InflateState` path with pseudo-random inputs.
  `lake exe test` runs a fixed-seed 100-iteration smoke check; the
  `fuzz_inflate` lake executable drives longer wall-clock budgeted
  runs. Sanitizer coverage is obtained by reusing the
  `ZLIB_CFLAGS / ZLIB_LDFLAGS / LD_PRELOAD` recipe from
  `scripts/sanitize-ffi.sh`.)
- [x] Audit all `malloc`/`realloc`/buffer-growth sites after each substantial
  C change.
  (Initial snapshot landed: see
  [`SECURITY_INVENTORY.md`](/home/kim/lean-zip/SECURITY_INVENTORY.md)
  § *"Allocation site audit (`c/zlib_ffi.c`)"* for the current row-per-
  call-site table. The re-audit-on-change obligation remains — this
  item tracks the invariant, not a one-time snapshot.
  [`scripts/check-c-allocations.sh`](/home/kim/lean-zip/scripts/check-c-allocations.sh)
  flags accidental new `malloc`/`realloc`/`calloc` sites at PR-review
  time against the baseline count recorded there.)

## Priority 4: Trusted runtime boundary documentation

Targets:

- [SECURITY_INVENTORY.md](/home/kim/lean-zip/SECURITY_INVENTORY.md)
- [PLAN.md](/home/kim/lean-zip/PLAN.md)

- [x] Keep the Lean runtime allocation/read issue tracked here until
  upstream fix status is confirmed and local regression coverage exists.
  (Landed by the PR closing issue #1582: new *"Upstream tracking"*
  sub-block in
  [`SECURITY_INVENTORY.md`](/home/kim/lean-zip/SECURITY_INVENTORY.md)
  § *"Lean Runtime"* records the report, the current upstream status
  (*"no upstream link yet — local tracking only"*, dated 2026-04-22),
  and the local regression coverage — ZIP64 oversized-size fixtures
  from PRs #1543/#1544, CD-vs-LH mismatch fixtures from PR #1554,
  and the bomb-limit regression tests from PRs #1560/#1561 — that
  guards this attack surface today.)
- [x] Add minimized reproducer references once they are checked into the repo
  or linked from issues.
  (Landed by this PR: new *"Minimized Reproducer Corpus"* section in
  [`SECURITY_INVENTORY.md`](/home/kim/lean-zip/SECURITY_INVENTORY.md)
  tabulates all 31 fixtures under `testdata/zip/malformed/`,
  `testdata/tar/malformed/`, and `testdata/tar/security/` with the
  guard they exercise, their first-landing PR (or `481e562` for
  fixtures inherited from the initial `lean-zlib → lean-zip` import),
  and a `{oversized allocation, partial-decoder panic, archive-slip,
  decompression bomb, other}` class tag.)
- [x] Record which callsites have been guarded locally to avoid depending on
  runtime behavior for adversarial size rejection.
  (See [`SECURITY_INVENTORY.md`](/home/kim/lean-zip/SECURITY_INVENTORY.md)
  § *"Local guard inventory for `Handle.read` and `Stream.read`"* for
  the per-site audit of the `Zip/Archive.lean` and `Zip/Tar.lean` read
  surface, with explicit rows for each `readExact`, `readEntryData`,
  `skipEntryData`, and inline-loop callsite.)

## Priority 5: Proof-friendly guard lemmas

Targets:

- [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean)
- [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean)

- [x] Introduce proof-friendly helper functions for bounded reads and
  validated spans.
  (PR #1608 landed `readBoundedSpanFromHandle`,
  `readBoundedExactFromHandle`, `readBoundedExactFromStream`, and
  `readBoundedEntryData` plus smoke coverage in
  `ZipTest/BoundedReadTest.lean`.)
- [x] Prove simple lemmas of the form:
  validated span implies requested read length is file-bounded.
  (This PR introduced the pure `Archive.SpanInFile` predicate alongside
  `assertSpanInFile`, the two `IO` reduction theorems
  `assertSpanInFile_eq_pure_of_spanInFile` /
  `spanInFile_of_assertSpanInFile_succeeds`, and the `Nat`-level
  arithmetic corollaries `SpanInFile.toNat_add_le` /
  `SpanInFile.toNat_length_le_remaining`.)
- [x] Use those helpers so parser hardening is easier to audit and less
  likely to regress than open-coded checks.
  (This PR migrated the three `Zip/Archive.lean` `readEntryData`
  `assertSpanInFile` + seek + `readExact` chains to
  `readBoundedSpanFromHandle`, and the four GNU/PAX
  `Zip/Tar.lean` `readEntryData` callsites to
  `readBoundedEntryData`.)

## Completion Rule

This checklist is not done when items are merely documented. Each closed
item should ideally land with at least one of:

- a code guard
- a regression test or malformed fixture
- a sanitizer/fuzz harness
- a proof or helper lemma
