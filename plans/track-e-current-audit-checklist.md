# Track E Current Audit Checklist

First-pass, repo-specific checklist for the current attack surface.
This is the concrete queue the orchestrator should keep draining in
parallel with proof work.

## Priority 0: ZIP unchecked-size and local-span audit

Target file: [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean:1)

- [x] Add a helper that validates `entry.localOffset`, local header size,
  `nameLen`, `extraLen`, and `compressedSize` against actual file size
  before any `readExact` of local metadata or payload.
  (`assertSpanInFile` in `Zip/Archive.lean`.)
- [x] Make `readEntryData` fail before `Handle.read` if the claimed local
  data span extends past EOF. (Span checks wrap the header, name+extra,
  and payload reads; see `readEntryData` in `Zip/Archive.lean`.)
- [ ] Add malformed fixtures for ZIP64 entries claiming exabyte-scale
  compressed or uncompressed sizes. (Partially covered by the 32-bit
  `oversized-compressed-size.zip` fixture; ZIP64-specific variants
  still outstanding.)
- [x] Add a regression test that ensures oversized claims fail cleanly
  without panic or OOM.
  (`testdata/zip/malformed/oversized-compressed-size.zip` +
   `ZipTest/ZipFixtures.lean` assertThrows on `"local data span"`.)
- [ ] Audit central-directory vs local-header consistency checks and decide
  which mismatches should be hard errors.

## Priority 1: Tar partial-decoder audit

Target file: [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean:1)

- [ ] Enumerate all `String.fromUTF8!` callsites reachable from untrusted
  tar bytes and replace them with validated or failure-returning paths
  where needed.
- [ ] Add malformed PAX fixtures:
  invalid UTF-8 keys, invalid UTF-8 values, oversized decimal lengths,
  truncated records, and inconsistent record lengths.
- [ ] Add malformed GNU long-name fixtures:
  missing terminator, truncated payload, invalid UTF-8.
- [ ] Document symlink and hardlink extraction policy explicitly and test
  archive-slip variants against it.

## Priority 2: Public decompression limit policy

Targets:

- [Zip/Basic.lean](/home/kim/lean-zip/Zip/Basic.lean:1)
- [Zip/Gzip.lean](/home/kim/lean-zip/Zip/Gzip.lean:1)
- [Zip/RawDeflate.lean](/home/kim/lean-zip/Zip/RawDeflate.lean:1)
- [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean:432)

- [ ] Inventory every public API where `0 = no limit`.
- [ ] Decide which APIs should keep that behavior and which should expose
  safer extraction defaults.
- [ ] Add decompression-bomb tests for:
  raw deflate, gzip, zlib, ZIP extraction, and tar.gz extraction.
- [ ] Make the limit policy explicit in docstrings and user-facing errors.

## Priority 3: FFI adversarial validation

Target file: [c/zlib_ffi.c](/home/kim/lean-zip/c/zlib_ffi.c:1)

- [ ] Add a dedicated sanitizer script or documented invocation for
  building/running the FFI paths under ASan and UBSan.
- [ ] Add regression coverage for:
  truncated streams, concatenated-member edge cases, repeated `inflateReset`,
  zero-length chunks, and near-limit outputs.
- [ ] Add a fuzz harness for whole-buffer and streaming inflate entry points.
- [ ] Audit all `malloc`/`realloc`/buffer-growth sites after each substantial
  C change.

## Priority 4: Trusted runtime boundary documentation

Targets:

- [SECURITY_INVENTORY.md](/home/kim/lean-zip/SECURITY_INVENTORY.md:1)
- [PLAN.md](/home/kim/lean-zip/PLAN.md:1)

- [ ] Keep the Lean runtime allocation/read issue tracked here until
  upstream fix status is confirmed and local regression coverage exists.
- [ ] Add minimized reproducer references once they are checked into the repo
  or linked from issues.
- [ ] Record which callsites have been guarded locally to avoid depending on
  runtime behavior for adversarial size rejection.

## Priority 5: Proof-friendly guard lemmas

Targets:

- [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean:341)
- [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean:169)

- [ ] Introduce proof-friendly helper functions for bounded reads and
  validated spans.
- [ ] Prove simple lemmas of the form:
  validated span implies requested read length is file-bounded.
- [ ] Use those helpers so parser hardening is easier to audit and less
  likely to regress than open-coded checks.

## Completion Rule

This checklist is not done when items are merely documented. Each closed
item should ideally land with at least one of:

- a code guard
- a regression test or malformed fixture
- a sanitizer/fuzz harness
- a proof or helper lemma
