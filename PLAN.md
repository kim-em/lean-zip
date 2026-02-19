# Current Plan

<!-- Rewritten at the start of each work session. -->
<!-- If a session ends with unchecked items, the next session continues here. -->

## Status: Complete

## Session type: review

## Objective

Full review of code added since last review (2026-02-19 Phase 2 review).
That review covered BitReader.lean and Inflate.lean. Since then:
- `Zip/Native/Gzip.lean` (gzip/zlib framing) — NEW, not yet reviewed
- `Zip/Archive.lean` integration changes — not yet reviewed
- `Zip/Tar.lean` integration changes — not yet reviewed
- `ZipTest/NativeGzip.lean` — not yet reviewed
- `ZipTest/NativeIntegration.lean` — not yet reviewed

## Review checklist

- [x] **Gzip.lean deep review**: RFC 1952/1950 compliance, error handling,
      edge cases, security (max output enforcement, header parsing bounds)
- [x] **Archive.lean integration**: correct native decompression path,
      error handling, CRC verification
- [x] **Tar.lean integration**: correct native gzip path, memory handling
- [x] **Test coverage review**: gaps in NativeGzip and NativeIntegration tests
- [x] **Slop detection**: dead code, verbose comments, unused imports across
      all recent additions
- [x] **Security audit**: input validation, zip bomb protection, integer
      handling in new code
- [x] **Lean idioms**: newer APIs, style consistency
- [x] **Toolchain check**: is there a newer stable Lean release?
- [x] **Prompting/skills check**: is .claude/CLAUDE.md still accurate?

## Fixes applied

- **Security**: Capped per-member inflate budget to remaining output allowance
  in `GzipDecode.decompress`, preventing ~2x maxOutputSize peak memory with
  crafted concatenated gzip streams
- **Dead code**: Removed unused `BitReader.ofByteArray`, `remaining`, `isEof`
- **Test refactor**: Extracted `mkRandomData` helper to `Helpers.lean`,
  deduplicated from NativeInflate and NativeGzip tests
- **Test output**: Fixed NativeIntegration test to use consistent formatting
- **Documentation**: Updated CLAUDE.md source layout to list all Native/ files
