# Session b4c8dcdd — 2026-03-13

**Type**: feature
**Issue**: #1367 — Track E: Frame-level WellFormedSimpleBlocks succeeds

## Accomplished

All three deliverables from the issue completed:

1. **`decompressFrame_succeeds_of_well_formed_simple`**: Frame-level theorem proving
   `decompressFrame` succeeds when blocks satisfy `WellFormedSimpleBlocks`. Direct
   analogue of `decompressFrame_succeeds_of_well_formed` but for raw/RLE-only blocks.

2. **`decompressZstd_succeeds_of_well_formed_simple`**: API-level theorem lifting the
   frame-level result to `decompressZstd`, following the standard proof chain:
   `parseFrameHeader_succeeds` → frame-level → `decompressZstd_single_frame`.

3. **`decompressZstd_succeeds_three_blocks_raw_rle_raw_simple`**: Three-block corollary
   demonstrating N-block composition at the API level (raw → RLE → raw).

## Quality Metrics

- Sorry count: 4 (unchanged, all in XxHash)
- No new sorries introduced
- `lake build Zip.Spec.ZstdFrame` passes cleanly
- Full build has pre-existing `zstd_ffi.o` failure (missing zstd.h on this machine)

## Decisions

- Followed the exact same proof structure as `decompressFrame_succeeds_of_well_formed`
  for consistency — the proofs are essentially identical but use the SimpleBlocks variant.
- Three-block corollary uses raw/RLE/raw pattern (issue suggested raw/RLE/raw) to
  demonstrate mixed block types at frame level.
