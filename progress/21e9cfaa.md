# Progress: API-level two-block succeeds (comp_zero_seq first)

- **Date**: 2026-03-12 ~10:30 UTC
- **Session**: feature (21e9cfaa)
- **Issue**: #1255

## Accomplished

Added two API-level composed completeness theorems in `Zip/Spec/ZstdFrame.lean`:

1. `decompressZstd_succeeds_compressed_zero_seq_then_raw_frame` — lifts
   `decompressFrame_succeeds_compressed_zero_seq_then_raw` through
   `parseFrameHeader_succeeds` + `decompressZstd_single_frame`

2. `decompressZstd_succeeds_compressed_zero_seq_then_rle_frame` — lifts
   `decompressFrame_succeeds_compressed_zero_seq_then_rle` similarly

Both follow the established API-level composition pattern with universally
quantified hypotheses over `(hdr, afterHdr)` from `parseFrameHeader`, and
use `let off2 := ...` binding in block 2 hypotheses (matching the raw-first
pattern for variable-offset block 2).

## Decisions

- Used `let off2 := afterHdr + 3 + block1CompressedSize` pattern for block 2
  hypotheses since compressed block 1 has variable size (unlike RLE's fixed
  offset of `afterHdr + 4`)
- Also skipped stale issue #1283 (fix merge conflict for closed PR #1265) —
  PR was superseded and branch reused

## Quality metrics

- Sorry count: 4 (unchanged, all XxHash UInt64)
- Zero errors in build
- All tests pass
- 1 file modified: `Zip/Spec/ZstdFrame.lean` (+220 lines)

## API-level two-block matrix after this PR

| Block 1 ↓ / Block 2 → | raw | rle | comp (zero-seq) | comp (sequences) |
|------------------------|-----|-----|-----------------|------------------|
| raw | ⏳ | ⏳ | ⏳ | ❌ |
| rle | ⏳ | ⏳ | ⏳ | ❌ |
| comp (zero-seq) | **✅** | **✅** | ❌ | ❌ |
| comp (sequences) | ❌ | ❌ | ❌ | ❌ |
