# Progress: decompressFrame compressed content

- **Date**: 2026-03-08 UTC
- **Session**: 6626fe38 (feature)
- **Issue**: #973

## Accomplished

Added two frame-level content theorems for compressed blocks in `Zip/Spec/Zstd.lean`:

1. **`decompressFrame_single_compressed_literals_content`**: When `decompressFrame`
   succeeds and the frame contains a single last compressed block with numSeq=0
   (literals only), the output equals the literal section content.

2. **`decompressFrame_single_compressed_sequences_content`**: When `decompressFrame`
   succeeds and the frame contains a single last compressed block with sequences
   (numSeq > 0), the output equals the `executeSequences` result.

Both follow the established pattern from `decompressFrame_single_raw_content` and
`decompressFrame_single_rle_content`: derive block-loop precondition, apply
block-loop theorem, unfold `decompressFrame`, handle dictionary check, and use
`grind` to finish.

## Key decisions

- For the sequences theorem, the `executeSequences` hypothesis uses `ByteArray.empty`
  as the window history (not the conditional window check expression), since
  `decompressBlocks` starts with empty output and `ByteArray.empty.size = 0` is
  never `> windowSize.toNat`. An intermediate `hexec'` lemma bridges the gap
  using `simp only [ByteArray.size_empty, Nat.not_lt_zero, decide_false, Bool.and_false]`.

## Quality metrics

- Sorry count: 4 (unchanged, all in XxHash)
- All tests pass (48/48 conformance)
- No new `sorry` introduced
- 136 lines added to `Zip/Spec/Zstd.lean`
