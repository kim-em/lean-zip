# Progress: Compressed sequences block-loop theorems

- **Date**: 2026-03-08 UTC
- **Session**: f891c5e7 (feature)
- **Issue**: #967

## Accomplished

Added two theorems to `Zip/Spec/Zstd.lean` completing the block-loop content
characterization for compressed blocks with numSeq > 0:

1. **`decompressBlocksWF_single_compressed_sequences`**: When `decompressBlocksWF`
   encounters a single last compressed block with sequences, the result is
   `output ++ blockOutput` (from the full sequence pipeline) at position blockEnd.

2. **`decompressBlocksWF_compressed_sequences_step`**: When a non-last compressed
   block with sequences is encountered, the function recurses with updated output,
   Huffman table, completely replaced FSE tables, and updated offset history.

## Key decisions

- Used `simp only` with `hNumSeq` (¬ numSeq == 0) to dismiss the literals-only
  branch, matching the mechanical WF unfolding pattern from raw/RLE theorems.
- Step theorem uses `cases huffTree <;> exact heq` to handle the Huffman table
  update match expression (simpler than `convert`/`congr` approach needed for
  the dependent match pattern from function unfolding).

## Quality metrics

- Sorry count: 4 (unchanged, all in XxHash)
- No `native_decide`
- All proofs use `simp only [...]`
- Build and tests pass

## What remains

With these 2 theorems, the 8-theorem block-loop matrix is complete:
- Raw: single + step (existing)
- RLE: single + step (existing)
- Compressed numSeq=0: single + step (#957)
- Compressed numSeq>0: single + step (this session)

Issue #973 (frame-level compressed content) was blocked waiting for this work.
