# Progress: decompressBlocksWF compressed literals-only content theorems

- **Date**: 2026-03-08 UTC
- **Session**: feature (1ed18030)
- **Issue**: #957

## Accomplished

Added two block-loop content characterization theorems for compressed blocks
with numSeq == 0 (literals only) in `Zip/Spec/Zstd.lean`:

1. **`decompressBlocksWF_single_compressed_literals_only`**: When a single
   last compressed block has numSeq == 0, result is `output ++ literals` at
   position `afterHdr + hdr.blockSize.toNat`.

2. **`decompressBlocksWF_compressed_literals_only_step`**: When a non-last
   compressed block has numSeq == 0, the function recurses with updated output
   (`output ++ literals`), updated Huffman table (new if present, else previous),
   unchanged FSE tables and offset history, at position blockEnd.

## Decisions

- Used `Except.mapError.eq_2` instead of `Except.mapError` in simp sets —
  the latter causes incomplete reduction while the equation lemma cleanly
  handles the `.ok` case from `parseLiteralsSection`.
- For the step theorem, used `rw [show ... from by unfold ...; rfl]` to unfold
  only the LHS (since `unfold` affects all occurrences), then closed the
  residual huffTree match discrepancy with `congr 1; cases huffTree <;> rfl`.
- Added `beq_self_eq_true` to simp sets for the `numSeq == 0` boolean check.
- Used `SequenceCompressionModes` (not `SequencesHeaderModes` as the issue
  stated) — the actual type in the codebase.

## Quality metrics

- Sorry count: 4 → 4 (unchanged, all XxHash UInt64)
- Tests: 48/48 conformance, all pass
- No `native_decide`
- Proofs use `simp only [...]`

## What remains

- Future: compressed block content theorems for numSeq > 0 (full sequence
  decoding pipeline — significantly more complex)
