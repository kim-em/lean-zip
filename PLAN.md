# Current Plan

<!-- Rewritten at the start of each work session. -->
<!-- If a session ends with unchecked items, the next session continues here. -->

## Status: Complete

## Session type: review

## Goal: Split InflateCorrect.lean + dead code removal

InflateCorrect.lean was at 1282 lines (over 1000-line limit).

### Steps

1. [x] Remove dead `insert_go_complete` (superseded by `insert_go_complete'`)
2. [x] Fix unused simp argument `beq_iff_eq`
3. [x] Build and test to verify dead code removal
4. [x] Split into 3 files:
   - `Zip/Spec/BitstreamCorrect.lean` — bitstream layer (268 lines)
   - `Zip/Spec/HuffmanCorrect.lean` — TreeHasLeaf, insert, fromLengths (833 lines)
   - `Zip/Spec/InflateCorrect.lean` — final connection + main theorem (146 lines)
5. [x] Update imports in Zip.lean
6. [x] Build and test after split
7. [x] Update CLAUDE.md source layout table
8. [x] Update SESSION.md and PROGRESS.md

### Review findings

- **Dead code**: `insert_go_complete` (58 lines) — superseded by `insert_go_complete'`,
  never referenced
- **Dead variables**: `hlen_pos_nat` in both `insertLoop_forward` and
  `insertLoop_backward` — attempted removal but omega needs them (bridges
  UInt8 ordering to Nat). NOT dead — kept.
- **Duplicated proof**: NC invariant proof in `insertLoop_forward` and
  `insertLoop_backward` (~40 lines each, nearly identical). Not extracting
  because the helper would need ~20 parameters, making it longer than the
  duplication.
- **Duplicated proof**: Initial NC proof in `fromLengths_hasLeaf` and
  `fromLengths_leaf_spec` (~22 lines each). Same reason for not extracting.
- **Huffman.lean at 959 lines**: candidate for splitting but under 1000.
  Defer to future review.
