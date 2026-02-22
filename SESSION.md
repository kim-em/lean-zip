# Session State

<!-- Overwritten at the end of each work session. -->
<!-- Records current working state for the next session to pick up. -->

## Sorry count: 2

Both in `Zip/Spec/InflateCorrect.lean`:
- `decodeDynamicTrees_correct` (line ~91): dynamic Huffman tree correspondence

## Known good commit

`1274d43` — `lake build && lake exe test` succeeds, all tests pass.

## What was accomplished this session

### Review: file split + proof improvements

Split `InflateCorrect.lean` (1050 lines, over 1000-line limit) into two files:

- **`DecodeCorrect.lean`** (705 lines): block-level decode correctness
  - `huffTree_decode_correct`, `decodeStored_correct`, `decodeHuffman_correct`
  - Invariant preservation lemmas (readBits_wf, readBits_pos_inv, etc.)
  - Table correspondence lemmas
  - Copy loop helpers (copyLoop_spec, copyLoop_eq_ofFn)

- **`InflateCorrect.lean`** (333 lines): stream-level correctness
  - `inflateLoop_correct`, `inflate_correct`, `inflate_correct'`
  - `decodeDynamicTrees_correct` (sorry)
  - Fixed/dynamic code correspondence helpers

Proof improvements:
1. Combined `decodeStored_wf` + `decodeStored_pos_inv` into single
   `decodeStored_invariants` theorem (~25 lines saved)
2. Extracted `bfinal_beq_nat_true`/`bfinal_beq_nat_false` helpers
   (3x dedup each in `inflateLoop_correct`)
3. Removed unused `↓reduceIte` from final-block cases
4. Changed `readBits_wf` and `readBits_pos_inv` from `private` to
   public for cross-file access

### Comprehensive scan findings (no action needed)

- All `simp` calls use `simp only` (bare simps only for contradiction closing)
- No unused imports
- No dead code beyond previously documented `readBitsMSB`
- `array_set_ne`/`array_set_self` duplication (Nat vs UInt32) previously
  evaluated, not worth extracting
- Toolchain v4.29.0-rc1 is latest; v4.29.0 stable not yet released
- All files under 1000 lines (largest: Huffman.lean at 959)

## Next action

Priority for next session:

1. **Prove `decodeDynamicTrees_correct`**: The only remaining sorry. This
   connects the native dynamic Huffman tree decoder to the spec. Involves:
   - Code length alphabet decoding
   - Repeat codes (16, 17, 18)
   - Two-pass tree construction
   This is substantial but purely mechanical — no new proof techniques needed.

2. **Alternative**: Implementation session for Phase 4 (compressor).

## Architecture

```
inflate_correct (DONE — depends on decodeDynamicTrees_correct sorry)
  ├── decodeStored_correct (DONE, in DecodeCorrect.lean)
  ├── decodeHuffman_correct (DONE, in DecodeCorrect.lean)
  │   ├── huffTree_decode_correct (DONE)
  │   ├── literal case (DONE)
  │   ├── end-of-block case (DONE)
  │   └── length/distance case (DONE)
  │       └── copyLoop_eq_ofFn (DONE)
  ├── decodeDynamicTrees_correct (sorry — REMAINING WORK)
  └── inflateLoop_correct (DONE, in InflateCorrect.lean)
```

## Notes

- Toolchain v4.29.0-rc1 is current
- Sorry count unchanged at 2 (both decodeDynamicTrees_correct)
- All tests pass
