# Current Plan

## Status: In progress

## Session type: review

## Goal: Split InflateCorrect.lean + proof improvements

### Focus areas
1. **File size**: InflateCorrect.lean at 1050 lines (over 1000 limit)
2. **Refactoring and proof improvement**: deduplication
3. **Lean idioms / toolchain check**

### Steps

1. [ ] Split InflateCorrect.lean: extract block-level correctness proofs
   into `Zip/Spec/DecodeCorrect.lean` (~700 lines)
   - `decodeBits_eq_spec_decode`, `huffTree_decode_correct`
   - All invariant preservation lemmas (`decode_wf`, `readBit_pos_inv`, etc.)
   - Table correspondence lemmas
   - LZ77 copy loop helpers
   - `decodeStored_correct`
   - `decodeHuffman_correct`
   Remaining InflateCorrect.lean (~350 lines):
   - `decodeStored_wf`, `decodeStored_pos_inv`
   - Fixed code correspondence
   - `decodeDynamicTrees_correct` (sorry)
   - `inflateLoop_correct`
   - `inflate_correct`, `inflate_correct'`

2. [ ] Combine `decodeStored_wf` + `decodeStored_pos_inv` into single
   theorem (identical structure, ~25 lines saved)

3. [ ] Extract `bfinal` helper lemmas for the 3x repeated patterns
   in `inflateLoop_correct`

4. [ ] Scan for other improvements (bare simp, idioms, dead code)

5. [ ] Toolchain check

6. [ ] Build + test
