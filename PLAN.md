# Current Plan

<!-- Rewritten at the start of each work session. -->
<!-- If a session ends with unchecked items, the next session continues here. -->

## Status: Completed

## Session type: review

## Goal: Deep review of recent proofs (InflateCorrect.lean, ZipForStd/Nat.lean)

### Steps

- [x] Deep review InflateCorrect.lean proofs — simplified decode_go_decodeBits branches, used UInt32.toNat_one
- [x] Review ZipForStd/Nat.lean — replaced induction with Nat.two_pow_add_eq_or_of_lt
- [x] Quick idioms scan across Spec/ files — no opportunities found
- [x] Build + test — passes
- [x] /second-opinion on changes — no issues
- [x] Document in PROGRESS.md and SESSION.md

### Next session priorities

1. **Prove `decodeBits_eq_spec_decode`** — show that the pure tree decode
   agrees with the spec's linear-search decode. Approach:
   - Define "tree maps codeword to symbol" predicate
   - Prove `insert` maintains it
   - Prove `fromLengths` establishes it for all canonical codes
   - Connect to `Huffman.Spec.decode`'s linear search
2. Prove `inflate_correct'` from `inflate_correct`
3. Work on `inflate_correct` (the main theorem)
