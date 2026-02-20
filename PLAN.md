# Current Plan

<!-- Rewritten at the start of each work session. -->
<!-- If a session ends with unchecked items, the next session continues here. -->

## Status: In progress

## Session type: review

## Goal: Deep review of InflateCorrect.lean — TreeHasLeaf + insert proofs

Focus areas: **refactoring/proof improvement** and **Lean idioms**.

### Review targets

1. [x] Reorganize UInt32 bit lemmas into a contiguous section:
   - Move `shift_toUInt32_mod32`, `uint32_testBit`, `insert_bit_zero`,
     `insert_bit_one` together, before `uint32_bit_eq_testBit`
   - Simplify `uint32_bit_eq_testBit` to delegate to `uint32_testBit`
     (2 lines via `rwa` instead of 5-line direct proof)
   - Use `shift_toUInt32_mod32` in `uint32_testBit` instead of inline proof

2. [x] Simplify `decodeBits_of_hasLeaf`:
   - Replace 4-line structured induction with `induction h <;> simp_all [decodeBits]`

3. [ ] Scan `insert_go_hasLeaf` and `insert_go_preserves` for simplifications

4. [ ] Check `decode_go_decodeBits` for branch deduplication

5. [ ] Full slop/dead code scan of new TreeHasLeaf infrastructure

6. [ ] Toolchain check (v4.29.0-rc1 is latest, no upgrade needed)

### Unfinished plan items from last session

- `fromLengths_hasLeaf` — needs loop invariant (implementation work, deferred)
- `fromLengths_leaf_spec` — depends on above
- `inflate_correct` / `inflate_correct'` — main theorem (deferred)
