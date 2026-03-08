# Review: complete simp_all campaign — Fse.lean + HuffmanEncode.lean + HuffmanCorrect.lean

**Date**: 2026-03-08 UTC
**Session type**: review
**Issue**: #990

## Accomplished

Eliminated all remaining `simp_all` and bare `simp` instances across the final
three files in the codebase-wide simp_all campaign:

1. **Fse.lean line 346**: bare `simp [Nat.shiftLeft_eq]` → `simp only [Nat.shiftLeft_eq, Nat.one_mul]`
2. **Fse.lean line 800**: `simp_all only [beq_iff_eq, Nat.add_eq_zero_iff]` → explicit
   case split with `assumption` (true case) and `absurd h.1 hne` (false case, derives
   contradiction from `bitsRemaining + 8*(bytePos-startPos) = 0` vs `¬(bitsRemaining = 0)`)
3. **HuffmanEncode.lean line 498**: `constructor <;> (intro h; obtain h|h|h := h <;> simp_all only [true_or, or_true])`
   → `simp only [or_left_comm]` (the goal was just disjunction rearrangement)
4. **HuffmanCorrect.lean line 124**: `simp_all only [decodeBits, ...]` →
   `simp only [...] <;> assumption` (leaf case closed by simp, left/right closed by IH via assumption)

## Decisions

- `tauto` is a Mathlib tactic, unavailable in this project. Used `simp only [or_left_comm]`
  instead for disjunction rearrangement.
- HuffmanCorrect's `simp_all` was documented as "genuinely needed" but actually
  `simp only + assumption` works fine since the induction hypothesis is an exact match.
- Proof optimization pass: all three files already well-optimized. No significant
  `rw` combination or pattern extraction opportunities found.

## Quality metrics

- Sorry count: 4 → 4 (unchanged, all XxHash UInt64)
- simp_all in these files: 3 → 0
- bare simp in these files: 1 → 0
- All tests pass (48/48 conformance)
- Pre-existing SIGSEGV in Zip.Spec.ZstdHuffman build (toolchain bug, unrelated)
