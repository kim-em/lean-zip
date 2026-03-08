# Review: HuffmanEncodeCorrect.lean quality pass

**Date**: 2026-03-08 UTC
**Session**: f891c5e7 (review)
**Issue**: #938

## Accomplished

1. **Converted 3 `simp_all` instances** to explicit alternatives:
   - `canonicalCodes_go_size`: replaced `simp_all` after `setIfInBounds` split
     with `rw [Array.size_set!]` — eliminated the entire `setIfInBounds`
     unfolding pattern (4 lines → 1 line)
   - `canonicalCodes_go_inv` hresSize/hncSize: same pattern, replaced 8 lines
     of `setIfInBounds` + `split` + `simp_all` with 2 one-liners using
     `Array.size_set!`

2. **Converted 5 bare `simp` calls** to `simp only`:
   - 4 `simp [hlsList/lsList, hi]` → `simp only [hlsList/lsList, List.length_map, Array.length_toList, hi]`
   - 1 `simp [show k < lengths.size from hks]` → `simp only [Array.size_replicate, ..., getElem!_pos, Array.getElem_replicate]`

3. **Minor proof optimization**:
   - Simplified `if_neg` pattern in NC invariant zero-length case: removed
     redundant `beq_iff_eq, Bool.false_eq_true, ↓reduceIte` from simp only

## Key patterns discovered

- `Array.size_set!` is the right replacement for `setIfInBounds` unfolding +
  `split` + `simp_all` patterns when proving size preservation after `set!`.
  This is already documented in the proof-review-checklist skill.
- `beq_iff_eq` rewrites ALL `==` occurrences including inside `foldl` lambdas,
  which breaks goals that depend on the `(l == b) = true` form. Must use
  targeted `have` instead of `simp only [beq_iff_eq]` in these contexts.

## Metrics

- simp_all: 3 → 0
- bare simp: 5 → 0
- Lines: 303 → 296
- Sorry count: 4 (unchanged, all XxHash)
