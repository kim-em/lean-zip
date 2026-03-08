# Review: DeflateFixedTables.lean quality pass

- **Date**: 2026-03-08 UTC
- **Session**: ee34402e (review)
- **Issue**: #953

## Accomplished

1. **Converted 2 `simp_all` instances** to explicit `obtain rfl := Nat.le_zero.mp hjk; exact Nat.le_refl _`
   in `specLengthBase_monotone` and `specDistBase_monotone` zero cases.

2. **Proof optimization pass** on all 25 theorems:
   - Combined `hsize_eq` + `hsize` into single proof step (both `fixedLitCodes_agree`
     and `fixedDistCodes_agree`) — eliminated intermediate hypothesis
   - Inlined `hmap_len` into `List.getElem_of_eq` call site
   - Combined `hlen'_nat` with anonymous `have` and final `omega` into single closing step
   - Removed duplicate `↓reduceIte` entries in 3 `simp only` calls in
     `findTableCode_go_of_first_match`
   - Removed redundant comments that duplicated obvious proof structure

3. **Line count**: 357 → 347 (10 lines, ~3% reduction)

## Verification

- `lake build` — no errors
- `lake exe test` — all tests pass
- Sorry count: 4 (unchanged, all XxHash)
- Zero `simp_all`, zero `native_decide`
- All theorem statements unchanged

## Decisions

- Did not extract shared helper for `fixedLitCodes_agree`/`fixedDistCodes_agree`:
  the two theorems are nearly identical but parameterized over different tables.
  Extracting a helper would require abstracting over 5+ parameters with little
  reuse benefit for just 2 call sites.
- Similarly for `encodeSymbol_litTable_eq`/`encodeSymbol_distTable_eq` — the
  `hmem'` sub-proof pattern repeats but is only 4 lines; abstracting it would
  add complexity without clear benefit.
