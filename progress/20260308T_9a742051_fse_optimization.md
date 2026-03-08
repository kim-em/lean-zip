# Progress: Fse.lean deep quality pass — proof optimization and simp_all cleanup

- **Date**: 2026-03-08 UTC
- **Session**: review (9a742051)
- **Issue**: #909

## Accomplished

### Deliverable 1: Proof optimization pass (87 lines removed, 5.5%)
- `highBitPos_lt_eight`: 18→2 lines via `grind`
- `BackwardBitReader_init_{startPos,data}_eq`: 13/12→7 lines each
- `readBits_go_{data,startPos}_eq`: 14→10 lines each
- 8 "done never happens" loop handlers: 5-6→2 lines each using
  `split <;> (try split) <;> exact nomatch`
- `readBits_go_totalBitsRemaining{,_ge}`: compressed 6-line `by_cases`
  tails to 2 lines via chained `<;>` combinators
- `log2_le_of_lt_pow2_succ`: 15→8 lines
- `BackwardBitReader_init_totalBitsRemaining_lt`: compressed sentinelPos==0
  sub-cases (14→4 lines)

### Deliverable 2: Bare simp_all elimination (2 instances)
- `readBit_bitOff_lt'`: `simp_all` → `dsimp only []`
- `getD_set!`: `simp_all` → `grind` (after extensive testing of
  alternatives — `simp_all only [...]` blocked by hypothesis rewriting)

## Decisions
- Used `grind` instead of explicit `simp_all only [...]` for `getD_set!`
  because `simp_all` rewrites `¬P` hypotheses before `getElem?_neg` can
  fire. `grind` handles all 4 cases cleanly.
- `by_contra` not available without Mathlib; kept `if/else` pattern for
  `log2_le_of_lt_pow2_succ` but compressed.

## Quality metrics
- Sorry count: 4 (unchanged, all in XxHash.lean)
- Bare simp_all: 0 (was 2)
- Bare simp: 0 (unchanged)
- Line count: 1587→1500
- All tests pass
