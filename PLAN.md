# Current Plan

<!-- Rewritten at the start of each work session. -->
<!-- If a session ends with unchecked items, the next session continues here. -->

## Status: Complete

## Session type: implementation

## Goal: Prove the two remaining sorry's in Huffman.lean — DONE

### Deliverables

- [x] Define `ncRec` — simple recursive nextCodes recurrence
- [x] Define `kraftSumFrom` — partial Kraft sum from position b
- [x] Prove conservation law: `ncRec b * 2^(maxBits-b) + kraftSumFrom b = kraftSumFrom 0`
- [x] Prove `kraftSumFrom_mono` (non-negative terms → monotone)
- [x] Connect `kraftSumFrom 0` to ValidLengths Kraft inequality
- [x] Prove `nextCodes.go` returns `ncRec` values (Array loop invariant)
- [x] Prove `countLengths[b]! = foldl count` for valid b
- [x] Assemble `nextCodes_plus_count_le`
- [x] Prove `canonical_prefix_free` different-length case

### Additional lemmas proved (for canonical_prefix_free)

- [x] `natToBits_append` — split natToBits across high/low bits
- [x] `natToBits_prefix_lt` — prefix → numerical upper bound
- [x] `ncRec_shift` — ncRec scales monotonically across bit lengths
- [x] `foldl_count_init` — init-shift for counting foldl

## Failed approaches (for future reference)

- Simple induction on `S(b) ≤ 2^b` fails: IH too weak, doesn't leave room
  for blCount[b+1] in the step case
- `by_contra`, `push_neg`, `set` are Mathlib-only — use `by_cases`/`omega`
- `le_refl` not in scope — use `(by omega)` or `Nat.le.refl`
- `apply ih` with bullets: goal ordering is unpredictable — use `exact ih ... (by ...) ...`
- `_` type placeholders in `have h : _ + _ + 1 ≤ ...` fail — Lean can't synthesize
  code values from context. Solution: rewrite hypotheses to use named abbreviations
  first (`rw [hnc₁, hnc₂] at hupper`), then state inequalities in terms of those.
- `simp only [heqf]` for converting `if ... then acc + 1 else acc` to `acc + if ...`
  inside foldl causes max recursion depth — use dedicated `foldl_count_init` instead.
