# Current Plan

<!-- Rewritten at the start of each work session. -->
<!-- If a session ends with unchecked items, the next session continues here. -->

## Status: In progress

## Session type: implementation

## Goal: Prove the two remaining sorry's in Huffman.lean

### Deliverables

- [ ] Define `ncRec` — simple recursive nextCodes recurrence
- [ ] Define `kraftSumFrom` — partial Kraft sum from position b
- [ ] Prove conservation law: `ncRec b * 2^(maxBits-b) + kraftSumFrom b = kraftSumFrom 0`
- [ ] Prove `kraftSumFrom_mono` (non-negative terms → monotone)
- [ ] Connect `kraftSumFrom 0` to ValidLengths Kraft inequality
- [ ] Prove `nextCodes.go` returns `ncRec` values (Array loop invariant)
- [ ] Prove `countLengths[b]! = foldl count` for valid b
- [ ] Assemble `nextCodes_plus_count_le`
- [ ] Prove `canonical_prefix_free` different-length case (if time)

### Proof strategy for nextCodes_plus_count_le

The bound `nc[b] + count[b] ≤ 2^b` follows from a conservation law:

```
ncRec b * 2^(maxBits-b) + kraftSumFrom b = kraftSumFrom 0
```

Where `kraftSumFrom b = ∑_{i=b}^{maxBits} blCount[i]! * 2^(maxBits-i)`.

Since all terms are non-negative:
- `(ncRec b + blCount[b]!) * 2^(maxBits-b) = ncRec b * 2^(maxBits-b) + blCount[b]! * 2^(maxBits-b)`
- `= kraftSumFrom 0 - kraftSumFrom b + blCount[b]! * 2^(maxBits-b)`
- `= kraftSumFrom 0 - kraftSumFrom (b+1)`
- `≤ kraftSumFrom 0`
- `≤ 2^maxBits` (Kraft inequality)

Then divide both sides by `2^(maxBits-b)`.

### Proof strategy for canonical_prefix_free (different lengths)

Need: `ncRec b ≥ (ncRec a + blCount[a]!) * 2^(b-a)` for `a < b`.
Then code₂ ≥ nc[len₂] ≥ (code₁ + 1) * 2^(len₂-len₁), contradicting prefix.
Plus a natToBits prefix → numerical range lemma.

## Failed approaches (for future reference)

- Simple induction on `S(b) ≤ 2^b` fails: IH too weak, doesn't leave room
  for blCount[b+1] in the step case
- `by_contra`, `push_neg`, `set` are Mathlib-only — use `by_cases`/`omega`
- `le_refl` not in scope — use `(by omega)` or `Nat.le.refl`
- `apply ih` with bullets: goal ordering is unpredictable — use `exact ih ... (by ...) ...`
