# Current Plan

<!-- Rewritten at the start of each work session. -->
<!-- If a session ends with unchecked items, the next session continues here. -->

## Status: In progress

## Session type: implementation

## Objective

Prove `nextCodes_plus_count_le` — the last sorry blocking `codeFor_injective`.

## Proof strategy for nextCodes_plus_count_le

The key insight: the recurrence `S(b) = 2*S(b-1) + blCount[b]` with
`S(b) = nc(b) + blCount[b]` telescopes when multiplied by `2^(maxBits-b)`:

```
S(b) * 2^(maxBits-b) + kraftTail(b+1) = S(b-1) * 2^(maxBits-b+1) + kraftTail(b)
```

So by induction: `S(b) * 2^(maxBits-b) + kraftTail(b+1) ≤ 2^maxBits`.

### Implementation steps

- [ ] Define `kraftTail blCount maxBits b` = remaining Kraft sum from b
- [ ] Prove telescoping: `S * 2^k + tail = prev_S * 2^(k+1) + prev_tail`
- [ ] Prove base case: `kraftTail 1 ≤ 2^maxBits` (connect to ValidLengths)
- [ ] Connect filter-based Kraft sum to blCount-based sum
- [ ] Prove `countLengths[b]!` = foldl count for valid b
- [ ] Prove `nextCodes[b]!` satisfies the recurrence
- [ ] Assemble `nextCodes_plus_count_le`
- [ ] Prove `canonical_prefix_free` different-length case (may need nc spacing)

## Failed approaches (for future reference)

- Simple induction on `S(b) ≤ 2^b` fails: IH too weak, doesn't leave room
  for blCount[b+1] in the step case
- `by_contra`, `push_neg`, `set` are Mathlib-only — use `by_cases`/`omega`
- `le_refl` not in scope — use `(by omega)` or `Nat.le.refl`
- `apply ih` with bullets: goal ordering is unpredictable — use `exact ih ... (by ...) ...`
