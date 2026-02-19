# Session State

<!-- Overwritten at the end of each work session. -->
<!-- Records current working state for the next session to pick up. -->

## Sorry count: 2

## Incomplete proofs

- `Zip/Spec/Huffman.lean:230` — `nextCodes_plus_count_le`: For valid lengths,
  `nextCodes[b]! + foldl_count_b ≤ 2^b`. This is the Kraft-based invariant
  of the canonical code construction.
- `Zip/Spec/Huffman.lean:419` — `canonical_prefix_free` different-length case:
  when `len₁ < len₂`, the shorter code can't be a prefix of the longer one.

Both reduce to analyzing the `nextCodes.go` loop.

## Structurally complete proofs

- `code_value_bound` — proved using `nextCodes_plus_count_le` (sorry'd) +
  `offset_of_lt` (proved) + omega
- `codeFor_injective` — proved using `code_value_bound`, `codeFor_spec`,
  `natToBits_injective`, `offset_of_lt`
- `canonical_prefix_free` same-length case — proved using `codeFor_injective`

## Known good commit

`7947885` — `lake build && lake exe test` passes

## Next action

Prove `nextCodes_plus_count_le`. Proof plan:

1. Define `ncSimple blCount b = (ncSimple blCount (b-1) + blCount[b-1]!) * 2`
   (simple structural recursion matching `nextCodes.go`)
2. Define `kraftTail blCount maxBits b = ∑_{i=b}^{maxBits} blCount[i]! * 2^(maxBits-i)`
3. Prove invariant by induction:
   `(ncSimple b + blCount[b]!) * 2^(maxBits-b) + kraftTail(b+1) ≤ 2^maxBits`
   - Base (b=0): reduces to `kraftTail(1) ≤ 2^maxBits` (Kraft inequality)
   - Step: `(ncSimple(b+1) + blCount[b+1]!) * 2^(maxBits-b-1) + kraftTail(b+2)`
     = `(ncSimple(b) + blCount[b]!) * 2^(maxBits-b) + kraftTail(b+1)` ≤ 2^maxBits (by IH)
4. Conclude: `ncSimple b + blCount[b]! ≤ 2^b`
5. Show `nextCodes[b]! = ncSimple b` for `1 ≤ b ≤ maxBits`
6. Relate foldl count to `countLengths[b]!` (countLengths_eq_foldl_count)

The step in (3) is an equality, making it clean. The tricky parts are:
- (5) analyzing `nextCodes.go` (Array operations, termination)
- (6) relating `countLengths` Array foldl to scalar foldl
- Connecting the blCount-based Kraft sum to the ValidLengths filter-based sum

Alternative: prove `nextCodes.go` invariant directly (same math, avoids ncSimple).

For `canonical_prefix_free` different-length case, additionally need:
- `ncSimple b ≥ (ncSimple a + blCount[a]!) * 2^(b-a)` for `a < b`
  (follows from the recurrence by induction)

## Notes

- `by_contra` and `push_neg` are NOT available without Mathlib
- `set` tactic is NOT available without Mathlib — use `let` or work inline
- `le_refl` is not in scope — use `(by omega)` or `Nat.le.refl`
- Toolchain v4.29.0-rc1 is current
