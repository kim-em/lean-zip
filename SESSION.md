# Session State

<!-- Overwritten at the end of each work session. -->
<!-- Records current working state for the next session to pick up. -->

## Sorry count: 2

## Incomplete proofs

- `Zip/Spec/Huffman.lean:222` — `code_value_bound`: code value assigned by
  canonical construction fits in `len` bits. This is the key helper for
  `codeFor_injective`. Requires proving `nc[b] + count[b] ≤ 2^b` from
  the nextCodes recurrence and Kraft inequality.
- `Zip/Spec/Huffman.lean:390` — `canonical_prefix_free` different-length case:
  when `len₁ < len₂`, the shorter code can't be a prefix of the longer one.
  Requires `nc[len₂] ≥ (nc[len₁] + count[len₁]) * 2^(len₂ - len₁)`.

Both require analyzing the `nextCodes.go` loop invariant.

## Structurally complete proofs

- `codeFor_injective` — fully structured, compiles with 0 errors. Depends on
  `code_value_bound` (sorry'd helper). Proof chain: codeFor_spec extracts
  components → natToBits_length shows lengths equal → natToBits_injective
  shows code values equal → offset_of_lt gives contradiction if s₁ ≠ s₂.
- `canonical_prefix_free` same-length case — proved. Different-length case sorry'd.

## Known good commit

`5b64cb2` — `lake build && lake exe test` passes

## Next action

The remaining sorry's all reduce to the same problem: proving an invariant
about `nextCodes.go`. The proof strategy:

1. Define `ncRec blCount b = (ncRec blCount (b-1) + blCount[b-1]!) * 2` (simple recursion)
2. Show `(nextCodes blCount maxBits)[b]! = ncRec blCount b`
3. Show `ncRec blCount b + blCount[b]! = ∑_{i=0}^{b} blCount[i]! * 2^(b-i)`
4. Multiply by `2^(maxBits-b)` to get partial Kraft sum ≤ 2^maxBits
5. Divide to get `ncRec blCount b + blCount[b]! ≤ 2^b`

For the different-length case of `canonical_prefix_free`, also need:
6. Show `ncRec blCount b ≥ (ncRec blCount a + blCount[a]!) * 2^(b-a)` for `a < b`

## Notes

- `natToBits` was rewritten from accumulator-based to simple recursion for
  easier inductive proofs
- `codeFor_spec` helper avoids fighting with `split at h` inside complex
  dite/ite nesting — extracts the three key facts in one lemma
- `offset_of_lt` needed `simp only [List.length_cons] at hs₁ hs₂` (not just
  `hs₁`) to give omega visibility into both bounds
- Toolchain v4.29.0-rc1 is current
