# Session State

<!-- Overwritten at the end of each work session. -->
<!-- Records current working state for the next session to pick up. -->

## Sorry count: 3

All in `Zip/Spec/InflateCorrect.lean`:
- `decodeBits_eq_spec_decode` (line 357): tree-table correspondence
  (pure tree decode ≡ spec's linear-search decode)
- `inflate_correct` (line 409): main correctness theorem
- `inflate_correct'` (line 419): corollary for position-0 inflate

## Known good commit

`2a1af3f` — `lake build && lake exe test` passes

## Completed this session (implementation)

### Proved readBits_toBits (sorry 4 → 3)

Key new lemma: `Nat.or_two_pow_eq_add` in `ZipForStd/Nat.lean` —
when `a < 2^n`, bitwise OR with `2^n` equals addition (no overlapping
bits). Proof by induction on n using `Nat.eq_of_testBit_eq`.

Proof structure for readBits:
- `readBits_go_spec`: generalized loop invariant for `readBits.go`
  (induction on k, the number of bits remaining). Connects the native
  accumulator `acc ||| (bit <<< shift)` to the spec's `readBitsLSB`.
- `readBits_toBits`: derived from `readBits_go_spec` with acc=0, shift=0.

Helper lemmas:
- `shift_toUInt32_mod32`: shift < 32 → shift.toUInt32.toNat % 32 = shift
- `acc_or_shift_toNat`: OR accumulation = addition (using `or_two_pow_eq_add`)
- `acc_or_shift_bound`: accumulator stays < 2^(shift+1)

### Decomposed huffTree_decode_correct

Split into two steps:
1. `decode_go_decodeBits` (PROVED): BitReader-based tree decode
   corresponds to pure `decodeBits` on bit lists. By induction on
   tree structure, using `readBit_toBits` at each node.
2. `decodeBits_eq_spec_decode` (SORRY): pure tree decode agrees with
   spec's linear-search `Huffman.Spec.decode`. Requires connecting
   `fromLengths` (tree building) to `allCodes` (code generation).

The main `huffTree_decode_correct` is proved assuming (2).

## Next action

Priority order for next implementation session:
1. Prove `decodeBits_eq_spec_decode` — the tree-table correspondence.
   This requires showing that `fromLengths` builds a tree where each
   leaf's path matches its canonical codeword from `allCodes`.
   Approach: define a "tree contains codeword→symbol mapping" predicate,
   prove `insert` maintains it, prove `fromLengths` establishes it,
   then connect to `Huffman.Spec.decode`.
2. Prove `inflate_correct'` from `inflate_correct` (should be straightforward)
3. Make progress on `inflate_correct` (the main theorem)

## Notes

- Toolchain v4.29.0-rc1 is current
- `decodeBits_eq_spec_decode` is the hardest remaining sorry — it
  requires connecting the imperative `fromLengths` (with mutable arrays)
  to the functional `allCodes` (with `codeFor`). Both implement RFC 1951
  §3.2.2 canonical Huffman construction but in very different styles.
- Key available lemmas for future proofs:
  - `readBit_toBits`, `readBit_wf` (single bit correspondence)
  - `readBits_toBits` (multi-bit correspondence, n ≤ 32)
  - `decode_go_decodeBits` (tree decode BitReader→bits)
  - `Nat.or_two_pow_eq_add` (non-overlapping OR = ADD)
