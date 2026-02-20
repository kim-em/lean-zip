# Current Plan

<!-- Rewritten at the start of each work session. -->
<!-- If a session ends with unchecked items, the next session continues here. -->

## Status: In progress

## Session type: implementation

## Goal: Prove `decodeBits_eq_spec_decode` — tree-table correspondence

The theorem says: for a tree built by `fromLengths`, the pure tree decode
`decodeBits` agrees with the spec's linear-search `Huffman.Spec.decode`.

### Proof strategy

Decompose via an inductive predicate `TreeHasLeaf`:

```
inductive TreeHasLeaf : HuffTree → List Bool → UInt16 → Prop
  | leaf : TreeHasLeaf (.leaf s) [] s
  | left : TreeHasLeaf z cw s → TreeHasLeaf (.node z o) (false :: cw) s
  | right : TreeHasLeaf o cw s → TreeHasLeaf (.node z o) (true :: cw) s
```

#### Layer 1: Structural correspondence (decodeBits ↔ TreeHasLeaf)

- [x] `decodeBits_of_hasLeaf`: TreeHasLeaf tree cw sym → decodeBits tree (cw ++ rest) = some (sym, rest)
- [x] `hasLeaf_of_decodeBits`: decodeBits tree bits = some (sym, rest) → ∃ cw, TreeHasLeaf tree cw sym ∧ bits = cw ++ rest

#### Layer 2: insert creates the right tree structure

- [ ] `insertBits` definition + `insertBits_eq_natToBits` bridge
- [ ] `insert_go_hasLeaf`: insert.go creates a leaf at `insertBits code len`
- [ ] `insert_go_preserves`: insert.go preserves existing leaves at different paths

#### Layer 3: fromLengths loop → TreeHasLeaf for all canonical codes

- [ ] fromLengths loop invariant: tree has leaves for all inserted symbols
- [ ] Connect nextCode tracking to codeFor's offset computation

#### Layer 4: Wire up final theorem

- [ ] Forward: decodeBits some → decode specTable some (via TreeHasLeaf + decode_prefix_free)
- [ ] Backward: decode specTable some → decodeBits some (via fromLengths_hasLeaf)
- [ ] None case: decodeBits none ↔ decode specTable none

### Notes

- Layer 1 is clean structural induction
- Layer 2 requires handling the `.leaf` collision case (precondition: no collision)
- Layer 3 is the hardest part — connecting imperative `nextCode` to functional `codeFor`
- `insertBits code len` and `natToBits code.toNat len` differ only in UInt32 vs Nat
  operations; bridge lemma needed
