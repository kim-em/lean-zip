# Session State

<!-- Overwritten at the end of each work session. -->
<!-- Records current working state for the next session to pick up. -->

## Sorry count: 4

All in `Zip/Spec/InflateCorrect.lean`:
- `fromLengths_hasLeaf` (line 565): tree has leaf for every allCodes entry
- `fromLengths_leaf_spec` (line 576): every tree leaf is in allCodes
- `inflate_correct` (line 682): main correctness theorem
- `inflate_correct'` (line 694): corollary for position-0 inflate

## Known good commit

`153cb27` — `lake build && lake exe test` passes

## Completed this session (implementation)

### decodeBits_eq_spec_decode proved (+295 lines)

Decomposed the tree-table correspondence theorem into layers using
`TreeHasLeaf` inductive predicate:

**Layer 1: Structural correspondence (decodeBits ↔ TreeHasLeaf)**
- `TreeHasLeaf` predicate: tree has leaf with symbol at path
- `decodeBits_of_hasLeaf`: TreeHasLeaf → decodeBits works
- `hasLeaf_of_decodeBits`: decodeBits works → TreeHasLeaf exists

**Layer 2: insert creates correct tree structure**
- `uint32_testBit`: UInt32 bit extraction matches Nat.testBit
- `insert_bit_zero` / `insert_bit_one`: bridge to insert's comparison
- `NoLeafOnPath`: no leaf collision predicate
- `insert_go_hasLeaf`: insert.go places leaf at natToBits path
- `insert_go_preserves`: insert.go preserves existing non-prefix leaves

**Layer 3: Wiring**
- `decode_some_mem`: spec decode result → table membership
- `to_codes` / `to_table`: specTable ↔ specCodes membership
- Prefix-free property of specTable derived from allCodes_prefix_free_of_ne
- `decodeBits_eq_spec_decode` proved from all components

**Theorem signature changes:**
- Added `ValidLengths` precondition to `decodeBits_eq_spec_decode`
  and `huffTree_decode_correct` (required for prefix-freeness)

### Remaining sorry's (fromLengths loop analysis)

The two remaining sorry's (`fromLengths_hasLeaf`, `fromLengths_leaf_spec`)
require reasoning about the `for` loop in `fromLengths`:
- Track that `nextCode[len]!` at symbol `i` equals `nc[len] + offset_i`
- Show that `insert` calls create/only-create the right leaves
- May need a loop invariant relating mutable state to functional `codeFor`

## Next action

Priority order for next implementation session:
1. Prove `fromLengths_hasLeaf` — show the for loop builds correct leaves.
   Approach: define a functional version of the loop, prove equivalence
   with `fromLengths`, then show the functional version establishes
   `TreeHasLeaf` for each `codeFor` entry.
2. Prove `fromLengths_leaf_spec` — show all tree leaves are from allCodes.
3. Prove `inflate_correct'` from `inflate_correct` (straightforward)
4. Make progress on `inflate_correct` (the main theorem)

## Notes

- Toolchain v4.29.0-rc1 is current
- Sorry count increased 3 → 4 because `decodeBits_eq_spec_decode` was
  decomposed into two focused helper sorry's. The theorem itself is proved.
- `fromLengths_hasLeaf` needs `ValidLengths` to ensure no collisions
  during insertion (when a `.leaf` already exists at an intermediate
  position, `insert.go` skips the insertion)
- Key available lemmas for future `fromLengths` proofs:
  - `insert_go_hasLeaf`: insert places leaf at natToBits path
  - `insert_go_preserves`: insert preserves leaves at non-prefix paths
  - `nextCodes_eq_ncRec`: nextCodes array matches ncRec recurrence
  - `countLengths_eq`: countLengths matches counting foldl
  - `ncRec_bound`: ncRec b + blCount[b]! ≤ 2^b (Kraft)
