# Current Plan

<!-- Rewritten at the start of each work session. -->
<!-- If a session ends with unchecked items, the next session continues here. -->

## Status: Complete

## Session type: implementation

## Goal: Prove `fromLengths_hasLeaf` and `fromLengths_leaf_spec`

All steps completed. Sorry count reduced from 4 to 2.

### Steps

1. [x] Add `HuffTree.insertLoop` to `Inflate.lean` (recursive model of loop 3)
2. [x] Refactor `fromLengths` to call `insertLoop` instead of `for` loop
3. [x] Build and test to verify refactoring is correct
4. [x] Prove `insert_go_noLeafOnPath`: inserting preserves `NoLeafOnPath`
5. [x] Prove `insert_go_complete`: every leaf in `insert.go` output is
   either from the original tree or at the inserted path
6. [x] Prove `insertLoop_forward` with NC + NoLeafOnPath + previous-symbol invariants
7. [x] Prove `insert_go_complete'` (without NoLeafOnPath requirement)
8. [x] Prove `insertLoop_backward` with NC invariant
9. [x] Derive `fromLengths_hasLeaf` from `insertLoop_forward`
10. [x] Derive `fromLengths_leaf_spec` from `insertLoop_backward`

### Remaining sorry's

- `inflate_correct` — main stream correctness (requires block-level + LZ77 + loop)
- `inflate_correct'` — corollary (trivial from `inflate_correct`)
