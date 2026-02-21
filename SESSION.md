# Session State

<!-- Overwritten at the end of each work session. -->
<!-- Records current working state for the next session to pick up. -->

## Sorry count: 2

All in `Zip/Spec/InflateCorrect.lean`:
- `inflate_correct` (line 1262): main correctness theorem
- `inflate_correct'` (line 1274): corollary for position-0 inflate

## Known good commit

`c8201d0` — `lake build && lake exe test` passes

## Completed this session (implementation)

### Proved fromLengths_hasLeaf and fromLengths_leaf_spec

These are the two key theorems connecting the native HuffTree builder
(`fromLengths`) to the spec's code table (`allCodes`):

**fromLengths_hasLeaf** (forward): Every `(s, cw) ∈ allCodes` has a
corresponding `TreeHasLeaf tree cw s.toUInt16` in the built tree.

**fromLengths_leaf_spec** (backward): Every `TreeHasLeaf tree cw sym`
implies `(sym.toNat, cw) ∈ allCodes`.

### Key new theorems and lemmas

- **`insertLoop_forward`**: Main inductive invariant for the forward
  direction. Tracks NC (nextCode correspondence with spec), NoLeafOnPath
  (no collisions), and previous-symbol (already-inserted leaves) invariants.
  Proved all three cases: base, skip (length=0), insert (length>0).

- **`insertLoop_backward`**: Backward invariant using NC + `insert_go_complete'`.
  Every leaf in the result tree either pre-existed or was inserted for
  some symbol k with `start ≤ k < lengths.size` and `codeFor lsList 15 k = some cw`.

- **`insert_go_complete'`**: Like `insert_go_complete` but without the
  `NoLeafOnPath` requirement. Handles the `.leaf` case (where `insert.go`
  returns the tree unchanged) by returning `.inl h`.

- **`array_set_ne_u32`**, **`array_set_self_u32`**: Helper lemmas for
  `Array.set!` with UInt32 values.

- **`codeFor_some`**: Helper proving `codeFor lsList maxBits k` is `some`
  when `1 ≤ lsList[k] ≤ maxBits`.

### Design decisions

- **NC invariant**: Tracks `nextCode[b]!.toNat = ncSpec[b]! + partial_count`
  where `partial_count` is the count of symbols with length `b` in
  `lsList.take start`. This connects the mutable `nextCode` array to the
  spec's `nextCodes` function.

- **`hlen_bound : lengths.size ≤ UInt16.size`** added to `fromLengths_leaf_spec`,
  `decodeBits_eq_spec_decode`, and `huffTree_decode_correct`. Needed for
  `k.toUInt16.toNat = k` conversion. Always satisfied in DEFLATE (max 320
  entries vs 65536 limit).

- **`insert_go_complete'` without NoLeafOnPath**: The `.leaf` case in
  `insert.go` returns the tree unchanged (`.leaf s => .leaf s`), so any
  leaf in the result is pre-existing. This eliminates the need for the
  `hnlop` invariant in `insertLoop_backward`, simplifying the proof.

## Next action

Priority order for next implementation session:
1. Prove `inflate_correct'` from `inflate_correct` (straightforward corollary)
2. Make progress on `inflate_correct` — this is the top-level theorem
   connecting `inflateRaw` to `Deflate.Spec.decode`. Requires:
   - Block-level correspondence (stored, fixed, dynamic blocks)
   - Stream-level loop correspondence (multiple blocks → fuel)
   - LZ77 back-reference resolution correspondence

## Notes

- Toolchain v4.29.0-rc1 is current
- Sorry count 4 → 2
- `decodeBits_eq_spec_decode` and `huffTree_decode_correct` now have
  the extra `hlen_bound` parameter
