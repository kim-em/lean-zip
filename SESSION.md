# Session State

<!-- Overwritten at the end of each work session. -->
<!-- Records current working state for the next session to pick up. -->

## Sorry count: 1

In `Zip/Spec/InflateCorrect.lean`:
- `inflate_correct` (line 636): main correctness theorem

## Known good commit

`17076a0` — `lake build Zip` succeeds, no warnings except expected sorry.
(Note: test exe linker error on macOS with v4.29.0-rc1 is pre-existing.)

## What was accomplished this session

### copyLoop_spec: PROVED

Replaced the `for i in [:length]` loop in `decodeHuffman.go` with an
explicit recursive `copyLoop` function. The `forIn` on `Range` uses
`Std.Legacy.Range.forIn'` whose inner `loop✝` cannot be unfolded by
name, making proofs intractable. The explicit recursion is straightforward
to reason about by well-founded induction on `length - k`.

Key theorems proved:
- `ba_getElem!_eq_toList`: bridge between ByteArray and List getElem!
- `push_getElem_lt`: push preserves earlier elements
- `push_data_toList`: push appends to toList
- `copyLoop_spec`: generalized loop invariant — the copy loop produces
  `output ++ List.ofFn (fun i => output[start + i%distance]!)`
- `copyLoop_eq_ofFn`: specialization for the LZ77 case (start = size - distance)

### decodeHuffman_correct: FULLY COMPLETE

With `copyLoop_spec` proved, `decodeHuffman_correct` has no remaining
sorries. All three symbol types are handled: literal, end-of-block,
length/distance (with copy loop correspondence).

## Next action

Priority for next session (implementation):

1. **Prove `inflate_correct`**: The main theorem connecting the native
   block-level loop to the spec's fuel-based recursion. Needs:
   - Loop correspondence: native `for` block loop ↔ spec fuel-based decode
   - Block type dispatch: stored/dynamic Huffman cases already proved
   - Final block flag handling

## Architecture of remaining decomposition

```
inflate_correct (sorry)
  ├── decodeStored_correct (DONE)
  ├── decodeHuffman_correct (DONE)
  │   ├── huffTree_decode_correct (DONE)
  │   ├── literal case (DONE)
  │   ├── end-of-block case (DONE)
  │   └── length/distance case (DONE)
  │       └── copyLoop_eq_ofFn (DONE)
  └── loop correspondence (for → fuel) — REMAINING WORK
```

## Notes

- Toolchain v4.29.0-rc1 is current (still latest)
- Sorry count: 2 → 1 (proved copyLoop_spec)
- Pre-existing linker error for test:exe on macOS with v4.29.0-rc1
