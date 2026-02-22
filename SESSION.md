# Session State

<!-- Overwritten at the end of each work session. -->
<!-- Records current working state for the next session to pick up. -->

## Sorry count: 2

In `Zip/Spec/InflateCorrect.lean`:
- `copyLoop_eq_ofFn` (line 282): copy loop ↔ List.ofFn correspondence
- `inflate_correct` (line 590): main correctness theorem

## Known good commit

`28b8ebb` — `lake build Zip` succeeds, no warnings except expected sorries.
(Note: test exe linker error on macOS with v4.29.0-rc1 is pre-existing.)

## What was accomplished this session

### decodeHuffman_correct: length/distance case COMPLETE

The third and final case of `decodeHuffman_correct` is now proved,
modulo the `copyLoop_eq_ofFn` helper. This means all three symbol
types (literal, end-of-block, length/distance) are handled.

Key work:
- Table correspondence lemmas: `lengthBase_eq`, `lengthExtra_eq`,
  `distBase_eq`, `distExtra_eq` — all proved by `decide` over `Fin`
- Helper lemmas: `lengthExtra_le_32`, `distExtra_le_32` (for readBits
  bounds), `spec_distBase_pos` (for distance > 0 guard)
- Full 8-operation monadic case splitting for the length/distance path
- `decodeLitLen` evaluation proof using `getElem?_pos`/`getElem!_pos`
- `resolveLZ77` guard condition proofs (dist > 0, dist ≤ output.length)
- Clean factoring: the copy loop is isolated in `copyLoop_eq_ofFn`

### Proof patterns discovered

- `getElem?_pos` needs explicit container argument (not `_`) to avoid
  type class synthesis failures
- `getElem?_pos` gives `c[i]? = some c[i]` while we need `c[i]!`;
  use `getElem!_pos` to bridge: `rw [getElem!_pos ...]; exact getElem?_pos ...`
- `spec_distBase_pos ⟨n, h⟩` creates `Fin.val ⟨n, h⟩` vs `n` mismatch
  in omega; fix with `have : ... := spec_distBase_pos ⟨n, h⟩` to normalize
- `(n == m) = false` for Nat: use `cases heq : n == m <;> simp_all [beq_iff_eq]`

## Next action

Priority for next session (implementation):

1. **Prove `copyLoop_eq_ofFn`**: The forIn copy loop produces the same
   result as `List.ofFn`. Key insight: all reads are within the original
   buffer range, so the growing buffer doesn't affect values. Provable
   by induction on the range length with a loop invariant.
2. **Loop correspondence**: Native `for` block loop ↔ spec fuel-based recursion
3. **Close `inflate_correct`**: Combine block + loop correspondence

## Architecture of remaining decomposition

```
inflate_correct (sorry)
  ├── decodeStored_correct (DONE)
  ├── decodeHuffman_correct (DONE, modulo copyLoop_eq_ofFn)
  │   ├── huffTree_decode_correct (DONE)
  │   ├── literal case (DONE)
  │   ├── end-of-block case (DONE)
  │   └── length/distance case (DONE)
  │       └── copyLoop_eq_ofFn (sorry — standalone lemma)
  └── loop correspondence (for → fuel)
```

## Notes

- Toolchain v4.29.0-rc1 is current (still latest)
- Sorry count: 2 (unchanged from previous session)
- Pre-existing linker error for test:exe on macOS with v4.29.0-rc1
