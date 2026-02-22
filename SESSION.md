# Session State

<!-- Overwritten at the end of each work session. -->
<!-- Records current working state for the next session to pick up. -->

## Sorry count: 2

In `Zip/Spec/InflateCorrect.lean`:
- `decodeHuffman_correct` (line 342): length/distance case
- `inflate_correct` (line 368): main correctness theorem

## Known good commit

`f6541c7` — `lake build Zip` succeeds, no warnings except expected sorries.
(Note: test exe linker error on macOS with v4.29.0-rc1 is pre-existing.)

## Completed this session (implementation)

### Spec bug fix
- Removed `DecodedBlock` and `decodeBlock` from Deflate.lean
- Inlined block dispatch into `decode.go`, passing `acc` to `resolveLZ77`
- This correctly models RFC 1951's cross-block sliding window
- Committed as `19ae92e`

### decodeHuffman_correct — 2 of 3 cases proved
- **Literal case** (sym < 256): decodeLitLen → .literal, resolveLZ77_literal, IH
- **End-of-block case** (sym == 256): decodeLitLen → .endOfBlock, decodeSymbols with fuel 1
- **Length/distance case**: sorry — see PLAN.md for detailed blockers

### Helper lemmas added
- `decode_wf`: HuffTree.decode preserves bitOff < 8
- `readBits_go_wf`, `readBits_wf`: readBits preserves bitOff < 8
- Changed `decodeHuffman` from `private` to `protected` for cross-file access

### UInt16 proof patterns discovered
- `sym < 256` (UInt16 lt) directly proves `sym.toNat < 256` via `exact hsym`
- `¬(sym < 256)` → `sym.toNat ≥ 256` via `Nat.le_of_not_lt`
- `sym.toUInt8 = sym.toNat.toUInt8` is `rfl` (UInt16.toUInt8 = fun a => a.toNat.toUInt8)
- UInt16 is now BitVec-based (not Fin-based) in v4.29.0-rc1

## Next action

Priority for next session:

1. **Make native tables protected**: Change `lengthBase`, `lengthExtra`,
   `distBase`, `distExtra` from `private` to `protected` in Inflate.lean
2. **Prove table correspondence**: Native UInt16 arrays ↔ spec Nat lists
3. **Prove copy loop ↔ List.ofFn**: Factor out as a standalone lemma
4. **Complete length/distance case**: Chain all correspondence lemmas
5. **Loop correspondence**: Native `for` block loop ↔ spec fuel-based recursion
6. **Close `inflate_correct`**: Combine block + loop correspondence

## Architecture of remaining decomposition

```
inflate_correct (sorry)
  ├── decodeStored_correct (DONE)
  ├── decodeHuffman_correct (2/3 cases DONE)
  │   ├── huffTree_decode_correct (DONE)
  │   ├── literal case (DONE)
  │   ├── end-of-block case (DONE)
  │   └── length/distance case (sorry)
  └── loop correspondence (for → fuel)
```

## Notes

- Toolchain v4.29.0-rc1 is current
- Sorry count: 2 (up from 1, but decodeHuffman_correct is a new theorem
  decomposing inflate_correct — the extra sorry represents progress)
- Pre-existing linker error for test:exe on macOS with v4.29.0-rc1
