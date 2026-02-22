# Current Plan

<!-- Rewritten at the start of each work session. -->
<!-- If a session ends with unchecked items, the next session continues here. -->

## Status: In progress

## Session type: implementation

## Goal: Complete decodeHuffman_correct

### Steps

1. [x] Fix spec bug: pass `acc` to `resolveLZ77` for cross-block back-references
2. [x] State `decodeHuffman_correct`
3. [x] Prove literal case (sym < 256)
4. [x] Prove end-of-block case (sym == 256)
5. [ ] Prove length/distance case (sym > 256)
6. [ ] Work on inflate_correct loop correspondence

### Length/distance case blockers

The length/distance case needs:

1. **Make native tables accessible**: `lengthBase`, `lengthExtra`, `distBase`,
   `distExtra` are `private` in Inflate.lean. Change to `protected` so
   InflateCorrect.lean can reference them in proofs.

2. **Table correspondence lemmas**: Show that for valid indices:
   - `Zip.Native.Inflate.lengthBase[idx]!.toNat = Deflate.Spec.lengthBase[idx]!`
   - Same for `lengthExtra`, `distBase`, `distExtra`
   These might be provable by `decide` since the tables are finite constants.

3. **Copy loop ↔ List.ofFn**: The native `for i in [:length] do out := out.push
   out[start + (i % distance)]!` must equal the spec's `List.ofFn fun i =>
   acc[start + (i.val % dist)]!`. Key insight: all reads are within the
   original buffer range (`start + (i % distance) < output.size`), so the
   growing buffer doesn't affect read values.

4. **readBits ↔ readBitsLSB** for extra bits (already proven as `readBits_toBits`)

5. **distTree.decode ↔ Huffman.Spec.decode** for distance symbol (use
   `huffTree_decode_correct` with `distLengths`)

### Approach for length/distance case

After making tables `protected`, the proof follows the same pattern as the
literal case but with more intermediate steps:
1. Split `h` on each bounds check and monadic operation (~10 case splits)
2. Chain correspondence lemmas for each sub-operation
3. Show `decodeLitLen` returns `.reference length distance`
4. Show `resolveLZ77` on `.reference` produces the copy loop result
5. Apply IH for the recursive call

### Architecture of remaining decomposition

```
inflate_correct (sorry)
  ├── decodeStored_correct (DONE)
  ├── decodeHuffman_correct (2/3 cases DONE)
  │   ├── huffTree_decode_correct (DONE)
  │   ├── literal case (DONE)
  │   ├── end-of-block case (DONE)
  │   └── length/distance case (sorry — see blockers above)
  └── loop correspondence (for → fuel)
```

### UInt16 proof patterns discovered

- `sym < 256` (UInt16) proves `sym.toNat < 256` (Nat) via `exact hsym`
- `¬(sym < 256)` → `sym.toNat ≥ 256` via `Nat.le_of_not_lt hge`
- `sym.toNat = 256` → `sym = 256` via `UInt16.toNat_inj.mp (by simp; exact heq)`
- `sym.toUInt8 = sym.toNat.toUInt8` is `rfl` (UInt16.toUInt8 defined as `a.toNat.toUInt8`)
- `pure (...) = some (...)` for Option needs `simp only [..., pure]`
- `if (256 : Nat) < 256` reduces with `show ¬((256 : Nat) < 256) from by omega` + `↓reduceIte`
- `(256 : Nat) == 256 = true` is `rfl`
