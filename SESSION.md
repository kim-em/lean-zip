# Session State

<!-- Overwritten at the end of each work session. -->
<!-- Records current working state for the next session to pick up. -->

## Sorry count: 1

In `Zip/Spec/InflateCorrect.lean`:
- `inflate_correct` (line 209): main correctness theorem

## Known good commit

`350666b` — `lake build Zip` succeeds, no warnings except expected sorry.
(Note: test exe linker error on macOS with v4.29.0-rc1 is pre-existing,
Lean compilation succeeds.)

## Completed this session (implementation)

### Proved `inflate_correct'` from `inflate_correct`
Straightforward corollary: unfold `inflate`, case-split on `inflateRaw`,
apply `inflate_correct` with `startPos = 0`. Committed as `f80b5b8`.

### Bitstream correspondence lemmas (BitstreamCorrect.lean)
- `readBitsLSB_testBit`, `readBitsLSB_byteToBits`, `readBitsLSB_split`
- `alignToByte_toBits` — native `alignToByte` ↔ spec `Deflate.Spec.alignToByte`
- `readUInt16LE_toBits` — native LE 16-bit read ↔ spec `readBitsLSB 16`
- `readNBytes_aligned` — inductive core for byte-level reading
- `readBytes_toBits` — native `readBytes` ↔ spec `readNBytes`
- Helper lemmas: `readUInt16LE_wf`, `readUInt16LE_data`, `readBytes_wf`,
  `alignToByte_id_of_aligned`

### Proved `decodeStored_correct` (InflateCorrect.lean)
Full stored-block correspondence: native `Inflate.decodeStored` ↔ spec
`Deflate.Spec.decodeStored`. Chains `readUInt16LE_toBits` (×2) and
`readBytes_toBits`, with XOR complement check and byte-alignment invariants.

### Visibility change
- `private` → `protected` for `Inflate.decodeStored` (cross-file access)

## Next action

Priority order for next implementation session:
1. **Huffman block correspondence** — `decodeHuffman_correct`:
   - Symbol decode loop: iterate `huffTree_decode_correct` for lit/len/dist
   - LZ77 back-reference resolution: native copy loop ↔ spec `resolveLZ77`
   - Dynamic tree header parsing correspondence
2. **Loop correspondence** — native `for` block loop ↔ spec fuel-based recursion
3. **Close `inflate_correct`** — combine block + loop correspondence

## Architecture of remaining decomposition

```
inflate_correct (sorry)
  ├── decodeStored_correct (DONE)
  ├── decodeHuffman_correct (NEXT)
  │   ├── huffTree_decode_correct (DONE)
  │   ├── symbol decode loop correspondence
  │   └── LZ77 resolve correspondence
  └── loop correspondence (for → fuel)
```

## Notes

- Toolchain v4.29.0-rc1 is current
- Sorry count decreased from 2 → 1 (proved inflate_correct')
- Pre-existing linker error for test:exe on macOS with v4.29.0-rc1
  (zstd -Bstatic/-Bdynamic flags not recognized by lld on macOS)
