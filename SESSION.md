# Session State

<!-- Overwritten at the end of each work session. -->
<!-- Records current working state for the next session to pick up. -->

## Sorry count: 1

In `Zip/Spec/InflateCorrect.lean`:
- `inflate_correct` (line 209): main correctness theorem

## Known good commit

`fc91055` — `lake build Zip` succeeds, no warnings except expected sorry.
(Note: test exe linker error on macOS with v4.29.0-rc1 is pre-existing,
Lean compilation succeeds.)

## Completed this session (review)

### BitstreamCorrect.lean deep review
- Proofs are clean, near-minimal
- `simp only []` in `readBitsLSB_split` confirmed structurally needed
  (normalizes goal for `congr 1`; `omega` can't handle `2^k` without it)
- Simplified `flatMap_drop_mul`: universal quantifier replaces membership-
  restricted hypothesis, eliminating membership threading (-3 lines)

### Huffman.lean size scan
- 959 lines — approaching 1000 limit but file is near-stable
- Split deferred (definitions vs Kraft machinery is natural boundary)

### HuffmanCorrect.lean NC invariant
- ~35 lines duplicated between insertLoop_forward/backward
- Extraction evaluated: ~17 parameters needed, not worth complexity

### Dead code / toolchain checks
- No unused private/protected definitions found
- v4.29.0-rc1 is latest toolchain (stable v4.29.0 not yet released)

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
- Sorry count: 1 (stable since last session)
- Pre-existing linker error for test:exe on macOS with v4.29.0-rc1
  (zstd -Bstatic/-Bdynamic flags not recognized by lld on macOS)
