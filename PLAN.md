# Current Plan

<!-- Rewritten at the start of each work session. -->
<!-- If a session ends with unchecked items, the next session continues here. -->

## Status: Complete

## Session type: review

## Goal: Deep review of BitstreamCorrect + file size scan

### Steps

1. [x] Deep review BitstreamCorrect.lean proofs (simplification opportunities)
2. [x] Simplify `flatMap_drop_mul` hypothesis (universal quantifier)
3. [x] Scan Huffman.lean (959 lines) for split/simplification
4. [x] Check for dead code across Spec files
5. [x] Check toolchain updates
6. [x] Verify build, commit, document

### Next session priorities

1. **Huffman block correspondence** (`decodeHuffman_correct`):
   - Symbol decode loop: iterate `huffTree_decode_correct` for lit/len/dist
   - LZ77 back-reference resolution: native copy loop ↔ spec `resolveLZ77`
   - Dynamic tree header parsing correspondence
2. **Loop correspondence**: native `for` block loop ↔ spec fuel-based recursion
3. **Close `inflate_correct`**: combine block + loop correspondence

### Architecture of remaining decomposition

```
inflate_correct (1 sorry remaining)
  ├── decodeStored_correct (DONE)
  ├── decodeHuffman_correct (NEXT — largest remaining piece)
  │   ├── huffTree_decode_correct (DONE)
  │   ├── symbol decode loop correspondence
  │   └── LZ77 resolve correspondence
  └── loop correspondence (for → fuel)
```

### Potential upstreaming candidates (ZipForStd)

- `UInt8.ofNat_toNat` (round-trip for UInt8)
- `ByteArray.data_extract` / `Array.toList_extract`
- `List.drop_eq_getElem_cons` variant
