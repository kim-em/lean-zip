# Current Plan

<!-- Rewritten at the start of each work session. -->
<!-- If a session ends with unchecked items, the next session continues here. -->

## Status: Complete

## Session type: implementation

## Goal: Prove inflate_correct' + decompose inflate_correct

### Steps

1. [x] Prove `inflate_correct'` from `inflate_correct` (corollary: startPos=0)
2. [x] Add `readUInt16LE_toBits` correspondence lemma (BitstreamCorrect)
3. [x] Add `readBytes_toBits` correspondence lemma (BitstreamCorrect)
4. [x] Add `alignToByte_toBits` correspondence lemma (BitstreamCorrect)
5. [x] State `decodeStored_correct` — stored block correspondence
6. [x] Prove `decodeStored_correct` using bitstream lemmas
7. [x] Build and test

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
