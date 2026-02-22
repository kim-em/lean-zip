# Current Plan

<!-- Rewritten at the start of each work session. -->
<!-- If a session ends with unchecked items, the next session continues here. -->

## Status: In progress

## Session type: implementation (next)

## Goal: Complete decodeHuffman_correct length/distance case

### Steps

1. [x] Fix spec bug: pass `acc` to `resolveLZ77` for cross-block back-references
2. [x] State `decodeHuffman_correct`
3. [x] Prove literal case (sym < 256)
4. [x] Prove end-of-block case (sym == 256)
5. [x] Make native tables accessible (lengthBase, etc. now public)
6. [ ] Prove table correspondence lemmas
7. [ ] Prove copy loop ↔ List.ofFn
8. [ ] Complete length/distance case (sym > 256)
9. [ ] Work on inflate_correct loop correspondence

### Table correspondence lemmas needed

Now that native tables are public, prove:
- `Inflate.lengthBase[idx]!.toNat = Deflate.Spec.lengthBase[idx]!`
  for valid `idx < 29`
- Same for `lengthExtra`, `distBase`, `distExtra`

These should be provable by `decide` since the tables are finite constants.

### Copy loop ↔ List.ofFn

The native `for i in [:length] do out := out.push out[start + (i % distance)]!`
must equal the spec's `List.ofFn fun i => acc[start + (i.val % dist)]!`.

Key insight: all reads are within the original buffer range
(`start + (i % distance) < output.size`), so the growing buffer
doesn't affect read values.

### Architecture of remaining decomposition

```
inflate_correct (sorry)
  ├── decodeStored_correct (DONE)
  ├── decodeHuffman_correct (2/3 cases DONE)
  │   ├── huffTree_decode_correct (DONE)
  │   ├── literal case (DONE)
  │   ├── end-of-block case (DONE)
  │   └── length/distance case (sorry — steps 6-8 above)
  └── loop correspondence (for → fuel)
```

### Review improvements applied (from review session)

- `simp` → `simp only [Option.map]` in `huffTree_decode_correct` (line 107)
- Simplified literal case rewrite chain (combined two `rw` into one)
- Native DEFLATE tables made public for cross-file access
- Verified spec ↔ native correspondence (all tables, all block types)
- No dead code or slop found

### CLAUDE.md observation

`protected` doesn't work for definitions that need unqualified access
within the same namespace. Use public (no modifier) instead. The
CLAUDE.md guidance "protected not private" should note this caveat.
