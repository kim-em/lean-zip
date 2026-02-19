# Current Plan

<!-- Rewritten at the start of each work session. -->
<!-- If a session ends with unchecked items, the next session continues here. -->

## Status: Complete

## Session type: implementation

## Objective

Two deliverables for this session:

1. **Adler32 bounds proofs** — prove that `updateByte` and `updateList`
   preserve the invariant that both state components are < MOD_ADLER.

2. **Begin Phase 3: DEFLATE spec formalization** — create Huffman code
   specification and DEFLATE bitstream specification.

## Checklist

- [x] Adler32 bounds: `updateByte_fst_lt` — first component < MOD_ADLER
- [x] Adler32 bounds: `updateByte_snd_lt` — second component < MOD_ADLER
- [x] Adler32 bounds: `updateList_valid` — both components < MOD_ADLER for
      any input starting from a valid state
- [x] Adler32 bounds: `init_valid` — initial state satisfies the invariant
- [x] Adler32 bounds: `updateBytes_valid` — lifted to native ByteArray impl
- [x] Build and test after Adler32 proofs
- [x] Huffman spec: codeword type, canonical construction from code lengths
- [x] Huffman spec: `isPrefixOf`, `decode`, prefix-free property
- [x] Huffman spec: `ValidLengths` predicate, theorem statements
- [x] DEFLATE spec: bitstream conversion (`bytesToBits`, `readBitsLSB`)
- [x] DEFLATE spec: LZ77 symbol type and resolution
- [x] DEFLATE spec: all three block types (stored, fixed, dynamic)
- [x] DEFLATE spec: stream-level decode function
- [x] Fix issues from Codex review (alignment, error handling, overshoot)
- [x] Build and test after DEFLATE spec

## Remaining sorry locations

- `Zip/Spec/Huffman.lean:145` — `codeFor_injective`
- `Zip/Spec/Huffman.lean:155` — `canonical_prefix_free`

These are the core Huffman theory proofs, requiring reasoning about the
canonical code assignment. Both now have proper `ValidLengths` preconditions.
