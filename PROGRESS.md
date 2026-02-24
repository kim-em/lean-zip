# lean-zip Progress

Global milestones — updated only on phase transitions and major events.
Per-session details are in `progress/`.

## Current State

- **Phase**: Phase 4 in progress (native compressor + roundtrip verification)
- **Toolchain**: leanprover/lean4:v4.29.0-rc1
- **Sorries**: 9 (in 3 compressor verification files)
- **Sessions**: 69 completed (Feb 19–24)

## Milestones

### Phase 1: Checksums (complete, Feb 19)
Native CRC32 and Adler32 with equivalence proofs against FFI implementations.
Proved in 2 sessions. Key technique: `bv_decide` for bitvector reasoning.

### Phase 2: DEFLATE Decompressor (complete, Feb 19)
Pure Lean DEFLATE inflate implementation (RFC 1951) with gzip/zlib wrappers.
Conformance tests pass against FFI zlib. Integrated as alternative backend
for ZIP and tar.gz extraction. Completed in 4 sessions.

### Phase 3: Verified Decompressor (complete, Feb 23)
Correctness proofs for the DEFLATE decompressor, completed over 25 sessions
(Feb 19–23). Zero sorries. The proof chain covers:
- BitReader ↔ bytesToBits correspondence (BitstreamCorrect)
- Canonical Huffman tree ↔ spec table correspondence (HuffmanCorrect)
- Block-level decode correctness for all 3 block types (DecodeCorrect)
- Dynamic Huffman tree decode correctness (DynamicTreesCorrect)
- Stream-level inflate theorem (InflateCorrect)

Key theorems: `inflate_correct` (native decompressor agrees with formal
DEFLATE bitstream specification), `decodeStored_correct`,
`decodeHuffman_correct`, `decodeDynamicTrees_correct`.

### Phase 4: DEFLATE Compressor (in progress, started Feb 23)
Native compression + roundtrip verification. ~36 sessions so far.

**Completed:**
- Native Level 0 (stored) and Level 1 (fixed Huffman) compressors, all
  conformance tests passing
- Native gzip/zlib compression wrappers (GzipEncode, ZlibEncode)
- BitWriter with formal correctness proofs (writeBits, writeHuffCode)
- Spec-level LZ77 greedy matcher with fundamental roundtrip theorem
  (`resolveLZ77_matchLZ77`)
- Spec-level lazy LZ77 matcher with Level 2 roundtrip
  (`deflateLevel2_spec_roundtrip`)
- Spec-level fixed Huffman encoder with Level 1 roundtrip
  (`deflateLevel1_spec_roundtrip`)
- Stored-block encode/decode roundtrip (`encodeStored_decode`)
- Native LZ77 correctness: `lz77Greedy_valid`, `lz77Greedy_encodable`,
  `lz77Greedy_size_le`
- Fuel independence for all spec decode functions
- Huffman code length computation with Kraft equality for binary trees
- Huffman symbol encoding functions with `encodeSymbols_decodeSymbols`

**Remaining sorries (9):**

`DeflateFixedCorrect.lean` (5):
- `emitTokens_spec` — native emitTokens ↔ spec encodeSymbols; blocked on
  `canonicalCodes ↔ allCodes` correspondence
- `deflateFixed_spec` — depends on emitTokens_spec
- `inflate_complete` — reverse direction (spec success → native success);
  identified as very hard
- `inflate_deflateFixed` — main native roundtrip, depends on above
- `inflate_deflateLazy` — lazy variant roundtrip, same proof strategy

`DeflateStoredCorrect.lean` (3):
- `fromLengths_fixedLit_ok` — Array.any is kernel-opaque
- `fromLengths_fixedDist_ok` — same issue
- `inflate_deflateStoredPure` — needs fromLengths proofs + multi-block
  induction

`DeflateEncodeDynamic.lean` (1):
- `encodeDynamicTrees_decodeDynamicTables` — dynamic tree header roundtrip

**Key remaining gap**: `canonicalCodes ↔ allCodes` correspondence is the
critical bridge between native and spec Huffman encoding. Both use the
same `countLengths`/`nextCodes` building blocks but different iteration
patterns.

### Infrastructure
- Multi-agent coordination via `pod` with worktree-per-session isolation
- GitHub-based coordination (agent-plan issues, auto-merge PRs)
- Session dispatch: planners create issues, workers claim and execute
- 69 sessions: ~40 implementation, ~22 review, ~1 self-improvement,
  ~6 PR maintenance
