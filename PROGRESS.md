# lean-zip Progress

Global milestones — updated only on phase transitions and major events.
Per-session details are in `progress/`.

## Current State

- **Phase**: Phase 4 in progress (native compressor + roundtrip verification)
- **Toolchain**: leanprover/lean4:v4.29.0-rc2
- **Sorries**: 0 (zero-sorry milestone achieved Feb 24)
- **Sessions**: ~120 completed (Feb 19–24)

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
- Block-level decode correctness for all 3 block types (DecodeCorrect, DecodeComplete)
- Dynamic Huffman tree decode correctness (DynamicTreesCorrect)
- Stream-level inflate theorem (InflateCorrect)

Key theorems: `inflate_correct` (native decompressor agrees with formal
DEFLATE bitstream specification), `decodeStored_correct`,
`decodeHuffman_correct`, `decodeDynamicTrees_correct`.

### Phase 4: DEFLATE Compressor (in progress, started Feb 23)
Native compression + roundtrip verification. ~70 sessions so far.

**Completed:**
- Native Level 0 (stored), Level 1 (fixed Huffman), and Level 5 (dynamic
  Huffman) compressors, all conformance tests passing
- Native gzip/zlib compression wrappers (GzipEncode, ZlibEncode)
- BitWriter with formal correctness proofs (writeBits, writeHuffCode)
- Spec-level LZ77 greedy matcher with fundamental roundtrip theorem
  (`resolveLZ77_matchLZ77`)
- Spec-level lazy LZ77 matcher with Level 2 roundtrip
  (`deflateLevel2_spec_roundtrip`)
- Spec-level fixed Huffman encoder with Level 1 roundtrip
  (`deflateLevel1_spec_roundtrip`)
- Stored-block encode/decode roundtrip (`encodeStored_decode`)
- Native stored-block roundtrip (`inflate_deflateStoredPure`)
- Native LZ77 correctness: `lz77Greedy_valid`, `lz77Greedy_encodable`,
  `lz77Greedy_size_le`
- Native lazy LZ77 correctness: `lz77Lazy_valid`, `lz77Lazy_encodable`,
  `lz77Lazy_resolvable`
- Fuel independence for all spec decode functions
- Huffman code length computation with Kraft equality for binary trees
- Huffman symbol encoding functions with `encodeSymbols_decodeSymbols`
- Canonical codes correctness: `canonicalCodes_correct_pos`
- Dynamic tree header roundtrip: `encodeDynamicTrees_decodeDynamicTables`
- Native `emitTokens` ↔ spec `encodeSymbols` correspondence:
  `emitTokens_spec`, `emitTokensWithCodes_spec`
- `inflate_complete` (spec decode success → native inflate success)
- `readBits_complete` (BitReader completeness, spec → native direction)
- `readUInt16LE_complete`, `readBytes_complete` (BitstreamComplete)
- `deflateFixed_spec` (native fixed compressor ↔ spec encodeFixed)
- `huffTree_decode_complete`, `decode_go_complete` (DecodeComplete)
- `decodeHuffman_complete`, `decodeStored_complete` (DecodeComplete)
- `decodeCLSymbols_complete` (DynamicTreesComplete)
- Dynamic tree decode completeness chain (DynamicTreesComplete)
- `inflateLoop_complete` (InflateCorrect)
- `inflate_deflateFixed` — Level 1 roundtrip (DeflateFixedCorrect)
- `inflate_deflateLazy` — Level 2 roundtrip (DeflateFixedCorrect)
- `inflate_deflateDynamic` — Level 5 roundtrip (DeflateDynamicCorrect)
- `deflateRoundtrip` — unified roundtrip for all levels (DeflateRoundtrip)
- DecodeCorrect.lean split into DecodeCorrect + DecodeComplete

**Remaining sorries: 0**

All sorries have been resolved, including `deflateDynamic_spec` and
`inflate_deflateDynamic` (Level 5 roundtrip). The unified roundtrip
theorem `deflateRoundtrip` in `DeflateRoundtrip.lean` covers all
compression levels (stored, fixed, lazy, dynamic).

### Infrastructure
- Multi-agent coordination via `pod` with worktree-per-session isolation
- GitHub-based coordination (agent-plan issues, auto-merge PRs)
- Session dispatch: planners create issues, workers claim and execute
- ~120 sessions: majority implementation, ~30 review, ~3 self-improvement,
  remainder PR maintenance
