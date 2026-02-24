# lean-zip Progress

Global milestones — updated only on phase transitions and major events.
Per-session details are in `progress/`.

## Current State

- **Phase**: Phase 4 in progress (native compressor + roundtrip verification)
- **Toolchain**: leanprover/lean4:v4.29.0-rc2
- **Sorries**: 12 (in 4 verification files — see Phase 4 details)
- **Sessions**: ~90 completed (Feb 19–24)

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
Native compression + roundtrip verification. ~60 sessions so far.

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

**Remaining sorries (12):**

`BitstreamCorrect.lean` (3) — completeness direction (spec → native):
- `readBits_complete` — spec readBitsLSB → native readBits
- `readUInt16LE_complete` — spec readBitsLSB 16 → native readUInt16LE
- `readBytes_complete` — spec readNBytes → native readBytes

`DecodeCorrect.lean` (3) — completeness direction (spec → native):
- `decodeStored_complete` — spec decodeStored → native decodeStored
- `huffTree_decode_complete` — spec Huffman decode → native tree decode
- `decodeHuffman_complete` — spec decodeSymbols → native decodeHuffman.go

`InflateCorrect.lean` (2) — completeness direction (spec → native):
- `decodeDynamicTrees_complete` — spec decodeDynamicTables → native
- `inflateLoop_complete` — spec decode.go → native inflateLoop

`DeflateFixedCorrect.lean` (4) — compressor roundtrips:
- `deflateFixed_spec` — native fixed compressor ↔ spec encodeFixed
- `inflate_deflateFixed` — Level 1 roundtrip, depends on completeness lemmas
- `inflate_deflateLazy` — Level 2 roundtrip, same strategy
- `inflate_deflateDynamic` — Level 5 roundtrip, needs dynamic header + completeness

**Key remaining gap**: The 8 completeness sorries (BitstreamCorrect,
DecodeCorrect, InflateCorrect) form the reverse direction of existing
soundness proofs. Once these are proved, the 4 compressor roundtrip
theorems in DeflateFixedCorrect follow by composition.

### Infrastructure
- Multi-agent coordination via `pod` with worktree-per-session isolation
- GitHub-based coordination (agent-plan issues, auto-merge PRs)
- Session dispatch: planners create issues, workers claim and execute
- ~90 sessions: majority implementation, ~25 review, ~1 self-improvement,
  remainder PR maintenance
