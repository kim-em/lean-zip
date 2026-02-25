# lean-zip Progress

Global milestones — updated only on phase transitions and major events.
Per-session details are in `progress/`.

## Current State

- **Phase**: Phase 4+ (gzip/zlib framing roundtrip proofs in progress)
- **Toolchain**: leanprover/lean4:v4.29.0-rc2
- **Sorries**: 10 (8 in GzipCorrect.lean, 2 in ZlibCorrect.lean)
- **Sessions**: ~148 completed (Feb 19–25)
- **Source files**: 81 (41 spec, 14 native impl, 26 test/support)
- **Merged PRs**: 113

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
- Fuel independence of spec decode (DeflateFuelIndep)
- `fromLengths` success implies `ValidLengths` (DynamicTreesCorrect)

**Characterizing properties** (mathematical content independent of implementation):
- Huffman codes are prefix-free and canonical (Huffman.Spec)
- Kraft inequality bounds symbol counts (HuffmanKraft)
- Prefix-free codes decode deterministically (`decode_prefix_free`)
- Bitstream operations correspond to LSB-first bit lists
- LZ77 overlap semantics: `copyLoop_eq_ofFn`
- RFC 1951 tables verified by `decide`

**Algorithmic correspondence** (native implementation agrees with spec decoder):
- `inflate_correct`: native inflateRaw → spec decode succeeds with same result
- `inflate_complete`: spec decode succeeds → native inflateRaw succeeds with same result
- Both directions proved for stored, fixed Huffman, and dynamic Huffman blocks

### Phase 4: DEFLATE Compressor + Roundtrip (complete, Feb 23–24)
Native compression + roundtrip verification. ~80 sessions. Zero sorries
for the core DEFLATE roundtrip.

**Compressor infrastructure:**
- Native Level 0 (stored), Level 1 (fixed Huffman), and Level 5 (dynamic
  Huffman) compressors, all conformance tests passing
- Native gzip/zlib compression wrappers (GzipEncode, ZlibEncode)
- BitWriter with formal correctness proofs (writeBits, writeHuffCode)

**LZ77 layer (BB1):**
- Spec-level LZ77 greedy matcher with fundamental roundtrip theorem
  (`resolveLZ77_matchLZ77`)
- Spec-level lazy LZ77 matcher with Level 2 roundtrip
  (`deflateLevel2_spec_roundtrip`)
- Native LZ77 correctness: `lz77Greedy_valid`, `lz77Greedy_encodable`,
  `lz77Greedy_size_le`
- Native lazy LZ77 correctness: `lz77Lazy_valid`, `lz77Lazy_encodable`,
  `lz77Lazy_resolvable`

**Huffman layer (BB2):**
- Huffman symbol encoding functions with `encodeSymbols_decodeSymbols`
- Canonical codes correctness: `canonicalCodes_correct_pos`
- Huffman code length computation with Kraft equality for binary trees

**Bitstream layer (BB3):**
- BitWriter correctness (BitstreamWriteCorrect)
- `readBits_complete` (BitReader completeness, spec → native direction)
- `readUInt16LE_complete`, `readBytes_complete` (BitstreamComplete)

**Block framing layer (BB4):**
- Stored-block encode/decode roundtrip (`encodeStored_decode`)
- Dynamic tree header roundtrip: `encodeDynamicTrees_decodeDynamicTables`
- `writeDynamicHeader_spec` — BitWriter chain for dynamic header
- Native `emitTokens` ↔ spec `encodeSymbols` correspondence:
  `emitTokens_spec`, `emitTokensWithCodes_spec`

**Per-level roundtrips:**
- `inflate_deflateStoredPure` — Level 0 (stored blocks)
- `inflate_deflateFixed` — Level 1 (fixed Huffman)
- `inflate_deflateLazy` — Levels 2–4 (lazy LZ77)
- `inflate_deflateDynamic` — Level 5+ (dynamic Huffman)

**Capstone theorem** (DeflateRoundtrip.lean):
```lean
theorem inflate_deflateRaw (data : ByteArray) (level : UInt8)
    (hsize : data.size < 5000000) :
    Inflate.inflate (deflateRaw data level) = .ok data
```
Covers all compression levels (stored, fixed, lazy, dynamic). The 5MB
size bound arises from the lazy LZ77 path (levels 2–4); it propagates
from array indexing bounds in the hash table implementation.

**Note on scope**: This theorem proves the raw DEFLATE roundtrip.
It does not cover gzip/zlib framing (header parsing, checksum
verification) — that is Phase 4+ below.

**Proof quality reviews** (35+ sessions): systematic code review across
all spec files, reducing proof size, extracting reusable lemmas to
ZipForStd, splitting large files for maintainability.

### Phase 4+: Gzip/Zlib Framing Roundtrip (in progress)

Extends the core DEFLATE roundtrip to full gzip (RFC 1952) and zlib
(RFC 1950) framing, proving that the encode/decode wrappers are
inverses.

**Target theorems:**
```lean
-- GzipCorrect.lean
theorem gzip_decompressSingle_compress (data : ByteArray) (level : UInt8)
    (hsize : data.size < 5000000) :
    GzipDecode.decompressSingle (GzipEncode.compress data level) = .ok data

-- ZlibCorrect.lean
theorem zlib_decompressSingle_compress (data : ByteArray) (level : UInt8)
    (hsize : data.size < 5000000) :
    ZlibDecode.decompressSingle (ZlibEncode.compress data level) = .ok data
```

**What's proved:**
- Pure proof-friendly decoders: `GzipDecode.decompressSingle`,
  `ZlibDecode.decompressSingle` (no loops/mut)
- Format lemmas: gzip header bytes, zlib CMF/FLG/CINFO/FDICT fields
- `compress_size` (total output size = header + deflated + trailer)
- Binary LE/BE read/write roundtrip proofs (BinaryCorrect.lean)
- `inflateRaw_complete`: if spec decode succeeds at arbitrary offset,
  native inflateRaw succeeds with same result
- Suffix invariance: `decode_go_suffix` (spec decode ignores trailing bits)
- Zlib proof structurally complete (all steps present, 2 sorry gaps)
- BitReader invariant infrastructure: 14 `_inv` lemmas tracking
  `data`, `hpos`, and `pos ≤ data.size` through all BitReader operations
  (6 fully proved: readBit, readBits, readBits.go, HuffTree.decode,
  HuffTree.decode.go, readCLCodeLengths; 4 sorry: decodeStored,
  decodeHuffman.go, decodeCLSymbols, decodeDynamicTrees)

**What's sorry (10 total):**

All 10 sorries are blocked on the same infrastructure problem —
`inflateLoop_endPos_le`, which proves that after decompression the
returned `endPos ≤ data.size`.

| Sorry | File | What it proves | Why it's needed |
|-------|------|---------------|-----------------|
| `decodeStored_inv` | GzipCorrect | BitReader invariant for stored blocks | Feeds inflateLoop_endPos_le |
| `decodeHuffman_go_inv` | GzipCorrect | BitReader invariant for Huffman decode loop | Feeds inflateLoop_endPos_le |
| `decodeCLSymbols_inv` | GzipCorrect | BitReader invariant for CL symbol decode | Feeds decodeDynamicTrees_inv |
| `decodeDynamicTrees_inv` | GzipCorrect | BitReader invariant for dynamic tree decode | Feeds inflateLoop_endPos_le |
| `inflateLoop_endPos_le` body | GzipCorrect | endPos ≤ data.size after inflate loop | Needed for trailer parsing bounds |
| `inflateRaw_endPos_le` guard | GzipCorrect | startPos ≤ data.size | Precondition for inflateLoop_endPos_le |
| `gzip_decompressSingle_compress` | GzipCorrect | Top-level gzip roundtrip | Blocked on inflateLoop_endPos_le |
| `hendPos_tight` | ZlibCorrect | endPos + 4 ≤ compressed.size | Blocked on inflateLoop_endPos_le |
| `hadler` | ZlibCorrect | Adler32 trailer matches at endPos | Blocked on knowing exact endPos value |

**Dependency chain:**
1. Fill 4 remaining `_inv` lemmas (decodeStored, decodeHuffman.go,
   decodeCLSymbols, decodeDynamicTrees) — mechanical but verbose
2. Complete `inflateLoop_endPos_le` using the invariant chain
3. Derive `inflateRaw_endPos_le` (trivial corollary)
4. Fill gzip roundtrip (endPos bound enables trailer parsing)
5. Fill zlib roundtrip (same endPos infrastructure)

### Infrastructure
- Multi-agent coordination via `pod` with worktree-per-session isolation
- GitHub-based coordination (agent-plan issues, auto-merge PRs)
- Session dispatch: planners create issues, workers claim and execute
- ~148 sessions: majority implementation, ~35 review, ~3 self-improvement,
  remainder PR maintenance and planning
- 113 merged PRs (Feb 19–25)
