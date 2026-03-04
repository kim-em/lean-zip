# lean-zip Progress

Global milestones — updated only on phase transitions and major events.
Per-session details are in `progress/`.

## Current State

- **Phase**: Phase 4+ complete; Track C2 complete; Track E (Zstd) progressing rapidly
- **Toolchain**: leanprover/lean4:v4.29.0-rc2
- **Sorries**: 0
- **Sessions**: ~275 completed (Feb 19 – Mar 4)
- **Source files**: 90 (43 spec, 11 native impl, 9 FFI/archive, 4 ZipForStd, 23 test)
- **Merged PRs**: 238
- **Bare simp**: 0 remaining — campaign complete (43 spec files, ZipForStd/, Native/ all clean)

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
    (hsize : data.size < 1024 * 1024 * 1024) :
    Inflate.inflate (deflateRaw data level) = .ok data
```
Covers all compression levels (stored, fixed, lazy, dynamic). The 1 GiB
size bound is now the native inflate's default `maxOutputSize` (a runtime
zip-bomb guard), not a fuel/termination limitation — all recursive functions
use well-founded recursion (Track C2 complete).

**Proof quality reviews** (80+ sessions): systematic code review across
spec files, reducing proof size, extracting reusable lemmas to ZipForStd,
splitting large files for maintainability, and converting bare `simp` to
`simp only`. Reviews to date: Deflate (#369), DecodeComplete (#374, #442, #517),
BitReaderInvariant (#382), HuffmanCorrect + HuffmanCorrectLoop (#385),
InflateCorrect (#387), InflateRawSuffix (#391, #484), DeflateFixedCorrect (#404),
LZ77 (#408), InflateLoopBounds (#413), DeflateDynamicFreqs (#414),
DynamicTreesComplete (#440), DynamicTreesCorrect (#441),
DeflateEncode (#448, #457), BitstreamCorrect (#459),
HuffmanEncode (#467), EmitTokensCorrect (#470), DeflateEncodeProps (#485),
BitWriterCorrect (#488, #505), DeflateStoredCorrect (#498),
BitstreamWriteCorrect (#500), DeflateDynamicCorrect (#507),
InflateComplete (#513), DeflateDynamicEmit (#514),
HuffmanTheorems (#518), BinaryCorrect + LZ77Lazy + DeflateRoundtrip (#528),
DeflateSuffix (#531), ZipForStd/ (#539), Adler32 + DeflateDynamicCorrect +
DeflateStoredCorrect (#543), 5 small-count files (#545),
GzipCorrect + HuffmanKraft + ZlibCorrect (#547).

**Bare simp status**: 0 standalone bare simps remaining across all 43 spec files
(100% clean). The campaign reduced standalone bare simps from ~129 to 0
(100% reduction) over ~30 review PRs. ZipForStd/ and Native/ are also fully
clean. Campaign completed Mar 4, 2026.

### Phase 4+: Gzip/Zlib Framing Roundtrip (complete, Feb 24–26)

Extends the core DEFLATE roundtrip to full gzip (RFC 1952) and zlib
(RFC 1950) framing, proving that the encode/decode wrappers are
inverses.

**Capstone theorems** (zero sorries):
```lean
-- GzipCorrect.lean
theorem gzip_decompressSingle_compress (data : ByteArray) (level : UInt8)
    (hsize : data.size < 1024 * 1024 * 1024) :
    GzipDecode.decompressSingle (GzipEncode.compress data level) = .ok data

-- ZlibCorrect.lean
theorem zlib_decompressSingle_compress (data : ByteArray) (level : UInt8)
    (hsize : data.size < 1024 * 1024 * 1024) :
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
- BitReader invariant infrastructure: 14 `_inv` lemmas tracking
  `data`, `hpos`, and `pos ≤ data.size` through all BitReader operations
  (all proved — split across BitReaderInvariant.lean + InflateLoopBounds.lean)
- `inflateLoop_endPos_le`: endPos ≤ data.size after inflate loop
- `inflateRaw_endPos_eq`: exact endPos calculation for trailer parsing
- Encoder padding decomposition (`deflateRaw_pad`) and `remaining.length < 8`
  via `decode.goR` (decode with remaining) variant
- Suffix invariance chain: `decodeCLSymbols_append`,
  `decodeDynamicTrees_append`, `decodeHuffman_go_append`
- CRC32 and ISIZE trailer byte matching (gzip)
- Adler32 trailer byte matching (zlib)

**Architecture:** The original monolithic `GzipCorrect.lean` (1949 lines) was
split into 4 focused modules: `BitReaderInvariant.lean` (522 lines),
`InflateLoopBounds.lean` (614 lines), `InflateRawSuffix.lean` (501 lines),
and `GzipCorrect.lean` (286 lines).

### Track C1: Size Bound Improvement (complete, Feb 25–26)
Raised the size bound on all roundtrip theorems from 500MB to 1 GiB.
PR #305 raised fuel limits throughout the spec decode functions.
The per-path bounds:
- Stored: 655MB
- Fixed Huffman (greedy): 1GiB
- Lazy LZ77 (levels 2–4): 500MB (most restrictive at previous bound)
- Dynamic Huffman: 500MB

The unified bound is now 1 GiB (`1024 * 1024 * 1024`), up from 500MB
previously and 5MB at the start of Track C1.

### Track C2: Fuel Elimination (complete, Mar 2)
Replaced all fuel-based recursion with well-founded recursion, eliminating
the data size bound as a proof artifact. The 1 GiB bound in the capstone
theorem is now solely the native inflate's `maxOutputSize` zip-bomb guard.

**All 6 fuel-using functions converted to WF:**
- Spec `decodeCLSymbols` → WF (#328): `termination_by totalCodes - acc.length`
- Native `decodeCLSymbols` → WF (#332): same termination measure
- Spec `decodeSymbols` → WF (#337): `termination_by` on remaining bits
- Native `decodeHuffman.go` → WF (#341): `termination_by dataSize * 8 - br.bitPos`
- Spec `decode.go`/`decode.goR` → WF (#344): required deleting DeflateFuelIndep.lean
  (fuel independence became moot once spec functions are WF) and updating 11
  downstream proof files
- Native `inflateLoop` → WF (#397): `termination_by dataSize * 8 - br.bitPos`

**Key proofs repaired during and after WF conversions:**
- `inflateLoop_correct` (#358): native→spec block loop correspondence
- `decodeDynamicTrees_complete` (#361): composed from sub-completeness theorems
- `inflateLoop_complete` (#373): spec→native block loop, strong induction
- Proof repairs across 6 PRs (#345, #350, #351, #356, #357, #362)

**Sorry count trajectory:** 0 → ~15 (during conversions) → 0 (all repaired).

**New skill:** `lean-wf-recursion` (#349) capturing WF function unfolding rules,
`f.induct` functional induction patterns, and fuel-to-WF migration checklist.

### Track D: Benchmarking (in progress, Feb 25 – Mar 2)
Benchmark infrastructure comparing native Lean compression/decompression
vs FFI (zlib) across all levels (0–9) with various data patterns (constant,
cyclic, random, text) at sizes 1KB–1MB.

**Large-input fixes:**
- `lz77GreedyIter` — tail-recursive LZ77 greedy matcher with proved
  equivalence (`lz77GreedyIter_eq_lz77Greedy`), replacing the stack-
  overflowing `lz77Greedy_mainLoop` for level 5+ (#372)
- `lz77LazyIter` — tail-recursive LZ77 lazy matcher with proved
  equivalence (`lz77LazyIter_eq_lz77Lazy`), enabling levels 2–4 at
  large input sizes (#380)
- All compression levels now work at 256KB+ inputs

**Benchmark infrastructure** (NativeScale.lean, NativeCompressBench.lean):
- Decompression benchmarks added (#379): inflate, gzip decompress, zlib
  decompress — native vs FFI across all patterns and sizes
- Text corpus pattern added (#390): realistic text data alongside
  constant, cyclic, and random patterns
- Compression size cap removed (#390): all levels run at all sizes
  (was previously split into small/large tiers with restricted levels)
- All-level compression ratios (#399): native vs FFI output sizes for
  levels 0–9 across all 4 data patterns
- MB/s throughput calculations (#399) added to all benchmark sections

### Track E: Zstd Native Decompressor (in progress, Mar 2–4)
Native Lean Zstd implementation, following the same methodology as DEFLATE
(B-track). The core decompression infrastructure is now largely in place;
the remaining work is wiring these components together for compressed block
decompression and adding multi-frame support.

**Frame and block layer:**
- Frame header parser (#398): magic number, frame header descriptor bit fields,
  optional window descriptor, dictionary ID, frame content size — per
  RFC 8878 §3.1.1. `ZstdFrameHeader` structure with `parseFrameHeader`.
- Block header parsing and raw/RLE decompression (#405): 3-byte block
  headers (Last_Block, Block_Type, Block_Size), verbatim copy for raw blocks,
  single-byte repeat for RLE blocks, `decompressFrame` loop over blocks.
- XXH64 checksum verification (#432): pure Lean xxHash64 implementation wired
  into frame decompressor for content checksum validation.
- Compressed block header parsing (#439): `parseLiteralsSection` (4 literal
  block types × 3 size formats) and `parseSequencesHeader` (sequence count
  + compression mode bytes for literals/offsets/match lengths).

**FSE (Finite State Entropy) infrastructure (`Zip/Native/Fse.lean`, ~359 lines):**
- Distribution decoder (#429): `decodeFseDistribution` reads compact probability
  distributions from the bitstream, producing normalized symbol counts.
- Table construction (#429): `buildFseTable` builds the FSE decoding table
  (1 << accuracyLog cells) using RFC 8878 §4.1.1 position-stepping algorithm.
- Backward bitstream reader (#452): `BackwardBitReader` for Zstd's MSB-first
  backward bitstream format (RFC 8878 §4.1), with `init`, `readBits`,
  `isFinished`.
- Symbol decoding (#452): `decodeFseSymbols` decodes sequences of symbols
  from FSE state machine lookups.
- `decodeFseSymbolsAll` (#479): variant that loops until `BackwardBitReader.isFinished`
  (for variable-length outputs like Huffman weight sequences).

**Sequence execution (`ZstdFrame.lean`):**
- Sequence execution engine (#447): `ZstdSequence` structure, `resolveOffset`
  with repeat offset codes 1–3 (RFC 8878 §3.1.2.3), `copyMatch` with overlap
  semantics, `executeSequences` for reconstructing output from literal/match
  interleaving.

**Huffman tree descriptors (#458, #479):**
- Direct representation parsing (#458): `parseHuffmanWeightsDirect` reads raw 4-bit
  weight nibbles, `weightsToMaxBits` computes max bit depth from weight
  distribution, `buildZstdHuffmanTable` constructs lookup table from weights.
- FSE-compressed representation (#479): `parseHuffmanWeightsFse` decodes weight
  sequences via FSE tables, the common case in real-world Zstd files at default
  compression levels.
- `parseHuffmanTreeDescriptor` dispatches between direct and FSE-compressed
  weight representations.

**Sequence infrastructure (#466):**
- Extra bits tables (`litLenExtraBits`, `matchLenExtraBits`, `litLenBaseValues`,
  `matchLenBaseValues`) implementing RFC 8878 §3.1.1.3.2.1 tables.
- Compression mode parsing: `parseCompressionMode` decodes 2-bit mode fields
  (predefined, RLE, FSE-compressed, repeat) for sequence header entries.

**Multi-frame support (#490):**
- `decompressMultiFrame`: loops over concatenated frames (RFC 8878 §3.1),
  accumulating decompressed output.
- `decompressSkippableFrame`: identifies and skips skippable frames
  (magic 0x184D2A50–0x184D2A5F).
- `decompressZstd`: top-level entry point handling both standard and
  skippable frames.

**Tests:** 25+ tests in `ZipTest/ZstdNative.lean` covering header parsing,
RLE/raw blocks, FSE distribution decoding, table construction, backward
bitstream reading, sequence execution, Huffman weight parsing, compression
mode parsing, multi-frame support, and checksum verification.

**Huffman-compressed literals (#508, merged):**
- `decodeHuffmanSymbol`, `decodeHuffmanStream`, `decodeFourHuffmanStreams` for
  flat table lookup with `BackwardBitReader`
- Handles litType 2 (Huffman-compressed) in `parseLiteralsSection` per
  RFC 8878 §3.1.1.3.1

**FSE table resolution (#548, merged):**
- `buildRleFseTable`: constructs single-symbol FSE table for RLE mode
- `resolveSingleFseTable`: dispatches on compression mode (predefined,
  RLE, FSE-compressed, repeat) to produce an FSE decoding table
- `resolveSequenceFseTables`: resolves all three sequence tables
  (literal length, offset, match length) from compression modes
- This was the critical connector between compression mode parsing
  and sequence decoding — completing issue #473

**Remaining:**
- Treeless literals (litType 3) — issue #554
- Consolidate parseSequencesHeader and wire modes into decompressBlocks
  — issue #520 (claimed)
- Wire compressed block sequence decoding end-to-end — issue #552
  (blocked on #520)
- Block size and window size validation — issue #540 (has PR #549
  with merge conflict)
- Spec-level decoder with correctness proofs
- Compressor + roundtrip proof

Track E has crossed a significant threshold: the individual building blocks
for compressed block decompression are all implemented — FSE tables, backward
bitstreams, sequence execution, Huffman descriptors (both direct and FSE-
compressed), Huffman-compressed literal streams, extra bits tables,
compression mode parsing, FSE table resolution, and multi-frame support. The
remaining implementation work is primarily integration: connecting these
components into the `decompressBlocks` pipeline for `ZstdBlockType.compressed`.

**PR queue health improvement:** The previous summary flagged 5 open PRs all
with merge conflicts. PR #535 rebased 3 of them (#489, #512, #515), which
were subsequently closed (superseded by merged work). The queue is now down
to 2 open PRs (#555 chore, #549 with merge conflict), a significant
improvement.

### Infrastructure
- Multi-agent coordination via `pod` with worktree-per-session isolation
- GitHub-based coordination (agent-plan issues, auto-merge PRs)
- Session dispatch: planners create issues, workers claim and execute
- ~275 sessions: majority implementation, ~130 review, ~9 self-improvement,
  remainder PR maintenance, planning, and summarization
- 238 merged PRs (Feb 19 – Mar 4)
- 100% module docstring coverage across all source files
- Full linter compliance (all warnings eliminated)
- Agent skills: `lean-wf-recursion` (#349), `proof-review-checklist` (#386),
  bare-simp-resistant pattern catalog (#386), `lean-zstd-patterns` (#491),
  `agent-pr-recovery` (#546)
- **Open PR health**: 2 open PRs (down from 5 at last summary), 1 with merge
  conflict (#549). Stale PRs cleaned up via #535 and #555.
