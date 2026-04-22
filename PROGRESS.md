# lean-zip Progress

Global milestones — updated only on phase transitions and major events.
Per-session details are in `progress/`.

## Current State

- **Phase**: Phase 4+ complete; Track C1 complete; Track C2 complete;
  proven-bounds campaign complete (0 runtime `]!` across `Zip/Native/`
  and `Zip/`); Track E (security audit) in progress — P0 + P1 + P2
  closed, all of P3 closed (P3.1 / P3.2 / P3.4 in prior batches;
  P3.3 fuzz harness landed as #1602 in this batch), P4 closed, P5.1
  proof-friendly helpers landed as #1608 in this batch (P5.2 filed
  mid-batch as #1628; P5.3 tracked as #1614 and in flight as PR #1626
  at batch close). `SECURITY_INVENTORY.md` *Recommended policy* block:
  Rec. 1 / 3 / 5 executed in this batch (#1623 / #1618 / #1617);
  Rec. 2 structurally set up by #1610 (parameter added; default still
  `0`, issue #1625 tracks the flip); Rec. 4 tracked as #1621
- **Toolchain**: leanprover/lean4:v4.29.1
- **Sorries**: 0
- **Sessions**: ~660 completed (Feb 19 – Apr 22)
- **Source files in-repo**: `Zip/Spec/` 42, `Zip/Native/` 7,
  `Zip/` (FFI/archive/tar/gzip/basic/checksum) 6, `ZipTest/` 24
- **Merged PRs**: ~653 (approximate; authoritative count via `gh pr list`)
- **Spec lines**: 20,606 across 42 spec files (DEFLATE-only, post-split)
- **Bare simp**: 0 standalone bare `simp` remaining across all spec files
- **Bare simp_all**: 0 across all spec files (campaign complete)
- **Zstd**: Moved to https://github.com/kim-em/lean-zstd (#1487, 2026-03-27)
- **Shared utilities**: Moved to https://github.com/kim-em/lean-zip-common
  (#1487, 2026-03-27); pulled in via `require zipCommon from git`
- **Proven-bounds**: 0 runtime `]!` across `Zip/Native/` and `Zip/`;
  only 2 comment-only occurrences remain in `Zip/Native/Deflate.lean`
- **Track E audit checklist**:
  [`plans/track-e-current-audit-checklist.md`](plans/track-e-current-audit-checklist.md)
  is the source of truth for "what is done vs. what remains"; the
  human-readable trust-boundary catalogue is
  [`SECURITY_INVENTORY.md`](SECURITY_INVENTORY.md)
- **Track E *Recommended policy* block**: fully Executed (items 1–6, post-#1710 on 2026-04-22); *Missing work* reads "Residual gaps: none currently open at this layer"
- **Checksum characterizing-property ladders**: Adler-32 closed end-to-end (last rung `_combine` in #1698); CRC32 closed at the concrete-shape terminus `_pair` (#1701); `_replicate*` / `_combine` for CRC32 require GF(2)[x] algebra (out of scope)

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

**Bare simp status**: 0 standalone bare simps remaining across all 44 spec files
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

### Track C1: Size Bound Improvement (complete, Feb 25 – Mar 6)
Eliminated the hard-coded size bound from all roundtrip theorems. The
capstone theorem is now fully parametric in `maxOutputSize`:

```lean
theorem inflate_deflateRaw (data : ByteArray) (level : UInt8)
    (maxOutputSize : Nat) (hsize : data.size < maxOutputSize) :
    Zip.Native.Inflate.inflate (deflateRaw data level) maxOutputSize = .ok data
```

This was achieved progressively:
- #305: raised fuel limits from 5MB to 500MB–1GiB
- #654: generalized stored block roundtrip to parametric `maxOutputSize`
- #656: generalized levels 1–4 and dynamic roundtrips, plus the capstone

The `maxOutputSize` parameter is now a caller-chosen zip-bomb guard, not
a proof limitation. Combined with Track C2 (fuel elimination), the DEFLATE
roundtrip theorem has no artificial restrictions.

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

### Track E: Zstd Native Decompressor (in progress, Mar 2–6)
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

**Treeless literals (#566, merged):**
- litType 3 (treeless) support in `parseLiteralsSection`: reuses the
  Huffman tree from a previous block via `prevHuffTree` parameter
- Huffman tree state threaded through the `decompressBlocks` loop

**Cross-block state (#572, merged):**
- `executeSequences` now accepts `windowPrefix` (prior blocks' output)
  and `offsetHistory` (repeat offset state across blocks)
- Match offsets can reach into previous blocks' output
- Return type extended to propagate offset history for next block

**Sequences header consolidation (#556, merged):**
- Unified `parseSequencesHeader` variants, removing code duplication
- Wired compression modes directly into `decompressBlocks`

**Dictionary frame rejection (#565, merged):**
- `decompressFrame` now returns an error if `dictionaryId ≠ 0`
- 3 validation edge case tests (dictionary rejection, checksum
  corruption, truncated frame)

**Malformed data tests (#567, merged):**
- 12 new test cases (158 lines) covering: reserved frame header bits,
  content size mismatch, max window size, truncated headers, reserved
  block types, raw block underflow, RLE boundaries, Huffman weight
  validation, skippable frame overflow, trailing data detection

**Zstd specification infrastructure:**
- `Zip/Spec/Fse.lean` (#584, merged, 133 lines): FSE distribution validity
  predicates (`ValidAccuracyLog`, `ValidDistribution`, `ValidFseTable`)
  with `Decidable` instances. Predefined distribution validity proved by
  `decide`. Sorry count reduced from 3 to 1 by proving
  `decodeFseDistribution_accuracyLog_ge` and `_le` (#603).
  `decodeFseDistribution_sum_correct` proved via loop invariant (#619).
  `buildFseTable_accuracyLog_eq` proved (#646); 1 sorry remains
  (`buildFseTable_cells_size`, requires `forIn` loop invariant).
- `Zip/Spec/XxHash.lean` (#618, merged, ~180 lines): XXH64 specification
  predicates — prime value validation, initial state, round function
  properties. `xxHash64_empty` proved (#642). 4 sorry remaining (3 UInt64
  test vectors too expensive for kernel evaluation, 1 docstring mention).
- `Zip/Spec/ZstdHuffman.lean` (#606, merged, ~170 lines): Huffman weight
  validity predicates per RFC 8878 §4.2.1 — `ValidWeights`, `ValidMaxBits`,
  `ValidHuffmanTable`. `isPow2_iff` and `weightSum_pos_of_exists_nonzero`
  proved (#628). `buildZstdHuffmanTable_maxBits_pos` proved via WF
  refactoring of `while` loop to `findMaxBitsWF` (#641). 2 sorry remaining
  (`buildZstdHuffmanTable_tableSize` fill loop invariant, one other).
- `Zip/Spec/Zstd.lean` (#587, merged): frame specification predicates.
  `parseBlockHeader_blockSize_lt` proved via `bv_decide` (#647) — corrected
  from false `_le` statement to true `< 2^21` bound. 0 sorry remaining.
- `Zip/Spec/ZstdSequence.lean` (#632, merged): sequence validity predicates
  and block size validation. `executeSequences_output_length` proved (#653)
  via refactoring `executeSequences` from `forIn` to explicit recursion.
  0 sorry remaining.

**Code modularity:**
- ZstdFrame.lean split (#599): monolithic 1059-line file split into
  `ZstdHuffman.lean` (400 lines), `ZstdSequence.lean` (392 lines),
  `ZstdFrame.lean` (302 lines). Error prefixes normalized. This resolved
  the merge conflict bottleneck by reducing concurrent modification surface.
- Block size and window size validation (#613): `decompressBlocks` validates
  block size ≤ 128KB, `executeSequences` validates match offsets against
  window size. 4 validation tests added.

**Code quality reviews:**
- ZstdFrame.lean audit (#583): 1059 lines reviewed. Splitting plan
  identified and executed via #599.
- Fse.lean + XxHash.lean audit (#579): 481 lines reviewed. No critical
  issues found.
- Stale PR triage (#611): closed 4 conflicted PRs (#561, #577, #602,
  #596) and 2 stale issues (#568, #558). Unblocked #540 and #552 for
  fresh work.
- Label cleanup (#612): removed stale `has-pr` labels, reviewed and
  merged PR #606 (Huffman spec).
- Final bare simp sweep (#607): completed with
  DeflateEncodeDynamicProps residual fixed.
- Zstd spec PR review (#624): reviewed #618 (XxHash) and #619 (FSE sum).
  Noted one bare `simp` in #619 and CLAUDE.md modification in #618.

**Self-improvement:**
- Merge conflict cascade analysis (#597): documented recovery-of-recovery
  anti-pattern and prevention strategies in `agent-pr-recovery` skill.
- Zstd spec infrastructure retrospective (#623): created
  `lean-zstd-spec-pattern` skill documenting file structure and naming
  conventions. Updated `lean-monad-proofs` with `eq_of_beq` pattern and
  `split vs by_cases` decision guide.

**Compressed block integration (#651, milestone):**
- Wired full compressed block pipeline end-to-end in `decompressBlocks`:
  `resolveSequenceFseTables` → backward bitstream → `decodeSequences` →
  `executeSequences`
- Added `PrevFseTables` struct for FSE Repeat mode across blocks
- All three Zstd block types (raw, RLE, compressed) now decompress
  through a unified pipeline
- This was the critical integration step (issue #552) that had been
  blocked by merge conflict cascades for multiple summary periods

**Zstd spec quality audit (#650):**
- Eliminated 12 bare `simp` occurrences across ZstdHuffman.lean and
  ZstdSequence.lean spec files
- Removed `xxHash64_deterministic` (tautological — was just `rfl`)
- Added missing docstrings to specification theorems

**Test infrastructure expansion:**
- `ZstdNative.lean` test monolith split into 3 focused files (#630):
  `ZstdFrameNative.lean`, `ZstdFseNative.lean`, `ZstdHuffmanNative.lean`

**WF refactoring (continued, #667, #671):**
- `decompressBlocksWF` (#667): replaced opaque `forIn` loop with
  well-founded recursion on remaining data, proved `parseBlockHeader_pos_eq`
- `buildZstdHuffmanTable` fill loops (#671): extracted `fillHuffmanTableInnerWF`
  and `fillHuffmanTableWF` from opaque `for` loops, proved
  `fillHuffmanTableInnerWF_preserves_size` and `fillHuffmanTableWF_preserves_size`

**Spec proofs (14-PR batch, Mar 6):**
- #664: `decompressFrame_contentSize_eq` and `decompressFrame_checksum_valid`
  — characterizing properties relating frame output to header metadata
- #672: `copyBytes_getElem_lt` and `copyMatch_getElem_lt` — existing buffer
  content preserved during sequence execution
- #677: `decompressRawBlock_content`, `decompressRawBlock_pos_eq`,
  `decompressRLEBlock_content`, `decompressRLEBlock_pos_eq` — raw and RLE
  block content preservation and position advance
- #681: `resolveOffset_repeat1_val`, `resolveOffset_repeat2_val`,
  `resolveOffset_repeat3_val` — exact return values for repeat offset codes
- #685: `litLenExtraBits_size`, `matchLenExtraBits_size`,
  `decodeLitLenValue_small`, `decodeMatchLenValue_small`,
  `decodeOffsetValue_positive` — RFC table sizes and decoded value bounds

**Conformance testing (#680, #686):**
- End-to-end test matrix: 48 combinations of FFI compress → native decompress
  across 4 compression levels × 4 data patterns × 3 sizes
- Tests in `ZipTest/ZstdConformance.lean`
- 36/48 passing (12 text-pattern Huffman failures, known bug tracked in #703)

**Spec proofs (12-PR batch, Mar 6):**

This batch deepened the sequence execution spec toolkit in ZstdSequence.lean
(now 47 theorems/lemmas, 740 lines) across three areas:

*Sequence execution framework:*
- #700: `executeSequences_empty` (base case), `executeSequences_loop_output_size_ge`
  (output size monotonicity)
- #714: `executeSequences_loop_cons` (single-step unfolding),
  `executeSequences_loop_cons_output_size` (output size composition)

*Content theorems and value bounds:*
- #690: `copyBytes_getElem_ge` and `copyMatch_getElem_ge` — content of newly
  written bytes during sequence execution
- #704: `copyMatch_loop_getElem_ge` and `copyMatch_getElem_ge` — general
  content theorem for copyMatch including overlapping regions (subsumes the
  non-overlapping case)
- #705: `decodeMatchLenValue_ge_three` and `decodeOffsetValue_ge_two` — RFC
  8878 value decoding bounds via `decide_cbv`

*resolveOffset completeness:*
- #687: `resolveOffset_shifted1_val`, `resolveOffset_shifted2_val`,
  `resolveOffset_shifted3_val` — exact values and history rotation for shifted
  repeat offsets (litLen = 0 case)
- #695: `resolveOffset_history_valid_large` and
  `resolveOffset_history_valid_repeat` — ValidOffsetHistory preservation
- #710: `resolveOffset_positive_shifted12` (shifted repeat codes 1–2 positivity),
  `resolveOffset_positive_all` (unified positivity covering all cases)

*Infrastructure:*
- #694, #699: stale PR cleanup (closed #686 duplicate, #689) + composability
  audit identifying 4 gaps in the executeSequences proof path
- #711: skills update — added WF helper functions, table correctness,
  exhaustive case analysis, loop invariant sections to lean-zstd-spec-pattern;
  added split/letFun chains, inline show proofs to lean-monad-proofs

**Position advancement spec campaign (16-PR batch, Mar 6):**

This batch focused on proving that Zstd parsing functions advance their
position correctly — a prerequisite for composing position bounds into
end-to-end frame position proofs.

*Position specs proved:*
- #723: `decompressBlocksWF_pos_gt` (output monotonicity and position advancement)
- #724: `parseSequencesHeader_pos_gt`, `parseSequencesHeader_pos_bounded` (advances
  by 1–4 bytes), `parseSequencesHeader_byte0_zero` (zero-case characterization)
- #730: `skipSkippableFrame_pos_eq` (exact position formula), `skipSkippableFrame_pos_gt`
- #738: `buildRleFseTable` structural specs, `resolveSingleFseTable_predefined_pos`
- #739: `parseLiteralsSection` raw/RLE position advancement and huffTable specs
- #740: `resolveSingleFseTable_rle_pos` (RLE advances by 1), `resolveSingleFseTable_repeat_pos`
  (repeat mode position unchanged)
- #753: `parseFrameHeader_pos_gt` (strict advancement), `parseFrameHeader_pos_ge`
  (minimum bound)

*Structural invariants and sorry reduction:*
- #707: `weightsToMaxBits_valid` proved (corrected false bound from `1 <<< (m - 1)` to
  `1 <<< m`), removing 1 sorry from ZstdHuffman.lean
- #718: `buildFseTable_size_eq` (table size = 1 <<< accuracyLog),
  `buildFseTable_accuracyLog_eq` (accuracy log passthrough)
- #733: BackwardBitReader base-case specs — `isFinished` characterization,
  `readBits` zero returns current state, error characterization
- #748: `buildPredefinedFseTables_accuracyLogs` proved; `buildPredefinedFseTables_success`
  blocked by opaque `while` loop (adds 1 sorry to Fse.lean)

*WF recursion:*
- #744: `decompressZstd` refactored from opaque `while` loop to well-founded
  recursion (`decompressZstdWF` with `termination_by data.size - pos`). Runtime
  guards ensure non-advancing frames throw errors. This was the last opaque
  `while` loop in the top-level Zstd pipeline.

*Quality reviews:*
- #725: ZstdSequence.lean — combined duplicate loop induction proofs into single pass
- #749: Fse.lean — replaced all 22 bare simp/simp_all with explicit `simp only`
- #754: ZstdSequence.lean — eliminated 7 remaining bare simp calls

*Housekeeping:*
- #729: closed stale PR #721, closed issue #701, unclaimed #703 for reassignment

**Conformance testing:**
- 48/48 test matrix passing (FFI compress → native decompress, 4 levels × 4
  patterns × 3 sizes)

**11-PR batch (Mar 6–7): sorry reduction, position specs, quality reviews:**

*Sorry reduction:*
- #776: `buildPredefinedFseTables_success` proved — removed the last Fse.lean
  sorry. Used structural success proof (each loop body returns .ok) rather than
  WF refactoring. Added `buildFseTable_ok_of_valid` and `forIn_pure_ok` helpers.
  Sorry count: 4 → 3.

*Position advancement specs:*
- #760: `BitReader.readBits` exact bitPos advancement (`readBits_bitPos_eq`,
  `readBits_pos_eq`). Previously the last uncovered function in the position
  campaign.
- #763: `decompressFrame` position advancement (`decompressFrame_pos_gt`) —
  composed from `parseFrameHeader_pos_gt` and `decompressBlocksWF_pos_gt`.
- #772: `resolveSingleFseTable` FSE-compressed mode position advancement
  (`resolveSingleFseTable_fseCompressed_pos_gt`). Composed from
  `decodeFseDistribution_bitPos_ge` and `buildFseTable` passthrough.
- #779: `parseLiteralsSection` compressed path position specs — unified
  `parseLiteralsSection_pos_gt` covering all literal types (0–3).
- #781: `resolveSequenceFseTables` position composition — composed three
  `resolveSingleFseTable` calls proving `resolveSequenceFseTables_pos_ge`.

*Characterizing properties:*
- #768: `windowSizeFromDescriptor` positivity (`windowSizeFromDescriptor_pos`)
  and minimum bound (`windowSizeFromDescriptor_ge_1024`). Proved via exhaustive
  evaluation over all 256 UInt8 inputs.

*WF refactoring:*
- #765: `buildFseTable` while loop refactored to WF recursion
  (`buildFseTableStepWF`). Proves `buildFseTableStepWF_pos_lt` for position
  advancement and `buildFseTableStepWF_cells_size` for size preservation.

*Quality reviews (bare simp_all elimination):*
- #764: ZstdHuffman.lean — replaced 3 bare `simp_all`, extracted duplicate
  monadic bind peeling into `buildZstdHuffmanTable_ok_elim` helper (-36 lines).
- #778: BitstreamCorrect.lean — replaced 4 bare `simp_all` with targeted
  tactics (`dsimp`, `eq_of_beq`, explicit `split` cases).
- #780: BitReaderInvariant.lean — replaced 3 bare `simp_all` with explicit
  `simp_all only [...]` lemma lists.

**11-PR batch (Mar 7): value bounds, top-level specs, quality reviews:**

*Track E position/value specs (5 PRs):*
- #792: `readBits_value_lt_pow2` — BackwardBitReader.readBits produces value < 2^n
- #795: `buildFseTable_numBits_le` — cells numBits ≤ accuracyLog (ValidFseTable
  condition c). Used `set!_preserves_forall` helper for dependent type reasoning.
- #797: New `Zip/Spec/ZstdFrame.lean` — first specs for `decompressZstdWF`:
  `decompressZstdWF_base`, `_single_standard_frame` (base case and single-frame
  equivalence)
- #803: `readBits_totalBitsRemaining_sub`, `_lt` — exact bit consumption tracking
  for BackwardBitReader.readBits. Key discovery: `↓reduceIte` doesn't reduce
  concrete numeral comparisons.
- #808: `decompressZstdWF_single_skippable_frame`, `_skip_then_standard` — skippable
  frame composition specs for the top-level decompressor

*Quality reviews (5 PRs):*
- #787: Zstd.lean spec audit — deduplicated `parseFrameHeader` position proofs,
  documented grind usage (-15 lines)
- #796: Closed stale PR #789, compressed `decompressBlocksWF` proof boilerplate
  (-37 lines)
- #802: Zstd.lean quality pass — documented grind, converted bare simp
- #807: XxHash.lean quality pass — converted 4 bare simp to simp only
- #811: DeflateEncodeDynamic.lean quality pass — replaced 5 simp_all with targeted
  tactics (termination proofs: `simp only` + `omega`; Bool→Prop: `beq_eq_false_iff_ne`)

*Skill updates (1 PR):*
- #798: Updated lean-zstd-spec-pattern, lean-monad-proofs, lean-zstd-patterns with
  position-spec campaign patterns and BackwardBitReader proof techniques

**BackwardBitReader lifecycle coverage** now complete:
- init → totalBitsRemaining bound and startPos
- readBits → value bound (val < 2^n), exact bit consumption, bitPos advancement
- isFinished → characterization

**Remaining:**
- Prove remaining sorry stubs: 3 in XxHash (UInt64 test vectors too
  expensive for kernel evaluation — intractable without native_decide)
- Compose position specs into end-to-end frame position theorem
- Spec-level decoder with correctness proofs (algorithmic correspondence
  between native and spec decoder, following the DEFLATE B3 pattern)
- Compressor + roundtrip proof

**12-PR batch (Mar 7): le_size campaign + characterizing properties + quality reviews:**

This batch established position-within-bounds invariants (`le_size` theorems)
across 6 Zstd parsing functions and extended characterizing properties for
compressed headers and sequence parsing.

*Track E le_size campaign (6 PRs):*
- #825: `skipSkippableFrame_le_size`, `decompressRawBlock_le_size`,
  `decompressRLEBlock_le_size` — frame-level position bounds
- #835: `parseBlockHeader_le_size`, `parseFrameHeader_le_size` — header
  parsers stay within data bounds
- #834: `parseSequencesHeader_le_size`, `parseSequencesHeader_medium_encoding`
  — sequence header position bound and medium encoding characterization

*Characterizing properties (3 PRs):*
- #833: `decodeHuffmanSymbol` specs — bit consumption monotonicity
  (`decodeHuffmanSymbol_pos_mono`) and bounds
- #829: `parseCompressedLiteralsHeader` specs — `headerSize`, `fourStreams`,
  `regen_bound` characterizing compressed literal header fields
- #826: `parseSequencesHeader_numSeq_small` — small encoding extraction
  (1-byte case: numSeq = byte0 when 0 < byte0 < 128)

*Top-level decompressor specs (1 PR):*
- #839: `decompressZstdWF_output_size_ge` (output monotonicity via functional
  induction) and `decompressZstd_single_frame` (API-level single-frame theorem)

*Quality reviews (2 PRs):*
- #832: DeflateSuffix.lean — converted 3 bare `simp_all`
- #822: Fse.lean — fixed bare simp, documented grind, combined rw calls

The le_size campaign now covers the "easy" functions (those with simple bounds
checks): `skipSkippableFrame`, `decompressRawBlock`, `decompressRLEBlock`,
`parseBlockHeader`, `parseFrameHeader`, `parseSequencesHeader`. Remaining
le_size gaps require deeper invariants: `parseLiteralsSection` (variable-length
compressed headers), `BitReader` operations, FSE distribution chain,
`decompressBlocks` loop, and frame-level composition.

**Summary:** The Zstd spec infrastructure now spans 6 files with 195
theorems/lemmas: ZstdSequence (57), Fse (50), ZstdHuffman (43), Zstd (27),
XxHash (12), ZstdFrame (6). Total spec line count: 4,448 lines.

**11-PR batch (Mar 7–8): le_size capstone + content preservation + FSE validity + quality reviews:**

This batch completed the le_size campaign to the frame level, started content
preservation proofs for sequence execution, proved FSE table validity
composition, and continued quality reviews across DEFLATE spec files.

*Track E le_size campaign completion (3 PRs):*
- #848: `parseHuffmanTreeDescriptor_le_size` — tree descriptor position bounds
- #856: `decompressBlocksWF_le_size` — block loop position within data bounds
  (composed from `parseBlockHeader_le_size` + per-block-type bounds)
- #861: `decompressFrame_le_size` — frame-level capstone. When
  `decompressFrame` succeeds, returned position ≤ data.size. Composed from
  `parseFrameHeader_le_size` and `decompressBlocksWF_le_size`. This completes
  the le_size chain: `readBit` → `readBits` → `parseLiteralsSection` →
  `parseHuffmanTreeDescriptor` → `decompressBlocksWF` → `decompressFrame`.

*Track E content preservation (1 PR):*
- #865: `executeSequences_loop_getElem_lt` — sequence execution loop preserves
  previously written output bytes. First content preservation theorem for the
  Zstd sequence execution pipeline.

*Track E BackwardBitReader invariants (1 PR):*
- #858: `readBits_data_eq`, `readBits_startPos_eq`, `init_data_eq`,
  `init_startPos_eq` — field preservation through BackwardBitReader operations.

*Track E FSE table validity (1 PR):*
- #872: `buildFseTable_symbol_lt` (symbol indices within bounds through all 4
  construction loops) and `buildFseTable_valid` (composed `ValidFseTable`
  predicate). Used `forIn_range_preserves` helper for loop invariants. Added
  `toUInt16_toNat_lt_of_lt` for UInt16 bounds reasoning.

*Quality reviews (4 PRs):*
- #853: ZstdHuffman.lean spec audit — eliminated bare `simp`, compressed
  proofs, improved consistency (-121 lines net)
- #857: DeflateEncodeDynamic.lean — converted all 7 bare `simp` to
  `simp only` with explicit lemma lists
- #862: DeflateEncodeDynamic.lean quality pass — aggregated skill updates
  and progress documentation alongside bare simp conversions
- #869: DeflateDynamicEmit.lean — removed 1 unused linter pragma and 2
  unnecessary `maxRecDepth 2048` pragmas (default settings sufficient)

*Maintenance (1 PR):*
- #866: Rebased PR #857 to resolve merge conflicts in progress files

**11-PR batch (Mar 8): Huffman validity, content preservation, offset history, bare simp completion, multi-frame composition:**

This batch advanced Track E spec coverage across four dimensions and
completed the bare simp campaign project-wide.

*Track E table validity (1 PR):*
- #884: `buildZstdHuffmanTable_numBits_le` (cells numBits within max bit
  depth) and `buildZstdHuffmanTable_valid` (composed `ValidHuffmanTable`
  predicate). 3 helper lemmas for fill loop invariants.

*Track E content/field preservation (2 PRs):*
- #887: `decompressZstdWF_prefix` (every byte in the initial accumulator
  is preserved at the same index in the result — append-only property via
  WF induction) and `decompressZstd_empty` (empty input → empty output).
- #894: `decodeHuffmanSymbol_data_eq` and `decodeHuffmanSymbol_startPos_eq`
  — BackwardBitReader `data` and `startPos` fields are unchanged through
  Huffman symbol decoding.

*Track E offset history validity (1 PR):*
- #880: `resolveOffset_history_valid_of_fst_ne_zero` and
  `executeSequences_loop_history_valid` — `ValidOffsetHistory` threaded
  through the full sequence execution loop. This connects
  `resolveOffset`'s per-step history validity to loop-level invariants.

*Track E multi-frame composition (1 PR):*
- #901: `decompressZstdWF_standard_then_standard` (two consecutive
  standard frames produce concatenated output at WF level) and
  `decompressZstd_two_frames` (same at API level). First compositional
  spec for multi-frame Zstd streams.

*Bare simp campaign completion (5 PRs):*
- #879: DeflateDynamicHeader.lean — bare simp + linter pragma cleanup
- #885: DeflateEncodeDynamicProps.lean first half (lines 17–310)
- #886: DeflateEncodeDynamicProps.lean second half (lines 311–695)
- #892: Huffman.lean — completes the non-intentional bare simp campaign
- #900: Fse.lean, HuffmanKraft.lean, BitstreamComplete.lean — final sweep

With #900, zero standalone bare `simp` calls remain anywhere in the
codebase (Zip/, ZipForStd/, Native/). Only the 15 documented intentional
instances in DeflateSuffix.lean persist. 4 bare `simp_all` calls remain
in DeflateEncode, DeflateStoredCorrect, EmitTokensCorrect, and
InflateCorrect (see correction in Mar 8 batch notes).

*Skill updates (1 PR):*
- #891: Created `lean-content-preservation` skill from 16-PR batch
  patterns. Updated `lean-zstd-patterns`, `lean-zstd-spec-pattern`,
  `lean-content-preservation` with recurring proof strategies.

**12-PR batch (Mar 8): FSE validity chain capstone, WF decoder refactors, quality reviews:**

This batch completed the FSE table validity chain from predefined tables
through `resolveSequenceFseTables`, added WF variants of two decoder functions
with output size theorems, proved API-level specs for sequence history and
skippable frames, and continued quality reviews across core spec files.

*FSE table validity chain completion (3 PRs):*
- #911: `buildPredefinedFseTables_valid` — all three predefined FSE tables
  satisfy `ValidFseTable` (litLen at accuracyLog 6, matchLen at 6, offset at 5)
- #919: `resolveSingleFseTable_le_size` — per-mode position bound preservation
  (predefined/RLE/repeat modes all return pos' ≤ data.size)
- #924: `resolveSingleFseTable_fseCompressed_valid` (FSE-compressed mode
  produces `ValidFseTable`), `resolveSingleFseTable_valid_ex` (unified across
  all 4 modes), and `resolveSequenceFseTables_valid` (all three sequence tables
  valid when previous tables valid). This is the FSE validity chain capstone:
  `buildFseTable_valid` → `resolveSingleFseTable_*_valid` →
  `resolveSequenceFseTables_valid`.

*WF decoder refactors with output size theorems (2 PRs):*
- #929: `decodeHuffmanStreamWF` — structurally recursive variant of
  `decodeHuffmanStream` with two composition theorems:
  `decodeHuffmanStreamWF_size` (output = acc.size + count) and
  `decodeHuffmanStreamWF_totalBitsRemaining_le` (bit budget monotonicity)
- #930: `decodeFseSymbolsWF` — structurally recursive variant of
  `decodeFseSymbols` with `decodeFseSymbolsWF_size` (output has exactly
  `count` elements). Both WF variants replace opaque `for` loops that
  could not be unfolded in proofs.

*API-level specs (2 PRs):*
- #907: `executeSequences_history_valid` (ValidOffsetHistory preserved through
  sequence execution) and `executeSequences_history_size` (output history
  maintains 3 entries). These lift loop-level invariants to the API boundary.
- #912: `decompressZstd_single_skippable` (single skippable frame → empty
  output) and `decompressZstd_skip_then_standard` (skip + standard → only
  standard content). API-level specializations of WF-level frame theorems.

*Quality reviews (4 PRs):*
- #908: ZstdHuffman.lean — extracted `readBits_elim` pattern, removed dead code
- #915: Zstd.lean — `unfold_except` tactic macro replacing 20 identical
  monadic unfolding calls, grind audit (6 calls verified appropriate),
  removed 4 unused `termination_by`/`decreasing_by` clauses (-21 lines)
- #918: Fse.lean — proof optimization (-87 lines, 5.5%), 2 bare simp_all
  eliminated
- #926: Deflate.lean — 3 bare simp_all to targeted tactics, proof optimization
  (-67 lines, 6.3%), dead code removal (`le_bytes_eq_encodeLEU16`, 30 lines)

*Skill updates (1 PR):*
- #925: Meditate: updated `lean-zstd-spec-pattern` with table validity chain
  and frame composition patterns; updated `proof-review-checklist` with
  compression and helper extraction patterns

**13-PR batch (Mar 8): WF maturation, content characterization, simp_all review throughput:**

This batch advanced Track E along two fronts — WF refactoring enabling output
size theorems, and content characterization for raw/RLE literals and blocks —
while continuing the simp_all elimination campaign across DEFLATE spec files.

*Track E feature PRs (5):*
- #935: `decodeFseLoop_probs_ge_neg1` — FSE loop probability bound invariant.
  When `decodeFseLoop` succeeds and all input probs have `.toInt ≥ -1`, all
  output probs also have `.toInt ≥ -1`. 8 supporting lemmas covering
  `Array.push` preservation, `pushZeros` bounds, `readProbValue` output bounds.
- #940: `parseHuffmanTreeDescriptor_valid` (composed `ValidHuffmanTable` from
  descriptor parsing) and `parseHuffmanTreeDescriptor_maxBits_pos` (maxBits ≥ 1).
  Validity composition connecting tree descriptor parsing to table construction.
- #943: `decodeSequencesWF` — structurally recursive variant of
  `decodeSequences` with `decodeSequencesWF_size` (output has exactly `numSeq`
  elements when numSeq > 0). Replaces opaque `for` loop.
- #951: `decodeFourHuffmanStreamsWF` — structurally recursive variant of
  `decodeFourHuffmanStreams` with `decodeFourHuffmanStreamsWF_size` (output
  buffer size = regenSize). Combines four individual `decodeHuffmanStreamWF_size`.
- #952: `parseLiteralsSection_raw_eq_extract` (raw literals are an exact
  contiguous slice of input data) and `parseLiteralsSection_rle_all_eq` (RLE
  literals are all-equal). First content characterizations for literal sections.

*Track E content — block level (1 PR):*
- #955: `decompressBlocksWF_single_raw` and `decompressBlocksWF_single_rle` —
  single-block output characterization. When the block loop processes a single
  last raw/RLE block, the result is `output ++ block` at the correct position.

*Review PRs — simp_all campaign (7):*
- #936: HuffmanCorrectLoop.lean — simp_all conversion + proof optimization
- #939: HuffmanCorrect.lean — simp_all audit + proof optimization
- #944: HuffmanEncodeCorrect.lean — simp_all + bare simp elimination
- #947: DecodeCorrect.lean — simp_all conversion + proof optimization
- #950: DecodeComplete.lean — simp_all conversion + proof optimization
- #956: BitstreamWriteCorrect.lean — simp_all conversion + proof optimization
- #961: DeflateFixedTables.lean — simp_all conversion + proof optimization

**Summary:** The Zstd spec infrastructure now spans 6 files with 272
theorems/lemmas: ZstdSequence (77), Fse (73), ZstdHuffman (65), Zstd (33),
XxHash (12), ZstdFrame (12). Total spec line count: 6,267 lines.

**Bare simp_all correction:** The previous batch claimed "0 bare simp_all
remaining" but 4 instances survived in DeflateEncode.lean,
DeflateStoredCorrect.lean, EmitTokensCorrect.lean, and InflateCorrect.lean.
These are pre-existing residuals, not regressions from this batch. The simp_all
campaign has made substantial progress (12 `simp_all only` conversions across
spec files) but is not yet complete.

**WF refactoring status:** The WF refactoring pipeline now covers 5 Zstd
decoder functions: `decodeFseSymbolsWF`, `decodeHuffmanStreamWF`,
`decodeFourHuffmanStreamsWF`, `decodeSequencesWF`, `decompressBlocksWF`. Each
WF variant replaces an opaque `for`/`while` loop that could not be unfolded
in proofs, enabling output size theorems and loop invariant reasoning.

**Content characterization emergence:** This batch introduced the first
literal section content specs (raw extract, RLE all-equal) and composed them
to the block loop level (single-block raw/RLE output = `output ++ block`).
Combined with the existing `executeSequences_loop_getElem_lt` (sequence
execution preserves previously written bytes), this represents the beginning
of end-to-end content characterization for Zstd frames — though significant
gaps remain between the literal/sequence level and full frame output.

**10-PR batch (Mar 8): content pipeline maturation + simp_all campaign completion:**

This batch advanced the Track E content pipeline from single-block characterization
to multi-block composition and frame-level output, while completing the simp_all
campaign down to 2 remaining instances.

*Track E content pipeline — block level (3 PRs):*
- #962: `decompressBlocksWF_raw_step` and `decompressBlocksWF_rle_step` —
  non-last block continuation theorems. When the block loop processes a non-last
  raw/RLE block followed by more blocks, the intermediate output is `output ++ block`
  at the correct position.
- #988: `decompressBlocksWF_two_raw` and `decompressBlocksWF_two_rle` —
  two-block composition for same-type blocks. Output = `output ++ block1 ++ block2`.
- #1000: `decompressBlocksWF_two_compressed_literals` — two-block composition
  for compressed-literals blocks (non-last compressed + last compressed).

*Track E content pipeline — mixed types (1 PR):*
- #997: `decompressBlocksWF_raw_then_rle` and `decompressBlocksWF_rle_then_raw`
  — mixed-type two-block composition. Raw followed by RLE and vice versa.

*Track E content pipeline — frame level (1 PR):*
- #974: `decompressFrame_raw_content` and `decompressFrame_rle_content` —
  single-block frame output characterization. When a frame contains a single
  raw/RLE block, the frame-level output matches the block content.

*Merge conflict recovery (2 PRs):*
- #989: rebased compressed sequences theorems (#977) onto master after
  merge conflicts from concurrent PRs
- #982: rebased compressed literals-only theorems (#970) onto master

*simp_all campaign (3 PRs):*
- #976: HuffmanTheorems + EmitTokensCorrect + DeflateStoredCorrect — converted
  all bare `simp_all` in these files to explicit alternatives. Reduces bare
  simp_all count from 4 to 2.
- #996: Fse.lean + HuffmanEncode.lean + HuffmanCorrect.lean — completes the
  simp_all campaign across these files (0 remaining in each).
- #995: ZstdSequence.lean — simp_all conversion + proof optimization.

*Quality reviews (2 PRs):*
- #981: GzipCorrect.lean + ZlibCorrect.lean — bare simp cleanup + proof optimization
- #971: BitReaderInvariant.lean — simp_all conversion + proof optimization

**Content pipeline status:** The Track E content characterization now covers:

| Block type | Single | Step (non-last) | Two-block (same) | Two-block (mixed) | Frame (single) |
|---|---|---|---|---|---|
| Raw | done | done | done | raw+RLE done | done |
| RLE | done | done | done | RLE+raw done | done |
| Compressed (literals-only) | done | done | done | — | — |
| Compressed (with sequences) | — | — | — | — | — |

**simp_all campaign status:** 2 bare `simp_all` remaining (DeflateEncode.lean,
InflateCorrect.lean). Both are covered by existing review issue #968. Down from
~50+ at campaign start to 2.

**Summary:** The Zstd spec infrastructure now spans 6 files with 333
theorems/lemmas: ZstdSequence (84), Fse (80), ZstdHuffman (73), Zstd (59),
XxHash (25), ZstdFrame (12). Total spec line count: 6,719 lines.

**15-PR batch (Mar 8–9): compressed composition matrix, API-level content, Zstd benchmarking:**

This batch filled in the block-level compressed composition matrix,
extended frame-level content to compressed block types, lifted content
theorems to the API level, added Zstd decompression benchmarking, and
continued quality reviews.

*Track E block-level compositions (4 PRs):*
- #1013: `decompressBlocksWF_two_compressed_sequences_blocks` (homogeneous
  compSeq pair) and `decompressBlocksWF_compressed_seq_then_raw` (compSeq+raw)
- #1019: `decompressBlocksWF_compressed_literals_then_raw` and
  `decompressBlocksWF_compressed_literals_then_rle` (compLit+raw, compLit+RLE)
- #1033: `decompressBlocksWF_raw_then_compressed_sequences`,
  `decompressBlocksWF_rle_then_compressed_sequences`,
  `decompressBlocksWF_compressed_seq_then_rle` (raw/RLE+compSeq, compSeq+RLE)
- #1034: `decompressBlocksWF_compressed_seq_then_compressed_lit` and
  `decompressBlocksWF_compressed_lit_then_compressed_seq` (cross-compressed pairs)

*Track E frame-level content (3 PRs):*
- #1020: `decompressFrame_raw_then_rle_content` and
  `decompressFrame_rle_then_raw_content` (mixed raw/RLE two-block frames)
- #1027: `decompressFrame_single_compressed_literals_content` and
  `decompressFrame_single_compressed_sequences_content` (single compressed blocks)
- #1051: `decompressFrame_compressed_lit_then_raw_content` and
  `decompressFrame_compressed_lit_then_rle_content` (compressed-first + raw/RLE)

*Track E API-level content (2 PRs):*
- #1029: `decompressZstd_two_raw_blocks_content` and
  `decompressZstd_two_rle_blocks_content` (two-block raw/RLE at API level)
- #1039: `decompressZstd_single_compressed_literals` and
  `decompressZstd_single_compressed_sequences` (single compressed-block at API level)

*Track D (1 PR):*
- #1038: Zstd decompression benchmarking suite in `ZipTest/ZstdBench.lean` —
  native vs FFI across 4 compression levels × 4 data patterns × 3 sizes

*Quality reviews (3 PRs):*
- #1032: DynamicTreesComplete + DynamicTreesCorrect cleanup
- #1040: DecodeCorrect.lean + GzipCorrect.lean bare simp cleanup
- #1046: ZstdFrame.lean — 1 bare simp eliminated, helper lemma extraction

*Merge conflict recovery (1 PR):*
- #1023: rebased PR #1009 onto master, closed stale #1006

*Self-improvement (1 PR):*
- #1024: Meditate — composition matrix scaling patterns, review campaign
  completion analysis, conflict resolution patterns

**Block-level composition matrix status (14/16):**

|  | Raw | RLE | CompLit | CompSeq |
|---|---|---|---|---|
| **Raw +** | done | done | — | done |
| **RLE +** | done | done | — | done |
| **CompLit +** | done | done | done | done |
| **CompSeq +** | done | done | done | done |

2 remaining: raw+compLit and RLE+compLit (covered by open PR #1011).

**Content pipeline status (updated):**

| Block type | Single block | Step (non-last) | Two-block (same) | Two-block (mixed) | Frame (single) | Frame (two-block) | API (single) |
|---|---|---|---|---|---|---|---|
| Raw | done | done | done | raw+RLE | done | two_raw, raw+RLE | two_raw |
| RLE | done | done | done | RLE+raw | done | two_rle, RLE+raw | two_rle |
| CompLit | done | done | done | compLit+raw, +RLE | done | compLit+raw, +RLE | done |
| CompSeq | done | done | done | compSeq+raw, +RLE, +compLit, compLit+compSeq | done | — | done |

**simp_all campaign status:** 0 bare `simp_all` remaining (DeflateEncode and
InflateCorrect instances now have explicit lemma arguments: `simp_all [beq_iff_eq]`
and `simp_all [← UInt32.toNat_inj]` respectively). Campaign complete.

**Summary:** The Zstd spec infrastructure now spans 6 files with 361
declarations: ZstdSequence (84), Fse (81), ZstdHuffman (73), Zstd (78),
XxHash (26), ZstdFrame (19). Total spec line count: 8,172 lines.

**12-PR batch (Mar 9): two-block content theorem completion wave + simp_all elimination + quality reviews:**

This batch completed the block-level composition matrix, extended frame-level
content coverage across most two-block combinations, lifted several pairings
to API level, completed the simp_all elimination campaign, and continued
proof quality reviews.

*Track E block-level completion (1 PR):*
- #1068: `decompressBlocksWF_raw_then_compressed_literals` and
  `decompressBlocksWF_rle_then_compressed_literals` — completing the 16/16
  block-level composition matrix.

*Track E frame-level content (4 PRs):*
- #1055: `decompressFrame_compressed_seq_then_raw_content` and
  `decompressFrame_compressed_seq_then_rle_content` (compSeq-first + raw/RLE)
- #1060: `decompressFrame_compressed_seq_then_compressed_lit_content` and
  `decompressFrame_compressed_lit_then_compressed_seq_content` (cross-compressed)
- #1073: `decompressFrame_two_compressed_literals_blocks_content` and
  `decompressFrame_two_compressed_sequences_blocks_content` (homogeneous compressed)

*Track E API-level content (3 PRs):*
- #1052: `decompressZstd_raw_then_rle_content` and `decompressZstd_rle_then_raw_content`
  (mixed raw/RLE two-block frames at API level)
- #1060: `decompressZstd_single_raw_block_content` and
  `decompressZstd_single_rle_block_content` (single raw/RLE at API level)
- #1061: `decompressZstd_compressed_lit_then_raw_content` and
  `decompressZstd_compressed_lit_then_rle_content` (compLit+raw/RLE at API level)
- #1074: `decompressZstd_compressed_seq_then_compressed_lit_content` and
  `decompressZstd_compressed_lit_then_compressed_seq_content` (cross-compressed at API level)

*Track E FSE spec (1 PR):*
- #1067: `readProbValue_pos_le_size` and `decodeFseDistribution_pos_le_size` —
  position-within-bounds chain for FSE distribution decoding

*simp_all campaign final completion (1 PR):*
- #1069: Converted the last 4 `simp_all` calls across Deflate.lean,
  DeflateEncode.lean, and InflateCorrect.lean to `simp only` with explicit
  lemma lists. 0 `simp_all` now remain across all spec files.

*Quality reviews (2 PRs):*
- #1056: DeflateStoredCorrect + DeflateFixedCorrect — proof optimization
- #1062: DeflateDynamicCorrect + DeflateDynamicFreqs — proof optimization

*Self-improvement (1 PR):*
- #1066: Meditate — content pipeline template, hot file tracking, extraction heuristics

**Block-level composition matrix status (16/16 — COMPLETE):**

|  | Raw | RLE | CompLit | CompSeq |
|---|---|---|---|---|
| **Raw +** | done | done | done | done |
| **RLE +** | done | done | done | done |
| **CompLit +** | done | done | done | done |
| **CompSeq +** | done | done | done | done |

**Two-block content theorem coverage matrix (block / frame / API):**

| First \ Second | Raw | RLE | CompLit | CompSeq |
|---|---|---|---|---|
| **Raw** | B/F/A | B/F/A | B/—/— | B/—/— |
| **RLE** | B/F/A | B/F/A | B/—/— | B/—/— |
| **CompLit** | B/F/A | B/F/A | B/F/— | B/F/A |
| **CompSeq** | B/F/— | B/F/— | B/F/A | B/F/— |

B = block-level, F = frame-level, A = API-level. All 4 single-block types
are fully covered at all three levels.

Block-level: 16/16 complete. Frame-level: 12/16 covered (missing 4:
raw+compLit, raw+compSeq, rle+compLit, rle+compSeq — all raw/RLE-first +
compressed-second pairings). API-level: 8/16 covered (missing 8: the 4
frame-level gaps plus compLit+compLit, compSeq+raw, compSeq+rle,
compSeq+compSeq).

**The lifting pattern**: block-level → frame-level → API-level. Each level
composes the lower level's theorem with frame/API wrapping. Frame-level
theorems add `parseFrameHeader` + checksum handling. API-level theorems add
`decompressZstdWF` single-frame unwinding. The raw/RLE-first + compressed
gap at frame level is the bottleneck — these require lifting the block-level
compositions that include compressed-second blocks through `decompressFrame`.

**simp_all campaign status:** 0 `simp_all` remaining anywhere in `Zip/Spec/`.
Campaign fully complete: all instances converted to `simp only` with explicit
lemma lists or targeted alternatives. This is a significant proof quality
milestone — every simplifier call in the spec layer now declares its
dependencies explicitly.

**Summary:** The Zstd spec infrastructure now spans 6 files with 543
declarations: Fse (151), ZstdSequence (147), Zstd (102), ZstdHuffman (84),
XxHash (32), ZstdFrame (27). Total spec line count: 9,503 lines.

**10-PR batch (Mar 9–10): parsing completeness direction + API-level content completion + quality reviews:**

This batch introduced a new proof direction — parsing completeness ("if input
is well-formed, parsing succeeds") — and completed the two-block API-level
content coverage to 14/16 combinations.

*Track E two-block API-level content completion (3 PRs):*
- #1083: `decompressZstd_raw_then_compressed_lit_content` and
  `decompressZstd_rle_then_compressed_lit_content` (raw/RLE + compLit at API level)
- #1087/#1095: Merge conflict fixes for PR #1076 (compSeq+raw/RLE) and PR #1075
  (compSeq+raw/RLE at API level), plus ZstdFrame.lean API-level coverage audit
- #1101: `decompressZstd_raw_then_compressed_seq_content` and
  `decompressZstd_rle_then_compressed_seq_content` (raw/RLE + compSeq at API level)

*Track E API-level metadata validation (1 PR):*
- #1096: `decompressZstd_single_frame_contentSize` (when frame header declares
  contentSize = some n, output has exactly n bytes) and
  `decompressZstd_single_frame_checksum` (when frame has checksum enabled,
  xxHash64 of output matches stored checksum). These are characterizing
  properties — they relate frame metadata to decompressed content.

*Track E parsing completeness — new proof direction (3 PRs):*
- #1097: `parseBlockHeader_succeeds`, `decompressRawBlock_succeeds`,
  `decompressRLEBlock_succeeds` — first parsing completeness theorems. Prove
  that when the input has enough bytes, these functions return `.ok`. Used
  `bv_decide` for bitwise AND reasoning in block header catch-all case.
- #1108: `parseFrameHeader_succeeds` — proves frame header parsing succeeds
  when data has the correct magic number and enough bytes (via
  `frameHeaderMinSize` helper). Required `maxRecDepth 4096` and
  `maxHeartbeats 800000` for deeply nested monadic expressions.
- #1114: `parseCompressedLiteralsHeader_succeeds` and
  `parseLiteralsSection_succeeds_treeless` — compressed literals header and
  treeless literals section completeness.

*Quality reviews (2 PRs):*
- #1109: ZstdHuffman.lean audit — extracted `parseHuffmanTreeDescriptor_ok_elim`
  shared eliminator combining three separate case analyses (-62 lines, -4.3%).
- #1112: Fse.lean audit — extracted `decodeFseDistribution_ok_decompose` helper
  from 5 theorems sharing identical unfolding boilerplate (-47 lines, -2.4%).

*Merge conflict resolution (1 PR):*
- #1087: Resolved merge conflicts for raw/RLE+compSeq frame-level content

**Parsing completeness — concept and coverage:**
This is the converse of existing correctness theorems. Where correctness says
"if parsing returns `.ok`, the result satisfies properties P", completeness
says "if input satisfies conditions C, parsing returns `.ok`". Together they
give "well-formed input ↔ successful parsing". This is a prerequisite for
composing "well-formed Zstd frame → decompression succeeds" end-to-end.

Current parsing completeness coverage:
- `parseBlockHeader_succeeds` (pos + 3 ≤ data.size)
- `decompressRawBlock_succeeds` (pos + blockSize ≤ data.size)
- `decompressRLEBlock_succeeds` (pos + 1 ≤ data.size)
- `parseFrameHeader_succeeds` (magic number + enough bytes per header format)
- `parseCompressedLiteralsHeader_succeeds` (pos + headerSize ≤ data.size)
- `parseLiteralsSection_succeeds_treeless` (treeless path, sufficient bytes)

Remaining gaps: `parseLiteralsSection` Huffman-compressed path,
`parseSequencesHeader`, `resolveSingleFseTable` (FSE-compressed mode),
`resolveSequenceFseTables` composition, `decompressBlocks` loop, full frame.

**Two-block content theorem coverage matrix (block / frame / API):**

| First \ Second | Raw | RLE | CompLit | CompSeq |
|---|---|---|---|---|
| **Raw** | B/F/A | B/F/A | B/F/A | B/F/A |
| **RLE** | B/F/A | B/F/A | B/F/A | B/F/A |
| **CompLit** | B/F/A | B/F/A | B/F/— | B/F/A |
| **CompSeq** | B/F/A | B/F/A | B/F/A | B/F/— |

B = block-level, F = frame-level, A = API-level. All 4 single-block types
are fully covered at all three levels.

Block-level: 16/16 complete. Frame-level: 16/16 complete. API-level: 14/16
covered (missing 2: compLit+compLit and compSeq+compSeq — homogeneous
compressed pairs).

**Summary:** The Zstd spec infrastructure now spans 6 files with 563
declarations: Fse (152), ZstdSequence (147), Zstd (111), ZstdHuffman (86),
XxHash (32), ZstdFrame (35). Total spec line count: 10,377 lines.

**15-PR batch (Mar 10–11): completeness chain deepening + API-level content completion + review campaign:**

This batch deepened the parsing completeness chain to cover nearly every
sub-function in the Zstd decompression pipeline, completed the two-block
API-level content matrix to 16/16, and advanced the code quality review
campaign to 4 of 5 Zstd spec files.

*Track E parsing completeness (7 PRs):*
- #1121: `parseLiteralsSection_succeeds_compressed` — completeness for
  Huffman-compressed literals (litType=2), the most complex literal path
- #1123: `resolveSequenceFseTables_succeeds` — composed completeness
  theorem threading three `resolveSingleFseTable` calls
- #1130: `parseHuffmanTreeDescriptor_succeeds_fse` and
  `parseHuffmanWeightsFse_succeeds` — FSE-path Huffman tree descriptor
  completeness
- #1131: `BackwardBitReader_init_succeeds` — backward bitstream
  initialization completeness
- #1134: `resolveSingleFseTable_succeeds_fse` (FSE-compressed mode) and
  `decodeSequencesWF_succeeds_zero` (zero-sequence case)
- #1135: `decodeHuffmanLiterals_succeeds_single` and
  `decodeHuffmanLiterals_succeeds_four` — Huffman literal decoding
  completeness for both 1-stream and 4-stream modes
- #1138: `parseSequencesHeader_succeeds` and
  `parseSequencesHeader_succeeds_zero` — universal parsing completeness
  with byte0 case dispatch

*Track E characterization (1 PR):*
- #1144: `parseBlockHeader_lastBlock_eq`, `parseBlockHeader_blockType_eq`,
  `parseBlockHeader_blockSize_eq` — field characterization theorems proving
  each field equals specific bit ranges of the 24-bit header word

*Track E API-level content completion (1 PR):*
- #1151: `decompressZstd_two_compressed_literals_blocks_content` and
  `decompressZstd_two_compressed_sequences_blocks_content` — the final
  two API-level content theorems, completing the 16/16 matrix

*Quality reviews (4 PRs):*
- #1139: ZstdSequence.lean — proof body compression and refactoring
- #1145: ZstdSequence.lean — proof quality audit
- #1152: Zstd.lean — proof quality audit with `frame_from_blocks` tactic
  macro extraction and `parseBlockHeader_data_not_le` helper (−406 lines,
  −10.3%)
- #1153: ZstdFrame.lean — proof quality audit

*Housekeeping (2 PRs):*
- #1127: Meditate — parsing completeness maturity analysis, created
  `lean-parsing-completeness` skill (255 lines)
- #1146: Stale issue cleanup — closed 2 moot issues, removed stale labels

**Parsing completeness coverage (updated):**

| Function | Status |
|----------|--------|
| `parseBlockHeader` | done |
| `decompressRawBlock` | done |
| `decompressRLEBlock` | done |
| `parseFrameHeader` | done |
| `parseCompressedLiteralsHeader` | done |
| `parseLiteralsSection` (treeless) | done |
| `parseLiteralsSection` (compressed, litType=2) | done |
| `parseHuffmanWeightsDirect` | done |
| `parseHuffmanWeightsFse` | done |
| `parseHuffmanTreeDescriptor` (direct) | done |
| `parseHuffmanTreeDescriptor` (FSE) | done |
| `BackwardBitReader.init` | done |
| `decodeHuffmanLiterals` (1-stream, 4-stream) | done |
| `resolveSingleFseTable` (predefined/RLE/repeat/FSE) | done |
| `resolveSequenceFseTables` (composed) | done |
| `parseSequencesHeader` | done |
| `decodeSequencesWF` (zero-case) | done |
| `parseLiteralsSection` (raw/RLE) | gap |
| `decompressBlocksWF` (composed) | gap |
| `executeSequences` | gap |
| Frame-level composed | gap |

The completeness chain now covers 17 functions/paths. Remaining gaps:
`parseLiteralsSection` raw/RLE paths, `decompressBlocksWF` loop
composition, `executeSequences`, and full frame-level composition.

**Two-block content theorem coverage matrix (block / frame / API) — COMPLETE:**

| First \ Second | Raw | RLE | CompLit | CompSeq |
|---|---|---|---|---|
| **Raw** | B/F/A | B/F/A | B/F/A | B/F/A |
| **RLE** | B/F/A | B/F/A | B/F/A | B/F/A |
| **CompLit** | B/F/A | B/F/A | B/F/A | B/F/A |
| **CompSeq** | B/F/A | B/F/A | B/F/A | B/F/A |

All 16/16 combinations covered at all three levels (block, frame, API).
All 4 single-block types also fully covered at all three levels.

**Review campaign progress:** 4 of 5 Zstd spec files audited:
- ZstdHuffman.lean (#1109, #853) — extracted shared eliminators, −4.3%
- Fse.lean (#1112, #822) — extracted decomposition helpers, −2.4%
- ZstdSequence.lean (#1145, #1139) — proof compression + quality audit
- Zstd.lean (#1152) — tactic macro extraction, −10.3%
- ZstdFrame.lean (#1153) — proof quality audit
Remaining: XxHash.lean (previously audited at #807).

**Spec declaration count note:** Total spec declarations dropped from
1,819 to 1,793 despite net additions — the Zstd.lean review (#1152)
removed dead code and deduplicated helper lemmas more aggressively
than new theorems were added. The Zstd-specific declaration count rose
from 563 to 572 (net +9 new theorems).

**Summary:** The Zstd spec infrastructure now spans 6 files with 572
declarations: ZstdSequence (168), Fse (148), Zstd (106), ZstdHuffman (89),
ZstdFrame (37), XxHash (24). Total spec line count: 10,448 lines.

**12-PR batch (Mar 11–12): frame completeness chain + review campaign completion + field characterization:**

This batch deepened the parsing completeness chain from individual function
completeness to composed frame-level completeness for raw/RLE and compressed
blocks, completed the Zstd spec file review campaign (all 6 files audited),
and proved executeSequences loop completeness.

*Track E parsing completeness — raw/RLE literals (1 PR):*
- #1159: `parseLiteralsSection_succeeds_raw` and `parseLiteralsSection_succeeds_rle`
  — completeness for raw and RLE literal section parsing. Closes the gap
  identified in the previous batch's completeness coverage table.

*Track E composed frame-level completeness (4 PRs):*
- #1160: `skipSkippableFrame_succeeds` (skippable frame completeness) and
  `decompressZstd_succeeds_single_skippable` (composed skippable-frame
  completeness at WF level)
- #1161: `decompressBlocksWF_succeeds_single_raw` and
  `decompressBlocksWF_succeeds_single_rle` — composed block-loop completeness
  for single raw/RLE blocks (6-step pattern: typeVal derivation → parse result →
  field characterization → constraints → operation result → composition)
- #1168: `decompressBlocksWF_succeeds_single_compressed_zero_seq` (numSeq=0) and
  `decompressBlocksWF_succeeds_single_compressed_sequences` (numSeq>0) —
  composed block-loop completeness for single compressed blocks
- #1178: `decompressFrame_succeeds_single_raw` and
  `decompressFrame_succeeds_single_rle` — composed frame-level completeness for
  single raw/RLE blocks (composes `parseFrameHeader_succeeds` +
  `decompressBlocksWF_succeeds_single_*`)

*Track E sequence execution completeness (1 PR):*
- #1179: `executeSequences_loop_succeeds` and `executeSequences_succeeds` —
  completeness for the sequence execution loop under windowed mode. Added
  `OffsetsValidForLoop` predicate for per-step offset validity and
  `foldl_litLen_add` helper. 118 lines added to ZstdSequence.lean.

*Track E field characterization (1 PR):*
- #1164: `parseFrameHeader_frameHeaderDescriptor_eq`,
  `parseFrameHeader_windowDescriptor_eq`, `parseFrameHeader_dictionaryId_eq`,
  `parseFrameHeader_frameContentSize_eq` — proves each parsed field equals
  specific byte ranges of the raw header data

*Track E API-level content completion (1 PR):*
- #1151: `decompressZstd_two_compressed_literals_blocks_content` and
  `decompressZstd_two_compressed_sequences_blocks_content` — the final two
  API-level content theorems, completing the 16/16 two-block content matrix

*Quality reviews (3 PRs):*
- #1152: Zstd.lean proof quality audit — extracted `frame_from_blocks` tactic
  macro (replacing 19-line frame-unwinding epilogue in ~20 theorems) and
  `parseBlockHeader_data_not_le` helper (−406 lines, −10.3%)
- #1153: ZstdFrame.lean proof quality audit
- #1154: Removed dead `_hdict` hypotheses from 20 theorem signatures across
  2 Zstd spec files

*Housekeeping (2 PRs):*
- #1158: ZipForStd upstreaming readiness audit — assessed 4 files (52 lemmas)
  for Lean/Std PR readiness
- #1167: Closed duplicate issue #1163, updated ZstdFrame.lean content matrix
  docstring from "12/16" to "16/16"

*Self-improvement (1 PR):*
- #1171: Meditate — updated `lean-parsing-completeness` skill with 6-step
  composed completeness pattern, updated `lean-simp-tactics` with
  Bool/Prop bridging reference

**Parsing completeness coverage (updated):**

| Function | Status |
|----------|--------|
| `parseBlockHeader` | done |
| `decompressRawBlock` | done |
| `decompressRLEBlock` | done |
| `parseFrameHeader` | done |
| `parseCompressedLiteralsHeader` | done |
| `parseLiteralsSection` (treeless) | done |
| `parseLiteralsSection` (compressed, litType=2) | done |
| `parseLiteralsSection` (raw) | done |
| `parseLiteralsSection` (RLE) | done |
| `parseHuffmanWeightsDirect` | done |
| `parseHuffmanWeightsFse` | done |
| `parseHuffmanTreeDescriptor` (direct) | done |
| `parseHuffmanTreeDescriptor` (FSE) | done |
| `BackwardBitReader.init` | done |
| `decodeHuffmanLiterals` (1-stream, 4-stream) | done |
| `resolveSingleFseTable` (predefined/RLE/repeat/FSE) | done |
| `resolveSequenceFseTables` (composed) | done |
| `parseSequencesHeader` | done |
| `decodeSequencesWF` (zero-case) | done |
| `skipSkippableFrame` | done |
| `executeSequences` | done |
| `decompressBlocksWF` (single raw) | done |
| `decompressBlocksWF` (single RLE) | done |
| `decompressBlocksWF` (single compressed, zero-seq) | done |
| `decompressBlocksWF` (single compressed, with-seq) | done |
| `decompressFrame` (single raw) | done |
| `decompressFrame` (single RLE) | done |
| `decompressBlocksWF` (multi-block composed) | gap |
| `decompressFrame` (compressed blocks) | gap |
| `decompressZstd` (full end-to-end) | gap |

The completeness chain now covers 21 functions/paths (up from 17). Composed
completeness reaches the frame level for raw/RLE single-block frames. Remaining
gaps: multi-block composed completeness, compressed-block frame-level
completeness, and end-to-end `decompressZstd` completeness.

**Review campaign status (6/6 Zstd spec files — COMPLETE):**
- Fse.lean (#1112, #822, #918) — decomposition helpers, proof optimization
- ZstdHuffman.lean (#1109, #853, #908) — shared eliminators, dead code removal
- ZstdSequence.lean (#1145, #1139, #995) — proof compression + quality audit
- Zstd.lean (#1152) — tactic macro extraction, −10.3%
- ZstdFrame.lean (#1153) — proof quality audit
- XxHash.lean (#807) — quality pass

**Summary:** The Zstd spec infrastructure now spans 6 files with 634
declarations: ZstdSequence (181), Fse (154), Zstd (130), ZstdHuffman (99),
ZstdFrame (38), XxHash (32). Total spec line count: 11,136 lines.

**14-PR batch (Mar 12): two-block compressed completeness + write-side review campaign:**

This batch advanced Track E composed completeness into compressed block
territory (both at block and frame/API levels) while the review campaign
audited 8 DEFLATE write-side spec file pairs.

*Track E composed completeness — block level (3 PRs):*
- #1198: `decompressBlocksWF_succeeds_two_raw_blocks` and
  `decompressBlocksWF_succeeds_two_rle_blocks` — homogeneous two-block
  completeness for raw and RLE blocks
- #1205: `decompressBlocksWF_succeeds_raw_then_rle`,
  `decompressBlocksWF_succeeds_rle_then_raw` — heterogeneous raw/RLE
  two-block completeness
- #1220: `decompressBlocksWF_succeeds_raw_then_compressed_zero_seq` and
  `decompressBlocksWF_succeeds_rle_then_compressed_zero_seq` — first
  two-block completeness involving compressed blocks (raw/RLE + compressed
  zero-seq)

*Track E composed completeness — frame and API levels (2 PRs):*
- #1193: `decompressFrame_succeeds_single_compressed_zero_seq` and
  `decompressFrame_succeeds_single_compressed_sequences` — frame-level
  completeness for single compressed blocks (both zero-seq and with-seq)
- #1212: `decompressZstd_succeeds_single_compressed_zero_seq_frame` and
  `decompressZstd_succeeds_single_compressed_sequences_frame` — end-to-end
  API-level completeness for single compressed blocks. Composes
  `parseFrameHeader_succeeds` → `decompressFrame_succeeds_*` →
  `decompressZstd_single_frame`.

*DEFLATE write-side review campaign (7 PRs):*
- #1189: DecodeCorrect + DecodeComplete — bare `simpa` conversion,
  dead hypothesis removal
- #1194: HuffmanCorrect — proof audit, no changes needed
- #1195: GzipCorrect + ZlibCorrect + DeflateRoundtrip (695 lines) —
  redundant `have` inlining, proof optimization (−18 lines)
- #1199: BitstreamCorrect + BitstreamComplete — proof audit
- #1202: DeflateDynamicHeader + DeflateDynamicEmit (706 lines) —
  merged consecutive `simp only` pairs, inlined dead `have` bindings
- #1206: BitstreamWriteCorrect + BitWriterCorrect — proof audit
- #1209: DeflateEncode + DeflateEncodeProps (1021 lines) — merged
  consecutive `rw` calls, removed unnecessary case split, dead variable
- #1214: DeflateEncodeDynamic + DeflateEncodeDynamicProps (1141 lines) —
  replaced verbose `List.reduceReplicate` pattern with `List.length_replicate`
- #1215: DynamicTreesCorrect + DynamicTreesComplete (1305 lines) — 2 bare
  `simpa` → `simpa only`, 1 dead hypothesis removed. Discovered bare simp
  count from issue was inflated — all `simp` calls already used `simp only`.

**Composed completeness coverage (updated):**

| Function | Status |
|----------|--------|
| `decompressBlocksWF` (two raw) | done |
| `decompressBlocksWF` (two RLE) | done |
| `decompressBlocksWF` (raw+RLE, RLE+raw) | done |
| `decompressBlocksWF` (raw/RLE + compressed zero-seq) | done |
| `decompressFrame` (single compressed zero-seq) | done |
| `decompressFrame` (single compressed with-seq) | done |
| `decompressZstd` (single compressed zero-seq frame) | done |
| `decompressZstd` (single compressed with-seq frame) | done |
| `decompressBlocksWF` (raw/RLE + compressed with-seq) | gap |
| `decompressBlocksWF` (compressed + raw/RLE) | gap |
| `decompressFrame` (two-block compressed) | gap |
| `decompressZstd` (full end-to-end multi-block) | gap |

The composed completeness chain now reaches the API level for single
compressed blocks (both zero-seq and with-sequences). Two-block
completeness covers all raw/RLE combinations and the first mixed
raw/RLE + compressed pairings. Remaining gaps: compressed-first
two-block completeness, and composing multi-block completeness to
frame and API levels.

**Review campaign progress:** The write-side DEFLATE review campaign
covered 8 file pairs (4,868 lines total). All files are now clean:
0 bare `simp`, 0 bare `simp_all`, no dead hypotheses. The campaign
confirmed that most files had already reached review quality from
previous passes — the main value was verification rather than
remediation.

**Summary:** The Zstd spec infrastructure now spans 6 files with 454
declarations: Zstd (117), ZstdSequence (97), ZstdHuffman (88),
Fse (87), ZstdFrame (39), XxHash (26). Total spec line count: 11,879 lines.

**17-PR batch (Mar 12): completeness matrix expansion + DEFLATE review deepening:**

This batch expanded the two-block composed completeness ("succeeds") matrix
across all three levels (block, frame, API), primarily filling in compressed
block combinations. Concurrently, 7 review PRs deepened the DEFLATE proof
quality campaign into previously unaudited spec files.

*Track E composed completeness — block level (4 PRs):*
- #1227: `decompressBlocksWF_succeeds_compressed_zero_seq_then_raw` and
  `decompressBlocksWF_succeeds_compressed_zero_seq_then_rle` — compressed
  zero-seq first + raw/RLE second
- #1248: `decompressBlocksWF_succeeds_compressed_sequences_then_raw` and
  `decompressBlocksWF_succeeds_compressed_sequences_then_rle` — compressed
  sequences first + raw/RLE second
- #1256: `decompressBlocksWF_succeeds_compressed_zero_seq_then_compressed_zero_seq`
  and `decompressBlocksWF_succeeds_compressed_zero_seq_then_compressed_sequences`
  — compressed-to-compressed pairs
- #1281: `decompressBlocksWF_succeeds_compressed_sequences_then_compressed_zero_seq`
  and `decompressBlocksWF_succeeds_compressed_sequences_then_compressed_sequences`
  — remaining compressed-to-compressed pairs (conflict fix for #1264)

*Track E composed completeness — frame level (3 PRs):*
- #1231: `decompressFrame_succeeds_raw_then_compressed_zero_seq` and
  `decompressFrame_succeeds_rle_then_compressed_zero_seq` — raw/RLE first
  + compressed zero-seq second
- #1242: `decompressFrame_succeeds_compressed_zero_seq_then_raw` and
  `decompressFrame_succeeds_compressed_zero_seq_then_rle` — compressed
  zero-seq first + raw/RLE second
- #1277: `decompressFrame_succeeds_compressed_sequences_then_raw` and
  `decompressFrame_succeeds_compressed_sequences_then_rle` — compressed
  sequences first + raw/RLE second (conflict fix for #1188/#1257)

*Track E composed completeness — API level (3 PRs):*
- #1252: `decompressZstd_succeeds_rle_then_rle_frame`,
  `decompressZstd_succeeds_rle_then_raw_frame`,
  `decompressZstd_succeeds_rle_then_compressed_zero_seq_frame` — rle-first
  frames at API level
- #1269: `decompressZstd_succeeds_two_raw_frame`,
  `decompressZstd_succeeds_raw_then_rle_frame`,
  `decompressZstd_succeeds_raw_then_compressed_zero_seq_frame` — raw-first
  frames at API level (conflict fix for #1253)
- #1277: `decompressZstd_succeeds_single_raw_frame` and
  `decompressZstd_succeeds_single_rle_frame` — single raw/RLE at API level

*Quality reviews — DEFLATE spec files (7 PRs):*
- #1230: LZ77.lean + LZ77Lazy.lean — proof quality audit
- #1234: HuffmanKraft.lean + HuffmanTheorems.lean — proof quality audit
- #1243: ZstdHuffman.lean — proof quality audit (refactoring)
- #1244: ZstdFrame.lean — proof quality audit
- #1258: DeflateStoredCorrect.lean + DeflateFixedCorrect.lean — proof quality audit
- #1262: LZ77NativeCorrect.lean + EmitTokensCorrect.lean — proof quality audit
- #1278: DeflateSuffix.lean + BinaryCorrect.lean — proof quality audit

*Self-improvement (1 PR):*
- #1226: Meditate — 17-PR batch skill updates

**Two-block composed completeness ("succeeds") matrix — current state:**

Block-level (14/16):

|  | Raw | RLE | CompZS | CompSeq |
|---|---|---|---|---|
| **Raw +** | done | done | done | — |
| **RLE +** | done | done | done | — |
| **CompZS +** | done | done | done | done |
| **CompSeq +** | done | done | done | done |

Missing at block level: raw+comp_sequences and rle+comp_sequences.

Frame-level (10/16 two-block + 4 single):

|  | Raw | RLE | CompZS | CompSeq |
|---|---|---|---|---|
| **Raw +** | done | done | done | — |
| **RLE +** | done | done | done | — |
| **CompZS +** | done | done | — | — |
| **CompSeq +** | done | done | — | — |

Missing at frame level: all 4 compressed-to-compressed pairs plus
raw+comp_sequences and rle+comp_sequences.

API-level (6/16 two-block + 5 single):

|  | Raw | RLE | CompZS | CompSeq |
|---|---|---|---|---|
| **Raw +** | done | done | done | — |
| **RLE +** | done | done | done | — |
| **CompZS +** | — | — | — | — |
| **CompSeq +** | — | — | — | — |

The API level covers raw/RLE-first pairings only. Compressed-first and
compressed-to-compressed API-level completeness remains to be lifted
from the frame level.

**Review campaign:** This batch extended the DEFLATE proof quality review
to 7 additional file pairs, including LZ77 (greedy + lazy), Huffman
characterizing properties, and several correctness files. These are
cumulative with the previous write-side campaign (#1189–#1215) and the
Zstd spec review campaign (all 6 files). The codebase now has extensive
review coverage across both DEFLATE and Zstd spec layers.

**Summary:** The Zstd spec infrastructure now spans 6 files with 501
declarations: Zstd (145), ZstdSequence (104), Fse (95), ZstdHuffman (86),
ZstdFrame (48), XxHash (23). Total spec line count: 14,081 lines.

**8-PR batch (Mar 12): API-level succeeds near-completion + review campaign deepening:**

This batch advanced the API-level succeeds matrix to 19/21 and continued
the DEFLATE proof quality review campaign across 4 more spec file pairs.

*Track E API-level succeeds (3 PRs):*
- #1296: Merge conflict fix for frame-level comp_zero_seq + compressed
  block theorems, unblocking downstream API-level lifting
- #1306: `decompressZstd_succeeds_compressed_sequences_then_raw_frame` and
  `decompressZstd_succeeds_compressed_sequences_then_rle_frame` — compressed
  sequences first + raw/RLE at API level
- #1320: `decompressZstd_succeeds_raw_then_compressed_sequences_frame`,
  `decompressZstd_succeeds_rle_then_compressed_sequences_frame`,
  `decompressZstd_succeeds_compressed_sequences_then_compressed_zero_seq_frame`,
  `decompressZstd_succeeds_two_compressed_sequences_frame` — 4 compressed-
  sequences two-block pairs at API level, derived from content theorems

*Quality reviews — DEFLATE spec files (4 PRs):*
- #1300: DeflateDynamicCorrect + DeflateDynamicFreqs — proof optimization
- #1304: InflateLoopBounds + InflateRawSuffix — proof quality audit
  (conflict fix for #1276)
- #1314: DynamicTreesCorrect + DynamicTreesComplete — minimal changes,
  files already at review quality
- #1316: BitReaderInvariant + BitWriterCorrect — proof quality audit

*Infrastructure (1 PR):*
- #1307: Meditate — merge conflict frequency analysis, completeness matrix
  scaling patterns

*Housekeeping (3 PRs):*
- #1321: Triage stale issue #1318 (work already merged via #1306)
- #1325: Recovered proof-review-checklist patterns from conflicted PR #1312
- #1326: Recovered `bfinal_suffix_dispatch` tactic macro from PR #1312

**Two-block composed completeness ("succeeds") matrix — current state:**

API-level (19/21):

|  | Raw | RLE | CompZS | CompSeq |
|---|---|---|---|---|
| **Raw +** | done | done | done | done |
| **RLE +** | done | done | done | done |
| **CompZS +** | done | done | — | — |
| **CompSeq +** | done | done | done | done |

Missing at API level: czs+czs and czs+cs. Both exist at frame level
(from `decompressFrame_succeeds_compressed_zero_seq_then_compressed_*`
theorems in Zstd.lean) and need only the standard API-level lift.

Frame-level completeness is 16/16 for two-block combinations plus all
4 single-block types. Block-level completeness is 16/16.

**Review campaign progress:** The DEFLATE proof quality review campaign
now covers all 49 spec files across multiple passes. This batch audited
4 DEFLATE spec file pairs (BitReaderInvariant, BitWriterCorrect,
InflateLoopBounds, InflateRawSuffix, DeflateDynamicCorrect,
DeflateDynamicFreqs, DynamicTreesCorrect, DynamicTreesComplete).
Most files required only minimal changes, confirming convergence toward
review-complete quality.

**Summary:** The Zstd spec infrastructure now spans 6 files with 491
declarations: Zstd (137), ZstdSequence (97), Fse (87), ZstdHuffman (88),
ZstdFrame (56), XxHash (26). Total spec line count: 15,091 lines.

**5-PR batch (Mar 12): review campaign completion + Track D1 benchmark:**

This batch completed the DEFLATE proof quality review campaign to cover
all 49 spec files and added the first DEFLATE decompression throughput
benchmark.

*Quality reviews — final DEFLATE spec files (4 PRs):*
- #1327/#1328: HuffmanCorrect + HuffmanCorrectLoop proof quality audit
  (with merge conflict rebase)
- #1332: Deflate.lean proof quality audit
- #1333: Final spec file batch — Adler32, Crc32, Huffman, DeflateFixedTables.
  These were the last 4 unreviewed DEFLATE spec files. With this PR, all
  49 spec files in `Zip/Spec/` have been audited at least once.

*Track D1 (1 PR):*
- #1339: DEFLATE decompression throughput benchmark (`ZipTest/DeflateBench.lean`).
  Measures native vs FFI inflate/gzip/zlib decompression across 4 data
  patterns (constant, cyclic, random, text) and 4 sizes (1KB–1MB).
  Adds the first Track D infrastructure since the compression benchmark
  suite (#399).

**Review campaign — project-wide completion:**

All 49 spec files in `Zip/Spec/` have now been audited at least once
across the review campaign (spanning ~30 review PRs from #369 to #1333).
The campaign covered:
- 43 DEFLATE spec files (checksums, bitstream, Huffman, LZ77, inflate,
  deflate encode/decode, dynamic trees, framing, roundtrip)
- 6 Zstd spec files (Fse, XxHash, ZstdHuffman, ZstdSequence, Zstd,
  ZstdFrame)

Quality metrics at campaign completion:
- 0 standalone bare `simp` across all spec files
- 0 bare `simp_all` across DEFLATE spec files
- 5 bare `simp_all` remaining in Zstd.lean only (post-campaign additions
  from Track E completeness work)
- Multiple files saw significant proof compression (Zstd.lean −10.3%,
  ZstdHuffman.lean −4.3%, Fse.lean −2.4%)

The review campaign reached diminishing returns — most files in the final
batch required minimal or no changes, confirming convergence toward
stable proof quality.

**11-PR batch (Mar 12–13): WellFormedBlocks all-type induction + review campaign + benchmarks:**

This batch generalized the WellFormedBlocks induction predicate to all block
types, expanded block-level two-block succeeds coverage, continued the Zstd
proof quality review campaign, and consolidated benchmark infrastructure.

*Track E feature PRs (3):*
- #1361: `WellFormedSimpleBlocks` induction predicate for raw/RLE N-block
  sequences
- #1372: `WellFormedBlocks` generalized to all 8 block types (raw, RLE,
  compressed_literals, compressed_sequences × last/non-last). **Milestone**:
  universal induction predicate for arbitrary block sequences.
- #1382: Block-level two-block succeeds for raw/RLE + compressed_sequences
  combinations (closes #1232)

*Proof quality reviews (3 PRs):*
- #1359: Zstd.lean foundational sections audit — proof compression
- #1380: Zstd.lean step theorems + raw/RLE two-block audit
- #1383: Fse.lean proof quality audit — compressed proof patterns

*Proof compression (1 PR):*
- #1358: GzipCorrect + ZlibCorrect proof pattern compression

*Infrastructure (3 PRs):*
- #1356: Recovered skill updates from superseded PR #1351
- #1368: Meditate — two-block completion + review campaign transition
- #1377: Rebased ZstdFrame.lean review PRs (#1366 + #1371), net −149 lines

*Track D (1 PR):*
- #1357: Benchmark consolidation — merged NativeCompressBench + NativeScale
  into unified Benchmark.lean, added Zstd multi-iteration support

Bare simp_all in Zstd.lean: 5 → 2. Zstd spec lines: 15,091 → 15,811.

**14-PR batch (Mar 13): proven-bounds campaign + Zstd splitting + WellFormedBlocks completion:**

This batch launched the proven-bounds campaign (converting `[i]!` runtime
bounds checks to proven-bounds `[i]` access), split Spec/Zstd.lean into
three files, and completed the WellFormedBlocks/WellFormedSimpleBlocks
induction predicates at frame and API levels.

*Proven-bounds campaign (5 PRs):*
- #1414: Deflate.lean — encoding helpers + constant tables (22 patterns)
- #1417: DEFLATE length/distance tables — 4 patterns in `decodeHuffman.go`
  with `@[simp]` size lemmas for all 5 constant tables
- #1426: ZstdHuffman.lean — 13 `data[pos + i]!` → `data[pos + i]'(by omega)`
  in `parseCompressedLiteralsHeader`
- #1427: Merge conflict fix for ZstdFrame.lean proven-bounds PR #1413
- #1428: ZstdSequence.lean — data byte reads + history array access

*Zstd spec splitting (1 PR):*
- #1409: Extracted ZstdBase.lean (542 lines, L1: base predicates) and
  ZstdBlockLoop.lean (493 lines, L2: block loop specs) from the 6011-line
  Spec/Zstd.lean. Spec/Zstd.lean remains at 6011 lines — further splitting
  planned.

*Track E WellFormedBlocks completion (3 PRs):*
- #1393: API-level `WellFormedBlocks` succeeds (full predicate)
- #1398, #1401: Frame/API-level `WellFormedSimpleBlocks` succeeds,
  including 3-block corollary (raw → RLE → raw)

*Quality reviews (3 PRs):*
- #1394: ZstdSequence.lean proof quality audit
- #1397: Zstd.lean file organization — splitting plan
- #1402: Zstd.lean proof quality audit (frame characterization + compressed
  two-block) — eliminated 2 bare `simp_all`

*Self-improvement (1 PR):*
- #1420: Meditate — created `proven-bounds` skill, assessed Zstd splitting
  readiness

**Proven-bounds campaign status:** 149 `]!` remaining across 10 native files.
Largest concentrations: Deflate.lean (53), ZstdSequence.lean (29), Fse.lean (18),
ZstdHuffman.lean (14), Gzip.lean (12), DeflateDynamic.lean (11). Files fully
converted: Crc32.lean, Adler32.lean, BitWriter.lean.

**Remaining:**
- Zstd.lean at 6011 lines needs further splitting (plan: #1432)
- Prove remaining sorry stubs: 4 in XxHash (UInt64 test vectors too
  expensive for kernel evaluation — intractable without native_decide)
- Proven-bounds campaign: 149 `]!` across 10 native files
- Composed completeness: lift czs+czs and czs+cs to API level (19→21),
  compose multi-block completeness to end-to-end `decompressZstd`
- Content preservation campaign: extend to N-block frames and compressed
  block content (with sequences)
- Spec-level decoder with correctness proofs (algorithmic correspondence
  between native and spec decoder, following the DEFLATE B3 pattern)
- Compressor + roundtrip proof

**31-PR batch (Mar 13 – Apr 18): proven-bounds continuation + lean-zip-common/lean-zstd split + Lean 4.29.1 CI fixes (summarize #1511):**

This batch is dominated by two strands: the proven-bounds campaign
(converting `[i]!` runtime bounds checks to statically-proven access)
and a structural split of the repository into three repos. See
`progress/20260418T081059Z_10fac7ec.md` for the full PR breakdown.

*The structural change (#1487, 2026-03-27):* `lean-zip` was split into
three repositories:

- [lean-zip-common](https://github.com/kim-em/lean-zip-common) — shared
  utilities (Binary, Handle, BitReader, ZipForStd, io_ffi.c)
- [lean-zstd](https://github.com/kim-em/lean-zstd) — Zstandard
  decompression (13 spec files + FSE + XxHash + frame decoder +
  Huffman + sequences)
- `lean-zip` (this repo) — zlib/DEFLATE/Gzip/ZIP/Tar with all specs and
  proofs

39 files were moved out; a `require zipCommon from git` pin replaced
them. `Zip/Spec/` dropped from 51 files to 42.

*Proven-bounds campaign (18 PRs)*: pre-split coverage in
ZstdHuffman/ZstdSequence/Fse/BitReader/Binary (now in sibling repos)
plus DEFLATE-side work in Deflate.lean (#1446 emitTokens, #1500
canonicalCodes/findTableCode/insertLoop), DeflateDynamic.lean (#1450,
#1498), Inflate.lean (#1449, #1451), Tar.lean (#1459), and
Gzip.lean (#1492). A cross-file consistency audit (#1431) kept
conventions aligned.

*Spec file splitting (5 PRs, pre-split)*: Spec/Zstd.lean and
ZstdFrame.lean were modularized in-repo just before the #1487 split
(#1438 ZstdTwoBlock extraction; #1460/#1466 splitting assessments;
#1473 ZstdFrameBase extraction; #1479 three-way Spec/Zstd.lean split).
The resulting files migrated to lean-zstd.

*Other PRs (4)*: #1468 Track C1 fuel-dependent Zstd audit, #1491
closing stale Zstd PRs post-split, #1497 Track E ZIP local-header span
validation, #1501 InflateCorrect + InflateComplete proof-quality audit,
#1502 localized Array.set! monotonicity lemma.

*Toolchain / CI (3 PRs)*: Lean 4.29.1 introduced a Lake "compiled
configuration invalid" regression on `lake exe test`. #1495 switched CI
to `lake test`; #1506 pinned zipCommon + added `lake reconfigure` in
CI; #1499 renamed call sites to upstream-compatible lemma names
(`Nat.or_two_pow_eq_add_of_lt`, `List.getElem_foldl_set_*`,
`ByteArray.getElem!_push_lt`) and pinned zipCommon to cleanup commit
`89204d6`.

*Carry-over*: 48 `]!` remaining in Native/, all in two files —
`Zip/Native/Deflate.lean` (42, LZ77 matcher family: tracked in new
issues #1508/#1509/#1510 splitting into three clusters) and
`Zip/Native/DeflateDynamic.lean` (6, after PR #1513 merged mid-
summarize addressed 2 of the 8 from #1505). Three diag PRs (#1496,
#1503, #1507) remain open as instrumentation for the Lake/Lean 4.29.1
regression.

Quality metrics: 0 sorries; `Zip/Spec/` at 42 files, 20,151 LOC
(DEFLATE-only — Zstd's ~16 kLOC of spec work migrated to lean-zstd);
`Zip/Native/` at 7 files, 1,603 LOC. Toolchain: `v4.29.1`.

**10-PR batch (Apr 18): proven-bounds campaign completion (summarize #1537):**

This batch closes out the DEFLATE-side proven-bounds campaign carried
forward from the batch above. Eight feature PRs converted every
remaining `]!` runtime-bounds access in the LZ77 matcher family of
`Zip/Native/Deflate.lean` (clusters A/B/C1/C2/C3 — spanning the
recursive and iterative variants of `lz77Greedy` and `lz77Lazy` plus
their `where`-local `hash3`/`countMatch`/`trailing`/`mainLoop`/
`updateHashes` helpers) and in the two remaining clusters of
`Zip/Native/DeflateDynamic.lean` (cluster A `emitTokensWithCodes`;
cluster B `tokenFreqs.go`). End-point: `]!` in
`Zip/Native/Deflate.lean` 24 → 0 and `Zip/Native/DeflateDynamic.lean`
6 → 0 as runtime reads — the only remaining `]!` in `Deflate.lean`
(2 occurrences) live inside comments, with no runtime-bounded
accesses left in the compressor.

*Cluster pattern that landed.* The matcher plumbing grew three
signature-level size invariants threaded from the top-level call down
through each `where`-local helper:
`hht : hashTable.size = hashSize`, `hhv : hashValid.size = hashSize`,
and `hhs : 0 < hashSize` for the hash-table reads;
`h1 : p1 + maxLen ≤ data.size` + `h2 : p2 + maxLen ≤ data.size` for
the `countMatch` byte-compare loops; and `h : pos + 2 < data.size` on
each local `hash3`. The iterative (`lz77GreedyIter`/`lz77LazyIter`,
PRs #1517 and #1529) and recursive (`lz77Greedy`/`lz77Lazy`,
PRs #1532 and #1524 + #1535) variants each required their own
size-preservation lemma pair —
`lz77{Greedy,Lazy}_updateHashes_{fst,snd}_size`, four in total —
because `updateHashes` is private to each `where`-block and cannot be
shared without a larger refactor. Dead-branch fallbacks for the outer
`hht`/`hhv` failure are byte-identical across the iterative and lazy
variants (emit one literal, advance `pos + 1`); the inner lookahead
guard in `mainLoop_lazy` takes the lookahead-dropped branch and
commits the already-found match. The `emitTokensWithCodes` dead
fallback recurses without emitting — ruled out by
`nativeFindLengthCode_idx_bound` + `hlit_size`, retained only to keep
the elaborator happy.

*Skill-file deltas (#1530).* Appended two pitfalls to
`.claude/skills/proven-bounds/SKILL.md`, bringing the numbered list
from 7 to 9. Pitfall #8 records that `unless` rebinds the threaded
`mut` state even when the body does not write to it, so bounds
captured before `unless` no longer apply to reads after; remedy is to
read all fields up front inside the `if h : pos + N ≤ data.size`
guard (pattern used in the Gzip decompressor rewrite). Pitfall #9
records that `List.pmap` (and other `@[expose]` combinators) cause
`rfl`-proved specs to unfold the skeleton simultaneously on each side
and blow the kernel recursion limit; remedy is a named-helper wrapper
(`freqsToPairs` in `DeflateDynamic.lean`).

*Proof-quality review (#1536).* Audited the six feature PRs landed
across the clusters. No cross-cluster renames rose to the "wrap it"
bar — hypothesis names (`hht`, `hhv`, `hhs`, `hlit`, `hdist`) overload
by scope in ways that are consistently scope-disambiguated.
`getElem!_le_set!_incr` was the sole repeated spec-cascade idiom that
justified a local helper lemma, and #1526 already introduced it. The
four size-preservation lemmas in `Zip/Spec/DeflateFixedCorrect.lean`
(`lz77{Greedy,Lazy}_updateHashes_{fst,snd}_size`) remain independent
rather than being collapsed, because `lz77Greedy.updateHashes` and
`lz77Lazy.updateHashes` are private to their respective `where`-blocks
— unification would require a separate refactor hoisting
`updateHashes` to top-level. Review landed doc-only (no cleanup
commit), per the issue's explicit opt-out.

*Self-improvement (#1516).* Post-proven-bounds-campaign meditate
captured the clustering heuristic that split the Deflate matcher work
into sub-issues #1508/#1509/#1510, and recorded the `]!` distribution
across `Zip/Native/` that scoped this batch.

Quality metrics: 0 sorries across `Zip/`;
`Zip/Native/Deflate.lean` and `Zip/Native/DeflateDynamic.lean` both at
0 runtime `]!` reads (2 comment-only occurrences remain in the
former); `Zip/Native/` at 7 files, 1,780 LOC (up from 1,603 —
+177 LOC from the threaded size hypotheses and dead-branch
fallbacks); `Zip/Spec/` at 42 files, 20,516 LOC (up from 20,151 —
+365 LOC across `DeflateFixedCorrect.lean`, `DeflateDynamicEmit.lean`,
`DeflateDynamicFreqs.lean`, `DeflateDynamicCorrect.lean`,
`LZ77NativeCorrect.lean`); toolchain `v4.29.1`.

*Track E carry-over.* #1531 and #1533 (ZIP64
oversized-compressedSize / oversized-uncompressedSize malformed-
fixture features) remain unclaimed Priority-0 work for the next
planner.

**11-PR batch (Apr 18 – Apr 21): Track E security-audit cluster (summarize #1563):**

This batch is the first concentrated sweep of the Track E security-audit
sub-roadmap. No DEFLATE / Huffman / LZ77 code path changed; no spec file
was touched; `grep -rc sorry Zip/` stayed at `0` throughout. The work is
entirely on the trust boundary — parser guards, malformed fixtures,
regression tests, and boundary documentation. The library's
cryptographic and compression kernels are unchanged; what moved is how
much of the attack surface is now explicitly guarded, tested, or
catalogued. The corresponding Track E checklist is
[`plans/track-e-current-audit-checklist.md`](plans/track-e-current-audit-checklist.md);
this summary reads side-by-side with it rather than restating the full
matrix.

*Priority 0 — ZIP unchecked-size + local-span audit (closed).*

- #1543 — ZIP64 oversized-`compressedSize` malformed fixture
  (`testdata/zip/malformed/oversized-zip64-compressed-size.zip`,
  134 B; fires `assertSpanInFile`'s `"local data span"` branch with
  a claimed exabyte `compressedSize`).
- #1544 — ZIP64 oversized-`uncompressedSize` malformed fixture
  (`testdata/zip/malformed/oversized-zip64-uncompressed-size.zip`,
  134 B; the exabyte claim is caught by the post-read
  `"size mismatch"` guard rather than a span check — method-0 stored
  payload, so `fileData.size` never matches `entry.uncompressedSize`).
  A later strict ZIP64 local-extra parse (landed in #1554) now rejects
  this fixture earlier with `truncated ZIP64 local extra field`; the
  fixture's assert was updated to reflect the stricter check.
- #1554 — Central-directory vs. local-header consistency audit.
  `Archive.readEntryData` now parses the remaining LH fields
  (`flags`, `method`, `crc`, `stdLocalCompSize`, `stdLocalUncompSize`,
  ZIP64 local-extra block) and hard-errors on any CD/LH mismatch on
  method / compressedSize / uncompressedSize / crc, except when flag
  bit 3 (data-descriptor) legitimately leaves LH crc/sizes at zero.
  Covered by
  `testdata/zip/malformed/cd-lh-method-mismatch.zip` and
  `cd-lh-size-mismatch.zip` (both deterministic, built by
  `scripts/build-cd-lh-mismatch.py`). `parseZip64Extra` is reused for
  the LH case; a follow-up could thread `Entry.flags` for a bit-11
  UTF-8 check.

*Priority 1 — Tar partial-decoder audit (closed).*

- #1545 — Malformed PAX extended-header fixtures
  (`testdata/tar/malformed/pax-oversized-length.tar`,
  `pax-truncated-record.tar`, `pax-invalid-utf8-key.tar`,
  `pax-invalid-utf8-value.tar`, `pax-inconsistent-length.tar` —
  each 2048 B; built deterministically by
  `scripts/build-pax-malformed-fixtures.lean`). Every malformation
  was silently skipped by existing `parsePaxRecords` guards; no
  hardening needed, but the regression pins behaviour.
- #1546 — Malformed GNU long-name / long-link fixtures
  (`testdata/tar/malformed/gnu-longname-truncated.tar`,
  `gnu-longname-no-terminator.tar`, `gnu-longname-invalid-utf8.tar`,
  `gnu-longlink-truncated.tar`; built by
  `scripts/build-gnu-long-malformed-fixtures.lean`). Invalid UTF-8
  in long-names falls through `String.fromUTF8?` to a Latin-1
  fallback, which is now pinned by test rather than left implicit.
- #1550 — `String.fromUTF8!` callsite audit in `Zip/Tar.lean`. Three
  panicking raw-byte truncations in `buildPaxEntry` and `create`
  replaced by `Tar.truncateUTF8` (codepoint-aware); the two remaining
  `fromUTF8!` callsites in `splitPath` now carry an explanatory
  comment (split is at an ASCII `'/'` byte, safe by construction).
  Regression coverage in new test module `ZipTest/TarPathTruncation.lean`.
- #1555 — Symlink / hardlink extraction policy documented explicitly.
  Per-typeflag policy is now in both the `Tar.extract` docstring and
  `SECURITY_INVENTORY.md`'s new
  *"Symlink/hardlink extraction policy"* subsection: `typeRegular` /
  `typeDirectory` go through `Binary.isPathSafe`; `typeSymlink`
  validates `linkname` for absolute / backslash / `..` components
  before `createSymlink`; `typeHardlink` (now a named constant,
  `0x31`) and all other typeflags (devices, FIFO, GNU sparse) silently
  skip — the payload is consumed but no filesystem entry is created.
  New fixtures `testdata/tar/security/symlink-absolute.tar` and
  `hardlink-outside.tar` plus the previously orphaned
  `backslash-slip.tar` now have asserts in `ZipTest/TarFixtures.lean`;
  built by `scripts/build-symlink-hardlink-malformed-fixtures.lean`.

*Priority 2 — Public decompression limit policy (items 1–3 closed,
item 4 open).*

- #1556 — Public decompression limit policy inventory. Added a new
  *"Decompression Limit Inventory"* section to `SECURITY_INVENTORY.md`
  cataloguing every public decompression / extraction API (16 entry
  points across FFI + native + archive + tar) with *Entry point /
  Parameter / Default / Semantics of 0 / Notes* columns. Flagged four
  known inconsistencies (FFI whole-buffer vs. streaming cap defaults;
  `Archive.readEntryData` silent `0 → 256 MiB` upgrade on the native
  backend; native-decoder 1 GiB vs. 256 MiB default disagreement;
  `maxCentralDirSize` finite but `maxEntrySize` unlimited mixed
  semantics) and proposed a six-point *"Recommended policy"* with
  placeholder numbers (256 MiB FFI whole-buffer, 1 GiB archive
  per-entry, streaming FFI gains a cap, native-decoder defaults
  normalised). No `Zip/*.lean` changes — inventory + policy proposal
  only.
- #1560 — Bomb-limit regression tests for `Gzip.decompress`,
  `RawDeflate.decompress`, and `Zip.Native.GzipDecode.decompress`
  (added to `ZipTest/Gzip.lean`, `ZipTest/RawDeflate.lean`,
  `ZipTest/NativeGzip.lean`). Each test compresses ~6200 B of
  `mkTestData`, then calls the decoder with `maxDecompressedSize := 10`
  (or `maxOutputSize := 10` for native) and asserts the error
  substring (`"exceeds limit"` for FFI, `"exceeds maximum size"` for
  native — the substrings diverge because the native path errors
  originate in `Zip/Native/Inflate.lean`, not in the C code).
- #1561 — Bomb-limit regression tests for `Archive.extract`,
  `Archive.extractFile`, `Tar.extract`, and `Tar.extractTarGzNative`
  (added to `ZipTest/Archive.lean` and `ZipTest/Tar.lean`). Each test
  builds the bomb in-memory via `mkTestData` + `Tar.create` /
  `Gzip.compress` rather than committing new fixtures. The `Tar`
  test uses `(maxEntrySize := 0) (maxOutputSize := 10)` and asserts
  `"exceeds maximum size"` — the gzip-decode budget fails before
  per-entry limits are reached.
- #1562 — Reconcile audit checklist + `SECURITY_INVENTORY.md`
  missing-work lists. Checklist line for each of the six items closed
  above now carries its closing PR number. `SECURITY_INVENTORY.md`'s
  ZIP / Tar "Missing work" lists shrunk to genuinely-open items
  (bounded-read lemmas on the ZIP side, none on the tar side);
  completed items moved to a new per-subsystem *"Recent wins"* bullet
  list referencing the closing PRs. Documentation-only — no code
  changes.

*Test-fixture inventory added in this batch.* New fixtures landed in
three families, all built by committed deterministic builders
(`scripts/build-*`) so they can be regenerated byte-stable:

- `testdata/zip/malformed/` — 4 new: `oversized-zip64-compressed-size.zip`,
  `oversized-zip64-uncompressed-size.zip`, `cd-lh-method-mismatch.zip`,
  `cd-lh-size-mismatch.zip` (count 11 after this batch, up from 7).
- `testdata/tar/malformed/` — 9 new: 5 `pax-*.tar` + 4 `gnu-longname/longlink-*.tar`
  (count 12, up from 3).
- `testdata/tar/security/` — 2 new files
  (`symlink-absolute.tar`, `hardlink-outside.tar`) and the
  previously-orphaned `backslash-slip.tar` now exercised rather than
  committed-but-unused (count 6, up from 4; the other three are
  `tar-slip.tar`, `tar-absolute.tar`, `symlink-slip.tar`).

*Scope discipline.* Every PR in this batch deliberately stopped at
the doc / fixture / test boundary. Where `Zip/*.lean` did change —
#1550 (Tar.truncateUTF8 + `ZipTest/TarPathTruncation.lean`), #1554
(`Archive.readEntryData` LH consistency) — the changes were new
guards + regression fixtures; nothing was removed or weakened, and
no proof / spec file was touched. `SECURITY_INVENTORY.md` *"Recommended
policy"* numbers are deliberately flagged as seed values for follow-up
issues, not decisions. The library's proof corpus (42 spec files,
20,516 LOC, 0 sorries) is byte-identical to the pre-batch tree.

Quality metrics: 0 sorries across `Zip/`; 0 runtime `]!`; `Zip/Spec/`
at 42 files, 20,516 LOC (unchanged); `Zip/Native/` at 7 files, 1,780
LOC (unchanged); `Zip/` (FFI / archive / tar / gzip / basic) at 6
files, 1,437 LOC (+ `Archive.lean` grew from `readEntryData` LH
parse + guards; `Tar.lean` grew from `truncateUTF8` + docstring);
`ZipTest/` at 22 files (+1 from `TarPathTruncation.lean`); toolchain
`v4.29.1`.

*Track E open work (post-batch).* P2 item 4 (docstring + error-message
policy), all of P3 (FFI adversarial validation: sanitizer harness,
truncated / concatenated-gzip / repeated-`inflateReset` / near-limit
regression tests, fuzz harness), P4 (runtime-boundary docs), and P5
(proof-friendly guard lemmas for bounded reads). Planner has already
queued the next wave: #1558 / #1559 / #1564 / #1565 / #1566 track the
remaining Priority 2–3 items.

**15-PR batch (Apr 22): Track E security-audit follow-ups (summarize #1588):**

This batch is the second concentrated wave of the Track E security-audit
sub-roadmap. It builds on the 11-PR cluster captured in the prior block
(summarize #1563 / PR #1568) by closing every remaining audit-checklist
P-item except P3.3 (fuzz harness) and P5.* (proof-friendly guard
lemmas). No DEFLATE / Huffman / LZ77 code path changed; no spec file
was touched; `grep -rc sorry Zip/` stayed at `0` throughout. All work
sits on the trust boundary — limit-policy docstrings, FFI regression
tests, sanitizer harness, allocation-site audit, and three new
`SECURITY_INVENTORY.md` sub-sections (upstream-runtime tracking,
minimized reproducer corpus, and local guard inventory). The library's
cryptographic and compression kernels are unchanged; what moved is
how much of the audit checklist is now formally documented and locally
guarded. The corresponding checklist file is
[`plans/track-e-current-audit-checklist.md`](plans/track-e-current-audit-checklist.md)
(source of truth for checkbox state).

*Priority 2 item 4 — Limit-policy docstrings (closed).*

- #1573 — Explicit limit-policy docstrings for FFI whole-buffer +
  streaming decompression (`Zip/Basic.lean`, `Zip/Gzip.lean`,
  `Zip/RawDeflate.lean`). Documents per-API the `0 = no limit` /
  `Some n` / default-cap semantics surfaced by #1556's inventory.
- #1586 — Public-API limit-policy docstrings for `Archive.extract`,
  `Archive.extractFile`, `Tar.extract`, `Tar.extractTarGzNative`
  (`Zip/Archive.lean`, `Zip/Tar.lean`).
- #1594 — P2.4 final wedge: native-decoder limit-policy docstrings
  for `Zip/Native/Inflate.lean` (`maxOutputSize`) and
  `Zip/Native/Gzip.lean` (`maxDecompressedSize`).

*Priority 3 — FFI adversarial validation (P3.1 / P3.2 / P3.4 closed; P3.3 open).*

- #1576 — P3.1: dedicated sanitizer script `scripts/sanitize-ffi.sh`
  rebuilds `c/zlib_ffi.c` under `-fsanitize=address,undefined`,
  explicitly links GCC's libasan / libubsan past Lean's bundled
  clang, and runs the test suite with `LD_PRELOAD` so ASan
  initialises first. The April 2026 tree is ASan + UBSan clean.
- #1571 — P3.2 first tranche: truncated-stream regression tests for
  `Zlib`, `Gzip`, and `RawDeflate` FFI entry points (added to
  `ZipTest/Zlib.lean`, `ZipTest/Gzip.lean`, `ZipTest/RawDeflate.lean`).
- #1572 — P3.2 second tranche: concatenated-gzip-member +
  zero-length-chunk regression tests (added to the same FFI test
  modules).
- #1577 — P3.2 third tranche: repeated-`inflateReset` across
  concatenated gzip members + exact-fit and n−1 near-limit-output
  regression tests.
- #1580 — P3.4: `c/zlib_ffi.c` malloc/realloc/buffer-growth audit.
  New *"Allocation site audit (`c/zlib_ffi.c`)"* sub-section in
  `SECURITY_INVENTORY.md` enumerates every allocation call-site
  (kind / overflow guard / failure mode);
  `scripts/check-c-allocations.sh` flags accidental new sites at
  PR-review time against the recorded baseline.

*Priority 4 — Trusted runtime boundary documentation (P4.1 / P4.2 / P4.3 closed).*

- #1585 — P4.3: per-call-site local-guard inventory for
  `Handle.read` and `Stream.read` callsites in `Zip/Archive.lean`
  and `Zip/Tar.lean`. New *"Local guard inventory for `Handle.read`
  and `Stream.read`"* sub-section in `SECURITY_INVENTORY.md`
  records each `readExact`, `readEntryData`, `skipEntryData`, and
  inline-loop callsite together with the bound it relies on
  (claimed-vs-actual span, `assertSpanInFile` enclosure, etc.).
- #1589 — P4.1: upstream-runtime tracking sub-block in
  `SECURITY_INVENTORY.md` § *"Lean Runtime"*. Records the
  ZIP64 oversized-size / CD-vs-LH attack surface, pins the upstream
  status as *"no upstream link yet — local tracking only"* (dated
  2026-04-22), and lists the local regression coverage
  (#1543 / #1544 / #1554 / #1560 / #1561) that guards the surface
  today.
- #1590 — P4.2: *"Minimized Reproducer Corpus"* section in
  `SECURITY_INVENTORY.md` tabulating all 29 fixtures under
  `testdata/zip/malformed/`, `testdata/tar/malformed/`, and
  `testdata/tar/security/` with the guard each exercises, the
  first-landing PR (or `481e562` for fixtures inherited from the
  initial `lean-zlib → lean-zip` import), and a `{oversized
  allocation, partial-decoder panic, archive-slip, decompression
  bomb, other}` class tag.

*Housekeeping (4 PRs).*

- #1569 — Meditate session: patterns and friction in the Track E
  security-audit phase (drafted skill notes; the materialised SKILL
  files landed in #1579).
- #1579 — Materialise the skill drafts from #1569 as
  `.claude/skills/<skill>/SKILL.md` files.
- #1584 — Doc: progress entry for #1581 rebase fix.
- #1592 — Doc: progress entry for #1590 rebase fix.

*Track E open work (post-batch).* Two checklist items remain:

- **P3.3** — fuzz harness for whole-buffer and streaming inflate
  entry points. Tracking issue: #1595 (unclaimed at the time of
  writing).
- **P5.1** — proof-friendly helpers for bounded reads and validated
  spans in `Zip/Archive.lean` / `Zip/Tar.lean`. Tracking issue:
  #1596 (unclaimed at the time of writing).
- **P5.2 / P5.3** — bounded-span lemmas + helper-adoption rollout;
  no tracking issue yet, downstream of #1596.

A bonus boundary-hardening PR is in flight outside the checklist:
PR #1597 / issue #1593 caps Tar `readEntryData` reads at the
GNU-long-name and PAX extended-header callsites (open at the time
this summary lands; not counted in the 15-PR batch above).

*Scope discipline.* Same rule as the prior batch: every PR in this
wave stopped at the doc / fixture / test boundary, plus narrow
boundary-layer edits in `Zip/Native/Inflate.lean`,
`Zip/Native/Gzip.lean`, `Zip/Basic.lean`, `Zip/Gzip.lean`,
`Zip/RawDeflate.lean`, `Zip/Archive.lean`, and `Zip/Tar.lean` for
the limit-policy docstring PRs (#1573 / #1586 / #1594) — none of
these touched a logic guard or a spec file. The library's proof
corpus (42 spec files, 20,516 LOC, 0 sorries) is byte-identical to
the pre-batch tree.

Quality metrics: 0 sorries across `Zip/`; 0 runtime `]!`;
`Zip/Spec/` at 42 files, 20,516 LOC (unchanged); `Zip/Native/` at
7 files, 1,813 LOC (was 1,780; +33 LOC from limit-policy
docstrings in `Zip/Native/Inflate.lean` and `Zip/Native/Gzip.lean`);
`Zip/` (FFI / archive / tar / gzip / basic) at 6 files, 1,511 LOC
(was 1,437; +74 LOC across the four FFI modules + `Archive.lean` +
`Tar.lean` for limit-policy docstrings); `ZipTest/` at 22 files,
unchanged (P3.2 added test cases inside existing modules);
`testdata/` fixture counts unchanged (11 / 12 / 6 across
`zip/malformed`, `tar/malformed`, `tar/security`); 16 new
progress entries in this batch; toolchain `v4.29.1`.

**12-PR batch (Apr 22): Track E audit-completion wave (summarize #1629):**

This batch is the third concentrated Track E wave. It finishes off
the checklist items that were still open after summarize #1598 —
P3.3 (fuzz harness) lands as #1602 and P5.1 (proof-friendly
bounded-read helpers) lands as #1608 — and executes three of the
five entries in the `SECURITY_INVENTORY.md` *"Recommended policy"*
block (Rec. 1, 3, 5). A fourth recommendation (Rec. 2, streaming FFI
default-flip) is set up structurally by #1610, which adds the
`maxDecompressedSize` parameter to the three streaming FFI decoders
but leaves the default at `0` (half-closed, no policy flip). As in
the prior two Track E waves, no DEFLATE / Huffman / LZ77 logic
changed; no spec file was touched; `grep -rc sorry Zip/` stayed at
`0` throughout. The window runs from 04:18Z (#1600 meditate) to
07:35Z (#1623 Rec. 1 default-flip) on 2026-04-22. The audit
checklist source of truth remains
[`plans/track-e-current-audit-checklist.md`](plans/track-e-current-audit-checklist.md).

*Track E feature work (7 PRs), grouped by `SECURITY_INVENTORY.md`
recommendation or checklist item:*

- **Rec. 1 — whole-buffer FFI default → 1 GiB.** #1623 flips
  `Zip.Basic.decompress`, `Zip.Gzip.decompress`, and
  `Zip.RawDeflate.decompress` from `maxDecompressedSize = 0` (no
  limit) to `1073741824` (1 GiB). Per-decoder bomb-limit regression
  tests added to `ZipTest/Zlib.lean`, `ZipTest/Gzip.lean`, and
  `ZipTest/RawDeflate.lean`.
- **Rec. 3 — per-entry archive extractor default → 1 GiB.** #1618
  flips `Archive.extract`, `Archive.extractFile`, `Tar.extract`,
  `Tar.extractTarGz`, and `Tar.extractTarGzNative` from
  `maxEntrySize = 0` to `1073741824`. Fast-followed by the rebase
  fix #1620 (superseded; its progress entry landed as the ride-along
  #1622).
- **Rec. 5 — native-side uniformity at 1 GiB.** #1617 lifts the
  native `Zip.Native.Inflate.inflate`, `Zip.Native.GzipDecode.decompress`,
  `Zip.Native.ZlibDecode.decompress`, and `Zip.Native.ZlibDecode.decompressAuto`
  default `maxOutputSize` from the previous non-uniform mix to a
  single 1 GiB cap matched with the FFI side.
- **Streaming FFI `maxDecompressedSize` parameter (not a default
  flip).** #1610 adds the parameter to `Gzip.decompressStream`,
  `Gzip.decompressFile`, and `RawDeflate.decompressStream`. The
  default stays at `0` (no limit) in this PR — it half-closes the
  `SECURITY_INVENTORY.md` Rec. 2 gap by making the cap expressible;
  the default flip is a separate follow-up, filed as issue #1625.
- **P3.3 — fuzz harness for whole-buffer and streaming inflate
  entry points.** #1602 adds `ZipTest/FuzzInflate.lean`, a randomized
  harness that exercises both FFI and native backends across random
  seeds; harness quality was audited out-of-band by review #1607.
- **P5.1 — proof-friendly helpers for bounded reads and validated
  spans.** #1608 lands four helpers —
  `readBoundedSpanFromHandle`, `readBoundedExactFromHandle`,
  `readBoundedEntryData`, and `readBoundedExactFromStream` — plus
  `ZipTest/BoundedReadTest.lean` exercising each. #1608 deliberately
  left its checklist box unticked; the box is the concern of the
  follow-up P5.3 caller migration.
- **Inventory-drift detector** (tooling, not a recommendation).
  #1612 lands `scripts/check-inventory-links.sh`, a line-number /
  fixture-path drift checker for `SECURITY_INVENTORY.md` that fires
  at PR review time.

*Review rounds (3 PRs).* All three are doc-only and pair with a
specific feature PR:

- #1604 — standalone review of `SECURITY_INVENTORY.md` /
  audit-checklist reference drift (pairs with no single feature PR;
  fixes line-number drift and cross-references).
- #1607 — quality audit of #1602 (fuzz harness) before Track E's
  7-day exit-criterion window closes.
- #1616 — quality audit of #1610 (streaming FFI
  `maxDecompressedSize` parameter).

*Infrastructure (2 PRs).*

- #1600 — meditate session that catalogued the patterns and friction
  of the prior Track E wave (~15 PRs since #1569). Drafted skill
  notes in its progress entry; the SKILL.md file edits themselves
  were either part of the prior wave (#1579) or reserved for a
  later meditate.
- #1622 — ride-along progress entry for the #1620 rebase fix of
  PR #1618 (per-entry `maxEntrySize` default flip). Doc-only.

*Remaining gaps (as of batch close, 07:35Z).* Per the issue body,
three Track E items remained outside this batch:

- **Rec. 2 — streaming FFI default-flip.** Tracked as issue #1625
  at summarize-issue filing; structurally set up by #1610.
- **Rec. 4 — whole-archive `maxTotalSize` cap.** Tracked as issue
  #1621 at summarize-issue filing; not started in this batch.
- **P5.2** — validated-span / bounded-read lemma proofs over the
  P5.1 helpers; filed fresh mid-batch as issue #1628.
- **P5.3** — caller migrations in `Zip/Archive.lean` / `Zip/Tar.lean`
  to consume the P5.1 helpers. The issue body flagged PR #1626 as
  "in flight at summarize time"; in reality #1626 had merged at
  07:48:16Z, ~2 minutes *before* the summarize issue was filed
  (07:50Z). It is out of the 12-PR batch by issue scope, but the
  P5.3 checklist box is closed at the time this summary lands.
  Since batch close, the three remaining gaps above have also
  landed (#1630 Rec. 4 at 08:10Z, #1631 Rec. 2 at 08:28Z, #1636
  P5.2 at 09:17Z); they belong to the next summarize batch.

*Scope discipline.* Same rule as the prior two Track E waves: the
only `Zip/*.lean` edits in the batch are narrow parameter-addition
and default-flip changes on FFI / native / extractor entry points
(#1610 streaming-FFI parameter; #1617 native-side default unification;
#1618 extractor `maxEntrySize`; #1623 FFI whole-buffer
`maxDecompressedSize`), plus the new P5.1 helper family in
`Zip/Archive.lean` and `Zip/Tar.lean` (#1608). No spec file was
touched. No proof was changed. The library's proof corpus (42
spec files, 20,606 LOC, 0 sorries) remains intact; the only spec
LOC movement (20,516 → 20,606) is from a spec file not in this
batch's window, inherited post-#1598. The `]!` count is still 0
and `Zip/Native/` retains 0 runtime bounds assertions.

Quality metrics: 0 sorries across `Zip/` (unchanged; the issue
body's "4 → 4 XxHash" baseline claim is stale — `Zip/Spec/XxHash.lean`
does not exist in this repository, and `grep -rc sorry Zip/` sums
to 0); 0 runtime `]!` (unchanged); `Zip/Spec/` at 42 files, 20,606
LOC (+90 LOC relative to prior summarize; not attributable to a PR
in this batch); `Zip/Native/` at 7 files, 1,852 LOC (was 1,813;
+39 LOC from #1617 default-unification docstrings + #1608 helper
support); `Zip/` (FFI / archive / tar / gzip / basic / checksum) at
6 files, 1,833 LOC (was 1,511; +322 LOC from #1608 bounded-read
helper family landing in `Zip/Archive.lean` + `Zip/Tar.lean`, plus
the streaming-FFI parameter in #1610 and the default-flip docstring
updates in #1617 / #1618 / #1623; `Zip/Checksum.lean` is a new
sixth file present in the file list but inherited from earlier);
`ZipTest/` at 24 files (+2 — `ZipTest/FuzzInflate.lean` from #1602
and `ZipTest/BoundedReadTest.lean` from #1608); `testdata/` fixture
counts 11 / 14 / 6 (the +2 in `testdata/tar/malformed/` is from
pre-batch PR #1597 — it merged 03:43Z but was outside the prior
summarize's stated scope); toolchain `v4.29.1`.

### Infrastructure
- Multi-agent coordination via `pod` with worktree-per-session isolation
- GitHub-based coordination (agent-plan issues, auto-merge PRs)
- Session dispatch: planners create issues, workers claim and execute
- ~660 sessions (Feb 19 – Apr 22)
- ~653 merged PRs (approximate; authoritative count via `gh pr list`)
- 100% module docstring coverage across all source files
- Full linter compliance (all warnings eliminated)
- Repository split into `lean-zip` + `lean-zip-common` + `lean-zstd`
  (#1487, 2026-03-27)
- Agent skills: `lean-wf-recursion` (#349), `proof-review-checklist` (#386,
  updated #925, #1325), bare-simp-resistant pattern catalog (#386),
  `lean-zstd-patterns` (#491), `agent-pr-recovery` (#546, updated #597),
  `lean-zstd-spec-pattern` (#623, updated #711, #840, #925),
  `lean-monad-proofs` (updated #711, #840),
  `lean-content-preservation` (#891),
  `lean-parsing-completeness` (#1127, updated #1171),
  `proven-bounds` (#1420)
