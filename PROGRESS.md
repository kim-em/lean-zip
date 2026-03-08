# lean-zip Progress

Global milestones — updated only on phase transitions and major events.
Per-session details are in `progress/`.

## Current State

- **Phase**: Phase 4+ complete; Track C1 complete; Track C2 complete; Track E (Zstd) all block types decompressing
- **Toolchain**: leanprover/lean4:v4.29.0-rc4
- **Sorries**: 3 (all XxHash.lean — UInt64 test vectors too expensive for kernel evaluation)
- **Sessions**: ~410 completed (Feb 19 – Mar 8)
- **Source files**: 101 (49 spec, 13 native impl, 9 FFI/archive, 4 ZipForStd, 26 test)
- **Merged PRs**: 380
- **Spec theorems/lemmas**: 927 declarations across 49 spec files (25,781 lines)
- **Bare simp**: 0 remaining — campaign complete (49 spec files, ZipForStd/, Native/ all clean)
- **Bare simp_all**: 0 remaining — campaign complete (all spec files, DeflateEncodeDynamic included)

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

**Summary:** The Zstd spec infrastructure now spans 6 files with 213
theorems/lemmas: ZstdSequence (58), Fse (58), ZstdHuffman (50), Zstd (29),
XxHash (12), ZstdFrame (6). Total spec line count: 4,872 lines.

**Remaining:**
- Prove remaining sorry stubs: 3 in XxHash (UInt64 test vectors too
  expensive for kernel evaluation — intractable without native_decide)
- Compose position specs into end-to-end frame position theorem
- Content preservation campaign: extend `executeSequences_loop_getElem_lt`
  to full sequence execution and block loop levels
- Spec-level decoder with correctness proofs (algorithmic correspondence
  between native and spec decoder, following the DEFLATE B3 pattern)
- Compressor + roundtrip proof

### Infrastructure
- Multi-agent coordination via `pod` with worktree-per-session isolation
- GitHub-based coordination (agent-plan issues, auto-merge PRs)
- Session dispatch: planners create issues, workers claim and execute
- ~410 sessions (Feb 19 – Mar 8)
- 380 merged PRs
- 100% module docstring coverage across all source files
- Full linter compliance (all warnings eliminated)
- Agent skills: `lean-wf-recursion` (#349), `proof-review-checklist` (#386),
  bare-simp-resistant pattern catalog (#386), `lean-zstd-patterns` (#491),
  `agent-pr-recovery` (#546, updated #597), `lean-zstd-spec-pattern` (#623,
  updated #711, #840), `lean-monad-proofs` (updated #711, #840)
