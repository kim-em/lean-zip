# lean-zip Progress

Global milestones — updated only on phase transitions and major events.
Per-session details are in `progress/`.

## Current State

- **Phase**: Phase 4+ complete; Track C2 (fuel elimination) nearly complete
- **Toolchain**: leanprover/lean4:v4.29.0-rc2
- **Sorries**: 2 (both `inflateLoop_complete` variants — completeness direction of the block loop)
- **Sessions**: ~204 completed (Feb 19 – Mar 1)
- **Source files**: 84 (43 spec, 8 native impl, 9 FFI/archive, 4 ZipForStd, 20 test)
- **Merged PRs**: 167

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
size bound arises from fuel-based termination in the native `inflateLoop`
(the last remaining fuel-based function — see Track C2).

**Proof quality reviews** (45+ sessions): systematic code review across
all spec files, reducing proof size, extracting reusable lemmas to
ZipForStd, splitting large files for maintainability. Recent reviews:
BitstreamCorrect (#336), EmitTokensCorrect (#340), DecodeCorrect (#362),
DeflateSuffix (#365).

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

### Track C2: Fuel Elimination (nearly complete, Mar 1)
Replacing fuel-based recursion with well-founded recursion to eliminate
the data size bound entirely.

**Completed — 5 of 6 functions converted:**
- Fuel audit (#323) identifying all 6 fuel-using functions
- Spec `decodeCLSymbols` → WF (#328): `termination_by totalCodes - acc.length`
- Native `decodeCLSymbols` → WF (#332): same termination measure
- Spec `decodeSymbols` → WF (#337): `termination_by` on remaining bits
- Native `decodeHuffman.go` → WF (#341): `termination_by dataSize * 8 - br.bitPos`
- Spec `decode.go`/`decode.goR` → WF (#344): required deleting DeflateFuelIndep.lean
  (fuel independence became moot once spec functions are WF) and updating 11
  downstream proof files
- `inflateLoop_correct` proved (#358): native→spec block loop correspondence,
  composing block-level correctness with 7 new bit-length invariant lemmas
- `decodeDynamicTrees_complete` proved (#361): composed from sub-completeness
  theorems for each component
- Proof repairs across 6 PRs (#345, #350, #351, #356, #357, #362): WF
  conversions broke ~15 proofs; all repaired except 2 completeness sorries

**Sorry count trajectory:** 0 → ~15 (during WF conversions) → 2 (after repairs).
The rise was expected: changing function signatures cascades through proof files.

**Remaining:**
- Native `inflateLoop` — still fuel-based (block dispatch loop)
- 2 sorries: `inflateLoop_complete` and `inflateLoop_complete_ext` in the
  completeness direction (spec succeeds → native succeeds). The correctness
  direction (`inflateLoop_correct`: native succeeds → spec succeeds) is proved.

**New skill:** `lean-wf-recursion` (#349) capturing WF function unfolding rules,
`f.induct` functional induction patterns, and fuel-to-WF migration checklist.

### Track D: Benchmarking (started, Feb 25)
Initial benchmark infrastructure comparing native Lean compression vs
FFI (zlib) across levels 0/1/6 with various data patterns (constant,
cyclic, random) at sizes 1KB–32KB. Key finding: native LZ77
(`lz77Greedy_mainLoop`) had a stack overflow at 64KB+ due to
non-tail recursion.

**Fix:** `lz77GreedyIter` — a tail-recursive, Array-accumulating version
with proved equivalence (`lz77GreedyIter_eq_lz77Greedy`). Conformance
tests pass on inputs up to 256KB.

### Infrastructure
- Multi-agent coordination via `pod` with worktree-per-session isolation
- GitHub-based coordination (agent-plan issues, auto-merge PRs)
- Session dispatch: planners create issues, workers claim and execute
- ~204 sessions: majority implementation, ~90 review, ~4 self-improvement,
  remainder PR maintenance, planning, and summarization
- 167 merged PRs (Feb 19 – Mar 1)
- 100% module docstring coverage across all source files
- Full linter compliance (all warnings eliminated)
