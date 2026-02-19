# Progress

Session-by-session log for lean-zip development. Most recent first.

## 2026-02-19: Implementation — Adler32 bounds proofs + Phase 3 start

**Type**: implementation
**Phase**: Phase 3 (verified decompressor) — started
**Sorry count**: 0 → 2

**Accomplished**:
- Proved Adler32 bounds: `updateByte` output components are unconditionally
  < MOD_ADLER (no precondition on input state needed, since `% MOD_ADLER`
  is explicit). `updateList_valid` follows by induction. `updateBytes_valid`
  lifts to the ByteArray-based native implementation.
- Created `Zip/Spec/Huffman.lean`: Canonical Huffman code construction from
  RFC 1951 §3.2.2. Defines `codeFor`, `allCodes`, `decode`, `isPrefixOf`.
  Proved `isPrefixOf_iff`, `decode_deterministic`, `natToBits_length`.
  Added `ValidLengths` predicate (bounds + Kraft inequality) as precondition
  for the two sorry'd theorems.
- Created `Zip/Spec/Deflate.lean`: Complete DEFLATE bitstream spec.
  `bytesToBits` (LSB-first per byte), `readBitsLSB`/`readBitsMSB`,
  `LZ77Symbol` type with `resolveLZ77`, all RFC 1951 tables, full block
  decode pipeline (stored, fixed Huffman, dynamic Huffman), stream-level
  `decode` function. Proved `fixedLitLengths_length`, `fixedDistLengths_length`.

**Issues found and fixed (from Codex review)**:
- Simplified `alignToByte` to derive padding from `bits.length % 8` instead
  of threading a `bitsConsumed` counter — correct because `bytesToBits`
  always produces a multiple-of-8 list
- Fixed `decodeStored`: replaced `for` loop that returned `some` on failure
  with recursive `readNBytes` that properly returns `none`
- Added overshoot guards in `decodeDynamicTables` for repeat codes
- Guarded `codeFor` against `len > maxBits`
- Added `ValidLengths` preconditions to sorry'd theorem statements

**Codex false positive**: flagged Huffman bit ordering as wrong. Actually
correct: DEFLATE packs code MSB-first into byte LSB positions, `bytesToBits`
reads LSB-first, so first bit in list = MSB of code = matches `natToBits`.

**Decisions**:
- Spec functions use `List Bool` for bitstreams, `List UInt8` for output —
  clean for reasoning, independent of implementation's `ByteArray`/`BitReader`
- Used fuel for termination in `decodeSymbols`, `decode`, and
  `decodeCLSymbols` — consistent and simple
- `readBitsMSB` included but unused — kept for potential future proof needs

**Sorry locations**:
- `Zip/Spec/Huffman.lean:145` — `codeFor_injective`
- `Zip/Spec/Huffman.lean:155` — `canonical_prefix_free`

**Next**:
- Prove the Huffman theory sorries
- Conformance test: spec decode vs native inflate
- State the main correctness theorem

## 2026-02-19: Review — Gzip/integration code, slop detection

**Type**: review
**Phase**: Phase 2 (DEFLATE decompressor) — COMPLETE
**Sorry count**: 0 → 0

**Reviewed**:
- `Zip/Native/Gzip.lean`: RFC 1952/1950 compliance verified. Header
  parsing correct (FEXTRA, FNAME, FCOMMENT, FHCRC). Checksums (CRC-32,
  Adler-32) verified correctly. Concatenated gzip member handling correct.
  FHCRC not validated (acceptable, most implementations skip this).
- `Zip/Archive.lean` integration: Clean native/FFI dispatch. CRC path
  selection correct. `maxEntrySize = 0` handling documented.
- `Zip/Tar.lean` integration: `extractTarGzNative` correctly documented
  as O(file_size) memory. ByteArray-backed stream is correct.
- `ZipTest/NativeGzip.lean`: Good coverage — conformance at multiple
  compression levels, empty/single/large data, concatenated streams,
  auto-detect, all error cases.
- `ZipTest/NativeIntegration.lean`: Covers stored + deflated + empty +
  nested for both ZIP and tar.gz native extraction.
- Full slop detection across all Native/ and NativeTest* files.
- Toolchain check: v4.29.0-rc1 is latest (v4.28.0 latest stable).

**Fixes applied**:
- **Security**: Capped per-member inflate budget in `GzipDecode.decompress`
  to `maxOutputSize - result.size`. Previously each concatenated member
  got the full `maxOutputSize` independently, allowing peak memory of
  ~2x the limit with crafted concatenated streams.
- **Dead code**: Removed unused `BitReader.ofByteArray`, `remaining`,
  `isEof` (never called anywhere in the codebase).
- **Test refactor**: Extracted `mkRandomData` to `Helpers.lean`, replacing
  duplicated pseudo-random generation in NativeInflate and NativeGzip.
- **Test output**: Fixed NativeIntegration to use consistent `"  "` prefix
  and `"passed."` suffix matching other native test modules.
- **Documentation**: Updated CLAUDE.md source layout to enumerate all
  `Zip/Native/` files explicitly instead of "...".

**Not changed** (acceptable as-is):
- Gzip FHCRC (header CRC16) not validated — standard practice
- `detectFormat` false-positive on raw DEFLATE that looks like zlib —
  documented known limitation
- Test code duplication (compression level loops, corruption patterns) —
  keeping tests self-contained is preferred over over-factoring

**Next**:
- Phase 3: DEFLATE spec formalization
- Adler32 bounds proofs (warm-up for proof work)
- Self-improvement session

## 2026-02-19: Implementation — native backend integration (Phase 2 complete)

**Type**: implementation
**Phase**: Phase 2 (DEFLATE decompressor) — COMPLETE
**Sorry count**: 0 → 0

**Accomplished**:
- Integrated native pure-Lean decompressor as alternative backend for ZIP
  and tar.gz extraction, completing the final Phase 2 deliverable
- `Archive.extract`/`extractFile` now accept `useNative := true` to use
  `Zip.Native.Inflate.inflate` and `Crc32.Native.crc32` instead of C FFI
- Added `Tar.extractTarGzNative` for gzip decompression without C libraries
  (reads entire file into memory, O(file_size))
- Created `ZipTest/NativeIntegration.lean`: creates ZIP and tar.gz with FFI,
  extracts with native backend, verifies identical results for stored entries,
  deflated entries, empty files, and nested directories
- Fixed `maxEntrySize = 0` handling: FFI treats 0 as "no limit", native path
  caps at 256 MiB as zip-bomb guard (documented in docstring)

**Decisions**:
- ZIP integration is straightforward: entry data is already in memory
- Tar.gz native path is non-streaming (O(file_size) memory) because the
  native inflate works on complete ByteArrays. Streaming native inflate
  is future work
- Default `useNative := false` for backwards compatibility

**Codex review**:
- Flagged 256 MiB silent cap vs FFI "no limit" — addressed with docstring
- Flagged `Nat` overflow concerns — not applicable in Lean 4 (unbounded Nat)
- Suggested additional tests for CRC mismatch in native mode — deferred to
  review session (already covered in NativeGzip error tests)

**Next**:
- Review session for all Native/ code
- Phase 3: DEFLATE spec formalization
- Self-improvement session

## 2026-02-19: Implementation — gzip/zlib framing layer

**Type**: implementation
**Phase**: Phase 2 (DEFLATE decompressor) — feature-complete
**Sorry count**: 0 → 0

**Accomplished**:
- Refactored `Inflate.inflate` into `inflateRaw` (returns ending byte position)
  + `inflate` wrapper. This enables framing layers to read trailers after the
  DEFLATE stream.
- Implemented `Zip/Native/Gzip.lean`:
  - `GzipDecode.decompress`: Full RFC 1952 gzip header/trailer parsing, including
    FEXTRA, FNAME, FCOMMENT, FHCRC optional fields. CRC-32 and ISIZE verification.
    Supports concatenated gzip members.
  - `ZlibDecode.decompress`: RFC 1950 zlib header parsing (CMF+FLG check bits,
    compression method, window size). Adler-32 trailer verification (big-endian).
  - `detectFormat`: Auto-detects gzip/zlib/raw-deflate from first bytes.
  - `decompressAuto`: Dispatches to the right decompressor based on format.
- Added `ZipTest/NativeGzip.lean` with:
  - Conformance tests: gzip and zlib at multiple compression levels, empty, single
    byte, large (124KB), incompressible, concatenated gzip streams
  - Auto-detect tests for all three formats
  - Error-case tests: empty input, truncated headers/trailers, bad magic, CRC32
    mismatch, Adler32 mismatch, wrong compression method, invalid block type,
    truncated stored block
- Security fix: enforced maxOutputSize on total concatenated gzip output (not just
  per-member)

**Decisions**:
- Gzip treats non-gzip trailing bytes after a valid member as end-of-stream
  (consistent with standard gzip implementations)
- Auto-detect can false-positive on raw DEFLATE streams that happen to look like
  zlib headers; this is a known inherent limitation
- Minimum 6 bytes required for zlib (2 header + 4 trailer minimum)

**Next**:
- Integration as alternative backend for ZIP/tar code paths
- Phase 3: DEFLATE spec formalization
- Full review of all Native/ code as cohesive unit

## 2026-02-19: Review — Phase 2 DEFLATE decompressor

**Type**: review
**Phase**: Phase 2 (DEFLATE decompressor) — in progress
**Sorry count**: 0 → 0

**Reviewed**:
- `Zip/Native/BitReader.lean`: Clean, minimal, no issues. Bounds checks
  protect all `!` indexing. `readBits` n ≤ 25 precondition documented but
  not enforced — acceptable for internal API.
- `Zip/Native/Inflate.lean`: Thorough review against RFC 1951. All code
  paths correct: canonical Huffman construction (§3.2.2), fixed codes
  (§3.2.5), dynamic codes (§3.2.7), stored blocks (§3.2.4), LZ77
  back-reference with overlapping copy. Length/distance tables verified.
- `ZipTest/NativeInflate.lean`: Good coverage (all levels, empty, single
  byte, large, pseudo-random). No critical gaps.

**Fixes applied**:
- **Security**: Added `maxOutputSize` parameter (default 256 MiB) to
  `inflate`, `decodeStored`, and `decodeHuffman` to guard against zip bombs
- **Robustness**: Converted `while !isFinal` to bounded `for _ in [:10001]`
  loop, eliminating `isFinal` and `blockCount` mutable variables
- **Style**: Replaced `List.range n` with `[:n]` ranges (4 occurrences
  across Inflate.lean, Helpers.lean, Archive.lean)
- Fixed fuel exhaustion error message ("fuel limit" vs "size limit")

**Toolchain**: v4.29.0-rc1 is current (latest stable: v4.28.0, released
2026-02-16). No upgrade needed.

**Not changed** (acceptable as-is):
- `HuffTree.insert` catch-all for leaf nodes (returns leaf unchanged) —
  only reachable with invalid data, and the error surfaces later in decode
- `!` indexing throughout — all uses are bounds-safe, but converting to
  proof-carrying indexing is future work for Phase 3

**Next**:
- Gzip/zlib framing layer (headers, trailers, checksums)
- DEFLATE spec formalization
- Error-case tests for inflate

## 2026-02-19: Phase 2 start — pure Lean DEFLATE decompressor

**Type**: implementation
**Phase**: Phase 2 (DEFLATE decompressor) — in progress
**Sorry count**: 0 → 0

**Accomplished**:
- Implemented `Zip/Native/BitReader.lean`: LSB-first bit-level reader for
  ByteArray with readBit, readBits (up to 25), byte-aligned reads
- Implemented `Zip/Native/Inflate.lean`: complete DEFLATE (RFC 1951)
  decompressor supporting all three block types (stored, fixed Huffman,
  dynamic Huffman). Includes canonical Huffman tree construction, LZ77
  back-reference resolution, and code length decoding for dynamic blocks
- Added `ZipTest/NativeInflate.lean`: conformance tests against FFI zlib
  covering levels 0–9, empty, single byte, large (124KB), and pseudo-random
- All 10 test cases pass; native inflate produces identical output to zlib

**Decisions**:
- Used fuel parameter (10M iterations) for Huffman block decoding to
  guarantee termination without `partial`
- Used `Except String` monad for error handling (not `IO`) to keep the
  implementation pure
- Implemented all 3 block types in one session since types 1 and 2 share
  the same Huffman decoding infrastructure

**Bug fixed**:
- `HuffTree.insert` had off-by-one: `go tree (len - 1)` → `go tree len`.
  For an n-bit code, need n branching decisions, not n-1

**Next**:
- Review session for Phase 2 code
- Gzip/zlib framing layer (headers, trailers, checksums)
- Begin DEFLATE spec formalization

## 2026-02-19: Phase 1 complete — CRC-32 table equivalence proved

**Type**: implementation + review
**Phase**: Phase 1 (Checksums) — COMPLETE
**Sorry count**: 1 → 0

**Accomplished**:
- Proved `crcByteTable_eq_crcByte`: table-driven CRC-32 byte update equals
  bit-by-bit specification. This was the last sorry in Phase 1.
- Key technique: `crcBits8_split` lemma (8-fold `crcBit` linearity over
  high/low byte split) proved directly by `bv_decide`, avoiding the need
  to iterate the single-step `crcBit_xor_high` lemma manually
- Helper lemmas for UInt8→UInt32 conversion: rewrite via
  `BitVec.ofNat_toNat` to `BitVec.setWidth`, enabling `bv_decide`
- Updated ARCHITECTURE.md with native implementation and spec sections
- Reviewed all Phase 1 code: clean, no issues found

**Decisions**:
- Proved `crcBits8_split` directly by `bv_decide` instead of iterating
  `crcBit_xor_high` 8 times. The direct approach is simpler and avoids
  intermediate goal management
- Pattern for `UInt32.ofNat byte.toNat` opacity: rewrite to
  `⟨byte.toBitVec.setWidth 32⟩` via `BitVec.ofNat_toNat`, then use
  `show` + `congr 1` to expose `BitVec` for `bv_decide`

**Next**:
- Review session (no reviews done yet)
- Begin Phase 2 (DEFLATE decompressor) per VERIFICATION.md

## 2026-02-19: Phase 1 kickoff — native checksums

**Type**: implementation
**Phase**: Phase 1 (Checksums)
**Sorry count**: 0 → 1

**Accomplished**:
- Created `Zip/Spec/Adler32.lean`: formal Adler-32 spec using `List.foldl`
  with compositionality theorem (`updateList_append`)
- Created `Zip/Native/Adler32.lean`: pure Lean implementation using
  `Array.foldl`, with proved equivalence to spec via `Array.foldl_toList`
- Created `Zip/Spec/Crc32.lean`: formal CRC-32 spec with bit-by-bit
  polynomial definition, lookup table construction, and compositionality
- Created `Zip/Native/Crc32.lean`: table-driven CRC-32, with the key
  linearity lemma proved (`crcBit_xor_high`) via `bv_decide`
- Created `ZipTest/NativeChecksum.lean`: comprehensive conformance tests
  for both native checksums against FFI (known values, large data,
  incremental, empty, single byte)

**Decisions**:
- Use `Array.foldl` on `data.data` instead of `ByteArray.foldl` because
  `Array.foldl_toList` exists in the standard library
- Use `data.data.toList` in theorem statements instead of `data.toList`
  because `ByteArray.toList` has an unrelated loop implementation
- `bv_decide` is effective for UInt32/BitVec reasoning (proved CRC
  linearity in one line)

**Next**:
- Complete `crcByteTable_eq_crcByte` proof (see PLAN.md for strategy)
- Consider Adler32 bounds proofs (state components < MOD_ADLER)
- Continue Phase 1 or do a review session
