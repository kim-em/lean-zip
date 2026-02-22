# Verification Plan for lean-zip

This document outlines a plan to add parallel native Lean implementations
alongside the existing FFI wrappers, add conformance tests between the
two, and formally prove properties of the native implementations.

## Current Architecture

lean-zip currently wraps system libraries (zlib, Zstandard) via C FFI for
compression, decompression, and checksums. Archive formats (tar, ZIP) are
already implemented in pure Lean.

| Component | Implementation | Lines (approx) |
|-----------|---------------|----------------|
| CRC32, Adler32 | C FFI (zlib) | ~40 C |
| DEFLATE compress/decompress | C FFI (zlib) | ~600 C |
| Gzip/Zlib framing | C FFI (zlib) | included above |
| Zstd compress/decompress | C FFI (libzstd) | ~350 C |
| Tar archives | Pure Lean | ~600 |
| ZIP archives | Pure Lean | ~420 |
| Binary packing | Pure Lean | ~140 |

## What Adding Native Implementations Would Involve

| Component | Algorithmic complexity | Estimated effort |
|-----------|----------------------|------------------|
| CRC32 | Table-driven, ~50 lines of logic | Easy (days) |
| Adler32 | Trivial arithmetic | Easy (hours) |
| DEFLATE decompression (inflate) | Huffman decoding + LZ77 sliding window | Hard (weeks) |
| DEFLATE compression (deflate) | Huffman coding + LZ77 matching + lazy matching + levels 0-9 | Very hard (months) |
| Gzip/Zlib framing | Header/trailer parsing, CRC/size checks | Easy (days) |
| Zstd decompression | FSE + Huffman + sequence decoding + window management | Very hard (months) |
| Zstd compression | All of the above plus match finding, optimal parsing | Extremely hard (many months) |

## What Is Realistic to Prove

### Checksums (CRC32, Adler32)

Very provable. These are pure mathematical functions. Tractable theorems:

- Equivalence of the table-driven implementation to the bit-by-bit
  polynomial definition
- Compositionality of incremental computation:
  `crc32(crc32(init, a), b) = crc32(init, a ++ b)`
- Equivalence to a polynomial specification (CRC32 as division in
  GF(2)[x])

### DEFLATE Roundtrip

The key structural insight: decompression is deterministic (given a valid
DEFLATE stream, there is exactly one output), but compression is not
(different compression levels produce different valid bitstreams that all
decompress to the same output).

The natural theorem is:

```
∀ (data : ByteArray) (level : Fin 10), inflate (deflate data level) = data
```

Proving this requires:

1. Formally specify what constitutes a valid DEFLATE bitstream
2. Prove `inflate` correctly decodes any valid bitstream
3. Prove `deflate` produces a valid bitstream
4. Prove the composition

Step 2 is the hardest implementation work but the most tractable proof.
Step 3 is where the real pain lies -- the compression side has complex
heuristics (lazy matching, level-dependent strategies) that are correct
but messy to reason about.

### Zstd Roundtrip

Significantly harder than DEFLATE. The Zstd format involves:

- Finite State Entropy (FSE) coding (more complex than Huffman)
- Multiple interleaved bitstreams
- A dictionary system
- Repeat offset codes
- Frame/block structure with multiple block types

Estimated at 3-5x the work of DEFLATE.

## Evaluation

### Strengths

- Lean 4 is well-suited: `ByteArray`, `UInt8`, bitwise operations are
  all available
- The conformance testing approach (run both implementations, compare
  outputs) is valuable engineering regardless of proofs
- CRC32/Adler32 are low-hanging fruit with real proof value
- A verified DEFLATE decompressor would be a genuinely novel contribution
  -- there is no runnable verified DEFLATE implementation in any proof
  assistant that I am aware of
- The archive format code (tar, ZIP) is already pure Lean, so adding
  native compression would yield a fully verified archive pipeline

### Challenges

- **Performance**: A naive Lean DEFLATE implementation will be orders of
  magnitude slower than zlib. Zlib is hand-tuned C with SIMD
  specializations. The FFI implementations should remain available as the
  fast path; the native implementations serve as verified reference
  implementations that can also be used when the C libraries are
  unavailable
- **Specification gap**: RFC 1951 is informal English. Senjak & Hofmann
  (2016) formalized it in Coq (see References below), but no Lean 4
  formalization exists. Formalizing the spec is a prerequisite for
  proving anything about an implementation
- **Compression level fidelity**: Matching zlib's exact output
  byte-for-byte at each compression level is probably not worth pursuing.
  The correct goal is roundtrip correctness, not output equivalence
- **Sliding window management**: Mutable arrays in Lean require careful
  handling of linearity/borrowing for performance
- **Huffman tree construction proofs**: Code length limits, canonical
  ordering -- tedious but not deep
- **LZ77 match-finding**: Inherently heuristic. Proving it produces
  *valid* output is tractable; proving it produces *good* output is a
  research problem
- **Zstd is a moving target**: The format is complex and has evolved; the
  RFC (3.1) is 100+ pages

## Optimization Strategy

The plan is to start with naive, easy-to-reason-about Lean
implementations and prove correctness properties about these first. These
initial versions prioritize clarity over performance: simple loops instead
of table lookups for CRC32, straightforward linear scans instead of hash
chains for LZ77 matching, direct bit-by-bit Huffman decoding instead of
table-based multi-bit lookups.

Once the core proofs are established against these simple implementations,
we add progressively more efficient versions and prove they produce
identical output to the unoptimized versions. The roundtrip proofs then transfer automatically: if `inflate_fast` is
proven equivalent to `inflate_simple`, and we have proven
`inflate_simple (deflate data level) = data`, then
`inflate_fast (deflate data level) = data` follows immediately.

This layered approach applies to compression levels as well. Rather than
implementing all nine DEFLATE compression levels at once, we work through
them progressively:

- **Level 0** (stored blocks, no compression): trivial to implement and
  prove correct
- **Level 1** (greedy LZ77, fixed Huffman codes): the simplest real
  compression, and the first interesting roundtrip proof
- **Levels 2-4** (lazy matching, increasing effort): each level extends
  the match-finding heuristic while producing equally valid DEFLATE
  bitstreams
- **Levels 5-9** (dynamic Huffman codes, maximum effort): the most
  complex compression strategies

Each level produces a valid DEFLATE bitstream, so the decompressor proof
covers all of them. The per-level work is proving that each compression
strategy produces a valid bitstream, not re-proving decompression.

## Development Cycle

Each native implementation follows a formalization-first cycle:

1. **Type signature** of the new function, implemented as `:= sorry`
2. **Specification theorems** stating the desired properties, with `:= by sorry` proofs
3. **Implementation** of the function body
4. **Conformance tests** verifying agreement with the FFI/library version
5. **Proofs** of the specification theorems

This same pattern applies to optimized versions: the specification theorems
are equivalence with the unoptimized version, and the roundtrip/correctness
proofs transfer automatically via the equivalence.

Writing specs before implementations ensures the work stays grounded in
what we can actually prove, and prevents implementations from getting ahead
of the formalization.

## Phased Plan

### Phase 1: Checksums

Pure Lean CRC32 and Adler32 with proofs of equivalence to a formal
specification. Conformance tests against the FFI implementations.

**Estimated effort**: Days to weeks.

**Deliverables**:
- Native Lean CRC32 (table-driven)
- Native Lean Adler32
- Proof: table-driven CRC32 matches bit-by-bit definition
- Proof: incremental computation composes correctly
- Conformance test harness comparing native vs FFI on random inputs

### Phase 2: DEFLATE Decompressor

Pure Lean DEFLATE decompressor (inflate only). No proofs yet.

**Estimated effort**: 2-4 weeks of implementation.

**Deliverables**:
- Huffman decoder (fixed and dynamic trees)
- LZ77 back-reference resolution with sliding window
- Gzip/Zlib framing (header/trailer parsing, checksum verification)
- Conformance tests against zlib on a corpus of compressed data
- Integration as an alternative backend for existing ZIP/tar code paths

### Phases 3–4: Verified DEFLATE Roundtrip

The overarching goal:

```
∀ (data : ByteArray) (level : Fin 10), inflate (deflate data level) = data
```

The roundtrip decomposes into five building blocks. The decompressor
(Phase 3) contributes the "right half" of each invertibility theorem;
the compressor (Phase 4) contributes the "left half." Each building
block is independently meaningful.

#### The roundtrip pipeline

```
data → matchLZ77 → symbols → huffEncode → bits → pack → compressed
                                                           │
compressed → unpack → bits → huffDecode → symbols → resolveLZ77 → data
```

The full proof chains three invertibility steps:

```
  inflate (deflate data level)
= resolveLZ77 (huffDecode (unpack (pack (huffEncode (matchLZ77 data)))))
= resolveLZ77 (huffDecode (huffEncode (matchLZ77 data)))  -- bitstream
= resolveLZ77 (matchLZ77 data)                            -- Huffman
= data                                                    -- LZ77
```

(Simplified — actual proof routes through block framing.)

#### Building block 1: LZ77 fundamental theorem

```lean
resolveLZ77 (matchLZ77 data level) [] = some data.toList
```

The LZ77 matcher produces a symbol stream; resolving it reconstructs
the original data. This holds for all compression levels because every
valid match (greedy, lazy, or literal) describes the same data.

**Level 0 (stored blocks, no LZ77):** Emits stored blocks with literal
bytes. Roundtrip is literal copy-through. Trivial.

**Level 1 (greedy matching, fixed Huffman):** At position `p`, the
matcher either emits `Literal data[p]` or finds the longest match at
distance `d` and emits `BackRef len d`. Proof by induction on `p` with
invariant `resolveLZ77 remaining acc = some data.toList` where
`acc = data[0..p]`:
- Literal: extends `acc` by one byte, direct.
- BackRef: matcher verified `data[p..p+len] = data[p-d..p-d+len]`.
  By `copyLoop_eq_ofFn`, the copy produces `data[p..p+len]`, extending
  `acc` to `data[0..p+len]`.

**Levels 2–4 (lazy matching):** At position `p`, finds match M1, then
checks `p+1` for a longer M2. If M2 is longer, emits
`Literal data[p]; BackRef M2`; otherwise `BackRef M1`. Same invariant
— proof branches on matcher's decision but `data[p..]` is produced
either way.

**Levels 5–9 (dynamic Huffman, more search):** LZ77 validity is
identical to levels 2–4; only which matches are found differs, not
their correctness. Dynamic Huffman affects the encoding layer (BB2),
not the LZ77 layer.

#### Building block 2: Huffman encode/decode invertibility

```lean
decodeSymbols litLens distLens (encodeSymbols litLens distLens syms ++ rest)
  = some (syms, rest)
```

For prefix-free code tables. The single-symbol case is already proved:
`decode_prefix_free` (Huffman.lean) says that for `(cw, sym)` in a
prefix-free table, `decode table (cw ++ rest) = some (sym, rest)`.
Extension to symbol sequences is induction on the symbol list.

For length/distance sub-encoding (codes 257–285 + extra bits), the
encode side reverses the table lookup. Invertibility follows because
the tables are monotone and extra bits fill the gaps exactly.

#### Building block 3: Bitstream packing invertibility

```lean
bytesToBits (bitsToBytes bits) = bits    -- for length divisible by 8
```

BitstreamCorrect already proves the unpack direction (`readBit_toBits`,
`readBits_toBits`). The pack direction is new but mechanical.

#### Building block 4: Block framing

- **Stored:** LEN/NLEN header + literal copy. Trivially invertible.
- **Fixed Huffman:** Shared constant tables. Reduces to BB2.
- **Dynamic Huffman:** Tree description (code lengths via RLE +
  code-length Huffman) must round-trip. Tedious but not deep.
- **Block sequence:** BFINAL (1 bit) + BTYPE (2 bits) are fixed-width.
  Symbol 256 terminates compressed blocks. BFINAL=1 marks last block.
- **Cross-block back-references:** LZ77 references can span block
  boundaries (RFC 1951 §2). The decompressor passes accumulated output
  across blocks. Invariant: after block k, output = `data[0..pₖ]`.

#### Building block 5: Composition

Chain BB1–BB4 to obtain the full roundtrip theorem.

#### What exists vs. what's needed

| Building block | Decompressor half (Phase 3) | Compressor half (Phase 4) |
|---|---|---|
| BB1: LZ77 | `resolveLZ77` correctness ✓, `copyLoop_eq_ofFn` ✓ | `matchLZ77` + fundamental theorem |
| BB2: Huffman | `decode_prefix_free` ✓, tree correspondence ✓ | `huffEncode` + sequence roundtrip |
| BB3: Bitstream | `readBit_toBits`, `readBits_toBits` ✓ | `bitsToBytes` + pack roundtrip |
| BB4: Framing | `decodeStored_correct` ✓, `decodeHuffman_correct` ✓, `inflateLoop_correct` (2 minor sorries), `decodeDynamicTrees_correct` (sorry) | Block framing encoder, dynamic tree encoding |
| BB5: Composition | — | Full roundtrip theorem |

### Phase 3: Verified Decompressor

The decompressor contributes the "right half" of each building block.
The verification has two layers, reflecting the structure of DEFLATE:

**Characterizing properties** — mathematical content independent of any
particular implementation:

- Huffman codes are prefix-free and canonical (Huffman.Spec) ✓
- Kraft inequality bounds symbol counts ✓
- Prefix-free codes decode deterministically (`decode_prefix_free`) ✓
- Bitstream operations correspond to LSB-first bit lists ✓
- LZ77 overlap semantics: `copyLoop_eq_ofFn` ✓
- RFC 1951 tables verified by `decide` ✓
- TODO: Fuel independence of spec decode
- TODO: `fromLengths` success implies `ValidLengths`

**Algorithmic correspondence** — the native implementation agrees with
a reference decoder that transcribes RFC 1951 §3.2.3 pseudocode into
proof-friendly style (`List Bool`, `Option` monad, fuel):

- Stored blocks ✓
- Huffman blocks (literal, end-of-block, length/distance cases) ✓
- Block loop (2 minor position-invariant sorries)
- Dynamic Huffman tree decode (sorry — hardest remaining piece)

The reference decoder (`Deflate.Spec.decode`) is not a mathematical
specification — it is the RFC algorithm in proof-friendly dress. At
the block-dispatch level, the RFC IS pseudocode; correspondence with
a faithful transcription is the appropriate verification tool. The
mathematical content lives in the building blocks (Huffman, bitstream,
LZ77), not in the top-level algorithm.

### Phase 4: DEFLATE Compressor

The compressor contributes the "left half" of each building block plus
the composition into the full roundtrip theorem.

**Deliverables** (progressive, each level adds to the previous):

- Level 0: stored blocks, literal copy. Roundtrip trivial.
- Level 1: greedy LZ77 matching, fixed Huffman codes.
  First non-trivial roundtrip — proves BB1 for greedy matching.
- Levels 2–4: lazy matching. Same BB1 invariant with branching.
- Levels 5–9: dynamic Huffman codes. Adds dynamic tree encoding
  roundtrip (BB4) on top of BB1.
- Conformance tests: zlib can decompress our output and vice versa.
- Full roundtrip theorem: `inflate (deflate data level) = data`.

### Phase 5: Zstd (Aspirational)

Native Lean Zstd implementation. This is a separate multi-month to
multi-year project.

**Estimated effort**: PhD thesis scale.

**Deliverables**:
- FSE (Finite State Entropy) decoder and encoder
- Zstd frame/block parsing
- Decompressor with proofs (following the Phase 2-3 pattern)
- Compressor with roundtrip proof

## Conformance Testing Infrastructure

Worth building regardless of proofs. The approach:

1. Generate random `ByteArray` inputs of varying sizes
2. Compress/decompress with both FFI and native implementations
3. Assert byte-for-byte equality of decompressed output
4. For compression, assert cross-compatibility: native compress + FFI
   decompress = original, and FFI compress + native decompress = original
5. Test edge cases: empty input, single byte, large inputs, incompressible
   data, maximum compression ratios

Having two independent implementations tested against each other catches
bugs that neither catches alone.

## References

- **RFC 1951** (Deutsch, 1996), "DEFLATE Compressed Data Format
  Specification version 1.3". The primary specification. Available in
  `references/rfc1951.txt`. Section 3.2.3 contains the decoding
  algorithm pseudocode; Section 3.2.2 defines canonical Huffman codes;
  Section 3.2.5 defines the length/distance tables.

- **RFC 1950** (Deutsch & Gailly, 1996), "ZLIB Compressed Data Format
  Specification version 3.3". Zlib framing around DEFLATE. Available
  in `references/rfc1950.txt`.

- **RFC 1952** (Deutsch, 1996), "GZIP file format specification version
  4.3". Gzip framing around DEFLATE. Available in `references/rfc1952.txt`.

- **Senjak & Hofmann (2016)**, "An implementation of Deflate in Coq",
  arXiv:1609.01220. Available in `references/senjak-hofmann-2016.pdf`
  (LaTeX source in `references/codings.tex`). A complete Coq
  formalization of DEFLATE with a verified roundtrip. The most relevant
  prior art is their canonical prefix-free coding library (Sections
  1–4): uniqueness from code lengths, constructive existence via Kraft
  inequality, 4-axiom characterization. Their relational specification
  framework (Section 5: "strong decidability" / "strong uniqueness")
  is designed for Coq's extraction mechanism and is not adopted here —
  Lean 4 is code-first, so we write the implementation and prove
  characterizing properties about it rather than extracting code from
  relational specifications.

## Bottom Line

| Target | Feasibility | Value |
|--------|------------|-------|
| CRC32/Adler32 with proofs | Do it | Easy and valuable |
| DEFLATE decompressor | Ambitious but tractable | Novel contribution to verified software |
| DEFLATE roundtrip with proofs | Research project (6-12 person-months) | High, if completed |
| Zstd | PhD thesis scale | Very high, but enormous effort |
