# Verification Plan for lean-zip

This document outlines a plan to add parallel native Lean implementations
alongside the existing FFI wrappers, add conformance tests between the
two, formally prove properties of the native implementations, and then
iteratively optimize the native implementations with verified correctness.

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

## Optimization Strategy

### Initial approach: clarity first

Start with naive, easy-to-reason-about Lean implementations and prove
correctness properties about these first. These initial versions prioritize
clarity over performance: simple loops instead of table lookups for CRC32,
straightforward linear scans instead of hash chains for LZ77 matching,
direct bit-by-bit Huffman decoding instead of table-based multi-bit lookups.

Once the core proofs are established against these simple implementations,
we add progressively more efficient versions and prove they produce
identical output to the unoptimized versions. The roundtrip proofs then
transfer automatically: if `inflate_fast` is proven equivalent to
`inflate_simple`, and we have proven
`inflate_simple (deflate data level) = data`, then
`inflate_fast (deflate data level) = data` follows immediately.

### Compression levels

Rather than implementing all nine DEFLATE compression levels at once, we
work through them progressively:

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

### Generational refinement

After the initial roundtrip theorem is established, optimization follows
a generational approach. The key insight is that optimizing verified code
is fundamentally different from optimizing unverified code: you cannot
simply swap in a faster algorithm and check if tests pass — you must
prove the new version agrees with the old one.

There are two approaches, chosen based on the scope of the change:

**Approach 1: In-place modification.** For small, local changes (e.g.
replacing a linear scan with a hash lookup in one function), modify the
implementation directly and update the proofs that it still satisfies its
specification. This works well when the proof structure survives the change
with modest adjustments.

**Approach 2: Generational refinement.** For larger changes (restructuring
data flow, changing representations, rewriting a pipeline stage), build a
new implementation alongside the existing one:

1. Write the faster implementation (Gen N+1) as a new definition
2. Prove `genN_plus_1 = genN` (or the relevant component equivalence)
3. Transfer the roundtrip theorem across the equivalence
4. The old implementation (Gen N) remains in the codebase — theorems
   reference it

This naturally produces a chain: Gen 0 (spec) → Gen 1 (first native) →
Gen 2 (optimized) → ... Each generation exists in the codebase because
theorems reference it. The chain is the proof trail.

**Identifying what to optimize.** Benchmarking means profiling, not just
timing. Use Lean's profiling tools to identify where time is actually
spent — allocation patterns, ByteArray copying, List-to-Array conversions,
unnecessary intermediate structures. These are all algorithmic choices
that can be improved in the next generation. A List-to-Array conversion
that dominates runtime is as much a target for generational refinement as
a change from linear to binary search.

**Chain compression.** Over time, the chain of generations may become long.
Periodically, it is worth "compressing the chain" — proving that Gen N+2
directly equals Gen N, eliminating Gen N+1 as an intermediate. This
simplifies the codebase and the proof dependencies. But don't do this
reflexively: if an intermediate generation captures a genuinely different
algorithmic idea, keep it — it serves as documentation of the design
evolution. Compress when the intermediate's only purpose is as a proof
stepping stone and the direct proof is clearly shorter. Sometimes it may
also be possible to *permute* changes in the chain, bringing related
improvements together and enabling further compressions.

**When to stop.** Optimization is open-ended. A reasonable stopping point:
when the native Lean implementation is competitive with or faster than the
FFI-wrapped C libraries on representative workloads!

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

### Overview

The work is organized into a linear **A-track** (DEFLATE verification
pipeline) followed by parallel tracks **B**, **C**, and **D** that can
be worked on concurrently. Two cross-cutting concerns run throughout.

**Dependency graph:**

```
A1 → A2 → A3 → A4
      │    │
      ↓    ↓
      C    B
D (independent)
```

- **A1–A4** are sequential: each depends on the previous.
- **B** (size limit elimination) depends on A3: fuel-based proofs must
  exist before they can be replaced with well-founded recursion.
- **C** (benchmarking and optimization) depends on A2: native
  implementations must exist before they can be profiled.
- **D** (Zstd) is independent: it follows the same A1–A4 methodology
  for a different compression format and can start at any time.
- **Cross-cutting concerns** (characterizing properties, ZipForStd)
  apply from A1 onwards and are not gated on any particular phase.

Planning agents should spread work across tracks wherever dependencies
allow, rather than finishing one track before starting another.

### A1: Checksums

Pure Lean CRC32 and Adler32 with proofs of equivalence to a formal
specification. Conformance tests against the FFI implementations.

**Deliverables**:
- Native Lean CRC32 (table-driven)
- Native Lean Adler32
- Proof: table-driven CRC32 matches bit-by-bit definition
- Proof: incremental computation composes correctly
- Conformance test harness comparing native vs FFI on random inputs

### A2: DEFLATE Decompressor

Pure Lean DEFLATE decompressor (inflate only). No proofs yet.

**Deliverables**:
- Huffman decoder (fixed and dynamic trees)
- LZ77 back-reference resolution with sliding window
- Gzip/Zlib framing (header/trailer parsing, checksum verification)
- Conformance tests against zlib on a corpus of compressed data
- Integration as an alternative backend for existing ZIP/tar code paths

### A3–A4: Verified DEFLATE Roundtrip

The overarching goal:

```
∀ (data : ByteArray) (level : Fin 10), inflate (deflate data level) = .ok data
```

(Both `inflate` and `deflate` return `Except String ByteArray`; the
theorem says compression always succeeds and decompression of
well-formed output never fails.)

The roundtrip decomposes into five building blocks. The decompressor
(A3) contributes the "right half" of each invertibility theorem;
the compressor (A4) contributes the "left half." Each building
block is independently meaningful.

#### The roundtrip pipeline

For levels 1–9 (compressed blocks), the data flows through three
invertible layers:

```
data → matchLZ77 → symbols → huffEncode → bits → pack → compressed
                                                          │
compressed → unpack → bits → huffDecode → symbols → resolveLZ77 → data
```

Level 0 (stored blocks) bypasses LZ77 and Huffman entirely — the
roundtrip reduces to stored-block framing (BB4) alone.

For levels 1–9, the full proof chains three invertibility steps:

```
  inflate (deflate data level)
= resolveLZ77 (huffDecode (unpack (pack (huffEncode (matchLZ77 data)))))
= resolveLZ77 (huffDecode (huffEncode (matchLZ77 data)))  -- bitstream
= resolveLZ77 (matchLZ77 data)                            -- Huffman
= data                                                    -- LZ77
```

(Simplified — actual proof routes through block framing via BB4.)

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
-- Given valid canonical code lengths producing prefix-free tables:
decodeSymbols litLens distLens (encodeSymbols litLens distLens syms ++ rest)
  = some (syms, rest)
```

Requires that `litLens` and `distLens` produce valid prefix-free codes
(established by `fromLengths` success + `ValidLengths`), and that the
symbol list is well-formed (literals < 256, lengths in 3–258, distances
in 1–32768, terminated by end-of-block).

The single-symbol case is the core lemma:
`decode_prefix_free` says that for `(cw, sym)` in a prefix-free table,
`decode table (cw ++ rest) = some (sym, rest)`. Extension to symbol
sequences is induction on the symbol list.

For length/distance sub-encoding (codes 257–285 + extra bits), the
encode side reverses the table lookup. Invertibility follows because
the tables are monotone and extra bits fill the gaps exactly.

#### Building block 3: Bitstream packing invertibility

```lean
bytesToBits (bitsToBytes bits) = bits
```

Holds when `bits.length` is a multiple of 8 (byte-aligned). In
practice, DEFLATE block encoding pads the final byte, so the theorem
applies to the padded bit sequence; the padding itself is handled at
the block framing level (BB4).

#### Building block 4: Block framing

- **Stored:** LEN/NLEN header + literal copy. Trivially invertible.
- **Fixed Huffman:** Shared constant tables. Reduces to BB2.
- **Dynamic Huffman:** Tree description (code lengths via RLE +
  code-length Huffman) must round-trip. Mechanically detailed and
  the hardest framing sub-proof.
- **Block sequence:** BFINAL (1 bit) + BTYPE (2 bits) are fixed-width.
  Symbol 256 terminates compressed blocks. BFINAL=1 marks last block.
- **Cross-block back-references:** LZ77 references can span block
  boundaries (RFC 1951 §2). The decompressor passes accumulated output
  across blocks. Invariant: after block k, output = `data[0..pₖ]`.

#### Building block 5: Composition

Chain BB1–BB4 to obtain the full roundtrip theorem.

#### Proof architecture by phase

| Building block | Decompressor half (A3) | Compressor half (A4) |
|---|---|---|
| BB1: LZ77 | `resolveLZ77` correctness, `copyLoop_eq_ofFn` | `matchLZ77` + fundamental theorem |
| BB2: Huffman | `decode_prefix_free`, tree correspondence | `huffEncode` + sequence roundtrip |
| BB3: Bitstream | `readBit_toBits`, `readBits_toBits` | `bitsToBytes` + pack roundtrip |
| BB4: Framing | `decodeStored_correct`, `decodeHuffman_correct`, `inflateLoop_correct`, `decodeDynamicTrees_correct` | Block framing encoder, dynamic tree encoding |
| BB5: Composition | — | Full roundtrip theorem |

#### A3: Verified Decompressor

The decompressor contributes the "right half" of each building block.
The verification has two layers, reflecting the structure of DEFLATE:

**Characterizing properties** — mathematical content independent of any
particular implementation:

- Huffman codes are prefix-free and canonical
- Kraft inequality bounds symbol counts
- Prefix-free codes decode deterministically (`decode_prefix_free`)
- Bitstream operations correspond to LSB-first bit lists
- LZ77 overlap semantics: `copyLoop_eq_ofFn`
- RFC 1951 tables verified by `decide`
- Fuel independence of spec decode
- `fromLengths` success implies `ValidLengths`

**Algorithmic correspondence** — the native implementation agrees with
a reference decoder that transcribes RFC 1951 §3.2.3 pseudocode into
proof-friendly style (`List Bool`, `Option` monad, fuel):

- Stored blocks
- Huffman blocks (literal, end-of-block, length/distance cases)
- Block loop with position invariants
- Dynamic Huffman tree decode

The reference decoder (`Deflate.Spec.decode`) is not a mathematical
specification — it is the RFC algorithm in proof-friendly dress. At
the block-dispatch level, the RFC IS pseudocode; correspondence with
a faithful transcription is the appropriate verification tool. The
mathematical content lives in the building blocks (Huffman, bitstream,
LZ77), not in the top-level algorithm.

#### A4: DEFLATE Compressor

The compressor contributes the "left half" of each building block plus
the composition into the full roundtrip theorem.

**Deliverables** (progressive, each level adds to the previous):

- Level 0: stored blocks, literal copy. Roundtrip trivial.
- Level 1: greedy LZ77 matching, fixed Huffman codes.
  Establishes BB1 for greedy matching; combines with BB2–BB4 for the
  first non-trivial end-to-end roundtrip.
- Levels 2–4: lazy matching. Same BB1 invariant with branching.
- Levels 5–9: dynamic Huffman codes. Adds dynamic tree encoding
  roundtrip (BB4) on top of BB1.
- Conformance tests: zlib can decompress our output and vice versa.
- Full roundtrip theorem: `inflate (deflate data level) = .ok data`.

### B: Size Limit Elimination

**Depends on: A3**

The initial roundtrip theorem uses fuel parameters (explicit recursion
bounds) to ensure termination. This imposes a data size limit on the
theorem — e.g. `data.size < N` for some concrete `N`. The limit is an
artifact of the proof technique, not a fundamental constraint: DEFLATE
decompression always terminates (each iteration consumes at least one
bit), and compression always terminates (each step advances at least one
byte in the input).

This track has two stages:

**B1: Raise bounds to huge.** If the fuel is computed from `data.size`,
the bound may already be large. If it is a fixed constant, raise it to
an astronomically large value (exabyte scale). This should require only
modest proof adjustments and eliminates the bound as a practical concern.

**B2: Eliminate fuel entirely.** Replace fuel-based recursion with
well-founded recursion on a decreasing measure (remaining input length
for decompression, remaining unprocessed bytes for compression). This
requires restructuring the recursive functions so that Lean's termination
checker can verify progress. The result is a roundtrip theorem with no
size restriction at all:

```
∀ (data : ByteArray) (level : Fin 10), inflate (deflate data level) = .ok data
```

B2 is a significant redesign of the proof-friendly spec functions.
The native implementations will likely use structural patterns that
terminate naturally — the main work is in the spec layer and the proofs.

### C: Benchmarking and Verified Optimization

**Depends on: A2**

This track is open-ended. It has two dimensions: **runtime performance**
(how fast the code runs) and **compression quality** (how small the
output is). Both matter, and both follow the same generational
refinement methodology.

**Comparison targets.** The native implementations should be compared
against multiple reference compressors, not just zlib:

- **zlib** — the ubiquitous baseline
- **miniz_oxide** — Rust reimplementation of miniz, widely used
- **libdeflate** — optimized DEFLATE library, often faster than zlib
- **zopfli** — Google's maximum-compression DEFLATE encoder (very slow,
  very small output — the upper bound on DEFLATE quality)

Different targets illuminate different things: zlib and miniz_oxide
are the "match this" bar for general use; libdeflate shows what's
possible with careful optimization; zopfli shows the theoretical
compression quality ceiling within the DEFLATE format.

**Reporting tools.** Build and maintain dashboards that make it easy to
see where we stand:

- **Runtime comparison**: native vs each reference library, across data
  patterns (constant, cyclic, text, incompressible), sizes (1KB to
  100MB), and compression levels (0–9). Report throughput in MB/s for
  both compression and decompression.
- **Compression quality comparison**: output sizes for the same inputs
  across native levels and each reference library's levels. Report both
  absolute sizes and ratios relative to the best-known result (zopfli).
- **Regression tracking**: store benchmark results so that optimization
  work can be validated against a baseline and regressions caught.

These tools are first-class deliverables, not afterthoughts.

**Methodology:**

1. **Benchmark** runtime and compression quality against reference
   implementations on representative workloads.
2. **Profile** using Lean's profiling tools to identify where time is
   spent — not just which functions are slow, but why: allocation
   patterns, ByteArray copying, intermediate List/Array conversions,
   redundant traversals. For compression quality, analyze where the
   native compressor makes worse choices than the reference (shorter
   matches found, suboptimal block boundaries, less efficient Huffman
   trees).
3. **Identify** the highest-impact improvement target across both
   dimensions.
4. **Implement** the optimization using generational refinement
   (Approach 1 or 2 from the Optimization Strategy section).
5. **Prove** correctness of the optimized version.
6. **Re-benchmark** to measure the improvement.
7. **Repeat** from step 2.

This cycle continues until the native implementations are competitive
with or faster than the C libraries on both runtime and compression
quality. At that point, the FFI wrappers become optional — the native
path is verified, performant, and compresses well.

### D: Zstd

**Independent — can start at any time.**

Native Lean Zstd implementation following the same A1–A4 methodology.
This is a separate multi-month to multi-year project.

**Deliverables**:
- FSE (Finite State Entropy) decoder and encoder
- Zstd frame/block parsing
- Decompressor with proofs (following the A2–A3 pattern)
- Compressor with roundtrip proof (following the A4 pattern)

The same B and C tracks apply to Zstd once its A-track is sufficiently
advanced.

## Cross-Cutting Concerns

These are not phases — they apply throughout all work from A1 onwards.

### Characterizing Properties

Beyond roundtrip correctness, prove mathematical properties that are
independent of any particular implementation. These deepen the
verification and catch classes of bugs that roundtrip alone cannot.

Examples, to be pursued as the relevant algorithms are implemented:

- **Prefix-freeness and Kraft inequality** for Huffman codes
- **Compression ratio bounds**: stored blocks have at most ~0.05%
  overhead; fixed Huffman has known worst-case expansion; dynamic
  Huffman is bounded by the entropy of the symbol distribution
- **Determinism of decompression**: any correct DEFLATE decompressor
  must produce the same output for the same input (follows from
  prefix-freeness + deterministic LZ77 resolution)
- **CRC32 as polynomial division** in GF(2)[x], beyond just
  table-implementation equivalence

These properties are not gated on optimization or size limit work.
They can and should be pursued as soon as the relevant algorithms
exist, starting from A1.

### ZipForStd / Standard Library Pipeline

During proof work, lemmas about `ByteArray`, `Array`, `List`, `Nat`,
and `BitVec` are routinely developed that have nothing to do with
compression — they are general-purpose facts missing from Lean's
standard library.

These should be:

1. Collected in `ZipForStd/` as they are developed
2. Kept general (no compression-specific assumptions)
3. In a form where collaborators could upstreamt them to Lean's standard library via PRs

This is part of every phase, not a separate effort. A healthy ZipForStd
pipeline demonstrates that the verification methodology scales and
contributes back to the ecosystem.

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

## Design Considerations

- **Performance**: An initial naive Lean DEFLATE implementation will be
  slower than zlib (which is hand-tuned C with SIMD specializations).
  The FFI implementations serve as the fast path until Track C closes
  the gap through iterative profiling and verified optimization.
- **Specification gap**: RFC 1951 is informal English. Senjak & Hofmann
  (2016) formalized it in Coq (see References below), but no Lean 4
  formalization exists. Formalizing the spec is a prerequisite for
  proving anything about an implementation.
- **Compression level fidelity**: Different DEFLATE compressors (zlib,
  miniz_oxide, libdeflate, etc.) all produce different byte streams —
  the format only specifies decompression, not compression choices.
  Byte-for-byte output matching is a non-goal. Compression *quality*
  (output sizes), however, is a goal — Track C targets competitive
  ratios across all levels.
- **Sliding window management**: Mutable arrays in Lean require careful
  handling of linearity/borrowing for performance.
- **Huffman tree construction proofs**: Code length limits, canonical
  ordering — tedious but not deep.
- **LZ77 match-finding**: Inherently heuristic. Proving it produces
  *valid* output is tractable; proving it produces *good* output
  (compression ratio bounds) is a characterizing property target.
- **Zstd is a moving target**: The format is complex and has evolved; the
  RFC (3.1) is 100+ pages.

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
