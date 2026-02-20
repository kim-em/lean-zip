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

### Phase 3: Verified Decompressor

Prove DEFLATE decompression correct against a formalized RFC 1951 subset.
This is the research-grade contribution.

**Estimated effort**: Months.

**Deliverables**:
- Formal specification of valid DEFLATE bitstreams in Lean
- Proof that `inflate` produces the unique correct output for any valid
  bitstream
- Proof that `inflate` rejects invalid bitstreams

This is the sweet spot of the project. Decompression is deterministic, the
algorithm is well-understood, and a verified decompressor has clear
practical value: you trust decompression more than compression in
adversarial contexts (processing untrusted archives).

**Prior art**: Senjak & Hofmann's Coq formalization (see References)
contains directly relevant proof techniques:
- Their Definition 1 gives a 4-axiom characterization of canonical
  prefix-free codings (prefix-free, shorter-precedes-longer,
  same-length-ordered-by-symbol, no-gaps). Compare against our
  `Huffman.Spec` axiomatization for completeness.
- Theorem 1 (uniqueness from code lengths): proved by contradiction —
  take the lex-smallest differing code and derive a contradiction via
  the no-gaps axiom. Relevant to `codeFor_injective` and the
  different-length case of `canonical_prefix_free`.
- Theorem 3 (constructive existence via Kraft inequality): validates
  the `ValidLengths` / Kraft-based approach.
- Section 5 (strong decidability / strong uniqueness): a relational
  framework for specifying encoding relations and extracting verified
  parsers. Their bind-like combinator for composing relations preserves
  both properties, enabling modular parser construction. Worth studying
  as an approach for the overall decompressor correctness proof.

### Phase 4: DEFLATE Compressor

Pure Lean DEFLATE compressor, starting with simple strategies (level 0
stored, level 1 greedy matching). Prove roundtrip correctness.

**Estimated effort**: Months.

**Deliverables**:
- Level 0 (stored blocks, no compression)
- Level 1 (greedy LZ77 matching, fixed Huffman codes)
- Higher levels as desired (lazy matching, dynamic Huffman codes)
- Proof: `inflate (deflate data level) = data` for implemented levels
- Conformance tests: verify zlib can decompress our output and vice versa

**Prior art**: Senjak & Hofmann (2016) proved `decompress(compress(d)) = d`
in Coq using a relational specification with monadic combinators
(Sections 5-6). Their approach defines encoding as a relation
`OutputType → InputType → Prop`, proves strong decidability (which
extracts a parser), then proves a compression function produces output
satisfying the relation. This is one viable approach; a more direct
functional proof may also work in Lean 4.

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

- **Senjak & Hofmann (2016)**, "An implementation of Deflate in Coq",
  arXiv:1609.01220. A complete Coq formalization of DEFLATE (RFC 1951)
  with a verified compression/decompression roundtrip. Includes a fully
  verified canonical prefix-free coding library (uniqueness, existence
  via Kraft inequality), a backreference resolver using exponential
  lists, and a relational specification framework ("strong decidability"
  / "strong uniqueness") for composing and extracting verified parsers.
  The extracted Haskell implementation handles multi-megabyte inputs.
  This is the closest prior work to lean-zip's verification effort; the
  main differences are the proof assistant (Coq vs Lean 4), the
  extraction approach (Coq extraction to Haskell vs native Lean), and
  performance characteristics.

## Bottom Line

| Target | Feasibility | Value |
|--------|------------|-------|
| CRC32/Adler32 with proofs | Do it | Easy and valuable |
| DEFLATE decompressor | Ambitious but tractable | Novel contribution to verified software |
| DEFLATE roundtrip with proofs | Research project (6-12 person-months) | High, if completed |
| Zstd | PhD thesis scale | Very high, but enormous effort |
