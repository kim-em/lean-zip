# Track D state — benchmarking & verified optimization

Durable backlog + status for Track D (PLAN.md §D). This file is the **generative
signal** for optimization work: it is read first when planning Track D, updated
whenever a Track D PR lands, and ranked so the next candidate is always obvious.
Without it, Track D dies between cycles (the queue is dominated by other tracks).

**Dashboard:** [`bench/README.md`](../bench/README.md) — runtime + compression-ratio
comparison of native lean-zip vs zlib / miniz_oxide / libdeflate / zopfli, with
log-scale SVG graphs. Regenerate with `bench/run.sh` and commit the refreshed
`bench/results/latest.json` + `bench/graphs/*.svg` alongside any change that
moves the numbers.

## The loop (per PLAN.md §D methodology)

1. `bench/run.sh` → refresh the dashboard.
2. Profile the dominant cost (Lean profiler) or diff the ratio gap vs the
   reference that wins on that input. **Profiling a compiled driver? Beat Lean's
   laziness twice or every phase reads ~0:** (a) a loop-invariant pure result is
   computed once then the thunk is *memoised* — perturb the input one byte per
   rep; (b) `let v := f x` in a `do`-block is *lazy*, so the work lands at the
   later use *outside* your `t0..t1` window — force `v` (and each phase's forced
   input) through an IO-sequenced branch (e.g. `if v % p == k then pure 1 else
   pure 0`) inside the timed region. Keep the driver out of the committed tree.
3. Pick the top unstarted candidate below.
4. Implement via **generational refinement**: new definition `genN+1`, prove
   `genN+1 = genN` (or component equivalence), transfer the roundtrip theorem.
5. Re-bench; update this file (move the item to *Landed*, record the delta) and
   commit the refreshed graphs.

## Measured gaps (snapshot: see `bench/results/latest.json` meta)

- **Compression throughput**: after D-3 (UInt32 hash) native ≈ 100 MB/s on
  compressible data (was ~10) vs zlib/miniz ≈ 500 MB/s, libdeflate ≈ 1 GB/s — the
  ~50–100× gap is now ~5×. Incompressible (prng) input is ~17 MB/s (more hashing
  per byte, fewer matches to skip over).
- **Compression ratio (text)**: native trails zlib and the zopfli floor.
- ~~**Incompressible input (prng)**: native expands small inputs~~ — **closed by
  D-1** (stored-block fallback); native now matches zlib (≈ 1.005 at 1 KiB).
- **Decompression**: competitive (hundreds of MB/s, same order as zlib).

## Backlog (ranked: impact × tractability)

| ID | Dimension | Candidate | Why / expected effect | Provability |
|----|-----------|-----------|-----------------------|-------------|
| D-2 | runtime | **Profile native `deflateRaw`** to find the dominant cost (allocation, `ByteArray.push` growth, List↔Array conversions, linear LZ77 scan) | Prerequisite for D-3/D-6; turns "10 MB/s" into a named bottleneck. | n/a (measurement). |
| D-4 | ratio | **Stronger lazy matching / longer match search** | Close the text-ratio gap toward zlib. The basic greedy→lazy switch at level ≥ 5 landed as D-8; what remains is a *longer* match search (hash chains / multi-candidate). | Med — still produces a valid token stream (BB1). |

## Landed

| ID | Change | Measured delta | Proof |
|----|--------|----------------|-------|
| D-1 | **Stored-block fallback** — `deflateRaw` now returns `pickSmaller (deflateStoredPure data) (deflateCompressed data level)` for levels ≥ 1, so the output is never larger than a stored block. | prng ratio at 1 KiB **1.058 → 1.005** (1083 → 1029 B), exact parity with zlib; 4 KiB 1.012 → 1.001; compressible data unchanged (`pickSmaller` keeps the compressed form). Runtime unaffected. | `inflate_deflateRaw` / `deflateRaw_pad` / `deflateRaw_goR_pad` re-proved via the new `deflateCompressed_*` lemmas + `inflate_deflateStoredPure`; 0 sorries. The result is provably never larger than `deflateStoredPure data`, so the change can never regress ratio. |
| D-1b | **Fixed-Huffman fallback at high levels** — `deflateCompressed` at levels ≥ 5 now returns `pickSmaller (deflateFixedIter data) (deflateDynamic data)`, so dynamic Huffman's tree-description overhead never makes the output larger than a plain fixed-Huffman block. | level-6 out shrinks where the tree overhead dominated: 1 KiB `constant` **18 → 10 B** (ratio 0.0176 → 0.0098), 1 KiB `cyclic` **47 → 27 B** (0.0459 → 0.0264), 4 KiB `cyclic` 54 → 49 B. No regressions anywhere — both candidates share the greedy LZ77 matcher, so it is a per-input best-of-{fixed, dynamic}. Runtime unaffected. | `inflate_deflateCompressed` / `deflateCompressed_pad` / `deflateCompressed_goR_pad` each wrap the level ≥ 5 case with `unfold pickSmaller; split`, discharging the fixed branch via the existing level-1 fixed-Huffman proof and the dynamic branch via the existing dynamic proof; 0 sorries. The result is provably never larger than either candidate, so it can never regress ratio. |
| D-7 | **Share one LZ77 token stream at level ≥ 5** — D-1b left `deflateCompressed`'s level-≥5 branch as `pickSmaller (deflateFixedIter data) (deflateDynamic data)`, and `deflateFixedIter`/`deflateDynamic` each ran `lz77GreedyIter data` independently, so the matcher (which dominates a compress pass) ran twice over identical input. Factored the dynamic encoder into a tokens-taking `deflateDynamicBlock` (`deflateDynamic` is now a thin wrapper), and rewrote the branch to compute `let tokens := lz77GreedyIter data` once, feeding both `deflateFixedBlock data tokens` and `deflateDynamicBlock data tokens`. | **Equivalence refactor — output byte-identical** (all 144 native rows: `out_size` unchanged; ratios untouched). Level-6 compress throughput ≈ doubles on compressible data — 1 MiB `text` **5.67 → 10.84 MB/s** (1.91×), `cyclic` 5.88 → 11.70 (1.99×), `constant` 5.60 → 11.11 (1.98×) — and **prng 1 MiB 4.06 → 7.09 MB/s (1.75×, a 43% wall-clock cut)**, matching the predicted ~42% from removing the redundant matcher pass. Levels 0–4 unaffected (don't use the shared path). | `inflate_deflateCompressed` / `deflateCompressed_pad` / `deflateCompressed_goR_pad` convert the shared `let` form back to `pickSmaller (deflateFixedIter data) (deflateDynamic data)` via `rw [show … from rfl]` (definitionally equal since `lz77GreedyIter` is deterministic), then reuse the D-1b proofs verbatim; `deflateDynamic_spec` adds `deflateDynamicBlock` to its `unfold` (body unchanged). 0 sorries. |
| D-3 | **UInt32 hash arithmetic** — the matcher's `hash3` computed `(a ^^^ (b<<<5) ^^^ (c<<<10)) % 65536` in boxed `Nat`, once per input byte; Lean's `Nat` bitwise XOR/shift is slow. Compute the XOR/shift in `UInt32` instead, with `.toNat % hashSize` preserving the exact same index. An experiment (`exp/d3-matcher`, not merged) decomposed the cost across variants: the `%`→`&&&` mask, `Array Nat`→`Array UInt32`/sentinel tables, and unchecked array access each contributed ~nothing — **the entire win is the `UInt32` hash arithmetic** (overturning the pre-experiment guess that table cache traffic was the lever). | **Equivalence — output byte-identical** (all native `out_size`/ratios unchanged). Matcher-only ~16× on text / ~4.6× on prng at 1 MiB; **end-to-end level-6 compress: 1 MiB `text` 11.1 → 100.6 MB/s (9.1×), `cyclic` 11.7 → 108.2 (9.3×), `prng` 7.2 → 16.8 (2.3×); 256 KiB `text` 11.0 → 96.4 (8.8×).** | The three `hash3` defs (`lz77Greedy`, `lz77GreedyIter`, `lz77Lazy` — the last shared by `lz77LazyIter`) change identically, so `hash3_eq` stays `rfl` and the `< hashSize` bound (`Nat.mod_lt`, the `%` wrapper preserved) is untouched — **0 new proof obligations, 0 sorries**. |
| D-6 | **Loop-free `BitWriter` bit-packing** — `writeBits`/`writeHuffCode` now merge a whole field into a 64-bit accumulator in one shift/OR and flush whole bytes (`flushAcc`), instead of a per-bit loop. Diagnosis correction: the old packer already flushed *per byte* (it pushed only when a byte filled), so the cost was the per-bit *iteration*, not `ByteArray.push`; on incompressible input `writeHuffCode` (≈58% of the level-6 prng pass) reversed each Huffman code bit-by-bit. The new `writeHuffCode` reverses the code's 16 bits with a branchless swap network (`reverse16`) + one down-shift, making each emitted symbol constant-work. (The List↔Array conversions originally hypothesized for D-6 were confirmed negligible and dropped from the backlog.) | **Output byte-identical** (all 144 native `out_size`/ratios unchanged). Level-6 **prng** compress **1 MiB 16.7 → 22.0 MB/s (1.31×)**, 256 KiB 16.2 → 21.2 (1.31×), 64 KiB 14.8 → 19.2 (1.30×); level-1 prng 1 MiB 23.1 → 29.7 (1.29×). `text`/`cyclic` ≈ 1.0–1.04× (matcher-bound — emit is a small fraction there). **Short of the issue's ≈1.8× target**: emit is now ~2× faster but only ~58% of the prng pass, so the rest needs the matcher constant-factor work (reframed D-3 follow-up). | New `flushAcc_spec` (a 64-bit accumulator holding `total` valid bits flushes to exactly those bits, by `testBit`), `reverse16_testBit` (the swap network flips bit `j`↔`15-j`, `bv_decide` over the 16 positions), and `writeBits_spec`/`writeHuffCode_spec` re-derive the four `_toBits`/`_wf` theorems with **unchanged statements**, so every downstream emit-correctness proof (`EmitTokensCorrect`, `DeflateDynamicEmit`, `DeflateFixedCorrect`, …) transfers verbatim. `writeBits` masks the field with `% (1 <<< n)` (cold path; cleaner to bridge than subtraction). Removed the dead per-bit `addBit` machinery. 0 sorries. |
| D-8 | **Lazy matching at level ≥ 5** — D-7 left the shared level-≥5 token stream as `lz77GreedyIter data`. Switched it to the **lazy** matcher `lz77LazyIter data` (the matcher levels 2–4 already use), so the high level finds better matches and narrows native's text-ratio gap vs zlib. Still one matcher pass feeding both `deflateFixedBlock data tokens` and `deflateDynamicBlock data tokens`. | **Text ratio improves at level 6 at every size** (lazy finds longer matches): 1 MiB `text` **0.0119 → 0.0105** (12431 → 11047 B, −11.1%), 256 KiB 0.0126 → 0.0112 (3291 → 2945 B), 64 KiB 0.0152 → 0.0136 (993 → 892 B), 16 KiB 0.0241 → 0.0220, 1 KiB 0.1797 → 0.1660. `cyclic` unchanged (strictly periodic — lazy finds no better match), `prng` unchanged (stored fallback). **No regression on any pattern.** Compress throughput essentially unchanged — 1 MiB `text` 10.84 → 11.07 MB/s (within run-to-run noise; still ≈ 2× faster than pre-D-7's two greedy passes). | Generalized `deflateDynamic_spec` → `deflateDynamicBlock_spec data tokens htok_enc hempty` (parameter lift: greedy-specific `lz77Greedy_encodable` use replaced by the `htok_enc` hypothesis; the empty-input branch by `hempty`; ~390-line body unchanged) and `inflate_deflateDynamic` → `inflate_deflateDynamicBlock` (adds an `hresolve` hypothesis); both greedy theorems re-derive as the `lz77GreedyIter` instance. The three `deflateCompressed_*` proofs feed the shared lazy tokens through the generalized lemmas via local `lz77LazyIter_{encodable,empty,resolves}` helpers; the fixed branch is `deflateLazyIter` (already proven). 0 sorries. |
| D-9 | **Size-then-emit — emit only the smallest block at level ≥ 5** (#2483). D-8 left the level-≥5 path emitting **all three** candidate blocks (stored + fixed + dynamic) and keeping the smallest via the `pickSmaller` cascade; on incompressible input the stored block wins, so both expensive Huffman symbol emissions were computed and discarded (profile D-2: `emitTokensWithCodes` ≈ 17.6 ms of the 60 ms prng path). Now each candidate's exact byte size is computed from the already-counted `tokenFreqs` as a freq·codeLen dot product (`symbolBitCount`/`fixedBlockBytes`/`dynBlockBytes`, O(#symbols), no bit-banging; the dynamic tree-header bits come from running `writeDynamicHeader` into an empty `BitWriter` and reading its new `bitLength`), and `deflateRaw`/`deflateCompressed` emit only the argmin (same strict-`<` tie-break). The dynamic emit reuses the sized code lengths via a new `deflateDynamicBlockCore` (takes precomputed `litLens`/`distLens`), so the winning tree is built once. | **Equivalence refactor — output byte-identical** (all native `out_size`/ratios unchanged across every row). **prng 1 MiB compress 16.7 → 38.8 MB/s (2.32×)** — both losing Huffman emits skipped; 256 KiB 16.2 → 35.4 (2.19×), 64 KiB 14.8 → 29.5 (1.99×). Compressible patterns also improve once the loser-emit + a redundant length recompute are removed: 1 MiB `text` 99.8 → 109.3 MB/s (1.09×), `cyclic` 109.0 → 113.8 (1.04×). No regression at any size ≥ 4 KiB (1 KiB `text` 0.95×, within noise). | The size helpers are opaque cost models (`@[irreducible]` to keep `split` from unfolding the 286-element fold past `maxRecDepth`); the freq·codeLen identity is **not** proved — the roundtrip theorems hold for whichever block is chosen, and the new `ZipTest/SizeHelpers` conformance tests pin `fixedBlockBytes`/`dynBlockBytes` to the emitted `.size` (so the selection reproduces `pickSmaller` exactly). `inflate_deflateRaw` / `deflateRaw_pad` / `deflateRaw_goR_pad` and the three `deflateCompressed_*` proofs `split` the new size conditions (the level-≥5 winner is one of the unchanged blocks; `deflateDynamicBlockCore … = deflateDynamicBlock data tokens` definitionally, so the dynamic lemmas transfer); `deflateDynamicBlock_spec` is unchanged (its `show` reframe is defeq through the new `Core` layer). 0 sorries. |
| D-5 | **Table-driven Huffman decode for inflate** (#2484). Native inflate decoded each Huffman symbol by walking the `HuffTree` one bit per node (`HuffTree.decode`). Added a `2^9` "fast-bits" lookup table (`HuffTree.buildTable`): slot `i` holds the `(symbol, codeLen)` reached by walking the tree on the bits of `i`. `HuffTree.decodeWithTable` peeks 9 bits (`peekFast`, two direct byte reads), indexes the table, and consumes `codeLen` bits in one step — falling back to the `HuffTree.decode` walk for codes longer than 9 bits and when fewer than `codeLen` bits remain. `Inflate.decodeHuffmanFast` builds the literal/length + distance tables once per block; `inflateLoop` runs it on the **verified route** (no `@[implemented_by]`). | **Equivalence refactor — inflate output byte-identical** (all roundtrip + 1000-iter fuzz tests pass; ratios untouched). **Decompress speedup on Huffman-decode-bound input** (the regime the table targets): a non-periodic `words` pattern (PRNG-ordered English words → many short matches + literals) decodes at **64 KiB 28.7 MB/s, 1 MiB 29.0 MB/s** vs the old bit-by-bit walk's ~20.5/21.5 (≈1.35–1.4×). The four periodic patterns are copy/stored-bound for *decode* (long matches or stored blocks) so they barely move — the table only helps where symbol decoding dominates. | **Formal proof, not `@[implemented_by]`** (Kim's call). `Zip.Spec.InflateTable.decodeWithTable_eq` proves `decodeWithTable (buildTable tree) br = decode tree br` as a full `Except` result (same symbol *and* reader): `tableEntry.go` reaching a leaf gives a `TreeHasLeaf` path = `cwOf idx len` (codeword from the peeked bits); `peekFast`'s bits match the stream (`peekFast_testBit`, UInt32↔Nat `testBit` accounting); `decode_go_complete` turns that into the tree-walk result; the advanced reader equals the walk's by `toBits` + cursor-bound (`advReader_eq`). `decodeHuffmanFast_eq` lifts it to the block loop by functional induction; `inflateLoop`'s correctness/completeness/suffix/bound proofs transfer with one `rw [decodeHuffmanFast_eq]` each. A `decodeWithTable` guard on `bitOff ≥ 8` makes the equality unconditional (no wf side-goals at transfer sites). 0 sorries; `ZipTest/InflateTable` adds a differential sanity check over every code-length regime. |

## Profile findings (D-2)

Per-phase wall-clock profile of the native level-6 compress path
(`Zip.Native.Deflate.deflateRaw data 6`), measured 2026-06-02 with a throwaway
compiled driver (per-rep one-byte input perturbation to defeat thunk memoisation;
each phase's input forced *before* the timed region so attribution is clean; min
of 7 reps). Driver kept out of the tree per the issue scope guard.

**Machine / inputs:** AMD EPYC 9455 (single-threaded), Lean `v4.30.0-rc2`, Linux
6.12.85. Inputs mirror `ZipBench.lean`: `text` (cycled English words, highly
compressible) and `prng` (LCG bytes, incompressible) at 64 KiB / 256 KiB / 1 MiB.

Per-phase min times (µs), 1 MiB inputs:

| Phase | text 1 MiB | prng 1 MiB |
|-------|-----------:|-----------:|
| `lz77GreedyIter` (matcher) | **87 471** | **104 011** |
| `tokenFreqs` (freq count) | 385 | 4 203 |
| `computeCodeLengths` (tree build) | 65 | 562 |
| `emitTokensWithCodes` (bit pack) | 540 | 17 569 |
| `deflateStoredPure` | 168 | 177 |
| `deflateFixedIter` (full = matcher + emit) | 87 994 | 123 105 |
| `deflateDynamic` (full = matcher + freq + tree + emit) | 88 203 | 121 721 |
| **`deflateRaw` level 6 (FULL)** | **176 944** | **244 964** |

The matcher scales linearly (matcher µs at 64 KiB→256 KiB→1 MiB is 6 476 → 26 191
→ 104 011 for prng, i.e. ~4× per 4× size), so `Array.set!` on the 65536-entry
hash tables is in-place (O(1)) — **there is no quadratic blow-up**. The cost is a
per-byte constant factor of ~100 ns/byte → ≈ 10 MB/s, which *is* the headline gap.

### Top hotspots

1. **The LZ77 matcher `lz77GreedyIter` dominates.** On `text` it is 99% of a
   single compress pass (87 471 of 87 994 µs); on `prng` it is 85% (104 011 of
   123 105). Suspected cause: per-byte constant factor — boxed-`Nat` hashing and
   positions, two `Array.set!` into cache-unfriendly 65536-entry tables per byte,
   byte-by-byte `countMatch`, and an `Array.push` per token. *Note:* the backlog's
   D-3 row calls this a "linear scan" — that premise is wrong. The matcher is
   already a single-probe hash (one candidate per position), so it is O(n); a
   hash *chain* would improve **ratio**, not speed. D-3 should be reframed as
   "shrink the matcher's per-byte constant factor (boxed-`Nat` → `UInt32`/`USize`,
   tighter inner loop)".

2. **The whole pipeline runs twice at level ≥ 5.** `deflateRaw` →
   `pickSmaller (deflateStoredPure) (deflateCompressed)` and `deflateCompressed`
   (level ≥ 5) → `pickSmaller (deflateFixedIter data) (deflateDynamic data)`.
   `deflateFixedIter` and `deflateDynamic` each call `lz77GreedyIter data`
   independently, so the **dominant phase runs twice** and the token stream is
   built twice. The measured full path (244 964 µs prng) ≈ `deflateFixedIter`
   (123 105) + `deflateDynamic` (121 721) + stored (177): the second matcher pass
   is ~42% of total wall-clock, pure redundancy (the token stream is identical).

### Proposed next issue

**D-7 (runtime): share one LZ77 token stream between the fixed and dynamic
encoders at level ≥ 5.** Refactor `deflateCompressed`'s level-≥5 branch to compute
`tokens := lz77GreedyIter data` once and feed both `deflateFixedBlock data tokens`
and a tokens-taking dynamic encoder, instead of `pickSmaller (deflateFixedIter
data) (deflateDynamic data)` (each of which recomputes tokens). Expected effect:
removes one full matcher pass — **≈ 42% wall-clock cut** on the level-6 path
(244 964 → ~141 000 µs on prng 1 MiB) plus one redundant `tokenFreqs`/emit.
Provability: **High** — `lz77GreedyIter data` is deterministic, so the shared and
recomputed token streams are definitionally equal; the existing
`inflate_deflateCompressed` / `_pad` proofs transfer by rewriting both encoders to
their `…Block data (lz77GreedyIter data)` form before the `pickSmaller` split.
(The deeper matcher constant-factor work is the reframed D-3, a larger follow-up.)

## Orchestration hook (optional, not yet wired)

To keep the fleet feeding Track D rather than starving it, a future `/plan`
liveness step can: when `gh issue list --label track-d` is empty and the queue
has a deficit, create one `track-d` issue from the top unstarted backlog row
above. Pair it with an Orchestrator-Policy rule mirroring the standing Track E
queue (PLAN.md). Until then, Track D is driven directly from this file.
