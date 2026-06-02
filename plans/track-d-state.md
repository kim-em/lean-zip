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
| D-6 | runtime | **Remove hot-path List↔Array/ByteArray conversions** | Constant-factor compression + decompression speedup. | High — local representation-equivalence. |

## Landed

| ID | Change | Measured delta | Proof |
|----|--------|----------------|-------|
| D-1 | **Stored-block fallback** — `deflateRaw` now returns `pickSmaller (deflateStoredPure data) (deflateCompressed data level)` for levels ≥ 1, so the output is never larger than a stored block. | prng ratio at 1 KiB **1.058 → 1.005** (1083 → 1029 B), exact parity with zlib; 4 KiB 1.012 → 1.001; compressible data unchanged (`pickSmaller` keeps the compressed form). Runtime unaffected. | `inflate_deflateRaw` / `deflateRaw_pad` / `deflateRaw_goR_pad` re-proved via the new `deflateCompressed_*` lemmas + `inflate_deflateStoredPure`; 0 sorries. The result is provably never larger than `deflateStoredPure data`, so the change can never regress ratio. |
| D-1b | **Fixed-Huffman fallback at high levels** — `deflateCompressed` at levels ≥ 5 now returns `pickSmaller (deflateFixedIter data) (deflateDynamic data)`, so dynamic Huffman's tree-description overhead never makes the output larger than a plain fixed-Huffman block. | level-6 out shrinks where the tree overhead dominated: 1 KiB `constant` **18 → 10 B** (ratio 0.0176 → 0.0098), 1 KiB `cyclic` **47 → 27 B** (0.0459 → 0.0264), 4 KiB `cyclic` 54 → 49 B. No regressions anywhere — both candidates share the greedy LZ77 matcher, so it is a per-input best-of-{fixed, dynamic}. Runtime unaffected. | `inflate_deflateCompressed` / `deflateCompressed_pad` / `deflateCompressed_goR_pad` each wrap the level ≥ 5 case with `unfold pickSmaller; split`, discharging the fixed branch via the existing level-1 fixed-Huffman proof and the dynamic branch via the existing dynamic proof; 0 sorries. The result is provably never larger than either candidate, so it can never regress ratio. |
| D-7 | **Share one LZ77 token stream at level ≥ 5** — D-1b left `deflateCompressed`'s level-≥5 branch as `pickSmaller (deflateFixedIter data) (deflateDynamic data)`, and `deflateFixedIter`/`deflateDynamic` each ran `lz77GreedyIter data` independently, so the matcher (which dominates a compress pass) ran twice over identical input. Factored the dynamic encoder into a tokens-taking `deflateDynamicBlock` (`deflateDynamic` is now a thin wrapper), and rewrote the branch to compute `let tokens := lz77GreedyIter data` once, feeding both `deflateFixedBlock data tokens` and `deflateDynamicBlock data tokens`. | **Equivalence refactor — output byte-identical** (all 144 native rows: `out_size` unchanged; ratios untouched). Level-6 compress throughput ≈ doubles on compressible data — 1 MiB `text` **5.67 → 10.84 MB/s** (1.91×), `cyclic` 5.88 → 11.70 (1.99×), `constant` 5.60 → 11.11 (1.98×) — and **prng 1 MiB 4.06 → 7.09 MB/s (1.75×, a 43% wall-clock cut)**, matching the predicted ~42% from removing the redundant matcher pass. Levels 0–4 unaffected (don't use the shared path). | `inflate_deflateCompressed` / `deflateCompressed_pad` / `deflateCompressed_goR_pad` convert the shared `let` form back to `pickSmaller (deflateFixedIter data) (deflateDynamic data)` via `rw [show … from rfl]` (definitionally equal since `lz77GreedyIter` is deterministic), then reuse the D-1b proofs verbatim; `deflateDynamic_spec` adds `deflateDynamicBlock` to its `unfold` (body unchanged). 0 sorries. |
| D-3 | **UInt32 hash arithmetic** — the matcher's `hash3` computed `(a ^^^ (b<<<5) ^^^ (c<<<10)) % 65536` in boxed `Nat`, once per input byte; Lean's `Nat` bitwise XOR/shift is slow. Compute the XOR/shift in `UInt32` instead, with `.toNat % hashSize` preserving the exact same index. An experiment (`exp/d3-matcher`, not merged) decomposed the cost across variants: the `%`→`&&&` mask, `Array Nat`→`Array UInt32`/sentinel tables, and unchecked array access each contributed ~nothing — **the entire win is the `UInt32` hash arithmetic** (overturning the pre-experiment guess that table cache traffic was the lever). | **Equivalence — output byte-identical** (all native `out_size`/ratios unchanged). Matcher-only ~16× on text / ~4.6× on prng at 1 MiB; **end-to-end level-6 compress: 1 MiB `text` 11.1 → 100.6 MB/s (9.1×), `cyclic` 11.7 → 108.2 (9.3×), `prng` 7.2 → 16.8 (2.3×); 256 KiB `text` 11.0 → 96.4 (8.8×).** | The three `hash3` defs (`lz77Greedy`, `lz77GreedyIter`, `lz77Lazy` — the last shared by `lz77LazyIter`) change identically, so `hash3_eq` stays `rfl` and the `< hashSize` bound (`Nat.mod_lt`, the `%` wrapper preserved) is untouched — **0 new proof obligations, 0 sorries**. |
| D-8 | **Lazy matching at level ≥ 5** — D-7 left the shared level-≥5 token stream as `lz77GreedyIter data`. Switched it to the **lazy** matcher `lz77LazyIter data` (the matcher levels 2–4 already use), so the high level finds better matches and narrows native's text-ratio gap vs zlib. Still one matcher pass feeding both `deflateFixedBlock data tokens` and `deflateDynamicBlock data tokens`. | **Text ratio improves at level 6 at every size** (lazy finds longer matches): 1 MiB `text` **0.0119 → 0.0105** (12431 → 11047 B, −11.1%), 256 KiB 0.0126 → 0.0112 (3291 → 2945 B), 64 KiB 0.0152 → 0.0136 (993 → 892 B), 16 KiB 0.0241 → 0.0220, 1 KiB 0.1797 → 0.1660. `cyclic` unchanged (strictly periodic — lazy finds no better match), `prng` unchanged (stored fallback). **No regression on any pattern.** Compress throughput essentially unchanged — 1 MiB `text` 10.84 → 11.07 MB/s (within run-to-run noise; still ≈ 2× faster than pre-D-7's two greedy passes). | Generalized `deflateDynamic_spec` → `deflateDynamicBlock_spec data tokens htok_enc hempty` (parameter lift: greedy-specific `lz77Greedy_encodable` use replaced by the `htok_enc` hypothesis; the empty-input branch by `hempty`; ~390-line body unchanged) and `inflate_deflateDynamic` → `inflate_deflateDynamicBlock` (adds an `hresolve` hypothesis); both greedy theorems re-derive as the `lz77GreedyIter` instance. The three `deflateCompressed_*` proofs feed the shared lazy tokens through the generalized lemmas via local `lz77LazyIter_{encodable,empty,resolves}` helpers; the fixed branch is `deflateLazyIter` (already proven). 0 sorries. |
| D-5 | **Table-driven Huffman decode for inflate** — native inflate decoded each Huffman symbol by walking the `HuffTree` one bit per node (`HuffTree.decode`). Added a `2^9` "fast-bits" lookup table (`HuffTree.buildTable`): slot `i` holds the `(symbol, codeLen)` reached by walking the tree on the bits of `i`. `HuffTree.decodeWithTable` peeks 9 bits (`peekFast`, two direct byte reads), indexes the table, and consumes `codeLen` bits in one step — falling back to the `HuffTree.decode` walk for codes longer than 9 bits and when fewer than `codeLen` bits remain. `Inflate.decodeHuffmanFast` builds the literal/length + distance tables once per block and routes `decodeHuffman`'s runtime via `@[implemented_by]`; the bit-by-bit walk stays the canonical spec, so **every existing inflate correctness proof is untouched**. | **Decompress speedup on Huffman-decode-bound input** (the regime the table targets). The four existing bench patterns are all copy- or stored-bound for *decode* (`constant`/`cyclic`/`text` compress into a few very long matches → LZ77-copy-dominated; `prng` → stored blocks), so they barely move; added a **non-periodic `words` pattern** (PRNG-ordered English words → many short matches + literals) that is decode-bound. A/B (fast vs. `@[implemented_by]`-disabled tree walk, min-of-5 on the same zlib-deflated `words` stream the dashboard times): **64 KiB 20.5 → 28.3 MiB/s (1.38×)**, **1 MiB 21.5 → 28.1 MiB/s (1.31×)**. Modest, not the 2× a C decoder gets: in pure-Lean the per-byte output construction (`ByteArray.push`, `copyLoop`) and the bounds-checked bit reader dominate, so eliminating the per-bit tree descent only shaves part of the cost. Copy-bound patterns unchanged (within noise). | **Differential conformance**, not a transferred proof: `decodeHuffman` (the canonical spec) is unmodified and `@[implemented_by]` is trusted, so all `inflate_correct` / `decode.goR` proofs hold verbatim. `ZipTest/InflateTable.lean` checks `decodeWithTable (buildTable tree) br = decode tree br` (symbol + consumed `pos`/`bitOff`, or shared error) over trees spanning every code-length regime — short, exactly 9, longer than 9, a mixed 1..15 spine, and the fixed lit/dist trees — from every bit offset, including short inputs that trip the not-enough-bits fallback; plus the full roundtrip + 1000-iter inflate fuzz suite now exercises the fast path end-to-end. 0 sorries. (A formal symbol-level `decodeWithTable_eq` is a tractable follow-up — the `decodeBits`/`TreeHasLeaf` infrastructure in `HuffmanCorrect.lean` supports it.) |

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
