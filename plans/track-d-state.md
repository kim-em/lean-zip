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
   reference that wins on that input.
3. Pick the top unstarted candidate below.
4. Implement via **generational refinement**: new definition `genN+1`, prove
   `genN+1 = genN` (or component equivalence), transfer the roundtrip theorem.
5. Re-bench; update this file (move the item to *Landed*, record the delta) and
   commit the refreshed graphs.

## Measured gaps (snapshot: see `bench/results/latest.json` meta)

- **Compression throughput**: native ≈ 10 MB/s vs zlib/miniz ≈ 500 MB/s and
  libdeflate ≈ 1 GB/s — a ~50–100× gap. This is the headline problem.
- **Compression ratio (text)**: native trails zlib and the zopfli floor.
- ~~**Incompressible input (prng)**: native expands small inputs~~ — **closed by
  D-1** (stored-block fallback); native now matches zlib (≈ 1.005 at 1 KiB).
- **Decompression**: competitive (hundreds of MB/s, same order as zlib).

## Backlog (ranked: impact × tractability)

| ID | Dimension | Candidate | Why / expected effect | Provability |
|----|-----------|-----------|-----------------------|-------------|
| D-2 | runtime | **Profile native `deflateRaw`** to find the dominant cost (allocation, `ByteArray.push` growth, List↔Array conversions, linear LZ77 scan) | Prerequisite for D-3/D-6; turns "10 MB/s" into a named bottleneck. | n/a (measurement). |
| D-3 | runtime | **Hash-chain LZ77 match finder** (genN+1) replacing the linear scan | Likely the dominant compression-speed fix; biggest single runtime win. | Med — prove match-validity equivalence to the linear matcher. |
| D-4 | ratio | **Stronger lazy matching / longer match search** | Close the text-ratio gap toward zlib. | Med — still produces a valid token stream (BB1). |
| D-5 | runtime | **Table-driven multi-bit Huffman decode** (genN+1) vs bit-by-bit | Faster decompression. | Med — equivalence to the bit-by-bit decoder. |
| D-6 | runtime | **Remove hot-path List↔Array/ByteArray conversions** | Constant-factor compression + decompression speedup. | High — local representation-equivalence. |

## Landed

| ID | Change | Measured delta | Proof |
|----|--------|----------------|-------|
| D-1 | **Stored-block fallback** — `deflateRaw` now returns `pickSmaller (deflateStoredPure data) (deflateCompressed data level)` for levels ≥ 1, so the output is never larger than a stored block. | prng ratio at 1 KiB **1.058 → 1.005** (1083 → 1029 B), exact parity with zlib; 4 KiB 1.012 → 1.001; compressible data unchanged (`pickSmaller` keeps the compressed form). Runtime unaffected. | `inflate_deflateRaw` / `deflateRaw_pad` / `deflateRaw_goR_pad` re-proved via the new `deflateCompressed_*` lemmas + `inflate_deflateStoredPure`; 0 sorries. The result is provably never larger than `deflateStoredPure data`, so the change can never regress ratio. |
| D-1b | **Fixed-Huffman fallback at high levels** — `deflateCompressed` at levels ≥ 5 now returns `pickSmaller (deflateFixedIter data) (deflateDynamic data)`, so dynamic Huffman's tree-description overhead never makes the output larger than a plain fixed-Huffman block. | level-6 out shrinks where the tree overhead dominated: 1 KiB `constant` **18 → 10 B** (ratio 0.0176 → 0.0098), 1 KiB `cyclic` **47 → 27 B** (0.0459 → 0.0264), 4 KiB `cyclic` 54 → 49 B. No regressions anywhere — both candidates share the greedy LZ77 matcher, so it is a per-input best-of-{fixed, dynamic}. Runtime unaffected. | `inflate_deflateCompressed` / `deflateCompressed_pad` / `deflateCompressed_goR_pad` each wrap the level ≥ 5 case with `unfold pickSmaller; split`, discharging the fixed branch via the existing level-1 fixed-Huffman proof and the dynamic branch via the existing dynamic proof; 0 sorries. The result is provably never larger than either candidate, so it can never regress ratio. |

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
