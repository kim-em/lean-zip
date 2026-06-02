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
- **Incompressible input (prng)**: native *expands* small inputs to ~1.05×
  while zlib/miniz stay ≈ 1.0 — no stored-block fallback.
- **Decompression**: competitive (hundreds of MB/s, same order as zlib).

## Backlog (ranked: impact × tractability)

| ID | Dimension | Candidate | Why / expected effect | Provability |
|----|-----------|-----------|-----------------------|-------------|
| D-1 | ratio | **Stored-block fallback**: emit a stored block when the compressed output would be larger than the input | Fixes the prng expansion (1.05× → ≈1.0); matches zlib. Small, self-contained. | High — stored block roundtrips to input by existing framing lemmas. |
| D-2 | runtime | **Profile native `deflateRaw`** to find the dominant cost (allocation, `ByteArray.push` growth, List↔Array conversions, linear LZ77 scan) | Prerequisite for D-3/D-6; turns "10 MB/s" into a named bottleneck. | n/a (measurement). |
| D-3 | runtime | **Hash-chain LZ77 match finder** (genN+1) replacing the linear scan | Likely the dominant compression-speed fix; biggest single runtime win. | Med — prove match-validity equivalence to the linear matcher. |
| D-4 | ratio | **Stronger lazy matching / longer match search** | Close the text-ratio gap toward zlib. | Med — still produces a valid token stream (BB1). |
| D-5 | runtime | **Table-driven multi-bit Huffman decode** (genN+1) vs bit-by-bit | Faster decompression. | Med — equivalence to the bit-by-bit decoder. |
| D-6 | runtime | **Remove hot-path List↔Array/ByteArray conversions** | Constant-factor compression + decompression speedup. | High — local representation-equivalence. |

## Landed

_(none yet — this dashboard is the Track D baseline; subsequent rows record
each optimization's measured delta.)_

## Orchestration hook (optional, not yet wired)

To keep the fleet feeding Track D rather than starving it, a future `/plan`
liveness step can: when `gh issue list --label track-d` is empty and the queue
has a deficit, create one `track-d` issue from the top unstarted backlog row
above. Pair it with an Orchestrator-Policy rule mirroring the standing Track E
queue (PLAN.md). Until then, Track D is driven directly from this file.
