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
- **Compression ratio**: ~~native trails zlib and the zopfli floor~~ — after
  D-21 (near-optimal parsing, #2496), native **leads zlib and libdeflate on
  ratio at level 9** (Canterbury geomean 0.2844 vs zlib 0.2966 / libdeflate
  0.2904; Silesia 0.3140 vs 0.3185 / 0.3146). Level 6 still trails zlib by
  ~8% (single-pass greedy/lazy; the optimal parser is a level-9 candidate
  only). Remaining ratio headroom: raise the 16 MiB `optimalMaxSize` gate
  (4 large Silesia files skip the DP), region-aligned block cuts once the
  cut-list emitter lands, zopfli-style cost-model iteration depth.
- **Real corpora (Canterbury, D-17)**: on real data native at L6 is the worst
  real codec on compress/decompress speed (compress 10 MB/s vs zlib 55,
  decompress 92 vs zlib 696, geomean L6) — speed, not ratio, is now the
  headline gap.
- ~~**Incompressible input (prng)**: native expands small inputs~~ — **closed by
  D-1** (stored-block fallback); native now matches zlib (≈ 1.005 at 1 KiB).
- **Decompression**: competitive (hundreds of MB/s, same order as zlib).

## Backlog (ranked: impact × tractability)

| ID | Dimension | Candidate | Why / expected effect | Provability |
|----|-----------|-----------|-----------------------|-------------|
| — | — | *(backlog empty — the performance-pivot waves below are the active queue)* | | |

## Wave-0 phase profile (D-2, closed 2026-06-11)

Per-phase ms, `deflateRaw` (this machine; alice29.txt 152 KB / dickens 10.2 MB;
input perturbed per rep, IO-forced phases). `emit` = single dynamic block incl.
its internal freqs+lens recompute; candidates timed independently.

alice29.txt:
| lvl | match | freqs | emit | base | SC | SharedAt | optimal | full | MB/s | dec MB/s |
|---|---|---|---|---|---|---|---|---|---|---|
| 1 | 4.7 | 2.1 | 5.4 | 10.3 | | | | 10.4 | 14.7 | 106 |
| 6 | 23.4 | 1.8 | 4.7 | 28.2 | | | | 28.0 | 5.4 | 110 |
| 7 | 26.9 | 1.9 | 4.8 | 31.5 | 19.5 | 37.3 | | 88.7 | 1.7 | 114 |
| 9 | 30.4 | 1.9 | 4.8 | 35.2 | 19.8 | 40.8 | 161.0 | 254.4 | 0.6 | 105 |

dickens:
| lvl | match | freqs | emit | base | SC | SharedAt | optimal | full | MB/s | dec MB/s |
|---|---|---|---|---|---|---|---|---|---|---|
| 1 | 390 | 162 | 393 | 755 | | | | 749 | 13.6 | 97 |
| 6 | 1733 | 136 | 344 | 2064 | | | | 2062 | 4.9 | 113 |
| 7 | 2013 | 138 | 347 | 2335 | 1312 | 2696 | | 6329 | 1.6 | 111 |
| 9 | 2156 | 139 | 355 | 2493 | 1314 | 2854 | 10086 | 16591 | 0.6 | 101 |

**Ladder re-sweep verdict (Wave 2e, #2541, post-limiter-fix + post-#2548):**
the `chainDepth`/`insertCap` ladder is already on the speed/ratio frontier at
every level — a ×2-step sweep over Canterbury (12 configs/level, dedup-clean,
deployed single-block path) found no configuration faster than current within
+0.1% geomean ratio; every faster config costs ≥ 0.7% ratio (e.g. L6 at half
depth: 0.60× time, +1.14% ratio). Null result recorded; the levels' speed
budget must come from Wave-3 representation work, not knob tuning.

**Wave-3a verdict (2026-06-12): UInt32 chain-state representation — measured
negative, abandoned.** A UInt32-pure kernel microbenchmark predicted 1.12–1.13×
(and USize 0.78× — rejected outright), but the full matcher with
`Array UInt32` state + UInt32 guards measures *slower* than the deployed
proven-bounds `Array Nat` shape (alice29 matcher ms: L1 6.1 vs 4.87, L4 17.5
vs 16.2, L6 23.7 vs 22.7), and eliminating every hot-loop Nat↔UInt32
conversion moved ≤2% (`UInt32.ofNat` is an inline unbox in this toolchain —
conversions were never the cost). Branch `perf/3a-uint32-chain` preserved
unmerged (full direct-contract proofs + a token-for-token identity test gate,
reusable if the toolchain's codegen changes). Conclusion: knob tuning (#2541)
AND state-representation tuning are now both exhausted — the matcher's
remaining costs are structural (per-token allocation, RC traffic, the
ByteArray byte loop), i.e. Wave 3b (packed token stream) and Wave 5 (fused
phases) are the live levers.

**#2779 verdict (2026-07-07): packed `ByteArray` uint32 chain tables —
measured negative, and this time the *packing* (not the element type) is what
was tested.** Wave-3a (above) tested `Array UInt32` and was correctly dismissed
as still-boxed 8-byte slots. #2779 went further: it backed the merged chain
state with a raw `ByteArray` of genuinely-unboxed little-endian uint32 slots
(4 bytes/slot vs the `Array Nat`'s 8), read/written by
`ByteArray.ugetUInt32LE` / a new `usetUInt32LE`. A bench-only A/B (two matchers
byte-for-byte identical except chain storage, both mirroring
`lz77ChainLazyIterPMerged`, with a token-for-token gate against production
`lzMatchP`) measured **packed 7–19% slower on every corpus member and level**
(AMD EPYC 9455, taskset-pinned; `packed/arr` speedup):

| file (type)        | L6   | L7   | L8   |
|--------------------|------|------|------|
| alice29 152K text  | 0.81 | 0.85 | 0.84 |
| lcet10 427K text   | 0.86 | 0.88 | 0.88 |
| x-ray 8.5M binary  | 0.91 | 0.93 | 0.91 |
| mozilla 51M binary | 0.84 | —    | 0.82 |

`perf stat` (single-side `matcher-arr`/`matcher-packed`, x-ray L8) pins the
mechanism and **confirms the packing hypothesis was right about the cache and
wrong about the bottleneck**: packed does win the axis it targets —
**5× fewer LLC cache-misses** (11.7M → 2.4M; mozilla L8 3.3×, 43.0M → 12.9M)
and fewer L1-dcache misses — but the walk is **instruction-bound, not
memory-bound**, because the merged table (98304 slots = 768 KB as `Array Nat`,
384 KB packed) already fits this machine's **1 MiB private L2**, so there is no
residency to reclaim. Packing instead pays **+26–28% instructions**, and
`perf annotate` pins the mechanism exactly. `Array Nat` stores each slot as a
`lean_object*`, and a small `Nat` (< 2⁶³) is an *immediate* tagged in that word
as `(n<<1)|1` — the runtime's native representation, the same one the matcher's
`Nat` arithmetic already runs on. So the arr chain read is one inlined load
(`mov 0x18(%rax,%r15,8),%rbx`) yielding a ready-to-use tagged `Nat`, zero
conversions. The packed read emits `call lean_zip_uget_u32le` (the Lean compiler
compiles an `@[extern]` to a call; lake's default non-LTO C build leaves it in
the binary — a real 3.67%-of-total symbol, invisible in arr; it is *not*
fundamentally non-inlinable — `-flto` folds it, see below) and then must *tag*
the raw uint32 into a `Nat` (`mov %eax,%eax; lea 0x1(,%rax,2),%r14`); every write
untags the reverse way.
Counting tag ops (`lea …,2` / `test $0x1`) in the two loop bodies: arr 36 vs
packed 63. So the packed slot holds a *foreign* representation and each access
crosses the FFI boundary plus a `Nat`↔uint32 conversion — that, not the wide
store (which the C folds to a single `mov %edx,0x18(%rdi,%rsi,1)`) nor the size
guard (**equal branch-misses**, 42.3M vs 43.3M, perfectly predicted — *not* the
confound), is where the instructions go. The lesson: `Array Nat` is not a
wasteful 8-byte layout to be shrunk, it is the *only* chain-table layout with
conversion-free, inlinable access; any denser physical layout (element type,
Wave-3a; packing, #2779) trades that for a smaller footprint, a win only where
the footprint actually misses cache. This settles the *packing* question for
this hardware/toolchain — the cache win packing delivers only pays where the
table overflows L2, i.e. the issue's assumed **256 KiB-L2** machine, which the
bench EPYC is not. The call *is* removable: an `-flto` relink (both objects at
lake's exact `-O3 -DNDEBUG` flags) inlines the extern into `chainWalkBA` (call
count 2→0, verified; arr instructions/cycles/throughput unchanged, so the build
is clean) — but it only cuts ~6% of packed's instructions (mozilla L8 526.3B →
495.3B) and moves packed/arr from 0.855× to 0.894× (x-ray 0.93×→0.958×): still
4–11% slower, because LTO removes the *call* but not the `Nat`↔uint32 *tag*
conversion, and adds zero cache benefit. (The inlining LTO recovers here lands
natively once core lean#14053 ships `uget*` as primitives — tracked separately
as an independent production win in #2806, where the same wide-load externs sit
non-inlined in the far hotter `countMatch`.) A revival would therefore need
*both* the whole ring-index/`cand` arithmetic moved to `USize` (production
`chainWalkPackedU` moved only the accumulators, keeping `cand : Nat` — so the tag
tax stays) *and* the inlinable wide read (LTO today, or lean#14053's `ugetUInt32`
primitive), so the packed read becomes a bare load with no call and no tag —
and even then it only pays where the table overflows L2. Branch
`perf/2779-packed-chain-spike` (commit `b895430c`) preserved unmerged: the full
harness (`Bench.PackedChain`, the `matcher-ab` / `matcher-arr` / `matcher-packed`
bench ops, and `usetUInt32LE` + its C) is reusable to re-measure on a small-L2
chip or an oversized-table stress test. Reproduce:
`lake -d bench exe bench matcher-ab 0 @bench/corpora/silesia/x-ray 8` and
`perf stat -e instructions,cache-misses -- .lake/build/bin/bench matcher-packed 0 @bench/corpora/silesia/x-ray 8`.
Conclusion: chain-state *representation* tuning (element type, Wave-3a; packing,
#2779) is now exhausted on this hardware — the matcher's remaining costs stay
structural (instruction count, per-token allocation, RC traffic).

**#2795 verdict (2026-07-08): batched literal emission via `pushUInt64LE` —
measured negative; the per-literal push call is not on the decode critical
path.** This was the deciding probe set up by #2795's framing after
#2793/#2808 (−5% instructions moved wall-clock only 1–2%, so the decode is
latency-bound on the loop-carried bitBuf→mask→table-load→shift recurrence):
batch up to eight consecutive literals into a `UInt64` accumulator + `USize`
count threaded through the production tree-free loop (`goTreeFreeUB`,
replacing `goTreeFreeU`'s inline-literal `output.push`), flushing as **one**
proven-reference `ByteArray.pushUInt64LE` call on batch-full and before any
branch that observes `output` — removing the out-of-line
`lean_byte_array_push` call (exclusivity + capacity + store + size bump) from
the per-literal path. Same-worktree A/B per bench/README (`inflate-profile
decode`, level-6 libdeflate payloads, `sizeHint` set, medians of 5 interleaved
rounds — 8 for the shared baseline — AMD EPYC 9455; baseline = `41b1b857`, the
merged #2808), in **two** variants: the landable exact-guard form (the
output-limit guard reads the conceptual size `output.size + litCnt`) and a
measurement-only **ceiling** form that keeps the baseline's cheap
`output.size ≥ maxOut` guard (fires up to 7 bytes late; isolates the pure
effect of removing the call from the guard arithmetic). Both regress on both
axes (Δ vs baseline, exact / ceiling):

| file | Δ instructions | Δ cycles |
|---|---|---|
| x-ray (8.5M gray image) | +6.2% / +3.9% | +4.6% / +2.2% |
| ooffice (6.2M binary) | +5.5% / +3.1% | +5.4% / +3.4% |
| sao (7.3M star catalog) | +6.6% / +1.0% | +5.1% / +2.4% |
| alice29 (152K text) | +6.0% / +5.0% | +4.7% / +2.3% |
| plrabn12 (482K text) | +6.2% / +5.3% | +4.4% / +2.2% |

(Instruction counts are deterministic to ~0.01%; cycles are noisier, but the
best-of-rounds cycle comparison is also positive on every file for both
variants — exact +3.4–5.1%, ceiling +1.8–3.3% — so the regression is not a
median artifact.) **Stated plainly, per the probe's decision rule: cycles do
not drop more than instructions — median cycles do not drop at all, on any
file, in either variant; both axes rise together.** Mechanism: `lean_byte_array_push`'s exclusive fast path is only
~6–8 instructions *including* call overhead (1.96% whole-program self time on
x-ray — the issue's "~4%" evidence predates #2804/#2805/#2808 shifting the
mix), and its latency is fully hidden in the recurrence's shadow, so there was
no serialization to reclaim. The batch bookkeeping — per-literal accumulator
OR + two shifts, count increment + batch-full compare, one `pushUInt64LE` call
per eight literals **plus one per slow-path entry even with an empty batch
(i.e. per match)**, and in the exact form the boxed-Nat conceptual-size guard
(`lean_usize_to_nat` + `lean_nat_add` + `lean_nat_dec_le` per literal) — costs
more than the call it removes: the ceiling A/B on x-ray (+58.5M
instructions/rep over ~8M literals) nets ~+7 instructions per literal.
A leaner batcher was considered rather than measured — carry the shift (or a
write pointer) instead of the count, skip empty flushes before matches,
precompute the remaining output room per batch instead of per-literal Nat
arithmetic — but those shavings target known spike overhead the ceiling
variant already largely excludes, and the ceiling still regresses median
cycles on every file: there is no evidence that simple literal batching is a
lever here, and a substantially different output-write design should be
measured as its own probe rather than as a third variant of this one.
Consequence for the output-write story: per-literal *store-call*
removal is not a lever — the batched-store motivation for the heavier
structural rewrites (#2798/#2799) is dead, and any case for the
fastloop/slowloop split or the write-once `uset` cursor must rest on what
those *additionally* remove (the per-literal size-bump/guard bookkeeping, the
bounds discipline) and needs its own probe before committing. Branch
`perf/2795-batched-literal-spike` preserved unmerged: commit `604cc1a9` is the
exact-guard spike (equivalence theorem `goTreeFreeUB_eq` stated and `sorry`'d,
benchmark-first), commit `45b355c6` the ceiling probe; reproduce by building
`inflate-profile` at each commit per bench/README § *Profiling the decoder*.
Incidental discovery while attributing the loss (filed as #2811): the
`copy_within_ffi.o` lakefile target is compiled without `-O2 -DNDEBUG` —
unlike its `extend_within`/`bytearray_wide` siblings — so the match-copy
primitive runs un-inlined `lean.h` helpers *with asserts enabled*; on x-ray
decode that un-optimized TU (`lean_to_sarray` 9.1%, `lean_is_sarray` 6.4%,
`lean_zip_byte_array_copy_within` 7.5%, plus helpers) is roughly a third of
whole-program self time, inflating the denominator of every recent decode
percentage. Fixing it is a likely across-the-board decode win and re-baselines
future A/Bs. It does not change this verdict's sign — the added batching cost
is absolute, per-literal, and inside the loop TU, which is compiled optimized —
and #2795 needs no re-run after #2811 lands unless a post-#2811 profile shows
`lean_byte_array_push` becoming a materially larger self-time share of the
rebalanced decode.

**#2799 verdict (2026-07-08): fastloop / write-once cursor decode — measured
real but modest (~half the pre-registration), and the expensive branch-free
variant barely beats the cheap one.** The follow-up probe to #2795 (which killed
the *store-call*-removal motivation and demanded #2799 rest on what it
*additionally* removes: the per-literal size-bump/guard bookkeeping and bounds
discipline). Two spikes in a quarantined `Zip/Native/InflateFast.lean` (NOT on
any production path; `Inflate.inflate` unchanged), exact-size path only
(`sizeHint` = true decompressed length, pre-extended once via
`ByteArray.presize`; back-references written in place at the cursor via a new
`ByteArray.copyWithinAt` FFI primitive):

- **`goCur` (set! cursor):** `goTreeFreeU` with `output.push` → `set!` at an
  `outPos` cursor; input side byte-identical, isolating the output-write cost.
- **`goCurU` (uset fastloop — the actual #2799 shape):** a per-symbol margin
  guard `outPos + 299 ≤ output.size` gating a branch-free body with proven-bounds
  `uset` literals (real omega proof from the margin, **no `sorry`**) and no
  per-literal max-size check; the <299-byte tail delegates to `goCur`.

Same-**binary** A/B (three modes `decode`/`decode-fast`/`decode-fast-u` in one
`inflate-profile` — strictly more layout-comparable than the two-worktree rule),
Python-zlib level-6 raw-DEFLATE payloads (libdeflate FFI unavailable this env),
`perf stat` cycles (3 trials) + best-of-5 wall-clock cross-check, this machine:

| file | mix | Δ cyc set! | Δ cyc uset | Δ wall uset |
|---|---|---|---|---|
| dickens (10.2M text) | literal-heavy | −4.2% | **−6.0%** | −6.4% |
| x-ray (8.5M image) | literal-heavy | −3.3% | −3.6% | −3.5% |
| nci (33.6M chem) | match-heavy | −0.5% | −0.9% | −2.7% |
| **geomean** | | **−2.7%** | **−3.5%** | −4.2% |

**Instructions did NOT drop** — flat-to-slightly-up and layout-sensitive across
builds (the untouched `decode` baseline was bit-identical across rebuilds while
`goCur` in the edited module shifted ±4%), so the win is **microarchitectural**
(no realloc/regrow churn on the growing push buffer, no RC on its header), not an
instruction-count reduction: the cursor index arithmetic replaces `push`'s
internal bookkeeping ~1:1. **Stated per the probe's decision rule:** the
architecture is real and correct (byte-identical output on all corpora + block
types + RLE, guarded by `ZipTest/InflateFast.lean`), the shape matches the
estimate (literal-heavy > match-heavy), but the magnitude is ~half to two-thirds
of #2799's pre-registered 7–10% geomean. **Two decision-relevant facts:** (1) the
branch-free `uset` + 299-margin machinery — the heaviest proof surface in the
repo (write-once cursor equivalence through the exact-size buffer + the margin
invariant) — separates from the far-simpler `set!` cursor by only ~0.8% cycles,
**inside the ±4% layout/codegen sensitivity** the instruction counts showed, so
`uset` is **not proven materially better** than `set!`; (2) the `set!` cursor
alone captures ~two-thirds of the win at a fraction of the proof cost.
**Consequence:** do not pay for the full `uset`+margin equivalence proof on this
evidence; if #2799 is pursued, the `set!` cursor is the better win/proof ratio
and the branch-free refinement is not justified by a delta within noise. **Caveat
(blocks revival):** streams are Python-zlib level-6 (libdeflate FFI unavailable
this env), and #2799's pre-registration is on libdeflate's denser, fewer-literal
streams where the literal-write component is likely smaller — the magnitude is
not established; **a libdeflate-stream rerun is required before any
production/proof revival.** The reproducible probe (both spikes, FFI primitives,
conformance test, `decode-fast{,-u}` modes) is landed by this PR, quarantined
(not re-exported by `Zip`); `Inflate.inflate` is untouched and #2799's full
production-integration scope stays open.

**W5.P1 comparative component profile (2026-06-12, perf, alice29, per-compressor
windows, normalized to compressor-attributable samples; nix/Lean startup noise
excluded; miniz attribution degraded — inline monolith):**

| compressor | matcher | runtime/mem | code-lookup | emit | tree | dp/freqs |
|---|---|---|---|---|---|---|
| native L1 | 24.9 | **32.2** | **13.8** | 5.0 | 4.4 | 1.6 |
| native L6 | 58.3 | 20.3 | 5.1 | — | 1.2 | — |
| native L9 | 44.9 | 21.6 | 3.9 | — | 2.4 | 11.3 |
| zlib L1 | 48.5 | 14.9¹ | — | 14.4 | 1.5 | — |
| zlib L6 | 74.3 | 10.1¹ | — | 4.0 | 0.7 | — |
| libdeflate L6 | (in emit²) | 13.8¹ | — | 63.8 | 2.8 | — |

¹ includes the Lean harness's own RC around the FFI call. ² libdeflate's
matcher is fast enough that vectorized bit-packing dominates its profile.

**What it flags (re-ranking Wave 5):**
1. **Allocation/RC is native's #1 fast-end anomaly** (32% at L1 vs zlib's
   ≤15% incl. harness). Prime suspect found by reading the hot helpers: the
   #2548/#2551 `Guarded` helpers return boxed tuples per position
   (`headInsertGuarded : Nat × Array × Array`, `chainWalk* : Nat × Nat`) —
   a heap pair every byte. New profile-backed iso-ratio lead (and a likely
   explanation for why the 3a UInt32 change couldn't show: alloc dominated).
2. **`findTableCode` linear search confirmed at 13.8% of L1** (5.1% L6,
   3.9% L9) — W5.0's dense tables promoted from suspect to certainty.
3. **T2 feasibility check passes**: matcher-only throughput at L1 =
   15.2 / 0.249 ≈ **61 MB/s** — the ~39 MB/s fast-tier target is reachable
   purely by shedding overhead (73% of L1 is non-matcher), before any
   matcher knob trades.
4. zlib's own matcher is ~6× faster per matcher-second (L6: 53/0.743 ≈ 71
   vs native 6.9/0.583 ≈ 12 MB/s-equivalent) — the per-byte C-vs-Lean gap
   is real and not closable by overhead work; the fast tier's win comes
   from the other 73%, not from beating C at matching.

**Named bottlenecks (in priority order):**
1. **Matcher is 83–84% of the base path at L6** (and the lazy step at L4 costs
   ~2× over L3) — hash-chain maintenance + search; the Wave-3 matcher-state
   representation target.
2. **The L≥7 dispatch redundancy is exactly the cliff**: L7 = base + SC +
   SharedAt run end-to-end, each redoing the full matcher (SharedAt = matcher
   + ~0.7 s cut-arbitration/emit on dickens). One shared token pass + SC
   demoted to L9 ⇒ L7 ≈ matcher + two emit tails ≈ 2.1× immediately; the
   remaining gap to ~5 MB/s needs the freqs/sizing dedup inside the
   candidates (each candidate re-runs `tokenFreqs` over the same stream).
3. **At L1–3 the emit side is ~half the time** (dickens L1: matcher 52%,
   freqs 21%, emit ~27%) — `tokenFreqs` + `emitTokensWithCodes` are the
   fflate-goal lever, not just the matcher.
4. **Optimal DP = 61% of L9** (10.1 s/10 MB ≈ 1 MB/s parser throughput) —
   acceptable for the max tier; cache-build chain walk dominates within it.
5. **Decode is already 97–118 MB/s** on these files — the OCaml goal (≥120)
   needs only ~1.1–1.25×: targeted tail fixes, not a wave.


## Landed

| ID | Change | Measured delta | Proof |
|----|--------|----------------|-------|
| D-25 | **#2490 — pre-sized packed-token array (sub-win 3.2), and the UInt32-table half (3.1) retired against the existing measured-negative verdict.** Seeded the token accumulator of the production matchers `lz77ChainIterP`/`lz77ChainLazyIterP` with `Array.emptyWithCapacity data.size` instead of `#[]`, removing the geometric regrowth/copy of the token array (token count is always ≤ `data.size`, the exact capacity bound). **Sub-win 3.1 (UInt32 position/validity tables) NOT pursued — it is the same change as the Wave-3a "UInt32 chain-state representation" already measured slower in situ** (this table, D-22 row / lines 89–102: alice29 matcher L1 6.1 vs 4.87, L6 23.7 vs 22.7 ms; full proofs + token-identity gate preserved unmerged on `perf/3a-uint32-chain`). #2490's 3.1 description predates that verdict and also references the older `Array Bool` validity shape, which the production `lz77ChainIterP` (sentinel-`data.size` `Array Nat`) already moved past — no actionable work remains. | **Byte-identical (zero ratio drift): a before/after `bench-report` over Canterbury shows `out_size` identical on every one of the 99 native rows.** Throughput delta is within this machine's run-to-run noise (median +0.1%, mean +0.16% across native rows; rows swing −7%…+8% from machine noise, dwarfing the predicted ~1.4% token-build win) — the change is a pure allocation reduction that cannot regress, so the committed median-of-5 dashboard (D-23, unchanged ratios) was left as-is rather than overwritten with a sub-noise single-run regen. | **0 sorries.** `emptyWithCapacity n = #[]` by `rfl` (`Array.emptyWithCapacity_eq`, a `@[simp]` lemma), so the packed→boxed equivalence proofs (`lz77ChainIterP_eq`/`lz77ChainLazyIterP_eq` in `Zip/Spec/LZ77PackedCorrect.lean`) carry through with that one lemma added to the seed-reduction `simpa only` set; every theorem statement unchanged. `lake build` + `lake exe test` green. |
| D-24 | **Wave 6 — closing the iso-ratio emit frontier (a verdict wave).** Probed the BitWriter/emit path, the last untested iso-ratio lever. **W6.0 output preallocation: measured nil** (probe L1 23.1 vs master 23.4 MB/s) — `ByteArray.push` is already FBIP-in-place when uniquely owned and `flushAcc` threads the buffer linearly, so there is no realloc to remove (Codex predicted this). **Symbol-level perf put the entire BitWriter family at 5.0% of L1** (`flushAcc` 1.38%, `writeHuffCode`/`writeBits` 0.57% each), below the wave's own 10% stop-gate. **W6.1 per-token write fusion** (`writeFour` packing a reference token's 4 writes into one UInt64 + single drain, `bitCount<8` preserved; Route-A value-equality via a `flushAcc_or` composition lemma) was attempted at Kim's request for the ~1%: the design is sound and it built for everything except one residual `flushAcc_or` elaboration goal; **abandoned as not worth further build-loop debugging for a sub-1% noise-level win**, preserved on `perf/w61-writeref-fusion`. **Decode (W6.3):** #2500 closed obsolete (decode hot path already optimized by the merged #2502/#2505/#2507); #2501 (input-side wide bit reader) in pod. **Infrastructure:** root-caused the campaign-long `pod once` launch mortality to a macOS `stat -f %m` in `~/.claude/swap-account`'s lock-staleness check that wedged credential refresh on Linux — fixed cross-platform, restoring autonomous pod. | **No compress change landed (both emit slices nil/abandoned); ratios and the D-23 dashboard stand unchanged.** The verdict is the deliverable: **the iso-ratio frontier is exhausted.** Campaign arc (Waves 5–6): native L1 14.6 → 23.4 MB/s (+60%) at fixed ratio, OCaml L7–L9 dominated outright, L7 within 1.07×. The remaining gap is OCaml's *fast half* (L1–L5, ratios 0.34–0.40 where native's 0.3229 already wins on quality but needs 1.3–1.8× on speed). | **0 sorries on master; the abandoned W6.1 carries no sorry either** (it fails to build, not to a `sorry`). The limiter-completeness proof chain (#2536) advanced in parallel via pod: #2566 (per-step blKraft) + #2579 (`repairBl_complete`) merged, #2565/#2544 in flight. |
| W7 | **Strategic outlook (not yet started) — the fused single-pass compressor.** The iso-ratio toolbox is empty, but the fast half is **not disproven**: the W5.P1 profile showed the *matcher alone* runs ~60 MB/s (well above OCaml's 39), so the headroom exists — it is locked behind the per-token freqs+tree+emit assembly, where pure Lean + RC pays a structural tax C avoids with mutable buffers. **Wave 7 = the fused compressor** (histogram accumulated during matching; one tree per block; emit inline) — now far cheaper because the packed-token infrastructure (Wave 3b) and dense code tables (W5.0) already exist. Honest projection: **L4–L6 OCaml domination is plausible; L1–L3 is the true frontier** where the C-vs-Lean per-byte matcher gap bites. The W5.1 slice rejected the *quickest* one-pass design (fixed-only costs ~30% ratio; per-block dynamic barely beat production), so Wave 7 must be the *full* fused dynamic compressor, its own design pass with a second opinion. | *(planning)* | *(none yet)* |
| D-23 | **Wave 5 — the architecture-probe campaign** (plan of 2026-06-12, two Codex rounds). Free-win surgery: shared-split sized-tree reuse (#2559, closes #2552); the headline **dense length/distance code tables** memoizing `findLengthCode`/`findDistCode` over their full domains, routed through `findLengthCodeFast`/`findDistCodeFast` in the packed freq + emit passes by equality transfer (#2561); **per-position de-boxing** — `chainWalkPacked` returns `bestPos*512+bestLen` as one small Nat (compiled body: 0 `lean_alloc_ctor`), head insert split into `headProbeGuarded`+2×`guardedSet` (#2562). Profiling deliverable: the **W5.P1 comparative `perf` attention table** (native vs zlib/miniz/libdeflate per-compressor windows; flagged alloc/RC=32% and `findTableCode`=13.8% of L1 — both then banked). Recorded negative: the **W5.1 fused fast-tier F-vs-D gate FAILED** — variant F (fixed-only) costs ~30% ratio on text (0.51–0.58, refuting the 2–4% folk number — Codex called this in round 1), variant D (per-block dynamic) reaches only ~24–28 MB/s @ 0.40–0.45, barely above production L1; neither clears the 39 MB/s @ ≤0.38 target, so W5.1/W5.2/W5.3 were stopped and the slice preserved unmerged on `perf/w51-fast-tier-slice` (its fused matcher skeleton, match-only 40–63 MB/s, is reusable). | **The biggest single-wave compress gain of the project, at ratios unchanged to 4 decimals** (Canterbury geomean MB/s, committed dashboard → new): **L1 15.2→21.9 (+44%), L2 14.0→19.1 (+37%), L3 12.7→16.7 (+31%)**, L4–L6 +16–21%, L7–L8 +18–20%, L9 +4%; every ratio identical (L1 0.3229, L6 0.3020, L9 0.2844). **Dominance shift**: native now **outright dominates OCaml's L8 and L9** points (19.1 MB/s @ 0.3177 beats OCaml's 15.3/12.4 @ 0.319), and OCaml L7 is within 1.07×. The remaining gaps are OCaml's *fast half* (L1–L5, ratios 0.325–0.40 where native needs 1.3–1.8×) — and the W5.1 slice proved a one-pass fast tier cannot close them without unacceptable ratio loss; emit-share is now the binding constraint everywhere (37–46% in the fused slice), so the **next campaign is the emit/BitWriter micro-path**, scoped by these numbers. | **0 sorries; all merged work byte-identical** (dense-table `getElem_map`/`getElem_range` rewrites; de-box packed-Nat decode `%512`/`/512` with `min258_le_511`; the `Guarded`/`_eq` proof-bridge pattern throughout; every exported statement unchanged). The W5.1 slice carries **no proofs by design** (measurement-first doctrine — proofs deferred until a variant cleared its gate; it did not). |
| D-22 | **Wave 3 — the iso-ratio matcher/token campaign, full ledger** (plan of 2026-06-12). Banked: guarded proven-bounds head-inserts in all four mainLoops (#2551) and the L9 DP cache builder (#2553, closing #2547); packed token pipeline end-to-end on the single-block paths (#2555 producer + view equivalence, #2556 packed-native `tokenFreqsP` + dispatch plumbing, #2557 packed-native emission with the bit-level theory transferred by lockstep equality — `DeflateRoundtrip` untouched). Recorded negatives, in full: `chainDepth`/`insertCap` ladder re-sweep null (#2541/#2550); **UInt32 chain-state representation measured slower in situ** despite a 1.12× kernel prediction (conversions exonerated — `UInt32.ofNat` is an inline unbox; experiment preserved unmerged on `perf/3a-uint32-chain`); token packing worth only ~1–2% (boxing/traversal was never the cost; stage D not pursued). Plus two WF-elaboration landmines documented in-tree (fun_induction OOM/silent-sorry over heuristic defs; findLengthCode-over-stuck-words in match scrutinees). | **Compress +4–7% across the ladder at exactly unchanged ratios** (Canterbury geomean MB/s, old → new dashboard: L1 14.2→15.2, L3 12.0→12.7, L6 6.4→6.9, L8 3.1→3.2; ratio L6 0.3020 and L9 0.2844 to 4 decimals — the byte-identity discipline held). Strategic read: the iso-ratio toolbox for the current architecture is now **measured-empty** — remaining gaps to the Pareto goals (L6 6.9 vs OCaml 22.8; L1 15.2 vs OCaml 39 / fflate 77) require Wave-5 architecture (fused histogram, block pipelining, static-tree L1 tier under the approved low-level ratio-trade policy) and/or the emit micro-path; queued: #2552 (sized-tree reuse, ~5–8% at L7–8), #2500/#2501 (decode tail, needs only ~1.25×). | **0 sorries throughout; every PR byte-identical by construction or proven equality** (pack-direction lockstep + `Array.map_map` view transfer; opaque-helper pattern for packed-word matches; all existing theorem statements unchanged across the entire wave). |
| D-21 | **Near-optimal LZ parsing — cost-model DP closes the libdeflate ratio gap at level 9** (#2496). Replaced local match selection with libdeflate-style two-pass parsing in `Zip/Native/DeflateParse.lean`: (1) a per-position **candidate cache** (chain walk at *every* position, strictly-increasing-length nearest-first frontier, fixed-stride flat arrays, `niceLen` truncates depth but never skips positions); (2) dense **bit-cost tables** (static fixed-Huffman seed round, then refit to the region's own parse; zero-frequency symbols cost 15 bits, never 0); (3) a **backward DP** per 256 KiB region — `cost[i] = min(lit, matchCost + cost[i+len])` over the cached candidates, evaluated at full length *and* at length-code boundaries inside each candidate's interval — with the 259-entry cost tail seeded by a baseline bits/byte estimate so the region end is **not** a parse barrier (matches cross it; the emitter just skips the next region's prefix); (4) a forward emitter that **re-verifies every choice** (`countMatch` + the `lz77Chain` guards, literal fallback). Wired as a fourth `pickSmaller` candidate at level 9 (`deflateDynamicBlocksOptimal`, shared-window split over the optimal stream), gated at `optimalMaxSize` = 16 MiB until peak memory is measured (~16 B/byte transient). `tokenFreqs`/`dynamicCodeLengths` moved to `Zip/Native/DeflateFreqs.lean` so the parser sits below the emitters. | **Native now leads zlib AND libdeflate on ratio at L9** (this machine, geomean, baseline = master *with* D-entropy splitting #2532): Canterbury **0.2983 → 0.2844 (−4.7%)** vs zlib 0.2966, libdeflate 0.2904 — every file improves (kennedy.xls −10.7%, plrabn12 −5.3%, asyoulik −4.6%, lcet10 −4.6%); Silesia **0.3218 → 0.3140 (−2.4%)** vs zlib 0.3185, libdeflate 0.3146 (reymont −6.7%, xml −6.4%, dickens −4.8%; the 16 MiB gate initially excluded mozilla/nci/samba/webster — raised to 64 MiB in #2537 after RSS measurement, which brought nci −10.5% [0.0855, beating zlib 0.0891 *and* libdeflate 0.0872 — the former worst outlier], webster −5.0%, samba −4.5%, mozilla −1.7%, and the Silesia geomean to **0.3081**). Cost: L9 compress **~2.3× slower** (0.61 vs 1.38 MB/s geomean — libdeflate-shaped, nowhere near zopfli's 50–100×); **L6 byte-identical and speed-flat**. Ratio canary in `ZipTest.OptimalParse` pins the win (alice29 single-block 52049 vs lazy-9 54744; full `deflateRaw` L9 52111 vs L8 54492). | **0 sorries, no new axioms. Validity is proven; optimality is *measured, not proven* — by design.** The DP (cache, cost tables, choice arrays) never enters any proof: `optimalEmit` re-establishes validity per match (fresh `countMatch` = stored length + explicit guards), so `Zip/Spec/LZ77OptimalCorrect.lean` states `ValidDecomp` + encodability for **arbitrary** choice arrays (template: `lz77Chain_mainLoop_valid`), plus iter/list equivalence and the resolves/empty lemmas. Spec wiring is the `deflateDynamicBlocksShared` quadruple verbatim (`decode_`/`inflate_`/`_goR_pad`/`_pad` over the generic `emitSharedBlocks_decode`/`_decodeR` fold) and one extra `pickSmaller` layer in each of the three `deflateRaw` dispatch proofs. The cost model is a heuristic estimate (per-region histogram vs per-4096-token emission trees, baseline tail, truncation only at code boundaries) — compression quality is enforced by the test-suite ratio canary, not a theorem. |
| D-20 | **Fix the broken dynamic-Huffman length-limiter — recover ~40% on large text.** Instrumentation (D-19's real-corpus verdict) traced the large-text ratio gap to a latent bug, not a missing feature: `computeCodeLengths`' length-limiter capped each natural code length at 15 bits and, if that broke the Kraft inequality by *even one bit* (depth-16 tree → overflow), flattened **every** symbol to a uniform 15-bit code — worse than fixed Huffman, so `deflateRaw` silently shipped a *fixed* block on every large file. (plrabn12: natural depth 16, all 105 used symbols forced to 15 bits, 28 bits/token — provably non-optimal, since a correct length-limited code can never beat fixed and then lose to it.) Replaced the flat fallback with the standard zlib `gen_bitlen` redistribution (`cappedBlCount`/`repairBl`/`expandBl`/`limitedPairs`): cap, repair the small Kraft overflow through the `bl_count` histogram, assign lengths to symbols by decreasing frequency. | **Actual `deflateRaw` L6 output, roundtrip-verified:** `plrabn12.txt` **52.5% → 41.5%** (−40% of the block), `lcet10.txt` **42.2% → 34.7%**, both now within ~2.5% of zlib (was +30% / +24%). Small files unchanged (the bug never fired there: alice29 36.6%). Binary files whose tree already fit ≤15 bits (`kennedy.xls`) are unaffected — their residual gap is a separate, parse/block-structure cause. The single proper dynamic block already reaches near-zlib, so block-splitting and lazy-matching are now minor follow-ups. | **0 sorries, no new axioms.** The repair is a *heuristic* wrapped by the existing proven `fixKraftList` safety net, so `computeCodeLengths_valid` (the Kraft half) transfers **unchanged** — the spec demanded validity, never optimality. The only new obligations are structural: every `limitedPairs` length ∈ `[1, maxBits]` and every nonzero symbol receives a pair, both immediate from the `zip`-with-padded-`expandBl` shape (`limitedPairs_mem_range` / `_map_fst` / `_covers`). `computeCodeLengths_bounded`/`_valid`/`_nonzero` re-proven; all downstream dynamic-block + roundtrip proofs transfer; `lake exe test` (roundtrip + 1000-iter fuzz) green. |
| D-19 | **Silesia corpus added** (#2516, directive). The modern publishable standard (12 files, ~202 MB: prose, UNIX binaries, an HTML dictionary, a source tarball, XML, databases, medical images, a DLL) joins Canterbury on the dashboard, fetched on demand into a gitignored cache (`fetch_corpora.sh silesia`, pinned GitHub mirror, SHA-256-verified — not committed). `ZipBenchReport` runs a **per-corpus matrix**: Silesia uses a reduced grid (levels [1,6,9], single timing pass, zopfli skipped) since it is ~70× larger than Canterbury, while Canterbury keeps the full 9-level / median-of-5 grid; `run_external.py` matches the reduced levels for Silesia payloads. `plot.py` needed no change (already corpus-generic). Three prior one-shot agents skipped this as infeasible at full matrix; landed manually with the reduced matrix. | **Silesia confirms and sharpens the real-data verdict — native is the worst codec on every axis, and the ratio gap *grows* on large files.** L6 compression vs zlib: native gives up **+19 to +28% ratio** on large text/data (`dickens` +28%, `nci` +27%, `webster` +23%, `x-ray` +19%; binaries milder: `samba` +9%, `mozilla` +6%). Compress speed native 7–10 MB/s vs zlib ~21–27 (≈3×), libdeflate 75–105 (≈10×). Decode native ~100 MB/s vs zlib ~365 (≈3.6×), libdeflate ~800 (≈8×). The growing ratio deficit points squarely at the greedy hash-chain matcher (no lazy matching; window/chain limits) as the highest-value target — it would lift ratio *and* the headline. | **Bench harness only — 0 library/proof changes, 0 sorries.** `lake build bench-report` green; Silesia corpus bytes + dumped payloads gitignored (only charts + `latest.json` committed). |
| D-18 | **Remove all synthetic patterns — real corpora only** (#2518, directive). D-17's real-Canterbury read showed the synthetic patterns misled on every axis (the pseudo-prose pattern was 200:1 compressible and decoded ~3800 MB/s vs ~106 MB/s on real prose in the *same* run), so per the directive they are gone entirely. `ZipBenchReport.lean` drops `mkConstant/Cyclic/Prng/Text/Words`, `generateData`, `patterns`/`sizes`, `runCompressor`, and the orphaned `runRatioLevels`/`levelSize`; the timing matrix and `--dump-payloads` now run **only** over the committed corpora, discovered generically by directory (`loadCorpora` reads each `bench/corpora/<corpus>/` subdir — nothing hard-codes Canterbury, so Silesia slots in automatically). `bench/plot.py` drops `size_sweep`/`ratio_by_level`/`PATTERNS` and the synthetic figures; the per-level throughput/decompress/**ratio** charts are rebuilt on real corpora as `<corpus>_<metric>_L<n>.svg` (grouped bars, x = files, one bar per compressor), plus the stable level-6 bars and a new aggregate `_vs_level.svg` line chart (geomean over files) — all keyed off the `<corpus>/` prefixes present in the data. Stale synthetic SVGs deleted from `bench/graphs/`; `run.sh`/`README.md` updated. | **No data change — synthetic rows removed, real-corpus numbers unchanged** (same machine/commit base; the Canterbury figures are the D-17 headline: native L6 geomean ratio 0.323 vs zlib 0.299, compress 10 MB/s vs 55, decompress 92 vs 696 — worst real codec on all three axes, ratio gap largest on big prose `plrabn12` +30% / `lcet10` +24%). `latest.json` now contains zero `constant`/`cyclic`/`prng`/`text`/`words` rows; the graph set is real-corpus only. | **Bench harness only — 0 library/proof changes, 0 sorries.** `grep -nE 'constant\|cyclic\|prng\|"text"\|"words"\|generateData' ZipBenchReport.lean bench/plot.py` is clean; `lake build bench-report` green. |
| D-17 | **Real-corpus harness + Canterbury corpus** (#2515). The dashboard ran only on synthetic patterns (PLAN.md §D: not representative — the pseudo-text pattern is pathologically compressible, and native hit byte-for-byte reference parity on it). Added `bench/fetch_corpora.sh` (materializes the standard `cantrbry.tar.gz`, 11 files / ~2.8 MB, verified file-by-file against recorded SHA-256) and **committed** the corpus under `bench/corpora/canterbury/` (CI needs no network; larger corpora stay gitignored). `ZipBenchReport.lean` factors the timing grid into a workload-list core (`runWorkloads`) and runs it over the corpus files (pattern `canterbury/<file>`, one single-size workload each) for native + all FFI references + zopfli; `--dump-payloads` writes the corpus bytes under `payloads/canterbury/` so `run_external.py` (now corpus-aware via `discover_payloads`) feeds the Go/JS/Zig/OCaml comparators byte-identical input. `plot.py` adds per-file grouped-bar charts (`canterbury_{compress,decompress}_throughput.svg`, `canterbury_ratio.svg`); synthetic views unchanged. | **First read on real data (this machine, level 6, geomean over 11 files) — the synthetic "ratio parity" does NOT hold:** native ratio **0.323** vs zlib/miniz/go/zig **0.299**, libdeflate 0.296, zopfli floor 0.279 — native is the worst real codec on ratio (ties OCaml 0.321). The gap is small on short/structured files (alice29 0.366 vs 0.358) but **large on big prose**: `lcet10.txt` 0.422 vs 0.340 (+24%), `plrabn12.txt` **0.525 vs 0.405 (+30%)** — a real ratio hole the synthetic `text` pattern (which collapses to a few long matches ⇒ 0.0050 parity) entirely hid. **Compress throughput**: native **10.4 MB/s** geomean — last among real codecs (zlib 55, miniz 51, zig 72, js 47, go 34, ocaml 23, libdeflate 158); the synthetic ~100 MB/s on `text` was the matcher early-stopping on long repetitive matches, absent on real data. **Decompress**: native **92 MB/s** vs zlib 696 / libdeflate 946 / go 236 / ocaml 117 — also last. Each comparator self-verifies its roundtrip on the corpus bytes. | **Bench harness only — 0 library/proof changes, 0 sorries.** New next targets surfaced for the backlog: (a) the large-prose ratio gap (likely single-block Huffman / no block splitting over big files — `plrabn12`/`lcet10` are the signal), and (b) real-data compress throughput (the chain matcher does far more work without the synthetic long-match early-stop). |
| D-16 | **O(1) stored-block sizing — stop building and discarding a full-size stored copy.** The encode share of the *fast-level* pipeline was instrumented at **~30% on text L1** (matcher 2.46 / full deflateRaw L1 3.51 ms ⇒ encode ≈ 1.02 ms), ~7% on prng (matcher-bound). The dispatch sizes the stored/fixed/dynamic candidates from one shared token pass and emits only the smaller — *but* it materialized `deflateStoredPure data` (a ~`|data|`-byte `extract`+`++` copy) **unconditionally**, just to read its `.size`, then discarded it on every compressible input. A stored block is a 5-byte header per ≤65535-byte chunk, so its size is closed-form: added `storedBlockBytes` (O(⌈`|data|`/65535⌉), ~16 steps for 1 MiB) and only build the stored block in the branch where it actually wins. The fixed-Huffman shortcut (skip the dynamic tree at fast levels) was measured and **rejected** — +96% size on text (dynamic Huffman is far better on skewed literals), and it forces the emit on prng where stored is cheaper. | **Real `deflateRaw`, this machine, byte-identical output (sizes 5795/5765/5256 unchanged):** `text` L1 **3.51 → 3.34 ms (~5%)** — the discarded stored build was ~0.17 ms of the ~1 ms encode (`extract`+`++` is fast memcpy, so the waste was smaller than the 30% encode share suggested); `prng` flat (stored wins ⇒ built once either way, no regression). The remaining encode (tokenFreqs + dynamic tree + emit) is *necessary* work; cutting it further means the `BitWriter`/emit micro-path, a deeper lever. | **0 sorries, no new axioms.** `storedBlockBytes_eq : storedBlockBytes data pos = (deflateStoredPure data pos).size` by `fun_induction` (the two definitions share recursion structure) ⇒ branch selection is **provably identical** ⇒ output byte-identical ⇒ `inflate_deflateRaw` and the `_pad`/`_goR_pad` lemmas transfer **verbatim** (they `split` on the dispatch and use only the branch bodies, never the stored `.size` value). |
| D-15 | **zlib-style compression level ladder via deferred hash insertion.** The levels had collapsed (2–4 identical, 5–9 identical); made them a real speed/ratio spectrum following zlib's `deflate_fast`/`deflate_slow` split. **Instrumentation first** (the decisive step): the chain *walk* is not the bottleneck — best-length-first reject / word-`countMatch` / `hash4` move ~1% on text/cyclic (chains are shallow there, would-skip rate aside); **~70% of matcher time on compressible data is hash-chain *insertion*** (1 `hash3` + 2 `Array.set!` per byte, inserting every match-interior position). Added a per-level **`insertCap`** to the chain matcher: levels 1–3 defer most interior insertions (fast, lower ratio), levels ≥ 4 insert every position (best ratio); `chainDepth` deepens 8→1024. Level 6 (default) **byte-for-byte unchanged** (parity). | **Real `deflateRaw`, all levels, this machine:** `text` L1–3 **2–2.5× faster** (209/261/203 vs L6 102 MB/s) at **+10% ratio**; L4–9 parity, flat (chain depth differentiates only on deep-chain/real data, not synthetic — zlib-like). `cyclic` L1–3 ~2.4–2.9× at +98% ratio (periodic data is pathologically deferral-sensitive); `prng` flat (no matches to defer). Deferred-insertion `cap < 16` is *counterproductive* end-to-end (worse ratio → more tokens → Huffman encode dominates), so the fastest level uses `cap = 16`. **Deferred insertion is the first lever, not the last word:** ~70% of matcher time is per-byte hash-chain *maintenance* (the head-update + interior insertion: `hash3` + `Array.set!` traffic), and cutting that *at parity ratio* is open frontier — `UInt32`/`uget` tables (≈ 1.1× measured, untuned), reducing per-position table writes, the Huffman encode path, allocation/RC pressure, or a different matcher structure are all unexplored. libdeflate's C + SIMD + no-RC is a real edge, but it does **not** mean we're out of pure-Lean speed to find. | **0 sorries, no new axioms.** `insertCap` threads through the chain matcher as a parameter; the proofs treat hash + table contents **opaquely** (validity re-checked by `countMatch` at emit), so `lz77ChainIter_resolves`/`_valid`/`_encodable` hold for **every** cap — mechanical threading, no new obligation. `deflateRaw`/`deflateCompressed` + the unified roundtrip (`inflate_deflateRaw`, the `_pad`/`_goR_pad` lemmas) simplified to one stored-vs-chain dispatch across all levels. |
| D-14 | **Fast overlapping back-reference copy** (#2508). `copyLoop`'s memcpy fast path only covered *non-overlapping* references (`length ≤ distance`); overlapping/RLE copies (`distance < length`) fell to the per-byte `copyLoopGo`, dominating decode of highly repetitive data — `cyclic` lvl 6 sat ~11× behind zlib/miniz while everything else was ~2×. Added `fillDouble`: extend the `distance`-byte window to `length` bytes by **repeated doubling** (each step a `ByteArray` append = memcpy), `O(log(length/distance))` memcpys instead of `length` per-byte pushes. | **Same-machine, decode-only, old vs new `copyLoop` (default = buffered decoder):** `cyclic` 1 MiB lvl 6 **435 → 1902 MB/s (4.4×)**, 256 KiB 419 → 1674 (4.0×); `text` unchanged (4349, no overlapping copies). **Combined default vs C/Rust refs** (this dashboard): the 11× outlier is gone — `cyclic` lvl 6 now **2.4×** behind, in line with `text` 1.5× and `prng` 1.7×; native decode is uniformly within ~1.3–2.6× across every workload. Output byte-identical; roundtrip + fuzz pass. | **0 sorries, no new axioms.** `fillDouble` proven to be the periodic extension of the window (slot `i` = `seed[i % seed.size]`; doubling keeps `seed.size` dividing the running size — `fillDouble_get` via `fun_induction` + `Nat.mod_mod_of_dvd`), so the new branch of `copyLoop_eq_ofFn` yields the *same* `List.ofFn` characterization as `copyLoopGo` and every decode correctness proof transfers verbatim. |
| D-13 | **Wide-buffer decoder is now the default** (#2506). Realizes D-12 end-to-end: `Inflate.inflate` / `inflateRaw` / native gzip / native zlib now run `InflateBuf.decodeHuffmanFastBuf`. The buffered primitives moved into `Inflate.lean` (breaks the `InflateBuf` → `Inflate` import cycle); `decodeHuffmanFast` is now a one-line delegation to the buffered decoder, with the `BitReader` reference retained as `decodeHuffmanFastBR` purely as a proof bridge. The transfer lemma `decodeHuffmanFast_eq : decodeHuffmanFast = decodeHuffman` is re-proven as `buffered = BR = spec` (composing `decodeHuffmanFastBuf_eq` with `decodeHuffmanFastBR_eq`); it gains depth-≤15 + well-formed-reader hypotheses, discharged at all 12 transfer sites from facts already in scope. | **Realized end-to-end** (native `decompress_mbps`, this machine, vs pre-flip committed): 1 MiB `text` lvl 6 **1931 → 3729 MB/s (1.93×)**, lvl 1 1156 → 2534 (2.19×); 256 KiB `text` 1601 → 2717 (1.70×); `cyclic` lvl 1 up to 1.96× (Huffman-heavy), lvl ≥ 6 ~1.04× (back-reference copy dominates); `prng` ~1.0× (incompressible ⇒ stored blocks, no Huffman). Output byte-identical; roundtrip + 1000-iter fuzz pass. | **0 sorries**, no `@[extern]`/`@[implemented_by]`/`native_decide`/`maxHeartbeats`. gzip/zlib correctness rides free (built on `inflate`/`inflateRaw`-level theorems, statements unchanged). Two reusable helpers added — `readBits_pos_le` / `readBits_bitPos_le` (success of any ≥1-bit read ⇒ `pos ≤ size` / `bitPos ≤ size*8`, unconditionally) — discharge the reader bound at sites that don't thread it. |
| D-12 | **Wide-buffer Huffman decoder** (#2501, PR #2505). *(Adopted as the default in D-13 / #2506.)* The per-symbol cost left after D-5/D-10/D-11 is the immutable `BitReader` allocated on every symbol/field read. `InflateBuf.decodeHuffmanFastBuf` threads the bit cursor as unboxed scalars `(pos, bitBuf : UInt64, cnt)` — refilling up to 57 bits at a time from `data` (one refill covers a whole `lit(15)+lenExtra(5)+dist(15)+distExtra(13) ≤ 48`-bit back-reference) and consuming by shift — materialising a `BitReader` only at block boundaries; `@[inline]`/`@[specialize]` on `refill`/`decodeSym`/`takeBits` kill the boxed-tuple allocation that an earlier non-`@[inline]` attempt regressed on. **Not yet the default** — `inflateLoop` still calls the `BitReader`-based `decodeHuffmanFast`, so end-to-end decompress (gzip/zlib/inflate) is unchanged; this lands the proven-equal faster decoder, ready to adopt with a one-line swap. | **Standalone decoder, in-process A/B (80-round interleaved, perturbed inputs):** 1 MiB `text` ref 2110 → buf 4324 MB/s (**~2.0×**), 256 KiB `text` 1746 → 3052 (1.75×); `cyclic` ~1.07–1.09× (back-reference copy dominates, decode is a smaller share); `prng` ~1.00× (incompressible ⇒ stored blocks, no Huffman). **End-to-end users see 0 change until the default flips** — the win is unlocked, not yet realized. `takeBits` is now bounds-checked (errors on truncation like `readBitsFast`); inflate output byte-identical across every pattern/size/level. | **Full correspondence, 0 sorries, no `maxHeartbeats`/`native_decide`/`@[extern]`/`@[implemented_by]`.** `BufCorr` invariant → per-op (`refill`/`consume`/`decodeSym`↔`decodeWithTable`/`takeBits`↔`readBits`/`walkTree`↔`decode`) → the symbol-loop induction `go_corr` → `decodeHuffmanFastBuf = decodeHuffmanFast` → `inflateLoopBuf = inflateLoop` → `InflateBuf.inflate = Inflate.inflate` → roundtrip `inflate (deflateFixed x) = .ok x` transferred across the equality. The loop induction runs at default heartbeats via *split-before-unfold* (case the inner decodes while `go` is opaque) + *subst-at-opaque* (unify symbol/values before unfolding, so no proof-carrying `arr[sym]'h` breaks). New infra: `treeDepthLE` + `fromLengths` depth-≤15, a `bitOff < 8` preservation chain for the block sub-decoders, `readBits` availability/EOF lemmas. |
| D-1 | **Stored-block fallback** — `deflateRaw` now returns `pickSmaller (deflateStoredPure data) (deflateCompressed data level)` for levels ≥ 1, so the output is never larger than a stored block. | prng ratio at 1 KiB **1.058 → 1.005** (1083 → 1029 B), exact parity with zlib; 4 KiB 1.012 → 1.001; compressible data unchanged (`pickSmaller` keeps the compressed form). Runtime unaffected. | `inflate_deflateRaw` / `deflateRaw_pad` / `deflateRaw_goR_pad` re-proved via the new `deflateCompressed_*` lemmas + `inflate_deflateStoredPure`; 0 sorries. The result is provably never larger than `deflateStoredPure data`, so the change can never regress ratio. |
| D-1b | **Fixed-Huffman fallback at high levels** — `deflateCompressed` at levels ≥ 5 now returns `pickSmaller (deflateFixedIter data) (deflateDynamic data)`, so dynamic Huffman's tree-description overhead never makes the output larger than a plain fixed-Huffman block. | level-6 out shrinks where the tree overhead dominated: 1 KiB `constant` **18 → 10 B** (ratio 0.0176 → 0.0098), 1 KiB `cyclic` **47 → 27 B** (0.0459 → 0.0264), 4 KiB `cyclic` 54 → 49 B. No regressions anywhere — both candidates share the greedy LZ77 matcher, so it is a per-input best-of-{fixed, dynamic}. Runtime unaffected. | `inflate_deflateCompressed` / `deflateCompressed_pad` / `deflateCompressed_goR_pad` each wrap the level ≥ 5 case with `unfold pickSmaller; split`, discharging the fixed branch via the existing level-1 fixed-Huffman proof and the dynamic branch via the existing dynamic proof; 0 sorries. The result is provably never larger than either candidate, so it can never regress ratio. |
| D-7 | **Share one LZ77 token stream at level ≥ 5** — D-1b left `deflateCompressed`'s level-≥5 branch as `pickSmaller (deflateFixedIter data) (deflateDynamic data)`, and `deflateFixedIter`/`deflateDynamic` each ran `lz77GreedyIter data` independently, so the matcher (which dominates a compress pass) ran twice over identical input. Factored the dynamic encoder into a tokens-taking `deflateDynamicBlock` (`deflateDynamic` is now a thin wrapper), and rewrote the branch to compute `let tokens := lz77GreedyIter data` once, feeding both `deflateFixedBlock data tokens` and `deflateDynamicBlock data tokens`. | **Equivalence refactor — output byte-identical** (all 144 native rows: `out_size` unchanged; ratios untouched). Level-6 compress throughput ≈ doubles on compressible data — 1 MiB `text` **5.67 → 10.84 MB/s** (1.91×), `cyclic` 5.88 → 11.70 (1.99×), `constant` 5.60 → 11.11 (1.98×) — and **prng 1 MiB 4.06 → 7.09 MB/s (1.75×, a 43% wall-clock cut)**, matching the predicted ~42% from removing the redundant matcher pass. Levels 0–4 unaffected (don't use the shared path). | `inflate_deflateCompressed` / `deflateCompressed_pad` / `deflateCompressed_goR_pad` convert the shared `let` form back to `pickSmaller (deflateFixedIter data) (deflateDynamic data)` via `rw [show … from rfl]` (definitionally equal since `lz77GreedyIter` is deterministic), then reuse the D-1b proofs verbatim; `deflateDynamic_spec` adds `deflateDynamicBlock` to its `unfold` (body unchanged). 0 sorries. |
| D-3 | **UInt32 hash arithmetic** — the matcher's `hash3` computed `(a ^^^ (b<<<5) ^^^ (c<<<10)) % 65536` in boxed `Nat`, once per input byte; Lean's `Nat` bitwise XOR/shift is slow. Compute the XOR/shift in `UInt32` instead, with `.toNat % hashSize` preserving the exact same index. An experiment (`exp/d3-matcher`, not merged) decomposed the cost across variants: the `%`→`&&&` mask, `Array Nat`→`Array UInt32`/sentinel tables, and unchecked array access each contributed ~nothing — **the entire win is the `UInt32` hash arithmetic** (overturning the pre-experiment guess that table cache traffic was the lever). | **Equivalence — output byte-identical** (all native `out_size`/ratios unchanged). Matcher-only ~16× on text / ~4.6× on prng at 1 MiB; **end-to-end level-6 compress: 1 MiB `text` 11.1 → 100.6 MB/s (9.1×), `cyclic` 11.7 → 108.2 (9.3×), `prng` 7.2 → 16.8 (2.3×); 256 KiB `text` 11.0 → 96.4 (8.8×).** | The three `hash3` defs (`lz77Greedy`, `lz77GreedyIter`, `lz77Lazy` — the last shared by `lz77LazyIter`) change identically, so `hash3_eq` stays `rfl` and the `< hashSize` bound (`Nat.mod_lt`, the `%` wrapper preserved) is untouched — **0 new proof obligations, 0 sorries**. |
| D-6 | **Loop-free `BitWriter` bit-packing** — `writeBits`/`writeHuffCode` now merge a whole field into a 64-bit accumulator in one shift/OR and flush whole bytes (`flushAcc`), instead of a per-bit loop. Diagnosis correction: the old packer already flushed *per byte* (it pushed only when a byte filled), so the cost was the per-bit *iteration*, not `ByteArray.push`; on incompressible input `writeHuffCode` (≈58% of the level-6 prng pass) reversed each Huffman code bit-by-bit. The new `writeHuffCode` reverses the code's 16 bits with a branchless swap network (`reverse16`) + one down-shift, making each emitted symbol constant-work. (The List↔Array conversions originally hypothesized for D-6 were confirmed negligible and dropped from the backlog.) | **Output byte-identical** (all 144 native `out_size`/ratios unchanged). Level-6 **prng** compress **1 MiB 16.7 → 22.0 MB/s (1.31×)**, 256 KiB 16.2 → 21.2 (1.31×), 64 KiB 14.8 → 19.2 (1.30×); level-1 prng 1 MiB 23.1 → 29.7 (1.29×). `text`/`cyclic` ≈ 1.0–1.04× (matcher-bound — emit is a small fraction there). **Short of the issue's ≈1.8× target**: emit is now ~2× faster but only ~58% of the prng pass, so the rest needs the matcher constant-factor work (reframed D-3 follow-up). | New `flushAcc_spec` (a 64-bit accumulator holding `total` valid bits flushes to exactly those bits, by `testBit`), `reverse16_testBit` (the swap network flips bit `j`↔`15-j`, `bv_decide` over the 16 positions), and `writeBits_spec`/`writeHuffCode_spec` re-derive the four `_toBits`/`_wf` theorems with **unchanged statements**, so every downstream emit-correctness proof (`EmitTokensCorrect`, `DeflateDynamicEmit`, `DeflateFixedCorrect`, …) transfers verbatim. `writeBits` masks the field with `% (1 <<< n)` (cold path; cleaner to bridge than subtraction). Removed the dead per-bit `addBit` machinery. 0 sorries. |
| D-8 | **Lazy matching at level ≥ 5** — D-7 left the shared level-≥5 token stream as `lz77GreedyIter data`. Switched it to the **lazy** matcher `lz77LazyIter data` (the matcher levels 2–4 already use), so the high level finds better matches and narrows native's text-ratio gap vs zlib. Still one matcher pass feeding both `deflateFixedBlock data tokens` and `deflateDynamicBlock data tokens`. | **Text ratio improves at level 6 at every size** (lazy finds longer matches): 1 MiB `text` **0.0119 → 0.0105** (12431 → 11047 B, −11.1%), 256 KiB 0.0126 → 0.0112 (3291 → 2945 B), 64 KiB 0.0152 → 0.0136 (993 → 892 B), 16 KiB 0.0241 → 0.0220, 1 KiB 0.1797 → 0.1660. `cyclic` unchanged (strictly periodic — lazy finds no better match), `prng` unchanged (stored fallback). **No regression on any pattern.** Compress throughput essentially unchanged — 1 MiB `text` 10.84 → 11.07 MB/s (within run-to-run noise; still ≈ 2× faster than pre-D-7's two greedy passes). | Generalized `deflateDynamic_spec` → `deflateDynamicBlock_spec data tokens htok_enc hempty` (parameter lift: greedy-specific `lz77Greedy_encodable` use replaced by the `htok_enc` hypothesis; the empty-input branch by `hempty`; ~390-line body unchanged) and `inflate_deflateDynamic` → `inflate_deflateDynamicBlock` (adds an `hresolve` hypothesis); both greedy theorems re-derive as the `lz77GreedyIter` instance. The three `deflateCompressed_*` proofs feed the shared lazy tokens through the generalized lemmas via local `lz77LazyIter_{encodable,empty,resolves}` helpers; the fixed branch is `deflateLazyIter` (already proven). 0 sorries. |
| D-9 | **Size-then-emit — emit only the smallest block at level ≥ 5** (#2483). D-8 left the level-≥5 path emitting **all three** candidate blocks (stored + fixed + dynamic) and keeping the smallest via the `pickSmaller` cascade; on incompressible input the stored block wins, so both expensive Huffman symbol emissions were computed and discarded (profile D-2: `emitTokensWithCodes` ≈ 17.6 ms of the 60 ms prng path). Now each candidate's exact byte size is computed from the already-counted `tokenFreqs` as a freq·codeLen dot product (`symbolBitCount`/`fixedBlockBytes`/`dynBlockBytes`, O(#symbols), no bit-banging; the dynamic tree-header bits come from running `writeDynamicHeader` into an empty `BitWriter` and reading its new `bitLength`), and `deflateRaw`/`deflateCompressed` emit only the argmin (same strict-`<` tie-break). The dynamic emit reuses the sized code lengths via a new `deflateDynamicBlockCore` (takes precomputed `litLens`/`distLens`), so the winning tree is built once. | **Equivalence refactor — output byte-identical** (all native `out_size`/ratios unchanged across every row). **prng 1 MiB compress 16.7 → 38.8 MB/s (2.32×)** — both losing Huffman emits skipped; 256 KiB 16.2 → 35.4 (2.19×), 64 KiB 14.8 → 29.5 (1.99×). Compressible patterns also improve once the loser-emit + a redundant length recompute are removed: 1 MiB `text` 99.8 → 109.3 MB/s (1.09×), `cyclic` 109.0 → 113.8 (1.04×). No regression at any size ≥ 4 KiB (1 KiB `text` 0.95×, within noise). | The size helpers are opaque cost models (`@[irreducible]` to keep `split` from unfolding the 286-element fold past `maxRecDepth`); the freq·codeLen identity is **not** proved — the roundtrip theorems hold for whichever block is chosen, and the new `ZipTest/SizeHelpers` conformance tests pin `fixedBlockBytes`/`dynBlockBytes` to the emitted `.size` (so the selection reproduces `pickSmaller` exactly). `inflate_deflateRaw` / `deflateRaw_pad` / `deflateRaw_goR_pad` and the three `deflateCompressed_*` proofs `split` the new size conditions (the level-≥5 winner is one of the unchanged blocks; `deflateDynamicBlockCore … = deflateDynamicBlock data tokens` definitionally, so the dynamic lemmas transfer); `deflateDynamicBlock_spec` is unchanged (its `show` reframe is defeq through the new `Core` layer). 0 sorries. |
| D-4 | **Hash-chain match finder, wired at level ≥ 5** (#2485, A1). The single-probe matcher stored one position per hash bucket, so it only ever checked the most recent occurrence — leaving native text compression 2× behind zlib. Added `lz77Chain`/`lz77ChainIter`: a greedy matcher that walks a bounded-depth `head`/`prev` hash chain (`chainDepth` per level) and keeps the longest in-window match. `deflateCompressed`/`deflateRaw` at level ≥ 5 now run it instead of the single-probe lazy matcher. | **Native text compression reaches C-reference parity** (the 2× gap closed): 1 MiB `text` ratio **0.0105 → 0.0050** (= zlib/miniz/libdeflate exactly), 64 KiB **0.0136 → 0.0075**. `cyclic` unchanged (already matched), `prng` unchanged (stored fallback) — **no regression on any pattern**. Cost: compress throughput drops (chains do more work) — 1 MiB `text` 107 → 15 MB/s, the standard ratio/speed tradeoff; recoverable with an early-reject (candidate byte check before `countMatch`) and `nice_match`, deferred to #2494. | **Fresh validity proof, not equivalence** (output changes). `lz77Chain_valid`/`_resolves` (`ValidDecomp` → resolves) and `lz77Chain_encodable`, transferred to the iterative `lz77ChainIter` via `lz77ChainIter_eq_lz77Chain`. **Key insight:** the chain is only a *heuristic for finding* candidates — validity is re-established at emission by `countMatch` + the explicit window guards, so the `prev`/`hashTable` contents never enter the proof (`chainWalk_spec` holds for *any* `prev` array), making the matcher proof ~the size of the existing greedy one rather than a `prev`-invariant nightmare. The whole roundtrip (deflate/gzip/zlib, `*_pad`, `*_goR_pad`) transfers via the new generic `inflate_deflateFixedBlock` / `deflateFixedBlock_spec_of` (fixed-branch twins of the dynamic-block lemmas, accepting arbitrary valid token streams) and the `lz77ChainIter` contracts. 0 sorries; all tests + 1000-iter fuzz pass. |
| D-4b | **Per-level chain depth + `maxLen` early-stop** (#2494, A2). A1 left a fixed `chainDepth` and a `chainWalk` that always walked the full chain — so high levels gave no extra ratio and text compress throughput had regressed 107 → 15 MB/s (deep walks over long repetitive matches). Two changes: (1) `chainDepth` now scales 32/128/256/512/1024 across levels 5–9; (2) `chainWalk` stops as soon as `bestLen` reaches `maxLen` (the longest possible match — provably unbeatable). | **Throughput recovered with no ratio loss:** text 1 MiB compress **15 → 99 MB/s** at the same 0.0050 reference-parity ratio (the early-stop fires immediately on repetitive input where matches hit `maxLen`). **Level scaling now visible** on diverse input — `words` 256 KiB ratio **L1 0.517 → L6 0.340 → L9 0.332** (monotone; level 9 < level 6). No regression: text/cyclic/prng ratios unchanged. | **Proof free + one small case.** `chainDepth` is `∀`-quantified in every contract (`lz77ChainIter_*` take `maxChain` as a parameter), so the level map needs zero proof change. The early-stop adds one branch to `chainWalk`; `chainWalk_spec` gains a `split` on `bestLen ≥ maxLen` whose stop case reuses the same invariant `Q` the recursion already established — the returned `(bestLen, bestPos)` is valid whether the walk stops early or runs out. 0 sorries; all tests + fuzz pass. |
| D-10 | **Allocation-light `readBits` on the decode hot path** (#2500). A `perf` profile of native inflate on a real 1 MiB corpus showed decode is O(n) but **allocation-bound**: ~41% of time in `malloc`/`free`/`lean_dec_ref_cold` and ~26% in `BitReader.readBits`/`readBit`, because the immutable `BitReader` allocates a fresh struct (+ `Except`/pair) on *every bit* and `readBits n` loops `readBit` n times = n allocations. Added `readBitsFast` (in lean-zip, no `lean-zip-common` change): thread the cursor `(pos, bitOff)` as unboxed `Nat`s, build the `BitReader` **once** at the end — O(1) allocations per field. Wired into `decodeHuffmanFast`’s extra-bits reads (the hot ones). | **Decompress ~1.9× faster** on a real code corpus (42 → 79 MB/s); the `words` pattern (match-heavy ⇒ many extra-bit fields) **29 → 63 MB/s** (2.2×); `text` 313 → 372. Re-profile: `lean_dec_ref_cold` **19% → 7.6%**, `malloc`+`free` **~41% → ~12%** — the per-bit allocation churn collapsed. Inflate output identical; ratios untouched. (New top costs: `copyLoop` 15% — bulk back-reference copy is the next decode lever — and the per-symbol `BitReader` churn, #2501.) | **Generational refinement, 0 sorries.** `readBitsFast_eq : readBitsFast br n = br.readBits n` by a step-for-step loop correspondence (`readBitsFast.go` threading `(pos,bitOff)` ↔ `readBits.go` threading the `BitReader`; induction on the bit count, no bit-assembly). The looped `readBits` stays the canonical spec; `decodeHuffmanFast_eq` rewrites `readBitsFast → readBits` at the two extra-bits steps so the whole roundtrip (incl. gzip/zlib, pad, goR) transfers unchanged. All tests + 1000-iter fuzz pass. |
| D-11 | **Bulk `memcpy` for non-overlapping back-references** (#2503). D-10's re-profile left `Inflate.copyLoop` (~15%) + its `ByteArray.push` (~6%) as the top remaining decode cost: a back-reference was copied **one byte at a time** (`buf.push buf[start + k % distance]` for `k ∈ [0, length)`), so an `L`-byte match meant `L` `push`es / bounds-checks / `%` indices. Split `copyLoop` into a per-byte worker `copyLoopGo` (the reference) and a dispatcher `copyLoop`: for the common **non-overlapping** case (`k = 0 ∧ length ≤ distance`) every index `start + k % distance` is just `start + k`, so the whole copy is the contiguous slice `[start, start+length)` — one `buf.extract` + one `++` (a `memcpy`). Overlapping (RLE) copies fall back to `copyLoopGo`. Both decode functions call `copyLoop` verbatim, so the wiring needs no decode-function or `decodeHuffmanFast_eq` change. | **Decompress `text` up to ~4.6× faster, scaling with match length** (longer matches ⇒ more per-byte `push`es replaced by one `memcpy`): 256 KiB `text` lvl6 **358.8 → 1649.5 MB/s (4.6×)**, lvl1 303.2 → 1043.6 (3.4×); 64 KiB lvl6 304.4 → 915.2 (3.0×), lvl1 274.9 → 700.1 (2.5×); 16 KiB lvl6 193.1 → 336.4 (1.7×). `prng` unchanged (stored blocks, no back-references) — **no regression on any pattern**; inflate output byte-identical; ratios untouched. | **Generational refinement, 0 sorries.** `copyLoop_eq_ofFn` (the existing `List.ofFn` characterization, **statement unchanged**) is re-derived across the dispatcher's two branches: the non-overlapping case via a new `extract_data_toList_ofFn` (`(buf.extract start (start+length)).data.toList = List.ofFn (fun i => buf[start+i]!)`, by `List.ext_getElem`) plus `i % distance = i` since `length ≤ distance`; the fallback via the worker's `copyLoopGo_spec` (the old `copyLoop_spec`, renamed). Because the optimization lives entirely inside the `copyLoop` definition and `copyLoop_eq_ofFn` keeps its shape, `decodeHuffmanFast_eq` and every downstream inflate proof transfer **verbatim** — the heavy `InflateTable` proof is untouched. All tests + 1000-iter fuzz pass. |
| D-5 | **Table-driven Huffman decode for inflate** (#2484). Native inflate decoded each Huffman symbol by walking the `HuffTree` one bit per node (`HuffTree.decode`). Added a `2^9` "fast-bits" lookup table (`HuffTree.buildTable`): slot `i` holds the `(symbol, codeLen)` reached by walking the tree on the bits of `i`. `HuffTree.decodeWithTable` peeks 9 bits (`peekFast`, two direct byte reads), indexes the table, and consumes `codeLen` bits in one step — falling back to the `HuffTree.decode` walk for codes longer than 9 bits and when fewer than `codeLen` bits remain. `Inflate.decodeHuffmanFast` builds the literal/length + distance tables once per block; `inflateLoop` runs it on the **verified route** (no `@[implemented_by]`). | **Equivalence refactor — inflate output byte-identical** (all roundtrip + 1000-iter fuzz tests pass; ratios untouched). **Decompress speedup on Huffman-decode-bound input** (the regime the table targets): a non-periodic `words` pattern (PRNG-ordered English words → many short matches + literals) decodes at **64 KiB 28.7 MB/s, 1 MiB 29.0 MB/s** vs the old bit-by-bit walk's ~20.5/21.5 (≈1.35–1.4×). The four periodic patterns are copy/stored-bound for *decode* (long matches or stored blocks) so they barely move — the table only helps where symbol decoding dominates. | **Formal proof, not `@[implemented_by]`** (Kim's call). `Zip.Spec.InflateTable.decodeWithTable_eq` proves `decodeWithTable (buildTable tree) br = decode tree br` as a full `Except` result (same symbol *and* reader): `tableEntry.go` reaching a leaf gives a `TreeHasLeaf` path = `cwOf idx len` (codeword from the peeked bits); `peekFast`'s bits match the stream (`peekFast_testBit`, UInt32↔Nat `testBit` accounting); `decode_go_complete` turns that into the tree-walk result; the advanced reader equals the walk's by `toBits` + cursor-bound (`advReader_eq`). `decodeHuffmanFast_eq` lifts it to the block loop by functional induction; `inflateLoop`'s correctness/completeness/suffix/bound proofs transfer with one `rw [decodeHuffmanFast_eq]` each. A `decodeWithTable` guard on `bitOff ≥ 8` makes the equality unconditional (no wf side-goals at transfer sites). 0 sorries; `ZipTest/InflateTable` adds a differential sanity check over every code-length regime. |

## Experiment findings (D-4 / A1: hash chains, #2485)

Phase-0 experiment (throwaway `DeflateChainExp.lean`, unverified greedy matcher
with bounded-depth `head`/`prev` hash chains, fed through the existing
size-then-emit) on 64 KiB `text`, vs the shipped matcher (lazy + single-probe):

| matcher | size | ratio | roundtrip |
|---|---|---|---|
| native (lazy, single-probe) | 892 B | 0.01361 | — |
| greedy + chains, maxChain=16 | 505 B | 0.00771 | OK |
| **greedy + chains, maxChain=128** | **494 B** | **0.00754** | OK |
| greedy + chains, maxChain=1024/4096 | 494 B | 0.00754 | OK |

**Conclusion: chains close the entire 2× text-ratio gap and reach C-reference
parity** (zlib 0.0076, libdeflate 0.0074, miniz 0.0075) — *greedy alone*, before
adding lazy. The single-probe hash was the whole gap. Depth saturates fast on
this text (16 ≈ 128); `maxChain=128` is the sweet spot here, but harder inputs
will scale further (motivates per-level depth, #2494). All depths roundtrip.
Decisively justifies the verified-matcher proof effort (#2485). Compress
throughput cost not yet measured (chains add probes per position) — measure when
the verified version lands.

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
