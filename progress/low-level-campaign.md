# The low-levels campaign — L1 endpoint + L2-L5 speed (three PRs)

**Goal (Kim's directive):** move L1 faster — judged against the *extrapolated*
L2→L1 mixing line (the correct frontier test for a ladder endpoint, where
nothing exists to mix beyond) — and any pure speed at L2-L5.
**Result:** weighted Silesia L1 91.5 → 103.4 MB/s (+13%) at byte-identical
output (outside the endpoint line by construction), L2 69.0 → 93.4 (+35% at
equal ratio), L3 62.7 → 81.6 (+30% at *better* ratio), L4-L8 +2-5% as a
side effect. zlib L3 and the whole JS fflate L1-L4 curve moved inside the
native hull.

## What landed

1. **#2827 — merged-array USize greedy matcher loop.** The greedy tier
   (L1-L3) had never received the lazy tier's structural stack (#2767 merge,
   #2821 USize): it still threaded two chain arrays with a `Prod` allocation
   per match and runtime-guarded stores per position, profiling at 27-36%
   outer-loop self time. Byte-identical port, `greedyMergedLoop_eq`.
2. **#2829 — packed emit tables + scalar BitWriter flush kernel.** The emit
   path (24-27% of L1) chased a boxed `(UInt16 × UInt8)` pair per token and
   re-reversed each Huffman code's bits per symbol; codes are now packed
   pre-reversed into one `UInt32`, and the flush bookkeeping runs on
   registers. Byte-identical, `_def` equation statements unchanged.
3. **#2830 — L2/L3 re-grid.** The `l1-sweep2` grid (new bench exe) found both
   mid rows ~10% below the greedy-band mixing frontier; the libdeflate
   `niceLen` 10/14 cutoffs (#2744) were the culprit. L2 → (chain 8, cap 8,
   cutoff off): equal ratio, +11%. L3 → (chain 16, cap 32, cutoff off):
   better ratio, +7%.

## Verdicts worth remembering

- **The L1 endpoint is structurally settled.** No weaker-matcher corner comes
  near the extrapolated line: head-probe-only reaches 111 MB/s where the line
  demands ~340 (the line's zero-crossing is at ratio ≈ 0.394, so
  big-ratio-give-up corners like miniz L1 at 0.4133 can never qualify). L1's
  cost was never match search — it was loop overhead and emit. Endpoint
  progress = output-neutral structural speed, full stop.
- **Measurement hazards found by #2829** (recorded here because they will bite
  again): (a) inlining a branch into a hot FBIP writer made the ctor-reuse
  pass pick the wrong reuse site (−10-14%) — check `del_object` placement in
  the generated C after touching hot writers; (b) a baseline linked from stale
  `.lake` objects carried a luckier GCC inline layout for *untouched* code —
  check `nm` for hot-symbol presence, not just compiler strings, before
  trusting an A/B.
- **Fresh-worktree layout luck** (~1-2% on untouched levels) showed up in two
  dashboard refreshes; the interleaved same-worktree A/B in each PR body is
  the authoritative magnitude.

## Open round-3 candidates

Lazy-tier outer-loop untag (mirrors #2827 at L4-L8; `lz77LazyMergedLoop` is
~18% self at L5), freq-count fusion into the matcher pass (kills the separate
5-9% `tokenFreqsP` walk), the value-equal fused huff+extra writer, USize
emit-loop index, packing the fixed-Huffman tables like #2829 did the dynamic
ones.
