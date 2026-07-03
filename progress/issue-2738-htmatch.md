# Feature: chainless 2-way-bucket L1 matcher (ht_matchfinder) — negative result

- **Date**: 2026-07-02 UTC
- **Session type**: feature
- **Issue**: #2738
- **PR**: #2748

## What was built

A formally-verified chainless 2-way-bucket match finder (libdeflate
`ht_matchfinder` style), sorry-free:

- `htBest`/`htProbe` (shared): probe ≤2 bucket entries, keep the longest
  `countMatch`-verified in-window match, `niceLen = 32` early-out.
- `htInsert` (shared): after a match, insert interior positions into the 2-way
  table, bounded by `htInsertCap`. The table is a pure heuristic — it never
  enters a proof — so `htInsert` is one shared def used identically by all three
  twins with **zero** bridge lemmas.
- `htMatch` (recursive ref) / `htMatchIter` (boxed) / `htMatchIterP` (packed),
  min-match 4, in `Zip/Native/Deflate.lean`.
- Correctness in `Zip/Spec/HtMatchCorrect.lean`: `ValidDecomp` → `resolves`,
  `encodable`, `empty`; `htMatchIter_eq_htMatch`; `htMatchIterP_eq`/`_map`.
  Reuses the `chainWalk_spec`-shaped interface: `htProbe_spec` (`ProbeOk`
  postcondition) feeds a `lz77Chain_mainLoop_valid`-mirror proof.
- Conformance test `ZipTest/HtMatch.lean` (twin agreement, min-match-4 bounds,
  L1 roundtrip on edge shapes).

## Why it is NOT wired into L1

Direct A/B (both binaries `taskset`-pinned to one core, back-to-back so
contention is common-mode, native compress). **Silesia** (12 files, the
representative corpus; `dickens` is #2738's own profiling target), master drift
1.005x:

    htInsertCap   L1 speed vs chain    L1 ratio vs chain   (Silesia geomean)
    0 (fastest)   0.96x (slower)       +5.8% (larger)
    258 (best r)  0.61x (much slower)  +0.4% (still larger)

Canterbury (smaller, cache-resident, not the target) is slightly kinder — cap 0
ties speed, cap 258 reaches −1.6% ratio — but on Silesia the bucket cannot reach
ratio *parity* at any speed cost: maxed-out insertion is still +0.4% larger than
the chain while 39% slower. No config beats the chain on either axis. Interior
insertion buys ratio by spending work; the fastest point is already slower AND
larger. **L1 is emit-bound** (confirms #2726): the token walk + BitWriter
dominate, so matcher microcost is diluted, and any ratio loss is paid back as
extra emit work. #2738's "chain machinery ~47% of cycles → easy win" premise
does not translate. Codex, consulted independently, agreed.

So `lzMatch`/`lzMatchP` keep the chain at L1; the matcher stays as a verified
reference with the frontier recorded in the `htMatch` docstring.

## Process notes / lessons

- Speed measurements on the shared box (`chungus`) were worthless under load
  (load hit 60; the same change read as 0.7x–1.1x). Only a **same-core
  back-to-back A/B** gave a trustworthy verdict, and the final Silesia sweep was
  taken at load ~1.5 for good measure (master drift 1.005x confirmed it clean).
  Kim asked to enforce single-core pinning; that is already handled by open PR
  #2747 (`bench/pin_core.sh` picks the idlest core and routes `bench/run.sh` +
  the perf-pr-graphs skill through it), so I did not duplicate it.
- **Always benchmark on Silesia, not just Canterbury.** Canterbury (small,
  cache-resident text) was misleadingly kind here — it showed cap 0 tying speed
  and cap 258 winning ratio, which looked borderline-salvageable; Silesia (the
  representative corpus) showed the bucket losing on *both* axes at every cap.
  A Canterbury-only read would have overstated the case for the matcher.
- The "table is a pure heuristic" property is powerful: it let interior
  insertion be added/tuned with no proof churn at all.

## Disposition

PR #2748 keeps the matcher unwired as verified infra + documented finding.
Asked Kim (no response in the session window) whether to keep-as-infra or close
and ship nothing; defaulted to the PR so the work + finding are recorded. The
path to the fast-L1 corner is the emit half (#2734), not the matcher half.

## Quality metrics

- sorry count in `Zip/`: 0 (unchanged).
- Full `lake build` + `lake exe test` green.
