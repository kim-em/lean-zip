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
contention is common-mode, Canterbury, native compress):

    htInsertCap   L1 speed vs chain    L1 ratio vs chain
    0 (fastest)   1.00x (flat)         +5.2% (worse)
    2             0.92x (slower)       +1.7% (worse)
    258 (best r)  0.73x (much slower)  −1.6% (better)

No config beats the tuned depth-4 chain on both axes. Interior insertion buys
ratio by spending work; the fastest point only ties speed while losing 5%
ratio. **L1 is emit-bound** (confirms #2726): the token walk + BitWriter
dominate, so matcher microcost is diluted, and any ratio loss is paid back as
extra emit work. #2738's "chain machinery ~47% of cycles → easy win" premise
does not translate. Codex, consulted independently, agreed.

So `lzMatch`/`lzMatchP` keep the chain at L1; the matcher stays as a verified
reference with the frontier recorded in the `htMatch` docstring.

## Process notes / lessons

- Speed measurements on the shared box (`chungus`) were worthless under load
  (load hit 60; the same change read as 0.7x–1.1x). Only a **same-core
  back-to-back A/B** gave a trustworthy verdict. Kim asked to enforce single-core
  pinning; that is already handled by open PR #2747 (`bench/pin_core.sh` picks the
  idlest core and routes `bench/run.sh` + the perf-pr-graphs skill through it), so
  I did not duplicate it.
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
