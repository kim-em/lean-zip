# Progress: batched literal emission via pushUInt64LE (#2795) — negative verdict

**Date**: 2026-07-08 UTC
**Session type**: Feature (benchmark-first probe; measured negative, recorded as verdict)
**Issue**: #2795

## What was done

Followed the issue's framing comment exactly: spike first with the
equivalence `sorry`'d, measure with `inflate-profile` same-worktree A/B,
report both retired instructions and cycles, and treat the result as the
deciding probe — not a guaranteed win.

1. **Spike implemented** (`goTreeFreeUB` in `Zip/Native/InflateTreeFree.lean`):
   up to 8 consecutive literals accumulate LSB-first in a `UInt64` + `USize`
   count (both unboxed loop state), flushed as one `ByteArray.pushUInt64LE`
   on batch-full and at every slow-path entry (match / end-of-block /
   long-code literal); output-limit guard reads the conceptual size
   `output.size + litCnt`. Equivalence theorem `goTreeFreeUB_eq` stated
   against `goTreeFreeU` over `pushLEBytes`-flushed output, `sorry`'d
   pending the measurement. Full test suite passes with the spike wired in
   (behavioral witness).
2. **Measured** (protocol: bench/README § *Profiling the decoder*; baseline
   = 41b1b857 built in the same worktree; level-6 libdeflate payloads;
   x-ray / ooffice / sao / alice29 / plrabn12; medians of 5 interleaved
   rounds, 8 for the shared baseline; AMD EPYC 9455). Two variants: exact
   guard, and a measurement-only "ceiling" with the baseline's cheap guard.
   **Both regress: instructions +1.0–6.6%; median cycles +4.4–5.4% (exact)
   / +2.2–3.4% (ceiling); best-of-rounds cycles also positive on every
   file.** Full table in the `plans/track-d-state.md` verdict entry.
3. **Verdict recorded** in `plans/track-d-state.md` (this PR), mirroring the
   #2779/#2791 precedent. The equivalence proof was deliberately **not**
   written (benchmark-first: the measurement says don't land the change).
   A Codex second opinion concurred with the negative verdict; its asks
   (soften the "cannot flip the sign" claim, name the leaner-batcher
   shavings considered, more cycle rounds, a #2811 re-run caveat) are
   incorporated in the ledger entry.
4. **Spike preserved unmerged** on branch `perf/2795-batched-literal-spike`
   (604cc1a9 exact-guard, 45b355c6 ceiling probe).
5. **Incidental discovery filed as #2811**: `copy_within_ffi.o` is compiled
   without `-O2 -DNDEBUG` (unlike its two sibling FFI targets), leaving
   un-inlined lean.h helpers with asserts enabled on the match-copy path —
   roughly a third of whole-program decode self time on x-ray. Likely
   across-the-board decode win; re-baselines decode percentage claims.

## Key findings

- `lean_byte_array_push`'s exclusive fast path is ~6–8 instructions
  including call overhead (1.96% self time on x-ray), fully hidden in the
  bitBuf→table→len recurrence's latency shadow. The issue's "~4% / 10–15%"
  evidence predates #2804/#2805/#2808 and is further inflated by #2811.
- Batch bookkeeping nets ~+7 instructions per literal (ceiling A/B, x-ray),
  i.e. the replacement costs more than the removed call. An empty-batch
  flush call is also paid on every match.
- Decision-rule consequence, stated per the framing comment: cycles did NOT
  drop more than instructions — the store call was not on the critical
  path, so the batched-store motivation for #2798/#2799 is dead; any case
  for those rewrites must rest on what they additionally remove and needs
  its own probe.

## Quality metrics

- sorry count on this branch (`grep -rc sorry Zip/`): unchanged from master
  (the sorry'd spike lives only on the preserved spike branch).
- `lake exe test`: passes (doc-only change on this branch).

## What remains

Nothing on #2795 (closed by this PR as measured-negative). Follow-ups live
in #2811 (copy_within flags) and, if ever revisited, the preserved spike
branch documents the exact re-measurement protocol.
