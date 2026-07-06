# Progress: delete the lazy matcher's per-position `(hashTable, prev)` Prod (#2767)

**Date**: 2026-07-06 UTC
**Session type**: Feature (explore → optimize)
**Issue**: #2767
**Baseline**: ac14de13

## Summary

#2767 asked to delete the per-matched-position `(hashTable, prev)` Prod that
`updateHashesFastU` returns (one `lean_alloc_ctor` + unpack + free per matched
position). Two shapes were tried:

1. **Fuse the walk+insert into a separate step function** (the issue's proposal):
   **measured negative** — −24…−47 % on dickens and a **stack overflow** on
   mozilla. Retired.
2. **Merge `hashTable` + `prev` into one `Array Nat`** (the "cleaner kill" the
   rc-allocator-tax doc flagged): **measured positive** — **+3–5 % dickens,
   +2 % mozilla**, byte-identical, no stack overflow. This is the shipped
   direction (proof column in `Zip/Spec/LZ77MergedCorrect.lean`, one lockstep
   lemma WIP as of this entry).

## Profile (mozilla, mixed L4–L8, `perf record`, self-time)

    34.5%  chainWalkPackedU          ← match finding (out of scope; #2765/#2774)
    10.0%  lz77ChainLazyIterP_mainLoop
     9.3%  updateHashesFastU         ← the Prod-bearing insert walk
     3.5%  lean_dec_ref_cold ; 1.0% mi_free ; 0.85% mi_malloc_small
     0.34% updateHashesGuarded       ← dispatch, negligible

The Prod is O(1)/matched-position while the insert loop is O(matchLen), so it is a
minority of the 9.3 %; an extra-Prod-per-step control put one Prod at ~1.5–2.5 %
of total on dickens. Consistent with the rc-tax attribution (the pair was ~3–4 %
of L1 allocator traffic).

## Attempt 1 — separate-args fusion (negative, retired)

`lz77LazyLoopP`/`lz77LazyInsertP`: a mutually-recursive rewrite threading the two
arrays as separate args so no Prod is built. Byte-identical output, Prod
confirmed gone in the generated C — but:

| file | L4 | L5 | L6 | L7 | L8 |
|---|---|---|---|---|---|
| baseline dickens | 31.3 | 26.5 | 26.2 | 21.9 | 21.0 |
| fused dickens | 20.2 | 21.0 | 13.7 | 12.5 | 12.3 |
| fused mozilla | — **stack overflow** — | | | | |

Two independent, fatal causes, both from splitting the single self-tail-recursive
loop into two mutually-recursive functions:

1. **Refcount linearity lost across the boundary.** Borrow inference adds
   `lean_inc_n(prev, 2)` before the chain walks; insert self-time **tripled**
   (9.3 %→28.5 %) on a byte-identical loop body — the tables reach the insert loop
   shared, so the in-place `set` degrades. A `partial def` control of the
   *unfused* single loop measured at baseline, ruling out a `partial def`
   artifact — it is the split.
2. **No tail-call optimization across the mutual boundary.** Lean turns a single
   self-tail-recursive function into a `goto` loop (constant stack); it does not
   fuse two mutually sibling-tail-calling functions, and leanc does not TCO them —
   the stack grows one frame per position → **stack overflow on mozilla**,
   reintroducing the exact blow-up the iterative matchers were built to avoid.

## Attempt 2 — merge the two arrays (positive, shipped direction)

Hold the chain state in ONE `Array Nat` of size `prevSize + hashSize`, laid out
as **`prev ++ hashTable`** — the `prev` ring at offset `[0, prevSize)`, the hash
table at `[prevSize, …)`. The interior-hash walk (`updateHashesMerged`) threads
and returns a **single** array, so no Prod is allocated, while the main loop
(`lz77LazyMergedLoop`) stays one self-tail-recursive `goto` loop (linear arrays,
no stack growth).

The refinement that makes it a clean win: **`prev` at offset 0** ⇒ the 34.5 %-hot
chain walk reads `c[cand & 0x7FFF]` **unchanged** (the combined array is passed
straight in where `prev` was); only the once-per-position hash-table accesses take
a `+ prevSize` offset. Generated C confirmed: `updateHashesMerged` has **0
`lean_alloc_ctor`** (baseline `updateHashesFastU` had 2) and returns a single
array assigned directly at every call site (no `lean_ctor_get` pair unpack).

Measured with a **self-controlled sandwich** (base→merged→base, both binaries
built in the *same* worktree, pinned to one core, min-of-7; base = geomean of the
two bracketing runs). The dashboard *overlay* (single-pass Silesia, cross-session)
reads ~1.00x because a ~2-3 % delta is below its ±30 % noise floor — the sandwich
is the trustworthy signal for a delta this size (per `perf-pr-graphs`).

**Critical: the win needs proven-bounds `set` in the insert loop.** The first
cut used the runtime-guarded `guardedSet`/`headProbeGuarded` (a bounds branch per
insert step, chosen for proof-simplicity). That **regresses insert-dense files**
(xml −1.4…−2.9 %) — the per-step branch outweighs the per-position Prod saving.
Switching the inner loop to proven-bounds `set` (no branch, as `updateHashesFastU`
does) makes the win **uniform**:

| file (proven-bounds) | L4 | L6 | L8 | | guardedSet L6 |
|---|---|---|---|---|---|
| **dickens** (text) | +5.5% | +4.6% | +3.4% | | +3.3% |
| **xml** (dense text) | +1.6% | +1.9% | +1.3% | | **−2.2%** |
| **webster** (text) | ~+2% | ~+1% | +3% | | +0.7% |
| **mozilla** (binary) | +2.1% | +0.5% | +1.0% | | +0.5% |
| **sao** (binary) | +2.4% | +1.7% | +3.4% | | +1.7% |

So the shipping version **must** thread the bounds hypotheses (like
`updateHashesFastU`'s `hhs`/`hht`/`hpv`) rather than use `guardedSet`. Geomean
across text+binary is ~+2 % with proven bounds; dickens (high match density) the
biggest at +3.4…+5.5 %.

## Correctness (`Zip/Spec/LZ77MergedCorrect.lean`)

Equality transfer: prove `lz77ChainLazyIterPMerged = lz77ChainLazyIterP` under the
invariant **`c = prev ++ hashTable`**, so the whole packed-token column
(`lz77ChainLazyIterP_eq`, `lzMatchP_map`, roundtrip) is reused through one
rewrite; `lzMatchP` dispatches to the merged matcher at levels 4+.

Proven and compiling: the 4 `Array` append helpers, `chainWalk_append` (the walk
reads only `[0, prevSize)` where `c` and `prev` agree), its lift
`chainWalkGuardedPackedU_append`, `updateHashesMerged_append` (insertion on
`prev ++ hashTable` = the append of the pair `lz77Chain.updateHashes` returns),
the `updateHashes` size-preservation lemmas, and the entry theorem
`lz77ChainLazyIterPMerged_eq` (reduced to the loop lemma).

**WIP — two items before this ships:**
1. `mergedLoop_eq` — the lockstep induction assembling the above through the
   branch tree — is a documented `sorry` as of this entry (the main-chain-walk
   alignment is proven-working; the remaining branch assembly + lazy-walk
   alignment is mechanical, per the inline strategy comment).
2. Switch `updateHashesMerged`'s inner loop from `guardedSet`/`headProbeGuarded`
   to proven-bounds `set`/`getElem` (thread `0 < hashSize`,
   `prevSize + hashSize ≤ c.size`, `min chainWinSize data.size ≤ prevSize` — the
   loop-carried invariant, established once at the entry from the `replicate`
   size, preserved by `guardedSet`). This is what makes the win uniform
   (removes the xml regression); the committed code currently uses `guardedSet`,
   so it matches the existing proof but is *not* the shipping perf shape. The
   append proof changes only `set!`↔`set` (equal in-bounds).

Until both land, the `lzMatchP` swap rests on a `sorry` and carries the xml
regression; do not merge as a shipping perf PR.

## Also measured

- Removing `@[inline]` from `updateHashesGuarded`: neutral speed, −6 % generated
  C, byte-identical — the dispatch (0.34 %) is not the cost. Not shipped.

## Verdict

The Prod is real but small; the *fusion* shape loses badly (linearity + stack),
while the *merge* shape wins +3–5 % byte-identically by removing the Prod at its
source (a single-array return) with zero hot-path overhead. Both attempts and the
#2749 persistent-pair reuse (−1.9 %) are recorded together in
`progress/rc-allocator-tax-2739.md`.
