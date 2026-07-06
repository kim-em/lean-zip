# Progress: fuse the lazy matcher's walk+insert step (#2767) — measured negative

**Date**: 2026-07-06 UTC
**Session type**: Feature (explore / measurement-first)
**Issue**: #2767
**Baseline**: ac14de13

## Summary

#2767 proposed deleting the per-matched-position `(hashTable, prev)` Prod that
`updateHashesFastU` returns by **fusing** the interior-hash insertion into the
lazy matcher's main loop so the two chain-state arrays never cross a helper
boundary as a pair. Two fusion shapes were on the table (the issue explicitly
ruled the #2749 *threaded persistent pair* variant out at −1.9%). This session
spiked the remaining shape — a step function that threads the two arrays as
**separate** arguments — measured it in situ, and it is a **clear negative**:
−24 % to −47 % on dickens and a **stack overflow** on mozilla. Reverted; no code
change ships. Root cause and numbers below so the shape stays retired.

## What was built (spike, reverted)

`lz77LazyLoopP` / `lz77LazyInsertP`: a mutually-recursive rewrite of
`lz77ChainLazyIterP.mainLoop` in which `lz77LazyInsertP` does the per-position
hash-chain insertion threading `hashTable`/`prev` as separate args and, when the
interior walk finishes, **tail-calls** `lz77LazyLoopP` with them still separate —
so no `lean_alloc_ctor`/`lean_ctor_get`/`lean_dec` on a Prod. Built with `partial`
(termination deferred) and sorried `set` bounds (production guards
`0 < hashSize`, `hashSize ≤ hashTable.size`, `min chainWinSize data.size ≤
prev.size` always hold ⇒ runtime byte-identical). Output was confirmed
byte-identical to `lz77ChainLazyIterP` at every level on both files
(dickens L4 out=3851998, L6 out=3847941, L8 out=3833946; mozilla L4 out=20356893).

Generated C confirmed the Prod **did** disappear: `lz77LazyInsertP`'s inner loop
is the same tight `lean_array_fset` + `goto _start` as `updateHashesFastU`, and
its base case tail-calls `lz77LazyLoopP` directly (no ctor).

## Measurement (native `deflateRaw`, MB/s, min-of-N, pinned via `bench/pin_core.sh`)

| file | L4 | L5 | L6 | L7 | L8 |
|---|---|---|---|---|---|
| **baseline** dickens | 31.3 | 26.5 | 26.2 | 21.9 | 21.0 |
| fused dickens | 20.2 | 21.0 | 13.7 | 12.5 | 12.3 |
| Δ | −35 % | −21 % | **−47 %** | −43 % | −41 % |
| **baseline** mozilla | 48.1 | 38.4 | 26.4 | 22.0 | 19.0 |
| fused mozilla | — **stack overflow** — | | | | |

## Why it loses (two independent causes, both fatal)

The single-loop `mainLoop` is one self-tail-recursive function; the fusion splits
it into two mutually-recursive functions. That split breaks two things the
compiler does for a *single* function:

1. **Refcount linearity is lost across the boundary.** In the shipped single loop
   the whole-function analysis keeps `hashTable`/`prev` at RC=1, so every
   `guardedSet`/`updateHashes` `set` mutates in place. Split across `loopP`↔
   `insertP`, borrow inference inserts conservative refcount traffic — the fused
   `loopP` gains a `lean_inc_n(prev, 2)` before the two chain walks that the
   single-loop form does not have — and profile self-time on the insert loop
   **tripled** (9.3 % → 28.5 %) with a byte-identical loop body. The added
   `inc`/`dec` traffic plus the extra call frames (defeating the C optimizer's
   whole-function context and register allocation) are enough to explain the
   regression; the tripling on an unchanged body is *consistent with* the tables
   reaching the insert loop shared and the in-place `set` degrading to
   copy-on-write on the 65536-/32768-entry arrays, though I did not capture a
   snapshot of the copy path firing to prove that specific mechanism. Either way
   the linearity the single loop preserves is gone.

2. **No tail-call optimization across the mutual boundary.** Lean turns a single
   self-tail-recursive function into a `goto _start` loop (constant stack). It
   does *not* fuse two mutually sibling-tail-calling functions into one loop, and
   leanc/the C compiler does not TCO the mutual `return f(...)` calls, so the
   stack grows one frame per position → **stack overflow on mozilla**. This is
   exactly the stack blow-up the iterative (`…Iter`) matchers were written to
   avoid; the fusion reintroduces it.

## Control (rules out a `partial def` artifact)

A `partial def` copy of the **unfused** single loop (`lz77LazyLoopPControl`,
still crosses `updateHashesGuarded`, still allocates the Prod) measured
**identical to baseline** (dickens L4 32.0 / L6 26.4 / L8 21.5). So `partial def`
does not itself disable FBIP here — the slowdown is genuinely the two-function
split, not the measurement scaffold.

## Also tried: `@[inline]` on `updateHashesGuarded` (neutral)

Removing `@[inline]` from `updateHashesGuarded` (out-of-lining the dispatch that
is otherwise duplicated at 4 call sites) shrank the generated Deflate.c by ~6 %
(16391 → 15473 lines) with **byte-identical output and no proof churn**
(`updateHashesGuarded_eq` uses `unfold`, attribute-independent), but compress
speed was **neutral** (dickens within ±1 %). The dispatch is not the cost:
`updateHashesGuarded`'s own self-time is 0.34 %. Not shipped — a code-size-only
change under a perf issue.

## Profile (mozilla, mixed L4–L8, `perf record -g`, self-time)

    34.5%  chainWalkPackedU          ← match finding (out of scope; #2765/#2774)
    10.0%  lz77ChainLazyIterP_mainLoop
     9.3%  updateHashesFastU         ← the Prod-bearing insert walk
     4.2%  Huffman insertByWeight
     4.1%  countMatch
     3.5%  lean_dec_ref_cold ; 1.0% mi_free ; 0.85% mi_malloc_small
     0.34% updateHashesGuarded       ← dispatch, negligible

The Prod is O(1) per matched position while the insert loop is O(matchLen), so it
is a small fraction of the 9.3 % — and it sits under `chainWalkPackedU` (34.5 %),
the real crown, which #2767 does not touch. This is consistent with the
rc-allocator-tax attribution (`progress/rc-allocator-tax-2739.md`): the Prod
churn was ~3–4 % of total, and *both* known ways to remove it lose — the #2749
persistent-pair reuse (−1.9 %: `isShared` + two cell stores per position) and now
this separate-args fusion (−47 % + stack overflow).

## Verdict

Retire the walk+insert fusion. The only shape that could preserve FBIP linearity
and stack safety is a **single** well-founded loop owning all state with an
explicit insertion-phase flag — a full rewrite of the matcher plus its entire
`LZ77PackedCorrect`/`LZ77ChainLazyCorrect` equality column, for the "bounded
~3–5 % prize" the rc-tax doc already judged not worth it, against a Prod that is a
minority of a 9.3 % function while the 34.5 % match-finding crown is elsewhere.
No code ships from #2767.
