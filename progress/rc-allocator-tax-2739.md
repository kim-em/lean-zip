# Progress: attribute and cut the RC/allocator tax (#2739)

**Date**: 2026-07-02 UTC
**Session type**: Feature
**Issue**: #2739

## Step 1: attribution (done)

DWARF unwinding does not work on leanc-built binaries (verified with a
controlled pair: the same test program unwinds fully when built with gcc,
drops all intermediate frames when built with leanc), so `perf record
--call-graph dwarf` yields self==children for every symbol. **Hardware branch
sampling** (`perf record -j any_call,u -e cycles:u`, Zen 5) works instead:
every sampled `call` into an allocator symbol names its caller exactly, no
unwinding involved. Steady-state `compress-pareto` runs on chungus.

### L1/dickens (tax = 9.3% `lean_dec_ref_cold` + 4.3% `mi_free` + 3.4% `mi_malloc_small` ≈ 17%)

Two shapes explain essentially all of it:

| shape | share of `mi_malloc_small` calls | matching frees |
|---|---|---|
| `BitWriter.flushAcc` builds a fresh writer per `writeBits`/`writeHuffCode` | 59% | `writeHuffCode`/`writeBits` dec_ref (~55%) |
| `updateHashesFastU` allocates the `(hashTable, prev)` result pair per match | 41% | `lz77ChainIterP.mainLoop` destructuring it (~40%) |

**#2631's share is ~zero**: `lean_copy_expand_array` (push-doubling reallocs)
got 2 branch samples out of 45k. The BitWriter *output buffer* doubling is not
where the tax is; that issue's win must come from wide stores.

### L8/xml (tax ≈ 14.6%, plus 14.3% `findTableCode.go` self time)

| caller of `mi_malloc_small` | share | note |
|---|---|---|
| `findTableCode.go` | 38% | boxed sizing/emit path: `findLengthCode`/`findDistCode` allocate `some (a,b,c)` per reference, freed in `tokenFreqs.go` / `emitTokensWithCodes`; also a **linear scan** (14.3% self) where the packed path uses O(1) `lenCodeWordTab` |
| `updateHashesFastU` | 23% | same pair churn as L1 |
| `BitWriter.flushAcc` | 19% | same writer churn as L1 |
| `List.setTR.go` | 8% | `computeCodeLengths`' `List.set` folds (2.29% self time) — superseded if #2737 lands |
| `ptokens.map unpackTok` | 6% | boxed token materialization for the split path (the "stage D" gap) |
| `chooseSplitsHeuristic` loop | 3% | `forIn` loop-state tuples |

## Step 2: fixes

1. **BitWriter ctor reuse** (landed): `flushAcc` split into `flushBytes`
   (byte pushes, returns only the `ByteArray`) + `dropBytes` (leftover
   accumulator); `writeBits`/`writeHuffCode` construct the result writer
   themselves, where reset/reuse fires (verified in IR: in-place `set`/`sset`
   on the unique path). Proof cost: `flushAcc_eq` + restated defining
   equations; 4 proof lines in `BitWriterCorrect` switched from
   `simp only [writeBits]` to `rw [writeBits_def]`.

2. **updateHashes pair threading** (measured-negative, retired): the packed
   matcher main loops threaded the chain state as one `(hashTable, prev)` pair
   (`updateHashesFastUSt`/`updateHashesGuardedSt`) so ctor reuse recycles a
   single pair cell instead of allocating one per match. Built, proven
   (lockstep `_eq` lemmas, `lake exe test` green), and verified in the
   generated C (`lean_is_exclusive` + in-place `lean_ctor_set` on the hot
   path) — but pinned interleaved A/B measured **−1.9% L1 / −1.2% L8** vs the
   BitWriter fix alone: the reuse turns one alloc+free *per match* into an
   `isShared` check + two cell stores *per position* (and per insertion in
   the walk), which costs more than it saves. Reverted; patch preserved in
   the session scratchpad. A cleaner kill would merge `hashTable`/`prev` into
   one array (no pair exists anywhere), but that refactors `chainWalkPacked`
   indexing + the whole LZ77Chain proof column for a bounded ~3–5% prize.

   **Follow-up (#2767, also measured-negative):** the *other* way to delete the
   pair — fuse the insert into the main loop so the two arrays thread as separate
   args (a mutually-recursive `loopP`/`insertP`) — is far worse: −24…−47% on
   dickens and a **stack overflow** on mozilla. Splitting the single
   self-tail-recursive loop into two functions (a) loses whole-function FBIP
   linearity (the tables reach the insert loop shared ⇒ copy-on-write, insert
   self-time 9.3%→28.5%) and (b) is not tail-call-optimized across the mutual
   boundary ⇒ per-position stack growth. Details:
   `progress/lazy-fuse-walk-insert-2767.md`. Both known pair-removals lose; the
   Prod stays.

3. **Not fixed here, attributed**: the L8 boxed-lookup churn (`findTableCode`)
   wants the split path moved onto packed words (stage D) — the sizing 2/3
   overlaps #2737's sizing-pass retirement; the emit 1/3 survives #2737 and
   remains available as a follow-up. `List.setTR` (#2737) and
   `chooseSplitsHeuristic` loop tuples (3%) also left.

## Measurements (compress-pareto, `taskset -c 43`, interleaved A/B)

| | L1/dickens | L8/xml | L6/dickens | L9/xml |
|---|---|---|---|---|
| baseline (f00d7cc7) | 51.6 MB/s | 21.1 MB/s | 24.5 | 2.93 |
| + BitWriter ctor reuse | **56.7 (+9.9%)** | **21.9 (+3.8%)** | 25.4 | 3.01 |
| + pair threading (retired) | 55.6 (−1.9%) | 21.8 (−1.2%) | 25.2 | 3.04 |

Output byte-identical in every cell (L1 out=4259646, L8 out=674362,
L6 out=3873339, L9 out=656466).

## Method notes for future perf sessions

- Pin benchmark runs to one core: `taskset -c 40 .lake/build/bin/bench …`.
- For caller attribution on this box use branch sampling, not DWARF:
  `perf record -j any_call,u -e cycles:u -F 1997 -o out.data <cmd>`, then
  `perf script -F brstacksym | tr ' ' '\n' | grep "/<symbol>" | awk -F/ '{print $1}' | sort | uniq -c | sort -rn`.
- Check ctor-reuse hypotheses in IR before trusting them:
  prepend `set_option trace.compiler.ir.result true` and look for
  `set`/`sset` + `isShared` instead of `ctor` on the hot path.
