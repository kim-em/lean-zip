# Progress: Corpus-validated block-split knob defaults (#2529)

- **Date**: 2026-06-10 UTC
- **Session**: interactive (Kim + Claude), isolated worktree
- **Issue**: #2529

## Accomplished

Swept both `deflateRaw` block-split size knobs over Canterbury (11 files)
+ Silesia (12 files, ~202 MB) at levels 7–9 with a new compiled probe
(`lake exe ratio-sweep`, committed), and retuned the defaults:

- `sharedTokChunk`: 4096 → **8192**
- `splitChunkSize`: 32768 → **16384**

Headline: −0.188% corpus-total compressed size across levels 7–9
(−389 KB; ~−128–134 KB per level), with the same optimum at every level
— so single global defaults, **no level-dependence** (headroom of the
per-level optima over the best global pair was exactly 0 bytes).

## Method

Probe prints CSV sizes per (file, level) for: single-block base, the
self-contained split at chunk sizes {8192…131072}, the cross-block split
at token chunks {1024…32768} (one `lzMatch` pass per (file, level),
re-partitioned per candidate), and FFI zlib reference. 897 rows total.

Selection was **joint**, not independent per knob: `deflateRaw` emits
`min(base, sc(c), shared(t))`, and the full 30-cell Cartesian grid per
level showed the interaction matters — in isolation the self-contained
curve improves monotonically toward 131072, but jointly (with `shared`
already winning the large-text files) `sc = 16384` beats it. An
independent argmin would have picked the wrong value.

Optimum (16384, 8192) is interior to both grids (no endpoint extension
needed). Per-file regression policy (reject if any file regresses
> 0.5% **and** > 1 KiB vs the old defaults): 13 small regressions, all
≤ 180 bytes / ≤ 0.36% (Canterbury small files), summed ~660 bytes vs
~390 KB total win — passes.

Probe self-checks (always on unless `--fast`): the reused-token-pass
emission equals `deflateDynamicBlocksShared`, and min over the default
candidates equals `(deflateRaw …).size`. A post-change confirmation run
over Canterbury matched the sweep's predicted sizes in all 33 cells.

## Notes for #2528 (cost-model boundary heuristic)

- The fixed-cadence baseline the heuristic must beat is now
  (sc=16384, shared=8192) at 68,874,489 bytes corpus-total at level 9.
- The shared-knob curve is shallow around the optimum (8192 beat 16384
  by ~0.015% of corpus total), so the heuristic's win, if any, will come
  from *adaptive* boundaries, not from better fixed cadence.
- Sweep data: probe is committed; sizes are deterministic and
  reproducible via `bash bench/fetch_corpora.sh silesia` +
  `ls bench/corpora/{canterbury,silesia}/* | xargs -P 4 -n 1
  .lake/build/bin/ratio-sweep`.

## Not completed

Nothing outstanding; #2529 can close when the PR lands.
