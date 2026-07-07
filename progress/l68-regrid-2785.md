# L6–L8 ladder re-grid (#2785)

Re-baselined the L6–L8 tuning ladder (`chainDepth` / `niceLen` / `goodMatch`
and the block-split thresholds) after the native-Huffman-build (#2769),
cost-based-lazy-accept (#2776), half-depth-probe (#2774) and fused-split-pass
(#2762) landings shifted the per-file cost balance. Zero-proof-risk: every knob
is a search/emit heuristic re-verified at emission (`lz77ChainIter_resolves`
holds ∀ depth/cap), so no proof changed.

Harness: new `bench/l68-sweep` (committed). It models production exactly —
`lz77ChainLazyIterPMerged` with `lazyDepth = chain/2`, per-level size =
`deflateRaw`'s levels-6-8 base-vs-observation-split arbitration — cross-checked
against `(deflateRaw data level).size` for level ∈ {6,7,8} by `--verify` (✓ on
every file). Ratios are deterministic; speed from `--time` (pinned idle core,
3 config-interleaved reps) on dickens (10.2 MB text) + mozilla (51.2 MB binary),
the "dickens-vs-mozilla" text/binary pair. Ratio grids also over Canterbury
plrabn12 (text), kennedy.xls + ptt5 (binary).

## Outcome: one change adopted, three current settings re-confirmed

**Adopted — `chainDepth` L6 64 → 128** (drop the L6<L5 inversion).

Everything else stays: `niceLen` L8 = 258, `goodMatch` L5+ = 259, split floors
`minBlockBytes` 10000 / `softMaxBlockBytes` 300000 / `checkTokens` 512.

## 1. chainDepth: the L6=64 inversion no longer pays

`obs` = production per-level output size (base vs obs-split), `gm`=259, chain
sweep. Deeper chain is monotonically better ratio on every file; the split at
chain 64 no longer compensates for the shallower chain on text, so L6 (the
**default** level) was compressing *worse than L5*:

| file | L5 (128, single) | L6 cur (64+split) | L6 alt (128+split) | L6cur vs L5 |
|------|-----------------:|------------------:|-------------------:|------------:|
| dickens (text)   | 3 840 481 | 3 847 941 | 3 838 676 | **+0.194 %** (worse) |
| plrabn12 (text)  |   193 223 |   193 416 |   192 877 | **+0.100 %** (worse) |
| ptt5 (image)     |    55 097 |    55 195 |    55 097 | **+0.178 %** (worse) |
| kennedy (binary) |   218 565 |   202 676 |   201 371 | −7.27 % (split wins) |
| mozilla (binary) |20 209 289 |19 174 181 |19 147 804 | −5.12 % (split wins) |

Chain 128 restores L6 ≤ L5 output on every file. Speed (pinned, dickens+mozilla):

| L6 config | MB/s | output | Δ vs cur |
|-----------|-----:|-------:|---------:|
| 64 + split (cur)  | 25.08 | 23 022 122 | — |
| 128 + split (new) | 23.31 | 22 986 480 | **−7.1 % speed, +0.155 % ratio** |
| L7 256 + split    | 21.05 | 22 962 432 | (ladder neighbour) |

L6=128 stays clearly faster than L7 (23.3 vs 21.0 MB/s), so ladder ordering
holds. The 7% cost on the default level buys a monotonic ladder + ~0.15% ratio;
justified as a defect fix, not merely a Pareto tweak.

## 2. niceLen at L8: cutoff earns no speed (keep 258)

The issue asked whether a cutoff now earns its speed back (sweep 130/180/258).
It does not — the cutoff does not fire on dickens/mozilla, so it is speed-neutral
while only ever costing ratio:

| L8 niceLen | MB/s | output | note |
|-----------|-----:|-------:|------|
| 258 (cur) | 18.54 | 22 951 786 | — |
| 180 | 18.58 | 22 951 972 | +0.20% speed (noise), +0.001% ratio |
| 130 | 18.57 | 22 952 958 | +0.19% speed (noise), +0.005% ratio |

And on image-like data the cutoff costs real ratio — ptt5 @ chain 512:
nl258=53 091, nl180=53 121, nl130=53 360 (**+0.5%**), nl65=53 854 (+1.4%).
No speed to earn, only ratio to lose → **keep 258**.

## 3. goodMatch gate at L8: too much ratio for the speed (keep 259)

| L8 gate | MB/s | output | |
|---------|-----:|-------:|-|
| off, 259 (cur) | 18.54 | 22 951 786 | — |
| on, 8 | 21.31 | 23 043 788 | +14.9% speed but **+0.40% ratio** |

A bad trade at a ratio tier. (kennedy is the one file where gating helps ratio
slightly; mozilla loses 0.47%.) **Keep 259.**

## 4. Block-split thresholds: current values re-confirmed (keep 10000/300000/512)

Same grid optimum for L6, L7 and L8 — no per-level differentiation warranted.
`checkTokens` 512 is clearly best (256 → many tiny blocks, obs falls back to
base; 1024 ≈ 512). `softMaxBlockBytes` 300000 vs 600000 differ by < 0.01%.
`minBlockBytes` 5000 (libdeflate's floor) is the only real lever: it gains
~0.12% ratio on large binary (mozilla) but costs a consistent 2–3% speed across
all of L6-L8:

| level | minB 10k→5k speed | minB 10k→5k ratio |
|-------|------------------:|------------------:|
| L6 | −3.0% | −0.11% |
| L7 | −2.6% | −0.11% |
| L8 | −2.0% | −0.12% |

A blanket speed regression against the speed-ward direction of the recent
landings, for a small binary-only ratio gain. **Keep 10000.** Null result
recorded per the plan.

## Related: #2780 (hash3 singleton probe) premise is stale

While here, checked #2780 ("drop the hash3 singleton probe at L7/L8"). Its
premise does not hold against current code: `hash3Single`/`hash3Probe` are
consulted **only** in the L9/L10 candidate-cache DP build (`DeflateParse.lean`),
never in the L7/L8 lazy chain matcher (`Deflate.lean` docstring: "The L1–L8
chain matchers deliberately do not probe the singleton"). There is no hash3
consult to gate at L7/L8. #2780 needs re-scoping (or closing) before it can be
worked; not folded into this PR.
