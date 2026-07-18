# The bitter-end wave — L5 fix, emit micro, L1 endpoint, lazy2, #2782

Kim's directive: pull L5 back onto the curve, chase any L1 speed against the
extrapolated endpoint line, and take the remaining round-3 + #2782/#2783 items
"to the bitter end." Every item below is measured-first; four landed, five are
recorded negatives, one is scoped as a proof campaign.

## Landed

1. **#2835 — L5 re-grid.** L5 had become a dead vertex (15.6% inside the
   L4↔L6 blend after its neighbors improved). New L5 = light split tier
   (chain 24, gate 64, probe /4, no singleton): 0.3302 @ 46.4 → 0.3249 @ 46.2,
   −0.53pp at equal speed, +4.05% above the blend, a frontier vertex again.
2. **#2836 — fused huff+extra writer (+1.8–2.3%) and USize emit index.** The
   index conversion first measured a per-file WASH (+0.18% four-point geomean,
   floors ±0.3%) — then Kim's whole-tar instrument reversed it: on a single
   212 MB silesia.tar stream the paired A/B reads **+1.53%, 95% CI
   [+0.77%, +2.29%]**. Lesson: per-file harnesses under-resolve whole-stream
   effects; measure both before discarding sub-1% candidates.
3. **#2839 — sized floor at the optimal tiers.** L9/L10's `pickSmaller` fully
   emitted the always-discarded base candidate; the #2753 sized-prep now sizes
   it and forces only the winner. Byte-identical (verified INCLUDING ptt5 and
   kennedy.xls — see lesson below), L9 +1.7%, L10 +1.2%.

## Negative verdicts (all measured, all preserved)

- **L1 one-pass sampled-tree redesign** (`spike/l1-onepass`): −10% vs the
  extrapolated L2→L1 line — the prefix-sampled tree misfits mozilla (+9%
  ratio there) and a full freq pre-pass means matching twice (−67%).
- **L1 chunked-stored redesign** (same spike): improves weighted ratio below
  L1's (mozilla's incompressible stretches go stored) but lands −6.7% against
  L1↔L2 *blending*. With knobs, one-pass, and chunking all dead, the L1
  endpoint is confirmed near-optimal from three independent angles; endpoint
  progress is output-neutral structural speed only.
- **#2782 core hypothesis** (cheap-optimal parse as an L8 replacement):
  refuted — the optimal pipeline floors at ~7 MB/s even at cache chain 16,
  3.7× slower than L8. Chain-32/64 clear the L8↔L9 line but live just above
  L9, not at L8.
- **L9 depth-32 remap** (the tempting #2782 salvage): 0.3146 @ ~5.0 weighted
  — 3.6% BELOW the old L8↔L9 blend with the old point left uncovered by 3.4%.
  The spike's +8.8% margin belonged to the standalone parse without the
  pipeline's floor and emit. Rejected by the frontier test; postscript in
  `fastChainDepth`'s docstring.
- **Cheap-knobs floor matcher at L9/L10**: ~+7% on Silesia where the floor
  never wins — but the floor genuinely WINS on ptt5-class Canterbury bitmaps,
  and the weak floor cost ptt5 L9 +5.5% output. Wrong trade at the max-ratio
  tiers. **Two lessons:** (a) byte-identity spot checks must include the
  Canterbury floor-wins files, not just Silesia — the full matrix caught what
  the spot check missed; (b) never infer a component's speed-neutrality from
  cross-run full-matrix deltas — sandwich each component separately (the
  cheap floor initially read "neutral" from run-to-run noise and turned out
  to carry most of a +9% composite).
- **L4 re-position**: null. The ~2.7% sag (inherited when L3 and L5 improved
  around it) is real, but the best candidates (single c48-nl258, light-split
  c16) land exactly ON the L3↔L5 blend (+0.0%/+0.3%). L4 stays.

## Scoped for future sessions

- **#2837 — rolling lazy2 deferral at L7** (from #2783): Stage-1 certified
  +0.053pp weighted at ~+2.4% matcher — 5× more ratio-efficient than the
  ladder direction — but landing it re-threads the whole lazy proof tower
  with a variable-length-emission induction at four rungs. Proper
  multi-session campaign; spike preserved at `spike/…`/`perf/lazy2-deferral`.
