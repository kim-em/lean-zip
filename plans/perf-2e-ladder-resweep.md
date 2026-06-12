**Performance pivot Wave 2e — re-tune the level ladder for speed at iso-ratio. Knob sweep, no proof changes (`lz77ChainIter_resolves` holds for every depth/cap).**

### Current state

The `chainDepth`/`insertCap` ladder (`Zip/Native/DeflateDynamic.lean:~380-405`) was tuned while the dynamic-Huffman length-limiter was broken (fixed in D-20) and before lazy matching (#2530), entropy splitting (#2532), and the shared token pass landed — i.e., against a compressor whose ratio behavior differed substantially. The Wave-0 profile shows matcher time scaling steeply with depth (alice29 match: 4.7 ms at L1 → 23.4 at L6 → 30.4 at L9) while the marginal ratio gain saturates.

### Deliverables

1. Sweep `chainDepth` and `insertCap` per level over the committed Canterbury corpus (the #2529 sweep harness/methodology is the template — `ZipRatioSweep` / `lake exe ratio-sweep` exists), measuring ratio AND compress time per setting.
2. Adopt the fastest settings that hold ratio within ~0.1% of current at each level (levels 1–6 are the targets; 7–9 are dispatch-dominated). Document the sweep table in the PR.
3. Update the `chainDepth`/`insertCap` docstrings with the new rationale and re-bench (this one warrants a dashboard refresh since L1–6 numbers move).

### Context

Pure ratio/speed knob: the chain is a search heuristic, so any setting is correct (`lz77ChainIter_resolves` holds ∀ depth, cap — see D-15's Landed row). The win hypothesis: post-limiter-fix, shallower chains reach the same emitted size, recovering mid-level MB/s for free. If the sweep shows current settings are already optimal, record that result in track-d-state and close — a null result is acceptable.

### Verification

`lake build && lake exe test` green; sweep table in PR; refreshed `bench/results/latest.json` + graphs committed; no ratio regression > 0.1% at any level on the dashboard.
