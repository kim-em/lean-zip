**Performance pivot Wave 2d — bounds-check and `Option`-free hot loops in the matcher. Iso-ratio by construction (heuristic-only code paths).**

### Current state

The Wave-0 profile (see *Wave-0 phase profile* in `plans/track-d-state.md`) shows the matcher is 83–84% of the base candidate at L6 (dickens: 1733 of 2064 ms), and D-15 measured ~70% of matcher time in hash-chain maintenance. The hot loops use `[..]!` panic-checked indexing and `Array Nat` element traffic throughout: `lz77Greedy.countMatch`/`go`, `lz77Chain.chainWalk`, `lz77Chain.updateHashes`, the lazy-matcher loops, and the optimal parser's `chainWalkAll`/`buildCache` (`Zip/Native/Deflate.lean`, `Zip/Native/DeflateParse.lean`). A previous measurement put `uget`-style unchecked access at ≈1.1×, untuned.

### Deliverables

1. Convert `]!` to proven-bounds `]` access where a bound is already in scope (the `proven-bounds` skill documents the pattern: capture the guard, omega, propagate to callers), and to `uget`/`uset`-style unchecked access for the heuristic arrays whose contents never enter proofs (hash table, prev chain, candidate cache) where a proof-free bound is awkward.
2. Per-function before/after timing on alice29 + dickens at L1/L6/L9 in the PR description (an uncommitted driver is fine; the Wave-0 methodology notes in `track-d-state.md` apply).
3. No output change: all roundtrip/conformance tests and ratio canaries pass untouched; the chain state remains outside all proofs.

### Context

This is the mechanical on-ramp to the Wave-3 matcher-state representation change (packed unboxed chain state); landing it first isolates the bounds-check win from the representation win so both are measured honestly. Scope guard: do NOT change array element types or data layout in this issue — that is Wave 3a, planner-reserved.

### Verification

`lake build && lake exe test` green; 0 sorries; per-function timing table in the PR; dashboard refresh not required (no ratio change; full re-bench happens once per wave).
