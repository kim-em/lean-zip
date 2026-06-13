**Wave 3 Step 0.3 (re-scoped after code reading) — reuse the winning partition's sized trees at emission.**

### Current state

At L≥7, `chooseSplitsArbitrated` (Zip/Native/DeflateDynamic.lean:649) sizes BOTH candidate partitions via `sharedPartitionBits` — per block: `tokenFreqs (toks.extract pos j)` + `dynamicCodeLengths` (a full Huffman build) + `writeDynamicHeader` into an empty writer. The winning cut list then goes to `emitSharedBlocksAt`, whose `emitSharedBlock` (:406) recomputes the same per-block freqs + trees + header a second time. The losing partition's sizing pass is inherent to arbitration; the winner's recompute is pure duplication (~one of three per-block tree passes at L7–8 ≈ 5–8% of L7 wall time on dickens).

### Deliverables

1. A tree-taking emitter variant (e.g. `emitSharedBlocksAtSized`) that consumes the per-block `(litLens, distLens)` (with their length invariants) computed during arbitration, plus a `chooseSplitsArbitratedSized` returning cuts together with the winner's sized trees. The existing cut-generic emitter stays as the reference; prove the sized variant equal to it (the trees passed in are definitionally `dynamicCodeLengths (tokenFreqs group)` for the same group — an rfl-or-near lemma per block).
2. Wire into `deflateRaw`'s L≥7 branch; byte-identical output (ratio canaries + the SizeHelpers conformance test for `sharedPartitionBits` must stay green).
3. Per-level timing before/after at L7/L8 on alice29 + dickens in the PR.

### Context

Wave 3 Step 0.3 of the performance pivot (plan of 2026-06-12). Spec impact: the `deflateDynamicBlocksSharedAt` quadruple in Zip/Spec/DeflateBlockSplit.lean unfolds the emitter — the sized variant needs either the equality-lemma route (preferred; statements untouched) or a parallel quadruple. Lessons in #2540's closing comments apply (no content-invariant lemmas; no fun_induction over heuristic defs).

### Verification

`lake build && lake exe test` green; 0 sorries; byte-identity canaries unchanged (alice29 52049/54744); timing table in PR; no dashboard refresh needed (iso-output).
