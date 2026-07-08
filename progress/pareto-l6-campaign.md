# The miniz_oxide L6 campaign — five PRs, one target

**Goal (Kim's directive):** move the compress mixing frontier until miniz_oxide
L6 (weighted Silesia 0.3213 @ 35.5 MB/s) sits *inside* the native convex hull.
**Result: achieved** — the frontier at that ratio went 27.7 → 37.3 MB/s (+35%),
a −22% deficit turned into a **+5.1% margin**, and the native L6 point alone
(0.3205 @ 36.5) strictly dominates miniz L6 on both axes. miniz L7/L8/L9 and
zlib L7/L8 landed inside too (+30% to +71%).

## What landed (in merge order)

1. **#2821 — USize-native merged insertion loop.** The interior-hash insertion
   (13–25% of L4–L8 time) was still boxed-`Nat`; the `chainWalkPackedU`
   treatment applied to it. Byte-identical, proven (`updateHashesMergedFastU_eq`).
   Weighted Silesia L4–L8 +5–8%.
2. **#2823 — array-native two-queue Huffman tree build.** `limitedPairs` still
   built trees with `List.mergeSort` + O(n²) `insertByWeight` — the top profile
   entry (16.5%) on x-ray, whose stat-shifting rows make the splitter cut
   hundreds of blocks. Van Leeuwen two-queue over flat arrays; heuristic swap
   with property-based proofs (validity via `fixKraftList` is shape-only).
   x-ray L6 +21.6%, mozilla +9.6%; corpus ratio moved ≤ +0.0026%.
3. **#2822 — seed the lazy lookahead walk with the current match length**
   (zlib `prev_length`). Proven byte-identical (`chainWalk_seed`); +0.8–0.9% on
   match-dense text. Small, but its seeding lemmas are the machinery #2824 uses.
4. **#2824 — hash3-singleton length-3 coverage at the split tier (L6–L8).**
   The big one. Reopened #2742's plan item 1, rejected there on *unweighted
   geomean* — but the entire weighted deficit to miniz L6 sat on three
   hash4-blind binaries (x-ray/sao/ooffice, joined by an unheralded mozilla
   −340 KB). Certified spike first (`spike/h3-singleton-sweep`, pushed), then
   the production port reproduced the spike byte-for-byte on all 36 file×level
   rows. −0.28 pp corpus-weighted at each of L6/L7/L8; text pays single-digit
   speed, x-ray gets +34% *faster* (smaller token stream).
5. **#2825 — L6/L7 re-grid for the singleton cost structure.** 11-config
   gate-sweep (new `bench/gate-sweep` exe, committed): L6 → (chain 64, gate 64,
   probe /8, h3) = 0.3205 @ 36.5; L7 → the old L6 config (0.3196 @ 33.9,
   byte-identical point, keeps the vertex); L8 unchanged.

## Negative verdicts recorded this session

- **zstd-style accelerating skip through matchless runs** (`spike/runskip-sweep`,
  pushed, bench exe committed on the branch): best +1.0% (L6) / +1.3% (L7)
  corpus speed — far under the +4% bar — with the ratio cost concentrated on
  x-ray. Mechanism finding: on barely-compressible data our hash4 buckets are
  sparse, so the walks the skip would delete are already near-free; and sao
  never triggers the skip at all (constant spurious short matches reset the
  literal-run counter). A future attack on sao-like files needs a
  "matches-too-short-to-help" trigger, not a matchless-run trigger.
- **Intermediate lazy-gate values without the singleton** (gate-sweep round 1):
  gm64 ≈ free but ≈ no speed either; probe-depth cuts trade ~0.04 pp per +1.5%
  — the pre-singleton ladder was confirmed on its local frontier (consistent
  with the Wave-2e null result). It was the *singleton changing the cost
  structure* that made gate/depth cuts profitable at L6.

## Method notes for the next campaign

- The **weighted** (bytes/time) corpus aggregate is what the Pareto reads;
  unweighted geomean buried the singleton win once already (#2742) and diluted
  the Huffman win (x-ray +22% reads as +2% geomean). Check both.
- `bench/hull_check.py` (committed alongside this note) computes the mixing
  frontier from a bench-report JSON and prints the dominance verdict against
  every reference-codec point — the session's steering instrument.
- Profiles: matcher ~45–75% (walk + insert), and on stat-shifting binaries the
  per-block tree build was the sleeper. After this session's landings the L6
  profile is much flatter; the next big lever on record is #2782/#2783
  (cheap-optimal parse or true lazy2 cascade at L7/L8).
