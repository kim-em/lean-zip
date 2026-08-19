# Five key commits from the lean-zip performance climb

The README's animated Pareto chart replays 76 committed dashboard snapshots
(every commit touching `bench/results/latest.json`). Over that history, on the
Silesia corpus: L1 compression went from 18.8 to 111.6 MB/s (6x), L6 went from
11.4 to 39.5 MB/s while its ratio *improved* from 0.379 to 0.321, and the top
level's ratio went from 0.379 to 0.314. The five commits below were chosen from
that sequence for being algorithmically interesting, having traceable
provenance, or being the major levers; most are all three. Numbers are geomean
over the Silesia files unless noted.

A cross-cutting observation first, because it frames all five: the provenance
here is unusually well documented. Each port starts with a planning issue that
cites the C source of libdeflate or zlib by file and line number, then a
measurement-first spike, then keep-or-reject, with the rejections recorded
alongside the adoptions. It is not "inspired by libdeflate"; it is a selective,
receipted port, landed piece by piece into a codebase where every change had to
keep the roundtrip proofs green.

---

## 1. Lazy LZ77 matching, in three acts

**PR:** [feat: lazy LZ77 matching (distance-guarded) for levels ≥4 (#2530)](https://github.com/kim-em/lean-zip/pull/2530) (`19350797`)

The classic zlib `deflate_slow` idea from 1995: before committing to a match at
position p, peek at p+1; if a longer match starts there, emit one literal and
defer. In the dashboard data this is the biggest ratio-per-idea win in the
history: the frame after it lands shows L9's ratio falling from 0.3671 to
0.3234.

The story has three acts, and the middle one is the interesting part:

- **Act one: the textbook rule fails.** Naive zlib lazy (defer whenever the
  next match is longer) *regressed* large Canterbury text by up to +22%.
  Deferring trades a cheap close match for an expensive far one, and the extra
  distance bits outweigh the saved length.
- **Act two: a home-grown guard.** This PR's fix is a distance guard: defer
  only when the p+1 match is both longer **and no farther**. That keeps only
  the beneficial deferrals, worth −5.2% vs greedy across Canterbury levels
  4–9, 64 of 66 cells improved.
- **Act three: libdeflate's formula arrives.** Months later,
  [perf: cost-based lazy accept rule across the lazy tier (libdeflate) (#2776)](https://github.com/kim-em/lean-zip/pull/2776)
  replaces the guard with the real cost model (item 3 below).

Proof-wise, the trick that makes all the later matcher work cheap debuts here:
match-finding stays opaque to correctness. `chainWalk_spec` validates whatever
match the heuristic picks, and validity is re-established at emission, so
heuristic churn never touches the roundtrip theorems.

**Animation:** the canonical greedy-vs-lookahead scene. A greedy matcher grabs
`the cat` and misses the longer ` catalog` starting one byte later; replay
with the one-byte peek. Then act two animates itself: show a deferral that
swaps a distance-40 match for a distance-30000 match and *loses* bits, and
watch the distance guard reject it.

---

## 2. The 4-byte hash: the single biggest speed jump in the history

**PR:** [perf: 4-byte hash for the LZ77 chain matcher (W8) (#2620)](https://github.com/kim-em/lean-zip/pull/2620) (`5d772a0d`)

One commit: L6 compress went from 20.3 to 31.3 MB/s (+54%), the largest
single-frame speed jump in the 76 snapshots, and the ratio *improved* on text
at the same time. The PR calls it "a frontier push, not a move along the
speed/ratio curve."

The mechanism: zlib hashes 3 bytes into its chain buckets (its minimum match
length); libdeflate and zstd hash 4. The chain walk was 65% of L6 compress
time, and its cost is chain length. Hashing 4 bytes sends positions that share
only a 3-byte prefix to different buckets, so chains are dramatically shorter
and the candidates that survive are higher quality (4-gram matches that hit
the early-exit sooner). Measured on 2 MB Silesia slices: text L6 +58% speed at
better ratio, text L6 throughput 13.5 to 21.3 MB/s.

The sequel is the best single provenance document in the repo:
[perf: dual hash4+hash3 match finder (#2742)](https://github.com/kim-em/lean-zip/issues/2742)
walks through libdeflate's `hc_matchfinder.h:112-333` design in detail. Plain
hash4 was known to be blocked at the top levels (+7.4% ratio on x-ray, because
length-3 matches become unfindable), and libdeflate's answer is two tables
split by role: hash4 owns the chains, while a *singleton* hash3 table (one
most-recent position per bucket, no chain, consulted only while the best match
so far is shorter than 4) keeps length-3 matches reachable. That port landed
as [#2759](https://github.com/kim-em/lean-zip/pull/2759) and
[#2824](https://github.com/kim-em/lean-zip/pull/2824).

Proof cost of the original change: zero. All three `hash3` copies changed
identically, and every proof uses the hash only as an opaque `< hashSize`
index.

**Animation:** show the hash bucket for `the` as one enormous chain the
matcher must walk candidate by candidate, then re-hash with 4 bytes and watch
the bucket shatter into short, high-quality chains. The dual-table sequel adds
a second scene: the lone hash3 slot catching the length-3 match the chains can
no longer see.

---

## 3. libdeflate's cost-based accept rule: a formula, lifted with receipts

**PR:** [perf: cost-based lazy accept rule across the lazy tier (libdeflate) (#2776)](https://github.com/kim-em/lean-zip/pull/2776) (`ac14de13`)

The cleanest "we took that from libdeflate" artifact in the project. The
distance guard from act two of item 1 rejected every longer-but-farther match
outright. libdeflate instead asks whether the length gain pays for the extra
offset bits:

    4·Δlen + bsr(dist1) − bsr(dist2) > 2        (bsr x = ⌊log2 x⌋)

The planning issue
[perf(explore): lazy2 lookahead + cost-based accept rule at L7/L8 (#2765)](https://github.com/kim-em/lean-zip/issues/2765)
cites the source exactly: `deflate_compress.c:2738-2767`, including the second
threshold (`> 6`) for libdeflate's two-position lookahead. The formula lives at
`Zip/Native/Deflate.lean:1358` with the citation in its docstring.

Measured: −0.4% to −0.9% ratio at every lazy level (4–9) on every file, text
and binary alike, no regression anywhere, at neutral speed. Equally telling is
what was *rejected* in the same investigation: the two-position `pos+2`
lookahead was spiked, measured at ≤0.06% extra ratio, and dropped as not worth
a second chain walk plus a proof branch.

Two siblings share the provenance and complete the arc from item 1:
[perf: half-depth lazy lookahead probe (libdeflate) (#2774)](https://github.com/kim-em/lean-zip/pull/2774)
(probe the lookahead at half chain depth, libdeflate's value) and
[perf: lazy-match gating (zlib good_match) (#2619)](https://github.com/kim-em/lean-zip/pull/2619)
(skip the lookahead entirely once the first match is long, zlib's mechanism).

This PR is also where the before/after Pareto graph comments begin appearing on
perf PRs; its thread has a zoomed mid-band view captioned "native now lands in
the Rust/zlib cluster." Those committed graph images are drop-in video assets.

**Animation:** two candidate matches, one longer but far, one shorter but
near. Draw the actual bits each would cost (length code + distance code +
extra distance bits), and let the formula pick the cheaper. Contrast with the
old guard, which rejects the far match without looking.

---

## 4. Near-optimal parsing: a shortest-path problem, and the ratio crown

**PR:** [perf: near-optimal LZ parsing (cost-model DP) at level 9 (#2534)](https://github.com/kim-em/lean-zip/pull/2534) (`356a21bf`)

The deepest algorithm in the codebase. Greedy and lazy parsing choose matches
locally; the last few percent of ratio comes from choosing the *globally*
cheapest sequence of literals and matches under the actual Huffman bit costs.
The planning issue is literally titled
[perf: near-optimal LZ parsing (cost-model DP) — the libdeflate/zopfli ratio ceiling (#2496)](https://github.com/kim-em/lean-zip/issues/2496).

The structure: a per-position candidate cache (each position's matches as a
strictly-increasing-length, nearest-first Pareto frontier), dense bit-cost
tables, and a backward DP over 256 KiB regions:

    cost[i] = min( litCost(i) + cost[i+1],
                   min over matches (len,dist) at i of
                       matchCost(len,dist) + cost[i+len] )

with the elegant fixpoint refinement on top: parse once with static
fixed-Huffman seed costs, refit the cost tables to the parse's own histogram,
parse again. The PR is precise about the lineage: candidates are evaluated at
length-code boundaries to capture trim-to-cheaper-code wins "without zopfli's
full per-length enumeration," and the cost is "libdeflate-shaped, not zopfli's
50–100x."

The verification split is stated with unusual honesty: *validity* is proven
(the emitter re-verifies every DP choice with a fresh `countMatch` and falls
back to a literal, so the proofs hold for arbitrary choice arrays), while
*optimality* is measured, not proven, and enforced by a ratio canary test.

Result at landing: Canterbury L9 ratio 0.2989 to 0.2852, ahead of **both**
zlib (0.2966) and libdeflate itself (0.2904). The dashboard's L9 line then
tells a 10x recovery story: the DP started at 0.44 MB/s, and the candidate
cache work (dual-hash finder, libdeflate's `bt_matchfinder_skip_byte`
skip-ahead, match-interior skipping) brought it to 4.6 MB/s at the same ratio.

**Animation:** the showpiece. Positions as nodes, literals and matches as
edges weighted by bit cost; run the backward DP and light up the cheapest
path. Then re-weight the edges from the parse's own statistics and watch the
path shift. A second scene can show why greedy loses: taking the long match
now blocks a much better match two bytes later.

---

## 5. Entropy-divergence block splitting: the biggest ratio lever, with a hidden bug story

**PR:** [feat: entropy-divergence block splitting for the shared-window splitter (#2532)](https://github.com/kim-em/lean-zip/pull/2532) (`35f28549`)

The largest single ratio move in all 76 frames: L6 output shrank 8.7%, L1
shrank 11.5%, in one refresh; 98 native dashboard rows improved and none
regressed.

DEFLATE lets a stream start a fresh Huffman table at any block boundary. A
fixed block cadence cuts mid-run and re-cuts where the old tree was still
fine; the right cut points are where the *symbol statistics shift*. The
parentage is mixed and documented on both sides: the motivating issue
[feat: cost-model boundary heuristic for block splitting (#2528)](https://github.com/kim-em/lean-zip/issues/2528)
credits the idea to zlib's `_tr_flush_block` (end a block when the accumulated
entropy diverges from what the current trees predict), while the mechanism is
libdeflate's observation machinery, ported with its constants: 10 coarse
symbol classes (8 literal classes from bits 7,6,0 plus short/long match), a
divergence check every 512 symbols, cutoff 200/512, minimum block 5000 bytes,
soft maximum 300000. The follow-up
[perf: observation-divergence block splitting at L4-L8 (#2737)](https://github.com/kim-em/lean-zip/issues/2737)
quotes `deflate_compress.c:2055-2217` directly; the constants live at
`Zip/Native/DeflateDynamic.lean:1184` with the citations.

The proof design is the reason this was cheap to land: the block emitter
clamps every cut to a valid range, so *any* selector, however wrong, yields a
valid partition, and the roundtrip theorems quantify over arbitrary cut lists.
The heuristic carries zero proof obligations, and an exact-bit arbitration
keeps whichever of heuristic and fixed cadence sizes smaller, so it can never
regress.

The hidden story: the PR's new heterogeneous-input test exposed a pre-existing
bug in the Huffman length-limiter's Kraft repair. It was producing *incomplete*
codes that lean-zip's own verified decoders tolerated but zlib's stricter
inflate rejected: output that was provably roundtrip-correct and still
zlib-undecodable. The fix (drive the repair by the exact Kraft excess) was
worth −19% on dickens at the default level by itself. A sharp example of what
conformance testing against a foreign implementation adds beyond verification:
the proofs guarantee *we* can decode our output, not that everyone else will.

**Animation:** a file that changes character mid-stream (English prose, then
tables of digits). Two histograms drift apart as the scan proceeds; when the
divergence crosses the threshold, a cut appears and a fresh Huffman tree
starts, and the compressed size counter drops. The bug story animates too: a
Huffman tree with a dangling unused branch, accepted by one decoder, rejected
by the other.

---

## Runners-up

- [perf: match prefilter — skip countMatch for candidates that cannot beat best (#2618)](https://github.com/kim-em/lean-zip/pull/2618):
  zlib's `scan_end` trick; check one discriminating byte to prove a candidate
  cannot win before running the full compare. +26% at L6, byte-identical
  output, *proven* output-preserving via the contrapositive of
  `countMatch_matches`.
- [perf: word-at-a-time match extension in countMatch (#2746)](https://github.com/kim-em/lean-zip/pull/2746):
  compare 8 bytes per iteration; the word-to-byte equality step is discharged
  by `bv_decide`. Verified bit-twiddling.
- [perf(decode): ship the verified tree-free decoder as Inflate.inflate (#2685)](https://github.com/kim-em/lean-zip/pull/2685):
  the best pure-verification story. Moving to libdeflate-style table decoding
  exposed an accept-set gap (the fast path skipped Kraft validation, accepting
  malformed streams the reference rejects), and the equivalence proof forced
  it closed. The proof caught a security bug in the optimization.
- [perf: array-native two-queue Huffman tree build (#2823)](https://github.com/kim-em/lean-zip/pull/2823):
  the van Leeuwen two-queue O(n) Huffman construction; a pretty classical
  algorithm if the video wants a pure-algorithm interlude.
- The de-boxing arc (Waves 5–7, e.g.
  [bench: Wave-7 dashboard refresh (P1a USize countMatch landed) (#2617)](https://github.com/kim-em/lean-zip/pull/2617)):
  L1 roughly doubled (20 to 41 MB/s) by moving hot loops from boxed
  `Nat`/`Prod`/`Option` onto `USize` and packed scalar arrays. Not an
  algorithm, but the distinctly *Lean* chapter of the story: if the video's
  thesis is "verified code can be fast," this is the language-level half of
  the argument.
