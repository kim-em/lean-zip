# Five key commits in lean-zip's performance climb

The animated chart in the README is a compressed history. There are 77 raw
Silesia dashboard snapshots in the history of `bench/results/latest.json`, of
which 44 survive the animation's stale-branch and measurement-noise filters.
Across those displayed snapshots, lean-zip's level 1 moved from 18.77 MB/s at a
0.4059 compression ratio to 111.57 MB/s at 0.3614: 5.94 times faster while
producing output 11% smaller. Level 6 moved from 11.42 MB/s at 0.3785 to 39.46
MB/s at 0.3213: 3.45 times faster and 15% smaller.

No single trick did that. A useful way to tell the story is in two acts. First,
lean-zip learned to make better compression decisions, sometimes spending more
CPU to push the curve left. Then it recovered speed with increasingly surgical
optimizations that provably did not change the chosen output at all.

These are not simply the five largest vertical jumps in the graph. They are five
commits that combine real leverage, an explainable algorithm, interesting
provenance, and a visual idea that should work in a video.

One methodological warning: a dashboard frame is not always a controlled A/B.
Some refreshes collect several changes, Silesia timing is noisier than its
deterministic output sizes, and one squash below contains an unrelated bug fix.
The numbers here therefore prefer the paired measurements recorded in each PR
over naive subtraction of adjacent animation frames.

## 1. Look one byte ahead: lazy matching

**Commit:** [`19350797`](https://github.com/kim-em/lean-zip/commit/19350797c95dffb1b954aa6287211f6b526bfdd1),
[`feat: lazy LZ77 matching (distance-guarded) for levels ≥4`](https://github.com/kim-em/lean-zip/pull/2530)

A greedy LZ77 parser takes the best match beginning at the current byte. That is
locally sensible but can be globally shortsighted: a merely decent match now may
consume the beginning of a much better match one byte later.

Lazy matching asks one extra question before committing. After finding the best
match `M` at position `p`, it searches again at `p + 1`. If the new match `M'`
is better, the encoder emits the byte at `p` literally and then takes `M'`.
Spending one literal can unlock a much longer back-reference.

The broad idea is explicitly zlib's [`deflate_slow`](https://github.com/madler/zlib/blob/e3dc0a85b7032e98380dec011bc8f2c2ee0d8fca/deflate.c#L1956-L2067).
The interesting lean-zip wrinkle was the acceptance rule. A naive "take any
longer match" version made some Canterbury prose as much as 22% larger: the new
match was longer, but so much farther away that its extra distance bits cost more
than the additional length saved. The landed commit deferred only when `M'` was
both longer and no farther away. A later commit, `ac14de13`, refined this again
using libdeflate's explicit length-versus-distance cost formula.

On Silesia, the initial lazy parser reduced ratio by roughly 2.4% at levels 4-6
and 11.9% at levels 7-9. It was initially expensive: every promising position
could now pay for a second hash-chain walk, and the dense levels became much
slower. That apparent setback is part of the story. Lazy matching created new
high-quality territory on the left of the chart; later commits made that
territory fast.

The proof architecture made the experiment unusually safe. Match finding is
opaque to correctness. Whichever candidate the heuristic chooses, the matcher
must establish that it is a real in-window backward match before emitting it.
Changing the deferral predicate changes compression quality, not the statement
being proved. The implementation and discussion now live around
`lz77ChainLazy` in [`Zip/Native/Deflate.lean`](Zip/Native/Deflate.lean).

**Animation beat:** put a cursor over repeated text. Greedy grabs a short match
at `p`. Rewind, move one byte right, and reveal a much longer match at `p + 1`.
Replace the short match with one literal plus the long back-reference. Then move
the source of the long match farther away and let a small "distance bits" meter
show why longer is not automatically cheaper.

## 2. Cut blocks where the data changes character

**Commit:** [`35f28549`](https://github.com/kim-em/lean-zip/commit/35f28549f12bedae292d622f8afcdbbf1f5f2885),
[`feat: entropy-divergence block splitting for the shared-window splitter`](https://github.com/kim-em/lean-zip/pull/2532)

DEFLATE does not use one Huffman tree forever. It can begin a new block and fit a
new tree to a new symbol distribution. The question is where to cut.

The old lean-zip splitter cut at a fixed token cadence. That is simple, but real
files are not statistically uniform: prose turns into a table, XML markup turns
into values, an executable's code turns into embedded data. A tree fitted before
that transition becomes stale after it.

This commit walks the LZ77 token stream and maps every token into one of ten
coarse observation classes: eight cheap literal classes, plus short-match and
long-match classes. Every 512 tokens it compares the recent histogram with the
histogram for the block so far. When their distributions diverge sufficiently,
it starts a new DEFLATE block and builds a fresh Huffman tree. Crucially, the
32 KiB LZ history remains shared across the boundary, so the encoder gets a new
codebook without forgetting earlier bytes it can still reference.

This is the clearest provenance find in the sequence. The planning issue
originally proposed a zlib `_tr_flush_block`-style cost model, but the
implementation switched to libdeflate's cheaper observation heuristic. The PR
and source explicitly name libdeflate's
[`observe_literal`, `observe_match`, and `do_end_block_check`](https://github.com/ebiggers/libdeflate/blob/b122c8be1d78b19f6d0a6efc5bb79bfcbb30dd51/lib/deflate_compress.c#L2055-L2197).
lean-zip carries over the ten classes, the 512-observation window, the 10 KB
minimum, the 300 KB soft maximum, and the integer-only distribution test. The
corresponding code is documented under "Entropy-divergence boundary heuristic"
in [`Zip/Native/DeflateDynamic.lean`](Zip/Native/DeflateDynamic.lean).

lean-zip adds a useful safety valve for compression quality. It sizes the
heuristic partition and the old fixed-cadence partition in exact bits, then keeps
the smaller. At the next level out, `pickSmaller` still compares the split stream
with the single-block candidate.

The splitter helped heterogeneous files especially: the original work reported
18% smaller output on `kennedy.xls`, 12.5% on Silesia's `ooffice`, and 5.9% on
`mozilla`. On prose it narrowed the remaining level-9 gap to zlib by about a
third. The later [`be4eed6a`](https://github.com/kim-em/lean-zip/commit/be4eed6a102e07563e503be4819b2111988bb9e7)
commit moved the same idea onto packed tokens and deployed it across the
mid-level frontier.

There is an important archaeology caveat. `35f28549` also corrected two bugs in
the dynamic-Huffman length limiter. Those fixes dominate the enormous L1-L6
leftward jump in that animation frame. The block splitter itself mainly affected
the original L7-L9 split tiers. The frame is real, but attributing all of it to
entropy splitting would be wrong.

The proof story is almost as interesting as the heuristic. The cut-list emitter
clamps every proposed cut into a valid range, so its roundtrip theorem accepts an
arbitrary selector—including a bad, non-monotone, or out-of-range one. The
selector is therefore free to be an unproved performance heuristic. It may make
poor blocks, but it cannot make an invalid stream.

**Animation beat:** color the token stream by observation class. Above it, show
two ten-bin histograms labelled "block so far" and "recent window". As the file
changes regime, the histograms separate and a divergence gauge crosses its
threshold. Drop a block boundary, refresh the Huffman tree, but keep a translucent
32 KiB history ribbon flowing across the boundary.

## 3. Turn parsing into a shortest-path problem

**Commit:** [`356a21bf`](https://github.com/kim-em/lean-zip/commit/356a21bf3842f7baf743d2530f3d4db29a02ac18),
[`perf: near-optimal LZ parsing (cost-model DP) at level 9`](https://github.com/kim-em/lean-zip/pull/2534)

Greedy parsing sees one position. Lazy parsing sees two. Neither can reason about
a chain of choices: perhaps a shorter match here exposes a very cheap match
later, or perhaps two individually attractive matches use symbols that produce a
worse Huffman distribution for the block as a whole.

The near-optimal parser turns the input into a weighted directed graph. Every
byte position is a node. Emitting the next byte literally is an edge of length
one; every available back-reference is a longer edge that jumps over the bytes
it covers. The edge weight estimates the number of DEFLATE bits needed for its
literal or length/distance symbols and extra bits.

The implementation has four main pieces:

1. At every position, walk the match chain and cache a small Pareto set of useful
   `(length, distance)` candidates in fixed-stride flat arrays.
2. Build dense literal, length, and distance cost tables.
3. Work backward through a 256 KiB region, computing the cheapest cost-to-end
   from each position.
4. Walk forward along the chosen edges to produce tokens.

There are two optimization rounds. Round one seeds the costs with fixed-Huffman
code lengths. The resulting parse has a symbol histogram; round two fits dynamic
Huffman costs to that histogram and solves the graph again. This is explicitly
libdeflate-style and closely follows libdeflate's
[`deflate_find_min_cost_path` and iterative cost refitting](https://github.com/ebiggers/libdeflate/blob/b122c8be1d78b19f6d0a6efc5bb79bfcbb30dd51/lib/deflate_compress.c#L3313-L3502).
The Lean implementation is in [`Zip/Native/DeflateParse.lean`](Zip/Native/DeflateParse.lean).

The result moved the dense end of the graph substantially. Canterbury level 9
became about 4.6% smaller; Silesia became about 2.2% smaller even though four
large files were initially excluded by a memory gate. Native then beat both
zlib and libdeflate on Canterbury ratio. The cost was deliberate: level 9 took
roughly 2.2–2.8 times as long, making this a maximum-compression tier rather than
a free speedup.

This commit may offer the clearest explanation of what verification does and
does not need to prove. The dynamic program is not proved optimal. In fact, it
does not appear in the correctness proof at all. Its choice arrays are treated
as untrusted advice. Before emitting a chosen match, a forward pass reruns
`countMatch`, checks the distance and bounds, and falls back to a literal if the
advice is invalid. The theorem proves that arbitrary choices still produce a
valid parse; a benchmark and a ratio canary establish that these particular
choices are good.

**Animation beat:** transform a byte stream into nodes on a line. Draw short
literal edges and long match arcs, label them with bit costs, and illuminate the
minimum costs backward from the end. Then light the chosen path forward. Fade
that path into a symbol histogram, adjust the edge weights, and run the second
round. End by showing each chosen match pass through a small "reverified" gate
before emission.

## 4. Reject a hopeless match with one byte

**Commit:** [`7b2e1bec`](https://github.com/kim-em/lean-zip/commit/7b2e1becb7a9fcb6d18b942ab1c9963028a7fc71),
[`perf: match prefilter — skip countMatch for candidates that cannot beat best`](https://github.com/kim-em/lean-zip/pull/2618)

The first three commits improve decisions. This one notices how much time is
being spent evaluating candidates that cannot possibly change a decision.

Suppose the best match found so far has length `N`. A new candidate can improve
on it only if its first `N + 1` bytes match. Before comparing those bytes from
the beginning, inspect just the candidate's byte at offset `N`. If it differs
from the input's byte at offset `N`, the candidate's match length is at most
`N`; it cannot beat the incumbent, so the full comparison is wasted.

This is zlib's `scan_end` prefilter. Compare the explanation in lean-zip's
`chainWalkPacked` in [`Zip/Native/Deflate.lean`](Zip/Native/Deflate.lean) with
[zlib's early candidate rejection](https://github.com/madler/zlib/blob/e3dc0a85b7032e98380dec011bc8f2c2ee0d8fca/deflate.c#L1434-L1451).

The target mattered: `countMatch` accounted for roughly 65% of level-6
compression time, and collision-heavy hash chains contained many doomed
candidates. On Silesia the prefilter improved level 1 by about 10%, level 4 by
22%, level 6 by 26%, and level 8 by 16%. Output was byte-for-byte identical at
every level.

That identity is not merely an intuition. `countMatch_le_of_byte_ne` formalizes
the discriminator: if the bytes differ at offset `N`, the full match length
cannot exceed `N`. The optimized chain walk is then proved equal to the old
walk. This is a different verification pattern from the heuristic commits:
instead of proving that any choice is safe, prove that the optimization makes
exactly the same choice.

**Animation beat:** show a queue of hash-chain candidates entering an expensive
byte-by-byte comparison tunnel. Put a checkpoint at offset `bestLen`. Most
candidates fail that single-byte test, turn red, and disappear. Only the few
survivors enter the tunnel.

## 5. Compare eight bytes, then ask the CPU where they differ

**Commit:** [`95d13b87`](https://github.com/kim-em/lean-zip/commit/95d13b87b33086ad335bb2b77c6c3a84cb0c0aeb),
[`perf: word-at-a-time match extension in countMatch`](https://github.com/kim-em/lean-zip/pull/2746)

After the prefilter rejects hopeless candidates, the survivors still have to be
extended to find their exact match length. The straightforward loop compares one
byte per iteration. This commit compares eight.

Load eight bytes from each position as little-endian `UInt64` words. If the words
are equal, advance eight bytes immediately. If they differ, XOR them. Equal bits
become zero; the first differing bit becomes the least-significant set bit in the
XOR. Counting trailing zeros locates that bit, and shifting the count right by
three divides by eight:

```text
first differing byte = ctz(word1 XOR word2) >> 3
```

The technique comes directly from libdeflate's
[`lz_extend` in matchfinder_common.h`](https://github.com/ebiggers/libdeflate/blob/b122c8be1d78b19f6d0a6efc5bb79bfcbb30dd51/lib/matchfinder_common.h#L174-L221).
lean-zip's `goUW` implementation and its dispatch live in
[`Zip/Native/Deflate.lean`](Zip/Native/Deflate.lean).

There is a good failed-optimization story inside the commit. The first version
did the wide comparison but, on a mismatch, handed control back to the byte loop
at the beginning of the eight-byte window. Short matches are common, so it paid
for a 64-bit load and then rescanned the same bytes; both corpora regressed. The
XOR-plus-`ctz` revision removed the rescan and turned the change into a 4.9%
Silesia win. The output remained byte-identical.

Proving the bit trick correct required connecting machine-level and byte-level
views. `ugetUInt64LE_ctz_first_diff` proves that the computed index is below
eight, every earlier byte agrees, and the selected byte differs. `goUW_eq` then
proves that the word loop returns the same match length as the original byte
loop.

This commit is part of the underlying performance history but not one of the 44
retained README frames. Its dashboard movement was below the history renderer's
roughly 8% unchanged-ratio noise threshold. That makes it a weak choice for a
frame-by-frame narration but a particularly strong standalone explanatory
animation.

**Animation beat:** place two eight-byte strips side by side, pack each into a
64-bit word, and XOR them. Zoom into the resulting bit mask, highlight the lowest
`1`, count the zeros before it, then shift the count right by three and point
directly to the first mismatching byte. Emphasize that there is no second scan.

## The larger story

Together, these commits show three different ways a proof can support aggressive
optimization:

- **Keep correctness independent of the heuristic.** Lazy matching and block
  splitting can choose different valid parses or partitions without changing
  the roundtrip theorem.
- **Treat optimization as untrusted advice.** The near-optimal dynamic program
  can be tuned freely because every proposed match is reverified before it is
  emitted.
- **Prove an optimized kernel equal to a simple reference.** The `scan_end`
  prefilter and word-at-a-time comparator retain clean specifications while the
  production path becomes increasingly machine-shaped.

The provenance is part of the point too. These agents did not conjure every
compression technique from nowhere. They read mature implementations—zlib and
especially libdeflate--identified ideas that fit lean-zip's architecture, ported
them into Lean, measured them on real corpora, and then supplied the proof bridge
that lets the rest of the verified compressor trust the result.

That gives the video a natural arc: make a better local choice; notice when the
data distribution changes; optimize the whole parse; eliminate comparisons that
cannot matter; finally do eight remaining comparisons at once. The red curve's
movement is the accumulated result of all five.

## Archaeology note

The provenance above was checked against commit messages, PR descriptions,
issue descriptions and comments, benchmark comments, current source comments,
and the named upstream implementations. The relevant PRs have no submitted
GitHub reviews or inline review threads containing additional attribution; the
evidence lives in the PR/issue narrative and in the code itself.
