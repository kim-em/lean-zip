# Why Lean is faster than Rust, part 2: what the agents actually did

In [the last post](blog.md), I showed you an animated graph. The red
`lean-zip` curve moved up and to the left through the optimization history,
until it dominated the green `miniz_oxide` curve at levels 6 through 9.

"The AIs optimized it" is not much of an explanation. So what did they
actually do?

There was no single trick. On the Silesia corpus, level 1 went from 18.8 to
111.6 MB/s. Level 6 went from 11.4 to 39.5 MB/s, while its compression ratio
improved from 0.379 to 0.321. That is the accumulated result of dozens of
changes, including plenty which were too small to see in the animation.

The history does have a useful shape. First, the compressor learned to make
better decisions, which generally moved the graph to the left and sometimes
made it slower. Then a long sequence of changes made those decisions cheaper,
which moved the graph back up.

To follow the interesting parts, you only need a small amount of DEFLATE.
Repeated bytes can be replaced by a reference which says "go backward this
distance and copy this many bytes". Bytes which are not part of a useful match
are emitted as literals. DEFLATE then Huffman-codes the resulting stream, giving
frequent symbols shorter codes, and it may start a fresh Huffman code at a block
boundary.

```text
input bytes
    |
    v
find possible matches --> choose literals and references --> cut into blocks
                                                              |
                                                              v
                                                        Huffman-code them
```

That gives us three questions. Where are the matches? Which matches should we
take? Where should we cut the blocks?

The agents changed all three.

## One byte ahead

A greedy LZ77 parser takes the best match at the current position. That sounds
reasonable, but it can consume the first byte of a much better match which
starts one position later.

```text
past window:    ... abc ... bcdefghijk ...

current input:      a b c d e f g h i j k
                    [-----]                 match now:   length 3
                      [-----------------]   one byte on: length 10

greedy:           [ reference 3 ] [ ... ]
one-byte lazy:    [ literal "a" ] [       reference 10       ]
```

[Commit `19350797`](https://github.com/kim-em/lean-zip/commit/19350797c95dffb1b954aa6287211f6b526bfdd1)
added this one-byte lookahead, following the broad shape of zlib's
[`deflate_slow`](https://github.com/madler/zlib/blob/e3dc0a85b7032e98380dec011bc8f2c2ee0d8fca/deflate.c#L1950-L2067).
Before committing to the match at `p`, search again at `p + 1`. If the later
match is better, emit one literal and defer to it.

The first acceptance rule was obvious: if the later match is longer, take it.
It was also wrong.

A DEFLATE reference has a length and a distance. Longer references are usually
good, but farther references require more distance bits. The naive rule could
discard a cheap nearby match for one which was only slightly longer and much
farther away. Some large text files became substantially larger.

The version which landed therefore had two gates:

```text
match at p + 1
     |
     +--> is it longer? -------- no --> keep the match at p
     |          |
     |         yes
     |          v
     +--> is it no farther? ---- no --> keep the match at p
                |
               yes
                v
        emit one literal and defer
```

This episode captures one of the most useful patterns in the history. The agent
did not merely port a textbook idea. It implemented the obvious rule, measured
a bad result, worked out why it was bad, changed the rule, and measured again.

Four weeks later,
[commit `ac14de13`](https://github.com/kim-em/lean-zip/commit/ac14de13e4bf6f35338f6c374fc9b1a9279a8cd6)
replaced the conservative "no farther" gate with an adaptation of
[libdeflate's cost rule](https://github.com/ebiggers/libdeflate/blob/b122c8be1d78b19f6d0a6efc5bb79bfcbb30dd51/lib/deflate_compress.c#L2722-L2735).
The relevant part of the C asks whether the extra length is worth the change in
distance cost:

```c
if (next_len >= cur_len &&
    4 * (int)(next_len - cur_len) +
    ((int)bsr32(cur_offset) -
     (int)bsr32(next_offset)) > 2) {
```

The Lean version expresses the same idea without being a transliteration:

```lean
@[inline] def lazyAcceptCost (len1 dist1 len2 dist2 : Nat) : Bool :=
  decide (len1 < len2) &&
    decide (4 * (len2 - len1) + dist1.log2 > 2 + dist2.log2)
```

The inequality has been rearranged for `Nat`, where subtraction truncates at
zero. The strict length check is stated separately. On the paired 105 MB
Silesia subset, this made levels 4 through 9 another 0.4% to 0.9% smaller at
essentially neutral speed. A second lookahead position was also implemented and
rejected because its small ratio gain did not justify another chain search and
another proof branch.

What did all this churn cost in proof work? Very little, by design.

The search validates each candidate with `countMatch` before the accept rule
sees it. The rule may choose poorly, but it only chooses between matches which
`chainWalk` has already established. The proof needs the small fact that an
accepted lookahead is strictly longer; the distance-cost inequality itself is
opaque. The benchmark decides whether that inequality is good.

One byte of foresight helped. It was still only one byte.

## Cut when the statistics change

DEFLATE can give each block a different Huffman code. This matters when a file
changes character. A code fitted to prose is unlikely to be a good code for the
table of numbers which follows it.

An earlier
[self-contained splitter](https://github.com/kim-em/lean-zip/commit/c1378a8aa5c71c0a296d35c7d836df1641f2cf51)
started a fresh match window in every block. The major shared-window change was
[commit `437e77cc`](https://github.com/kim-em/lean-zip/commit/437e77cc4ed104b6a572f8da6ccecc720366a297).
`lean-zip` would match the input once, keep the 32 KiB LZ77 history continuous,
and divide the token stream into separate blocks with separate Huffman codes.

```text
one continuous LZ77 history
<-------------------------------------------------------------->

tokens:  [ prose prose prose prose | digits digits digits digits ]
          <---- block A ----->   <------- block B ------------->
             Huffman tree A          Huffman tree B

back-reference:             <--------------------
                            may cross the block boundary
```

The distinction is important. Starting a new Huffman block does not mean
forgetting the previous bytes. References may still cross the boundary. On the
large Silesia text files at level 9, this fixed-cadence shared-window split cut
output by roughly 15% to 20%. It was one of the largest ratio levers in the
history.

The fixed cadence was statistically blind, though. The first version cut every
4,096 tokens. That number was soon tuned, but any fixed cadence has the same
problem: it cuts whether or not anything has changed there.

[Commit `35f28549`](https://github.com/kim-em/lean-zip/commit/35f28549f12bedae292d622f8afcdbbf1f5f2885)
added an observation-based partition as an alternative to that cadence, using an
[observation scheme adapted from libdeflate](https://github.com/ebiggers/libdeflate/blob/b122c8be1d78b19f6d0a6efc5bb79bfcbb30dd51/lib/deflate_compress.c#L2055-L2217).
It maintains two coarse, ten-bin histograms: one for the block so far and one
for each new observation batch, normally 512 tokens. When their distributions
diverge enough, the splitter proposes a boundary after that sampled batch and
starts a fresh Huffman code.

```text
tokens:    prose prose prose prose | digits digits digits digits
                                     ^

block so far:  [1 4 8 7 3 1 1 2 1 0]
recent batch:  [1 4 7 6 3 1 1 2 1 0]   distributions still agree

block so far:  [1 4 8 7 3 1 1 2 1 0]
recent batch:  [0 0 1 1 7 8 6 5 0 0]   distributions diverged: propose cut
```

The diagram puts the cut at the visible change for clarity. The implementation
checks non-overlapping observation batches and cuts after the batch which
detected the shift, not at the exact transition byte.

The ten bins are intentionally cheap. Literals are placed into eight broad
classes using three bits of the byte, while matches go into short and long
classes. This is not an attempt to predict the exact Huffman tree. It is enough
to notice that the token population has changed.

There was a second safety valve in that commit. The emitter sized the
observation-based partition and the old fixed-cadence partition in exact bits,
then kept the smaller one. This cost model was designed and conformance-tested
not to lose to the old cadence inside that arbitration. The roundtrip proof made
a different statement: the selector could be arbitrary because the emitter
clamped every proposed cut into a valid range. Later dispatch work removed the
fixed-cadence candidate, but this was the comparison which landed with the new
heuristic.

The measured story needs one careful qualification. Observation-based splitting
was a modest extra improvement on Silesia at level 9. It was gated off at levels
1 through 6, so all movement there came from a different fix bundled into the
same pull request. The level-7 through level-9 frame also included the limiter
fix and an unisolated chunk-tuning baseline.

That fix is my favourite bug in the project.

The new heterogeneous-input test produced output which `lean-zip`'s verified
reference decoder accepted and zlib rejected. The previous day's
[length redistribution](https://github.com/kim-em/lean-zip/commit/aa23f0c7e436689c39e18a02fa7e84185b12919c),
adapted from zlib's
[`gen_bitlen`](https://github.com/madler/zlib/blob/e3dc0a85b7032e98380dec011bc8f2c2ee0d8fca/trees.c#L540-L613),
had introduced an error in the generic Huffman length limiter. It could drop
leaves while repairing the histogram for DEFLATE's 19-symbol code-length
alphabet. The result was an incomplete code-length alphabet. Our decoder
accepted that shape. zlib reported `invalid code lengths set`.

```text
                         +--> inflateReference --> original bytes  [proved]
compressed byte stream --+
                         +--> zlib inflate ------> REJECTED        [test failed]
```

The roundtrip theorem was not wrong. It was precise:

```lean
inflateReference (deflateRaw data level) maxOutputSize = .ok data
```

It says that `inflateReference` can decode the stream. It does not say that
the code-length alphabet is complete, which zlib requires for this table.
Targeted conformance tests, and the current encoder fuzz test, therefore
decompress through zlib. Proofs cover the statement which was proved.
Cross-implementation conformance tests cover a different boundary.

The test also exposed a property worth proving. Three days later,
[commit `d2991121`](https://github.com/kim-em/lean-zip/commit/d29911215d5fa467d0e2ccd6820cc3e74c83ab9e)
added `computeCodeLengths_complete`, which proves exact Kraft equality for the
multi-symbol path. The missing conformance property became part of the formal
specification.

The repair drove the length histogram by its exact Kraft excess and updated it
sequentially, so leaves could no longer disappear through stale array updates.
On `dickens`, a Silesia file, the level-6 output became 19% smaller. That is a
clean view of the limiter fix because the observation splitter was gated to the
higher levels there.

## The whole future

Greedy parsing sees one position. Lazy parsing sees two. Neither can reason
about a long chain of choices.

[Commit `356a21bf`](https://github.com/kim-em/lean-zip/commit/356a21bf3842f7baf743d2530f3d4db29a02ac18)
turned the parse into a shortest-path problem. Put a node at every byte
position. A literal is an edge to the next node. Every available match is an
edge which jumps over the bytes it covers. Label each edge with the estimated
number of bits it will cost.

```text
                         match: 9 bits              match: 12 bits
                    +------------------> 4 ----------------------> 8
                   /
position:         0 -- literal: 8 bits --> 1 --------------------> 8
                                               match: 10 bits

route through 4:  0 --> 4 --> 8      total 21 bits
route through 1:  0 --> 1 --> 8      total 18 bits
```

The recurrence is simple. Start at the end, where the remaining cost is zero,
and work backward:

```text
cost[i] = min(
  literalCost(i) + cost[i + 1],
  matchCost(length, distance) + cost[i + length]  for every cached match
)
```

At each position, record the cheapest outgoing edge. A final forward walk
follows those choices and emits the parse.

There is a circularity hiding in the edge weights. A symbol's cost depends on
its Huffman code. The Huffman code depends on the symbol frequencies. The
frequencies depend on the parse which we have not chosen yet.

Following the
[general shape of libdeflate's near-optimal parser](https://github.com/ebiggers/libdeflate/blob/b122c8be1d78b19f6d0a6efc5bb79bfcbb30dd51/lib/deflate_compress.c#L3313-L3502),
`lean-zip` solves twice:

```text
fixed-Huffman seed costs
          |
          v
  cheapest path, round 1 --> symbol histogram --> fitted costs
                                                       |
                                                       v
                                              cheapest path, round 2
```

This is an adaptation, not line-for-line code. The Lean version uses cached
candidate frontiers, considers useful length-code boundaries, works in bounded
regions with a tail estimate, and performs exactly two rounds. Within each
round, the estimated costs are fixed while the dynamic program runs.

The name "near-optimal" matters. The algorithm finds a minimum through the
cached candidates under the estimated costs. It does not enumerate every
possible DEFLATE stream, and there is no theorem claiming that it found the
global optimum.

In fact, the correctness theorem does not trust the dynamic program at all.
Its result is a pair of arrays proposing lengths and distances. The emitter
checks each proposal against the input again. If the proposed source bytes do
not match, it emits a literal instead.

```text
DP choice arrays --> UNTRUSTED ADVICE --> check bounds and bytes
                                                 |
                              valid -------------+------------- invalid
                                |                                  |
                                v                                  v
                         emit reference                       emit literal
```

The theorem is stated for arbitrary choice arrays. The dynamic program may be
suboptimal. It may even return nonsense. It cannot make the encoder lie about
the input.

At landing, Silesia level 9 became another 2.2% smaller, with compression taking
2.2 to 2.8 times as long. This was a maximum-compression tier, not a free
improvement.

Now the agents had to make all of that machinery fast.

## Getting the speed back

The high-compression path did not stay that slow. Its per-position candidate
cache landed with the dynamic program; later commits made the cache and its
construction cheaper, then added a dual hash finder and skip-ahead through long
match interiors. The parser and its ratio evolved at the same time, so the
current high-level throughput is not a clean before-and-after comparison. The
ordinary levels climbed much farther. Some of that recovery came from new
algorithms; some came from avoiding work which could never matter; and some
came from representing the same work differently.

Hashing a fourth byte shortened the chains.

`lean-zip` stored earlier positions in hash chains. Positions which began with
the same three bytes shared a bucket. English puts a great many positions into
the `the` bucket:

```text
hash("the") --> the_ --> them --> then --> they --> there --> ...
                  x        x        x        x         yes
```

The matcher still had to walk the chain and compare each candidate. Profiling
put this walk at roughly 65% of level-6 compression time.

[Commit `5d772a0d`](https://github.com/kim-em/lean-zip/commit/5d772a0dcf0bddffea9c03a4d81f2787b5d6d572)
hashed four bytes instead:

```text
hash("the ") --> the_ --> ...
hash("them") --> them --> ...
hash("then") --> then --> ...
hash("they") --> they --> ...
hash("ther") --> there --> ...
```

One crowded bucket became several short chains. Level 6 became about 54%
faster in the historical Silesia dashboard.

The function was still called `hash3`, although it now hashed four bytes.

This was not free. A four-byte chain cannot discover a match which is exactly
three bytes long, and those small matches still mattered on some binary data.
Later work explicitly adapted
[libdeflate's two-table design](https://github.com/ebiggers/libdeflate/blob/b122c8be1d78b19f6d0a6efc5bb79bfcbb30dd51/lib/hc_matchfinder.h#L108-L130):

```text
hash4 table: bucket --> candidate --> candidate --> candidate
                         chains for matches of length 4 or more

hash3 table: bucket --> newest candidate only
                         one cheap chance to recover a length-3 match
```

The provenance is worth stating carefully. The original four-byte hash PR was
driven by profiling and does not claim libdeflate as its source. The later
dual-table work does cite libdeflate directly.

What did the hash change cost in proof work? It cost nothing. The hash proposes
candidates. It does not get to certify them.

The next change rejected most candidates after checking one byte.

Suppose the current best match has length `N`. A new candidate can only beat it
if the byte at offset `N` also matches. Before running the full comparison,
[commit `7b2e1bec`](https://github.com/kim-em/lean-zip/commit/7b2e1becb7a9fcb6d18b942ab1c9963028a7fc71)
checks that single byte:

```text
best so far:  [ 0 1 2 3 4 5 ]                 N = 6
candidate:    [ = = = = = = ] [ byte 6: X ]  mismatch
                                      |
                                      +--> cannot exceed the best match
                                           skip the full comparison
```

This adapts the early-rejection idea behind zlib's
[`scan_end`](https://github.com/madler/zlib/blob/e3dc0a85b7032e98380dec011bc8f2c2ee0d8fca/deflate.c#L1434-L1451),
although Lean's concrete discriminator is different. It made Silesia level 6
about 26% faster with byte-identical output. The key lemma,
`countMatch_le_of_byte_ne`, proves that a candidate rejected at byte `N` cannot
have improved the answer.

Surviving candidates were compared eight bytes at a time.

For candidates which survived,
[commit `95d13b87`](https://github.com/kim-em/lean-zip/commit/95d13b87b33086ad335bb2b77c6c3a84cb0c0aeb)
adapted libdeflate's
[word-at-a-time match extension](https://github.com/ebiggers/libdeflate/blob/b122c8be1d78b19f6d0a6efc5bb79bfcbb30dd51/lib/matchfinder_common.h#L174-L221).
Load eight bytes from each position into two 64-bit words. If the words agree,
advance eight bytes. If they differ, XOR them. Matching bits become zero, so the
least-significant `1` lies inside the first differing byte.

```text
bytes A:     L  E  A  N  -  Z  I  P
bytes B:     L  E  A  F  -  Z  I  P
             =  =  =  x

A XOR B:    [zero][zero][zero][nonzero][zero][zero][zero][zero]
                                   ^
first differing byte = countTrailingZeros(A XOR B) / 8
```

The first version noticed the word mismatch and then scanned the same bytes
again one at a time. Short matches are common, so that version became slower.
The version which landed used count-trailing-zeros to jump directly to the
mismatch. It improved the paired Silesia measurement by 4.9%, with identical
output.

Here the proof boundary is stronger than it was for lazy matching. The wide
loop is proved equal to the byte loop. The bit-level step which turns XOR and
`ctz` into the first byte index is discharged with `bv_decide`. The simple loop
remains the specification for the fast one.

Lean's representation mattered too.

The representation-focused sequence moved level 1 from roughly 20 to 37 MB/s.
The separately described prefilter helped take it beyond 41, and batched stores
landed later. Hot loops moved away from boxed `Nat`, `Prod`, and `Option` values
and toward machine words and packed scalar arrays. Those changes are less
interesting to draw than the dynamic program, but they are central to the claim
that Lean can be fast. A transferred algorithm is only half the job. The runtime
representation has to suit the hot path as well.

## What the proofs were doing

Did the agents invent all of this from nowhere? No, and that is reassuring.

They read zlib and libdeflate in the same way an engineer would read a paper or
a mature implementation. The planning issues cite files and line ranges. An
idea was isolated, adapted to `lean-zip`'s architecture, measured, and either
kept or rejected.

```text
zlib or libdeflate source
            |
            v
     isolate an idea
            |
            v
adapt it to Lean --> state a proof boundary --> benchmark it
                                                |
                              regression -------+------- improvement
                                  |                         |
                                  v                         v
                               reject                     keep
```

That process produced several kinds of provenance. zlib supplied the broad
one-byte-lookahead pattern. libdeflate supplied the later lazy cost rule, the
observation classes for block splitting, the dual hash tables, the shape of the
near-optimal parser, and the XOR-plus-first-set-bit technique. The original
four-byte hash was independently motivated by profiling. Other variants were
implemented, measured, and discarded.

The examples also use three recurring proof shapes:

```text
1. Heuristic-independent correctness
   Search validates candidate matches, and construction clamps block cuts.
   The ranking heuristic may choose badly among those safe possibilities.
   Examples: lazy acceptance, hash candidates, and block boundaries.

2. Untrusted advice
   The optimizer may propose nonsense; a proved checker validates it.
   Example: the near-optimal choice arrays.

3. Equality to a simple reference
   The fast kernel must return exactly the result of the simple one.
   Examples: the prefilter and the word-at-a-time match loop.
```

The interoperability bug adds a warning to all three. A theorem covers only its
statement. Our roundtrip theorem says that our stated decoder returns the
original input. It does not replace benchmarks, ratio canaries, or conformance
tests against other implementations.

What it supplied was a ratchet. Profiling found a bottleneck. Mature
implementations supplied some ideas. Agents tried them, including variants
which failed. Benchmarks chose the winners. The theorem kept those wins from
quietly breaking the proved roundtrip property.

That leaves the two conclusions from the first post intact. With enough tuning,
basic algorithms written in Lean can be competitive with implementations in
fast languages. More importantly, much of that tuning can be delegated to AI
agents when a theorem states what their changes are not allowed to break.

The theorem did not tell us which optimization would work. It told us what had
to survive while we found out.
