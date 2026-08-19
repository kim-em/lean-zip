# Why Lean is faster than Rust, part 2: what the agents actually did

"The AIs optimized it" is not an explanation.

Fine. What did they actually do?

DEFLATE compression has two broad stages. First it replaces repeated bytes with
*back-references*: instead of writing `catalog` again, it can say "go back 8,192
bytes and copy 7". Bytes that are not part of a useful match are written as
*literals*. It then Huffman-codes that stream of literals and references.

```text
input bytes
    │
    ▼
find possible matches ──► choose literals and references ──► Huffman-code them
       "where could I copy from?"       "which copies are cheapest?"
```

Almost all of the story below happens in those first two boxes.

I'm going to tell it in the order a byte encounters the machinery, rather than
the order the commits landed. We will start by finding matches, then decide
whether to take one, then turn all the possible decisions into a graph. At the
end we'll return to the git history and watch the agents claw back the time all
that cleverness cost.

## One more byte

Suppose the compressor is sitting at the beginning of `there`. It wants to find
earlier occurrences of the same bytes. Searching the previous 32 KiB one byte at
a time would be rather slow, so lean-zip used a hash table. Positions beginning
with the same three bytes were linked together in a chain.

That works, but English is unhelpfully fond of `the`:

```text
three-byte key

                         one long chain
hash("the") ──► the_ ──► them ──► then ──► they ──► there ──► ...
                  ×         ×         ×         ×          ✓
              compare   compare   compare   compare     useful
```

The matcher still has to walk that chain and compare each candidate with the
current input. On the level-6 profile, the chain walk was consuming roughly 65%
of compression time.

Then commit [`5d772a0d`](https://github.com/kim-em/lean-zip/commit/5d772a0dcf0bddffea9c03a4d81f2787b5d6d572)
made a small change: [hash four bytes instead of
three](https://github.com/kim-em/lean-zip/pull/2620).

```text
four-byte keys

hash("the ") ──► the_ ──► ...
hash("them") ──► them ──► ...
hash("then") ──► then ──► ...
hash("they") ──► they ──► ...
hash("ther") ──► there ─► ...

             one crowded bucket becomes several short chains
```

Positions which merely share a three-byte prefix stop colliding. The chains get
shorter, and the candidates which remain are more likely to survive the first
few comparisons.

That was enough to move level 6 from 20.3 to 31.3 MB/s in the dashboard: **54%
faster**.

The function was still called `hash3`, although it now hashed four bytes.

This was not a universal free lunch. A chain indexed by four bytes cannot find a
match which is *exactly* three bytes long, and on some difficult binary files
those tiny matches mattered. Across the whole Silesia corpus, the level-6 ratio
became slightly worse even though text became both faster and smaller.

There is a nice sequel here. [libdeflate's hash-chain match
finder](https://github.com/ebiggers/libdeflate/blob/b122c8be1d78b19f6d0a6efc5bb79bfcbb30dd51/lib/hc_matchfinder.h#L112-L130)
uses two tables with different jobs:

```text
hash4 table:  bucket ──► candidate ──► candidate ──► candidate
                         a chain for matches of length 4 or more

hash3 table:  bucket ──► newest candidate only
                         one cheap chance to recover a length-3 match
```

Later lean-zip commits
[`52a0d6d9`](https://github.com/kim-em/lean-zip/commit/52a0d6d9)
and [`026a0a47`](https://github.com/kim-em/lean-zip/commit/026a0a47)
explicitly adapted that two-table design. The long chains stay cleanly keyed by
four bytes; a single most-recent three-byte candidate acts as a lifeboat for the
short matches.

It is worth being precise about the provenance. The original `5d772a0d` PR does
not say "we got hash4 from libdeflate". Profiling led to that experiment, while
libdeflate and other mature compressors made the same broad design choice. The
later dual-table work *does* cite libdeflate directly.

What did changing the hash cost in proof work?

Nothing.

The correctness theorem never assumes that the hash table finds the best match,
or indeed a match at all. It only insists that a reference which is eventually
emitted really points backward to equal bytes. The hash is an opaque way to
propose candidates. A worse hash hurts speed or compression ratio, but it does
not get to manufacture a false reference.

We could now find matches much faster. That did not mean we were choosing the
right match.

## One byte ahead

A greedy LZ77 parser takes the best match it can see at the current position.
That sounds sensible. It is also occasionally a trap.

```text
past window:    ... abc ... bcdefghijk ...

current input:      a b c d e f g h i j k
                    └─────┘                 match now:    length 3
                      └─────────────────┘   one byte on:  length 10

greedy:           [ reference 3 ] [ ... ]
one-byte lazy:    [ literal "a" ] [       reference 10       ]
```

Spending one literal can expose a much longer reference beginning at the next
byte. Commit
[`19350797`](https://github.com/kim-em/lean-zip/commit/19350797c95dffb1b954aa6287211f6b526bfdd1)
added this [one-position lookahead](https://github.com/kim-em/lean-zip/pull/2530),
following the broad pattern of zlib's
[`deflate_slow`](https://github.com/madler/zlib/blob/e3dc0a85b7032e98380dec011bc8f2c2ee0d8fca/deflate.c#L1950-L2067).

The first rule was obvious: if the match one byte later is longer, defer.

It was also wrong.

DEFLATE references have both a length and a distance. Farther distances usually
need more bits. The naive rule sometimes threw away a cheap nearby match for one
which was slightly longer but vastly farther away. On some large Canterbury
prose files it made the output as much as 22% larger.

The version which landed therefore had two gates:

```text
candidate at p + 1
        │
        ├── is it LONGER than the match at p? ── no ──► keep p
        │                         │
        │                        yes
        │                         ▼
        └── is it NO FARTHER than the match at p? ── no ──► keep p
                                  │
                                 yes
                                  ▼
                         emit one literal; defer
```

This is a lovely example of an optimization being discovered rather than merely
implemented. The textbook idea came from zlib. The first translation measured
badly. The agent found the reason, changed the acceptance rule, measured again,
and kept the version which worked.

A few weeks later, commit
[`ac14de13`](https://github.com/kim-em/lean-zip/commit/ac14de13e4bf6f35338f6c374fc9b1a9279a8cd6)
kept the strict "longer" gate, but replaced the conservative "no farther" gate
by adapting [libdeflate's compact cost
inequality](https://github.com/ebiggers/libdeflate/blob/b122c8be1d78b19f6d0a6efc5bb79bfcbb30dd51/lib/deflate_compress.c#L2722-L2735):

```text
4 · (length₂ - length₁) + floor(log₂ distance₁) - floor(log₂ distance₂) > 2
```

It is not a complete simulation of the eventual Huffman stream. It is a cheap
test for whether the extra length is likely to pay for the more expensive
distance. That refinement made every tested lazy level another 0.4–0.9% smaller
at essentially neutral speed. A second, two-position lookahead was also tried;
it bought at most 0.06%, so it was thrown away.

The initial lazy parser was a much bigger lever. In the controlled Canterbury
comparison, the distance-guarded version made levels 4–9 about 5.2% smaller than
greedy overall; 64 of 66 file-and-level cells improved.

The corresponding dashboard frame moves even farther left, especially at the
dense levels, but it is not a clean lazy-only measurement. It also picked up an
earlier cross-block-splitting change whose benchmark data had not yet been
refreshed. This is why reading the PR measurements matters as much as watching
the graph.

Unfortunately, it also made those dense levels dramatically slower. Looking one
byte ahead means doing another chain search. On the animated graph the red curve
moves sharply left, toward smaller output, and also down.

This was not a failure. It created valuable new territory on the Pareto graph.
The rest of the history is partly the story of making that territory fast.

And again, the proof did not need to know whether the acceptance rule was wise.
It uses the small fact that an accepted lookahead is longer; it does not prove
that libdeflate's cost model is a good one. Before emission, lean-zip
re-established that the distance was in the window and that the source bytes
actually matched. Changing "longer and no farther" into a cost formula changed
compression decisions without changing the roundtrip statement.

One byte of foresight helped enormously. But it was still only one byte.

## The whole future

There is no local rule which always finds the cheapest parse. A short match now
may expose a spectacular match later. A long match may skip over it. The symbols
chosen by one part of the parse also affect the Huffman code lengths used to
price the rest.

Commit
[`356a21bf`](https://github.com/kim-em/lean-zip/commit/356a21bf3842f7baf743d2530f3d4db29a02ac18)
turned [near-optimal parsing](https://github.com/kim-em/lean-zip/pull/2534) into a
shortest-path problem.

Imagine a node at every byte position. Writing a literal is an edge to the next
node. Taking a match is an edge which jumps over the matched bytes. Give every
edge the estimated number of DEFLATE bits it will cost:

```text
                         match: 9 bits             match: 12 bits
                    ╭────────────────► 4 ─────────────────────► 8
                   ╱
position:         0 ── literal: 8 bits ──► 1 ─────────────────► 8
                                               match: 10 bits

greedy-looking route:  0 ─► 4 ─► 8       total 21 bits
cheapest route:         0 ─► 1 ─► 8       total 18 bits
```

Once phrased this way, the algorithm is beautifully simple. Start at the end,
where the remaining cost is zero. Move backward. At each position, compare the
cost of its literal edge with every available match edge, plus the cheapest cost
already known at the destination:

```text
cost[i] = min(
  literalCost(i) + cost[i + 1],
  matchCost(length, distance) + cost[i + length]  for each cached match
)
```

The winning edge records what to do at that position. A final forward walk
follows those choices to produce the token stream.

There is a chicken-and-egg problem. The price of a literal or match depends on
its Huffman code, but the Huffman codes depend on how often the chosen parse uses
each symbol.

lean-zip resolves this with two passes:

```text
fixed-Huffman seed costs
          │
          ▼
  cheapest path, round 1 ──► symbol histogram ──► fitted Huffman costs
                                                       │
                                                       ▼
                                              cheapest path, round 2
```

This is explicitly a [libdeflate-style
adaptation](https://github.com/ebiggers/libdeflate/blob/b122c8be1d78b19f6d0a6efc5bb79bfcbb30dd51/lib/deflate_compress.c#L3313-L3502),
not a line-for-line port. libdeflate supplied the minimum-cost-path and iterative
cost-refitting shape. The Lean version begins with fixed-Huffman seed costs,
keeps a bounded Pareto set of candidate matches at each position, considers
useful length-code boundaries, works in 256 KiB regions with an estimated tail
cost, and performs exactly two rounds.

The name "near-optimal" matters. It finds the cheapest path through the cached
candidates under the current estimated costs. It does not enumerate every
possible DEFLATE stream, and lean-zip does not prove that the result is globally
optimal. It solves one 256 KiB region at a time, with an estimated tail cost so
a match may cross the boundary.

In fact, the dynamic program is not trusted by the correctness proof at all.

Its output is two arrays saying "take this length and distance here". The emitter
treats those arrays as advice. It checks the bounds, reruns the match comparison,
and emits the reference only if the claimed bytes really match. Otherwise it
falls back to a literal.

```text
DP choice arrays ──►  UNTRUSTED ADVICE  ──► recheck length, distance and bytes
                                                   │
                                   valid ──────────┴──── invalid
                                     │                       │
                                     ▼                       ▼
                               emit reference           emit literal
```

The theorem is deliberately stated for *arbitrary* choice arrays. The optimizer
may be suboptimal. It may even be nonsense. It still cannot make the encoder lie
about the input.

At landing, Canterbury level 9 became about 4.6% smaller and Silesia about 2.2%
smaller. On Canterbury, lean-zip's ratio moved ahead of both zlib and libdeflate.
It took roughly 2.2–2.8 times as long. This was a maximum-compression tier, not a
free speedup.

## Paying back the bill

The profiles now had an unsurprising complaint: we were spending a great deal of
time comparing match candidates.

Some of the fixes were grand dynamic programs. Some were one byte.

Suppose the best match found so far has length `N`. A new candidate can beat it
only if the byte at offset `N` also matches. So before comparing from the
beginning, commit
[`7b2e1bec`](https://github.com/kim-em/lean-zip/commit/7b2e1becb7a9fcb6d18b942ab1c9963028a7fc71)
checked that one discriminating byte:

```text
best so far:   [ 0 1 2 3 4 5 ]                length N = 6
candidate:     [ = = = = ? ? ] [ byte 6: X ]  mismatch
                                      │
                                      └── cannot possibly exceed length 6

                      skip the full comparison
```

This adapts zlib's [`scan_end` early-rejection
idea](https://github.com/madler/zlib/blob/e3dc0a85b7032e98380dec011bc8f2c2ee0d8fca/deflate.c#L1434-L1451).
zlib's concrete test uses word checks near the start and end of the incumbent;
Lean uses a different single-byte discriminator and proves it sufficient. The
result was byte-for-byte identical output and about **26% more level-6
throughput**.

For the candidates which survived, commit
[`95d13b87`](https://github.com/kim-em/lean-zip/commit/95d13b87b33086ad335bb2b77c6c3a84cb0c0aeb)
adapted libdeflate's [word-at-a-time match
extension](https://github.com/ebiggers/libdeflate/blob/b122c8be1d78b19f6d0a6efc5bb79bfcbb30dd51/lib/matchfinder_common.h#L174-L221).
Instead of comparing one byte on each loop iteration, load eight bytes from each
position into two 64-bit words.

If the words are equal, advance eight. If they differ, XOR them. Equal bits
become zero, so the least-significant `1` lies inside the first differing byte.

```text
bytes A:       c  a  t  a  l  o  g  !
bytes B:       c  a  t  a  l  y  s  t
               =  =  =  =  =  ≠

64-bit XOR:   [ all zero ][ all zero ][ ... ][ first non-zero byte ][ ... ]
                                                       ▲
first differing byte = countTrailingZeros(A XOR B) / 8 = 5
```

The first version did the wide comparison, noticed a mismatch, and then scanned
the same eight bytes again one by one to locate it. Short matches are common, so
this managed to do more work and made both corpora slower.

The revised version used the CPU's count-trailing-zeros operation to jump
directly to the mismatching byte. A clean paired Silesia measurement improved by
4.9%, with byte-identical output. The change was too small to survive the
animation's noise filter, but it is perhaps the prettiest optimization in the
whole sequence.

These last two changes use a stronger proof pattern than the earlier heuristics.
It is not merely that any result they produce will decode safely. lean-zip proves
that the optimized operation returns exactly the same answer as the simple
byte-at-a-time reference.

## So did the agents just copy libdeflate?

No. But they quite sensibly read it.

libdeflate is an extraordinarily good implementation of the same format. zlib
has three decades of accumulated practical knowledge. Ignoring either would be
a peculiar way to do performance work.

The actual process looked more like this:

```text
zlib / libdeflate source
           │
           ▼
   isolate one idea ──► adapt it to lean-zip's architecture ──► prove a boundary
                              │                                      │
                              ▼                                      ▼
                         benchmark it ───── regression? ─────► reject it
                              │
                             win
                              ▼
                         keep the commit
```

Sometimes the source supplied a broad pattern, as zlib did for lazy matching.
Sometimes the provenance was an exact little mechanism, as with libdeflate's
XOR-plus-first-set-bit match extension. Sometimes profiling independently led
to the same design choice, as with the original four-byte hash. And some ideas
were measured and rejected: naive lazy matching, a second lookahead position,
and the first rescan-after-wide-compare implementation all failed before their
better descendants landed.

This is the part I find most interesting. Verification did not tell an agent
that four bytes would hash better than three. It did not prove that the dynamic
program was optimal. It did not make a bad benchmark good.

What it did was give each experiment a narrow, explicit safety boundary:

```text
candidate heuristic       may choose badly; emitted matches must be real
untrusted optimizer       may give nonsense advice; the emitter rechecks it
optimized inner loop      must equal the simple reference operation exactly
```

That is the ratchet behind the animated graph. Profiling finds a bottleneck.
Mature compressors supply some ideas. Agents try them, including the variants
which turn out not to work. Benchmarks decide what is fast. The proofs prevent
the experiments from quietly changing what decompression means.

The theorem never told us which optimization would work. It merely let us keep
asking, much more recklessly than would otherwise be sensible.
