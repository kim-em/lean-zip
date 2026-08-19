# Where the performance came from

In [the last post](blog.md) I showed you an animated chart: the red line of
`lean-zip`'s compression Pareto frontier sweeping up and to the left through
the project's git history, until it dominated `miniz_oxide`. I promised some
highlights of how that actually happened. This post is the archaeology.

The raw material is the benchmark dashboard itself. Every performance PR
refreshed `bench/results/latest.json`, so the repository contains 76 usable
snapshots of the Silesia numbers, each attributable to the commits that landed
in between. Replaying them:

* Level 1 went from 18.8 MB/s to 111.6 MB/s, six times faster.
* Level 6 (the default, and the headline of the last post) went from 11.4 MB/s
  to 39.5 MB/s, while its compression ratio *improved* from 0.379 to 0.321:
  three and a half times faster, with 15% smaller output.
* The top level's ratio went from 0.379 to 0.314, past anything the reference
  `zlib` produces.

No single trick did that: it's roughly a hundred performance commits. But the story
has a clean two-act structure. In act one, the compressor learned to make
better *decisions*, sometimes paying speed for them: the curve moved left. In
act two, a long sequence of optimizations made those decisions cheap, with
proofs that the output didn't change: the curve moved back up.

I picked out the commits below for being algorithmically interesting, or for
having interesting provenance, or both. First, though, the provenance story
deserves its own section, because it surprised me.

## The agents read libdeflate

I had vaguely expected the optimization history to be a pile of Lean-specific
tuning. Some of it is (more on that below). But the big algorithmic moves were
not invented from nothing, and they weren't vague pattern-matching on
"compression techniques" either. The planning issues *cite the C source of
zlib and libdeflate by file and line number*, the way you'd cite a paper.

Here is a typical example, from
[the issue proposing the dual-hash match finder](https://github.com/kim-em/lean-zip/issues/2742):

> **What libdeflate does (`hc_matchfinder.h:112-333`)**
> Two tables, split by role: **hash4** (16-bit table) owns the chains ...
> **hash3** (15-bit table) is a **singleton**: one most-recent position per
> bucket, no chain. It is consulted once, only while `best_len < 4`, to keep
> length-3 matches reachable.

The workflow is always the same: read the mature implementation, port the
idea, measure it on real corpora, and keep it or reject it. The rejections
are recorded next to the adoptions. libdeflate's two-position lookahead was
implemented, measured at ≤0.06% of ratio, and rejected as not worth a second
chain walk plus a proof branch. libdeflate's `nice_match_length` values were
tried and backed out when they cost ratio here. This isn't "inspired by libdeflate";
it's a selective port with receipts, into a codebase where every step had to
keep `inflate (deflateRaw data level) = .ok data` green.

I find this genuinely reassuring, by the way. "The AI read the best C
implementation in the world and carefully transplanted the load-bearing ideas,
proving each step safe" is a much better story than "the AI made something
up".

## Act one: better decisions

### Look one byte ahead (and know when not to)

The first big ratio move is the oldest idea here: zlib's `deflate_slow`, from
1995. A greedy LZ77 parser takes the best match starting at the current byte.
That's locally sensible and globally shortsighted: a decent match *now* can
swallow the first byte of a much better match one position later.

```text
input:      ... t h e _ c a t a l o g u e ...
                ^
greedy:         [the_cat] found here (7 bytes), take it
lazy:           peek one byte ahead first:
                  [he_catalogue] (12 bytes) starts at the next position
                emit 't' as a literal, take the longer match instead
```

Lazy matching runs the match search a second time at `pos+1`, and if that
finds something better, emits one literal and defers. One byte of literal buys
a much longer back-reference.

It turns out the textbook version doesn't work as written. The first attempt,
deferring whenever the lookahead match was merely *longer*, made some large
text files up to **22% larger**: a longer match that is much farther away
costs more in distance bits than it saves in length. (DEFLATE encodes a match
as a length code plus a distance code, and far distances need more extra
bits.) So
[the commit that landed lazy matching](https://github.com/kim-em/lean-zip/pull/2530)
invented a guard: defer only when the lookahead match is longer **and no
farther**. On Silesia the guarded rule cut output by about 2.4% at the middle
levels and by almost 12% at level 9.

The third act came four weeks later, when
[the accept rule was replaced with libdeflate's cost model](https://github.com/kim-em/lean-zip/pull/2776).
Instead of refusing every longer-but-farther match, ask whether the length
gain pays for the extra offset bits:

```lean
@[inline] def lazyAcceptCost (len1 dist1 len2 dist2 : Nat) : Bool :=
  decide (len1 < len2) && decide (4 * (len2 - len1) + dist1.log2 > 2 + dist2.log2)
```

That is libdeflate's `4·Δlen + bsr(dist1) − bsr(dist2) > 2`, transplanted from
`deflate_compress.c` (the planning issue cites lines 2738-2767) into `Nat`
arithmetic, written with additions on both sides so the subtractions never
truncate. On Silesia it produced 0.4% to 0.9% smaller output at every lazy
level, on both text and binary files, with no regression anywhere.

So the arc runs from a textbook rule that fails, through a home-grown guard,
to the mature cost model. The reason all this experimentation was cheap is a
deliberate design decision in the proof architecture: match-finding is opaque
to correctness. Every candidate a heuristic picks is re-verified at emission
by proven code, so the roundtrip theorem is quantified over the accept
predicate, and swapping the rule re-threads a couple of lemmas rather than
redoing any real proof. The proofs did their hard work once, at the emission
boundary, precisely so that experiments like these would never have to touch
them again.

*(Figure: three-panel static diagram. Panel 1: greedy takes the short match.
Panel 2: lazy defers to the longer match. Panel 3: a "distance bits" meter
showing a longer-but-farther match losing to a shorter-but-nearer one.)*

### Cut blocks where the data changes character

A DEFLATE stream isn't one Huffman code forever: the encoder may end a block
at any point and start a new one with a fresh code fitted to fresh statistics.
The question is where to cut. `lean-zip` originally cut at a fixed token
cadence, which is provably safe and statistically oblivious: real files switch
character mid-stream (prose into tables, XML markup into values, code into
embedded data), and a tree fitted before the switch is stale after it.

[The entropy-divergence splitter](https://github.com/kim-em/lean-zip/pull/2532)
walks the token stream once, bucketing every token into one of ten coarse
observation classes (eight literal classes from three cheap bits of the byte,
plus short-match and long-match). Every 512 tokens it compares the recent
window's histogram against the block-so-far histogram, and when the
distributions diverge past a threshold, it cuts:

```text
tokens:   [ prose prose prose prose | digits digits digits ... ]
                                    ^
block-so-far histogram:  ▂▅▇▆▃▁▁▂   |
recent-window histogram: ▂▅▇▅▃▁▁▂ → | → ▁▁▂▂▇▇▆▅   diverged: cut here,
                                    |              start a fresh Huffman code
```

The 32 KiB LZ window deliberately stays shared across the cut: the new block
gets a new codebook but doesn't forget the bytes it can still reference.

The idea has a double parentage.
[The planning issue](https://github.com/kim-em/lean-zip/issues/2528) credits
the concept to zlib's `_tr_flush_block`, which ends a block when accumulated
entropy diverges from what the current trees predict. The mechanism that
actually landed is libdeflate's observation machinery
(`observe_literal` / `observe_match` / `do_end_block_check`), ported with its
constants intact: ten classes, a check every 512 observations, minimum block
size, soft maximum. Both attributions sit in the docstrings of
`Zip/Native/DeflateDynamic.lean` today.

And there's a safety valve that's very characteristic of this project: the
heuristic partition and the old fixed cadence are both sized in exact bits,
and the emitter keeps whichever is smaller. The heuristic literally cannot
regress the output. It also carries zero proof obligations, because the
cut-list emitter clamps every proposed cut into a valid range, so the
roundtrip theorem holds for an *arbitrary* selector, including a hostile one.
A bad selector can make poor blocks; it cannot make an invalid stream.

This was the single biggest ratio lever in the whole history. The dashboard
frame it landed in shows 98 native rows improving and none regressing, with
the big heterogeneous files (where one tree was most wrong) improving by
double digits.

That frame is a little too good to take at face value, though: the same PR
also fixed a pre-existing bug in the dynamic-Huffman length-limiter, and the
bug fix accounts for much of the enormous jump at levels 1 to 6. That bug is
my favourite of the project, and it deserves its own section.

### The bug the proofs couldn't see

The splitter PR added a test compressing heterogeneous input (text followed by
incompressible bytes), and that test failed in a very specific way: the
output was fine by `lean-zip`'s own decoders, and rejected by zlib.

The length-limiter (the code that caps Huffman code lengths at 15 bits, as
DEFLATE requires) had a repair step whose chained array updates read stale
values, silently dropping leaves from the histogram. The result was an
*incomplete* Huffman code: a tree with a dangling unused branch. `lean-zip`'s
verified decoder tolerates incomplete codes. zlib's stricter inflate does not.
So we had output that provably roundtripped through our own inflate, and
wasn't decodable by the most widely deployed decoder on earth.

The roundtrip theorem is not wrong, it's just precise: it guarantees *we* can
decode our output, not that everyone else will. Conformance testing against a
foreign implementation is what covers the gap, and it's why the test suite
decompresses everything through both the native decoder and the zlib FFI. The
fix (drive the repair by the exact Kraft excess, with sequential updates) was
worth an immediate 19% on `dickens` at the default level, because those broken
flat trees had been quietly losing the size arbitration all along.

### Compression as a shortest path

The deepest algorithm in the codebase is
[the near-optimal parser](https://github.com/kim-em/lean-zip/pull/2534),
and it's the one I'd explain to a mathematician. Greedy parsing sees one
position. Lazy parsing sees two. Neither can reason about a *chain* of
choices. The fix is to stop being clever locally and solve the global problem:
every byte position is a node, emitting a literal is an edge to the next
position, every available match is an edge jumping over the bytes it covers,
and each edge is weighted by the number of DEFLATE bits it would cost.
Compression is now a shortest-path problem, solved by a backward dynamic
program:

```text
cost[i] = min( litCost(data[i])       + cost[i+1],
               min over matches (len,dist) at i of
                   matchCost(len,dist) + cost[i+len] )
```

There's a lovely wrinkle: the edge weights depend on the answer. A symbol's
Huffman cost depends on the symbol histogram, which depends on the parse you
haven't chosen yet. So the parser runs twice: round one seeds the costs from
the fixed Huffman code, round two refits the costs to round one's own
histogram and re-solves. (zopfli iterates this many times and pays 50 to 100x;
following libdeflate, `lean-zip` stops at two rounds and pays about 2.5x at
the top level.)

The verification split here is stated with unusual honesty, and I think it's
the right pattern for this kind of code. The DP is not proven optimal. It
doesn't appear in the correctness proof at all. Its output is treated as
*untrusted advice*: the emitter re-verifies every proposed match with a fresh
`countMatch` and falls back to a literal if the advice is bad, so the
roundtrip theorem holds for arbitrary choice arrays. Validity is proven;
optimality is measured, and pinned by a ratio canary in the test suite.

At landing, this cut Silesia's level-9 output by a further 2.2%, on the way to
the final top-level ratio of 0.314 that no zlib level reaches. The initial
cost was brutal (level 9 dropped to 0.44 MB/s on Silesia), and the subsequent
10x recovery, to 4.6 MB/s at the same ratio, is a story of its own: a per-position candidate cache,
libdeflate's dual hash4+hash3 finder, and `bt_matchfinder_skip_byte`-style
skip-ahead through long match interiors.

*(Figure: positions as nodes on a line, literal edges and match arcs labelled
with bit costs, the cheapest path highlighted; a second panel showing the path
shifting after the costs are refit.)*

## Act two: getting the speed back

Act one's decisions moved the curve left and often *down*. Act two moved it
up: dozens of commits, mostly proven output-identical. A few highlights.

**The 4-byte hash.**
[One commit](https://github.com/kim-em/lean-zip/pull/2620) made level 6
compression 54% faster, the single biggest speed jump in the history, and
improved the ratio on text at the same time. zlib hashes 3 bytes into its chain buckets (its minimum
match length); libdeflate and zstd hash 4. The chain walk was 65% of level-6
compress time, and its cost is chain length: hashing a 4th byte means
positions sharing only a 3-byte prefix stop sharing a bucket, so the chains
shatter into short, high-quality ones. The known blocker (a plain 4-byte hash
makes length-3 matches unfindable and had cost +7.4% ratio on `x-ray` at
level 9) was later dissolved by porting libdeflate's dual-table design: hash4
owns the chains, and a singleton hash3 table catches the length-3 matches.

**Reject a candidate with one byte.**
[zlib's `scan_end` prefilter](https://github.com/kim-em/lean-zip/pull/2618):
if the best match so far has length N, a candidate can only win if it matches
in at least N+1 bytes, so check the single byte at offset N first and skip
the full comparison when it differs. Most candidates on a hot chain are
doomed, so this is +26% at level 6 with byte-identical output. The identity
isn't an intuition: `countMatch_le_of_byte_ne` proves the discriminator
sound, and the optimized walk is proven equal to the reference walk.

**Compare eight bytes at a time.**
[Word-at-a-time match extension](https://github.com/kim-em/lean-zip/pull/2746):
load 8 bytes from each side as a `UInt64`, and on a mismatch, XOR the words
and count trailing zeros to land directly on the first differing byte. The
proof that the word loop equals the byte loop goes through `bv_decide`, which
pleases me: verified bit-twiddling. This one's dashboard movement was under
the animation's noise threshold, a good reminder that the red line is the
integral of many commits too small to see individually.

**De-boxing.**
The distinctly Lean chapter. Between two dashboard waves, level 1 nearly
doubled (20 to 41 MB/s) with no algorithmic change at all: hot loops moved
from boxed `Nat`, `Prod`, and `Option` onto `USize` and packed scalar arrays,
FFI stores got batched, tables got packed into single words. If you want the
"Lean can be fast" lesson in one sentence: the algorithms transferred from C
unchanged, and the remaining gap was memory representation, which is exactly
the part the equivalence proofs make safe to rewrite aggressively.

## What the proofs were doing all along

Looking back over the whole history, the proofs supported the optimization
work in three distinct ways, and I think the taxonomy is the real lesson of
the project:

1. **Correctness independent of the heuristic.** Lazy accept rules, block-cut
   selectors, and probe depths are quantified out of the theorems entirely, so
   the agents could churn heuristics freely. The proofs say any choice is
   safe; the benchmarks say which choice is good.
2. **Optimization as untrusted advice.** The near-optimal DP is unverified and
   unverifiable in practice, so its output is re-checked at emission by
   verified code. We prove the checker and measure the advisor.
3. **Optimized kernel proven equal to a simple reference.** The prefilter, the
   word-at-a-time compare, the packed tables, and the de-boxed loops all
   produce the same output, bit for bit, and the reference implementation is
   kept as the specification.

Every performance commit in this story is one of those three shapes. And that,
more than any individual trick, is why it was possible to let the agents run:
each shape comes with a precise statement of what "didn't break anything"
means.

The one thing none of the three shapes can promise is that *other people's
decoders* accept our output. That gap is covered by conformance tests against
zlib, and the length-limiter bug is the cautionary tale: it was proved to
roundtrip, rejected by the rest of the world, and caught by a test.

That, to me, is the real result of the experiment. It isn't that Lean beat
Rust on a chart; it's that a theorem told us exactly which risks we were and
weren't taking while the agents ran.
