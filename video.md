# Why Lean is faster than Rust

This is the collaborative voice-over script and animation storyboard. The
target runtime is 9:30, with an absolute cap of 10:00. The extra thirty seconds
are reserved for pauses, transitions, and variation in the recorded delivery.
`video-v1.md` and `video-v2.md` are frozen historical drafts.

Storyboard notation:

- **VO** is spoken narration.
- **SB** is animation and editing direction.
- `[SYNC: "words"]` means that the named visual event lands on those exact
  spoken words.
- Scene class names are stable and correspond to `video/scenes.py`.

The visual grammar stays consistent throughout. `lean-zip` is red,
`miniz_oxide` is green, literals are amber, matches are violet, and proof
boundaries are blue. Scene 2 introduces the roundtrip theorem in full. Later
scenes summon a compact green roundtrip glyph only when correctness enters the
story: two short byte ribbons joined by a `deflate`/`inflate` loop and a check
mark, with no surrounding banner. It disappears again after each proof beat.
Code on screen must be real code from the pinned sources in the production
notes.

---

## Scene 1: ColdOpenScene, the race (0:00 to 0:35)

**VO:**

> I can't possibly be serious, can I, claiming that Lean is faster than Rust?
>
> Let me show you something. On the left is `miniz_oxide`, the standard Rust
> DEFLATE implementation. On the right is `lean-zip`, written in Lean. They
> compress the same 212 megabyte Silesia corpus at level 6.
>
> Lean takes slightly less time, and it produces a slightly smaller file.

**SB:**

1. Begin on black with the sentence `Lean is faster than Rust?` in the center.
   The question mark appears half a beat after the rest of the title.
2. Replace the title with a split terminal. The left pane is labelled
   `miniz_oxide (Rust)`, and the right pane is labelled `lean-zip (Lean)`.
   Type the two commands from `blog.md`, but do not wait through five seconds of
   footage.
3. Reveal the dated result cards together. Use the committed nine-run medians
   from `bench/results/whole_tar_l6.json` at `696ce7f2` on `chungus2`: 5.777 s
   and 68,112,144 bytes for Rust, then 5.629 s and 67,943,851 bytes for Lean.
   Never combine timing from one run with sizes from another.
4. [SYNC: "slightly less time"] Give the Lean time a restrained green outline.
   [SYNC: "slightly smaller file"] Give its byte count the same outline.
5. Freeze the terminals and place the video title over them. Do not add a
   percentage claim to this shot.

---

## Scene 2: TheoremScene, the ratchet (0:35 to 1:15)

**VO:**

> How is that even remotely possible? The secret is this.
>
> This theorem says that inflating what we deflate returns the original input,
> exactly, at every compression level. It is tested, and it is proved.
>
> That let Claude and Codex agents work unusually autonomously. They changed the
> hot loops, measured, and tried again, but the theorem had to survive every
> step.
>
> It does not prove speed, ratio, or compatibility with every decoder. It gives
> each optimization one strong boundary it cannot cross.

**SB:**

1. [SYNC: "The secret is this"] Slide the terminal away and reveal the real
   production-decoder corollary from
   `Zip/Spec/DeflateRoundtripProduction.lean`:

   ```lean
   theorem inflate_deflateRaw (data : ByteArray) (level : UInt8)
       (maxOutputSize : Nat) (hsize : data.size ≤ maxOutputSize) :
       Zip.Native.Inflate.inflate (deflateRaw data level) maxOutputSize = .ok data :=
     (Zip.Native.Inflate.inflate_ok_iff_reference _ _ _).mpr
       (inflateReference_deflateRaw data level maxOutputSize hsize)
   ```
2. Animate a ribbon of bytes into `deflateRaw`, through `Inflate.inflate`, and
   back into the identical ribbon. Underline `.ok data` when the two ribbons
   coincide.
3. Condense the theorem into the compact green roundtrip glyph, without a box,
   for the rest of this scene. Beside it, send commit cards through a loop
   labelled PROFILE, CHANGE, MEASURE, CHECK ROUNDTRIP.
4. [SYNC: "survive every step"] Let several commit cards lock into a growing
   history. Let one failed card bounce off the proof gate and disappear.
5. When the VO names the limits, place three small grey labels beside the glyph:
   `not speed`, `not ratio`, and `not every decoder`. Fade the whole theorem
   motif at the scene boundary; it does not persist over the Pareto chart.

---

## Scene 3: ParetoHistoryScene, the chart and the honest claim (1:15 to 3:00)

**VO:**

> Here is what came out of that process. Every compressor has a level knob that
> trades speed for compression. Sweep through the levels and you get a curve.
> Left is smaller. Up is faster.
>
> The green curve is `miniz_oxide`, written in Rust. The red curve replays
> `lean-zip` through the
> optimization history. It begins far below, then moves left and climbs. Rust
> stays faster at the low and middle settings. By the end, `miniz_oxide` levels
> 6 through 9 are dominated: `lean-zip` can compress both faster and smaller.
>
> I still can't quite believe it.
>
> There is an obvious objection. Nobody has subjected `miniz_oxide` to this same
> campaign, and I am sure it could improve too. There is also a more important
> chart. When we include the whole field, `libdeflate`, carefully tuned C with
> SIMD, remains in another league. This implementation does not use
> `libdeflate`'s architecture-specific SIMD.
>
> So I am not claiming that Lean is faster than Rust in general. The claim is
> narrower. With enough tuning, an implementation in Lean can compete with
> implementations in fast languages. The unusual part is that much of the
> tuning can be delegated to agents because the theorem states what their
> changes are not allowed to break.
>
> What did the agents actually change?

**SB:**

1. Draw the axes from the committed benchmark data in `video/data/history.json`.
   [SYNC: "Left is smaller. Up is faster."] Draw the left arrow, then the up
   arrow, and keep both labels on screen.
2. Draw the green `miniz_oxide` frontier. Rewind the red frontier to the first
   retained benchmark frame. Use the full frame; no theorem banner or glyph is
   present in this scene.
3. [SYNC: "The red curve replays `lean-zip`"] Play the actual retained history
   frames. A small ticker shows dates and short commit hashes, but the VO does
   not claim a particular number of commits or frames.
4. Pause briefly on two leftward moves and one upward move. Do not identify the
   algorithms yet. Their icons return later.
5. [SYNC: "levels 6 through 9 are dominated"] For each green point from level 6
   through level 9, draw a short up-left guide to the red frontier setting which
   beats it. Pulse those four comparisons in order. Do not shade a continuous
   region, since mixed adjacent-level settings are not single built-in levels
   and would obscure the four explicit comparisons. Leave the low and middle
   green advantages plainly visible.
6. Show the objection by placing a dormant optimization loop behind the Rust
   curve. Its cards remain blank because this experiment did not run it.
7. Zoom out to `bench/graphs/silesia_compress_pareto.svg`, with every comparator
   visible. [SYNC: "`libdeflate`, carefully tuned C with SIMD, remains in
   another league"] Pin the `libdeflate` frontier and show a small SIMD register
   beside it.
8. [SYNC: "The claim is narrower"] Put the two claims side by side. Cross out
   `Lean is generally faster than Rust`. Keep `A tuned Lean implementation can
   be competitive, and proofs make agent optimization tractable`.
9. On the final question, dive into one red history point until it becomes a
   ribbon of input bytes.

---

## Scene 4: DeflatePrimerScene, three levers (3:00 to 3:28)

**VO:**

> You only need two ideas to follow the archaeology. DEFLATE replaces repeated
> bytes with references that say, go backward this distance and copy this many
> bytes. Everything else is a literal. It then gives frequent symbols short
> Huffman codes, with a fresh code available at each block.
>
> That leaves three levers: find matches, choose matches, and cut blocks.

**SB:**

1. Place `BANANA_BANANAS` on a byte ribbon. Colour the second `BANANA` violet
   and draw an arc back to the first. [SYNC: "go backward this distance and copy
   this many bytes"] Collapse the second occurrence into a `(distance, length)`
   token. Leave the unmatched underscore and trailing `S` as amber literals.
2. Feed the tokens into a schematic Huffman coder. Frequent token types shrink
   into visibly shorter bit strings. Do not explain tree construction.
3. Divide the ribbon into two blocks and let the second block grow a different
   small Huffman tree.
4. [SYNC: "three levers"] Lock three labels beneath the ribbon: FIND MATCHES,
   CHOOSE MATCHES, and CUT BLOCKS. Highlight CHOOSE MATCHES for the transition.

---

## Scene 5: LazyMatchingScene, one byte ahead (3:28 to 4:32)

**VO:**

> A greedy parser takes the best match at the current byte. Following zlib, lazy
> matching looks one byte ahead. One literal can expose a much longer match.
>
> The obvious rule was to defer whenever the later match was longer. It was
> wrong. Some large text files became substantially larger because a farther
> reference can cost more distance bits than its extra length saves.
>
> The version that landed required the next match to be longer and no farther.
> Four weeks later, an adapted libdeflate rule asked whether the length gain
> would pay for the extra distance bits.
>
> `chainWalk` has already validated both candidates. The proof only needs the
> later one to be longer; the cost formula is opaque. A bad choice can waste
> bits, but it cannot invent a match.

**SB:**

1. Highlight CHOOSE MATCHES. Show a cursor at position `p`, where a violet
   bracket claims five bytes. [SYNC: "looks one byte ahead"] Move a ghost cursor
   to `p + 1`, reveal an eleven-byte bracket, rewind, emit one amber literal,
   and take the longer reference. As each bracket emerges from `chainWalk`, run
   its bytes through a `countMatch` equality scanner. [SYNC: "already validated
   both candidates"] Leave a blue validation stamp on each bracket before the
   acceptance gates appear.
2. Slide the source of that second match far to the left on a logarithmic
   distance ruler. Its distance-bit meter grows until the total cost exceeds
   the nearer match. Stamp `longer always wins` with `failed on large text`,
   then cross the rule out.
3. Build two gates labelled LONGER? and NO FARTHER?. [SYNC: "longer and no
   farther"] Close the second gate on a distant candidate. Move the red point
   left and add `guarded rule kept after corpus measurement`.
4. Use a split code panel for the provenance morph. On the left, show only this
   condition from libdeflate commit `b122c8b`:

   ```c
   if (next_len >= cur_len &&
       4 * (int)(next_len - cur_len) +
       ((int)bsr32(cur_offset) -
        (int)bsr32(next_offset)) > 2) {
   ```

   On the right, show the current Lean rule:

   ```lean
   @[inline]
   def lazyAcceptCost (len1 dist1 len2 dist2 : Nat) : Bool :=
     decide (len1 < len2) &&
       decide (4 * (len2 - len1) + dist1.log2 > 2 + dist2.log2)
   ```

   Keep both source panels stationary. Lift copies of the common concepts into
   a neutral card labelled `IDEA: length gain must pay distance cost`. Build the
   Lean branch independently from that card. Add two blue delta badges:
   `C may accept equal length when distance wins; Lean requires len1 < len2` and
   `signed subtraction moves to the right for Nat arithmetic`. Caption the
   result `ported idea, not line-for-line code`. Show the measured Silesia
   result `paired 105 MB Silesia subset, levels 4 to 9: 0.4% to 0.9% smaller`
   without adding it to the VO.
5. Show the cost gate choosing between the two already-stamped candidates, then
   summon and pulse the compact green roundtrip glyph. Let it disappear before
   the scene ends. Do not add an emitter-side recheck to this path.
6. Move the red Pareto point slightly left and down. The second chain search
   improved compression but initially cost speed.

---

## Scene 6: BlockSplittingScene, cut when the statistics change (4:32 to 5:44)

**VO:**

> DEFLATE gives each block its own Huffman code. Shared-window splitting matched
> the input once, fitted each block separately, and still allowed references
> across boundaries. On large Silesia text files at level 9, output fell 15 to 20
> percent. The cuts still came at a fixed cadence.
>
> Later, a libdeflate-style refinement compared the block-so-far histogram with
> each recent batch, normally 512 tokens. When the statistics diverge, it
> proposes a boundary and a fresh code. Exact sizing then chose between the
> observed and fixed partitions.
>
> The same pull request exposed my favourite bug in the project. Our verified
> decoder accepted its output, but zlib rejected it. A broken length limiter
> had produced an incomplete Huffman code-length alphabet.
>
> The theorem was not wrong. It was precise. Our production `inflate` decoder
> can decode the output. External conformance is separate, so the zlib test
> found the gap. The missing completeness property soon became a theorem too.

**SB:**

1. Highlight CUT BLOCKS. Flow a long token ribbon from prose-like colours into
   digit-like colours. Drop several fixed-cadence boundaries onto it, but keep a
   translucent 32 KiB history ribbon running beneath them. Draw one reference
   arc across a boundary and stamp `Silesia L9 text: 15% to 20% smaller`.
2. Grow two live ten-bin histograms above the ribbon, labelled `block so far`
   and `recent batch, normally 512`. Reset the recent histogram after each
   non-overlapping check. The histograms initially move together. [SYNC: "the
   statistics diverge"] Let their shapes separate and fill a divergence gauge.
3. Drop a cut line after the sampled batch which detected the change, not at the
   first changed token. [SYNC: "a fresh code"] Grow a new Huffman tree over the
   right-hand block. The history ribbon and its cross-boundary reference remain
   intact.
4. Put `fixed cadence` and `observed split` onto an exact-bit scale. Keep the
   smaller candidate. Caption this narrowly: `Designed and conformance-tested
   not to lose to fixed cadence in this landing's cost arbitration.`
5. Add an archaeology note in small type: `Observation splitting was a smaller
   refinement. It was off at L1 to L6, so all movement there was the limiter
   fix. L7 to L9 also bundled the limiter and an unisolated tuning baseline.`
6. Darken the palette for a twenty-second bug interlude. Draw the 19-symbol
   code-length alphabet as an incomplete Huffman tree with one dashed, unused
   branch, and caption it `incomplete CODES alphabet`. Send its stream toward
   two decoder doors. The `Inflate.inflate` door opens and summons the compact
   green roundtrip glyph. [SYNC: "zlib rejected it"] Slam the zlib door and
   stamp it `invalid code lengths set`.
7. [SYNC: "The theorem was not wrong. It was precise."] Enlarge the theorem,
   circle `Inflate.inflate`, then collapse it back into the green roundtrip
   glyph. Place a separate blue boundary beside it labelled `zlib conformance`;
   do not turn either boundary into a full-width rail.
8. End the interlude with a small follow-up card: `Three days later:
   computeCodeLengths_complete proves the missing Kraft equality.`

---

## Scene 7: OptimalParsingScene, the whole future (5:44 to 7:11)

**VO:**

> Greedy sees one position, and lazy sees two. Neither plans the whole parse.
>
> Put a node at every byte position. Literals move one node; matches jump over
> several. Give each edge an estimated bit cost, and compression becomes a
> shortest-path problem.
>
> The dynamic program works backward from the end. It adds each edge cost to
> the best known destination cost and keeps the cheapest choice.
>
> Huffman costs depend on the parse, so the weights depend on the answer.
> Following libdeflate's design, `lean-zip` solves with seed costs, refits them
> to that parse, and solves the graph again.
>
> Here, near-optimal means a minimum through cached candidates inside bounded
> 256 kilobyte regions with an estimated tail, not the best possible DEFLATE
> stream. Its arrays are untrusted advice. The emitter checks every match and
> falls back to a literal when necessary.
>
> The price was speed. Now the agents had to buy it back.

**SB:**

1. Highlight CHOOSE MATCHES again. Place nodes `0`, `1`, `4`, and `8` on a line.
   Add four edges with explicit toy costs: `0 to 4 match = 9`, `4 to 8 match =
   12`, `0 to 1 literal = 8`, and `1 to 8 match = 10`. Put `TOY COSTS` above
   the graph so nobody reads the numbers as actual DEFLATE prices.
2. Trace a locally attractive 21-bit path. Then reveal an 18-bit path that
   begins with a literal and wins globally. [SYNC: "a shortest-path problem"]
   Fade the expensive path but leave its ghost visible.
3. Put zero at the final node. [SYNC: "works backward from the end"] Sweep a
   wave from right to left. At each node, visibly add `edge cost + destination
   cost`, feed the sums into a `min` funnel, and write the result below the
   node. Give this animation at least twenty-five uninterrupted seconds.
4. When the wave reaches the start, follow the stored choices forward. The red
   path should emerge from the blue backward computation.
5. Drop the selected tokens into a histogram. Feed the histogram into a new
   set of edge labels while leaving the path as a ghost. Raise `1 to 8` from 10
   to 14 and lower `4 to 8` from 12 to 10, so the former 18-bit winner becomes
   22 bits and the other route becomes 19. [SYNC: "solves the graph again"] Run
   a second, faster backward wave and flip the red path. Keep costs frozen
   within each individual sweep.
6. Caption the adaptation: `libdeflate supplied the backward-path and cost-refit
   shape; Lean uses different caches, regions, pruning, and validation.`
7. Turn the chosen length and distance arrays into a ticket stamped UNTRUSTED
   ADVICE. Corrupt one proposed match. The emitter compares the bytes, rejects
   it, and [SYNC: "falls back to a literal"] swaps in an amber literal without
   breaking the output stream.
8. End silently on two result cards: `Silesia L9: 2.2% smaller at landing` and
   `2.2 to 2.8 times the compression time`. Move the corresponding red point
   left and sharply down.

---

## Scene 8: SpeedMontageScene, getting the speed back (7:11 to 8:12)

**VO:**

> Better decisions moved the curve left and often down. A long sequence of
> speed improvements moved it back up. Here are three.
>
> Hashing four bytes instead of three shattered overloaded match chains. That
> one commit made level 6 54 percent faster. The function was still called
> `hash3`. It now hashed four bytes.
>
> That experiment came from profiling. The later dual-table repair explicitly
> adapted libdeflate.
>
> A zlib-style prefilter checked one decisive byte and rejected candidates that
> could not possibly win. Survivors were compared eight bytes at a time using a
> libdeflate technique. XOR and count-trailing-zeros located the first differing
> byte directly.
>
**SB:**

Use one continuous comparison tunnel. Each vignette removes a different kind
of work from the same stream of candidates.

1. Place many `the?` positions into one long three-byte hash chain. Add the
   fourth byte to every key. [SYNC: "shattered overloaded match chains"] Break
   the bucket into `the_`, `them`, `then`, `they`, and `ther` chains while each
   candidate keeps its identity. Stamp `historical Silesia L6: +54%`.
2. Briefly ghost an exact three-byte match that the four-byte chain can miss.
   Show a later singleton `hash3` lifeboat beside the `hash4` chains, captioned
   `later dual-table design explicitly adapted from libdeflate`. Do not imply
   that the original hash4 commit claimed this provenance.
3. Give the current best match a ruler of length `N`. Check the new candidate's
   byte at offset `N`. [SYNC: "could not possibly win"] Drop every mismatch
   through a trapdoor before the full comparison. Stamp `Silesia L6: +26%,
   byte-identical` and show an equality glyph.
4. Pack `LEAN-ZIP` and `LEAF-ZIP` into two 64-bit words. XOR them so equal bytes
   dissolve to zero. Let the lowest set bit glow, run `ctz`, divide the result by
   eight, and [SYNC: "the first differing byte"] land an arrow on `N` versus
   `F`. Briefly show the failed version rescanning the eight bytes, cross it
   out, then jump directly to the mismatch. Stamp `paired Silesia: +4.9%` and a
   second equality glyph.
5. Reassemble the three vignettes as small icons on the Pareto chart, and move
   the red curve upward.

---

## Scene 9: ProofShapesScene, three shapes of safety (8:12 to 8:57)

**VO:**

> These optimizations use three recurring shapes of proof.
>
> First, correctness can be independent of a ranking heuristic. Search validates
> match candidates, and block construction clamps cuts, before the heuristic's
> choice matters.
>
> Second, optimizer output can be untrusted advice. The dynamic program proposes
> a choice, and the proved emitter checks it.
>
> Third, a fast kernel can be proved exactly equal to a simple one. That is how
> the prefilter and word-at-a-time matcher keep byte-for-byte behaviour.
>
> The proof says which choices are safe. The benchmark says which choices are
> good.

**SB:**

1. Reuse visual objects from earlier scenes rather than introducing a new
   symbolic vocabulary.
2. In the first panel, place the `countMatch` scanner before the lazy acceptance
   gate, and place the block histogram behind a valid-range cut clamp. [SYNC:
   "independent of a ranking heuristic"] Highlight both checked boundaries
   while the heuristics change freely.
3. In the second panel, feed the DP's UNTRUSTED ADVICE ticket into the byte
   checker. [SYNC: "untrusted advice"] Corrupt one ticket and show the literal
   fallback again.
4. In the third panel, place the byte loop beside the prefilter and wide-word
   loop. [SYNC: "exactly equal"] Join them with the equality glyph and a small
   `bv_decide` stamp.
5. Keep the three blue proof boundaries distinct. Once all three are visible,
   summon the compact green roundtrip glyph in the corner. [SYNC: "which
   choices are safe"] Pulse the glyph. [SYNC: "which choices are good"] Pulse
   a separate benchmark gauge, then dismiss the glyph.

---

## Scene 10: OutroScene, return to the curve (8:57 to 9:30)

**VO:**

> So the red curve caught the Rust curve at the high-compression levels. Better
> choices moved it left. Speed work moved it up.
>
> `libdeflate` is still the ceiling.
>
> The proof did not choose the optimizations. Profiles, upstream ideas, and
> benchmarks did. It was the ratchet that let the wins accumulate.

**SB:**

1. Replay the final few seconds of the red history over the faint full-field
   chart. Mark shared-window splitting `437e77cc`, lazy `19350797`, observation
   splitting `35f28549`, the dynamic program `356a21bf`, prefilter `7b2e1bec`,
   and hash4 `5d772a0d` in landing order. Show word-at-a-time `95d13b87` as a
   dashed off-ticker pulse because its frame was filtered out.
2. [SYNC: "`libdeflate` is still the ceiling"] Restore the full-field opacity and
   pin `libdeflate` again.
3. [SYNC: "The proof did not choose the optimizations."] Separate the three
   sources of progress beneath the chart: `profiles found bottlenecks`, `zlib
   and libdeflate supplied ideas`, and `benchmarks chose winners`.
4. [SYNC: "It was the ratchet"] Summon the compact green roundtrip glyph. Fade
   the chart, expand the glyph into `inflate(deflate(data)) = data` at the
   center, and let one final byte ribbon complete the round trip.
5. Hold the repository URL, the two blog titles, and `benchmarks: Silesia,
   methodology in bench/README.md` for the remaining four seconds.

---

## Production notes

The benchmark result cards use paired measurements from the relevant pull
requests, not subtraction between adjacent animation frames. Some frames bundle
multiple changes. In particular, the entropy-divergence splitter landing also
contains the length-limiter fix and an unisolated tuning baseline.

Three complete benchmark snapshots are available for the opening cards:

- the current `blog.md` shell block: 5.75 s and 68,112,444 bytes for Rust,
  then 5.67 s and 67,944,300 bytes for Lean
- the reproducible committed `bench/results/whole_tar_l6.json`: nine
  alternating runs on `chungus2` at commit `696ce7f2`, with medians of 5.777 s
  and 68,112,144 bytes for Rust, then 5.629 s and 67,943,851 bytes for Lean
- a newer three-repetition local race at master: best runs of 5.749 s and
  68,110,828 bytes for Rust, then 5.410 s and 67,943,831 bytes for Lean

They disagree slightly because the builds, crate versions, machines, and timing
summaries are not identical. The present Scene 1 storyboard chooses the
committed nine-run source. At picture lock, choose one complete source and
update both the `blog.md` shell block and the cards together; never combine a
time from one snapshot with a size from another. The spoken narration
deliberately avoids exact values.

Use these repository assets:

- `bench/graphs/silesia_compress_pareto_history_vs_rust.svg`
- `bench/graphs/silesia_compress_pareto.svg`
- `bench/results/latest.json` and the retained history generated by
  `bench/pareto_history.py`
- `video/data/history.json`, which currently feeds the rendered Pareto scene
- `Zip/Native/Deflate.lean:1382` for `lazyAcceptCost`
- `Zip/Native/DeflateDynamic.lean:1184` onward for the block splitter
- `Zip/Native/Deflate.lean:565` onward for XOR plus `UInt64.ctz`
- `Zip/Spec/LZ77ChainCorrect.lean:406` onward for the prefilter theorem
- `Zip/Spec/DeflateRoundtripProduction.lean:22` for the displayed roundtrip
  theorem through the production `Inflate.inflate` decoder
- `ZipTest/NativeDeflate.lean:469` for the seven-bit code-length-alphabet
  regression and zlib's `invalid code lengths set` result
- `Zip/Native/Inflate.lean:98` for the decoder's Kraft-inequality boundary
- `Zip/Spec/HuffmanEncode.lean:1924` for the later completeness theorem

`DeflateRoundtripProduction.lean` is currently a tested working-tree addition.
Before picture lock, land it and record the exact landing commit used for the
render.

The two-library SVG is a generated, currently untracked blog asset. Regenerate
it from the benchmark-history tooling before publication. The rendered video
scene should continue to use `video/data/history.json`, so it does not depend on
that SVG being checked in.

Use these immutable upstream references:

- libdeflate lazy acceptance rule at commit `b122c8b`:
  <https://github.com/ebiggers/libdeflate/blob/b122c8be1d78b19f6d0a6efc5bb79bfcbb30dd51/lib/deflate_compress.c#L2722-L2735>
- libdeflate observation-based block splitting at the same commit:
  <https://github.com/ebiggers/libdeflate/blob/b122c8be1d78b19f6d0a6efc5bb79bfcbb30dd51/lib/deflate_compress.c#L2055-L2217>
- libdeflate dual hash tables at the same commit:
  <https://github.com/ebiggers/libdeflate/blob/b122c8be1d78b19f6d0a6efc5bb79bfcbb30dd51/lib/hc_matchfinder.h#L108-L130>
- libdeflate near-optimal parser at the same commit:
  <https://github.com/ebiggers/libdeflate/blob/b122c8be1d78b19f6d0a6efc5bb79bfcbb30dd51/lib/deflate_compress.c#L3313-L3502>
- libdeflate word-at-a-time match extension at the same commit:
  <https://github.com/ebiggers/libdeflate/blob/b122c8be1d78b19f6d0a6efc5bb79bfcbb30dd51/lib/matchfinder_common.h#L174-L221>
- zlib's match prefilter at commit `e3dc0a8`:
  <https://github.com/madler/zlib/blob/e3dc0a85b7032e98380dec011bc8f2c2ee0d8fca/deflate.c#L1434-L1451>

Before picture lock, verify that every `[SYNC]` phrase occurs once in its scene's
VO, render the scratch narration at ordinary speed, and cut content if the
complete video exceeds 10:00. Do not recover time by accelerating the voice.
