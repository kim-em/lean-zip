# Why Lean is faster than Rust — video script and storyboard, v2

**Target runtime:** roughly 17 minutes, allowing time for diagrams to move and
code transformations to breathe.

**Format:** voiceover-led mathematical explainer. No talking head is required,
although a brief presenter shot can replace the title card or final shot.

**Editorial premise:** the first four minutes are a compact, self-contained
version of `blog.md`. The remainder tells the algorithm story from
`blog-part2-v2.md`. The commits are explained in the order a byte encounters
the machinery—find candidates, make a local choice, then reason over a whole
region of the parse—not their exact landing order. The final return to the
history graph restores the true chronology.

## Visual language

Use a dark navy field and clean vector geometry. Aim for the clarity and
object-continuity of a mathematical explainer, without copying another channel's
branding, fonts, palette, or signature motifs.

- Input bytes are square tiles on one persistent horizontal ribbon.
- Literals are amber tiles and one-step amber edges.
- Back-references are violet arcs.
- Candidate positions and hash structures are cyan.
- Estimated bit costs are coral number chips.
- Rejected or wasted work fades to gray and receives a red slash.
- The lean-zip Pareto curve is red; miniz_oxide is green, matching the existing
  graph.
- A thin green rail along the bottom represents the roundtrip theorem. It is
  present whenever optimized code is running.
- A green **shield** means "any heuristic choice is safe after validation."
- A green **equals sign** means "this optimized kernel returns exactly the same
  result as the simple reference."
- An off-white **UNTRUSTED ADVICE** ticket is used for the dynamic program.

Do not use a generic "FORMALLY VERIFIED" stamp. The proof establishes the
stated roundtrip/equivalence properties; it does not prove benchmark quality,
optimality, interoperability with every foreign decoder, or the absence of
every possible security bug.

For upstream provenance, always use the same visual grammar:

1. Show a small typeset source card with repository, file, immutable commit and
   line range.
2. Highlight at most two or three semantic fragments.
3. Lift those fragments into a central, language-neutral **IDEA** card.
4. Bring the Lean implementation in on a separate branch, with explicit
   **LEAN DELTA** badges for material differences.
5. Keep both citations in the footer.

Do not literally morph C tokens into Lean tokens. The animation should show an
idea being adapted, not code being mechanically translated.

---

## 0:00–0:42 — Cold open: an apparently ridiculous claim

**VOICEOVER**

> I can't possibly be serious, can I, claiming that Lean is faster than Rust?
>
> Let me show you something.

**STORYBOARD**

- Begin on black. A terminal cursor blinks twice.
- Type two short commands, using the actual built executables:

  ```shell
  $ bench/.lake/build/bin/compress-file silesia.tar 6
  $ bench/rust/miniz_oxide_shim/target/release/miniz-compress-file silesia.tar 6
  ```

- Do not wait through real five-second runs in the edit. Use a quick spinner,
  then reveal two result cards from `bench/results/whole_tar_l6.json`:

  ```text
  pure Lean       5.629 s median     67,943,851 bytes
  miniz_oxide     5.777 s median     68,112,144 bytes
  ```

- Label these precisely: "cold whole-tar L6 · recorded 2026-07-22". Add a
  production marker to rerun `bench/whole_tar_l6.sh` immediately before final
  recording and update the card if the committed measurement changes.
- The Lean time and size turn red; the Rust values turn green. The smaller time
  and size receive subtle upward/left arrows rather than a victory animation.

**VOICEOVER**

> This is lean-zip's implementation of DEFLATE compressing the standard
> Silesia corpus. At this setting, the pure-Lean compressor is producing a
> slightly smaller file in slightly less time than miniz_oxide, the standard
> Rust implementation.
>
> How is that even remotely possible?

- On the last sentence, pull the two result cards apart and reveal the title
  between them:

  **WHY LEAN IS FASTER THAN RUST**

- After a half-beat, add a much smaller subtitle:

  **or, more accurately: how verification changed an optimization process**

---

## 0:42–1:35 — The proof is the ratchet

**VOICEOVER**

> The secret is this.

**ON-SCREEN CODE**

```lean
/-- Inflating what we deflate returns the input exactly. -/
theorem inflate_deflateRaw (data : ByteArray) (level : UInt8)
    (maxOutputSize : Nat) (hsize : data.size ≤ maxOutputSize) :
    inflate (deflateRaw data level) maxOutputSize = .ok data
```

**STORYBOARD**

- Typeset the theorem, rather than showing an editor screenshot. Syntax-color
  it using restrained Lean-like colors.
- Highlight `deflateRaw data level`, move its result through a small compressor
  box, then through an inflater box. The original byte ribbon reappears exactly.
- The theorem condenses into the persistent bottom rail:

  ```text
  inflate(deflate(data)) = data
  ```

**VOICEOVER**

> The library isn't just tested and validated. Its central roundtrip property
> is proved. That meant we could let coding agents make aggressive changes,
> while requiring the proof to survive every step.
>
> Without that boundary, autonomous optimization would demand a rather heroic
> amount of human review. Here, when the theorem still held, we could at least
> say: whatever this optimization did, the compressor still cannot lie about
> the bytes it encoded.

**STORYBOARD**

- Above the theorem rail, show a procession of small commit cards entering a
  test-and-proof gate. Red failure cards bounce back. Green cards snap into a
  growing chain.
- Avoid showing an AI as a robot. Use small labeled worktree cards—"profile",
  "change", "measure", "prove"—to keep the process concrete.

---

## 1:35–2:48 — The animated evidence

**VOICEOVER**

> What came out of that process is astonishing.

**ASSET**

`bench/graphs/silesia_compress_pareto_history_vs_rust.svg`

**STORYBOARD**

- Draw the axes before revealing the curves. Animate the labels physically:
  "smaller output" travels left; "more bytes per second" travels up.
- Draw the fixed green miniz_oxide curve first.
- Bring in the red lean-zip curve at its earliest retained state. Let the
  repository animation play at a readable speed, with its commit ticker and
  faint per-level trails.
- Hold briefly on two unmistakable leftward moves and one vertical jump. Do not
  explain them yet. Place small question marks at those pulses.

**VOICEOVER**

> This is a Pareto frontier: compression ratio on the horizontal axis,
> throughput on the vertical axis. Left is smaller. Up is faster. Each library
> has levels which trade one for the other.
>
> The green curve is miniz_oxide. The animated red curve replays lean-zip's
> benchmark history, one retained dashboard refresh at a time, while Claude and
> Codex agents work on it.
>
> lean-zip is not close to miniz_oxide's fastest level. Around miniz's levels
> two through five, it is generally a little slower at the corresponding
> ratios—the worst gap here is about twenty-eight percent. But at the dense end,
> miniz's levels six through nine are dominated: the red frontier can compress
> both faster and smaller. At miniz level nine, the speed difference is about
> fifty-eight percent. Level six—the usual default—is the setting from our
> opening comparison.
>
> I still can't quite believe it.

- As the numbers are spoken, draw horizontal dashed lines from the relevant
  green points to the red achievable frontier. Keep labels small and temporary;
  the graph must remain legible.

---

## 2:48–4:20 — The reasonable objection, and the honest claim

**VOICEOVER**

> There is an obvious objection. No one has given miniz_oxide the same swarm of
> agents and the same sustained optimization campaign. I am sure Rust could be
> improved too.
>
> But would we trust every autonomous change? In an ordinary implementation we
> would need to audit the patches and hope the test suite covered the strange
> corners. On the Lean side, the agents still have to get through the proof
> gate.

**STORYBOARD**

- Split screen. Left: a Rust pull request with a large diff and a finite row of
  green tests, followed by question marks fading into the untested input space.
- Right: the same finite tests, plus the continuous theorem rail covering a
  large abstract set labelled "all inputs within the theorem's preconditions".
- Do not imply tests are unimportant; both sides visibly retain tests and
  benchmarks.

**VOICEOVER**

> And lean-zip is not the fastest DEFLATE implementation. When we reveal the
> full field, libdeflate—carefully tuned C with architecture-specific SIMD—
> blows it out of the water.

**ASSET**

`bench/graphs/silesia_compress_pareto.svg`

- Morph the two-library chart into the full static frontier. Highlight
  libdeflate, then zlib, Go, Zig, JavaScript and OCaml without reading a table of
  numbers.

**VOICEOVER**

> lean-zip dominates the OCaml and JavaScript implementations here. Against Go,
> Rust, Zig and the reference zlib implementation, it generally loses at the
> fast end and wins at the dense end. It is competitive with the field, while
> libdeflate remains in another league.
>
> The surprising claim is narrower. With enough work, basic algorithms written
> in Lean can compete with implementations in languages we normally call fast.
> And when the specification is strong enough, much of that work can be handed
> to agents far more freely than I would otherwise find comfortable.
>
> Still: "the agents optimized it" is not an explanation. What did they
> actually do?

- At the final question, all comparator curves fade except the red historical
  trail. The camera dives into one red point. It becomes a byte tile.

---

## 4:20–5:01 — DEFLATE in forty seconds

**VOICEOVER**

> DEFLATE first turns bytes into two kinds of token. A literal says "write this
> byte." A back-reference says "go some distance backward and copy this many
> bytes." It then Huffman-codes those tokens.
>
> So the compressor has to answer two questions. Where are the plausible copies?
> And which mixture of literals and copies will cost the fewest bits?

**STORYBOARD**

- Lay out a short input such as `BANANA_BANDANA` as tiles.
- The first occurrence remains amber literals. For the repeated substring,
  replace tiles with a violet arc back to the source and a `(length, distance)`
  tag.
- Flow the token tiles into a simplified Huffman tree and out as bits. Keep this
  portion schematic; the video does not need to teach canonical Huffman coding.
- Freeze on the two boxes:

  ```text
  FIND CANDIDATES  ──►  CHOOSE A PARSE  ──►  CODE THE TOKENS
  ```

**VOICEOVER**

> We will follow one byte through that pipeline. The commits landed in a
> different order; this order makes the algorithm easier to see.

---

## 5:01–7:06 — Chapter one: one more byte (`5d772a0d`)

### 5:01–5:53 — The crowded bucket

**VOICEOVER**

> To find earlier copies quickly, lean-zip placed positions into hash buckets.
> Positions beginning with the same three bytes formed a linked chain.
>
> Unfortunately, English contains quite a lot of "the".

**STORYBOARD**

- On the persistent ribbon, reveal occurrences of `the `, `them`, `then`,
  `they`, `there`, and `the.`.
- Copy their first three tiles upward into a cyan key `t h e`.
- All six positions fall into one bucket and connect into a long horizontal
  chain, newest first.
- A white current cursor at `there` walks the chain. At each node, animate byte
  comparisons until most candidates fail on byte four. A work counter ticks.
- Show a small profile pie: `chain walk ≈ 65% of L6 compression time`.

**VOICEOVER**

> Every candidate in that bucket still had to be inspected. The chain walk was
> roughly sixty-five percent of level-six compression time.
>
> Then an agent asked what happens if the hash looks at four bytes instead of
> three.

### 5:53–6:26 — The bucket shatters

**STORYBOARD**

- A fourth blank tile appears on the key. Populate it separately with space,
  `m`, `n`, `y`, `r`, and `.`.
- Preserve object identity: the original bucket physically fractures into six
  buckets. Existing chain nodes travel into their new buckets rather than
  disappearing and reappearing.
- The work counter collapses. The current `ther` bucket has only relevant
  candidates.
- The tiny Pareto mini-map pulses at commit `5d772a0d`; show:

  ```text
  L6: 20.3 → 31.3 MB/s   (+54%)
  ```

**VOICEOVER**

> One crowded chain became several short ones. Fewer candidates survived, and
> the survivors were more likely to be useful. In the dashboard, level six
> jumped from about twenty to thirty-one megabytes per second: fifty-four
> percent faster.
>
> The function kept its old name, `hash3`, even though it now hashed four bytes.

### 6:26–7:06 — The missing three-byte match and the provenance coda

**STORYBOARD**

- Show an exact three-byte repeat `cat` whose fourth bytes differ. Its ghost arc
  can no longer be discovered through the hash4 chain. Caption:
  `tradeoff: exact length-3 matches are invisible`.
- Show the aggregate caveat in small type: text often improved on both axes,
  while the whole-corpus L6 ratio moved slightly the wrong way.
- Do **not** show libdeflate as the source of the original commit. Instead draw:

  ```text
  profile ──solid──► lean-zip hash4 experiment

  libdeflate hash4 chains ···dotted parallel mature design···
  ```

**VOICEOVER**

> It was not free. Exact three-byte matches became invisible, which slightly
> hurt the aggregate ratio on difficult binary data. And the original PR does
> not claim that this idea came from libdeflate; profiling led to the
> experiment.
>
> The explicit libdeflate connection arrives in the sequel.

**UPSTREAM SOURCE CARD — brief excerpt**

`libdeflate/lib/hc_matchfinder.h`, pinned at `b122c8b`, lines 112–130:

```c
mf_pos_t hash3_tab[1UL << HC_MATCHFINDER_HASH3_ORDER];
mf_pos_t hash4_tab[1UL << HC_MATCHFINDER_HASH4_ORDER];
```

**LEAN ADAPTATION CARD**

```lean
let seed := h3Seed useH3 data h3tab windowSize pos hlt
let m := chainWalk ... (seed % 512) (seed / 512)
```

- Extract a neutral idea card: `hash4 chain + one latest hash3 candidate`.
- Branch independently to the Lean card. Add deltas: `probe re-verifies 3
  bytes`, `seed packed into Nat`, `level/content gated`.

**VOICEOVER**

> libdeflate keeps the long chains keyed by four bytes, but also keeps one
> latest position per three-byte bucket. Later lean-zip commits explicitly
> adapted that two-table design: clean chains for long matches, and one cheap
> chance to rescue a length-three match.
>
> Changing the original hash required no proof changes. The hash only proposes
> candidates; a reference still has to be checked before it can be emitted.

- Transform the winning candidate node into a violet match arc. Move the camera
  to its start.

---

## 7:06–9:31 — Chapter two: one byte ahead (`19350797`)

### 7:06–7:50 — The greedy trap

**VOICEOVER**

> Finding a match quickly does not mean taking it is wise. A greedy parser grabs
> the best match beginning at the current byte. But a merely decent match now
> can consume the beginning of a much better match one byte later.

**STORYBOARD**

- Use a purpose-built ribbon with a length-5 match at position `p` and a
  length-11 match at `p + 1`.
- Greedy selects the first violet arc. The covered bytes collapse into a
  reference token.
- Rewind visibly. Move the cursor one tile right; the long arc grows into view.
- Emit the first tile as an amber literal, then select the long arc. Compare
  token coverage side by side.

**VOICEOVER**

> Lazy matching pays for one literal in order to take the better reference.
> The broad one-position-lookahead pattern comes from zlib's `deflate_slow`.

**UPSTREAM SOURCE CARD**

- Show only the function header and the three relevant regions from zlib
  `deflate.c` at commit `e3dc0a8`, lines 1950–2067.
- Highlight semantic actions rather than a long quotation:
  `remember current match` → `search next position` → `emit previous match or
  one literal`.
- Lift those into an **IDEA: ONE-POSITION LOOKAHEAD** card.
- Bring Lean in on a separate branch.

### 7:50–8:42 — The obvious rule fails

**VOICEOVER**

> The obvious rule was: if the next match is longer, defer.
>
> It was also wrong.

**STORYBOARD**

- Keep the two arcs, but slide the source of the longer one far to the left
  along a ruler marked `distance 32`, `256`, `4096`, `32768`.
- A distance-bit meter grows at logarithmic boundaries. The longer match saves a
  few length tiles but acquires a larger coral distance cost.
- Stamp the naive decision `+22% on worst affected prose` and then cross it out.
- On the Lean branch, form two gates:

  ```text
  LONGER?  ──yes──►  NO FARTHER?  ──yes──►  DEFER
  ```

**ON-SCREEN LEAN, LANDING VERSION**

```lean
if matchLen2 > matchLen ∧
   pos + 1 - matchPos2 ≤ pos - matchPos then
  -- emit one literal, then the lookahead match
```

**VOICEOVER**

> A farther match needs more distance bits. Naive lazy matching made some large
> prose files twenty-two percent bigger. The version which landed therefore
> deferred only when the next match was both longer and no farther away.
>
> In a controlled Canterbury comparison, the distance-guarded parser made
> levels four through nine about five-point-two percent smaller than greedy
> overall; sixty-four of sixty-six file-and-level cells improved. But the second
> chain search was expensive, so this quality came with a substantial speed
> bill.

- Show the real history graph in the upper-right expanding to half-screen.
  Pulse `19350797`; let the dense points move left and downward. Split its label
  into `lazy matching` and `earlier shared-window split, first refreshed here`.
  Add a small caption: `bundled dashboard frame; controlled lazy result quoted
  in narration`.

### 8:42–9:31 — From a guard to libdeflate's cost rule

**VOICEOVER**

> The no-farther rule was safe but conservative. A much longer match can still
> be worth taking even when it is farther away. Later, lean-zip adopted
> libdeflate's cheap length-versus-distance test.

**UPSTREAM SOURCE CARD — brief excerpt**

`libdeflate/lib/deflate_compress.c`, `b122c8b`, lines 2722–2735:

```c
4 * (next_len - cur_len) +
bsr32(cur_offset) - bsr32(next_offset) > 2
```

**IDEA CARD**

```text
reward extra length  +  compare logarithmic distance costs  >  threshold
```

**LEAN ADAPTATION CARD**

```lean
decide (len1 < len2) &&
decide (4 * (len2 - len1) + dist1.log2 > 2 + dist2.log2)
```

**STORYBOARD**

- Highlight `next_len - cur_len`, the two bit-scan terms, and `> 2` upstream.
- Lift them into the neutral idea card.
- Reassemble on the Lean branch. Animate the subtraction rearrangement which
  avoids truncating natural-number subtraction; grow type annotations and the
  small theorem `lazyAcceptCost_lt` beside it.
- Add `LEAN DELTA: explicit strict-length guard; Nat-safe rearrangement; emitted
  match still independently validated`.

**VOICEOVER**

> This is an adaptation, not a claim that the two source files are the same.
> The formula supplied the decision idea; Lean rearranges it for natural-number
> arithmetic and retains its own validation boundary.
>
> A second lookahead position was tried too. It bought at most six hundredths of
> a percent and was discarded. The failed experiments are part of the story.

- Duplicate the two positions outward until every byte position has a node and
  match arcs fill the screen.

---

## 9:31–12:58 — Chapter three: the whole future (`356a21bf`)

### 9:31–10:30 — Compression becomes a graph

**VOICEOVER**

> One byte of foresight helped enormously. But it was still only one byte.
>
> No local rule can always see the cheapest sequence. A long match now might
> hide an even better combination later. So lean-zip turned parsing into a
> shortest-path problem.

**STORYBOARD**

- Settle on eight byte-position nodes, zero through eight.
- Amber literal edges advance one node. Violet match edges jump several.
- Use deliberately simple, labelled **TOY COSTS**:
  - `0 → 4` match: 9 bits
  - `4 → 8` match: 12 bits
  - `0 → 1` literal: 8 bits
  - `1 → 8` match: 10 bits
- Greedy takes the long first match: total 21. Rewind. The alternate route costs
  18. Illuminate the difference.

**VOICEOVER**

> A byte position is a node. A literal advances one byte. A match jumps over
> every byte it covers. The edge weight estimates the DEFLATE bits needed for
> that literal, or for the match's length and distance.

### 10:30–11:16 — Derive the backward dynamic program

**STORYBOARD**

- Begin at node eight with a green `0` cost-to-end.
- Move right-to-left. At each node, physically add an edge's coral cost chip to
  the already-known destination cost. Slide all candidate sums into a `min`
  funnel; keep the smallest and fade the rest.
- Only after three nodes have been solved, typeset the recurrence underneath:

  ```text
  cost[i] = min(
    literalCost(i) + cost[i+1],
    matchCost(len, dist) + cost[i+len]  for each cached match
  )
  ```

- Once node zero is filled, trace the chosen path forward in bright white.

**VOICEOVER**

> Work backward from the end. At each position, add each edge's cost to the
> cheapest cost already known at its destination, and save the least expensive
> choice. Then walk those saved choices forward.
>
> This is near-optimal, not omniscient. The graph contains a bounded cache of
> useful candidate matches, and the edge weights are estimates.

### 11:16–12:00 — The Huffman chicken and egg

**VOICEOVER**

> There is a deeper problem. A symbol's price depends on its Huffman code, but
> the Huffman code depends on how frequently the chosen parse uses that symbol.
> We do not know the prices until we know the path, and we do not know the path
> until we know the prices.

**STORYBOARD**

- Label the first edge costs `fixed-Huffman seed`.
- Run the first backward sweep quickly. The chosen edges detach and fall into a
  ten-bin-style symbol histogram—not the block-split observation classes, just
  a literal/length/distance frequency visualization.
- Transform bar heights into Huffman code lengths and then new coral cost chips.
- Freeze the new costs, place a clear `ROUND 2` label, and rerun the backward
  sweep. A few path edges switch.
- Show the loop as a side diagram:

  ```text
  fixed costs → path 1 → histogram → fitted costs → path 2
  ```

**VOICEOVER**

> Round one uses fixed-Huffman costs. Its chosen path produces a histogram.
> Round two fits costs to that histogram and solves the graph again. The costs
> stay fixed during each sweep; the algorithm is not rebuilding a Huffman tree
> for every hypothetical path.

### 12:00–12:30 — libdeflate idea, Lean adaptation

**UPSTREAM SOURCE CARD — brief excerpt**

`libdeflate/lib/deflate_compress.c`, `b122c8b`, lines 3313–3502:

```c
cost_to_end = offset_cost + costs.length[len] +
              (cur_node + len)->cost_to_end;
```

**LEAN ADAPTATION CARD**

```lean
let cFull := lenCost[len]! + distCost[dist]! + cost[i + len]!
```

**STORYBOARD**

- Extract two ideas from the upstream card: `backward minimum-cost path` and
  `path → Huffman costs → another pass`.
- On the separate Lean branch add five delta badges:
  - `fixed-Huffman seed costs`
  - `8-slot Pareto candidate cache`
  - `full lengths + useful length-code boundaries`
  - `256 KiB regions with tail estimate`
  - `exactly two rounds`
- Caption the final fork:
  `libdeflate-style adaptation—not a line-for-line port`.

**VOICEOVER**

> The PR explicitly describes this as libdeflate-style near-optimal parsing.
> The backward path and cost-refitting loop are the inherited shape. lean-zip's
> candidate cache, pruning, region scheme and proof boundary are its own.

### 12:30–12:58 — Untrusted advice

**STORYBOARD**

- Convert the chosen path into two strips labelled `chLen` and `chDist`.
- Stamp them **UNTRUSTED ADVICE** and feed them toward an emitter gate.
- For one real choice, animate checks for length, bounds, distance, then a fresh
  byte comparison. It passes and becomes a violet reference.
- Deliberately corrupt the next distance. The gate rejects it and emits an
  amber literal instead. The theorem rail glows but no "optimal" badge appears.

**VOICEOVER**

> The most Lean part is what the proof refuses to trust. The dynamic program
> writes choice arrays. The emitter checks every proposed length and distance,
> compares the bytes again, and falls back to a literal if the advice is bad.
>
> Correctness is proved for arbitrary choice arrays. Optimality is measured,
> not proved.
>
> At landing, Canterbury level nine became about four-point-six percent smaller
> and Silesia about two-point-two percent smaller. It took roughly two-point-two
> to two-point-eight times as long. This was a maximum-compression tier, not a
> free speedup.

- Show the result card and move the red dense point left and down. Follow one
  valid match into the comparison gate and zoom inside it.

---

## 12:58–14:51 — Speed montage: do less, then do eight at once

### 12:58–13:41 — Reject a hopeless candidate with one byte (`7b2e1bec`)

**VOICEOVER**

> Having bought better compression with more work, the agents returned to the
> profiles. Match comparison was the hot loop.
>
> Suppose the best match so far has length N. A new candidate can beat it only
> if its byte at offset N also matches. So check that byte first.

**STORYBOARD**

- Candidates queue before a long byte-by-byte comparison tunnel.
- Place an incumbent ruler of length `N = 6` over the input.
- At the checkpoint, compare only candidate byte 6 with current byte 6. Most
  candidates flash red and dissolve before entering the tunnel.
- Show the logical implication on screen:

  ```text
  candidate[N] ≠ input[N]  ⇒  matchLength(candidate) ≤ N
  ```

- Bring in zlib's source card, pinned `deflate.c` lines 1434–1451, with only the
  `scan_end` early-continue region highlighted.
- Extract `test a discriminator near best length before full extension`.
- Branch to Lean's different predicate:

  ```lean
  data[cand + bestLen] != data[pos + bestLen]
  ```

- Add `LEAN DELTA: one byte; theorem countMatch_le_of_byte_ne`.
- Display the green equals glyph and result card:
  `L6 +26% · output byte-identical`.

**VOICEOVER**

> This is based on zlib's `scan_end` early-rejection idea, although the concrete
> tests differ. Lean checks one byte and proves that a rejected candidate could
> not have beaten the incumbent. Level six became about twenty-six percent
> faster, with exactly the same output.

### 13:41–14:51 — Eight bytes, XOR, and count trailing zeros (`95d13b87`)

**VOICEOVER**

> The survivors still need their exact match length. The simple loop compares
> one byte at a time. libdeflate compares a machine word.

**STORYBOARD**

- Two eight-byte ribbons enter side by side:

  ```text
  L E A N - Z I P
  L E A F - Z I P
  ```

- Pack each little-endian row into a 64-bit block. XOR them. Equal bytes turn
  transparent zero; the differing `N`/`F` byte contains the lowest set bit.
- Zoom into the XOR bit mask. Count trailing zeros to the first `1`; divide the
  count by eight with a visible `>> 3` tile. The resulting index points to byte
  3. Use whatever exact trailing-zero count the chosen glyph encoding produces;
  verify it rather than hard-coding a count in narration.

**VOICEOVER**

> XOR makes every equal bit zero. The lowest set bit is therefore inside the
> first differing byte. Count the zero bits before it, shift right by three—
> which divides by eight—and the CPU has told us exactly where the match ends.

**UPSTREAM SOURCE CARD — brief excerpt**

`libdeflate/lib/matchfinder_common.h`, `b122c8b`, lines 174–221:

```c
v_word = load_word_unaligned(matchptr + len) ^
         load_word_unaligned(strptr + len);
len += bsfw(v_word) >> 3;
```

**LEAN ADAPTATION CARD**

```lean
let w1 := data.ugetUInt64LE (p1 + i) hw1
let w2 := data.ugetUInt64LE (p2 + i) hw2
i + (UInt64.ctz (w1 ^^^ w2) >>> 3).toUSize
```

- Extract `word XOR → first set bit → byte offset`, then form the separate Lean
  branch. Add deltas: `explicit LE load`, `ctz FFI with BitVec reference body`,
  `ugetUInt64LE_ctz_first_diff`, `goUW_eq`.
- Show the failed first revision: after discovering a word mismatch, a red arrow
  loops back to byte zero and compares the same bytes one by one. Stamp
  `REGRESSION`.
- Cut the loop with scissors; ctz points directly to the mismatch.
- Result card: `paired Silesia +4.9% · output byte-identical · filtered from
  history animation as noise`. Use the green equals glyph.

**VOICEOVER**

> The first version loaded the word, noticed a mismatch, and then rescanned the
> same bytes one by one. Since short matches are common, it made both corpora
> slower. The ctz version removed the rescan and improved a clean paired Silesia
> run by four-point-nine percent.
>
> It was too small to survive the history animation's noise filter. It may still
> be the prettiest optimization in the sequence.

- Collapse the eight tiles into a red Pareto point and zoom back out.

---

## 14:51–15:58 — What "taken from libdeflate" actually means

**VOICEOVER**

> So did the agents just copy libdeflate?
>
> No. But they quite sensibly read it.
>
> libdeflate is an extraordinarily good implementation of the same format.
> zlib has three decades of accumulated practical knowledge. Ignoring either
> would be a peculiar way to do performance work.

**STORYBOARD**

- Lay out the provenance pipeline as connected stations:

  ```text
  READ SOURCE → ISOLATE IDEA → ADAPT → PROVE BOUNDARY → MEASURE → KEEP / REJECT
  ```

- Send the five story cards through it:
  - hash4: starts at `PROFILE`, dotted parallel line to libdeflate; later solid
    libdeflate line for the dual table.
  - lazy: solid zlib line to one-step lookahead; Lean delta for distance guard;
    later solid libdeflate line to cost rule.
  - DP: solid libdeflate-style line, with four adaptation deltas.
  - scan_end: solid zlib idea line, different Lean predicate.
  - word extension: solid libdeflate mechanism line, Lean proof/FFI deltas.
- Failed variants fall through a red trapdoor labelled `measured and rejected`:
  naive longer-only lazy; position-plus-two lookahead; word compare plus rescan.

**VOICEOVER**

> Sometimes an upstream implementation supplied a broad pattern. Sometimes it
> supplied an exact little mechanism. Sometimes profiling independently led to
> the same design choice. In every case, the useful unit was an idea: adapted to
> different data structures, measured in this implementation, and connected to
> a proof boundary.
>
> That boundary took three forms. A heuristic may choose badly, but emitted
> matches must be real. An optimizer may supply nonsense advice, but the emitter
> rechecks it. And a machine-shaped inner loop may be proved exactly equal to a
> simple reference loop.

- Reintroduce the shield, advice ticket, and equals glyph beside those three
  sentences. Connect all three to the same theorem rail, but keep their shapes
  distinct.

---

## 15:58–17:03 — Return to the curve

**ASSET**

`bench/graphs/silesia_compress_pareto_history.svg`

**STORYBOARD**

- Replay the full red history quickly. This time, stop at the true chronological
  positions of the five commits and label them:
  - `19350797` lazy matching
  - `356a21bf` near-optimal parse
  - `7b2e1bec` one-byte prefilter
  - `5d772a0d` four-byte hash
  - `95d13b87` word-at-a-time comparison, represented as a subtle pulse outside
    the retained-frame ticker because it was filtered out
- Let each label briefly recall its animation icon: two arcs, weighted DAG,
  checkpoint byte, splitting bucket, XOR mask.
- Pull back until the theorem rail spans the full width beneath the graph.

**VOICEOVER**

> Verification did not make these algorithms fast. Profiling found the
> bottlenecks. zlib and libdeflate supplied several of the ideas. Benchmarks
> separated the wins from the wonderfully plausible regressions.
>
> What the proof changed was how safely those experiments could compound. Every
> retained point on this curve still had to preserve the same simple promise:
> inflate what we deflate, and get the original bytes back.
>
> Obviously, Lean is not intrinsically faster than Rust. It is much easier to
> sit down and write fast systems code in Rust than in Lean. But this experiment
> suggests something more interesting than the title.
>
> The theorem never told us which optimization would work. It merely let us keep
> asking, much more recklessly than would otherwise be sensible.

**FINAL SHOT**

- The graph and all commit labels fade.
- Leave the original byte ribbon above the exact simplified equation:

  ```text
  inflate(deflate(data)) = data
  ```

- The ribbon passes through compressor and inflater once, returning unchanged.
- Fade to repository URL and credits.

---

## Production appendix

### Assets to use

- `bench/graphs/silesia_compress_pareto_history_vs_rust.svg` — two-library
  historical animation.
- `bench/graphs/silesia_compress_pareto.svg` — current full comparator field.
- `bench/graphs/silesia_compress_pareto_history.svg` — full historical return.
- `bench/results/whole_tar_l6.json` — terminal-demo numbers; refresh immediately
  before recording.
- `Zip/Native/Deflate.lean` — current hash, lazy, prefilter and word-at-a-time
  Lean source cards.
- `Zip/Native/DeflateParse.lean` — dynamic-program and revalidating-emitter
  source cards.

### Immutable upstream references

- zlib lazy pattern:
  [`deflate.c`, `e3dc0a8`, lines 1950–2067](https://github.com/madler/zlib/blob/e3dc0a85b7032e98380dec011bc8f2c2ee0d8fca/deflate.c#L1950-L2067)
- zlib early candidate rejection:
  [`deflate.c`, `e3dc0a8`, lines 1434–1451](https://github.com/madler/zlib/blob/e3dc0a85b7032e98380dec011bc8f2c2ee0d8fca/deflate.c#L1434-L1451)
- libdeflate dual hash-table structure:
  [`hc_matchfinder.h`, `b122c8b`, lines 112–130](https://github.com/ebiggers/libdeflate/blob/b122c8be1d78b19f6d0a6efc5bb79bfcbb30dd51/lib/hc_matchfinder.h#L112-L130)
- libdeflate lazy cost rule:
  [`deflate_compress.c`, `b122c8b`, lines 2722–2735](https://github.com/ebiggers/libdeflate/blob/b122c8be1d78b19f6d0a6efc5bb79bfcbb30dd51/lib/deflate_compress.c#L2722-L2735)
- libdeflate near-optimal path and refitting:
  [`deflate_compress.c`, `b122c8b`, lines 3313–3502](https://github.com/ebiggers/libdeflate/blob/b122c8be1d78b19f6d0a6efc5bb79bfcbb30dd51/lib/deflate_compress.c#L3313-L3502)
- libdeflate word-at-a-time match extension:
  [`matchfinder_common.h`, `b122c8b`, lines 174–221](https://github.com/ebiggers/libdeflate/blob/b122c8be1d78b19f6d0a6efc5bb79bfcbb30dd51/lib/matchfinder_common.h#L174-L221)

### Source-credit wording

Use this in the description or end credits:

> Algorithm references link to immutable upstream commits. On-screen excerpts
> are brief and used to explain the adaptations; the diagrams, animation and
> pseudocode are original. libdeflate is © 2016 Eric Biggers and © 2024 Google
> LLC, MIT-licensed. zlib is © 1995–2026 Jean-loup Gailly and Mark Adler,
> under the zlib license.

If a source excerpt grows beyond the tiny fragments specified above, include
the upstream license notice in the production asset repository. Prefer typeset
excerpts to screenshots of GitHub's interface.

### Accuracy checklist before picture lock

- Rerun or deliberately freeze the whole-tar opening numbers and label the date.
- Regenerate the graph assets from a clean checkout; do not render dirty
  worktree data as committed history.
- Call `5d772a0d` profiling-led. Reserve explicit libdeflate provenance for the
  later dual-table commits.
- Describe lazy commit `19350797` as "longer and no farther"; the libdeflate cost
  formula is the later `ac14de13` refinement.
- Say "near-optimal" and "minimum through cached candidates under estimated,
  frozen-per-round costs," never "proved globally optimal."
- Attribute the controlled DP result to the PR measurement: Canterbury −4.6%,
  Silesia −2.2%, roughly 2.2–2.8× slower.
- State that zlib and Lean use different concrete early-rejection predicates.
- Label +4.9% for XOR/ctz as the paired Silesia measurement, not a universal
  corpus result.
- Keep the proof scope precise: roundtrip validity and specific kernel
  equalities, not compression optimality or benchmark truth.
