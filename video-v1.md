# Why Lean is faster than Rust — video script v1

Voice-over narration (**VO**) interspersed with storyboard directions
(**SB**). Narration follows the two blog posts, tightened for speech. Target
runtime ~11 minutes. Asset paths refer to this repository; where a storyboard
needs upstream C source, the exact commit to pull from is noted so the
on-screen code is real, not paraphrased.

Structural note: the honest full-field comparison (libdeflate ahead, the
narrowed claim) is deliberately placed in Scene 3, inside the first three
minutes, so that viewers who drop off early still see it. The outro recaps it
but adds no new information. Do not move the disclosure back to the end.

Conventions for the animator:
- "Native red" = the lean-zip curve colour from the dashboard graphs; keep all
  other libraries in their existing dashboard colours for continuity.
- Code is always shown in real syntax-highlighted source, never mock code.
  Lean source references include file:line against current master.
- Sync points are marked like [SYNC: "phrase"] meaning the visual event lands
  on that spoken phrase.

---

## Scene 1 — Cold open: the race (0:00–0:45)

**VO:**

> I can't possibly be serious, can I, claiming that Lean is faster than Rust?
>
> Let me show you something. This is the standard Silesia compression corpus,
> about 200 megabytes of real-world data. On the left is miniz_oxide, the
> standard Rust DEFLATE implementation, at its default level. On the right is
> lean-zip, written in Lean, the theorem prover.
>
> It finishes faster, and the output is smaller.

**SB:**

1. Black screen, single line of white text: "Lean is faster than Rust." Hold
   1s, then a small "(really?)" fades in beneath it.
2. Cut to a clean split-screen terminal. Left pane titled `miniz_oxide (Rust)`,
   right pane titled `lean-zip (Lean)`. Both run a real recorded compression of
   `silesia.tar` at level 6 under `time`, live-typed. (Record with asciinema;
   do not fake the timings. The command lines should match whatever ships in
   the blog post.)
3. Progress bars race. lean-zip finishes first. [SYNC: "finishes faster"]
4. Output byte counts stamp in under each pane; lean-zip's is smaller. A small
   green delta label appears under each: "−x% time", "−y% bytes".
   [SYNC: "the output is smaller"]
5. Freeze frame, desaturate, title card over it: video title.

---

## Scene 2 — The secret is a theorem (0:45–1:35)

**VO:**

> How is that even remotely possible? The secret is this.
>
> This is the roundtrip theorem of lean-zip: inflating whatever we deflate
> returns the input, exactly, at every compression level. This isn't a test
> suite; it's a machine-checked proof.
>
> And that changes what you can do with AI. We let AI agents loose on the
> code, optimizing it aggressively, with one hard rule: the proof has to hold
> at every single commit. There is no human review of the hot loops: if the
> theorem still compiles, the optimization is admissible.

**SB:**

1. The terminal freeze-frame slides down; rising from below, a single Lean
   code block on a dark background:
   ```lean
   /-- Unified DEFLATE roundtrip: inflating what we deflate returns the input exactly. -/
   theorem inflate_deflateRaw (data : ByteArray) (level : UInt8)
       (maxOutputSize : Nat) (hsize : data.size ≤ maxOutputSize) :
       inflate (deflateRaw data level) maxOutputSize = .ok data
   ```
   Underline-animate `inflate (deflateRaw data level)` then `.ok data`
   as the VO says "inflating whatever we deflate returns the input".
2. [SYNC: "a machine-checked proof"] A green checkmark stamps next to the
   theorem; briefly show a real `lake build` success line.
3. [SYNC: "the proof has to hold at every single commit"] The theorem shrinks
   to a corner badge (it stays there for the rest of the video as a persistent
   HUD element, glowing green). Behind it, a stylized git commit graph starts
   scrolling horizontally, each commit node flashing green as it passes a
   checkmark gate.
4. One commit node flashes red and bounces back off the gate (a rejected
   optimization). [No VO reference; visual gag for attentive viewers.]

---

## Scene 3 — The chart, and the honest version of the claim (1:35–3:05)

**VO:**

> Here's the result, and let me be honest about the whole field straight
> away. Every DEFLATE library has a level knob trading speed against
> compression; sweep it and you get a curve. Up is faster, left is smaller
> output. This chart has everyone on it, and libdeflate, hand-tuned C with
> SIMD, is comfortably ahead of the pack. We can't touch SIMD from Lean
> today. So no, I'm not really claiming Lean is faster than Rust in general.
> The claim is narrower, and I think more interesting.
>
> Watch the red lean-zip curve against the green Rust one. The red curve is
> animated over the project's git history: about a hundred performance
> commits, each landing only if the proof still held. It starts far below,
> and then it climbs and pushes left, until at the default level and above
> the Rust curve is dominated: lean-zip compresses faster and smaller.
>
> I still can't quite believe it. The rest of this video is the archaeology
> of that animation: where the big moves actually came from.

**SB:**

1. Full-screen: the static full-field Pareto chart
   (`bench/graphs/silesia_compress_pareto.svg`), all libraries labelled.
   Animate axis annotations first: an arrow up labelled "faster", an arrow
   left labelled "smaller output". [SYNC: "Up is faster, left is smaller
   output"]
2. Callout pin on libdeflate's curve: "C + SIMD, the ceiling".
   [SYNC: "comfortably ahead of the pack"]
3. [SYNC: "The claim is narrower"] All curves except native red and
   miniz_oxide green fade to faint grey (they stay faintly visible; we are
   not hiding the field).
4. The red curve rewinds to frame 1 of the history animation (rebuilt from
   `bench/pareto_history.py` data; the interactive
   `bench/graphs/silesia_compress_pareto_history.html` player has per-frame
   commit info for callouts). Play the history at ~0.4s/frame with a corner
   ticker of commit hashes and dates. [SYNC: "animated over the project's
   git history"]
5. [SYNC: "the Rust curve is dominated"] Pause on the final frame; shade the
   region of levels where red is strictly up-and-left of green; pulse it.
6. Hold the final frame as the VO closes; the shading fades but the two
   curves remain.

---

## Scene 4 — Fifty seconds of DEFLATE (3:05–4:00)

**VO:**

> To follow the story you need exactly two ideas, one from 1977 and one from
> 1952.
>
> Idea one is LZ77: repeated text isn't stored twice. The second occurrence
> is a back-reference, a pair saying "go back this distance, copy this
> length". Finding and choosing matches is where all the cleverness lives.
>
> Idea two is Huffman coding: frequent symbols get short bit codes, and rare
> ones get long codes. DEFLATE splits the output into blocks, and each block
> carries its own Huffman code, fitted to its own statistics.
>
> The three levers are match finding, match choosing, and where you cut the
> blocks. Hold onto those, because they organise everything that follows.

**SB:**

1. A line of large monospace text: `the cat sat on the mat because the cat
   was tired`. Second `the cat` highlights; an arc sweeps backward to the
   first occurrence; the text collapses to
   `the cat sat on the mat because ⟨dist=31, len=8⟩ was tired`.
   [SYNC: "go back this distance, copy this length"]
2. Transition: the sentence's letters fall into a frequency histogram;
   frequent letters compress into short binary codes, rare into long
   (`e → 010`, `q → 111011010` style pairs). Keep this brief and pretty; no
   tree-building algorithm. [SYNC: "short bit codes"]
3. The stream view: a long ribbon divided into two blocks, each with its own
   miniature Huffman tree floating above it. [SYNC: "each block carries its
   own Huffman code"]
4. Three labels stamp onto the ribbon: FIND MATCHES / CHOOSE MATCHES / CUT
   BLOCKS. These labels are reused as chapter cards in Scenes 6–9.
   [SYNC: "Hold onto those"]

---

## Scene 5 — How the agents worked: reading libdeflate (4:00–4:45)

**VO:**

> One more thing before the algorithms, because it surprised me. The agents
> did what a good engineer would do: they read the masters. The planning
> issues cite the C source of zlib and libdeflate by file and line number,
> like citations in a paper. They read the mature implementation, ported the
> idea, measured it on real corpora, and kept it or rejected it, with the
> rejections recorded next to the adoptions.
>
> So this isn't AI inventing compression from nothing. It's a careful,
> receipted transplant of the best ideas in the field, into a language where
> every transplant has to keep a theorem alive.

**SB:**

1. A real screenshot-style rendering of GitHub issue #2742 ("dual hash4+hash3
   match finder"), scrolling to the section headed "What libdeflate does
   (hc_matchfinder.h:112-333)". Circle the file:line citation.
   [SYNC: "by file and line number"]
2. A four-step loop diagram: READ → PORT → MEASURE → KEEP/REJECT, drawn as a
   cycle. On "reject", two real examples tick past as strikethrough text:
   "pos+2 lookahead: ≤0.06%, rejected", "nice_match_length 10/14: regressed,
   reverted". [SYNC: "rejections recorded next to the adoptions"]
3. The theorem badge pulses. [SYNC: "keep a theorem alive"]

---

## Scene 6 — CHOOSE MATCHES, part one: lazy matching (4:45–6:00)

**VO:**

> The oldest idea is zlib's lazy matching, from 1995. Before committing to a
> match, the parser peeks one position ahead, and if a longer match starts
> there, it emits one literal and takes that instead.
>
> The textbook version failed: on some large text files it made the output
> twenty-two percent larger, because a longer match that is much farther
> away costs more in distance bits than it saves in length. The project
> first patched this with a cautious guard, deferring only to matches that
> were longer and no farther. Four weeks later, the guard was replaced with
> libdeflate's cost formula, which simply asks whether the length gain pays
> for the extra distance bits. Here is libdeflate's C, and here is the same
> rule in Lean.
>
> The correctness proof never mentions the rule at all: whatever the
> heuristic picks is re-verified before it's emitted, so the theorem is
> quantified over the heuristic. That design is what made this churn safe.

**SB:**

1. Chapter card: the Scene 4 ribbon with CHOOSE MATCHES highlighted (2s).
2. **The idea.** Text ribbon with a cursor: a greedy bracket `[the_cat]`
   (7 long) snaps on; scrub-back effect; the cursor steps one byte right; a
   longer bracket `[he_catalogue]` (12 long) glows beneath. The greedy
   bracket dissolves; a single literal `t` pops out; the long bracket takes
   over. [SYNC: "emits one literal and takes that instead"]
3. **The failure, fast.** A `dickens` file icon with a size bar; eager
   deferrals to far matches stretch a red "distance bits" meter; the bar
   grows to +22%, flashing red. A gate labelled "longer and no farther?"
   drops in and the bar shrinks below baseline. Keep this to ~10 seconds
   total. [SYNC: "twenty-two percent larger"]
4. **The morph (signature animation).**
   - Left panel: real libdeflate C from `lib/deflate_compress.c` (commit
     `b122c8b`, the lazy accept region cited in issue #2765 as lines
     2738-2767); highlight the arithmetic comparing the `4 * len` gain
     against `bsr32` of the two offsets.
   - The C tokens float apart and re-assemble as the real Lean
     (`Zip/Native/Deflate.lean:1382`):
     ```lean
     @[inline] def lazyAcceptCost (len1 dist1 len2 dist2 : Nat) : Bool :=
       decide (len1 < len2) && decide (4 * (len2 - len1) + dist1.log2 > 2 + dist2.log2)
     ```
   - Matched sub-expressions travel visibly (`4 * Δlen` → `4 * (len2 - len1)`,
     `bsr32(offset)` → `dist1.log2`); parts with no C counterpart materialize
     in a different colour, captioned "not a transliteration: Nat subtraction
     truncates, so the inequality is rearranged".
     [SYNC: "here is the same rule in Lean"]
   - Small caption under the finished Lean: "−0.4% to −0.9% at every lazy
     level (Silesia)".
5. **The proof point.** A magnifying glass at the emission point re-checks
   the chosen match bytes against the window and stamps green; the theorem
   badge glows. [SYNC: "re-verified before it's emitted"]

---

## Scene 7 — CUT BLOCKS: entropy divergence, and my favourite bug (6:00–7:10)

**VO:**

> A DEFLATE stream can start a fresh Huffman code at any block boundary, and
> the question is where to cut. lean-zip used to cut every so many tokens,
> which is safe but statistically blind. The fix, ported from libdeflate
> down to its constants, is to watch the statistics: keep one histogram for
> the block so far and one for the recent past, and when they diverge, cut
> and fit a fresh code. This was the single biggest ratio lever in the whole
> history, and by construction it cannot regress: both partitions are sized
> in exact bits, and the smaller one wins.
>
> The same pull request contains my favourite bug of the project. A new test
> produced output that our verified decoder accepted and zlib rejected: the
> length-limiter had been emitting incomplete Huffman codes. The theorem
> isn't wrong; it's precise. It says we can decode our own output, and it
> says nothing about everyone else. That's what conformance tests against
> zlib are for, and lean-zip runs them on everything.

**SB:**

1. Chapter card: CUT BLOCKS (2s).
2. **The heuristic in one shot.** The token ribbon as coloured confetti
   (10 class tints); the palette visibly shifts partway (prose into digits).
   Above, two live 10-bin histograms ("block so far" / "last 512") breathe
   together, then diverge at the regime change; a divergence gauge fills and
   crosses its threshold; a cut line slams down; a fresh miniature Huffman
   tree grows over the new block. A translucent 32 KiB history ribbon flows
   uninterrupted under the cut, with one back-reference arc reaching across
   it. [SYNC: "cut and fit a fresh code"]
3. Quick caption stamp, no dedicated visual: "sized in exact bits; the
   smaller partition wins". [SYNC: "cannot regress"]
4. **Bug interlude (~20s).** Style shift: darker, single spotlight. A small
   Huffman tree grows with one dangling dashed branch, captioned "incomplete
   code". Two decoder doors: `lean-zip inflate` (opens, green, theorem badge)
   and `zlib inflate` (slams, red REJECTED stamp). The roundtrip theorem
   reappears with `inflate` circled and annotated "OUR decoder".
   [SYNC: "It says we can decode our own output"]

---

## Scene 8 — CHOOSE MATCHES, part two: compression as a shortest path (7:10–8:35)

**VO:**

> Neither greedy nor lazy can plan ahead, and the last few percent of
> compression comes from planning the whole parse. There's a beautiful way
> to say it: every byte position is a node, literals and matches are edges
> jumping over the bytes they cover, and each edge is weighted by the bits
> it would cost. The best parse is the cheapest path, and the parser finds
> it backward, recording at each node the cheapest cost to the end.
>
> There's a catch, and it's my favourite part: the edge weights depend on
> the answer. A symbol's Huffman cost depends on how often it's used, which
> depends on the parse you haven't chosen yet. So the parser solves once
> with generic costs, refits the costs to its own parse, and solves again,
> and you can watch the path shift.
>
> And here the proof does something I find genuinely elegant: nothing. The
> dynamic program is untrusted advice. Every match it proposes is
> re-verified by proven code before emission, and bad advice falls back to a
> literal. Validity is proven; optimality is measured. At landing, this
> pushed lean-zip's best Silesia ratio past anything zlib produces.

**SB:**

1. Chapter card: CHOOSE MATCHES, "part two" sub-label (2s).
2. **Graph construction.** A short visible byte string (~20 chars) on a
   baseline; gaps become nodes; literal edges hop node-to-node with small
   bit costs; match arcs jump over spans with their costs. Build
   incrementally with the VO. [SYNC: "The best parse is the cheapest path"]
3. **Backward DP.** A wave sweeps right-to-left; each node lights up with
   its cost-to-end as the wave passes, briefly flashing the min() of its
   outgoing edges. This is the 3blue1brown moment; give it room. The optimal
   path then traces forward in native red.
4. **The fixpoint.** The chosen path's tokens fall into a histogram; the
   histogram feeds back into the edge labels, which visibly change; the
   backward wave re-runs fast; the red path re-traces and shifts, with a
   ghost of the old path for contrast. [SYNC: "watch the path shift"]
5. **Untrusted advice, one beat.** The path's tokens march through a
   checkpoint labelled with the real emitter code (`countMatch` + guards,
   a few highlighted lines from `Zip/Native/DeflateParse.lean`); one
   glitched token fails and is swapped for a literal, stream unbroken; the
   theorem badge glows. [SYNC: "bad advice falls back to a literal"]
6. Closing sting: the Pareto chart zoomed on the high-ratio end, the native
   top-level point sliding left past the end of the zlib curve.
   [SYNC: "past anything zlib produces"]

---

## Scene 9 — FIND MATCHES: the speed montage (8:35–9:35)

**VO:**

> Act one of the history moved the curve left, and paid speed for it. Act
> two bought the speed back, in dozens of commits proven not to change a
> single output byte. Here are four favourites.
>
> Hashing four bytes instead of three shattered the match finder's
> overloaded buckets, and that one commit made the default level fifty-four
> percent faster. A one-byte prefilter rejects candidates that cannot
> possibly win before the expensive comparison ever runs. The match extender
> compares eight bytes at once, using XOR and count-trailing-zeros to find
> the first difference, and the proof that it equals the byte loop goes
> through bv_decide. And the distinctly Lean chapter is unboxing: level one
> nearly doubled just by moving the hot loops off boxed integers onto raw
> machine words.

**SB:**

Four vignettes, ~12s each, hard cuts, consistent scoreboard stings.

1. **Hash4.** The `the` bucket as one grotesquely long chain a walker dot
   trudges down; switch to 4 bytes and the chain shatters into many short
   ones; the walker finishes instantly. Sting: "+54% at L6".
   [SYNC: "shattered"]
2. **Prefilter.** Candidates queue for a byte-by-byte comparison tunnel; a
   checkpoint sign reads "byte at offset bestLen?"; most flash red and drop
   through a trapdoor stamped `countMatch_le_of_byte_ne`. Sting: "+26% at
   L6, byte-identical".
3. **XOR + ctz.** Two 8-byte strips pack into two 64-bit words; XOR cancels
   matching bits in a wave; the first mismatching bit glows; a counter
   counts trailing zeros, ">> 3" converts to a byte index, an arrow lands on
   exactly that byte. Sting: `bv_decide ✓`.
4. **Unboxing.** A number as a gift-boxed parcel on the heap, repeatedly
   unwrapped and rewrapped by a slow loop; cut to the same number as raw
   bits in a register, loop spinning fast. Behind it, the history frames
   where L1 jumps from 20 to 41 MB/s. Sting: "L1 ×2, same algorithm".

---

## Scene 10 — Three shapes of safety (9:35–10:15)

**VO:**

> Step back, and every one of those hundred commits used a proof in one of
> exactly three ways.
>
> The first is to keep correctness independent of the heuristic. Accept
> rules, cut selectors, and probe depths are quantified out of the theorems,
> so agents can churn them freely. The proof says every choice is safe; the
> benchmark says which is good.
>
> The second is to treat the optimizer as untrusted advice and prove the
> checker. The dynamic program is unverified, but the emitter that re-checks
> it is not.
>
> The third is to prove the fast kernel equal to the simple one, bit for
> bit, keeping the simple one as the specification.
>
> That taxonomy, not any single trick, is why you can let AI optimize a
> compressor without reviewing the hot loops. Each shape is a precise answer
> to the question: what exactly does "didn't break anything" mean?

**SB:**

1. Three panels slide in side by side, each a minimal icon distilled from an
   earlier scene: the deferral gate with a `∀ heuristic` quantifier drawn
   over it (Scene 6); the DP path feeding through the `countMatch`
   checkpoint (Scene 8); two loops with an `=` sign and the `bv_decide`
   stamp (Scene 9).
2. As VO enumerates, each panel highlights in turn; the others dim.
3. All three panels shrink into the corner theorem badge, which expands once
   to fill the screen. [SYNC: "what exactly does 'didn't break anything'
   mean?"]

---

## Scene 11 — Outro: recap and close (10:15–10:50)

**VO:**

> So that's how a verified compressor caught the Rust curve: better
> decisions first, then provably identical speed. The honest chart from the
> start still stands, and libdeflate is still the ceiling. What the
> experiment shows is that a verified implementation got competitive with
> fast native code, and that all of the optimization was delegated to AI
> agents safely, because a theorem defined what they weren't allowed to
> break.
>
> The proofs weren't the finish line. They were the reason we could go fast.

**SB:**

1. Replay the last ~3 seconds of the history animation over the faint full
   field from Scene 3, ending on the dominance shading. The libdeflate
   callout pin from Scene 3 briefly reappears. [SYNC: "libdeflate is still
   the ceiling"]
2. [SYNC: "The proofs weren't the finish line"] The chart fades to black
   except the theorem badge, which drifts to center and holds.
3. End card: repository URL, blog post links, "benchmarks: silesia.tar,
   methodology in bench/README.md". Credits.

---

## Production notes

- **Assets that already exist:** the two Pareto SVGs and the history
  animation data (`bench/pareto_history.py --html` produces a scrubber player
  with per-frame commit metadata, useful for the Scene 3 ticker); the
  before/after zoom graph in the PR #2776 comment thread; all code snippets
  (real paths cited inline above).
- **Assets to pull:** libdeflate source at commit `b122c8b` for Scene 6
  (verify the exact line ranges named in issues #2765 and #2742 against that
  commit before animating; the issue citations are the source of truth).
- **Assets to record:** the Scene 1 terminal race (real timings, asciinema).
- **Numbers discipline:** every scoreboard sting uses the paired measurement
  from the corresponding PR, not subtraction of adjacent animation frames
  (some frames bundle several changes; the Scene 7 PR in particular mixes
  the splitter with the length-limiter fix).
- **Runtime flexibility:** if the video needs to come in under 10 minutes,
  cut Scene 5 first, then the Scene 8 untrusted-advice beat (Scene 10's
  middle panel covers the same idea). Scene 3's disclosure and Scene 10's
  taxonomy are load-bearing; do not cut them.
