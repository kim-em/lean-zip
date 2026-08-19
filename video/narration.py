"""Voice-over text per scene, segmented into timing cues.

Each scene maps to an ordered list of (cue_key, text). The build generates one
WAV per cue, measures it, and writes <Scene>_cues.json with narration-relative
start times; scenes schedule beats with CueScene.at_cue(key). Text is verbatim
from video.md (rev: 1069 words, 28 SYNC anchors); only the segmentation is
ours. Scenes not yet converted to cue timing carry a single "all" cue.
"""

NARRATION = {
    "ColdOpenScene": [
        ("serious", "I can't possibly be serious, can I, claiming that Lean "
                    "is faster than Rust?"),
        ("show", "Let me show you something. On the left is miniz_oxide, the "
                 "standard Rust DEFLATE implementation. On the right is "
                 "lean-zip, written in Lean. They compress the same 212 "
                 "megabyte Silesia corpus at level six."),
        ("less_time", "Lean takes slightly less time,"),
        ("smaller", "and it produces a slightly smaller file."),
    ],
    "TheoremScene": [
        ("secret", "How is that even remotely possible? The secret is this."),
        ("theorem", "This theorem says that inflating what we deflate "
                    "returns the original input, exactly, at every "
                    "compression level."),
        ("proved", "It is tested, and it is proved."),
        ("agents", "That let Claude and Codex agents work unusually "
                   "autonomously. They changed the hot loops, measured, and "
                   "tried again,"),
        ("survive", "but the theorem had to survive every step."),
        ("limits", "It does not prove speed, ratio, or compatibility with "
                   "every decoder. It gives each optimization one strong "
                   "boundary it cannot cross."),
    ],
    "ParetoHistoryScene": [
        ("all", "Here is what came out of that process. Every compressor "
                "has a level knob that trades speed for compression. Sweep "
                "through the levels and you get a curve. Left is smaller. "
                "Up is faster. The green curve is miniz_oxide, written in "
                "Rust. The red curve replays lean-zip through the "
                "optimization history. It begins far below, then moves left "
                "and climbs. Rust stays faster at the low and middle "
                "settings. By the end, miniz_oxide levels 6 through 9 are "
                "dominated: lean-zip can compress both faster and smaller. "
                "I still can't quite believe it. There is an obvious "
                "objection. Nobody has subjected miniz_oxide to this same "
                "campaign, and I am sure it could improve too. There is "
                "also a more important chart. When we include the whole "
                "field, libdeflate, carefully tuned C with SIMD, remains in "
                "another league. This implementation does not use "
                "libdeflate's architecture-specific SIMD. So I am not "
                "claiming that Lean is faster than Rust in general. The "
                "claim is narrower. With enough tuning, an implementation "
                "in Lean can compete with implementations in fast "
                "languages. The unusual part is that much of the tuning can "
                "be delegated to agents because the theorem states what "
                "their changes are not allowed to break. What did the "
                "agents actually change?"),
    ],
    "DeflatePrimerScene": [
        ("all", "You only need two ideas to follow the archaeology. DEFLATE "
                "replaces repeated bytes with references that say, go "
                "backward this distance and copy this many bytes. "
                "Everything else is a literal. It then gives frequent "
                "symbols short Huffman codes, with a fresh code available "
                "at each block. That leaves three levers: find matches, "
                "choose matches, and cut blocks."),
    ],
    "LazyMatchingScene": [
        ("all", "A greedy parser takes the best match at the current byte. "
                "Following zlib, lazy matching looks one byte ahead. One "
                "literal can expose a much longer match. The obvious rule "
                "was to defer whenever the later match was longer. It was "
                "wrong. Some large text files became substantially larger "
                "because a farther reference can cost more distance bits "
                "than its extra length saves. The version that landed "
                "required the next match to be longer and no farther. Four "
                "weeks later, an adapted libdeflate rule asked whether the "
                "length gain would pay for the extra distance bits. "
                "chainWalk has already validated both candidates. The proof "
                "only needs the later one to be longer; the cost formula is "
                "opaque. A bad choice can waste bits, but it cannot invent "
                "a match."),
    ],
    "BlockSplittingScene": [
        ("all", "DEFLATE gives each block its own Huffman code. "
                "Shared-window splitting matched the input once, fitted "
                "each block separately, and still allowed references across "
                "boundaries. On large Silesia text files at level 9, output "
                "fell 15 to 20 percent. The cuts still came at a fixed "
                "cadence. Later, a libdeflate-style refinement compared the "
                "block-so-far histogram with each recent batch, normally "
                "512 tokens. When the statistics diverge, it proposes a "
                "boundary and a fresh code. Exact sizing then chose between "
                "the observed and fixed partitions. The same pull request "
                "exposed my favourite bug in the project. Our verified "
                "decoder accepted its output, but zlib rejected it. A "
                "broken length limiter had produced an incomplete Huffman "
                "code-length alphabet. The theorem was not wrong. It was "
                "precise. Our production inflate decoder can decode the "
                "output. External "
                "conformance is separate, so the zlib test found the gap. "
                "The missing completeness property soon became a theorem "
                "too."),
    ],
    "OptimalParsingScene": [
        ("all", "Greedy sees one position, and lazy sees two. Neither plans "
                "the whole parse. Put a node at every byte position. "
                "Literals move one node; matches jump over several. Give "
                "each edge an estimated bit cost, and compression becomes a "
                "shortest-path problem. The dynamic program works backward "
                "from the end. It adds each edge cost to the best known "
                "destination cost and keeps the cheapest choice. Huffman "
                "costs depend on the parse, so the weights depend on the "
                "answer. Following libdeflate's design, lean-zip solves "
                "with seed costs, refits them to that parse, and solves the "
                "graph again. Here, near-optimal means a minimum through "
                "cached candidates inside bounded 256 kilobyte regions with "
                "an estimated tail, not the best possible DEFLATE stream. "
                "Its arrays are untrusted advice. The emitter checks every "
                "match and falls back to a literal when necessary. The "
                "price was speed. Now the agents had to buy it back."),
    ],
    "SpeedMontageScene": [
        ("all", "Better decisions moved the curve left and often down. A "
                "long sequence of speed improvements moved it back up. Here "
                "are three. Hashing four bytes instead of three shattered "
                "overloaded match chains. That one commit made level 6 54 "
                "percent faster. The function was still called hash3. It "
                "now hashed four bytes. That experiment came from "
                "profiling. The later dual-table repair explicitly adapted "
                "libdeflate. A zlib-style prefilter checked one decisive "
                "byte and rejected candidates that could not possibly win. "
                "Survivors were compared eight bytes at a time using a "
                "libdeflate technique. XOR and count-trailing-zeros located "
                "the first differing byte directly."),
    ],
    "ProofShapesScene": [
        ("all", "These optimizations use three recurring shapes of proof. "
                "First, correctness can be independent of a ranking "
                "heuristic. Search validates match candidates, and block "
                "construction clamps cuts, before the heuristic's choice "
                "matters. Second, optimizer output can be untrusted advice. "
                "The dynamic program proposes a choice, and the proved "
                "emitter checks it. Third, a fast kernel can be proved "
                "exactly equal to a simple one. That is how the prefilter "
                "and word-at-a-time matcher keep byte-for-byte behaviour. "
                "The proof says which choices are safe. The benchmark says "
                "which choices are good."),
    ],
    "OutroScene": [
        ("all", "So the red curve caught the Rust curve at the "
                "high-compression levels. Better choices moved it left. "
                "Speed work moved it up. libdeflate is still the ceiling. "
                "The proof did not choose the optimizations. Profiles, "
                "upstream ideas, and benchmarks did. It was the ratchet "
                "that let the wins accumulate."),
    ],
}


def full_text(scene):
    return " ".join(text for _key, text in NARRATION[scene])
