"""Manim scenes for the lean-zip video.

One class per scene of video.md; class names match the keys in narration.py.
Rendered by build.sh under nix-shell (Manim Community v0.20.x).

Synced to video.md rev "1069 words / 28 SYNC anchors": cold-open cards from
the committed whole_tar_l6.json medians, two-library-first Pareto ordering,
four-point dominance comparison, BANANA_BANANA primer, chainWalk-validates-
first lazy scene, specified toy DP graph, three-vignette montage (unboxing
cut), pinned outro commits.
"""
import json
import math
from pathlib import Path

from manim import (
    WHITE, GREY_C, GREY_E, GREEN, YELLOW, BLUE, ORANGE, RED, TEAL,
    UP, DOWN, LEFT, RIGHT, ORIGIN,
    ArcBetweenPoints, Axes, Create, CurvedArrow, DashedLine, Dot, FadeIn,
    FadeOut, Flash, Indicate, Line, Rectangle, RoundedRectangle, Scene, Square,
    SurroundingRectangle, Text, Transform, TransformMatchingShapes, Underline,
    VGroup, VMobject, config,
)

HERE = Path(__file__).resolve().parent
REPO = HERE.parent

COLOURS = {
    "native": "#d62728", "zlib": "#1f77b4", "miniz_oxide": "#2ca02c",
    "libdeflate": "#9467bd", "go": "#8c564b", "js": "#e377c2",
    "zig": "#bcbd22", "ocaml": "#17becf",
}
LABELS = {
    "native": "lean-zip", "zlib": "zlib", "miniz_oxide": "miniz_oxide (Rust)",
    "libdeflate": "libdeflate", "go": "Go", "js": "JS", "zig": "Zig",
    "ocaml": "OCaml",
}
import sys
sys.path.insert(0, str(HERE))
from style import (  # noqa: E402
    BG, SURFACE, SURFACE_2, EDGE, INK, INK2, MUTED,
    OK, BAD, WARN, INFO, AMBER, VIOLET,
    FONT_TEXT, FONT_CODE, TITLE, H1, BODY, SMALL, MICRO,
    t, m, panel, code_block, chip, pill, rule_under,
)

PROOF_BLUE = INFO
MONO = FONT_CODE

config.background_color = BG


def roundtrip_glyph(size=18):
    """The compact, unboxed roundtrip glyph (video.md: no persistent rail;
    scenes summon this only when correctness enters the narration)."""
    label = m("inflate (deflate data) = data", size=size, color=INK2)
    check = m("✓", size=size, color=OK)
    return VGroup(label, check).arrange(RIGHT, buff=0.2)


THEOREM_SOURCE = """theorem inflate_deflateRaw (data : ByteArray) (level : UInt8)
    (maxOutputSize : Nat) (hsize : data.size ≤ maxOutputSize) :
    Zip.Native.Inflate.inflate (deflateRaw data level) maxOutputSize = .ok data :=
  (Zip.Native.Inflate.inflate_ok_iff_reference _ _ _).mpr
    (inflateReference_deflateRaw data level maxOutputSize hsize)"""


def theorem_code(font_size=19):
    """The real production-decoder capstone, pygments-highlighted."""
    from manim import Code
    return Code(
        code_string=THEOREM_SOURCE,
        language="lean4",
        add_line_numbers=False,
        formatter_style="github-dark",
        background="rectangle",
        background_config={
            "fill_color": SURFACE_2, "fill_opacity": 1.0,
            "stroke_color": EDGE, "stroke_width": 1.4,
            "corner_radius": 0.14,
        },
        paragraph_config={"font": FONT_CODE, "font_size": font_size},
    ).scale_to_fit_width(12.6)


class CueScene(Scene):
    """A scene whose beats schedule against the narration cue timeline.

    Reads out/audio/<Class>_cues.json (written by make_vo.py). at_cue(key)
    waits scene time up to the cue's narration-relative start; end_pad() waits
    out the remaining narration so the video never freezes early.
    """

    def setup(self):
        p = HERE / "out" / "audio" / f"{type(self).__name__}_cues.json"
        self._cues = {}
        if p.exists():
            for c in json.loads(p.read_text()):
                self._cues[c["key"]] = c

    @property
    def now(self):
        return float(getattr(self.renderer, "time", 0.0))

    def at_cue(self, key, offset=0.0):
        c = self._cues.get(key)
        if c is None:
            return
        target = c["start"] + offset
        if target > self.now + 1e-3:
            self.wait(target - self.now)

    def end_pad(self, tail=0.4):
        total = max((c["start"] + c["dur"] for c in self._cues.values()),
                    default=0.0)
        if total + tail > self.now:
            self.wait(total + tail - self.now)


def _load_history():
    return json.loads((HERE / "data" / "history.json").read_text())


class ColdOpenScene(Scene):
    """Scene 1: the race. Cards from the committed whole_tar_l6.json medians
    (chungus2, commit 696ce7f2), per video.md SB item 3; commands from the
    recorded race (same shape as blog.md's shell block)."""

    def construct(self):
        wt = json.loads(
            (REPO / "bench" / "results" / "whole_tar_l6.json").read_text())
        e2e = wt["end_to_end"]
        lean = {"cmd": "time deflate-lean silesia.tar",
                "wall_ms": e2e["lean"]["wall_ms_median"],
                "size": e2e["lean"]["size"]}
        rust = {"cmd": "time deflate-rust silesia.tar",
                "wall_ms": e2e["rust"]["wall_ms_median"],
                "size": e2e["rust"]["size"]}

        claim = t("Lean is faster than Rust", size=TITLE, color=INK,
                  weight="BOLD")
        qmark = t("?", size=TITLE, color=INK, weight="BOLD")
        qmark.next_to(claim, RIGHT, buff=0.08)
        group = VGroup(claim, qmark).move_to(ORIGIN)
        qmark.set_opacity(0)
        self.play(FadeIn(claim))
        self.wait(0.5)
        self.play(qmark.animate.set_opacity(1))
        self.wait(1.0)
        self.play(FadeOut(group))

        def pane(title, accent, x_shift):
            box = panel(6.3, 4.0).shift(x_shift + DOWN * 0.5)
            head = chip(title, accent, size=SMALL)
            head.next_to(box.get_top(), DOWN, buff=0.3)
            head.align_to(box.get_left() + RIGHT * 0.45, LEFT)
            return box, head

        rust_box, rust_head = pane("miniz_oxide  (Rust)",
                                   COLOURS["miniz_oxide"], LEFT * 3.45)
        lean_box, lean_head = pane("lean-zip  (Lean)",
                                   COLOURS["native"], RIGHT * 3.45)
        self.play(FadeIn(rust_box), FadeIn(rust_head),
                  FadeIn(lean_box), FadeIn(lean_head))

        def cmdline(box, head, s):
            txt = m("$ " + s, size=18, color=INK)
            txt.next_to(head, DOWN, buff=0.35)
            txt.align_to(head, LEFT)
            return txt

        rust_cmd = cmdline(rust_box, rust_head, rust["cmd"])
        lean_cmd = cmdline(lean_box, lean_head, lean["cmd"])
        self.play(FadeIn(rust_cmd), FadeIn(lean_cmd))
        self.wait(0.8)

        def card(cmd, d):
            size_line = m(f"{d['size']}", size=24, color=INK)
            time_line = m(f"real  0m{d['wall_ms'] / 1000:.3f}s", size=24,
                          color=INK)
            g = VGroup(size_line, time_line).arrange(DOWN, aligned_edge=LEFT,
                                                     buff=0.28)
            g.next_to(cmd, DOWN, buff=0.55)
            g.align_to(cmd, LEFT)
            return g

        rust_res = card(rust_cmd, rust)
        lean_res = card(lean_cmd, lean)
        src = t("bench/results/whole_tar_l6.json · chungus2 · 696ce7f2 ·"
                " median of 9 runs", size=MICRO, color=MUTED)
        src.move_to(DOWN * 3.35)
        self.play(FadeIn(rust_res), FadeIn(lean_res), FadeIn(src))
        self.wait(1.0)

        t_rule = rule_under(lean_res[1], OK)
        s_rule = rule_under(lean_res[0], OK)
        self.play(Create(t_rule))
        self.wait(0.8)
        self.play(Create(s_rule))
        self.wait(1.2)

        everything = VGroup(rust_box, rust_head, lean_box, lean_head, rust_cmd,
                            lean_cmd, rust_res, lean_res, t_rule, s_rule, src)
        title = t("Why Lean is faster than Rust", size=H1, color=INK,
                  weight="BOLD")
        title.move_to(UP * 2.6)
        self.play(everything.animate.set_opacity(0.15), FadeIn(title))
        self.wait(2.0)


class TheoremScene(CueScene):
    """Scene 2, cue-timed: the real capstone theorem (pygments), the byte
    ribbon through the production decoder, the compact glyph, the ratchet."""

    def construct(self):
        # "The secret is this." -> the real theorem
        self.at_cue("secret", offset=1.2)
        block = theorem_code().move_to(UP * 1.4)
        self.play(FadeIn(block, shift=UP * 0.4), run_time=1.2)

        # "inflating what we deflate returns the original input"
        self.at_cue("theorem")
        ribbon = VGroup(*[Square(side_length=0.2, fill_color=AMBER,
                                 fill_opacity=0.85, stroke_opacity=0)
                          for _ in range(12)])
        ribbon.arrange(RIGHT, buff=0.07).move_to(DOWN * 1.6 + LEFT * 3.6)
        rib2 = ribbon.copy().move_to(DOWN * 1.6 + RIGHT * 3.6)
        arrow = CurvedArrow(ribbon.get_right() + RIGHT * 0.25,
                            rib2.get_left() + LEFT * 0.25, angle=-0.5,
                            color=INK2, tip_length=0.16, stroke_width=2.5)
        alab = t("deflateRaw, then Inflate.inflate", size=MICRO, color=INK2)
        alab.next_to(arrow, DOWN, buff=0.18)
        self.play(FadeIn(ribbon))
        self.play(Create(arrow), FadeIn(alab))
        self.play(FadeIn(rib2, lag_ratio=0.05))

        # "It is tested, and it is proved."
        self.at_cue("proved")
        check = m("✓", size=30, color=OK).next_to(block, RIGHT, buff=0.4)
        self.play(FadeIn(check, scale=1.6))
        self.play(FadeOut(ribbon), FadeOut(rib2), FadeOut(arrow),
                  FadeOut(alab))

        # agents + the ratchet loop
        self.at_cue("agents")
        glyph = roundtrip_glyph().to_corner(UP + RIGHT, buff=0.5)
        self.play(FadeOut(check), TransformMatchingShapes(block, glyph),
                  run_time=1.2)
        gate = DashedLine(UP * 1.3, DOWN * 1.7, color=OK,
                          stroke_width=2.5).move_to(RIGHT * 2)
        gate_label = t("profile · change · measure · check roundtrip",
                       size=SMALL, color=INK2).move_to(UP * 1.9)
        self.play(Create(gate), FadeIn(gate_label))
        cards = VGroup(*[
            RoundedRectangle(width=0.4, height=0.4, corner_radius=0.08,
                             stroke_color=EDGE, stroke_width=1.4,
                             fill_color=SURFACE, fill_opacity=1).move_to(
                LEFT * (6 + 1.3 * i) + DOWN * 0.2)
            for i in range(7)
        ])
        self.add(cards)
        self.play(cards.animate(run_time=4, rate_func=lambda t: t)
                  .shift(RIGHT * 11))

        # "but the theorem had to survive every step" -> the bounce
        self.at_cue("survive")
        accepted = VGroup(*[
            RoundedRectangle(width=0.4, height=0.4, corner_radius=0.08,
                             stroke_color=OK, stroke_width=1.4,
                             fill_color=SURFACE, fill_opacity=1).move_to(
                RIGHT * (3.2 + 0.55 * i) + DOWN * 0.2)
            for i in range(5)
        ])
        self.play(FadeIn(accepted, lag_ratio=0.15))
        bad = RoundedRectangle(width=0.4, height=0.4, corner_radius=0.08,
                               stroke_color=BAD, stroke_width=1.8,
                               fill_color=SURFACE,
                               fill_opacity=1).move_to(LEFT * 5 + DOWN * 0.2)
        self.add(bad)
        self.play(bad.animate(run_time=1.2, rate_func=lambda t: t)
                  .move_to(RIGHT * 1.75 + DOWN * 0.2))
        self.play(Flash(bad.get_center(), color=BAD, line_length=0.15))
        self.play(bad.animate(run_time=0.9).move_to(LEFT * 1 + DOWN * 1.4)
                  .set_opacity(0))

        # the limits, beside the glyph
        self.at_cue("limits")
        limits = VGroup(
            t("not speed", size=SMALL, color=INK2),
            t("·", size=SMALL, color=MUTED),
            t("not ratio", size=SMALL, color=INK2),
            t("·", size=SMALL, color=MUTED),
            t("not every decoder", size=SMALL, color=INK2),
        ).arrange(RIGHT, buff=0.35)
        limits.next_to(glyph, DOWN, buff=0.3).align_to(glyph, RIGHT)
        self.play(FadeIn(limits))
        self.end_pad()


class ParetoHistoryScene(Scene):
    """Scene 3, video.md order: two-library history first, four dominance
    comparisons, the dormant loop, then the full field and the two claims."""

    X_RANGE = (0.29, 0.45, 0.05)
    Y_RANGE = (-0.5, 2.7, 1.0)

    def curve(self, axes, pts, colour, width=3.0):
        line = VMobject(color=colour, stroke_width=width, fill_opacity=0)
        coords = [
            axes.coords_to_point(p["ratio"], math.log10(p["mbps"])) for p in pts
        ]
        line.set_points_as_corners(coords)
        dots = VGroup(*[Dot(c, color=colour, radius=0.045) for c in coords])
        return VGroup(line, dots)

    def construct(self):
        data = _load_history()
        axes = Axes(
            x_range=list(self.X_RANGE), y_range=list(self.Y_RANGE),
            x_length=10.5, y_length=5.4, tips=False,
            axis_config={"color": GREY_C, "include_ticks": True},
        ).shift(DOWN * 0.5)
        x_label = Text("compression ratio (smaller is better)",
                       font_size=20, color=GREY_C).next_to(axes, DOWN, buff=0.15)
        y_label = Text("compress MB/s (log)", font_size=20, color=GREY_C)
        y_label.rotate(math.pi / 2).next_to(axes, LEFT, buff=0.15)
        self.play(Create(axes), FadeIn(x_label), FadeIn(y_label))

        left_arr = Text("← smaller", font_size=24, color=WHITE)
        left_arr.move_to(axes.coords_to_point(0.312, -0.3))
        up_arr = Text("↑ faster", font_size=24, color=WHITE)
        up_arr.move_to(axes.coords_to_point(0.44, 2.35))
        self.play(FadeIn(left_arr))
        self.play(FadeIn(up_arr))
        self.wait(0.5)

        # two libraries only: green frontier, then the red history replay
        miniz = self.curve(axes, data["reference"]["miniz_oxide"],
                           COLOURS["miniz_oxide"], 4.0)
        mlab = Text("miniz_oxide (Rust)", font_size=18,
                    color=COLOURS["miniz_oxide"])
        mlab.next_to(miniz, UP + RIGHT, buff=-0.8)
        self.play(Create(miniz), FadeIn(mlab))

        frames = data["history"]
        ticker = Text(frames[0]["commit"] + "  " + frames[0]["date"],
                      font=MONO, font_size=17, color=GREY_C)
        ticker.to_corner(DOWN + RIGHT, buff=0.3)
        moving = self.curve(axes, frames[0]["levels"], COLOURS["native"])
        self.play(FadeIn(moving), FadeIn(ticker))
        for i, fr in enumerate(frames[1:], start=1):
            target = self.curve(axes, fr["levels"], COLOURS["native"])
            new_ticker = Text(fr["commit"] + "  " + fr["date"],
                              font=MONO, font_size=17, color=GREY_C)
            new_ticker.to_corner(DOWN + RIGHT, buff=0.3)
            if i % 6 == 0:
                ghost = moving.copy()
                ghost[0].set_stroke(opacity=0.1)
                ghost[1].set_fill(opacity=0.1).set_stroke(opacity=0)
                self.add(ghost)
            self.play(Transform(moving, target),
                      Transform(ticker, new_ticker),
                      run_time=0.16, rate_func=lambda t: t)
        self.wait(0.5)

        # four explicit dominance comparisons, green L6-L9 to the red point
        # that beats each (SB item 5: no continuous shading)
        native_pts = data["reference"]["native"]
        miniz_pts = data["reference"]["miniz_oxide"]
        guides = VGroup()
        for lvl in (6, 7, 8, 9):
            g = next(p for p in miniz_pts if p["level"] == lvl)
            beats = [p for p in native_pts
                     if p["ratio"] <= g["ratio"] and p["mbps"] >= g["mbps"]]
            if not beats:
                continue
            r = max(beats, key=lambda p: p["mbps"])
            a = axes.coords_to_point(g["ratio"], math.log10(g["mbps"]))
            b = axes.coords_to_point(r["ratio"], math.log10(r["mbps"]))
            guides.add(Line(a, b, color=WHITE, stroke_width=2.5))
        for gl in guides:
            self.play(Create(gl), run_time=0.4)
            self.play(Flash(gl.get_end(), color=COLOURS["native"],
                            line_length=0.15), run_time=0.3)
        self.wait(1.0)

        # the dormant optimization loop behind the Rust curve (the objection)
        dormant = VGroup(*[Square(side_length=0.3, color=GREY_E)
                           for _ in range(4)])
        dormant.arrange(RIGHT, buff=0.25)
        dormant.move_to(axes.coords_to_point(0.415, 1.9))
        dlab = Text("not run for Rust", font_size=15, color=GREY_E)
        dlab.next_to(dormant, DOWN, buff=0.1)
        self.play(FadeIn(dormant), FadeIn(dlab))
        self.wait(1.0)

        # zoom out to the full field
        rest = VGroup()
        legend = VGroup()
        for name in ("libdeflate", "zlib", "go", "zig", "js", "ocaml"):
            pts = data["reference"].get(name)
            if not pts:
                continue
            c = self.curve(axes, pts, COLOURS.get(name, GREY_C), 2.5)
            rest.add(c)
            legend.add(Text(LABELS.get(name, name), font_size=16,
                            color=COLOURS.get(name, GREY_C)))
        legend.arrange(DOWN, aligned_edge=LEFT, buff=0.1)
        legend.move_to(RIGHT * 5.7 + DOWN * 1.3)
        self.play(FadeIn(rest), FadeIn(legend), FadeOut(dormant), FadeOut(dlab))
        ld = data["reference"]["libdeflate"]
        top = max(ld, key=lambda p: p["mbps"])
        pin = Text("C + SIMD: another league", font_size=20,
                   color=COLOURS["libdeflate"])
        pin.next_to(axes.coords_to_point(top["ratio"], math.log10(top["mbps"])),
                    UP, buff=0.3).shift(LEFT * 1.6)
        simd = Text("[SIMD]", font=MONO, font_size=15,
                    color=COLOURS["libdeflate"]).next_to(pin, DOWN, buff=0.08)
        self.play(Indicate(rest[0]), FadeIn(pin), FadeIn(simd))
        self.wait(1.5)

        # the two claims (clear the lower band first so nothing collides)
        self.play(FadeOut(left_arr), FadeOut(up_arr), FadeOut(x_label),
                  legend.animate.set_opacity(0.35))
        c1 = Text("Lean is generally faster than Rust", font_size=20,
                  color=GREY_C).move_to(DOWN * 3.2 + LEFT * 3.6)
        strike = Line(c1.get_left() + LEFT * 0.1, c1.get_right() + RIGHT * 0.1,
                      color=RED)
        c2 = Text("a tuned Lean implementation can be competitive,\n"
                  "and proofs make agent optimization tractable",
                  font_size=20, color=WHITE).move_to(DOWN * 3.2 + RIGHT * 3.2)
        self.play(FadeIn(c1))
        self.play(Create(strike), FadeIn(c2))
        self.wait(2.0)


class DeflatePrimerScene(Scene):
    """Scene 4: BANANA_BANANA, Huffman codes, the three levers."""

    def construct(self):
        s = "BANANA_BANANA"
        line = Text(s, font=MONO, font_size=34, color=WHITE).move_to(UP * 1.6)
        line[6].set_color(AMBER)
        for i in range(7, 13):
            line[i].set_color(VIOLET)
        self.play(FadeIn(line))
        first_box = SurroundingRectangle(line[0:6], color=GREY_C, buff=0.06)
        second_box = SurroundingRectangle(line[7:13], color=VIOLET, buff=0.06)
        arc = CurvedArrow(second_box.get_top(), first_box.get_top(),
                          angle=1.0, color=VIOLET, tip_length=0.15)
        self.play(Create(second_box), Create(first_box))
        self.play(Create(arc))
        self.wait(0.8)
        token = Text("⟨distance 7, length 6⟩", font=MONO, font_size=28,
                     color=VIOLET)
        newline = VGroup(
            Text("BANANA", font=MONO, font_size=34, color=WHITE),
            Text("_", font=MONO, font_size=34, color=AMBER),
            token,
        ).arrange(RIGHT, buff=0.12).move_to(UP * 1.6)
        self.play(FadeOut(arc), FadeOut(first_box), FadeOut(second_box),
                  TransformMatchingShapes(line, newline))
        self.wait(1.2)

        bars = VGroup()
        freqs = [7, 5, 4, 3, 2, 1]
        for i, h in enumerate(freqs):
            b = Rectangle(width=0.5, height=h * 0.24, fill_color=BLUE,
                          fill_opacity=0.8, stroke_opacity=0)
            b.move_to(DOWN * 1.1 + RIGHT * (i * 0.7 - 4.2) + UP * (h * 0.12))
            bars.add(b)
        codes = VGroup(
            Text("frequent → 010", font=MONO, font_size=22, color=WHITE),
            Text("rare     → 111011010", font=MONO, font_size=22, color=GREY_C),
        ).arrange(DOWN, aligned_edge=LEFT).next_to(bars, RIGHT, buff=0.9)
        self.play(FadeIn(bars, lag_ratio=0.1), FadeIn(codes))
        self.wait(1.5)
        self.play(FadeOut(bars), FadeOut(codes), FadeOut(newline))

        levers = VGroup(
            Text("FIND MATCHES", font_size=30, color=TEAL),
            Text("CHOOSE MATCHES", font_size=30, color=VIOLET),
            Text("CUT BLOCKS", font_size=30, color=ORANGE),
        ).arrange(RIGHT, buff=1.0).move_to(DOWN * 0.4)
        self.play(FadeIn(levers, lag_ratio=0.3, shift=UP * 0.3))
        self.play(Indicate(levers[1], color=VIOLET))
        self.wait(2.5)


class LazyMatchingScene(Scene):
    """Scene 5: chainWalk validates both candidates first, then the failed
    rule, the guard gates, and the stationary-panel idea-card provenance."""

    SAMPLE = "shift the cathode, the catalogue arrives"

    def construct(self):
        chapter = Text("CHOOSE MATCHES", font_size=22, color=VIOLET)
        chapter.to_corner(UP + LEFT, buff=0.6).shift(DOWN * 0.3)
        self.add(chapter)

        line = Text(self.SAMPLE, font=MONO, font_size=28, color=WHITE)
        line.move_to(UP * 1.7)
        self.play(FadeIn(line))

        squashed = self.SAMPLE.replace(" ", "").replace(",", "")
        g_start = squashed.index("thecathode")
        greedy = SurroundingRectangle(line[g_start:g_start + 6], color=VIOLET,
                                      buff=0.06)
        g_label = Text("match at p", font_size=19, color=VIOLET)
        g_label.next_to(line, UP, buff=0.35).shift(LEFT * 3)
        v1 = Text("chainWalk + countMatch ✓", font_size=15, color=PROOF_BLUE)
        v1.next_to(greedy, DOWN, buff=0.08)
        self.play(Create(greedy), FadeIn(g_label))
        self.play(FadeIn(v1))
        self.wait(1.0)

        l_start = squashed.index("hecathode")
        lazy = SurroundingRectangle(line[l_start:l_start + 8], color=VIOLET,
                                    buff=0.06)
        l_label = Text("longer match at p+1", font_size=19, color=VIOLET)
        l_label.next_to(line, UP, buff=0.35).shift(RIGHT * 3)
        v2 = Text("chainWalk + countMatch ✓", font_size=15, color=PROOF_BLUE)
        v2.next_to(lazy, DOWN, buff=0.35)
        lit = Text("t", font=MONO, font_size=28, color=AMBER)
        lit.next_to(line, DOWN, buff=0.75).shift(LEFT * 4.5)
        lit_tag = Text("one literal", font_size=16, color=AMBER)
        lit_tag.next_to(lit, DOWN, buff=0.1)
        self.play(Create(lazy), FadeIn(l_label), FadeIn(v2),
                  FadeIn(lit, shift=DOWN * 0.3), FadeIn(lit_tag))
        self.wait(1.5)
        self.play(FadeOut(VGroup(greedy, g_label, v1, lazy, l_label, v2, lit,
                                 lit_tag)))

        rule = Text("longer always wins", font_size=22, color=WHITE)
        stamp = Text("failed on large text", font_size=20, color=RED)
        rule.move_to(DOWN * 0.2 + LEFT * 3.5)
        stamp.next_to(rule, DOWN, buff=0.15)
        strike = Line(rule.get_left() + LEFT * 0.1,
                      rule.get_right() + RIGHT * 0.1, color=RED)
        self.play(FadeIn(rule), FadeIn(stamp))
        self.play(Create(strike))
        gates = VGroup(
            Text("LONGER?", font_size=20, color=WHITE),
            Text("NO FARTHER?", font_size=20, color=WHITE),
        ).arrange(RIGHT, buff=0.6).move_to(DOWN * 0.2 + RIGHT * 3.0)
        gate_boxes = VGroup(*[SurroundingRectangle(g, color=GREY_C, buff=0.12)
                              for g in gates])
        note = Text("guarded rule kept after corpus measurement",
                    font_size=16, color=GREY_C)
        note.next_to(gates, DOWN, buff=0.2)
        self.play(FadeIn(gates), Create(gate_boxes), FadeIn(note))
        self.wait(1.5)
        self.play(FadeOut(VGroup(rule, stamp, strike, gates, gate_boxes, note)))

        # stationary panels + neutral idea card (SB item 4)
        c_lines = [
            "/* libdeflate deflate_compress.c @ b122c8b */",
            "if (next_len >= cur_len &&",
            "    4 * (int)(next_len - cur_len) +",
            "    ((int)bsr32(cur_offset) -",
            "     (int)bsr32(next_offset)) > 2) {",
        ]
        c_block = VGroup(*[Text(l, font=MONO, font_size=17, color="#8ecae6")
                           for l in c_lines])
        c_block[0].set_color(GREY_C)
        c_block.arrange(DOWN, aligned_edge=LEFT, buff=0.12)
        c_block.move_to(DOWN * 1.5 + LEFT * 3.9)

        idea_t = Text("IDEA: length gain must pay distance cost",
                      font_size=17, color=YELLOW)
        idea_box = SurroundingRectangle(idea_t, color=YELLOW, buff=0.15)
        idea = VGroup(idea_box, idea_t).move_to(UP * 0.6)

        lean_lines = [
            "-- Zip/Native/Deflate.lean:1382",
            "@[inline] def lazyAcceptCost",
            "    (len1 dist1 len2 dist2 : Nat) : Bool :=",
            "  decide (len1 < len2) &&",
            "  decide (4 * (len2 - len1) + dist1.log2",
            "          > 2 + dist2.log2)",
        ]
        lean_block = VGroup(*[Text(l, font=MONO, font_size=17, color=WHITE)
                              for l in lean_lines])
        lean_block[0].set_color(GREY_C)
        lean_block.arrange(DOWN, aligned_edge=LEFT, buff=0.12)
        lean_block.move_to(DOWN * 1.5 + RIGHT * 3.9)

        self.play(FadeIn(c_block))
        self.play(FadeIn(idea, shift=UP * 0.3))
        self.play(FadeIn(lean_block))
        badges = VGroup(
            Text("C may accept equal length; Lean requires len1 < len2",
                 font_size=14, color=PROOF_BLUE),
            Text("signed subtraction moves right for Nat arithmetic",
                 font_size=14, color=PROOF_BLUE),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.08)
        badges.move_to(DOWN * 3.05 + RIGHT * 3.4)
        cap = Text("ported idea, not line-for-line code", font_size=16,
                   color=YELLOW).move_to(DOWN * 3.05 + LEFT * 3.9)
        meas = Text("paired 105 MB Silesia subset, levels 4-9:"
                    " 0.4% to 0.9% smaller", font_size=14, color=GREY_C)
        meas.next_to(cap, DOWN, buff=0.08)
        self.play(FadeIn(badges), FadeIn(cap), FadeIn(meas))
        self.wait(2.0)
        glyph = roundtrip_glyph(size=16).to_corner(UP + RIGHT, buff=0.5)
        self.play(FadeIn(glyph))
        self.play(Indicate(glyph, color=OK))
        self.wait(1.5)


class BlockSplittingScene(Scene):
    """Scene 6: shared-window splitting, batch divergence, the bug interlude."""

    N = 36
    SWITCH = 22

    def construct(self):
        chapter = Text("CUT BLOCKS", font_size=22, color=ORANGE)
        chapter.to_corner(UP + LEFT, buff=0.6).shift(DOWN * 0.3)
        self.add(chapter)

        import random
        rng = random.Random(2532)
        blues = ["#1f77b4", "#4292c6", "#2171b5", "#6baed6"]
        oranges = ["#ff7f0e", "#fd8d3c", "#e6550d", "#fdae6b"]
        ribbon = VGroup()
        for i in range(self.N):
            pal = blues if i < self.SWITCH else oranges
            sq = Square(side_length=0.28, fill_color=rng.choice(pal),
                        fill_opacity=0.9, stroke_opacity=0)
            sq.move_to(LEFT * 5.2 + RIGHT * (i * 0.3) + UP * 0.5)
            ribbon.add(sq)
        self.play(FadeIn(ribbon, lag_ratio=0.03))

        cad = VGroup(*[
            DashedLine(UP * 0.95, UP * 0.05, color=GREY_C).move_to(
                ribbon[j].get_center() + UP * 0.45)
            for j in (11, 23, 35)
        ])
        window = Rectangle(width=6.0, height=0.16, fill_color=GREY_E,
                           fill_opacity=0.5, stroke_opacity=0)
        window.move_to(ribbon[18].get_center() + DOWN * 0.35)
        backref = CurvedArrow(ribbon[26].get_center() + DOWN * 0.2,
                              ribbon[14].get_center() + DOWN * 0.2,
                              angle=0.9, color=VIOLET, tip_length=0.12)
        stamp1 = Text("Silesia L9 text: 15% to 20% smaller", font_size=19,
                      color=GREEN).move_to(DOWN * 1.2)
        self.play(Create(cad), FadeIn(window), Create(backref))
        self.play(FadeIn(stamp1))
        self.wait(1.5)
        self.play(FadeOut(cad), FadeOut(stamp1))

        def histogram(x_shift, colour, heights):
            g = VGroup()
            for i, h in enumerate(heights):
                b = Rectangle(width=0.28, height=max(h, 0.05),
                              fill_color=colour, fill_opacity=0.85,
                              stroke_opacity=0)
                b.move_to(UP * (2.0 + h / 2) + RIGHT * (x_shift + i * 0.34))
                g.add(b)
            return g

        blockH = histogram(-4.6, BLUE, [0.8, 0.62, 0.45, 0.28, 0.14, 0.08])
        recentH = histogram(1.6, TEAL, [0.8, 0.62, 0.45, 0.28, 0.14, 0.08])
        lab1 = Text("block so far", font_size=16, color=GREY_C)
        lab1.next_to(blockH, UP, buff=0.08)
        lab2 = Text("recent batch, normally 512", font_size=16, color=GREY_C)
        lab2.next_to(recentH, UP, buff=0.08)
        self.play(FadeIn(blockH), FadeIn(recentH), FadeIn(lab1), FadeIn(lab2))

        cursor = Line(UP * 0.95, UP * 0.15, color=WHITE)
        cursor.move_to(ribbon[0].get_center() + UP * 0.45)
        self.play(FadeIn(cursor))
        # one non-overlapping batch completes cleanly and RESETS, then the
        # next batch straddles the regime change and diverges
        mid = histogram(1.6, TEAL, [0.78, 0.6, 0.47, 0.3, 0.12, 0.09])
        self.play(cursor.animate.move_to(ribbon[11].get_center() + UP * 0.45),
                  Transform(recentH, mid), run_time=1.5)
        reset = histogram(1.6, TEAL, [0.05] * 6)
        self.play(Transform(recentH, reset), run_time=0.4)
        recent2 = histogram(1.6, ORANGE, [0.08, 0.12, 0.3, 0.55, 0.72, 0.85])
        gauge_bg = Rectangle(width=2.2, height=0.2, stroke_color=GREY_C,
                             fill_opacity=0).move_to(DOWN * 0.7)
        gauge = Rectangle(width=0.02, height=0.2, fill_color=RED,
                          fill_opacity=1, stroke_opacity=0)
        gauge.move_to(gauge_bg.get_left(), aligned_edge=LEFT)
        glab = Text("divergence", font_size=16, color=GREY_C)
        glab.next_to(gauge_bg, DOWN, buff=0.08)
        self.play(FadeIn(gauge_bg), FadeIn(gauge), FadeIn(glab))
        self.play(
            cursor.animate.move_to(ribbon[self.SWITCH + 6].get_center()
                                   + UP * 0.45),
            Transform(recentH, recent2),
            gauge.animate.stretch_to_fit_width(2.1).move_to(
                gauge_bg.get_left() + RIGHT * 1.05),
            run_time=3.0,
        )
        # cut after the batch that detected the change, not at the first
        # changed token
        cut = DashedLine(UP * 1.05, DOWN * 0.05, color=WHITE, stroke_width=5)
        cut.move_to(ribbon[self.SWITCH + 6].get_center() + UP * 0.5)
        cutlab = Text("cut after the detecting batch: fresh Huffman code",
                      font_size=18, color=ORANGE)
        cutlab.next_to(cut, DOWN, buff=0.9).shift(LEFT * 1.5)
        self.play(Create(cut), FadeIn(cutlab), Flash(cut, color=ORANGE))
        self.wait(0.8)

        arb = Text("designed and conformance-tested not to lose to fixed"
                   " cadence in this landing's arbitration",
                   font_size=16, color=GREY_C).move_to(DOWN * 1.7)
        note = Text("(observation splitting was off at L1-L6: all movement"
                    " there was the limiter fix; L7-L9 also bundled tuning)",
                    font_size=14, color=GREY_C).next_to(arb, DOWN, buff=0.1)
        self.play(FadeIn(arb), FadeIn(note))
        self.wait(2.0)
        self.play(*[FadeOut(m) for m in
                    (ribbon, blockH, recentH, lab1, lab2, cursor, gauge_bg,
                     gauge, glab, cut, cutlab, window, backref, arb, note)])

        # bug interlude: the 19-symbol CODES alphabet
        root = UP * 1.3
        tree = VGroup(
            Line(root, root + DOWN + LEFT, color=WHITE),
            Line(root, root + DOWN + RIGHT, color=WHITE),
            Line(root + DOWN + LEFT, root + DOWN * 2 + LEFT * 1.5, color=WHITE),
            Line(root + DOWN + LEFT, root + DOWN * 2 + LEFT * 0.5, color=WHITE),
            DashedLine(root + DOWN + RIGHT, root + DOWN * 2 + RIGHT * 1.5,
                       color=RED),
        )
        tlab = Text("incomplete CODES alphabet (19 code-length symbols)",
                    font_size=19, color=RED).next_to(tree, UP, buff=0.15)

        def door(text, colour):
            t = Text(text, font_size=19, color=colour)
            box = SurroundingRectangle(t, color=colour, buff=0.2)
            return VGroup(box, t)

        doors = VGroup(door("inflateReference ✓", GREEN),
                       door("zlib: invalid code lengths set", RED))
        doors.arrange(RIGHT, buff=0.9).move_to(DOWN * 1.9)
        self.play(Create(tree), FadeIn(tlab))
        self.play(FadeIn(doors))
        self.play(Indicate(doors[1], color=RED))
        moral = Text("the theorem covers OUR decoder;"
                     " conformance tests cover everyone else",
                     font_size=19, color=YELLOW).move_to(DOWN * 2.9)
        follow = Text("three days later: computeCodeLengths_complete proves"
                      " the missing Kraft equality",
                      font_size=15, color=GREY_C).next_to(moral, DOWN, buff=0.12)
        self.play(FadeIn(moral))
        glyph = roundtrip_glyph(size=16).to_corner(UP + RIGHT, buff=0.5)
        self.play(FadeIn(follow), FadeIn(glyph))
        self.play(Indicate(glyph, color=OK))
        self.wait(2.5)


class OptimalParsingScene(Scene):
    """Scene 7: the specified toy graph (nodes 0,1,4,8), backward DP,
    the refit flip, and the untrusted-advice ticket."""

    NODES = [0, 1, 4, 8]
    # edges: (from, to, kind, cost round 1, cost round 2)
    EDGES = [
        (0, 4, "match", 9, 9),
        (4, 8, "match", 12, 10),
        (0, 1, "literal", 8, 8),
        (1, 8, "match", 10, 14),
    ]

    def construct(self):
        chapter = Text("CHOOSE MATCHES, again", font_size=22, color=VIOLET)
        chapter.to_corner(UP + LEFT, buff=0.6).shift(DOWN * 0.3)
        self.add(chapter)

        toy = Text("TOY COSTS", font_size=20, color=YELLOW).move_to(UP * 2.3)
        self.add(toy)

        xpos = {n: LEFT * 5.0 + RIGHT * (n * 1.3) + DOWN * 0.3
                for n in self.NODES}
        nodes = {n: Dot(xpos[n], radius=0.09, color=WHITE)
                 for n in self.NODES}
        nlabels = {n: Text(str(n), font_size=18, color=GREY_C).next_to(
            nodes[n], DOWN, buff=0.15) for n in self.NODES}
        self.play(*[FadeIn(d) for d in nodes.values()],
                  *[FadeIn(l) for l in nlabels.values()])

        arcs, labels = {}, {}
        for (a, b, kind, c1, _c2) in self.EDGES:
            colour = AMBER if kind == "literal" else VIOLET
            ang = -0.9 if b - a > 1 else -1.3
            arc = ArcBetweenPoints(nodes[a].get_center(),
                                   nodes[b].get_center(), angle=ang,
                                   color=colour, stroke_width=3,
                                   fill_opacity=0)
            lab = Text(f"{kind} {c1}", font_size=16, color=colour)
            lab.next_to(arc, UP, buff=0.05)
            arcs[(a, b)] = arc
            labels[(a, b)] = lab
        self.play(*[Create(a) for a in arcs.values()],
                  *[FadeIn(l) for l in labels.values()])
        self.wait(1.0)

        # locally attractive 21-bit path vs the 18-bit winner
        path_a = VGroup(arcs[(0, 4)].copy(), arcs[(4, 8)].copy())
        path_a.set_stroke(color=COLOURS["native"], width=6)
        pa_lab = Text("greedy: 9 + 12 = 21 bits", font_size=17, color=GREY_C)
        pa_lab.move_to(DOWN * 1.7 + LEFT * 3.5)
        self.play(Create(path_a), FadeIn(pa_lab))
        self.wait(1.0)
        path_b = VGroup(arcs[(0, 1)].copy(), arcs[(1, 8)].copy())
        path_b.set_stroke(color=COLOURS["native"], width=6)
        pb_lab = Text("literal first: 8 + 10 = 18 bits", font_size=17,
                      color=WHITE).move_to(DOWN * 1.7 + RIGHT * 2.5)
        self.play(path_a.animate.set_stroke(opacity=0.25),
                  pa_lab.animate.set_opacity(0.4))
        self.play(Create(path_b), FadeIn(pb_lab))
        self.wait(1.0)
        self.play(FadeOut(path_a), FadeOut(pa_lab), FadeOut(path_b),
                  FadeOut(pb_lab))

        # backward DP wave with visible sums and a min funnel
        def dp(round_idx):
            cost = {8: 0}
            choice = {}
            for n in (4, 1, 0):
                best, arg = None, None
                for (a, b, kind, c1, c2) in self.EDGES:
                    if a != n or b not in cost:
                        continue
                    c = (c1 if round_idx == 0 else c2) + cost[b]
                    if best is None or c < best:
                        best, arg = c, b
                cost[n] = best
                choice[n] = arg
            return cost, choice

        cost1, choice1 = dp(0)
        cost_labels = {}
        sums = None
        for n in (8, 4, 1, 0):
            cl = Text(str(cost1[n]), font_size=20, color=PROOF_BLUE)
            cl.next_to(nodes[n], DOWN, buff=0.55)
            cost_labels[n] = cl
            if n == 0:
                sums = Text("node 0: min(match 9 + 12, literal 8 + 10) = 18",
                            font_size=15, color=GREY_C)
                sums.move_to(DOWN * 2.4)
                self.play(FadeIn(sums), run_time=0.4)
            self.play(FadeIn(cl), Flash(nodes[n].get_center(),
                                        color=PROOF_BLUE, line_length=0.12),
                      run_time=0.6)
        # forward trace
        i, segs = 0, []
        while i != 8:
            j = choice1[i]
            seg = arcs[(i, j)].copy().set_stroke(color=COLOURS["native"],
                                                 width=6)
            segs.append(seg)
            i = j
        red_path = VGroup(*segs)
        self.play(Create(red_path), run_time=1.2)
        self.wait(1.0)
        self.play(FadeOut(sums))

        # refit: 1→8 rises 10→14, 4→8 falls 12→10; the path flips
        refit = Text("refit costs to the parse's own histogram", font_size=19,
                     color=YELLOW).move_to(UP * 1.7)
        nl1 = Text("match 14", font_size=16, color=VIOLET)
        nl1.move_to(labels[(1, 8)].get_center())
        nl2 = Text("match 10", font_size=16, color=VIOLET)
        nl2.move_to(labels[(4, 8)].get_center())
        self.play(FadeIn(refit), Transform(labels[(1, 8)], nl1),
                  Transform(labels[(4, 8)], nl2))
        cost2, choice2 = dp(1)
        for n in (8, 4, 1, 0):
            cl = Text(str(cost2[n]), font_size=20, color=PROOF_BLUE)
            cl.next_to(nodes[n], DOWN, buff=0.55)
            self.play(Transform(cost_labels[n], cl), run_time=0.25)
        ghost = red_path.copy().set_stroke(opacity=0.22)
        self.add(ghost)
        i, segs2 = 0, []
        while i != 8:
            j = choice2[i]
            seg = arcs[(i, j)].copy().set_stroke(color=COLOURS["native"],
                                                 width=6)
            segs2.append(seg)
            i = j
        self.play(Transform(red_path, VGroup(*segs2)), run_time=1.0)
        flip = Text("22 vs 19: the winner flips", font_size=16, color=GREY_C)
        flip.move_to(DOWN * 2.4)
        self.play(FadeIn(flip))
        self.wait(1.5)

        # untrusted advice + result cards (two rows, nothing off-screen)
        ticket_t = Text("UNTRUSTED ADVICE", font_size=17, color=YELLOW)
        ticket_b = SurroundingRectangle(ticket_t, color=YELLOW, buff=0.12)
        ticket = VGroup(ticket_b, ticket_t).move_to(DOWN * 3.0 + LEFT * 3.4)
        gate_t = Text("emitter checks every match ✓", font_size=17,
                      color=PROOF_BLUE)
        gate_b = SurroundingRectangle(gate_t, color=PROOF_BLUE, buff=0.15)
        gate = VGroup(gate_b, gate_t).move_to(DOWN * 3.0 + RIGHT * 2.2)
        cards = Text("Silesia L9: 2.2% smaller at landing;"
                     " 2.2 to 2.8 times the compression time",
                     font_size=15, color=GREY_C).move_to(DOWN * 3.65)
        self.play(FadeIn(ticket), FadeIn(gate), FadeIn(cards))
        self.wait(2.5)


class SpeedMontageScene(Scene):
    """Scene 8: three speed vignettes (hash4 + dual-table ghost, prefilter,
    XOR+ctz with the failed-rescan crossout)."""

    def construct(self):
        chapter = Text("FIND MATCHES", font_size=22, color=TEAL)
        chapter.to_corner(UP + LEFT, buff=0.6).shift(DOWN * 0.3)
        self.add(chapter)

        # 1: hash4 shatters the chain; dual-table lifeboat ghost
        head = Text("hash 4 bytes, not 3", font_size=24, color=WHITE)
        head.move_to(UP * 2.0)
        chain = VGroup(*[Dot(LEFT * 5.5 + RIGHT * (0.55 * i) + UP * 0.8,
                             radius=0.07, color=TEAL) for i in range(20)])
        chain_lab = Text('every "the?" position, one bucket', font_size=17,
                         color=GREY_C).next_to(chain, DOWN, buff=0.15)
        self.play(FadeIn(head), FadeIn(chain, lag_ratio=0.04),
                  FadeIn(chain_lab))
        self.wait(0.8)
        cols = VGroup()
        keys = ["the_", "them", "then", "they", "ther"]
        for k, key in enumerate(keys):
            col = VGroup(*[Dot(radius=0.07, color=TEAL) for _ in range(4)])
            col.arrange(DOWN, buff=0.12)
            col.move_to(LEFT * 4.4 + RIGHT * (k * 2.2) + DOWN * 0.6)
            tag = Text(key, font=MONO, font_size=16, color=GREY_C)
            tag.next_to(col, UP, buff=0.1)
            cols.add(VGroup(col, tag))
        stamp1 = Text("historical Silesia L6: +54%", font_size=19,
                      color=GREEN).move_to(DOWN * 2.2)
        self.play(Transform(chain, cols), FadeOut(chain_lab))
        self.play(FadeIn(stamp1))
        # the missed length-3 match and the later hash3 lifeboat
        ghost3 = Text("a length-3 match hash4 can miss", font_size=15,
                      color=GREY_E).move_to(DOWN * 1.5 + LEFT * 3.8)
        boat = Text("singleton hash3 table (later dual-table design,"
                    " adapted from libdeflate)", font_size=14, color=GREY_C)
        boat.move_to(DOWN * 1.5 + RIGHT * 3.0)
        self.play(FadeIn(ghost3), FadeIn(boat))
        self.wait(1.3)
        self.play(FadeOut(VGroup(chain, stamp1, head, ghost3, boat)))

        # 2: one-byte prefilter
        head2 = Text("reject with one byte", font_size=24, color=WHITE)
        head2.move_to(UP * 2.0)
        tunnel = Rectangle(width=2.6, height=1.0, color=GREY_C)
        tunnel.move_to(RIGHT * 4.2 + DOWN * 0.2)
        tun_lab = Text("full compare", font_size=16, color=GREY_C)
        tun_lab.next_to(tunnel, UP, buff=0.1)
        check = Text("byte at offset bestLen?", font_size=17, color=PROOF_BLUE)
        check.move_to(UP * 0.6 + LEFT * 0.5)
        cands = VGroup(*[Dot(LEFT * (5.5 - 0.6 * i) + DOWN * 0.2, radius=0.08,
                             color=TEAL) for i in range(8)])
        self.play(FadeIn(head2), FadeIn(tunnel), FadeIn(tun_lab),
                  FadeIn(check), FadeIn(cands))
        drops = [c for i, c in enumerate(cands) if i % 3 != 0]
        survivors = [c for i, c in enumerate(cands) if i % 3 == 0]
        self.play(*[c.animate.set_color(RED).shift(DOWN * 1.5).set_opacity(0)
                    for c in drops],
                  *[c.animate.shift(RIGHT * 7) for c in survivors],
                  run_time=1.5)
        stamp2 = Text("Silesia L6: +26%, byte-identical  (=)",
                      font_size=19, color=GREEN).move_to(DOWN * 2.2)
        self.play(FadeIn(stamp2))
        self.wait(1.2)
        self.play(FadeOut(VGroup(head2, tunnel, tun_lab, check, stamp2,
                                 *survivors)))

        # 3: XOR + ctz, with the failed-rescan crossout
        head3 = Text("compare eight bytes at once", font_size=24, color=WHITE)
        head3.move_to(UP * 2.0)
        w1 = Text("LEAN-ZIP", font=MONO, font_size=30, color=WHITE)
        w2 = Text("LEAF-ZIP", font=MONO, font_size=30, color=WHITE)
        w1.move_to(UP * 0.9 + LEFT * 2.5)
        w2.move_to(UP * 0.1 + LEFT * 2.5)
        failed = Text("v1: rescan all 8 bytes after a mismatch (regressed)",
                      font_size=15, color=GREY_C).move_to(DOWN * 0.6)
        fstrike = Line(failed.get_left() + LEFT * 0.05,
                       failed.get_right() + RIGHT * 0.05, color=RED)
        xor = Text("XOR → 00000000 00000000 00000000 00001000 ...",
                   font=MONO, font_size=19, color=GREY_C).move_to(DOWN * 1.2)
        ctz = Text("ctz >> 3  →  byte 3:  N vs F", font=MONO, font_size=21,
                   color=PROOF_BLUE).move_to(DOWN * 1.8)
        self.play(FadeIn(head3), FadeIn(w1), FadeIn(w2))
        self.play(FadeIn(failed))
        self.play(Create(fstrike))
        self.play(FadeIn(xor))
        self.play(FadeIn(ctz), Indicate(w1[3]), Indicate(w2[3]))
        stamp3 = Text("paired Silesia: +4.9%  (=, by bv_decide)",
                      font_size=19, color=GREEN).move_to(DOWN * 2.5)
        self.play(FadeIn(stamp3))
        self.wait(2.0)


class ProofShapesScene(Scene):
    """Scene 9: the three recurring shapes of proof."""

    def panel(self, title, x_shift):
        box = Rectangle(width=4.0, height=3.6, color=GREY_C, stroke_width=1.2)
        box.move_to(x_shift + DOWN * 0.5)
        head = Text(title, font_size=19, color=WHITE)
        head.next_to(box, UP, buff=0.12)
        return box, head

    def construct(self):

        b1, h1 = self.panel("heuristic-independent", LEFT * 4.6)
        scan = Text("countMatch scanner", font_size=15, color=PROOF_BLUE)
        scan.move_to(b1.get_center() + UP * 1.1)
        gates = VGroup(Text("accept rule (free to change)", font_size=13,
                            color=VIOLET),
                       Text("cut clamp before any selector", font_size=13,
                            color=ORANGE))
        gates.arrange(DOWN, buff=0.25).move_to(b1.get_center() + DOWN * 0.2)
        p1 = VGroup(b1, h1, scan, gates)

        b2, h2 = self.panel("untrusted advice", ORIGIN)
        ticket = Text("DP choice arrays", font_size=15, color=YELLOW)
        ticket.move_to(b2.get_center() + UP * 0.7)
        cp2 = Text("proved emitter checks ✓", font_size=15, color=PROOF_BLUE)
        cp2.move_to(b2.get_center() + DOWN * 1.0)
        p2 = VGroup(b2, h2, ticket, cp2)

        b3, h3 = self.panel("proven equal", RIGHT * 4.6)
        loops = VGroup(Text("byte loop", font=MONO, font_size=15, color=WHITE),
                       Text("=", font_size=24, color=GREEN),
                       Text("prefilter + word loop", font=MONO, font_size=15,
                            color=WHITE))
        loops.arrange(DOWN, buff=0.18).move_to(b3.get_center() + UP * 0.5)
        bv = Text("bv_decide", font=MONO, font_size=15, color=PROOF_BLUE)
        bv.move_to(b3.get_center() + DOWN * 1.0)
        p3 = VGroup(b3, h3, loops, bv)

        self.play(FadeIn(p1))
        self.play(Indicate(scan, color=PROOF_BLUE))
        self.play(FadeIn(p2))
        self.play(Indicate(cp2, color=PROOF_BLUE))
        self.play(FadeIn(p3))
        self.play(Indicate(loops[1], color=GREEN))
        self.wait(1.0)

        safe = Text("the proof says which choices are safe", font_size=20,
                    color=GREEN).move_to(DOWN * 3.0 + LEFT * 3.2)
        good = Text("the benchmark says which are good", font_size=20,
                    color=YELLOW).move_to(DOWN * 3.0 + RIGHT * 3.4)
        glyph = roundtrip_glyph(size=16).to_corner(UP + RIGHT, buff=0.5)
        self.play(FadeIn(safe), FadeIn(glyph))
        self.play(Indicate(glyph, color=OK))
        self.play(FadeIn(good))
        self.wait(2.5)


class OutroScene(Scene):
    """Scene 10: return to the curve with pinned commits, the ratchet line."""

    COMMITS = [
        ("437e77cc", "shared-window"),
        ("19350797", "lazy"),
        ("35f28549", "observation split"),
        ("356a21bf", "dynamic program"),
        ("7b2e1bec", "prefilter"),
        ("5d772a0d", "hash4"),
    ]

    def construct(self):
        data = _load_history()
        axes = Axes(
            x_range=[0.29, 0.45, 0.05], y_range=[-0.5, 2.7, 1.0],
            x_length=10.5, y_length=5.0, tips=False,
            axis_config={"color": GREY_E, "include_ticks": False},
        ).shift(DOWN * 0.5)

        def curve(pts, colour, width, op=1.0):
            line = VMobject(color=colour, stroke_width=width, fill_opacity=0)
            line.set_points_as_corners([
                axes.coords_to_point(p["ratio"], math.log10(p["mbps"]))
                for p in pts
            ])
            line.set_stroke(opacity=op)
            return line

        field = VGroup(*[
            curve(pts, COLOURS.get(n, GREY_C), 2.0, 0.25)
            for n, pts in data["reference"].items() if n != "native"
        ])
        native = curve(data["reference"]["native"], COLOURS["native"], 4.0)
        self.play(FadeIn(axes), FadeIn(field))
        self.play(Create(native), run_time=2.0)

        # pinned commits in landing order along a small timeline strip
        strip = VGroup()
        for i, (h, name) in enumerate(self.COMMITS):
            e = VGroup(Text(h, font=MONO, font_size=13, color=GREY_C),
                       Text(name, font_size=12, color=GREY_C))
            e.arrange(DOWN, buff=0.04)
            strip.add(e)
        strip.arrange(RIGHT, buff=0.55).move_to(UP * 2.0)
        wat = VGroup(Text("95d13b87", font=MONO, font_size=13, color=GREY_E),
                     Text("word-at-a-time (frame filtered)", font_size=11,
                          color=GREY_E))
        wat.arrange(DOWN, buff=0.04).next_to(strip, RIGHT, buff=0.5)
        wbox = DashedLine(wat.get_left() + DOWN * 0.25,
                          wat.get_right() + DOWN * 0.25, color=GREY_E)
        self.play(FadeIn(strip, lag_ratio=0.15))
        self.play(FadeIn(wat), Create(wbox))
        self.wait(1.0)

        pin = Text("libdeflate: still the ceiling", font_size=19,
                   color=COLOURS["libdeflate"]).move_to(UP * 1.2 + LEFT * 3.4)
        self.play(FadeIn(pin))
        self.wait(1.0)

        sources = VGroup(
            Text("profiles found bottlenecks", font_size=18, color=GREY_C),
            Text("zlib and libdeflate supplied ideas", font_size=18,
                 color=GREY_C),
            Text("benchmarks chose winners", font_size=18, color=GREY_C),
        ).arrange(RIGHT, buff=0.8).move_to(DOWN * 3.1)
        self.play(FadeIn(sources, lag_ratio=0.3))
        self.wait(1.5)

        glyph = roundtrip_glyph(size=16).to_corner(UP + RIGHT, buff=0.5)
        self.play(FadeIn(glyph))
        final = m("inflate (deflate data) = data", size=34, color=OK)
        self.play(FadeOut(axes), FadeOut(field), FadeOut(native), FadeOut(pin),
                  FadeOut(sources), FadeOut(strip), FadeOut(wat),
                  FadeOut(wbox),
                  TransformMatchingShapes(glyph, final))
        self.wait(1.0)
        credits = VGroup(
            Text("github.com/kim-em/lean-zip", font=MONO, font_size=22,
                 color=WHITE),
            Text("Why Lean is faster than Rust, parts 1 and 2",
                 font_size=18, color=GREY_C),
            Text("benchmarks: Silesia; methodology in bench/README.md",
                 font_size=16, color=GREY_C),
        ).arrange(DOWN, buff=0.25).move_to(DOWN * 1.6)
        self.play(FadeIn(credits))
        self.wait(3.0)
