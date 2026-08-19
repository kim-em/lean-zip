"""Design tokens and typographic components for the video.

Rules (from the dataviz method, adapted to manim):
- Text wears ink tokens; series/accent colours go on marks, chips, and rules,
  not on running text. A colored term is the exception, used sparingly.
- One type scale, at most three sizes per scene.
- Consistent paddings; components, not ad-hoc rectangles.
- Prose in Inter; code and numerals-as-output in JetBrains Mono; never
  monospace for prose.
"""
from manim import (
    DOWN, LEFT, RIGHT, UP, ITALIC,
    Dot, RoundedRectangle, Text, VGroup,
)

# surfaces and ink
BG = "#0e1116"
SURFACE = "#151a21"      # panels
SURFACE_2 = "#1b222b"    # nested/code panels
EDGE = "#2c3440"         # panel strokes
INK = "#e6e8eb"          # primary text
INK2 = "#9aa3ad"         # secondary text
MUTED = "#5c6570"        # tertiary/annotations

# accents (marks, chips, rules; not running text)
OK = "#57b183"
BAD = "#e35d6a"
WARN = "#d9a441"
INFO = "#5da9e9"         # proof boundaries
AMBER = "#d9a441"        # literals (same as WARN by design)
VIOLET = "#a487d9"       # matches

# dashboard series colours (identity continuity with committed graphs)
SERIES = {
    "native": "#d62728", "zlib": "#1f77b4", "miniz_oxide": "#2ca02c",
    "libdeflate": "#9467bd", "go": "#8c564b", "js": "#e377c2",
    "zig": "#bcbd22", "ocaml": "#17becf",
}

FONT_TEXT = "Inter"
# The NL (no-ligature) variant: manim's per-character bookkeeping breaks on
# ligated glyph pairs like `:=`, and code should show real characters anyway.
FONT_CODE = "JetBrains Mono NL"

# type scale — pick at most three per scene
TITLE = 54
H1 = 38
BODY = 27
SMALL = 21
MICRO = 17


def t(s, size=BODY, color=INK, weight="NORMAL", slant="NORMAL"):
    """Prose text."""
    return Text(s, font=FONT_TEXT, font_size=size, color=color,
                weight=weight, slant=slant)


def m(s, size=SMALL, color=INK):
    """Code/numeric text."""
    return Text(s, font=FONT_CODE, font_size=size, color=color)


def panel(width, height, fill=SURFACE):
    return RoundedRectangle(width=width, height=height, corner_radius=0.14,
                            stroke_color=EDGE, stroke_width=1.4,
                            fill_color=fill, fill_opacity=1.0)


def code_block(lines, size=SMALL, pad=0.4, comment_prefixes=("--", "/*", "#")):
    """A code panel: JetBrains Mono lines on a nested surface."""
    texts = []
    for l in lines:
        txt = m(l, size=size)
        if any(l.lstrip().startswith(p) for p in comment_prefixes):
            txt.set_color(MUTED)
        texts.append(txt)
    body = VGroup(*texts).arrange(DOWN, aligned_edge=LEFT, buff=0.16)
    box = panel(body.width + 2 * pad, body.height + 2 * pad, fill=SURFACE_2)
    body.move_to(box.get_center())
    return VGroup(box, body)


def chip(s, accent, size=SMALL):
    """Ink text with a small colored identity dot before it."""
    dot = Dot(radius=0.06, color=accent)
    txt = t(s, size=size, color=INK)
    g = VGroup(dot, txt).arrange(RIGHT, buff=0.16)
    return g


def pill(s, accent, size=SMALL, pad=0.22):
    """A stamp: ink text in a rounded outline tinted by its accent."""
    txt = t(s, size=size, color=INK)
    box = RoundedRectangle(width=txt.width + 2 * pad,
                           height=txt.height + 1.6 * pad,
                           corner_radius=0.12, stroke_color=accent,
                           stroke_width=1.6, fill_color=SURFACE,
                           fill_opacity=0.9)
    txt.move_to(box.get_center())
    return VGroup(box, txt)


def rule_under(mobj, accent, buff=0.08):
    """A thin accent rule under a mobject (replaces boxes around text)."""
    from manim import Line
    return Line(mobj.get_corner(DOWN + LEFT) + DOWN * buff,
                mobj.get_corner(DOWN + RIGHT) + DOWN * buff,
                color=accent, stroke_width=2.5)
