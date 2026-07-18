#!/usr/bin/env python3
"""Animate the compress-Pareto chart through its git history.

The static `<corpus>_compress_pareto.svg` shows where the native codec is
*today*; this script shows how it got there. It replays every committed
dashboard refresh (`bench/results/latest.json` in git history) as one frame
of an animation: the reference curves stay fixed at the current data while
the native curve moves, leaving a faint trail per level.

Outputs (all under bench/graphs/):
    <corpus>_compress_pareto_history.svg    always — self-playing SMIL SVG,
                                            no JavaScript, animates inside a
                                            GitHub README <img>; committed.
    <corpus>_compress_pareto_history.{mp4,gif}   with --video (needs ffmpeg
                                            on PATH); regenerable, untracked.
    <corpus>_compress_pareto_history.html   with --html — an interactive
                                            player (scrubber, tooltips, per-
                                            frame commit info) built from the
                                            sibling pareto_history_player.html
                                            template; regenerable, untracked.

Run inside the project shell (matplotlib comes from shell.nix, same as
plot.py):
    bench/pareto_history.py [--corpus silesia] [--video] [--html]

Frame hygiene — two filters run over the raw history (reported to stderr):
- spike: drop a frame whose ratios revert to an already-seen state while
  jumping away from its predecessor. Ratios are deterministic, so an exact
  match with an older frame cannot be measurement noise — it is a dashboard
  refresh benched from a stale branch, not a real code change.
- noise: drop a frame whose ratios are unchanged (< RATIO_EPS) and whose
  throughput moved < LOGSPEED_EPS in log10 (~8%) vs the last kept frame —
  within median-of-5 snapshot jitter, typically decode-only work. The first
  and last frames and any level-set change are always kept.

Aggregation is identical to plot.py's pareto_scatter (geomean ratio and
geomean compress MB/s per level over the corpus files), and the connectors
are the same achievable mixing frontier (`plot._mix_curve` maths: ratio
linear in the blend fraction, 1/throughput linear). The zopfli ratio-ceiling
overlay is applied to the reference curves exactly as in plot.py.
"""
import argparse
import json
import math
import shutil
import subprocess
import sys
import tempfile
from html import escape
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import plot  # COMPRESSORS, _level_points, _mix_curve maths, geomean

REPO = Path(__file__).resolve().parent.parent

NATIVE_COLOUR = dict((k, c) for k, _l, c, _m in plot.COMPRESSORS)["native"]

# frame-hygiene thresholds (see module docstring)
RATIO_EPS = 5e-4
LOGSPEED_EPS = 0.035
SPIKE_JUMP = 4e-3
SPIKE_MATCH = 1e-3

# animation timeline
FRAME_SECONDS = 0.4     # per dashboard refresh
HOLD_FIRST = 1.0
HOLD_LAST = 2.5

# fixed plot window (ratio linear, MB/s log) — covers every frame and curve
XLIM = (0.295, 0.44)
YLIM = (0.4, 340)


def git(*args):
    return subprocess.run(["git", "-C", str(REPO), *args],
                          capture_output=True, text=True, check=True).stdout


def latest_json_dirty():
    """True if bench/results/latest.json has uncommitted changes vs HEAD.

    The committed animation SVG is rendered from committed git history; a dirty
    latest.json would make it (references, a transient 'worktree' frame, and a
    wall-clock date) depend on the working tree, which CI's clean checkout cannot
    reproduce — so `animation-sync` would fail on the very next push."""
    return bool(git("status", "--porcelain", "--", "bench/results/latest.json").strip())


# --------------------------------------------------------------------------
# extraction

def native_points(results, corpus):
    return plot._level_points(results, corpus, "native", "compress_mbps")


def _dratio(a, b):
    ma = {p[0]: p[1] for p in a["points"]}
    mb = {p[0]: p[1] for p in b["points"]}
    return max((abs(ma[l] - mb[l]) for l in ma.keys() & mb.keys()), default=0)


def _dspeed(a, b):
    ma = {p[0]: p[2] for p in a["points"]}
    mb = {p[0]: p[2] for p in b["points"]}
    return max((abs(math.log10(ma[l] / mb[l])) for l in ma.keys() & mb.keys()),
               default=0)


def _levels(f):
    return {p[0] for p in f["points"]}


def drop_spikes(frames):
    """Drop stale-refresh spikes: a frame that jumps away from its
    predecessor, matches an older frame's deterministic ratios, AND is
    transient — the next frame lands back near the predecessor. A genuine
    regression that *persists* fails the transience test and is kept."""
    kept = []
    for i, f in enumerate(frames):
        if kept and i < len(frames) - 1 and _dratio(kept[-1], f) > SPIKE_JUMP \
                and any(_dratio(g, f) < SPIKE_MATCH for g in kept[:-1]) \
                and _dratio(kept[-1], frames[i + 1]) < 0.5 * _dratio(kept[-1], f):
            print(f"spike: drop {f['commit']} ({f['subject'][:60]})",
                  file=sys.stderr)
            continue
        kept.append(f)
    return kept


def drop_noise(frames):
    """Drop frames that move only within throughput noise vs the last
    kept frame; first/last frames and level-set changes always stay."""
    if len(frames) <= 1:
        return frames
    out = [frames[0]]
    for f in frames[1:-1]:
        if _levels(f) != _levels(out[-1]) or _dratio(out[-1], f) > RATIO_EPS \
                or _dspeed(out[-1], f) > LOGSPEED_EPS:
            out.append(f)
        else:
            print(f"noise: drop {f['commit']} (Δspeed {_dspeed(out[-1], f):.3f} "
                  f"log10) ({f['subject'][:52]})", file=sys.stderr)
    out.append(frames[-1])
    return out


def extract(corpus, include_worktree=False):
    """-> (references, frames, meta): fixed reference curves from the current
    latest.json (+ frozen zopfli ceiling), one filtered frame per committed
    dashboard refresh. When include_worktree is set, an uncommitted refresh that
    differs from HEAD is appended as a final 'worktree' frame — that path is for
    local --preview only; the committed SVG is built from committed frames so
    CI's clean checkout can reproduce it (see latest_json_dirty)."""
    now = json.load(open(REPO / "bench/results/latest.json"))
    results_now = now["results"]
    ceiling_path = REPO / "bench/results/zopfli-ceiling.json"
    if ceiling_path.exists():
        ceiling = json.load(open(ceiling_path))["results"]
        results_now = [r for r in results_now
                       if r["compressor"] != "zopfli"] + ceiling

    references = []
    for key, label, colour, marker in plot.COMPRESSORS:
        if key == "native":
            continue
        pts = plot._level_points(results_now, corpus, key, "compress_mbps")
        if pts:
            references.append(dict(key=key, label=label, colour=colour,
                                   marker=marker, points=pts))

    frames = []
    log = git("log", "--follow", "--reverse",
              "--format=%H\x1f%ad\x1f%s", "--date=iso-strict",
              "--", "bench/results/latest.json")
    for line in log.strip().splitlines():
        sha, cdate, subject = line.split("\x1f")
        try:
            d = json.loads(git("show", f"{sha}:bench/results/latest.json"))
        except Exception:
            continue
        pts = native_points(d.get("results", []), corpus)
        if pts:
            frames.append(dict(commit=sha[:8], subject=subject,
                               commit_date=cdate, points=pts))
    if not frames:
        sys.exit(f"no native {corpus} rows anywhere in the history of "
                 "bench/results/latest.json")

    # a just-refreshed, not-yet-committed dashboard becomes the final frame
    # (preview only; excluded from the committed SVG for CI reproducibility)
    if include_worktree:
        wt = native_points(now["results"], corpus)
        if wt and wt != frames[-1]["points"]:
            frames.append(dict(commit="worktree", subject="uncommitted dashboard refresh",
                               commit_date=now.get("meta", {}).get("date", "?"),
                               points=wt))

    raw = len(frames)
    frames = drop_noise(drop_spikes(frames))
    print(f"{raw} raw frames -> {len(frames)} kept", file=sys.stderr)

    nfiles = len(plot.corpus_patterns(results_now, corpus))
    if nfiles == 0:
        sys.exit(f"corpus {corpus!r} has history but no rows in the current "
                 "latest.json — nothing to anchor the reference curves to")
    m = now.get("meta", {})
    meta = dict(corpus=corpus, nfiles=nfiles,
                first_date=frames[0]["commit_date"][:10],
                last_date=frames[-1]["commit_date"][:10],
                ref_commit=m.get("git_commit", "?"),
                ref_date=m.get("date", "?")[:10],
                machine=m.get("machine", "?")
                         .replace("Linux ", "").replace(" x86_64", ""))
    return references, frames, meta


def title_of(meta):
    return (f"Compression speed vs ratio  ({meta['corpus']} — geomean over "
            f"{meta['nfiles']} files, {meta['first_date']} → {meta['last_date']})")


def provenance_of(meta):
    return (f"native curve replayed from the git history of latest.json · "
            f"references @ {meta['ref_commit']} "
            f"({meta['ref_date']}, {meta['machine']}) · "
            f"throughput = median snapshot; ratio deterministic")


# --------------------------------------------------------------------------
# self-playing SMIL SVG (no JavaScript; animates in a GitHub README <img>)

SVG_W, SVG_H = 940, 660
SVG_ML, SVG_MR, SVG_MT, SVG_MB = 62, 14, 64, 62


def build_svg(references, frames, meta, outfile):
    N = len(frames)
    T = HOLD_FIRST + FRAME_SECONDS * (N - 1) + HOLD_LAST
    starts = [HOLD_FIRST + FRAME_SECONDS * i for i in range(N)]
    keytimes = [0.0] + [s / T for s in starts] + [1.0]

    def keyframes(vals):
        seq = [vals[0]] + list(vals) + [vals[-1]]
        return ";".join(seq), ";".join(f"{k:.5f}" for k in keytimes)

    def sx(r):
        return SVG_ML + (r - XLIM[0]) / (XLIM[1] - XLIM[0]) * (SVG_W - SVG_ML - SVG_MR)

    def sy(v):
        return SVG_H - SVG_MB - (math.log10(v) - math.log10(YLIM[0])) / \
            (math.log10(YLIM[1]) - math.log10(YLIM[0])) * (SVG_H - SVG_MT - SVG_MB)

    def mix_d(x0, y0, x1, y1, n=16):
        p = []
        for i in range(n + 1):
            f = i / n
            r = (1 - f) * x0 + f * x1
            v = 1 / ((1 - f) / y0 + f / y1)
            p.append(("M" if i == 0 else "L") + f"{sx(r):.1f},{sy(v):.1f}")
        return "".join(p)

    def marker_d(kind, x, y, s):
        def P(q):
            return "M" + "L".join(f"{a:.2f},{b:.2f}" for a, b in q) + "Z"
        if kind == "s":
            return P([(x-s, y-s), (x+s, y-s), (x+s, y+s), (x-s, y+s)])
        if kind == "^":
            return P([(x, y-s), (x+s, y+s), (x-s, y+s)])
        if kind == "v":
            return P([(x, y+s), (x+s, y-s), (x-s, y-s)])
        if kind == "D":
            return P([(x, y-s), (x+s, y), (x, y+s), (x-s, y)])
        if kind in ("P", "X"):
            a = s * 0.42
            q = [(-a, -s), (a, -s), (a, -a), (s, -a), (s, a), (a, a),
                 (a, s), (-a, s), (-a, a), (-s, a), (-s, -a), (-a, -a)]
            if kind == "X":
                c = math.sqrt(0.5)
                q = [((px - py) * c, (px + py) * c) for px, py in q]
            return P([(x + px, y + py) for px, py in q])
        if kind == "*":
            return P([(x + (s * 0.45 if i % 2 else s) * math.cos(-math.pi/2 + i*math.pi/6),
                       y + (s * 0.45 if i % 2 else s) * math.sin(-math.pi/2 + i*math.pi/6))
                      for i in range(12)])
        if kind == "h":
            return P([(x + s * math.cos(-math.pi/2 + i*math.pi/3),
                       y + s * math.sin(-math.pi/2 + i*math.pi/3))
                      for i in range(6)])
        return None  # "o" is a <circle>

    def anim(attr, vals):
        v, k = keyframes(vals)
        return (f'<animate attributeName="{attr}" values="{v}" keyTimes="{k}" '
                f'calcMode="linear" dur="{T}s" repeatCount="indefinite"/>')

    levels = sorted({p[0] for f in frames for p in f["points"]})
    pos = {lvl: [None] * N for lvl in levels}
    for i, f in enumerate(frames):
        for lvl, r, v in f["points"]:
            pos[lvl][i] = (r, v)
    first_seen = {lvl: next(i for i in range(N) if pos[lvl][i]) for lvl in levels}

    def held(lvl):
        """Per-frame positions with gaps forward-filled: before first
        appearance hold the first point; through a mid-history gap hold the
        last visible point (opacity animates separately, so a hidden marker
        must not teleport back to its first position)."""
        fs = first_seen[lvl]
        out, last = [], pos[lvl][fs]
        for i in range(N):
            if i >= fs and pos[lvl][i]:
                last = pos[lvl][i]
            out.append(last)
        return out

    out = []
    out.append(f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {SVG_W} {SVG_H}" '
               f'font-family="Helvetica, Arial, sans-serif">')
    out.append(f'<rect width="{SVG_W}" height="{SVG_H}" fill="#ffffff"/>')
    out.append(f'<text x="{SVG_W/2:.0f}" y="24" text-anchor="middle" font-size="15" '
               f'font-weight="bold" fill="#222222">{escape(title_of(meta))}</text>')

    mono = 'font-family="Menlo, Consolas, monospace"'
    grid = ['<g stroke="#d9d9d9" stroke-width="0.7">']
    labels = [f'<g font-size="11" fill="#555555" {mono}>']
    for v in (0.5, 1, 2, 5, 10, 20, 50, 100, 200):
        y = sy(v)
        grid.append(f'<line x1="{SVG_ML}" x2="{SVG_W-SVG_MR}" y1="{y:.1f}" y2="{y:.1f}"/>')
        labels.append(f'<text x="{SVG_ML-8}" y="{y+3.5:.1f}" text-anchor="end">'
                      f'{v if v >= 1 else "0.5"}</text>')
    r = 0.30
    while r <= XLIM[1] + 1e-9:
        x = sx(r)
        grid.append(f'<line x1="{x:.1f}" x2="{x:.1f}" y1="{SVG_MT}" y2="{SVG_H-SVG_MB}"/>')
        labels.append(f'<text x="{x:.1f}" y="{SVG_H-SVG_MB+18}" text-anchor="middle">{r:.2f}</text>')
        r += 0.02
    grid.append("</g>")
    labels.append("</g>")
    out += grid + labels
    out.append(f'<rect x="{SVG_ML}" y="{SVG_MT}" width="{SVG_W-SVG_ML-SVG_MR}" '
               f'height="{SVG_H-SVG_MT-SVG_MB}" fill="none" stroke="#cccccc"/>')
    out.append(f'<text x="{(SVG_ML+SVG_W-SVG_MR)/2:.0f}" y="{SVG_H-22}" text-anchor="middle" '
               f'font-size="12.5" fill="#222222">compression ratio   '
               f'(compressed / original  —  ← smaller is better)</text>')
    out.append(f'<text transform="translate(16 {(SVG_MT+SVG_H-SVG_MB)/2:.0f}) rotate(-90)" '
               f'text-anchor="middle" font-size="12.5" fill="#222222">'
               f'compression speed   (MB/s, log)</text>')
    out.append(f'<text x="{SVG_ML+10}" y="{SVG_MT+20}" font-size="13" fill="#2a8a3a" '
               f'font-weight="bold">↖ fast &amp; small = best</text>')

    # fixed reference curves
    for ref in references:
        pts = ref["points"]
        for a, b in zip(pts, pts[1:]):
            out.append(f'<path d="{mix_d(a[1], a[2], b[1], b[2])}" fill="none" '
                       f'stroke="{ref["colour"]}" stroke-width="1.3" opacity="0.9"/>')
        for _lvl, rr, vv in pts:
            x, y = sx(rr), sy(vv)
            d = marker_d(ref["marker"], x, y, 4.4)
            shape = (f'<circle cx="{x:.1f}" cy="{y:.1f}" r="4.4"' if d is None
                     else f'<path d="{d}"')
            out.append(f'{shape} fill="none" stroke="{ref["colour"]}" '
                       f'stroke-width="1.4" opacity="0.95"/>')

    # trails: full per-level path, revealed by animated stroke-dashoffset.
    # The path visits only the frames where the level is present, so a level
    # that disappears mid-history simply contributes no vertex there.
    for lvl in levels:
        samples = [(i, pos[lvl][i]) for i in range(N) if pos[lvl][i]]
        pts = [(sx(r), sy(v)) for _, (r, v) in samples]
        if len(pts) < 2:
            continue
        d = "M" + "L".join(f"{x:.1f},{y:.1f}" for x, y in pts)
        seg = [0.0]
        for (xa, ya), (xb, yb) in zip(pts, pts[1:]):
            seg.append(seg[-1] + math.hypot(xb - xa, yb - ya))
        total = seg[-1]
        if total <= 0:
            continue
        # revealed arc length at frame i = up to the last sample at or before i
        reveal, k = [], 0
        for i in range(N):
            while k + 1 < len(samples) and samples[k + 1][0] <= i:
                k += 1
            reveal.append(seg[k] if samples[0][0] <= i else 0.0)
        out.append(f'<path d="{d}" fill="none" stroke="{NATIVE_COLOUR}" '
                   f'stroke-width="0.9" opacity="0.15" '
                   f'stroke-dasharray="{total:.1f} {total:.1f}" '
                   f'stroke-dashoffset="{total:.1f}">')
        out.append(anim("stroke-dashoffset", [f"{total - rv:.1f}" for rv in reveal]))
        out.append("</path>")

    # native connectors (mixing curves), d + opacity animated
    def connector(lvl_a, lvl_b, alive):
        ha, hb = held(lvl_a), held(lvl_b)
        ds = [mix_d(ha[i][0], ha[i][1], hb[i][0], hb[i][1]) for i in range(N)]
        op = [f"{1 if alive(i) else 0}" for i in range(N)]
        out.append(f'<path d="{ds[0]}" fill="none" stroke="{NATIVE_COLOUR}" '
                   f'stroke-width="2" opacity="{op[0]}">')
        out.append(anim("d", ds))
        out.append(anim("opacity", op))
        out.append("</path>")

    for a, b in zip(levels, levels[1:]):
        connector(a, b,
                  lambda i, a=a, b=b: pos[a][i] is not None and pos[b][i] is not None)
    # sparse frames (e.g. an early L1/L6/L9-only sweep) additionally get bridge
    # connectors between present-but-nonadjacent levels, alive only while EVERY
    # level in between is missing (if any intermediate is present, the ordinary
    # adjacent connectors through it carry the frontier instead)
    bridged = set()
    for i in range(N):
        present = [l for l in levels if pos[l][i] is not None]
        for a, b in zip(present, present[1:]):
            if levels[levels.index(a) + 1] != b and (a, b) not in bridged:
                bridged.add((a, b))
                connector(a, b, lambda i, a=a, b=b: (
                    pos[a][i] is not None and pos[b][i] is not None
                    and all(pos[m][i] is None
                            for m in levels[levels.index(a)+1:levels.index(b)])))

    # native markers
    for lvl in levels:
        h = held(lvl)
        cxs = [f"{sx(r):.1f}" for r, _ in h]
        cys = [f"{sy(v):.1f}" for _, v in h]
        op = [f"{1 if pos[lvl][i] else 0}" for i in range(N)]
        out.append(f'<circle cx="{cxs[0]}" cy="{cys[0]}" r="4.8" '
                   f'fill="{NATIVE_COLOUR}" opacity="{op[0]}">')
        out.append(anim("cx", cxs))
        out.append(anim("cy", cys))
        if any(o == "0" for o in op):
            out.append(anim("opacity", op))
        out.append("</circle>")

    # endpoint level tags: the lowest level on top, and the deepest level
    # present (which changes when a new deepest level ships)
    def tag(lvl, visible):
        h = held(lvl)
        xs = [f"{sx(r)+6:.1f}" for r, _ in h]
        ys = [f"{sy(v)-6:.1f}" for _, v in h]
        op = [f"{1 if visible(i) else 0}" for i in range(N)]
        out.append(f'<text x="{xs[0]}" y="{ys[0]}" font-size="11" font-weight="bold" '
                   f'fill="{NATIVE_COLOUR}" {mono} opacity="{op[0]}">L{lvl}')
        out.append(anim("x", xs))
        out.append(anim("y", ys))
        if any(o == "0" for o in op):
            out.append(anim("opacity", op))
        out.append("</text>")

    tag(levels[0], lambda i: True)
    deeper = {i: max(l for l in levels if pos[l][i] is not None) for i in range(N)}
    for lvl in sorted({v for v in deeper.values()}):
        tag(lvl, lambda i, lvl=lvl: deeper[i] == lvl)

    # commit ticker (discrete visibility per data frame), left-anchored so the
    # varying line width doesn't wobble
    out.append(f'<g font-size="11" fill="#333333" {mono}>')
    for i, f in enumerate(frames):
        subj = f["subject"]
        if len(subj) > 72:
            subj = subj[:69] + "…"
        txt = escape(f"{f['commit_date'][:10]} · {f['commit']} · "
                     f"{i+1:2d}/{N} — {subj}")
        s0 = starts[i] / T
        s1 = starts[i + 1] / T if i + 1 < N else None
        if N == 1:                      # single frame: static ticker, no animation
            out.append(f'<text x="{SVG_ML}" y="46">{txt}</text>')
            continue
        if i == 0:
            vals, keys = "1;0", f"0;{s1:.5f}"
        elif s1 is None:
            vals, keys = "0;1", f"0;{s0:.5f}"
        else:
            vals, keys = "0;1;0", f"0;{s0:.5f};{s1:.5f}"
        out.append(f'<text x="{SVG_ML}" y="46" opacity="0">{txt}'
                   f'<animate attributeName="opacity" values="{vals}" keyTimes="{keys}" '
                   f'calcMode="discrete" dur="{T}s" repeatCount="indefinite"/></text>')
    out.append("</g>")

    # legend, two columns, lower right (plot order, native first)
    entries = [("lean-zip (native)", NATIVE_COLOUR, "o", True)] + \
              [(r["label"], r["colour"], r["marker"], False) for r in references]
    rows = (len(entries) + 1) // 2
    lx, ly, rowh, colw = SVG_W - SVG_MR - 330, SVG_H - SVG_MB - 88, 16, 165
    out.append(f'<rect x="{lx-10}" y="{ly-14}" width="330" height="{rowh*rows+10}" '
               f'fill="#ffffff" opacity="0.85" stroke="#cccccc"/>')
    out.append('<g font-size="10.5" fill="#333333">')
    for j, (label, colour, marker, filled) in enumerate(entries):
        x = lx + (j // rows) * colw
        y = ly + (j % rows) * rowh
        d = marker_d(marker, x, y - 3.5, 4.2)
        shape = (f'<circle cx="{x}" cy="{y-3.5}" r="4.2"' if d is None
                 else f'<path d="{d}"')
        out.append(f'{shape} fill="{colour if filled else "none"}" '
                   f'stroke="{colour}" stroke-width="1.3"/>')
        out.append(f'<text x="{x+10}" y="{y}" '
                   f'font-weight="{"bold" if filled else "normal"}">{escape(label)}</text>')
    out.append("</g>")

    out.append(f'<text x="{SVG_W/2:.0f}" y="{SVG_H-6}" text-anchor="middle" '
               f'font-size="7.5" fill="#777777">{escape(provenance_of(meta))}</text>')
    out.append("</svg>")

    outfile.write_text("\n".join(out))
    print(f"wrote {outfile} ({outfile.stat().st_size} bytes, {T:.1f}s loop)",
          file=sys.stderr)


# --------------------------------------------------------------------------
# mp4 + GIF via matplotlib frames + ffmpeg

VIDEO_FPS = 30
TWEEN_STEPS = 12        # sub-frames per transition


def points_at(frames, t):
    """Native points at float frame position t: [(level, ratio, mbps, alpha)].
    Ratio interpolates linearly, speed in log space (smoothstep easing);
    levels entering or leaving the sweep fade."""
    N = len(frames)
    i = min(int(t), N - 1)
    f = t - i
    f = f * f * (3 - 2 * f)
    a = {p[0]: p for p in frames[i]["points"]}
    b = {p[0]: p for p in frames[min(i + 1, N - 1)]["points"]}
    out = []
    for lvl in sorted(a.keys() | b.keys()):
        pa, pb = a.get(lvl), b.get(lvl)
        if pa and pb:
            out.append((lvl, (1 - f) * pa[1] + f * pb[1],
                        math.exp((1 - f) * math.log(pa[2]) + f * math.log(pb[2])), 1.0))
        elif pa:
            out.append((lvl, pa[1], pa[2], 1 - f))
        else:
            out.append((lvl, pb[1], pb[2], f))
    return out


def draw_video_frame(plt, references, frames, meta, t, outfile):
    N = len(frames)
    fig, ax = plt.subplots(figsize=(9, 6.5), dpi=120)

    for ref in references:
        pts = ref["points"]
        xs = [p[1] for p in pts]
        ys = [p[2] for p in pts]
        ax.plot(xs, ys, linestyle="none", marker=ref["marker"], label=ref["label"],
                markersize=5, markerfacecolor="none", markeredgecolor=ref["colour"],
                markeredgewidth=1.3, alpha=0.95, zorder=4)
        for i in range(len(pts) - 1):
            cx, cy = plot._mix_curve(xs[i], ys[i], xs[i + 1], ys[i + 1])
            ax.plot(cx, cy, color=ref["colour"], linewidth=1.3, alpha=0.95, zorder=4)

    trails = {}
    for i in range(int(t) + 1):
        for lvl, r, v in frames[i]["points"]:
            trails.setdefault(lvl, []).append((r, v))
    cur = points_at(frames, t)
    for lvl, r, v, alpha in cur:
        if alpha == 1.0 and lvl in trails:
            trails[lvl].append((r, v))
    for q in trails.values():
        if len(q) > 1:
            ax.plot([p[0] for p in q], [p[1] for p in q],
                    color=NATIVE_COLOUR, linewidth=0.8, alpha=0.13, zorder=3)

    vis = [p for p in cur if p[3] > 0.02]
    for a, b in zip(vis, vis[1:]):
        cx, cy = plot._mix_curve(a[1], a[2], b[1], b[2])
        ax.plot(cx, cy, color=NATIVE_COLOUR, linewidth=2.0,
                alpha=min(a[3], b[3]), zorder=10)
    for _lvl, r, v, alpha in vis:
        ax.plot([r], [v], marker="o", markersize=7, color=NATIVE_COLOUR,
                alpha=alpha, zorder=11)
    for lvl, r, v, alpha in (vis[0], vis[-1]) if vis else ():
        ax.annotate(f"L{lvl}", (r, v), textcoords="offset points", xytext=(5, 5),
                    fontsize=8, color=NATIVE_COLOUR, fontweight="bold", alpha=alpha)

    handles, lbls = ax.get_legend_handles_labels()
    proxy = plt.Line2D([], [], linestyle="none", marker="o", markersize=7,
                       color=NATIVE_COLOUR, label="lean-zip (native)")
    ax.legend([proxy] + handles, ["lean-zip (native)"] + lbls,
              fontsize=8, ncol=2, loc="lower right")

    ax.set_yscale("log")
    ax.set_xlim(*XLIM)
    ax.set_ylim(*YLIM)
    ax.set_xlabel("compression ratio   (compressed / original  —  ← smaller is better)")
    ax.set_ylabel("compression speed   (MB/s, log)")
    ax.grid(True, which="both", linewidth=0.4, alpha=0.6)
    ax.text(0.015, 0.985, "↖ fast & small = best", transform=ax.transAxes,
            fontsize=10, va="top", color="#2a8a3a", fontweight="bold")

    k = round(t)
    fr = frames[k]
    subject = fr["subject"]
    if len(subject) > 76:
        subject = subject[:73] + "…"
    fig.suptitle(title_of(meta), fontsize=12, fontweight="bold")
    # left-anchored so the line doesn't wobble as its width changes
    fig.text(0.075, 0.912, f"{fr['commit_date'][:10]} · {fr['commit']} · "
             f"{k + 1:2d}/{N} — {subject}",
             ha="left", fontsize=8.5, family="monospace")
    fig.text(0.5, 0.005, provenance_of(meta), ha="center", fontsize=7,
             color="#555555")
    fig.tight_layout(rect=(0, 0.03, 1, 0.90))
    fig.savefig(outfile)
    plt.close(fig)


def build_video(references, frames, meta, mp4_out, gif_out):
    if not shutil.which("ffmpeg"):
        sys.exit("--video needs ffmpeg on PATH (e.g. nix-shell -p ffmpeg)")
    import matplotlib.pyplot as plt
    N = len(frames)
    schedule = [0.0] * int(HOLD_FIRST * VIDEO_FPS)
    for i in range(N - 1):
        schedule += [i + s / TWEEN_STEPS for s in range(TWEEN_STEPS)]
    schedule += [float(N - 1)] * int(HOLD_LAST * VIDEO_FPS)
    with tempfile.TemporaryDirectory(prefix="pareto_history_") as tmp:
        for n, t in enumerate(schedule):
            draw_video_frame(plt, references, frames, meta, t,
                             Path(tmp) / f"f_{n:04d}.png")
            if n % 100 == 0:
                print(f"video frame {n}/{len(schedule)}", file=sys.stderr)
        common = ["ffmpeg", "-y", "-loglevel", "error",
                  "-framerate", str(VIDEO_FPS), "-i", f"{tmp}/f_%04d.png"]
        subprocess.run(common + ["-c:v", "libx264", "-pix_fmt", "yuv420p",
                                 "-crf", "20", str(mp4_out)], check=True)
        subprocess.run(common + [
            "-vf", "fps=15,scale=810:-1:flags=lanczos,"
                   "split[s0][s1];[s0]palettegen=max_colors=128[p];"
                   "[s1][p]paletteuse=dither=bayer:bayer_scale=4",
            "-loop", "0", str(gif_out)], check=True)
    for f in (mp4_out, gif_out):
        print(f"wrote {f} ({f.stat().st_size} bytes)", file=sys.stderr)


# --------------------------------------------------------------------------

def build_html(references, frames, meta, outfile):
    template = Path(__file__).with_name("pareto_history_player.html").read_text()
    data = json.dumps(dict(references=references, frames=frames, meta=meta))
    marker = "/*__DATA__*/null"
    if marker not in template:
        sys.exit("pareto_history_player.html is missing its /*__DATA__*/ marker")
    outfile.write_text(template.replace(marker, data))
    print(f"wrote {outfile} ({outfile.stat().st_size} bytes)", file=sys.stderr)


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--corpus", default="silesia")
    ap.add_argument("--video", action="store_true",
                    help="also render mp4 + GIF (matplotlib frames + ffmpeg)")
    ap.add_argument("--html", action="store_true",
                    help="also emit the interactive player page")
    ap.add_argument("--preview", action="store_true",
                    help="render a local preview to <stem>_preview.svg that "
                         "includes the uncommitted working-tree refresh; the file "
                         "is untracked and must NOT be committed")
    args = ap.parse_args()

    graphs = REPO / "bench/graphs"
    graphs.mkdir(parents=True, exist_ok=True)
    stem = f"{args.corpus}_compress_pareto_history"

    if args.preview:
        references, frames, meta = extract(args.corpus, include_worktree=True)
        build_svg(references, frames, meta, graphs / f"{stem}_preview.svg")
        print(f"preview written to {stem}_preview.svg (untracked — do NOT commit); "
              "commit bench/results/latest.json and re-run without --preview to "
              "regenerate the tracked SVG", file=sys.stderr)
        return

    if latest_json_dirty():
        sys.exit(
            "refusing to regenerate the committed SVG: bench/results/latest.json "
            "has uncommitted changes.\n"
            "The committed animation is built from committed history so CI's clean "
            "checkout can reproduce it byte-for-byte; a dirty latest.json would bake "
            "in a transient 'worktree' frame and a wall-clock date that CI cannot "
            "reproduce, so animation-sync would fail on the next push.\n"
            "Commit bench/results/latest.json first, then re-run.  (Use --preview to "
            "render a local, uncommitted preview instead.)")

    references, frames, meta = extract(args.corpus, include_worktree=False)
    build_svg(references, frames, meta, graphs / f"{stem}.svg")
    if args.video:
        build_video(references, frames, meta,
                    graphs / f"{stem}.mp4", graphs / f"{stem}.gif")
    if args.html:
        build_html(references, frames, meta, graphs / f"{stem}.html")


if __name__ == "__main__":
    main()
