#!/usr/bin/env python3
"""Before/after native speed-vs-ratio graphs for a lean-zip performance PR.

Plots the chosen throughput metric (log y) against compression ratio (x) for
native BEFORE vs native AFTER, overlaid on the existing other-language curves
(reused from bench/results/latest.json — never re-measured). One chart per
corpus. Also prints a per-level before/after geomean table to stdout.

Usage:
  plot_before_after.py <before.json> <after.json> <metric> [latest.json] [outdir]

  metric : compress_mbps   (compression PRs — the interesting case: the
                            optimization can move BOTH ratio and speed, so the
                            speed-vs-ratio Pareto frontier is what to read)
           decompress_mbps (decode PRs — no ratio/speed tradeoff; this is just
                            a throughput-vs-ratio scatter for context)

  latest.json defaults to bench/results/latest.json
  outdir      defaults to bench/graphs

The before/after jsons are the native rows from `bench-report --native-only`
run on master (before) and the PR branch (after); see SKILL.md.
"""
import json, math, sys
from pathlib import Path
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

before_path, after_path, metric = sys.argv[1], sys.argv[2], sys.argv[3]
latest_path = sys.argv[4] if len(sys.argv) > 4 else "bench/results/latest.json"
outdir = Path(sys.argv[5] if len(sys.argv) > 5 else "bench/graphs")
assert metric in ("compress_mbps", "decompress_mbps"), f"bad metric {metric}"
outdir.mkdir(parents=True, exist_ok=True)

BEFORE = json.load(open(before_path))["results"]
AFTER  = json.load(open(after_path))["results"]
LATEST_DOC = json.load(open(latest_path))
LATEST = LATEST_DOC["results"]
LMETA  = LATEST_DOC.get("meta", {})

# Other-language / reference curves reused from latest.json (not re-measured).
# (compressor key, label, colour, marker)
REFS = [
    ("zlib",        "zlib (C)",            "#1f77b4", "s"),
    ("miniz_oxide", "miniz_oxide (Rust)",  "#2ca02c", "^"),
    ("libdeflate",  "libdeflate (C+SIMD)", "#9467bd", "D"),
    ("go",          "Go compress/flate",   "#8c564b", "P"),
    ("js",          "JS fflate",           "#e377c2", "X"),
    ("zig",         "Zig std.flate",       "#bcbd22", "*"),
    ("ocaml",       "OCaml decompress",    "#17becf", "h"),
]

def geomean(xs):
    xs = [x for x in xs if x and x > 0]
    return math.exp(sum(math.log(x) for x in xs) / len(xs)) if xs else None

def corpora(rows):
    return sorted({r["pattern"].split("/")[0] for r in rows})

def files(rows, corpus):
    return sorted({r["pattern"] for r in rows if r["pattern"].startswith(corpus + "/")})

def find(rows, comp, pat, lvl):
    for r in rows:
        if r["compressor"] == comp and r["pattern"] == pat and r["level"] == lvl:
            return r
    return None

def levels(rows, comp, corpus):
    return sorted({r["level"] for r in rows
                   if r["compressor"] == comp and r["pattern"].startswith(corpus + "/")})

def curve(rows, comp, corpus):
    """[(geomean ratio, geomean metric)] per level — points of the speed-vs-ratio curve."""
    pts = []
    for lvl in levels(rows, comp, corpus):
        fs = files(rows, corpus)
        rs = [find(rows, comp, p, lvl)["ratio"] for p in fs
              if find(rows, comp, p, lvl) and find(rows, comp, p, lvl).get("ratio") is not None]
        ss = [find(rows, comp, p, lvl)[metric] for p in fs
              if find(rows, comp, p, lvl) and find(rows, comp, p, lvl).get(metric) is not None]
        gr, gs = geomean(rs), geomean(ss)
        if gr and gs:
            pts.append((gr, gs))
    return sorted(pts)

label_speed = "compression speed" if metric == "compress_mbps" else "decode throughput"

for corpus in corpora(AFTER):
    fig, ax = plt.subplots(figsize=(10, 6.5))
    # other-language context (reused), drawn as hollow rings underneath
    for comp, lab, col, mk in REFS:
        pts = curve(LATEST, comp, corpus)
        if not pts:
            continue
        ax.plot([p[0] for p in pts], [p[1] for p in pts], marker=mk, color=col,
                lw=1.3, ms=5, alpha=0.9, zorder=4,
                markerfacecolor="none", markeredgecolor=col, label=lab)
    # native before (grey dashed) and after (solid red), on top
    pb = curve(BEFORE, "native", corpus)
    if pb:
        ax.plot([p[0] for p in pb], [p[1] for p in pb], marker="o", color="#7f7f7f",
                lw=2.2, ms=7, ls="--", zorder=11,
                markerfacecolor="none", markeredgecolor="#7f7f7f",
                label="lean-zip native — before")
    pa = curve(AFTER, "native", corpus)
    if pa:
        ax.plot([p[0] for p in pa], [p[1] for p in pa], marker="o", color="#d62728",
                lw=2.6, ms=8, zorder=12, label="lean-zip native — AFTER")
    ax.set_yscale("log")
    ax.set_xlabel("compression ratio  (compressed / original — ← smaller = more compressed)")
    ax.set_ylabel(f"{label_speed}  (MB/s, log)")
    ax.set_title(f"DEFLATE {label_speed} vs ratio — {corpus}\n"
                 f"native before/after; other languages reused "
                 f"({LMETA.get('machine','?')}; geomean over {len(files(AFTER, corpus))} files)")
    ax.grid(True, which="both", ls=":", alpha=0.4)
    ax.legend(fontsize=8, ncol=2, loc="best")
    fig.tight_layout()
    stem = outdir / f"perf_before_after_{metric}_{corpus}"
    fig.savefig(str(stem) + ".svg")
    fig.savefig(str(stem) + ".png", dpi=130)
    print(f"wrote {stem}.png / .svg")

    print(f"\n=== {corpus}: native {metric} geomean by level ===")
    print(f"{'lvl':>3} {'ratio':>7} {'before':>9} {'after':>9} {'speedup':>8}")
    for lvl in levels(AFTER, "native", corpus):
        fs = files(AFTER, corpus)
        b = geomean([find(BEFORE, "native", p, lvl)[metric] for p in fs
                     if find(BEFORE, "native", p, lvl) and find(BEFORE, "native", p, lvl).get(metric)])
        a = geomean([find(AFTER, "native", p, lvl)[metric] for p in fs
                     if find(AFTER, "native", p, lvl) and find(AFTER, "native", p, lvl).get(metric)])
        r = geomean([find(AFTER, "native", p, lvl)["ratio"] for p in fs
                     if find(AFTER, "native", p, lvl)])
        if a and b and r:
            print(f"{lvl:>3} {r:>7.3f} {b:>9.1f} {a:>9.1f} {a/b:>7.2f}x")
