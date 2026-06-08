#!/usr/bin/env python3
"""Render the Track D benchmark JSON into SVG graphs.

Reads bench/results/latest.json (produced by `lake exe bench-report`) and writes
SVG figures under bench/graphs/. Compares native lean-zip against each reference
implementation on compression ratio and on compress/decompress throughput, over
the **real corpora** only (synthetic patterns were removed — they misled on
every axis).

The plotting is corpus-generic: every `<corpus>/<file>` prefix present in the
data becomes its own chart set, so a new corpus (e.g. Silesia) slots in with no
code change.

Run via `bench/run.sh`, or directly:
    python bench/plot.py [results.json] [graphs_dir]
"""
import json
import math
import sys
from pathlib import Path

import matplotlib
matplotlib.use("svg")
import matplotlib.pyplot as plt

# Fixed plot order so colours/markers are stable across regenerations.
# C / SIMD references and the pure-Lean subject, plus language-native peers
# (Go / JS / Zig / OCaml) — the honest comparison group for a pure-Lean codec.
COMPRESSORS = [
    ("native",      "lean-zip (native)", "#d62728", "o"),
    ("zlib",        "zlib",              "#1f77b4", "s"),
    ("miniz_oxide", "miniz_oxide",       "#2ca02c", "^"),
    ("libdeflate",  "libdeflate",        "#9467bd", "D"),
    ("zopfli",      "zopfli",            "#ff7f0e", "v"),
    ("go",          "Go compress/flate", "#8c564b", "P"),
    ("js",          "JS fflate",         "#e377c2", "X"),
    ("zig",         "Zig std.flate",     "#bcbd22", "*"),
    ("ocaml",       "OCaml decompress",  "#17becf", "h"),
]

# Representative level for the per-file corpus bars carrying the stable
# (README-embedded) filenames; the per-level set covers every timed level.
CORPUS_LEVEL = 6


def load(path):
    with open(path) as f:
        return json.load(f)


def rows_for(results, compressor, pattern, *, level=None):
    out = []
    for r in results:
        if r["compressor"] != compressor or r["pattern"] != pattern:
            continue
        if level is not None and r["level"] != level:
            continue
        out.append(r)
    return out


def present_compressors(results):
    have = {r["compressor"] for r in results}
    return [c for c in COMPRESSORS if c[0] in have]


def corpora_in(results):
    """Corpus names present in the data, from `<corpus>/<file>` patterns."""
    return sorted({r["pattern"].split("/", 1)[0]
                   for r in results if "/" in r["pattern"]})


def corpus_patterns(results, corpus):
    """Sorted `<corpus>/<file>` patterns present in the results."""
    pref = corpus + "/"
    return sorted({r["pattern"] for r in results if r["pattern"].startswith(pref)})


def corpus_levels(results, corpus, metric):
    """Levels for which `corpus` carries `metric` data, sorted — drives the
    per-level chart set so it follows whatever the report timed."""
    pref = corpus + "/"
    return sorted({r["level"] for r in results
                   if r["pattern"].startswith(pref) and r.get(metric) is not None})


def geomean(xs):
    xs = [x for x in xs if x and x > 0]
    if not xs:
        return None
    return math.exp(sum(math.log(x) for x in xs) / len(xs))


def series_style(key, colour):
    """native is the subject — draw it solid and on top; references as hollow
    rings so coincident points stay visible."""
    native = key == "native"
    return dict(
        color=colour,
        linewidth=2.0 if native else 1.3,
        markersize=7 if native else 5,
        markerfacecolor=colour if native else "none",
        markeredgecolor=colour,
        markeredgewidth=1.3,
        zorder=10 if native else 4,
        alpha=1.0 if native else 0.95,
    )


def _provenance(meta):
    return (f"{meta.get('date','?')}  ·  {meta.get('machine','?')}  ·  "
            f"commit {meta.get('git_commit','?')}  ·  {meta.get('toolchain','?')}  ·  "
            "throughput = median snapshot; ratio is deterministic")


def _level_points(results, corpus, key, speed_metric):
    """[(level, geomean ratio, geomean speed)] for one compressor over the corpus
    files — the points of its speed-vs-ratio curve."""
    pats = corpus_patterns(results, corpus)
    levels = sorted({r["level"] for p in pats for r in rows_for(results, key, p)})
    pts = []
    for lvl in levels:
        ratios = [rows_for(results, key, p, level=lvl)[0]["ratio"]
                  for p in pats if rows_for(results, key, p, level=lvl)
                  and rows_for(results, key, p, level=lvl)[0].get("ratio") is not None]
        speeds = [rows_for(results, key, p, level=lvl)[0][speed_metric]
                  for p in pats if rows_for(results, key, p, level=lvl)
                  and rows_for(results, key, p, level=lvl)[0].get(speed_metric) is not None]
        gr, gs = geomean(ratios), geomean(speeds)
        if gr and gs:
            pts.append((lvl, gr, gs))
    return pts


def pareto_scatter(results, meta, corpus, speed_metric, speed_label, title, outfile):
    """Headline view: speed vs ratio. x = compression ratio (smaller = better,
    left), y = speed (MB/s, log). Each compressor is one line tracing its levels,
    so the whole speed/ratio tradeoff and the Pareto frontier read at a glance —
    top-left is ideal, a dominated codec sits to the lower-right. Collapses the
    per-level chart set into a single figure."""
    pats = corpus_patterns(results, corpus)
    if not pats:
        return
    fig, ax = plt.subplots(figsize=(9, 6.5))
    plotted = False
    for key, label, colour, marker in present_compressors(results):
        pts = _level_points(results, corpus, key, speed_metric)
        if not pts:
            continue
        xs = [p[1] for p in pts]
        ys = [p[2] for p in pts]
        ax.plot(xs, ys, marker=marker, label=label, **series_style(key, colour))
        # Mark the level sweep direction on the subject's curve only (avoid clutter).
        if key == "native" and len(pts) > 1:
            for idx in (0, -1):
                ax.annotate(f"L{pts[idx][0]}", (xs[idx], ys[idx]),
                            textcoords="offset points", xytext=(5, 5),
                            fontsize=7, color=colour, fontweight="bold")
        plotted = True
    if not plotted:
        plt.close(fig)
        return
    ax.set_yscale("log")
    ax.set_xlabel("compression ratio   (compressed / original  —  ← smaller is better)")
    ax.set_ylabel(speed_label + "   (MB/s, log)")
    ax.grid(True, which="both", linewidth=0.4, alpha=0.6)
    ax.legend(fontsize=8, ncol=2, loc="best")
    ax.text(0.015, 0.985, "↖ fast & small = best", transform=ax.transAxes,
            fontsize=10, va="top", color="#2a8a3a", fontweight="bold")
    fig.suptitle(f"{title}  ({corpus} — geomean over {len(pats)} files; line = level sweep)",
                 fontsize=13, fontweight="bold")
    fig.text(0.5, 0.005, _provenance(meta), ha="center", fontsize=7, color="#555")
    fig.tight_layout(rect=(0, 0.03, 1, 0.97))
    fig.savefig(outfile)
    plt.close(fig)
    print(f"wrote {outfile}")


def _geomean_at(results, corpus, key, metric, level):
    pats = corpus_patterns(results, corpus)
    vals = [rows_for(results, key, p, level=level)[0][metric]
            for p in pats if rows_for(results, key, p, level=level)
            and rows_for(results, key, p, level=level)[0].get(metric) is not None]
    return geomean(vals)


# (metric key, header, format, higher-is-better)
_SUMMARY_COLS = [("ratio", "ratio", "{:.3f}", False),
                 ("compress_mbps", "compress MB/s", "{:.0f}", True),
                 ("decompress_mbps", "decompress MB/s", "{:.0f}", True)]


def summary_table(results, meta, corpus, outfile, level=CORPUS_LEVEL):
    """Precise complement to the scatter: a colour-graded table of the geomean
    ratio / compress / decompress per codec at one level, sorted by speed."""
    rows = []
    for key, label, colour, _ in present_compressors(results):
        vals = [_geomean_at(results, corpus, key, m, level) for m, _, _, _ in _SUMMARY_COLS]
        if any(v is not None for v in vals):
            rows.append((key, label, vals))
    if not rows:
        return
    rows.sort(key=lambda r: (r[2][1] is None, -(r[2][1] or 0)))
    cmap = matplotlib.colormaps["RdYlGn"]
    ranges = []
    for j, _ in enumerate(_SUMMARY_COLS):
        vs = [r[2][j] for r in rows if r[2][j] is not None]
        ranges.append((min(vs), max(vs)))

    def colour_of(j, v):
        if v is None:
            return "#f2f2f2"
        lo, hi = ranges[j]
        t = 0.5 if hi == lo else (v - lo) / (hi - lo)
        good = t if _SUMMARY_COLS[j][3] else 1 - t      # 1 = best
        return cmap(0.15 + 0.7 * good)

    ncol = 1 + len(_SUMMARY_COLS)
    nrow = len(rows) + 1
    fig, ax = plt.subplots(figsize=(7.5, 0.45 * nrow + 0.8))
    ax.axis("off")
    ax.set_xlim(0, ncol)
    ax.set_ylim(0, nrow)
    headers = ["codec"] + [h for _, h, _, _ in _SUMMARY_COLS]
    for j, h in enumerate(headers):
        ax.text(j + 0.5, nrow - 0.5, h, ha="center", va="center",
                fontweight="bold", fontsize=9)
    for i, (key, label, vals) in enumerate(rows):
        y = nrow - 1.5 - i
        bold = "bold" if key == "native" else "normal"
        ax.text(0.5, y, label, ha="center", va="center", fontsize=8, fontweight=bold)
        for j, v in enumerate(vals):
            ax.add_patch(plt.Rectangle((j + 1, y - 0.5), 1, 1,
                                       facecolor=colour_of(j, v), edgecolor="white"))
            txt = "—" if v is None else _SUMMARY_COLS[j][2].format(v)
            ax.text(j + 1.5, y, txt, ha="center", va="center", fontsize=8, fontweight=bold)
    fig.suptitle(f"{corpus} — geomean over files, level {level}",
                 fontsize=13, fontweight="bold")
    fig.text(0.5, 0.01, _provenance(meta), ha="center", fontsize=7, color="#555")
    fig.savefig(outfile, bbox_inches="tight")
    plt.close(fig)
    print(f"wrote {outfile}")


def relative_heatmap(results, meta, corpus, metric, title, outfile, *,
                     higher_better, level=CORPUS_LEVEL, baseline="zlib"):
    """Per-file detail without 100 bars: rows = codecs, cols = files, cell =
    metric relative to `baseline` (e.g. +24% bigger than zlib). Diverging colours
    so 'worse than baseline' reads red at a glance, showing *where* a codec
    falls down (e.g. native's big-text ratio band)."""
    import numpy as np
    pats = corpus_patterns(results, corpus)
    files = [p.split("/", 1)[1] for p in pats]

    def val(key, p):
        rs = rows_for(results, key, p, level=level)
        return rs[0].get(metric) if rs else None

    M, labels = [], []
    for key, label, colour, _ in present_compressors(results):
        if key == baseline:
            continue
        row, any_v = [], False
        for p in pats:
            v, b = val(key, p), val(baseline, p)
            if v is not None and b:
                row.append(v / b - 1.0)
                any_v = True
            else:
                row.append(np.nan)
        if any_v:
            M.append(row)
            labels.append(label)
    if not M:
        return
    M = np.array(M)
    vmax = float(np.nanmax(np.abs(M))) or 0.01
    # higher_better: positive (faster) = green; ratio: positive (bigger) = red.
    cmap = "RdYlGn" if higher_better else "RdYlGn_r"
    fig, ax = plt.subplots(figsize=(max(8, len(files) * 0.75), 0.5 * len(labels) + 1.6))
    im = ax.imshow(M, cmap=cmap, vmin=-vmax, vmax=vmax, aspect="auto")
    ax.set_xticks(range(len(files)))
    ax.set_xticklabels(files, rotation=45, ha="right", fontsize=8)
    ax.set_yticks(range(len(labels)))
    ax.set_yticklabels(labels, fontsize=8)
    for i in range(len(labels)):
        for j in range(len(files)):
            if not np.isnan(M[i, j]):
                ax.text(j, i, f"{M[i, j] * 100:+.0f}", ha="center", va="center",
                        fontsize=6.5, color="black")
    fig.colorbar(im, ax=ax, fraction=0.025, pad=0.02,
                 label=f"% vs {baseline} ({'higher=faster' if higher_better else 'higher=bigger'})")
    fig.suptitle(f"{title}  ({corpus}, level {level}, relative to {baseline})",
                 fontsize=12, fontweight="bold")
    fig.text(0.5, 0.005, _provenance(meta), ha="center", fontsize=7, color="#555")
    fig.tight_layout(rect=(0, 0.03, 1, 0.96))
    fig.savefig(outfile)
    plt.close(fig)
    print(f"wrote {outfile}")


def main():
    results_path = Path(sys.argv[1]) if len(sys.argv) > 1 else Path("bench/results/latest.json")
    graphs_dir = Path(sys.argv[2]) if len(sys.argv) > 2 else Path("bench/graphs")
    graphs_dir.mkdir(parents=True, exist_ok=True)

    doc = load(results_path)
    results, meta = doc["results"], doc.get("meta", {})

    corpora = corpora_in(results)
    if not corpora:
        print("no real-corpus rows found; nothing to plot", file=sys.stderr)
        return

    for corpus in corpora:
        # Headline: speed-vs-ratio Pareto scatters (codecs as level-curves).
        pareto_scatter(results, meta, corpus, "compress_mbps", "compression speed",
                       "Compression speed vs ratio",
                       graphs_dir / f"{corpus}_compress_pareto.svg")
        pareto_scatter(results, meta, corpus, "decompress_mbps", "decompression speed",
                       "Decompression speed vs ratio",
                       graphs_dir / f"{corpus}_decompress_pareto.svg")
        # Precise: colour-graded geomean summary table.
        summary_table(results, meta, corpus, graphs_dir / f"{corpus}_summary.svg")
        # Per-file detail: relative-to-zlib heatmaps (ratio + compress speed).
        relative_heatmap(results, meta, corpus, "ratio", "Compression ratio vs zlib",
                         graphs_dir / f"{corpus}_ratio_heatmap.svg", higher_better=False)
        relative_heatmap(results, meta, corpus, "compress_mbps", "Compression speed vs zlib",
                         graphs_dir / f"{corpus}_compress_heatmap.svg", higher_better=True)


if __name__ == "__main__":
    main()
