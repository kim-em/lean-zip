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


def corpus_bars(results, meta, corpus, metric, ylabel, title, outfile, *,
                logy, level=CORPUS_LEVEL):
    """Per-file grouped bar chart for one real corpus: one x-tick per file, one
    bar per compressor, at a single level. Real-corpus files are single-size, so
    grouped bars (not a size sweep) are the right view."""
    pats = corpus_patterns(results, corpus)
    if not pats:
        return
    def val(key, pat):
        rs = rows_for(results, key, pat, level=level)
        return rs[0].get(metric) if rs else None
    comps = [c for c in present_compressors(results)
             if any(val(c[0], p) is not None for p in pats)]
    if not comps:
        return
    n = len(comps)
    width = 0.8 / n
    xs = list(range(len(pats)))
    fig, ax = plt.subplots(figsize=(max(11, len(pats) * 1.1), 6))
    for i, (key, label, colour, _marker) in enumerate(comps):
        pos, ys = [], []
        for x, p in zip(xs, pats):
            y = val(key, p)
            if y is not None:
                pos.append(x + (i - (n - 1) / 2) * width)
                ys.append(y)
        ax.bar(pos, ys, width=width, label=label, color=colour,
               edgecolor="black" if key == "native" else colour,
               linewidth=0.8 if key == "native" else 0.4,
               zorder=10 if key == "native" else 4)
    ax.set_xticks(xs)
    ax.set_xticklabels([p.split("/", 1)[1] for p in pats],
                       rotation=45, ha="right", fontsize=8)
    if logy:
        ax.set_yscale("log")
    ax.set_ylabel(ylabel)
    ax.grid(True, axis="y", which="both", linewidth=0.4, alpha=0.6)
    ax.legend(fontsize=8, ncol=2, loc="best")
    fig.suptitle(f"{title}  ({corpus}, level {level})",
                 fontsize=13, fontweight="bold")
    fig.text(0.5, 0.005, _provenance(meta), ha="center", fontsize=7, color="#555")
    fig.tight_layout(rect=(0, 0.03, 1, 0.97))
    fig.savefig(outfile)
    plt.close(fig)
    print(f"wrote {outfile}")


def corpus_vs_level(results, meta, corpus, metric, ylabel, title, outfile, *, logy):
    """Aggregate line chart: metric (geomean over the corpus files) vs level,
    one line per compressor. The headline shape of the corpus across levels."""
    pats = corpus_patterns(results, corpus)
    levels = corpus_levels(results, corpus, metric)
    if not pats or not levels:
        return
    fig, ax = plt.subplots(figsize=(9, 6))
    plotted = False
    for key, label, colour, marker in present_compressors(results):
        xs, ys = [], []
        for lvl in levels:
            vals = []
            for p in pats:
                rs = rows_for(results, key, p, level=lvl)
                if rs and rs[0].get(metric) is not None:
                    vals.append(rs[0][metric])
            g = geomean(vals)
            if g is not None:
                xs.append(lvl)
                ys.append(g)
        if xs:
            ax.plot(xs, ys, marker=marker, label=label, **series_style(key, colour))
            plotted = True
    if not plotted:
        plt.close(fig)
        return
    if logy:
        ax.set_yscale("log")
    ax.set_xlabel("compression level")
    ax.set_ylabel(ylabel)
    ax.grid(True, which="both", linewidth=0.4, alpha=0.6)
    ax.legend(fontsize=8, ncol=2, loc="best")
    fig.suptitle(f"{title}  ({corpus}, geomean over files)",
                 fontsize=13, fontweight="bold")
    fig.text(0.5, 0.005, _provenance(meta), ha="center", fontsize=7, color="#555")
    fig.tight_layout(rect=(0, 0.03, 1, 0.97))
    fig.savefig(outfile)
    plt.close(fig)
    print(f"wrote {outfile}")


# (metric key, ylabel, title, filename stem, log y-axis)
THROUGHPUT_FIGS = [
    ("compress_mbps",   "throughput (MB/s)", "Compression throughput per file",
     "compress_throughput", True),
    ("decompress_mbps", "throughput (MB/s)", "Decompression throughput per file",
     "decompress_throughput", True),
    ("ratio", "ratio (compressed / original)", "Compression ratio per file",
     "ratio", False),
]


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
        for metric, ylabel, title, stem, logy in THROUGHPUT_FIGS:
            # Canonical level-6 per-file bars (stable filenames for README embeds).
            corpus_bars(results, meta, corpus, metric, ylabel, title,
                        graphs_dir / f"{corpus}_{stem}.svg", logy=logy)
            # One per-file bar chart per timed level: <corpus>_<stem>_L<n>.svg.
            for lvl in corpus_levels(results, corpus, metric):
                corpus_bars(results, meta, corpus, metric, ylabel, title,
                            graphs_dir / f"{corpus}_{stem}_L{lvl}.svg",
                            logy=logy, level=lvl)
            # Aggregate (geomean over files) vs level.
            vs_label = ylabel + (", geomean" if metric != "ratio" else " (geomean)")
            vs_title = title.replace("per file", "vs level")
            corpus_vs_level(results, meta, corpus, metric, vs_label, vs_title,
                            graphs_dir / f"{corpus}_{stem}_vs_level.svg", logy=logy)


if __name__ == "__main__":
    main()
