#!/usr/bin/env python3
"""Render the Track D benchmark JSON into log-scale SVG graphs.

Reads bench/results/latest.json (produced by `lake exe bench-report`) and writes
SVG figures under bench/graphs/. Compares native lean-zip against each reference
implementation on compression ratio and on compress/decompress throughput.

Run via `bench/run.sh`, or directly:
    python bench/plot.py [results.json] [graphs_dir]
"""
import json
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
PATTERNS = ["constant", "cyclic", "prng", "text"]
SIZE_LEVEL = 6     # level used for the size-sweep figures
LEVEL_SIZE = 65536  # size used for the ratio-vs-level figure

# Real corpora rendered as per-file grouped-bar charts (their files are
# single-size, so the synthetic size-sweep figures don't apply).
CORPORA = ["canterbury"]
CORPUS_LEVEL = 6   # representative level for the per-file corpus bars


def load(path):
    with open(path) as f:
        return json.load(f)


def rows_for(results, compressor, pattern, *, level=None, size=None):
    out = []
    for r in results:
        if r["compressor"] != compressor or r["pattern"] != pattern:
            continue
        if level is not None and r["level"] != level:
            continue
        if size is not None and r["size"] != size:
            continue
        out.append(r)
    return out


def present_compressors(results):
    have = {r["compressor"] for r in results}
    return [c for c in COMPRESSORS if c[0] in have]


def series_style(key, colour):
    """native is the subject — draw it solid and on top; references as hollow
    rings so coincident points (common on compressible data) stay visible."""
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


def size_sweep(results, meta, metric, ylabel, title, outfile, *, logy, level=SIZE_LEVEL):
    """One 2x2 figure (subplot per pattern): metric vs input size, line per
    compressor, at `level`. Log x; log y iff logy."""
    fig, axes = plt.subplots(2, 2, figsize=(11, 8), sharex=True)
    comps = present_compressors(results)
    for ax, pat in zip(axes.flat, PATTERNS):
        for key, label, colour, marker in comps:
            rs = sorted(rows_for(results, key, pat, level=level),
                        key=lambda r: r["size"])
            xs = [r["size"] for r in rs if r.get(metric) is not None]
            ys = [r[metric] for r in rs if r.get(metric) is not None]
            if xs:
                ax.plot(xs, ys, marker=marker, label=label,
                        **series_style(key, colour))
        ax.set_xscale("log", base=2)
        if logy:
            ax.set_yscale("log")
        ax.set_title(f"{pat} data", fontsize=10)
        ax.grid(True, which="both", linewidth=0.4, alpha=0.6)
        ax.set_xlabel("input size (bytes)")
        ax.set_ylabel(ylabel)
    axes.flat[0].legend(fontsize=8, loc="best")
    fig.suptitle(f"{title}  (level {level})", fontsize=13, fontweight="bold")
    fig.text(0.5, 0.005, _provenance(meta), ha="center", fontsize=7, color="#555")
    fig.tight_layout(rect=(0, 0.02, 1, 0.97))
    fig.savefig(outfile)
    plt.close(fig)
    print(f"wrote {outfile}")


def timed_levels(results, metric="compress_mbps"):
    """Levels that actually carry timing data, sorted — drives the per-level
    chart set so it follows whatever the report timed (e.g. [1,6,9] or [1..9])."""
    return sorted({r["level"] for r in results if r.get(metric) is not None})


def ratio_by_level(results, meta, outfile):
    """Compression ratio vs level at LEVEL_SIZE, subplot per pattern."""
    fig, axes = plt.subplots(2, 2, figsize=(11, 8), sharex=True)
    comps = present_compressors(results)
    for ax, pat in zip(axes.flat, PATTERNS):
        for key, label, colour, marker in comps:
            rs = sorted(rows_for(results, key, pat, size=LEVEL_SIZE),
                        key=lambda r: r["level"])
            xs = [r["level"] for r in rs]
            ys = [r["ratio"] for r in rs]
            if xs:
                ax.plot(xs, ys, marker=marker, label=label,
                        **series_style(key, colour))
        ax.set_title(f"{pat} data", fontsize=10)
        ax.grid(True, which="both", linewidth=0.4, alpha=0.6)
        ax.set_xlabel("compression level")
        ax.set_ylabel("ratio (compressed / original)")
    axes.flat[0].legend(fontsize=8, loc="best")
    fig.suptitle(f"Compression ratio vs level  ({LEVEL_SIZE} bytes; lower is better)",
                 fontsize=13, fontweight="bold")
    fig.text(0.5, 0.005, _provenance(meta), ha="center", fontsize=7, color="#555")
    fig.tight_layout(rect=(0, 0.02, 1, 0.97))
    fig.savefig(outfile)
    plt.close(fig)
    print(f"wrote {outfile}")


def corpus_patterns(results, corpus):
    """Sorted `<corpus>/<file>` patterns present in the results."""
    pref = corpus + "/"
    return sorted({r["pattern"] for r in results if r["pattern"].startswith(pref)})


def corpus_bars(results, meta, corpus, metric, ylabel, title, outfile, *,
                logy, level=CORPUS_LEVEL):
    """Per-file grouped bar chart for one real corpus: one x-tick per file, one
    bar per compressor, at a representative level. Real-corpus files are
    single-size, so this replaces the synthetic size-sweep view."""
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


def _provenance(meta):
    return (f"{meta.get('date','?')}  ·  {meta.get('machine','?')}  ·  "
            f"commit {meta.get('git_commit','?')}  ·  {meta.get('toolchain','?')}  ·  "
            "throughput = median snapshot; ratio is deterministic")


def main():
    results_path = Path(sys.argv[1]) if len(sys.argv) > 1 else Path("bench/results/latest.json")
    graphs_dir = Path(sys.argv[2]) if len(sys.argv) > 2 else Path("bench/graphs")
    graphs_dir.mkdir(parents=True, exist_ok=True)

    doc = load(results_path)
    results, meta = doc["results"], doc.get("meta", {})

    # Canonical level-6 figures (stable filenames for the README embeds).
    size_sweep(results, meta, "compress_mbps", "throughput (MB/s)",
               "Compression throughput vs input size",
               graphs_dir / "compress_throughput.svg", logy=True)
    size_sweep(results, meta, "decompress_mbps", "throughput (MB/s)",
               "Decompression throughput vs input size",
               graphs_dir / "decompress_throughput.svg", logy=True)
    # One throughput figure per timed level (e.g. compress_throughput_L1.svg …).
    for lvl in timed_levels(results, "compress_mbps"):
        size_sweep(results, meta, "compress_mbps", "throughput (MB/s)",
                   "Compression throughput vs input size",
                   graphs_dir / f"compress_throughput_L{lvl}.svg", logy=True, level=lvl)
    for lvl in timed_levels(results, "decompress_mbps"):
        size_sweep(results, meta, "decompress_mbps", "throughput (MB/s)",
                   "Decompression throughput vs input size",
                   graphs_dir / f"decompress_throughput_L{lvl}.svg", logy=True, level=lvl)
    size_sweep(results, meta, "ratio", "ratio (compressed / original)",
               "Compression ratio vs input size",
               graphs_dir / "compression_ratio.svg", logy=False)
    ratio_by_level(results, meta, graphs_dir / "ratio_by_level.svg")

    # Real-corpus per-file bar charts (single-size files ⇒ no size sweep).
    for corpus in CORPORA:
        corpus_bars(results, meta, corpus, "compress_mbps", "throughput (MB/s)",
                    "Compression throughput per file",
                    graphs_dir / f"{corpus}_compress_throughput.svg", logy=True)
        corpus_bars(results, meta, corpus, "decompress_mbps", "throughput (MB/s)",
                    "Decompression throughput per file",
                    graphs_dir / f"{corpus}_decompress_throughput.svg", logy=True)
        corpus_bars(results, meta, corpus, "ratio", "ratio (compressed / original)",
                    "Compression ratio per file",
                    graphs_dir / f"{corpus}_ratio.svg", logy=False)


if __name__ == "__main__":
    main()
