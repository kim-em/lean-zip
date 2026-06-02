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
COMPRESSORS = [
    ("native",      "lean-zip (native)", "#d62728", "o"),
    ("zlib",        "zlib",              "#1f77b4", "s"),
    ("miniz_oxide", "miniz_oxide",       "#2ca02c", "^"),
    ("libdeflate",  "libdeflate",        "#9467bd", "D"),
    ("zopfli",      "zopfli",            "#ff7f0e", "v"),
]
PATTERNS = ["constant", "cyclic", "prng", "text"]
SIZE_LEVEL = 6     # level used for the size-sweep figures
LEVEL_SIZE = 65536  # size used for the ratio-vs-level figure


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


def size_sweep(results, meta, metric, ylabel, title, outfile, *, logy):
    """One 2x2 figure (subplot per pattern): metric vs input size, line per
    compressor, at SIZE_LEVEL. Log x; log y iff logy."""
    fig, axes = plt.subplots(2, 2, figsize=(11, 8), sharex=True)
    comps = present_compressors(results)
    for ax, pat in zip(axes.flat, PATTERNS):
        for key, label, colour, marker in comps:
            rs = sorted(rows_for(results, key, pat, level=SIZE_LEVEL),
                        key=lambda r: r["size"])
            xs = [r["size"] for r in rs if r.get(metric) is not None]
            ys = [r[metric] for r in rs if r.get(metric) is not None]
            if xs:
                ax.plot(xs, ys, marker=marker, color=colour, label=label,
                        linewidth=1.6, markersize=5)
        ax.set_xscale("log", base=2)
        if logy:
            ax.set_yscale("log")
        ax.set_title(f"{pat} data", fontsize=10)
        ax.grid(True, which="both", linewidth=0.4, alpha=0.6)
        ax.set_xlabel("input size (bytes)")
        ax.set_ylabel(ylabel)
    axes.flat[0].legend(fontsize=8, loc="best")
    fig.suptitle(f"{title}  (level {SIZE_LEVEL})", fontsize=13, fontweight="bold")
    fig.text(0.5, 0.005, _provenance(meta), ha="center", fontsize=7, color="#555")
    fig.tight_layout(rect=(0, 0.02, 1, 0.97))
    fig.savefig(outfile)
    plt.close(fig)
    print(f"wrote {outfile}")


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
                ax.plot(xs, ys, marker=marker, color=colour, label=label,
                        linewidth=1.6, markersize=5)
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

    size_sweep(results, meta, "compress_mbps", "throughput (MB/s)",
               "Compression throughput vs input size",
               graphs_dir / "compress_throughput.svg", logy=True)
    size_sweep(results, meta, "decompress_mbps", "throughput (MB/s)",
               "Decompression throughput vs input size",
               graphs_dir / "decompress_throughput.svg", logy=True)
    size_sweep(results, meta, "ratio", "ratio (compressed / original)",
               "Compression ratio vs input size",
               graphs_dir / "compression_ratio.svg", logy=False)
    ratio_by_level(results, meta, graphs_dir / "ratio_by_level.svg")


if __name__ == "__main__":
    main()
