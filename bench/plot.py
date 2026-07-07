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


def _level_points(results, corpus, key, speed_metric, ratio_mode="geomean"):
    """[(level, ratio, geomean speed)] for one compressor over the corpus files —
    the points of its speed-vs-ratio curve.

    ``ratio_mode`` selects how the per-file ratios are aggregated into the x-value:
    - "geomean": geometric mean of the per-file ratios (equal weight per file).
    - "pooled":  sum(compressed) / sum(uncompressed) over the corpus — the true
      corpus-wide ratio, byte-weighted so large files count proportionally.
    Speed is the geomean over files — in "pooled" mode over the *same* sized
    files the ratio pools, so a point never mixes a corpus-wide ratio with a
    differently-covered speed."""
    if ratio_mode not in ("geomean", "pooled"):
        raise ValueError(f"ratio_mode must be 'geomean' or 'pooled', got {ratio_mode!r}")
    pats = corpus_patterns(results, corpus)
    levels = sorted({r["level"] for p in pats for r in rows_for(results, key, p)})
    pts = []
    for lvl in levels:
        rows = [rows_for(results, key, p, level=lvl)[0]
                for p in pats if rows_for(results, key, p, level=lvl)]
        if ratio_mode == "pooled":
            sized = [r for r in rows if r.get("out_size") is not None and r.get("size")]
            den = sum(r["size"] for r in sized)
            gr = (sum(r["out_size"] for r in sized) / den) if den else None
            speed_rows = sized                      # coverage-match ratio and speed
        else:
            gr = geomean([r["ratio"] for r in rows if r.get("ratio") is not None])
            speed_rows = rows
        gs = geomean([r[speed_metric] for r in speed_rows if r.get(speed_metric) is not None])
        if gr and gs:
            pts.append((lvl, gr, gs))
    return pts


def _mix_curve(x0, y0, x1, y1, n=48):
    """Operating points reachable by compressing a byte-fraction `f` of the input
    at the higher-effort level and `1-f` at the lower one — the *achievable*
    frontier between two adjacent levels, and the honest connector between them.

    Ratio is additive in bytes, so it is linear in `f`; wall-clock time is
    additive, so **1/throughput** is linear in `f` (throughput itself is not).
    The frontier is therefore a straight line only in (ratio, time-per-byte)
    space — NOT a straight segment on the (ratio, MB/s) axis, and emphatically
    not on the log-MB/s axis, where a straight segment sags *above* the real
    frontier and overstates the speed reachable at an intermediate ratio. A new
    operating point is genuinely outside the frontier only if it sits above this
    curve (faster at equal ratio), never merely above the straight segment.

    Exact for a single workload; the dashboard points are per-file geomeans, so
    between two geomean points this is the mixing curve of the aggregate (a close
    proxy for, not literally, the corpus-geomean achievable set). See
    bench/README.md ("Reading the Pareto")."""
    if not (y0 > 0 and y1 > 0):          # 1/speed undefined — fall back to a segment
        return [x0, x1], [y0, y1]
    xs, ys = [], []
    for i in range(n + 1):
        f = i / n
        xs.append((1.0 - f) * x0 + f * x1)
        ys.append(1.0 / ((1.0 - f) / y0 + f / y1))
    return xs, ys


def pareto_scatter(results, meta, corpus, speed_metric, speed_label, title, outfile,
                   ratio_mode="geomean"):
    """Headline view: speed vs ratio. x = compression ratio (smaller = better,
    left), y = speed (MB/s, log). Each compressor is markers at its measured
    levels joined by the *mixing frontier* — the operating points reachable by
    blending two adjacent levels (`_mix_curve`), which is the physically
    achievable connector, unlike a straight segment on the log axis. So the whole
    speed/ratio tradeoff and the achievable frontier read at a glance — top-left
    is ideal; a point is outside a codec's frontier only if it sits above that
    codec's mixing curve, not merely above the straight level-to-level segment.
    Collapses the per-level chart set into a single figure."""
    pats = corpus_patterns(results, corpus)
    if not pats:
        return
    fig, ax = plt.subplots(figsize=(9, 6.5))
    plotted = False
    for key, label, colour, marker in present_compressors(results):
        pts = _level_points(results, corpus, key, speed_metric, ratio_mode)
        if not pts:
            continue
        style = series_style(key, colour)
        xs = [p[1] for p in pts]
        ys = [p[2] for p in pts]
        # Markers at the real (measured) level points carry the legend entry.
        ax.plot(xs, ys, linestyle="none", marker=marker, label=label,
                **{k: v for k, v in style.items() if k != "linewidth"})
        # Connectors are the achievable mixing frontier between consecutive
        # levels, not straight segments (see `_mix_curve`). A single-point series
        # (e.g. the frozen zopfli ceiling) has no connector — just its marker.
        for a in range(len(pts) - 1):
            cx, cy = _mix_curve(xs[a], ys[a], xs[a + 1], ys[a + 1])
            ax.plot(cx, cy, color=colour, linewidth=style["linewidth"],
                    alpha=style["alpha"], zorder=style["zorder"])
        # Mark the level sweep direction on the subject's curve only (avoid clutter).
        # When several levels land on the same plotted point (e.g. an above-64 MiB
        # input where L9's optimal parse is gated off, so L9 and L10 emit
        # byte-identical output and stack), label the endpoint with EVERY level
        # there — "L9=L10", never a lone "L10" with an invisible twin beneath it.
        # Coincidence keys on the ratio being identical (dx < 1e-6: ratios are
        # deterministic, so identical-output twins share a ratio exactly, while
        # distinct-on-plot levels differ by ≥~3e-4 at the report's 4-dp rounding),
        # with a loose speed window (dy < 5e-2) to absorb single-rep timing noise.
        # On a healthy sweep no two levels share a ratio, so this stays inert.
        if key == "native" and len(pts) > 1:
            def _stacked_levels(idx):
                out = []
                for j in range(len(pts)):
                    dx = abs(xs[j] - xs[idx]) / xs[idx]
                    dy = abs(math.log(ys[j]) - math.log(ys[idx]))
                    if dx < 1e-6 and dy < 5e-2:      # same plotted marker
                        out.append(pts[j][0])
                return sorted(set(out))
            labelled = set()
            for idx in (0, -1):
                stacked = _stacked_levels(idx)
                if tuple(stacked) in labelled:       # both endpoints in one stack
                    continue
                labelled.add(tuple(stacked))
                if len(stacked) > 1:
                    print(f"  note: {label} levels {stacked} share one marker on "
                          f"{corpus}'s Pareto — labelled together",
                          file=sys.stderr)
                ax.annotate("=".join(f"L{lv}" for lv in stacked), (xs[idx], ys[idx]),
                            textcoords="offset points", xytext=(5, 5),
                            fontsize=7, color=colour, fontweight="bold")
        plotted = True
    if not plotted:
        plt.close(fig)
        return
    pooled = ratio_mode == "pooled"
    xlab = ("compression ratio   (Σ compressed / Σ original  —  ← smaller is better)"
            if pooled else
            "compression ratio   (compressed / original  —  ← smaller is better)")
    ratio_agg = ("corpus-pooled ratio, geomean speed" if pooled
                 else f"geomean over {len(pats)} files")
    ax.set_yscale("log")
    ax.set_xlabel(xlab)
    ax.set_ylabel(speed_label + "   (MB/s, log)")
    ax.grid(True, which="both", linewidth=0.4, alpha=0.6)
    ax.legend(fontsize=8, ncol=2, loc="best")
    ax.text(0.015, 0.985, "↖ fast & small = best", transform=ax.transAxes,
            fontsize=10, va="top", color="#2a8a3a", fontweight="bold")
    fig.suptitle(f"{title}  ({corpus} — {ratio_agg})",
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


# Representative libdeflate level for the decode-density charts: one point per
# file at a single encode level, so the x-spread is the cross-file content range
# (text ~0.27 → incompressible ~0.9), not the narrow per-level range.
DECODE_LEVEL = 6


def _decoders_present(results, pref):
    have = {r["compressor"] for r in results if r["pattern"].startswith(pref)}
    return [k for (k, *_rest) in COMPRESSORS if k in have]


def _decode_pts(results, pref, key, level):
    return sorted((r["ratio"], r["decompress_mbps"]) for r in results
                  if r["compressor"] == key and r["level"] == level
                  and r["pattern"].startswith(pref)
                  and r.get("ratio") and r.get("decompress_mbps"))


def decode_density_plot(results, meta, corpus, outfile, level=DECODE_LEVEL):
    """Per-file decode throughput vs input density — the decompression analogue of
    the compress Pareto. Each file is compressed by the SAME encoder (libdeflate
    L{level}); x = that file's compression ratio (wide: ~0.27 text → ~0.9
    incompressible), y = decode MB/s (log). One point per (decoder, file) on
    byte-identical input, so it isolates decoder speed AND shows content-dependence
    (literal-heavy incompressible data vs match-heavy text). memcpy = the
    memory-bandwidth ceiling. Not a Pareto: density is exogenous to the decoder, so
    the highest band wins."""
    pref = corpus + "/"
    colour_of = {k: c for (k, _l, c, _m) in COMPRESSORS}
    label_of = {k: l for (k, l, _c, _m) in COMPRESSORS}
    marker_of = {k: m for (k, _l, _c, m) in COMPRESSORS}
    decoders = _decoders_present(results, pref)
    if not decoders:
        return
    fig, ax = plt.subplots(figsize=(9, 6.5))
    plotted = False
    for key in decoders:
        pts = _decode_pts(results, pref, key, level)
        if not pts:
            continue
        xs, ys = [p[0] for p in pts], [p[1] for p in pts]
        st = series_style(key, colour_of.get(key, "#888888"))
        st["linewidth"] = 0  # true scatter: one marker per file, no connecting line
        ax.plot(xs, ys, marker=marker_of.get(key, "o"), linestyle="none",
                label=label_of.get(key, key), **st)
        plotted = True
    mc = [r["decompress_mbps"] for r in results if r["compressor"] == "memcpy"
          and r["level"] == level and r["pattern"].startswith(pref) and r.get("decompress_mbps")]
    if mc:
        g = geomean(mc)
        ax.axhline(g, linestyle="--", color="#777777", linewidth=1.4, zorder=2)
        ax.text(0.995, g, f" memcpy ceiling ≈ {g/1000:.0f} GB/s",
                transform=ax.get_yaxis_transform(), ha="right", va="bottom",
                fontsize=8, color="#777777")
        plotted = True
    if not plotted:
        plt.close(fig)
        return
    ax.set_yscale("log")
    ax.set_xlabel(f"input compression ratio   (libdeflate L{level} per file  —  ← denser / more compressible)")
    ax.set_ylabel("decompression throughput   (MB/s, log)")
    ax.grid(True, which="both", linewidth=0.4, alpha=0.6)
    ax.legend(fontsize=8, ncol=2, loc="best")
    ax.text(0.015, 0.985, "↑ faster = better", transform=ax.transAxes,
            fontsize=10, va="top", color="#2a8a3a", fontweight="bold")
    npat = len({r["pattern"] for r in results if r["pattern"].startswith(pref)})
    fig.suptitle(f"Decode throughput vs input density  ({corpus} — {npat} files, one point each; "
                 f"all decoders on identical libdeflate L{level} streams)",
                 fontsize=12, fontweight="bold")
    fig.text(0.5, 0.005, _provenance(meta), ha="center", fontsize=7, color="#555")
    fig.tight_layout(rect=(0, 0.03, 1, 0.97))
    fig.savefig(outfile)
    plt.close(fig)
    print(f"wrote {outfile}")


def decode_ranking_plot(results, meta, corpus, outfile, level=DECODE_LEVEL):
    """Decode throughput ranking (lollipop) on identical libdeflate L{level}
    streams, geomean over the corpus files, log x. native is the subject; memcpy is
    the bandwidth ceiling (its distance shows the headroom)."""
    pref = corpus + "/"
    colour_of = {k: c for (k, _l, c, _m) in COMPRESSORS}
    label_of = {k: l for (k, l, _c, _m) in COMPRESSORS}

    def gm_at(key):
        return geomean([r["decompress_mbps"] for r in results
                        if r["compressor"] == key and r["level"] == level
                        and r["pattern"].startswith(pref) and r.get("decompress_mbps")])

    vals = [(k, gm_at(k)) for k in _decoders_present(results, pref)]
    vals = [(k, v) for k, v in vals if v]
    if not vals:
        return
    vals.sort(key=lambda kv: kv[1])  # slowest at the bottom
    fig, ax = plt.subplots(figsize=(8, 5))
    ys = list(range(len(vals)))
    xmin = min(v for _, v in vals) * 0.8
    ceiling = gm_at("memcpy")
    for y, (k, v) in zip(ys, vals):
        c = colour_of.get(k, "#888888")
        is_native = k == "native"
        ax.hlines(y, xmin, v, color=c, linewidth=2.4 if is_native else 1.3, alpha=0.9)
        ax.plot(v, y, "o", color=c, markersize=10 if is_native else 6, zorder=5)
        ax.text(v * 1.05, y, f"{v:.0f}", va="center", fontsize=8.5, color=c,
                fontweight="bold" if is_native else "normal")
    ax.set_yticks(ys)
    ax.set_yticklabels([label_of.get(k, k) + ("  ◄ subject" if k == "native" else "")
                        for k, _ in vals], fontsize=9)
    ax.set_xscale("log")
    if ceiling:
        ax.axvline(ceiling, linestyle="--", color="#777777", linewidth=1.4)
        ax.text(ceiling, len(vals) - 0.4, f"memcpy ≈ {ceiling/1000:.0f} GB/s ",
                rotation=90, ha="right", va="top", fontsize=8, color="#777777")
        ax.set_xlim(xmin, ceiling * 1.4)
    ax.set_xlabel("decompression throughput   (MB/s, log)  —  geomean over files")
    ax.grid(True, axis="x", which="both", linewidth=0.4, alpha=0.5)
    fig.suptitle(f"Decode throughput ranking  ({corpus} — identical libdeflate L{level} streams)",
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

    # Overlay the FROZEN zopfli ratio ceiling, generated once via
    # `bench-report --zopfli-ceiling` and never recomputed by the routine matrix
    # (zopfli is ~100x slower than zlib — see bench/README.md). zopfli is the
    # best-achievable-ratio reference; its ratio/out_size are deterministic (its
    # single-rep speed is indicative only).
    ceiling_path = results_path.parent / "zopfli-ceiling.json"
    if ceiling_path.exists():
        ceiling = load(ceiling_path)["results"]
        results = [r for r in results if r["compressor"] != "zopfli"] + ceiling

    corpora = corpora_in(results)
    if not corpora:
        print("no real-corpus rows found; nothing to plot", file=sys.stderr)
        return

    for corpus in corpora:
        # Headline: compression speed vs ratio (codecs as level-curves). Decode
        # speed doesn't trade off against the compression ratio, so there is no
        # frontier to read on a decode scatter — decode throughput lives in the
        # summary table's `decompress MB/s` column instead.
        # `ratio_mode="pooled"` is available (x = corpus-wide Σcompressed/Σoriginal,
        # byte-weighted) but not rendered by default — pass it explicitly to opt in.
        pareto_scatter(results, meta, corpus, "compress_mbps", "compression speed",
                       "Compression speed vs ratio",
                       graphs_dir / f"{corpus}_compress_pareto.svg")
        # Precise: colour-graded geomean summary table.
        summary_table(results, meta, corpus, graphs_dir / f"{corpus}_summary.svg")
        # Per-file detail: relative-to-zlib heatmaps (ratio + compress speed).
        relative_heatmap(results, meta, corpus, "ratio", "Compression ratio vs zlib",
                         graphs_dir / f"{corpus}_ratio_heatmap.svg", higher_better=False)
        relative_heatmap(results, meta, corpus, "compress_mbps", "Compression speed vs zlib",
                         graphs_dir / f"{corpus}_compress_heatmap.svg", higher_better=True)

    # Decode-density charts (the decompression analogue of the compress Pareto),
    # from the sibling decode_density.json: fixed libdeflate input, every decoder
    # on byte-identical streams + memcpy ceiling. Two views: a per-file density
    # scatter (the trend) and a ranking lollipop (the precise ordering).
    dd_path = results_path.parent / "decode_density.json"
    if dd_path.exists():
        dd = load(dd_path)
        dd_results, dd_meta = dd["results"], dd.get("meta", {})
        for corpus in corpora_in(dd_results):
            decode_density_plot(dd_results, dd_meta, corpus,
                                graphs_dir / f"{corpus}_decode_density.svg")
            decode_ranking_plot(dd_results, dd_meta, corpus,
                                graphs_dir / f"{corpus}_decode_ranking.svg")


if __name__ == "__main__":
    main()
