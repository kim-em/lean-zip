#!/usr/bin/env python3
"""Render and audit lean-zip native before/after Pareto evidence.

Inputs are deliberately separate:

* ``references``: a committed full ``bench/results/latest.json`` whose
  non-native rows provide the comparison curves;
* ``before``: a native-only median-of-5 benchmark JSON;
* ``after``: a native-only median-of-5 benchmark JSON.

The two PNG overlays follow lean-zip's PR graph conventions: reference curves
are hollow, native-before is hollow gray/dashed, native-after is solid red,
throughput is logarithmic, and connectors use reciprocal-throughput mixing.

The text audit is stricter than a visual overlay.  It transforms throughput
``v`` to time per byte ``t = 1/v``, constructs the lower convex hull reachable
by arbitrary byte-fraction mixtures of measured levels, and checks the
after-hull against the before-hull over their full relevant ratio domain.
Because both hulls are piecewise linear in ``(ratio, t)``, checking the union of
their breakpoints proves the inequality over every point between them.

Ratios are reconstructed from ``out_size / size`` when those exact integer
fields are present; the rounded JSON ``ratio`` field is only a fallback.

Usage:

    python3 pareto_evidence.py REFERENCES BEFORE AFTER -o OUTDIR

Outputs:

    OUTDIR/perf_before_after_compress_mbps_canterbury.png
    OUTDIR/perf_before_after_compress_mbps_silesia.png
    OUTDIR/pareto_audit.txt
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Sequence

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt


REFERENCE_STYLES = [
    ("zlib", "zlib (C)", "#1f77b4", "s"),
    ("miniz_oxide", "miniz_oxide (Rust)", "#2ca02c", "^"),
    ("zlib_rs", "zlib-rs (Rust)", "#7f7f7f", "<"),
    ("zlib-rs", "zlib-rs (Rust)", "#7f7f7f", "<"),
    ("zlib_ng", "zlib-ng", "#393b79", ">"),
    ("libdeflate", "libdeflate (C+SIMD)", "#9467bd", "D"),
    ("go", "Go compress/flate", "#8c564b", "P"),
    ("js", "JS fflate", "#e377c2", "X"),
    ("zig", "Zig std.flate", "#bcbd22", "*"),
    ("ocaml", "OCaml", "#17becf", "h"),
    ("zopfli", "zopfli (C)", "#ff7f0e", "*"),
]

NATIVE_LEVELS = tuple(range(1, 11))
PAIRING = "cell-interleaved checkerboard AB/BA"
ORDER_SCHEME = "checkerboard (file index + level index) parity"
PAIRED_META_FIELDS = (
    "pairing",
    "order_scheme",
    "cpu_affinity",
    "core_scheduling_cookies",
    "benchmark_sessions",
    "benchmark_binary_sha256",
    "benchmark_harness_sha256",
    "benchmark_driver_sha256",
    "controlled_link_layout_sha256",
    "relevant_link_inputs_sha256",
)
SHA256_RE = re.compile(r"[0-9a-fA-F]{64}")
COOKIE_RE = re.compile(r"0x[0-9a-fA-F]+")


@dataclass(frozen=True)
class Document:
    path: Path
    sha256: str
    meta: dict
    rows: list[dict]


@dataclass(frozen=True)
class AggregatePoint:
    level: int
    ratio: float
    speed: float
    nfiles: int


@dataclass(frozen=True)
class FrontierPoint:
    ratio: float
    time_per_mb: float
    labels: tuple[str, ...]

    @property
    def speed(self) -> float:
        return 1.0 / self.time_per_mb


class AuditReport:
    def __init__(self) -> None:
        self.lines: list[str] = []

    def add(self, line: str = "") -> None:
        self.lines.append(line)

    def extend(self, lines: Iterable[str]) -> None:
        self.lines.extend(lines)

    def render(self) -> str:
        return "\n".join(self.lines).rstrip() + "\n"


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("references", type=Path)
    parser.add_argument("before", type=Path)
    parser.add_argument("after", type=Path)
    parser.add_argument("-o", "--outdir", type=Path, required=True)
    parser.add_argument(
        "--metric",
        choices=("compress_mbps", "decompress_mbps"),
        default="compress_mbps",
    )
    parser.add_argument(
        "--corpora",
        nargs="+",
        default=("canterbury", "silesia"),
        help="corpora to render and audit (default: canterbury silesia)",
    )
    parser.add_argument(
        "--frontier-tolerance-pct",
        type=float,
        default=0.0,
        help="allowed after-vs-before frontier slowdown (default: strict 0)",
    )
    parser.add_argument(
        "--allow-machine-mismatch",
        action="store_true",
        help="permit native/reference timing from different machines",
    )
    parser.add_argument(
        "--allow-native-toolchain-mismatch",
        action="store_true",
        help="permit native before/after timing from different Lean toolchains",
    )
    parser.add_argument(
        "--allow-unverified-median5",
        action="store_true",
        help="permit input metadata that does not explicitly attest median-of-5",
    )
    parser.add_argument(
        "--allow-missing-comparators",
        action="store_true",
        help="permit missing miniz_oxide, zlib-rs, or zlib reference rows",
    )
    parser.add_argument(
        "--allow-legacy-or-partial-inputs",
        action="store_true",
        help=(
            "smoke tests only: permit absent legacy paired-run metadata and "
            "native inputs that do not contain every level L1-L10"
        ),
    )
    return parser.parse_args(argv)


def load_document(path: Path) -> Document:
    try:
        payload = path.read_bytes()
        raw = json.loads(payload)
    except (OSError, json.JSONDecodeError) as exc:
        raise ValueError(f"cannot read {path}: {exc}") from exc
    if not isinstance(raw, dict) or not isinstance(raw.get("results"), list):
        raise ValueError(f"{path}: expected an object with a results list")
    meta = raw.get("meta", {})
    if not isinstance(meta, dict):
        raise ValueError(f"{path}: meta must be an object")
    return Document(
        path.resolve(), hashlib.sha256(payload).hexdigest(), meta, raw["results"]
    )


def meta_value(doc: Document, key: str) -> str:
    value = doc.meta.get(key)
    return "?" if value is None or value == "" else str(value)


def median5_verified(doc: Document) -> bool:
    aggregation = str(doc.meta.get("timing_aggregation", "")).lower()
    reps = doc.meta.get("timing_reps")
    return aggregation == "median" and reps == 5


def valid_sha256(value: object) -> bool:
    return isinstance(value, str) and SHA256_RE.fullmatch(value) is not None


def validate_paired_native_metadata(
    before: Document,
    after: Document,
    *,
    allow_legacy: bool,
) -> None:
    """Validate the paired-native session contract.

    Final evidence requires the complete protocol-v3 output schema.  The
    explicit smoke-test escape hatch skips this check so legacy protocol-v2
    snapshots can still exercise graph/report generation before the final run.
    """
    if allow_legacy:
        return

    for field in PAIRED_META_FIELDS:
        before_has = field in before.meta and before.meta[field] is not None
        after_has = field in after.meta and after.meta[field] is not None
        if before_has != after_has:
            raise ValueError(
                f"paired metadata field {field!r} is present on only one native input"
            )
        if not before_has:
            raise ValueError(
                f"before and after must declare paired metadata field {field!r} "
                "(use --allow-legacy-or-partial-inputs only for a smoke test)"
            )

    if before.meta["pairing"] != PAIRING or after.meta["pairing"] != PAIRING:
        raise ValueError(f"paired metadata must use pairing={PAIRING!r}")
    if (
        before.meta["order_scheme"] != ORDER_SCHEME
        or after.meta["order_scheme"] != ORDER_SCHEME
    ):
        raise ValueError(
            f"paired metadata must use order_scheme={ORDER_SCHEME!r}"
        )

    before_cpu = before.meta["cpu_affinity"]
    after_cpu = after.meta["cpu_affinity"]
    for label, value in (("before", before_cpu), ("after", after_cpu)):
        if (
            not isinstance(value, list)
            or len(value) != 1
            or not isinstance(value[0], int)
            or isinstance(value[0], bool)
            or value[0] < 0
        ):
            raise ValueError(
                f"{label} cpu_affinity must contain exactly one nonnegative CPU"
            )
    if before_cpu != after_cpu:
        raise ValueError("paired before/after cpu_affinity must match")

    before_cookies = before.meta["core_scheduling_cookies"]
    after_cookies = after.meta["core_scheduling_cookies"]
    before_sessions = before.meta["benchmark_sessions"]
    after_sessions = after.meta["benchmark_sessions"]
    for label, cookies, sessions in (
        ("before", before_cookies, before_sessions),
        ("after", after_cookies, after_sessions),
    ):
        if type(sessions) is not int or sessions <= 0:
            raise ValueError(f"{label} benchmark_sessions must be a positive integer")
        if not isinstance(cookies, list) or len(cookies) != sessions:
            raise ValueError(
                f"{label} core_scheduling_cookies length must equal benchmark_sessions"
            )
        for cookie in cookies:
            if (
                not isinstance(cookie, str)
                or COOKIE_RE.fullmatch(cookie) is None
                or int(cookie, 16) == 0
            ):
                raise ValueError(
                    f"{label} core_scheduling_cookies must contain only private "
                    "nonzero hex cookies"
                )
    if before_sessions != after_sessions:
        raise ValueError("paired before/after benchmark_sessions must match")
    if before_cookies != after_cookies:
        raise ValueError("paired before/after core_scheduling_cookies must match")

    for field in (
        "benchmark_binary_sha256",
        "benchmark_harness_sha256",
        "benchmark_driver_sha256",
        "controlled_link_layout_sha256",
    ):
        for label, doc in (("before", before), ("after", after)):
            if not valid_sha256(doc.meta[field]):
                raise ValueError(f"{label} {field} must be a SHA-256 hex digest")

    for field in (
        "benchmark_harness_sha256",
        "benchmark_driver_sha256",
        "controlled_link_layout_sha256",
    ):
        if before.meta[field].lower() != after.meta[field].lower():
            raise ValueError(f"paired before/after {field} must match")

    before_inputs = before.meta["relevant_link_inputs_sha256"]
    after_inputs = after.meta["relevant_link_inputs_sha256"]
    for label, value in (("before", before_inputs), ("after", after_inputs)):
        if (
            not isinstance(value, dict)
            or not value
            or not all(isinstance(name, str) and name for name in value)
            or not all(valid_sha256(digest) for digest in value.values())
        ):
            raise ValueError(
                f"{label} relevant_link_inputs_sha256 must be a nonempty "
                "name-to-SHA-256 mapping"
            )
    if {
        key: value.lower() for key, value in before_inputs.items()
    } != {
        key: value.lower() for key, value in after_inputs.items()
    }:
        raise ValueError(
            "paired before/after relevant_link_inputs_sha256 must match"
        )

    # Protocol v3 emits these additional hashes.  They are not part of the
    # controlled-layout equality contract, but malformed provenance is still
    # rejected whenever the fields are present.
    for field in ("link_flags_sha256", "link_response_layout_sha256"):
        for label, doc in (("before", before), ("after", after)):
            if field in doc.meta and not valid_sha256(doc.meta[field]):
                raise ValueError(f"{label} {field} must be a SHA-256 hex digest")


def compressor_names(rows: Sequence[dict]) -> set[str]:
    return {str(r.get("compressor")) for r in rows}


def canonical_compressor(rows: Sequence[dict], aliases: Sequence[str]) -> str | None:
    names = compressor_names(rows)
    return next((alias for alias in aliases if alias in names), None)


def row_ratio(row: dict) -> float:
    size = row.get("size")
    out_size = row.get("out_size")
    if isinstance(size, (int, float)) and isinstance(out_size, (int, float)) and size > 0:
        ratio = float(out_size) / float(size)
    else:
        ratio = float(row["ratio"])
    if not math.isfinite(ratio) or ratio <= 0:
        raise ValueError(f"invalid ratio in row {row!r}")
    return ratio


def geomean(values: Iterable[float]) -> float | None:
    positive = [float(v) for v in values if v is not None and float(v) > 0]
    if not positive:
        return None
    return math.exp(math.fsum(math.log(v) for v in positive) / len(positive))


def corpus_of(row: dict) -> str | None:
    pattern = row.get("pattern")
    if not isinstance(pattern, str) or "/" not in pattern:
        return None
    return pattern.split("/", 1)[0]


def native_key(row: dict) -> tuple[str, int]:
    return str(row["pattern"]), int(row["level"])


def validate_unique_rows(doc: Document) -> None:
    seen: set[tuple[str, str, int]] = set()
    for row in doc.rows:
        try:
            key = (
                str(row["compressor"]),
                str(row["pattern"]),
                int(row["level"]),
            )
        except (KeyError, TypeError, ValueError) as exc:
            raise ValueError(f"{doc.path}: malformed result row {row!r}") from exc
        if key in seen:
            raise ValueError(f"{doc.path}: duplicate result row {key!r}")
        seen.add(key)


def native_rows(doc: Document) -> list[dict]:
    return [r for r in doc.rows if r.get("compressor") == "native"]


def corpus_patterns(rows: Sequence[dict], corpus: str, compressor: str) -> list[str]:
    prefix = corpus + "/"
    return sorted(
        {
            str(r["pattern"])
            for r in rows
            if r.get("compressor") == compressor
            and str(r.get("pattern", "")).startswith(prefix)
        }
    )


def validate_complete_native_levels(
    doc: Document,
    corpus: str,
    required_patterns: Sequence[str],
) -> None:
    """Require exactly one native L1-L10 row for every requested file."""
    prefix = corpus + "/"
    rows = [
        row
        for row in native_rows(doc)
        if str(row.get("pattern", "")).startswith(prefix)
    ]
    levels = {int(row["level"]) for row in rows}
    expected_levels = set(NATIVE_LEVELS)
    if levels != expected_levels:
        missing = sorted(expected_levels - levels)
        extra = sorted(levels - expected_levels)
        raise ValueError(
            f"{doc.path}: incomplete {corpus} native level coverage; "
            f"missing={missing}, extra={extra} "
            "(use --allow-legacy-or-partial-inputs only for a smoke test)"
        )
    required_set = set(required_patterns)
    for level in NATIVE_LEVELS:
        present = {
            str(row["pattern"])
            for row in rows
            if int(row["level"]) == level
        }
        if present != required_set:
            raise ValueError(
                f"{doc.path}: incomplete {corpus} native L{level} coverage: "
                f"{len(present)}/{len(required_set)} rows "
                "(use --allow-legacy-or-partial-inputs only for a smoke test)"
            )


def aggregate_points(
    rows: Sequence[dict],
    compressor: str,
    corpus: str,
    metric: str,
    required_patterns: Sequence[str],
    warnings: list[str],
) -> list[AggregatePoint]:
    prefix = corpus + "/"
    selected = [
        r
        for r in rows
        if r.get("compressor") == compressor
        and str(r.get("pattern", "")).startswith(prefix)
    ]
    by_level: dict[int, dict[str, dict]] = {}
    for row in selected:
        by_level.setdefault(int(row["level"]), {})[str(row["pattern"])] = row

    out: list[AggregatePoint] = []
    wanted = set(required_patterns)
    for level in sorted(by_level):
        indexed = by_level[level]
        missing = sorted(wanted - indexed.keys())
        if missing:
            warnings.append(
                f"{corpus}: skipped {compressor} L{level}: missing "
                f"{len(missing)}/{len(required_patterns)} corpus rows"
            )
            continue
        level_rows = [indexed[p] for p in required_patterns]
        try:
            ratios = [row_ratio(r) for r in level_rows]
            speeds = [float(r[metric]) for r in level_rows if r.get(metric) is not None]
        except (KeyError, TypeError, ValueError) as exc:
            raise ValueError(
                f"{compressor} {corpus} L{level}: invalid aggregate row"
            ) from exc
        if len(speeds) != len(level_rows) or any(
            not math.isfinite(v) or v <= 0 for v in speeds
        ):
            warnings.append(
                f"{corpus}: skipped {compressor} L{level}: incomplete/invalid {metric}"
            )
            continue
        ratio = geomean(ratios)
        speed = geomean(speeds)
        if ratio is not None and speed is not None:
            out.append(AggregatePoint(level, ratio, speed, len(level_rows)))
    return out


def sort_curve(points: Sequence[AggregatePoint]) -> list[AggregatePoint]:
    return sorted(points, key=lambda p: (p.ratio, p.level))


def mix_curve(
    x0: float, y0: float, x1: float, y1: float, samples: int = 64
) -> tuple[list[float], list[float]]:
    """Reciprocal-throughput mixing between two operating points."""
    if y0 <= 0 or y1 <= 0:
        return [x0, x1], [y0, y1]
    xs: list[float] = []
    ys: list[float] = []
    for i in range(samples + 1):
        fraction = i / samples
        xs.append((1.0 - fraction) * x0 + fraction * x1)
        ys.append(1.0 / ((1.0 - fraction) / y0 + fraction / y1))
    return xs, ys


def plot_series(
    ax,
    points: Sequence[AggregatePoint],
    *,
    color: str,
    marker: str,
    linewidth: float,
    markersize: float,
    label: str,
    linestyle: str = "-",
    zorder: int = 4,
    alpha: float = 0.9,
    hollow: bool = False,
) -> None:
    ordered = sort_curve(points)
    xs = [p.ratio for p in ordered]
    ys = [p.speed for p in ordered]
    ax.plot(
        xs,
        ys,
        linestyle="none",
        marker=marker,
        markersize=markersize,
        color=color,
        markerfacecolor="none" if hollow else color,
        markeredgecolor=color,
        markeredgewidth=1.2,
        zorder=zorder,
        label=label,
    )
    for left, right in zip(ordered, ordered[1:]):
        cx, cy = mix_curve(left.ratio, left.speed, right.ratio, right.speed)
        ax.plot(
            cx,
            cy,
            color=color,
            linewidth=linewidth,
            linestyle=linestyle,
            alpha=alpha,
            zorder=zorder,
        )


def provenance_footer(before: Document, after: Document, refs: Document) -> str:
    return (
        f"before {meta_value(before, 'git_commit')} "
        f"({meta_value(before, 'toolchain')}; {meta_value(before, 'date')})  ·  "
        f"after {meta_value(after, 'git_commit')} "
        f"({meta_value(after, 'toolchain')}; {meta_value(after, 'date')})  ·  "
        f"refs {meta_value(refs, 'git_commit')}  ·  exact ratios from sizes"
    )


def render_graph(
    *,
    corpus: str,
    metric: str,
    refs: Document,
    before: Document,
    after: Document,
    required_patterns: Sequence[str],
    outdir: Path,
    warnings: list[str],
) -> Path:
    label_speed = (
        "compression speed" if metric == "compress_mbps" else "decode throughput"
    )
    fig, ax = plt.subplots(figsize=(10, 6.5))
    used_keys: set[str] = set()
    for key, label, color, marker in REFERENCE_STYLES:
        # Avoid drawing an alias twice.
        if key in used_keys or key not in compressor_names(refs.rows):
            continue
        if key == "zlib-rs" and "zlib_rs" in compressor_names(refs.rows):
            continue
        used_keys.add(key)
        points = aggregate_points(
            refs.rows, key, corpus, metric, required_patterns, warnings
        )
        if not points:
            continue
        plot_series(
            ax,
            points,
            color=color,
            marker=marker,
            linewidth=1.3,
            markersize=5,
            zorder=4,
            hollow=True,
            label=label,
        )

    before_points = aggregate_points(
        before.rows, "native", corpus, metric, required_patterns, warnings
    )
    after_points = aggregate_points(
        after.rows, "native", corpus, metric, required_patterns, warnings
    )
    if not before_points or not after_points:
        raise ValueError(f"{corpus}: native before/after curve is empty")
    plot_series(
        ax,
        before_points,
        color="#7f7f7f",
        marker="o",
        linewidth=2.2,
        markersize=7,
        linestyle="--",
        zorder=11,
        alpha=1.0,
        hollow=True,
        label="lean-zip native — before",
    )
    plot_series(
        ax,
        after_points,
        color="#d62728",
        marker="o",
        linewidth=2.6,
        markersize=8,
        zorder=12,
        alpha=1.0,
        label="lean-zip native — AFTER",
    )

    machine = meta_value(after, "machine")
    short_machine = machine.removeprefix("Linux ").removesuffix(" x86_64")
    ax.set_yscale("log")
    ax.set_xlabel(
        "compression ratio  (compressed / original — ← smaller = more compressed)"
    )
    ax.set_ylabel(f"{label_speed}  (MB/s, log)")
    ax.set_title(
        f"DEFLATE {label_speed} vs ratio — {corpus}\n"
        f"native same-toolchain median-of-5; established expanded refs reused "
        f"({short_machine}; {len(required_patterns)}-file geomean)"
    )
    ax.grid(True, which="both", linestyle=":", alpha=0.4)
    ax.legend(fontsize=8, ncol=2, loc="best")
    fig.text(
        0.5,
        0.006,
        provenance_footer(before, after, refs),
        ha="center",
        fontsize=6.5,
        color="#555555",
    )
    fig.tight_layout(rect=(0, 0.025, 1, 1))
    outfile = outdir / f"perf_before_after_{metric}_{corpus}.png"
    fig.savefig(outfile, dpi=130)
    plt.close(fig)
    return outfile


def cross(a: FrontierPoint, b: FrontierPoint, c: FrontierPoint) -> float:
    return (b.ratio - a.ratio) * (c.time_per_mb - a.time_per_mb) - (
        b.time_per_mb - a.time_per_mb
    ) * (c.ratio - a.ratio)


def achievable_frontier(points: Sequence[AggregatePoint]) -> list[FrontierPoint]:
    """Lower convex, nondominated hull in (ratio, reciprocal throughput)."""
    raw = sorted(
        (
            FrontierPoint(p.ratio, 1.0 / p.speed, (f"L{p.level}",))
            for p in points
        ),
        key=lambda p: (p.ratio, p.time_per_mb),
    )
    if not raw:
        raise ValueError("cannot build a frontier from no points")

    # At an identical ratio, retain only the fastest point and combine labels
    # for exact ties (e.g. byte-identical L9=L10 endpoints).
    deduped: list[FrontierPoint] = []
    i = 0
    while i < len(raw):
        group = [raw[i]]
        j = i + 1
        while j < len(raw) and math.isclose(
            raw[j].ratio, raw[i].ratio, rel_tol=1e-13, abs_tol=1e-15
        ):
            group.append(raw[j])
            j += 1
        best_time = min(p.time_per_mb for p in group)
        labels = tuple(
            sorted(
                {
                    label
                    for p in group
                    if math.isclose(
                        p.time_per_mb, best_time, rel_tol=1e-13, abs_tol=1e-15
                    )
                    for label in p.labels
                }
            )
        )
        deduped.append(FrontierPoint(group[0].ratio, best_time, labels))
        i = j

    lower: list[FrontierPoint] = []
    for point in deduped:
        while len(lower) >= 2 and cross(lower[-2], lower[-1], point) <= 0.0:
            lower.pop()
        lower.append(point)

    # Points to the right of the globally fastest lower-hull point are dominated:
    # the faster point is available at an equal-or-smaller ratio.
    fastest_index = min(
        range(len(lower)), key=lambda idx: lower[idx].time_per_mb
    )
    return lower[: fastest_index + 1]


def time_at_or_below_ratio(
    frontier: Sequence[FrontierPoint], ratio_limit: float
) -> float:
    """Best reciprocal throughput reachable with ratio <= ``ratio_limit``."""
    if ratio_limit < frontier[0].ratio and not math.isclose(
        ratio_limit, frontier[0].ratio, rel_tol=1e-13, abs_tol=1e-15
    ):
        return math.inf
    if ratio_limit >= frontier[-1].ratio:
        return frontier[-1].time_per_mb
    for left, right in zip(frontier, frontier[1:]):
        if ratio_limit <= right.ratio or math.isclose(
            ratio_limit, right.ratio, rel_tol=1e-13, abs_tol=1e-15
        ):
            if math.isclose(left.ratio, right.ratio):
                return min(left.time_per_mb, right.time_per_mb)
            f = (ratio_limit - left.ratio) / (right.ratio - left.ratio)
            return (1.0 - f) * left.time_per_mb + f * right.time_per_mb
    return frontier[-1].time_per_mb


def frontier_label(frontier: Sequence[FrontierPoint]) -> str:
    return " → ".join(
        f"{'='.join(point.labels)}@({point.ratio:.6f}, {point.speed:.3f})"
        for point in frontier
    )


def compare_frontiers(
    before_frontier: Sequence[FrontierPoint],
    after_frontier: Sequence[FrontierPoint],
    tolerance_pct: float,
) -> tuple[bool, list[tuple[float, float, float, float]]]:
    """Return pass/fail and (ratio, before speed, after speed, factor) checks."""
    domain_start = before_frontier[0].ratio
    domain_end = before_frontier[-1].ratio
    checkpoints = {domain_start, domain_end}
    checkpoints.update(
        p.ratio
        for p in before_frontier
        if domain_start <= p.ratio <= domain_end
    )
    checkpoints.update(
        p.ratio
        for p in after_frontier
        if domain_start <= p.ratio <= domain_end
    )
    rows: list[tuple[float, float, float, float]] = []
    threshold = 1.0 - tolerance_pct / 100.0
    passed = True
    for ratio in sorted(checkpoints):
        before_t = time_at_or_below_ratio(before_frontier, ratio)
        after_t = time_at_or_below_ratio(after_frontier, ratio)
        before_speed = 1.0 / before_t
        if math.isinf(after_t):
            after_speed = 0.0
            factor = 0.0
        else:
            after_speed = 1.0 / after_t
            factor = after_speed / before_speed
        rows.append((ratio, before_speed, after_speed, factor))
        if factor + 1e-12 < threshold:
            passed = False
    return passed, rows


def points_by_level(points: Sequence[AggregatePoint]) -> dict[int, AggregatePoint]:
    return {point.level: point for point in points}


def add_native_level_table(
    report: AuditReport,
    corpus: str,
    before_points: Sequence[AggregatePoint],
    after_points: Sequence[AggregatePoint],
) -> None:
    bmap = points_by_level(before_points)
    amap = points_by_level(after_points)
    report.add(f"{corpus}: native measured levels")
    report.add(
        " lvl    ratio-before   ratio-after      before       after    speed factor      Δratio"
    )
    for level in sorted(bmap.keys() & amap.keys()):
        b = bmap[level]
        a = amap[level]
        report.add(
            f" L{level:<2}      {b.ratio:0.6f}      {a.ratio:0.6f}"
            f"   {b.speed:9.3f}   {a.speed:9.3f}"
            f"       {a.speed / b.speed:0.4f}x"
            f"   {a.ratio - b.ratio:+0.7f}"
        )
    report.add()


def add_exact_row_ratio_delta(
    report: AuditReport,
    corpus: str,
    before: Document,
    after: Document,
) -> None:
    prefix = corpus + "/"
    before_index = {
        native_key(row): row
        for row in native_rows(before)
        if str(row.get("pattern", "")).startswith(prefix)
    }
    after_index = {
        native_key(row): row
        for row in native_rows(after)
        if str(row.get("pattern", "")).startswith(prefix)
    }
    deltas = [
        (row_ratio(after_index[key]) - row_ratio(before_index[key]), key)
        for key in sorted(before_index.keys() & after_index.keys())
    ]
    if not deltas:
        return
    worst = max(deltas, key=lambda item: item[0])
    best = min(deltas, key=lambda item: item[0])
    largest_absolute = max(deltas, key=lambda item: abs(item[0]))
    changed_outputs = 0
    for key in before_index.keys() & after_index.keys():
        before_size = before_index[key].get("out_size")
        after_size = after_index[key].get("out_size")
        if before_size is not None and after_size is not None and before_size != after_size:
            changed_outputs += 1
    report.add(
        f"{corpus}: exact per-row ratio delta: worst {worst[0]:+.9f} at "
        f"{worst[1][0]} L{worst[1][1]}; best {best[0]:+.9f} at "
        f"{best[1][0]} L{best[1][1]}; max |Δ| {abs(largest_absolute[0]):.9f} at "
        f"{largest_absolute[1][0]} L{largest_absolute[1][1]}; "
        f"changed out_size rows {changed_outputs}/{len(deltas)}"
    )
    report.add()


def comparator_relation(
    native_frontier: Sequence[FrontierPoint], point: AggregatePoint
) -> tuple[str, float | None, float | None]:
    native_time = time_at_or_below_ratio(native_frontier, point.ratio)
    if math.isinf(native_time):
        return "native ratio unreachable", None, None
    native_speed = 1.0 / native_time
    factor = native_speed / point.speed
    if factor >= 1.0 - 1e-12:
        verdict = "native dominates/matches"
    else:
        verdict = "external faster at this ratio"
    return verdict, native_speed, factor


def add_comparator_table(
    report: AuditReport,
    *,
    corpus: str,
    label: str,
    points: Sequence[AggregatePoint],
    levels_to_show: Sequence[int],
    native_frontier: Sequence[FrontierPoint],
) -> bool:
    by_level = points_by_level(points)
    passed = True
    report.add(
        f"{corpus}: native-after relationship to {label} "
        "(native capability uses same-or-better ratio)"
    )
    report.add(
        " lvl       ext ratio    ext MB/s   native MB/s   native/ext   relationship"
    )
    for level in levels_to_show:
        point = by_level.get(level)
        if point is None:
            report.add(f" L{level:<2}              —           —             —            —   missing")
            passed = False
            continue
        verdict, native_speed, factor = comparator_relation(native_frontier, point)
        if native_speed is None or factor is None:
            native_text = "—"
            factor_text = "—"
            passed = False
        else:
            native_text = f"{native_speed:.3f}"
            factor_text = f"{factor:.4f}x"
            passed = passed and factor >= 1.0 - 1e-12
        report.add(
            f" L{level:<2}       {point.ratio:0.6f}   {point.speed:9.3f}"
            f"   {native_text:>11}   {factor_text:>10}   {verdict}"
        )
    report.add()
    return passed


def add_zlib_rs_vs_zlib(
    report: AuditReport,
    *,
    corpus: str,
    zlib_rs_points: Sequence[AggregatePoint],
    zlib_points: Sequence[AggregatePoint],
) -> None:
    rs = points_by_level(zlib_rs_points)
    zl = points_by_level(zlib_points)
    report.add(f"{corpus}: zlib-rs vs zlib same-level reference relationship")
    report.add(
        " lvl   rs ratio   zlib ratio   rs MB/s   zlib MB/s    rs ratio Δ    rs speed Δ   verdict"
    )
    for level in sorted(rs.keys() & zl.keys()):
        rp, zp = rs[level], zl[level]
        ratio_delta = rp.ratio / zp.ratio - 1.0
        speed_delta = rp.speed / zp.speed - 1.0
        rs_dominates = ratio_delta <= 0.0 and speed_delta >= 0.0
        zlib_dominates = ratio_delta >= 0.0 and speed_delta <= 0.0
        if rs_dominates:
            verdict = "zlib-rs dominates"
        elif zlib_dominates:
            verdict = "zlib dominates"
        else:
            verdict = "ratio/speed trade-off"
        report.add(
            f" L{level:<2}   {rp.ratio:0.6f}    {zp.ratio:0.6f}"
            f"   {rp.speed:8.3f}   {zp.speed:9.3f}"
            f"    {ratio_delta:+9.2%}    {speed_delta:+9.2%}   {verdict}"
        )
    report.add()


def validate_inputs(
    args: argparse.Namespace,
    refs: Document,
    before: Document,
    after: Document,
) -> dict[str, list[str]]:
    for doc in (refs, before, after):
        validate_unique_rows(doc)
        if not args.allow_unverified_median5 and not median5_verified(doc):
            raise ValueError(
                f"{doc.path}: metadata does not explicitly verify median-of-5 "
                "(use --allow-unverified-median5 only for a non-final smoke test)"
            )

    machines = {
        meta_value(refs, "machine"),
        meta_value(before, "machine"),
        meta_value(after, "machine"),
    }
    if not args.allow_machine_mismatch and "?" in machines:
        raise ValueError("all final evidence inputs must declare their machine")
    if not args.allow_machine_mismatch and len(machines) != 1:
        raise ValueError(
            "timing machine mismatch: "
            f"refs={meta_value(refs, 'machine')!r}, "
            f"before={meta_value(before, 'machine')!r}, "
            f"after={meta_value(after, 'machine')!r}"
        )
    before_toolchain = meta_value(before, "toolchain")
    after_toolchain = meta_value(after, "toolchain")
    if (
        not args.allow_native_toolchain_mismatch
        and (before_toolchain == "?" or after_toolchain == "?")
    ):
        raise ValueError("before and after must declare their Lean toolchain")
    if (
        not args.allow_native_toolchain_mismatch
        and before_toolchain != after_toolchain
    ):
        raise ValueError(
            "native before/after toolchain mismatch: "
            f"before={before_toolchain!r}, after={after_toolchain!r}"
        )

    validate_paired_native_metadata(
        before,
        after,
        allow_legacy=args.allow_legacy_or_partial_inputs,
    )

    before_native = native_rows(before)
    after_native = native_rows(after)
    if not before_native or not after_native:
        raise ValueError("before and after must each contain native rows")
    bkeys = {native_key(r) for r in before_native}
    akeys = {native_key(r) for r in after_native}
    if bkeys != akeys:
        only_before = sorted(bkeys - akeys)
        only_after = sorted(akeys - bkeys)
        raise ValueError(
            "native row coverage differs: "
            f"{len(only_before)} before-only, {len(only_after)} after-only; "
            f"examples before-only={only_before[:4]!r}, "
            f"after-only={only_after[:4]!r}"
        )

    patterns: dict[str, list[str]] = {}
    for corpus in args.corpora:
        corpus_files = corpus_patterns(after_native, corpus, "native")
        if not corpus_files:
            raise ValueError(f"after input has no native {corpus} rows")
        patterns[corpus] = corpus_files
        if not args.allow_legacy_or_partial_inputs:
            validate_complete_native_levels(before, corpus, corpus_files)
            validate_complete_native_levels(after, corpus, corpus_files)

    required = {
        "miniz_oxide": ("miniz_oxide",),
        "zlib-rs": ("zlib_rs", "zlib-rs"),
        "zlib": ("zlib",),
    }
    missing = [
        label
        for label, aliases in required.items()
        if canonical_compressor(refs.rows, aliases) is None
    ]
    if missing and not args.allow_missing_comparators:
        raise ValueError(
            "reference JSON is missing required comparator rows: "
            + ", ".join(missing)
            + " (use --allow-missing-comparators only for a smoke test)"
        )
    miniz_key = canonical_compressor(refs.rows, ("miniz_oxide",))
    if miniz_key is not None and not args.allow_missing_comparators:
        for corpus, required_patterns in patterns.items():
            required_set = set(required_patterns)
            for level in range(1, 10):
                present = {
                    str(row.get("pattern"))
                    for row in refs.rows
                    if row.get("compressor") == miniz_key
                    and row.get("level") == level
                    and corpus_of(row) == corpus
                }
                if present != required_set:
                    raise ValueError(
                        f"reference JSON has incomplete {corpus} miniz_oxide "
                        f"L{level} coverage: {len(present)}/{len(required_set)} rows"
                    )
    return patterns


def run(argv: Sequence[str]) -> int:
    args = parse_args(argv)
    if not math.isfinite(args.frontier_tolerance_pct) \
            or args.frontier_tolerance_pct < 0:
        raise ValueError("--frontier-tolerance-pct must be finite and nonnegative")
    refs = load_document(args.references)
    before = load_document(args.before)
    after = load_document(args.after)
    patterns_by_corpus = validate_inputs(args, refs, before, after)
    args.outdir.mkdir(parents=True, exist_ok=True)

    report = AuditReport()
    report.add("LEAN-ZIP BEFORE/AFTER PARETO AUDIT")
    report.add(
        "evidence mode: "
        + (
            "SMOKE — legacy/partial native inputs permitted"
            if args.allow_legacy_or_partial_inputs
            else "FINAL — complete native L1-L10 + hardened paired metadata required"
        )
    )
    report.add(f"evidence date: {meta_value(after, 'date')}")
    report.add(
        f"generator: {Path(__file__).name} | "
        f"sha256={hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}"
    )
    report.add(f"metric: {args.metric}")
    report.add(
        "aggregation: exact per-file out_size/size ratios; geometric mean over files; "
        "median-of-5 throughput"
    )
    report.add(
        "provenance roles: native before/after are required to use one machine and "
        "one Lean toolchain; non-native rows are reused read-only from the established "
        "expanded reference snapshot"
    )
    report.add(
        "frontier method: lower convex hull in (ratio, 1/throughput); arbitrary "
        "byte-fraction mixtures; same-or-better-ratio capability"
    )
    report.add(
        "scope: the breakpoint proof is exact for the dashboard's plotted "
        "geomean-endpoint mixing model; as bench/plot.py documents, mixing "
        "corpus geomeans is a close aggregate proxy rather than a literal "
        "single-workload mixture"
    )
    report.add(
        "proof of pointwise comparison: evaluate the union of both piecewise-linear "
        "hull breakpoint sets"
    )
    report.add(
        f"allowed frontier slowdown: {args.frontier_tolerance_pct:.6f}%"
    )
    report.add()
    for label, doc in (("references", refs), ("before", before), ("after", after)):
        report.add(
            f"{label:>10}: {doc.path.name} | sha256={doc.sha256} | "
            f"commit={meta_value(doc, 'git_commit')} | "
            f"date={meta_value(doc, 'date')} | machine={meta_value(doc, 'machine')} | "
            f"toolchain={meta_value(doc, 'toolchain')} | median-of-5=verified"
        )
    report.add()

    warnings: list[str] = []
    graph_paths: list[Path] = []
    overall_pass = True
    miniz_silesia_pass = True
    miniz_silesia_evaluated = False
    comparator_keys = {
        "miniz_oxide": canonical_compressor(refs.rows, ("miniz_oxide",)),
        "zlib-rs": canonical_compressor(refs.rows, ("zlib_rs", "zlib-rs")),
        "zlib": canonical_compressor(refs.rows, ("zlib",)),
    }

    for corpus in args.corpora:
        required_patterns = patterns_by_corpus[corpus]
        graph_paths.append(
            render_graph(
                corpus=corpus,
                metric=args.metric,
                refs=refs,
                before=before,
                after=after,
                required_patterns=required_patterns,
                outdir=args.outdir,
                warnings=warnings,
            )
        )
        before_points = aggregate_points(
            before.rows,
            "native",
            corpus,
            args.metric,
            required_patterns,
            warnings,
        )
        after_points = aggregate_points(
            after.rows,
            "native",
            corpus,
            args.metric,
            required_patterns,
            warnings,
        )
        add_native_level_table(report, corpus, before_points, after_points)
        add_exact_row_ratio_delta(report, corpus, before, after)

        before_frontier = achievable_frontier(before_points)
        after_frontier = achievable_frontier(after_points)
        passed, comparisons = compare_frontiers(
            before_frontier,
            after_frontier,
            args.frontier_tolerance_pct,
        )
        overall_pass &= passed
        report.add(f"{corpus}: achievable native frontier")
        report.add(f" before: {frontier_label(before_frontier)}")
        report.add(f" after : {frontier_label(after_frontier)}")
        report.add(
            " ratio checkpoint    before MB/s    after MB/s    after/before    result"
        )
        for ratio, before_speed, after_speed, factor in comparisons:
            threshold = 1.0 - args.frontier_tolerance_pct / 100.0
            result = "OK" if factor + 1e-12 >= threshold else "REGRESSION"
            report.add(
                f"       {ratio:0.6f}      {before_speed:9.3f}"
                f"     {after_speed:9.3f}         {factor:0.5f}x    {result}"
            )
        worst = min(comparisons, key=lambda row: row[3])
        report.add(
            f" POINTWISE FRONTIER: {'PASS' if passed else 'FAIL'}; "
            f"worst after/before speed factor {worst[3]:.5f}x "
            f"at ratio {worst[0]:.6f}"
        )
        report.add()

        reference_points: dict[str, list[AggregatePoint]] = {}
        for label, key in comparator_keys.items():
            if key is None:
                report.add(
                    f"{corpus}: {label} relationship unavailable: comparator absent "
                    "from reference JSON"
                )
                report.add()
                reference_points[label] = []
                continue
            reference_points[label] = aggregate_points(
                refs.rows,
                key,
                corpus,
                args.metric,
                required_patterns,
                warnings,
            )

        if reference_points["miniz_oxide"]:
            miniz_pass = add_comparator_table(
                report,
                corpus=corpus,
                label="miniz_oxide target levels",
                points=reference_points["miniz_oxide"],
                levels_to_show=tuple(range(1, 10)),
                native_frontier=after_frontier,
            )
            if corpus == "silesia":
                miniz_silesia_evaluated = True
                miniz_silesia_pass = miniz_silesia_pass and miniz_pass
        if reference_points["zlib-rs"]:
            # Show every available zlib-rs level so L9 is visible in curve context.
            add_comparator_table(
                report,
                corpus=corpus,
                label="zlib-rs context (L9 highlighted by inclusion)",
                points=reference_points["zlib-rs"],
                levels_to_show=tuple(
                    sorted(points_by_level(reference_points["zlib-rs"]))
                ),
                native_frontier=after_frontier,
            )
        if reference_points["zlib"]:
            add_comparator_table(
                report,
                corpus=corpus,
                label="zlib",
                points=reference_points["zlib"],
                levels_to_show=tuple(
                    sorted(points_by_level(reference_points["zlib"]))
                ),
                native_frontier=after_frontier,
            )
        if reference_points["zlib-rs"] and reference_points["zlib"]:
            add_zlib_rs_vs_zlib(
                report,
                corpus=corpus,
                zlib_rs_points=reference_points["zlib-rs"],
                zlib_points=reference_points["zlib"],
            )

    if warnings:
        report.add("COVERAGE WARNINGS")
        report.extend(f"- {warning}" for warning in sorted(set(warnings)))
        report.add()
    report.add(
        "OVERALL NATIVE ACHIEVABLE FRONTIER: "
        + ("PASS — no pointwise regression detected" if overall_pass else "FAIL — regression detected")
    )
    silesia_requested = "silesia" in args.corpora
    if silesia_requested and not miniz_silesia_evaluated \
            and not args.allow_missing_comparators:
        # Strict validation established that the rows exist, so reaching this
        # branch means none survived metric/ratio aggregation.  That is failed
        # evidence, not a vacuous containment pass.
        miniz_silesia_pass = False
    if miniz_silesia_evaluated or (
        silesia_requested and not args.allow_missing_comparators
    ):
        miniz_status = "PASS" if miniz_silesia_pass else "FAIL"
    else:
        miniz_status = "NOT EVALUATED"
    report.add(
        "SILESIA MINIZ_OXIDE L1-L9 CONTAINMENT: " + miniz_status
    )
    report.add("PNG outputs:")
    report.extend(f"- {path.name}" for path in graph_paths)

    rendered = report.render()
    audit_path = args.outdir / "pareto_audit.txt"
    audit_path.write_text(rendered)
    sys.stdout.write(rendered)
    miniz_gate_pass = (
        not silesia_requested
        or (args.allow_missing_comparators and not miniz_silesia_evaluated)
        or miniz_silesia_pass
    )
    return 0 if overall_pass and miniz_gate_pass else 1


def main() -> None:
    try:
        raise SystemExit(run(sys.argv[1:]))
    except ValueError as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        raise SystemExit(2)


if __name__ == "__main__":
    main()
