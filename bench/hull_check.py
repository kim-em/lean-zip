#!/usr/bin/env python3
"""Mixing-frontier dominance check on the weighted-Silesia compress plane.

Usage: hull_check.py <candidate.json> [reference.json]

Both files are bench-report JSONs. Native rows come from <candidate.json>
(fall back to reference for levels it lacks); every other compressor's rows
come from <reference.json> (default bench/results/latest.json).

For each codec point (weighted Silesia: ratio = sum(out)/sum(in), speed =
harmonic-by-bytes MB/s) this prints whether the native achievable mixing
frontier (upper-left hull over the native level points; mixing two levels is
linear in ratio and in sec/MB) strictly dominates it, and by what speed margin
at equal ratio. The headline question: is miniz_oxide L6 inside our hull?
"""
import json, sys
from collections import defaultdict

def load(path):
    with open(path) as f:
        return json.load(f)["results"]

def agg(rows, comp):
    pts = defaultdict(lambda: [0, 0, 0.0])  # level -> [in, out, sec]
    for r in rows:
        if r["compressor"] != comp or not r["pattern"].startswith("silesia/"):
            continue
        m = r.get("compress_mbps")
        if not m:
            continue
        a = pts[r["level"]]
        a[0] += r["size"]; a[1] += r["out_size"]; a[2] += r["size"] / 1e6 / m
    return {lvl: (o / i, i / 1e6 / t) for lvl, (i, o, t) in pts.items() if i}

def frontier(points):
    """Upper hull in (ratio asc, sec/MB): mixing is linear in both."""
    pts = sorted((r, 1.0 / s) for r, s in points.values())  # (ratio, sec per MB)
    hull = []
    for p in pts:
        while len(hull) >= 2:
            (x1, y1), (x2, y2) = hull[-2], hull[-1]
            # keep hull lower-convex in sec/MB over ratio
            if (y2 - y1) * (p[0] - x1) >= (p[1] - y1) * (x2 - x1):
                hull.pop()
            else:
                break
        # drop dominated points (higher time and higher ratio)
        if hull and p[1] >= hull[-1][1]:
            continue
        hull.append(p)
    return hull

def frontier_speed_at(hull, ratio):
    """Best achievable MB/s at the given ratio by mixing adjacent hull points."""
    if not hull:
        return None
    if ratio < hull[0][0]:
        return None  # ratio unreachable
    for (x1, y1), (x2, y2) in zip(hull, hull[1:]):
        if x1 <= ratio <= x2:
            f = (ratio - x1) / (x2 - x1) if x2 > x1 else 0.0
            return 1.0 / (y1 + f * (y2 - y1))
    return 1.0 / hull[-1][1] if ratio >= hull[-1][0] else None

def main():
    cand = load(sys.argv[1])
    ref = load(sys.argv[2] if len(sys.argv) > 2 else "bench/results/latest.json")
    native = agg(cand, "native")
    ref_native = agg(ref, "native")
    for lvl, pt in ref_native.items():
        native.setdefault(lvl, pt)
    hull = frontier(native)
    print("native points (weighted silesia):")
    for lvl in sorted(native):
        r, s = native[lvl]
        print(f"  L{lvl:<2} ratio={r:.4f} {s:7.2f} MB/s")
    print("native frontier vertices: " +
          ", ".join(f"({r:.4f}, {1/y:.1f} MB/s)" for r, y in hull))
    print()
    for comp in ["miniz_oxide", "zlib", "go", "zig", "js", "ocaml", "libdeflate"]:
        pts = agg(ref, comp)
        for lvl in sorted(pts):
            r, s = pts[lvl]
            fs = frontier_speed_at(hull, r)
            if fs is None:
                verdict, margin = "OUTSIDE (ratio unreachable)", ""
            else:
                margin = f"{100 * (fs - s) / s:+6.1f}%"
                verdict = "inside " if fs > s else "OUTSIDE"
            flag = "  <== TARGET" if (comp, lvl) == ("miniz_oxide", 6) else ""
            print(f"{comp:12s} L{lvl:<2} ratio={r:.4f} {s:7.2f} MB/s  "
                  f"native@ratio={fs and f'{fs:7.2f}' or '   ---'}  {verdict} {margin}{flag}")

if __name__ == "__main__":
    main()
