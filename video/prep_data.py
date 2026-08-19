#!/usr/bin/env python3
"""Extract the Pareto chart data the video needs into video/data/history.json.

Two parts, both geomean-per-level over the Silesia files, matching how
bench/plot.py aggregates:

- "reference": for every compressor in the committed bench/results/latest.json
  at HEAD, the (ratio, compress MB/s) point per level.
- "history": for every commit touching bench/results/latest.json, the native
  per-level points, with a light noise filter so the animation doesn't jitter
  (a frame is dropped when every ratio moved < 5e-4 and every throughput moved
  < 0.035 in log10 versus the last kept frame; first and last frames always
  kept). This mirrors bench/pareto_history.py's thresholds, not its full
  spike logic; good enough for the mockup.

Run from the repository root: python3 video/prep_data.py
"""
import json
import math
import subprocess
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
OUT = Path(__file__).resolve().parent / "data" / "history.json"

RATIO_EPS = 5e-4
LOGSPEED_EPS = 0.035


def geomean(xs):
    return math.exp(sum(math.log(x) for x in xs) / len(xs))


def level_points(results, compressor):
    """{level: (ratio, mbps)} geomean over silesia files."""
    per = {}
    for row in results:
        if row.get("compressor") != compressor:
            continue
        if not row.get("pattern", "").startswith("silesia/"):
            continue
        if not (row.get("compress_mbps") and row.get("ratio")):
            continue
        per.setdefault(row["level"], []).append((row["ratio"], row["compress_mbps"]))
    return {
        lv: (geomean([r for r, _ in v]), geomean([m for _, m in v]))
        for lv, v in per.items()
    }


def git_show(ref, path):
    return subprocess.run(
        ["git", "-C", str(REPO), "show", f"{ref}:{path}"],
        capture_output=True, text=True, check=True,
    ).stdout


def load_results(blob):
    data = json.loads(blob)
    return data["results"] if isinstance(data, dict) else data


def close(a, b):
    if set(a) != set(b):
        return False
    for lv in a:
        if abs(a[lv][0] - b[lv][0]) >= RATIO_EPS:
            return False
        if abs(math.log10(a[lv][1]) - math.log10(b[lv][1])) >= LOGSPEED_EPS:
            return False
    return True


def main():
    head = load_results(git_show("HEAD", "bench/results/latest.json"))
    compressors = sorted({r.get("compressor") for r in head} - {None})
    reference = {}
    for c in compressors:
        pts = level_points(head, c)
        if pts:
            reference[c] = [
                {"level": lv, "ratio": pts[lv][0], "mbps": pts[lv][1]}
                for lv in sorted(pts)
            ]

    log = subprocess.run(
        ["git", "-C", str(REPO), "log", "--reverse", "--format=%H|%h|%cs|%s",
         "--", "bench/results/latest.json"],
        capture_output=True, text=True, check=True,
    ).stdout
    frames, last_kept = [], None
    lines = [l for l in log.strip().split("\n") if l]
    for i, line in enumerate(lines):
        full, short, date, subject = line.split("|", 3)
        try:
            pts = level_points(load_results(git_show(full, "bench/results/latest.json")), "native")
        except Exception:
            continue
        if not pts:
            continue
        is_last = i == len(lines) - 1
        if last_kept is not None and not is_last and close(pts, last_kept):
            continue
        last_kept = pts
        frames.append({
            "commit": short, "date": date, "subject": subject,
            "levels": [
                {"level": lv, "ratio": pts[lv][0], "mbps": pts[lv][1]}
                for lv in sorted(pts)
            ],
        })

    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps({"reference": reference, "history": frames}, indent=1))
    print(f"wrote {OUT}: {len(reference)} reference curves, {len(frames)} history frames")


if __name__ == "__main__":
    main()
