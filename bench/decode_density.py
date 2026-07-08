#!/usr/bin/env python3
"""Run the external-language decoders over the fixed libdeflate streams and merge
their rows into the decode-density results JSON.

The decode-density experiment (see ZipBenchReport.runDecodeDensity) fixes the
encoder to libdeflate and measures every decoder on byte-identical raw-DEFLATE
streams. The in-process decoders (native/zlib/miniz/libdeflate) and the memcpy
ceiling are timed on the Lean side; this driver covers the external comparators
(Go / JS / Zig / OCaml) via their `decode` mode:

    <cmd...> decode <stream.deflate>   ->   stdout JSON
    {"decompress_mbps": Y, "decoded_size": N}

Each comparator self-times median-of-5, itersFor(decoded size) iters, throughput
against the decoded (uncompressed) byte count — the same methodology as the Lean
side. Rows reuse the results schema with `compressor` holding the decoder name and
`ratio` holding libdeflate's compression ratio (= stream size / decoded size), the
x-axis of the decode-density chart.

Usage: decode_density.py <streams_dir> <decode_density.json> [comparator_key ...]
"""
import json
import shutil
import subprocess
import sys
from pathlib import Path

# key -> (display label, decode-command prefix)
COMPARATORS = {
    "go":    ("Go compress/flate",      ["bench/comparators/go/bench-go", "decode"]),
    "js":    ("JS fflate (Node)",       ["node", "bench/comparators/js/bench.mjs", "decode"]),
    "zig":   ("Zig std.compress.flate", ["bench/comparators/zig/bench-zig", "decode"]),
    "ocaml": ("OCaml decompress",       ["bench/comparators/ocaml/bench-ocaml", "decode"]),
}


def runnable(cmd):
    head = cmd[0]
    return Path(head).exists() if "/" in head else shutil.which(head) is not None


# libdeflate levels dumped by ZipBenchReport.decodeDensityLevels (keep in sync).
KNOWN_LEVELS = {1, 3, 6, 9, 12}


def discover_streams(streams_dir):
    """Yield (path, corpus, pattern, level) for every recognized fixed-encoder
    stream. libdeflate streams are `<corpus>/<file>_L<level>.deflate` with level in
    KNOWN_LEVELS; the zopfli stream is `<corpus>/<file>_zopfli.deflate` and carries
    the level-less sentinel level 0. Anything else under the cache (stale or
    hand-dropped files) is skipped with a warning rather than crashing or leaking
    external-only rows that would unbalance the ranking geomean."""
    sdir = Path(streams_dir)
    items = []
    for sub in sorted(p for p in sdir.iterdir() if p.is_dir()):
        for stream in sorted(sub.glob("*.deflate")):
            stem = stream.stem
            if stem.endswith("_zopfli"):
                file, level = stem[: -len("_zopfli")], 0
            elif "_L" in stem:
                file, _, lvl = stem.rpartition("_L")
                if not lvl.isdigit() or int(lvl) not in KNOWN_LEVELS:
                    print(f"  skip unrecognized stream {sub.name}/{stream.name}", file=sys.stderr)
                    continue
                level = int(lvl)
            else:
                print(f"  skip unrecognized stream {sub.name}/{stream.name}", file=sys.stderr)
                continue
            items.append((stream, sub.name, f"{sub.name}/{file}", level))
    return items


def collect(key, streams):
    label, cmd = COMPARATORS[key]
    if not runnable(cmd):
        print(f"  skip {key} ({label}): {cmd[0]} not found", file=sys.stderr)
        return None
    rows = []
    for path, _corpus, pat, level in streams:
        try:
            out = subprocess.run(cmd + [str(path)], capture_output=True, text=True, check=True)
            stat = json.loads(out.stdout.strip().splitlines()[-1])
        except (subprocess.CalledProcessError, json.JSONDecodeError, IndexError) as e:
            print(f"  {key} {pat} L{level} failed: {getattr(e, 'stderr', str(e))}", file=sys.stderr)
            continue
        decoded = stat["decoded_size"]
        stream_size = path.stat().st_size
        rows.append({
            "compressor": key, "pattern": pat, "size": decoded, "level": level,
            "out_size": stream_size,
            "ratio": round(stream_size / max(decoded, 1), 4),
            "compress_mbps": None,
            "decompress_mbps": stat.get("decompress_mbps"),
        })
    print(f"  {key} ({label}): {len(rows)} rows", file=sys.stderr)
    return rows


def main():
    if len(sys.argv) < 3:
        sys.exit("usage: decode_density.py <streams_dir> <decode_density.json> [key ...]")
    streams_dir, results_path = sys.argv[1], Path(sys.argv[2])
    keys = sys.argv[3:] or list(COMPARATORS)

    doc = json.loads(results_path.read_text())
    results = doc["results"]
    streams = discover_streams(streams_dir)

    added = {}
    for key in keys:
        rows = collect(key, streams)
        if rows is not None:
            added[key] = rows

    results = [r for r in results if r["compressor"] not in added]
    for rows in added.values():
        results.extend(rows)
    doc["results"] = results
    results_path.write_text(json.dumps(doc, indent=0))
    total = sum(len(r) for r in added.values())
    print(f"merged {total} external decode rows from {list(added)} -> {results_path}", file=sys.stderr)


if __name__ == "__main__":
    main()
