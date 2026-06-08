#!/usr/bin/env python3
"""Run the external-language DEFLATE comparators and merge their rows into the
Track D results JSON.

Each comparator is a prebuilt CLI (see build_all.sh) honouring the contract:

    <cmd...> <payload.bin> <level>   ->   stdout JSON
    {"out_size": N, "compress_mbps": X, "decompress_mbps": Y}

It self-verifies its own roundtrip (compress -> decompress == original) and uses
the same timing methodology as ZipBenchReport.lean (median-of-5, itersFor(size)
iters, throughput vs uncompressed bytes). This driver pairs each emitted row with
the (pattern, size) parsed from the payload filename and the requested level,
computes ratio = out_size/size, and splices the rows into results.json's
"results" array (replacing any prior rows for the same compressors, so re-runs
are idempotent).

Usage: run_external.py <payloads_dir> <results.json> [comparator_key ...]
Comparators whose binary is missing are skipped with a warning, so the dashboard
degrades gracefully when a toolchain is unavailable.
"""
import json
import shutil
import subprocess
import sys
from pathlib import Path

# key -> (display label for warnings, run-command prefix, levels to sample)
COMPARATORS = {
    "go":    ("Go compress/flate",        ["bench/comparators/go/bench-go"],          range(1, 10)),
    "js":    ("JS fflate (Node)",         ["node", "bench/comparators/js/bench.mjs"],  range(1, 10)),
    "zig":   ("Zig std.compress.flate",   ["bench/comparators/zig/bench-zig"],         range(1, 10)),
    "ocaml": ("OCaml decompress",         ["bench/comparators/ocaml/bench-ocaml"],     range(1, 10)),
}


def runnable(cmd):
    """First token is either an on-PATH program (node) or a built binary path."""
    head = cmd[0]
    if "/" in head:
        return Path(head).exists()
    return shutil.which(head) is not None


def discover_payloads(payloads_dir):
    """Yield (path, pattern, size) for every benchmark payload.

    Two layouts coexist in the dump dir (see ZipBenchReport.dumpPayloads):
      * flat synthetic files  "<pattern>_<size>.bin"  -> pattern, size from name
      * real-corpus files in a per-corpus subdir "<corpus>/<file>.bin"
        -> pattern "<corpus>/<file>", size = byte length
    Both reconstruct the exact `pattern` string used by the native rows, so the
    external rows line up in the dashboard."""
    pdir = Path(payloads_dir)
    items = []
    for payload in sorted(pdir.glob("*.bin")):
        pat, _, size = payload.stem.rpartition("_")
        items.append((payload, pat, int(size)))
    for sub in sorted(p for p in pdir.iterdir() if p.is_dir()):
        for payload in sorted(sub.glob("*.bin")):
            items.append((payload, f"{sub.name}/{payload.stem}", payload.stat().st_size))
    return items


def collect(key, payloads):
    label, cmd, levels = COMPARATORS[key]
    if not runnable(cmd):
        print(f"  skip {key} ({label}): {cmd[0]} not found", file=sys.stderr)
        return None
    rows = []
    for payload, pat, size in payloads:
        for level in levels:
            try:
                out = subprocess.run(cmd + [str(payload), str(level)],
                                     capture_output=True, text=True, check=True)
                stat = json.loads(out.stdout.strip().splitlines()[-1])
            except (subprocess.CalledProcessError, json.JSONDecodeError, IndexError) as e:
                err = getattr(e, "stderr", str(e))
                print(f"  {key} {pat} {size} L{level} failed: {err}", file=sys.stderr)
                continue
            out_size = stat["out_size"]
            rows.append({
                "compressor": key, "pattern": pat, "size": size, "level": level,
                "out_size": out_size,
                "ratio": round(out_size / max(size, 1), 4),
                "compress_mbps": stat.get("compress_mbps"),
                "decompress_mbps": stat.get("decompress_mbps"),
            })
    print(f"  {key} ({label}): {len(rows)} rows", file=sys.stderr)
    return rows


def main():
    if len(sys.argv) < 3:
        sys.exit("usage: run_external.py <payloads_dir> <results.json> [key ...]")
    payloads_dir, results_path = sys.argv[1], Path(sys.argv[2])
    keys = sys.argv[3:] or list(COMPARATORS)

    doc = json.loads(results_path.read_text())
    results = doc["results"]

    payloads = discover_payloads(payloads_dir)

    added = {}
    for key in keys:
        rows = collect(key, payloads)
        if rows is not None:
            added[key] = rows

    # Idempotent splice: drop prior rows for the comparators we just ran.
    results = [r for r in results if r["compressor"] not in added]
    for rows in added.values():
        results.extend(rows)
    doc["results"] = results
    results_path.write_text(json.dumps(doc, indent=0))
    total = sum(len(r) for r in added.values())
    print(f"merged {total} external rows from {list(added)} -> {results_path}", file=sys.stderr)


if __name__ == "__main__":
    main()
