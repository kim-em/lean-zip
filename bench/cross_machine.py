#!/usr/bin/env python3
"""Cross-machine consistency report for the Track D dashboard.

Compares two `bench-report` result JSONs (an OLD machine and a NEW machine) and
emits a Markdown report on how the two machines relate, per compressor and per
metric. Used when migrating the canonical benchmark machine (e.g. chungus →
chungus2) to decide whether the move is sound.

Usage:
    python3 bench/cross_machine.py OLD.json NEW.json > report.md

What it checks
--------------
* **Compression ratio** is deterministic and machine-independent, so for the
  *same code* it must be byte-identical across machines. A per-compressor
  `max |Δratio|` therefore separates two effects:
    - external comparators (go/js/zig/ocaml/zlib/miniz_oxide/libdeflate) run the
      *same* third-party code on both machines → any ratio delta is version drift
      in the pinned toolchain, and should be ~0;
    - `native` (lean-zip) may legitimately differ if the two snapshots are at
      different commits — that is a *code* delta, not a machine delta, and is
      called out separately so it is not mistaken for machine inconsistency.
* **Throughput** (`compress_mbps`, `decompress_mbps`): the geomean of
  NEW/OLD per compressor is the machine speed factor. If it is roughly uniform
  across compressors, the two machines are consistently related (one is ~X%
  faster); large per-compressor spread is the signal that the machines are NOT
  cleanly comparable and the move needs scrutiny.

Only `(compressor, pattern, level)` cells present in BOTH inputs are compared.
"""
import json
import math
import sys


def load(path):
    d = json.load(open(path))
    rows = d.get("results", d.get("rows", []))
    idx = {}
    for r in rows:
        idx[(r["compressor"], r["pattern"], r["level"])] = r
    return d.get("meta", {}), idx


def geomean(xs):
    xs = [x for x in xs if x and x > 0]
    if not xs:
        return None
    return math.exp(sum(math.log(x) for x in xs) / len(xs))


def main():
    old_path, new_path = sys.argv[1], sys.argv[2]
    om, oi = load(old_path)
    nm, ni = load(new_path)
    common = sorted(set(oi) & set(ni))
    comps = sorted({k[0] for k in common})

    print("# Cross-machine benchmark consistency\n")
    print(f"- **OLD**: `{om.get('machine','?')}` @ `{om.get('git_commit','?')}` "
          f"({om.get('date','?')}) — `{old_path}`")
    print(f"- **NEW**: `{nm.get('machine','?')}` @ `{nm.get('git_commit','?')}` "
          f"({nm.get('date','?')}) — `{new_path}`")
    print(f"- Compared cells present in both: **{len(common)}** "
          f"across {len(comps)} compressors\n")
    same_commit = om.get("git_commit") == nm.get("git_commit")
    if not same_commit:
        print("> **Note:** the two snapshots are at *different commits*, so the "
              "`native` rows reflect a code delta on top of the machine delta. "
              "For a clean machine comparison read the external comparators "
              "(same third-party code on both machines); treat `native` "
              "throughput as machine × code.\n")

    # Throughput speed factor (NEW / OLD), geomean per compressor.
    print("## Throughput: NEW / OLD (geomean over shared cells)\n")
    print("| compressor | cells | compress× | decompress× |")
    print("|---|---|---|---|")
    for c in comps:
        keys = [k for k in common if k[0] == c]
        cz = geomean([ni[k]["compress_mbps"] / oi[k]["compress_mbps"]
                      for k in keys
                      if oi[k].get("compress_mbps") and ni[k].get("compress_mbps")])
        dz = geomean([ni[k]["decompress_mbps"] / oi[k]["decompress_mbps"]
                      for k in keys
                      if oi[k].get("decompress_mbps") and ni[k].get("decompress_mbps")])
        cs = f"{cz:.3f}x" if cz else "—"
        ds = f"{dz:.3f}x" if dz else "—"
        print(f"| {c} | {len(keys)} | {cs} | {ds} |")

    # External-only summary (the clean machine factor).
    ext = [c for c in comps if c != "native"]
    ext_keys = [k for k in common if k[0] in ext]
    ecz = geomean([ni[k]["compress_mbps"] / oi[k]["compress_mbps"]
                   for k in ext_keys
                   if oi[k].get("compress_mbps") and ni[k].get("compress_mbps")])
    edz = geomean([ni[k]["decompress_mbps"] / oi[k]["decompress_mbps"]
                   for k in ext_keys
                   if oi[k].get("decompress_mbps") and ni[k].get("decompress_mbps")])
    print(f"\n**External comparators (same code, clean machine factor): "
          f"compress {ecz:.3f}x, decompress {edz:.3f}x.** "
          f"A tight cluster around these means the machines are consistently "
          f"related; wide spread means they are not cleanly comparable.\n")

    # Ratio consistency.
    print("## Compression ratio consistency (deterministic → machine-independent)\n")
    print("| compressor | cells | max \\|Δratio\\| | cells with Δ≠0 |")
    print("|---|---|---|---|")
    for c in comps:
        keys = [k for k in common if k[0] == c]
        deltas = [abs(ni[k]["ratio"] - oi[k]["ratio"]) for k in keys
                  if oi[k].get("ratio") is not None and ni[k].get("ratio") is not None]
        mx = max(deltas) if deltas else 0.0
        nz = sum(1 for d in deltas if d > 1e-9)
        print(f"| {c} | {len(keys)} | {mx:.6f} | {nz} |")
    print("\nFor every *external* compressor `max |Δratio|` should be `0.000000` "
          "(same code, deterministic output). A nonzero value flags pinned-"
          "toolchain version drift. `native` may differ iff the snapshots are at "
          "different commits (a code delta, expected).")


if __name__ == "__main__":
    main()
