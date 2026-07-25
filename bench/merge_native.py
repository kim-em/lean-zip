#!/usr/bin/env python3
"""Upsert freshly-measured rows into an existing dashboard JSON.

    merge_native.py <old.json> <new.json> <out.json>

Rows are keyed by (compressor, pattern, level). Every row in <new.json>
overrides the matching row in <old.json>; all other <old.json> rows are kept.
This is how a `bench/run.sh --native-only` refresh splices fresh native rows
back over the prior dashboard without re-measuring the reference compressors
(their ratio is deterministic; their MB/s remains tied to its measurement
session), and how a level-restricted native run (e.g. skipping the slow
optimal-parse L9) keeps
the prior rows for the levels it did not regenerate.

The merged `meta` is taken from <new.json> so the dashboard records the fresh
run's date/commit. Both inputs must declare the routine median-of-5 timing
protocol; refusing legacy or one-shot inputs prevents a partial splice from
hiding mixed repetition counts behind one global metadata block.
"""
import json
import sys

from benchmark_json import load_routine

old_path, new_path, out_path = sys.argv[1:4]
old = load_routine(old_path)
new = load_routine(new_path)

key = lambda r: (r["compressor"], r["pattern"], r["level"])
merged = {key(r): r for r in old["results"]}
for r in new["results"]:
    merged[key(r)] = r

out = dict(old)
out["meta"] = new["meta"]
out["results"] = list(merged.values())
json.dump(out, open(out_path, "w"), indent=1)
print(f"merged {len(new['results'])} fresh rows over {len(old['results'])} "
      f"-> {len(merged)} total")
