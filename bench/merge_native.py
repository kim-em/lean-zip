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

The merged document keeps the fresh run's headline date/commit, while
``meta.row_provenance`` partitions every row into exact-key measurement groups.
On later merges, those groups are flattened and trimmed rather than nested, so
the original session for each reused row remains visible. Both inputs must
declare the routine median-of-5 timing protocol; refusing legacy or one-shot
inputs prevents a partial splice from hiding mixed repetition counts.
"""
import hashlib
import json
import sys
from pathlib import Path

from benchmark_json import load_routine

old_path, new_path, out_path = sys.argv[1:4]
old = load_routine(old_path)
new = load_routine(new_path)

if "row_provenance" in new["meta"]:
    sys.exit("new input must be a raw freshly measured snapshot, not a prior merge")
if old["meta"].get("machine") != new["meta"].get("machine"):
    sys.exit(
        "old and new benchmark rows were measured on different machines: "
        f"{old['meta'].get('machine')!r} != {new['meta'].get('machine')!r}"
    )

key = lambda r: (r["compressor"], r["pattern"], r["level"])
old_keys = [key(r) for r in old["results"]]
new_keys = [key(r) for r in new["results"]]
if len(set(old_keys)) != len(old_keys):
    sys.exit("old input contains duplicate (compressor, pattern, level) keys")
if len(set(new_keys)) != len(new_keys):
    sys.exit("new input contains duplicate (compressor, pattern, level) keys")

merged = {key(r): r for r in old["results"]}
for r in new["results"]:
    merged[key(r)] = r

fresh_keys = sorted(new_keys)
fresh_key_set = set(fresh_keys)
reused_keys = set(merged) - fresh_key_set

def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def source_meta(meta):
    """Remove merge-level annotations from a raw measurement metadata block."""
    return {
        field: value for field, value in meta.items()
        if field not in {"row_provenance", "provenance_scope"}
    }


def serialized_keys(keys):
    return [list(row_key) for row_key in sorted(keys)]


def prior_groups(doc, path):
    """Return validated, flat measurement groups for ``doc``'s old rows."""
    all_keys = {key(row) for row in doc["results"]}
    provenance = doc["meta"].get("row_provenance")
    groups = provenance.get("groups") if isinstance(provenance, dict) else None
    if groups is None:
        group = {
            "source": Path(path).name,
            "sha256": sha256(path),
            "row_count": len(all_keys),
            "keys": serialized_keys(all_keys),
            "meta": source_meta(doc["meta"]),
        }
        return [(group, all_keys)]
    if not isinstance(groups, list) or not groups:
        sys.exit("old input has malformed meta.row_provenance.groups")

    seen = set()
    validated = []
    for index, group in enumerate(groups):
        if not isinstance(group, dict) or not isinstance(group.get("keys"), list):
            sys.exit(f"old provenance group {index} is malformed")
        try:
            group_keys = {tuple(row_key) for row_key in group["keys"]}
        except TypeError:
            sys.exit(f"old provenance group {index} contains a malformed key")
        if any(len(row_key) != 3 for row_key in group_keys):
            sys.exit(f"old provenance group {index} contains a malformed key")
        if group.get("row_count") != len(group_keys):
            sys.exit(f"old provenance group {index} has an incorrect row_count")
        if seen & group_keys:
            sys.exit("old provenance groups contain duplicate keys")
        if not group_keys <= all_keys:
            sys.exit("old provenance groups contain keys absent from results")
        if not isinstance(group.get("meta"), dict):
            sys.exit(f"old provenance group {index} has no metadata block")
        seen.update(group_keys)
        validated.append((group, group_keys))
    if seen != all_keys:
        sys.exit("old provenance groups do not cover every result row")
    return validated


def retained_prior_groups(doc, path, retained_keys):
    groups = []
    for group, group_keys in prior_groups(doc, path):
        kept = group_keys & retained_keys
        if not kept:
            continue
        retained = {
            field: value for field, value in group.items()
            if field not in {"input_role", "row_count", "keys"}
        }
        retained.update({
            "input_role": "reused",
            "row_count": len(kept),
            "keys": serialized_keys(kept),
        })
        groups.append(retained)
    return groups

common_fields = (
    "date",
    "machine",
    "git_commit",
    "toolchain",
    "timing_aggregation",
    "timing_reps",
)
meta = {field: new["meta"][field]
        for field in common_fields if field in new["meta"]}
meta["provenance_scope"] = (
    "date/git_commit/machine/toolchain describe row_provenance.fresh_keys; "
    "row_provenance.groups partitions every row by measurement session; "
    "timing_aggregation/timing_reps are validated for all inputs"
)
fresh_group = {
    "input_role": "fresh",
    "source": Path(new_path).name,
    "sha256": sha256(new_path),
    "row_count": len(fresh_keys),
    "keys": serialized_keys(fresh_keys),
    "meta": source_meta(new["meta"]),
}
meta["row_provenance"] = {
    "schema_version": 1,
    "fresh_keys": serialized_keys(fresh_keys),
    "merge_inputs": {
        "fresh": {
            "source": Path(new_path).name,
            "sha256": sha256(new_path),
        },
        "reused": {
            "source": Path(old_path).name,
            "sha256": sha256(old_path),
        },
    },
    "groups": [fresh_group] + retained_prior_groups(old, old_path, reused_keys),
}
meta["note"] = (
    f"{len(fresh_keys)} freshly measured rows and {len(reused_keys)} reused rows; "
    "all throughput rows declare median-of-5; see row_provenance for "
    "session-specific metadata; ratio is deterministic"
)

out = dict(old)
out["meta"] = meta
out["results"] = list(merged.values())
with open(out_path, "w", encoding="utf-8") as stream:
    json.dump(out, stream, indent=1)
    stream.write("\n")
print(f"merged {len(new['results'])} fresh rows over {len(old['results'])} "
      f"-> {len(merged)} total")
