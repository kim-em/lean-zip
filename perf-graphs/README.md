# PR #2892 Pareto evidence

This directory pins the inputs, generator, audit, and rendered before/after
graphs used to review PR #2892.

- reference dashboard: `lean-zip-current-master-reference.5f15833e.json`,
  copied from current `master` at `5f15833e` (its native snapshot metadata
  names `88ed5fa0`)
- native before: compressor sources at `88ed5fa0`, paired median-of-5; this was
  not a clean checkout because it carried only the required, fingerprinted
  benchmark-interface backport
- native after: clean commit `54b38299`, paired median-of-5
- pairing manifest: `final-v6-manifest.54b38299.json`, recording one complete
  CPU-95 checkerboard AB/BA session plus two audited reruns of
  `silesia/mozilla|1`, each under a recorded private core-scheduling cookie;
  final session 2 replaced the contaminated timing
- frontier tolerance: 3% only for cross-session native timing drift; miniz
  containment remains strict

The updated Silesia L1 equal-file-geomean throughput is
`162.895 -> 267.322 MB/s`.

Reproduce from the project Nix shell:

```sh
python3 perf-graphs/pareto_evidence.py \
  perf-graphs/lean-zip-current-master-reference.5f15833e.json \
  perf-graphs/final-v6-before.54b38299.json \
  perf-graphs/final-v6-after.54b38299.json \
  --frontier-tolerance-pct 3 \
  -o perf-graphs/reproduced
```

The expected result is `OVERALL NATIVE ACHIEVABLE FRONTIER: PASS` and
`SILESIA MINIZ_OXIDE L1-L9 CONTAINMENT: PASS` in `pareto_audit.txt`.
