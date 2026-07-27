# PR #2892 Pareto evidence

This directory pins the inputs, generator, audit, and rendered before/after
graphs used to review PR #2892.

- reference dashboard: `latest.json` at source commit `db16e7ed`
- native before: clean commit `88ed5fa0`, paired median-of-5
- native after: clean commit `137e00f7`, paired median-of-5
- pairing manifest: one CPU-95 checkerboard AB/BA session under a private
  core-scheduling cookie
- frontier tolerance: 3% only for cross-session native timing drift; miniz
  containment remains strict

Reproduce from the project Nix shell:

```sh
python3 perf-graphs/pareto_evidence.py \
  perf-graphs/latest.json \
  perf-graphs/final-v4-before.137e00f7.json \
  perf-graphs/final-v4-after.137e00f7.json \
  --frontier-tolerance-pct 3 \
  -o perf-graphs/reproduced
```

The expected result is `OVERALL NATIVE ACHIEVABLE FRONTIER: PASS` and
`SILESIA MINIZ_OXIDE L1-L9 CONTAINMENT: PASS` in `pareto_audit.txt`.
