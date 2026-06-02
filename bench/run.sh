#!/usr/bin/env bash
# Regenerate the Track D benchmark dashboard end to end:
#   1. build + run the matrix  → bench/results/latest.json   (lake exe bench-report)
#   2. render the log-scale SVGs → bench/graphs/*.svg          (bench/plot.py)
#
# Run from anywhere in the repo. Re-enters nix-shell if not already inside one
# (needs zlib + cargo for the comparators and python3+matplotlib for plotting).
#
# Note: throughput numbers are a median-of-N snapshot of THIS machine; commit
# the regenerated JSON + SVGs together, and record the machine in the dashboard.
set -euo pipefail
cd "$(git -C "$(dirname "$0")" rev-parse --show-toplevel)"

OUT="bench/results/latest.json"
CMD="lake build bench-report \
  && lake env .lake/build/bin/bench-report $OUT \
  && python bench/plot.py $OUT bench/graphs"

if [ -n "${IN_NIX_SHELL:-}" ]; then
  bash -c "$CMD"
else
  nix-shell --run "$CMD"
fi

echo "Track D dashboard regenerated:"
echo "  data   → $OUT"
echo "  graphs → bench/graphs/*.svg"
