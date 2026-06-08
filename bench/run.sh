#!/usr/bin/env bash
# Regenerate the Track D benchmark dashboard end to end:
#   1. build + run the matrix    → bench/results/latest.json  (lake exe bench-report)
#   2. dump the exact payloads    → bench/payloads/<corpus>/*.bin
#   3. build + run the external-language comparators (Go / JS / Zig / OCaml),
#      merging their rows into the same JSON
#   4. render the log-scale SVGs  → bench/graphs/*.svg          (bench/plot.py)
#
# Run from anywhere in the repo. The Lean matrix and plotting use the project
# nix-shell (zlib + cargo for the FFI comparators, python3 + matplotlib for the
# plots); the external comparators each pull their own toolchain (see
# comparators/build_all.sh) and are run with node + python3 on PATH.
#
# Note: throughput numbers are a median-of-N snapshot of THIS machine; commit the
# regenerated JSON + SVGs together, and record the machine in the dashboard.
set -euo pipefail
cd "$(git -C "$(dirname "$0")" rev-parse --show-toplevel)"

OUT="bench/results/latest.json"

in_project_shell() {
  if [ -n "${IN_NIX_SHELL:-}" ]; then bash -c "$1"; else nix-shell --run "$1"; fi
}

# 0. Materialize the real corpora. Canterbury is committed, so this is a no-op
#    checksum re-verify in CI; it re-fetches only if the cache is missing.
if [ ! -d bench/corpora/canterbury ]; then
  bash bench/fetch_corpora.sh canterbury
fi
# Silesia (~202 MB, gitignored) is fetched on demand; skip if already present.
if [ ! -d bench/corpora/silesia ] || [ -z "$(ls -A bench/corpora/silesia 2>/dev/null)" ]; then
  bash bench/fetch_corpora.sh silesia
fi

# 1 + 2. Lean matrix and payload dump (project shell). The matrix times the real
#    corpus files only (pattern "<corpus>/<file>", e.g. "canterbury/alice29.txt");
#    --dump-payloads writes the corpus bytes under bench/payloads/<corpus>/ for the
#    external comparators.
in_project_shell "lake build bench-report \
  && lake env .lake/build/bin/bench-report $OUT \
  && lake env .lake/build/bin/bench-report --dump-payloads bench/payloads"

# 3. External-language comparators: build (own toolchains) then run + merge.
#    node + python3 must be on PATH for the JS comparator and the driver.
bash bench/comparators/build_all.sh
nix-shell -p nodejs python3 --run \
  "python3 bench/comparators/run_external.py bench/payloads $OUT"

# 4. Render (project shell: python + matplotlib).
in_project_shell "python bench/plot.py $OUT bench/graphs"

echo "Track D dashboard regenerated:"
echo "  data   → $OUT"
echo "  graphs → bench/graphs/*.svg"
