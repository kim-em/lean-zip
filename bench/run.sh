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

# Pin every *measurement* process to one CPU (#2739): unpinned runs migrate
# between cores mid-sweep and pick up multi-MB/s run-to-run drift on a busy
# box. Builds and plotting stay unpinned. Default: the last physical core
# (on an SMT machine, core N pairs with hyperthread N + nproc/2, so this also
# keeps the sibling of core 0 free). Override with BENCH_PIN=<cpu>, or
# BENCH_PIN=none to disable (e.g. single-core CI runners).
BENCH_PIN="${BENCH_PIN:-$(( $(nproc) / 2 - 1 ))}"
if [ "$BENCH_PIN" = "none" ]; then PIN=""; else PIN="taskset -c $BENCH_PIN"; fi

in_project_shell() {
  if [ -n "${IN_NIX_SHELL:-}" ]; then bash -c "$1"; else nix-shell --run "$1"; fi
}

# Fast path for Lean-only changes: refresh ONLY the native rows and splice them
# back over the existing dashboard, then re-plot. The reference compressors are
# not re-measured — their ratio is deterministic and their MB/s drifts <~3%
# run-to-run (verified across regens) — so this skips the ~2 h external-comparator
# rebuild entirely. The dominant remaining cost is native's own optimal-parse at
# levels 9 (L9-fast) and 10 (exact crown, ~1 MB/s); pass a level list to skip
# them when the Lean change does not touch that path (the prior rows are kept by
# the upsert merge).
#   bench/run.sh --native-only                  # all 10 native levels, incl. the L10 crown (~14 min)
#   bench/run.sh --native-only 1,2,3,4,5,6,7,8  # skip the slow L9/L10 (~half the time)
if [ "${1:-}" = "--native-only" ]; then
  [ -f "$OUT" ] || { echo "no existing $OUT to splice into — run a full bench/run.sh first" >&2; exit 1; }
  TMP="$(mktemp --suffix=.json)"
  in_project_shell "lake build bench-report"
  in_project_shell "$PIN lake env .lake/build/bin/bench-report --native-only $TMP ${2:-}"
  in_project_shell "python3 bench/merge_native.py $OUT $TMP $OUT \
    && python bench/plot.py $OUT bench/graphs"
  rm -f "$TMP"
  echo "Native-only dashboard refresh done:"
  echo "  data   → $OUT (native rows refreshed; reference rows reused)"
  echo "  graphs → bench/graphs/*.svg"
  exit 0
fi

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
in_project_shell "lake build bench-report"
in_project_shell "$PIN lake env .lake/build/bin/bench-report $OUT"
in_project_shell "lake env .lake/build/bin/bench-report --dump-payloads bench/payloads"

# 3. External-language comparators: build (own toolchains) then run + merge.
#    node + python3 must be on PATH for the JS comparator and the driver.
bash bench/comparators/build_all.sh
nix-shell -p nodejs python3 --run \
  "$PIN python3 bench/comparators/run_external.py bench/payloads $OUT"

# 3b. Decode-density experiment (the decompression analogue of the compress
#    Pareto): fix the encoder to libdeflate, dump its raw-DEFLATE streams for
#    Silesia at several levels, and time EVERY decoder on byte-identical input
#    (in-process native/zlib/miniz/libdeflate + a memcpy ceiling on the Lean
#    side, then the external comparators via their `decode` mode). Writes a
#    sibling decode_density.json that plot.py renders as
#    <corpus>_decode_density.svg.
DD="bench/results/decode_density.json"
in_project_shell "$PIN lake env .lake/build/bin/bench-report --decode-density $DD bench/payloads-deflate"
nix-shell -p nodejs python3 --run \
  "$PIN python3 bench/decode_density.py bench/payloads-deflate $DD"

# 4. Render (project shell: python + matplotlib). plot.py auto-detects the
#    sibling decode_density.json and emits the decode-density chart too.
in_project_shell "python bench/plot.py $OUT bench/graphs"

echo "Track D dashboard regenerated:"
echo "  data   → $OUT  (+ decode_density.json)"
echo "  graphs → bench/graphs/*.svg"
