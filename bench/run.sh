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
#
# Every *measurement* step below runs through bench/pin_core.sh, which pins the
# command (and its children) to the idlest single core — unpinned runs wander
# across cores and pick up scheduler/turbo/contention noise that has been
# mistaken for real perf deltas. Builds, merges, and plotting stay unpinned.
set -euo pipefail
cd "$(git -C "$(dirname "$0")" rev-parse --show-toplevel)"

OUT="bench/results/latest.json"
WTAR="bench/results/whole_tar_l6.json"
PIN="bash bench/pin_core.sh"

in_project_shell() {
  if [ -n "${IN_NIX_SHELL:-}" ]; then bash -c "$1"; else nix-shell --run "$1"; fi
}

# Whole-tar L6 measurement: record native vs miniz_oxide on the COLD whole
# silesia.tar (compressed size + cold time) into bench/results/whole_tar_l6.json.
# The per-file dashboard ($OUT) tracks WARM per-file throughput and misses the
# `zip silesia.tar` cold-stream workload, where a deeper L6 probe / rolling can
# regress invisibly (three PRs did). This is a MEASUREMENT that records — not a
# gate — surfaced in the perf-graphs review. Pinned like the other measurement
# steps; miniz here is deterministic and cheap, so it runs on both paths. Needs
# the `bench` exe (distinct from bench-report). Guarded on the silesia corpus.
refresh_whole_tar() {
  if [ ! -d bench/corpora/silesia ] || [ -z "$(ls -A bench/corpora/silesia 2>/dev/null)" ]; then
    echo "whole-tar L6: silesia corpus absent — skipping $WTAR refresh" >&2
    return 0
  fi
  in_project_shell "lake -d bench build bench \
    && $PIN bash bench/whole_tar_l6.sh bench/corpora/silesia 9 $WTAR"
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
  in_project_shell "lake -d bench build bench-report \
    && $PIN lake -d bench env bench/.lake/build/bin/bench-report --native-only $TMP ${2:-}"
  in_project_shell "python3 bench/merge_native.py $OUT $TMP $OUT \
    && python bench/plot.py $OUT bench/graphs \
    && python bench/pareto_history.py"
  rm -f "$TMP"
  refresh_whole_tar
  echo "Native-only dashboard refresh done:"
  echo "  data   → $OUT (native rows refreshed; reference rows reused)"
  echo "  data   → $WTAR (whole-tar L6: native vs miniz, cold)"
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
in_project_shell "lake -d bench build bench-report \
  && $PIN lake -d bench env bench/.lake/build/bin/bench-report $OUT \
  && lake -d bench env bench/.lake/build/bin/bench-report --dump-payloads bench/payloads"

# 3. External-language comparators: build (own toolchains) then run + merge.
#    node + python3 must be on PATH for the JS comparator and the driver. The
#    driver is pinned, so every comparator child inherits the single-core
#    affinity and their rows are measured like the native ones.
bash bench/comparators/build_all.sh
nix-shell -p nodejs_latest python3 --run \
  "$PIN python3 bench/comparators/run_external.py bench/payloads $OUT"

# 3b. Decode-density experiment (the decompression analogue of the compress
#    Pareto): fix the encoder to libdeflate, dump its raw-DEFLATE streams for
#    Silesia at several levels, and time EVERY decoder on byte-identical input
#    (in-process native/zlib/miniz/libdeflate + a memcpy ceiling on the Lean
#    side, then the external comparators via their `decode` mode). Writes a
#    sibling decode_density.json that plot.py renders as
#    <corpus>_decode_density.svg.
DD="bench/results/decode_density.json"
in_project_shell "$PIN lake -d bench env bench/.lake/build/bin/bench-report --decode-density $DD bench/payloads-deflate"
nix-shell -p nodejs_latest python3 --run \
  "$PIN python3 bench/decode_density.py bench/payloads-deflate $DD"

# 3c. Whole-tar L6 measurement (native vs miniz_oxide, cold). Records the
#    `zip silesia.tar` cold-stream workload the per-file Pareto misses into
#    bench/results/whole_tar_l6.json. See refresh_whole_tar above.
refresh_whole_tar

# 4. Render (project shell: python + matplotlib). plot.py auto-detects the
#    sibling decode_density.json and emits the decode-density chart too;
#    pareto_history.py replays the git history of latest.json into the
#    animated Pareto (the just-refreshed uncommitted data becomes its final
#    frame — see bench/pareto_history.py).
in_project_shell "python bench/plot.py $OUT bench/graphs \
  && python bench/pareto_history.py"

echo "Track D dashboard regenerated:"
echo "  data   → $OUT  (+ decode_density.json, whole_tar_l6.json)"
echo "  graphs → bench/graphs/*.svg"
