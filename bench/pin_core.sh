#!/usr/bin/env bash
# Run a command pinned to the idlest CPU core: bench/pin_core.sh <cmd> [args...]
#
# Every throughput number recorded under bench/results/ is a snapshot of one
# machine, and the dashboard compares snapshots across runs and branches — so
# a measurement that wanders across cores (scheduler migrations, turbo and
# cache effects, contention with concurrent builds on a shared box) adds
# run-to-run noise that has repeatedly been mistaken for real perf deltas.
# Pinning to a single idle core is the cheap fix, but only when every caller
# remembers to do it; this wrapper makes it automatic for the bench pipeline
# (bench/run.sh and the perf-pr-graphs skill route measurements through it).
#
# Core choice: sample /proc/stat twice, 300 ms apart, and pick the core with
# the highest idle fraction over the interval (ties → the highest-numbered
# core, which is least likely to pick up stray OS work). The pinned command
# and all its children inherit the affinity.
#
# On systems without taskset or /proc/stat (e.g. macOS), exec unpinned — the
# recorded numbers there are already marked by machine in the dashboard meta.
set -euo pipefail

if [ $# -eq 0 ]; then
  echo "usage: bench/pin_core.sh <cmd> [args...]" >&2
  exit 2
fi

if ! command -v taskset >/dev/null 2>&1 || [ ! -r /proc/stat ]; then
  echo "pin_core: taskset//proc/stat unavailable, running unpinned" >&2
  exec "$@"
fi

A="$(grep '^cpu[0-9]' /proc/stat)"
sleep 0.3
B="$(grep '^cpu[0-9]' /proc/stat)"

CORE=$(awk '
  NR == FNR { idle[$1] = $5 + $6; t = 0; for (i = 2; i <= NF; i++) t += $i; tot[$1] = t; next }
  {
    didle = ($5 + $6) - idle[$1]
    dtot = 0; for (i = 2; i <= NF; i++) dtot += $i; dtot -= tot[$1]
    frac = dtot > 0 ? didle / dtot : 1
    n = substr($1, 4) + 0
    if (!seen || frac > best + 1e-9 || (frac >= best - 1e-9 && n > core)) {
      seen = 1; best = frac; core = n
    }
  }
  END { print core }
' <(printf '%s\n' "$A") <(printf '%s\n' "$B"))

echo "pin_core: pinning to cpu${CORE}" >&2
exec taskset -c "$CORE" "$@"
