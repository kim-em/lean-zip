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
# Core choice: sample /proc/stat twice, 300 ms apart, and score each candidate
# by its idle fraction over the interval, downgraded to the *minimum* idle
# fraction across its SMT sibling group (an "idle" hyperthread whose twin runs
# a build still shares the physical core's execution resources — exactly the
# contention this wrapper exists to avoid). Candidates are intersected with
# the process's allowed affinity set (cgroup cpuset, CI slice, or an outer
# taskset), so the pick can never be a core we may not use. Ties go to the
# highest-numbered core, least likely to pick up stray OS work. The pinned
# command and all its children inherit the affinity.
#
# On systems without taskset or /proc/stat (e.g. macOS), or if anything about
# the selection fails, exec the command unpinned rather than blocking the
# benchmark — the recorded numbers carry the machine in the dashboard meta.
set -euo pipefail

if [ $# -eq 0 ]; then
  echo "usage: bench/pin_core.sh <cmd> [args...]" >&2
  exit 2
fi

if ! command -v taskset >/dev/null 2>&1 || [ ! -r /proc/stat ]; then
  echo "pin_core: taskset//proc/stat unavailable, running unpinned" >&2
  exec "$@"
fi

# CPUs this process may use (e.g. "0-95" or "2,5-7"); empty → no restriction.
ALLOWED="$(taskset -pc $$ 2>/dev/null | sed 's/.*: *//' || true)"

# SMT topology: one "cpu siblings-list" line per CPU (e.g. "0 0,48").
SIBLINGS="$(
  for f in /sys/devices/system/cpu/cpu[0-9]*/topology/thread_siblings_list; do
    [ -r "$f" ] || continue
    c="${f#/sys/devices/system/cpu/cpu}"
    printf '%s %s\n' "${c%%/*}" "$(cat "$f")"
  done 2>/dev/null || true
)"

A="$(grep '^cpu[0-9]' /proc/stat)"
sleep 0.3
B="$(grep '^cpu[0-9]' /proc/stat)"

CORE=$(awk -v allowed="$ALLOWED" '
  # expand a cpu-list spec like "0-3,7" into set[]
  function expand(spec, set,   n, parts, i, r, c) {
    n = split(spec, parts, ",")
    for (i = 1; i <= n; i++) {
      if (parts[i] == "") continue
      if (split(parts[i], r, "-") == 2) { for (c = r[1] + 0; c <= r[2] + 0; c++) set[c] = 1 }
      else set[parts[i] + 0] = 1
    }
  }
  FNR == 1 { fileno++ }
  fileno == 1 { idle[$1] = $5 + $6; t = 0; for (i = 2; i <= NF; i++) t += $i; tot[$1] = t; next }
  fileno == 2 {
    cpu = substr($1, 4) + 0
    didle = ($5 + $6) - idle[$1]
    dtot = 0; for (i = 2; i <= NF; i++) dtot += $i; dtot -= tot[$1]
    frac[cpu] = dtot > 0 ? didle / dtot : 1
    next
  }
  fileno == 3 && NF >= 2 { siblist[$1 + 0] = $2 }
  END {
    expand(allowed, ok)
    anyok = 0; for (c in ok) { anyok = 1; break }
    best = -1; core = -1
    for (cpu in frac) {
      c = cpu + 0
      if (anyok && !(c in ok)) continue
      # group score: the busiest sibling bounds what the physical core can give
      score = frac[c]
      if (c in siblist) {
        delete sset; expand(siblist[c], sset)
        for (s in sset) if ((s + 0) in frac && frac[s + 0] < score) score = frac[s + 0]
      }
      if (score > best + 1e-9 || (score >= best - 1e-9 && c > core)) { best = score; core = c }
    }
    if (core >= 0) print core
  }
' <(printf '%s\n' "$A") <(printf '%s\n' "$B") <(printf '%s\n' "$SIBLINGS"))

if ! [[ "$CORE" =~ ^[0-9]+$ ]] || ! taskset -c "$CORE" true 2>/dev/null; then
  echo "pin_core: could not select a usable core, running unpinned" >&2
  exec "$@"
fi

echo "pin_core: pinning to cpu${CORE}" >&2
exec taskset -c "$CORE" "$@"
