#!/usr/bin/env bash
# Cold single-shot L6 whole-tar dominance gate.
#
#   bench/l6_tar_gate.sh <tarPath> [N]        # N reps, default 9
#
# WHY COLD: the gate must FAIL if lean native DEFLATE L6 stops strictly
# dominating miniz_oxide L6 on the whole silesia.tar in BOTH size and time,
# matching Kim's `hyperfine zip silesia.tar` benchmark. That benchmark is COLD:
# a fresh process each run, so native pays its full page-fault / CAF-build tax
# every time (~0.24 s). An in-process warm loop amortizes that tax after the
# first rep and inflates native's apparent time margin from ~2% (cold) to
# ~4.5% (warm) — enough to green-light a config that is actually ~2.8% SLOWER
# cold. So every timed rep here spawns FRESH `bench` subprocesses.
#
# Native side  : `bench csize 0 @<tar> 6`          — prints native L6 out-size
# miniz side   : `bench compress-miniz 0 @<tar> 6` — prints miniz L6 out-size
# Both are single-shot: one compress of the whole tar, then exit.
#
# Method (paired ratio, cold):
#   (a) one run of each -> native_size, miniz_size; assert native_size < miniz_size.
#   (b) N interleaved cold reps: each rep spawns native and miniz as fresh
#       processes, wall-times each, ALTERNATING which runs first to cancel
#       ordering bias; per-rep ratio = native_wall / miniz_wall.
#   (c) median ratio across reps; assert median < 1.0.
#
# Pinning: keep this script simple; the CI step (or a manual invocation) wraps
# it in bench/pin_core.sh so the whole process tree inherits one idle core.
set -euo pipefail

TAR="${1:-}"
N="${2:-9}"

if [ -z "$TAR" ]; then
  echo "usage: bench/l6_tar_gate.sh <tarPath> [N]" >&2
  exit 2
fi
if [ ! -f "$TAR" ]; then
  echo "FAIL: tar not found: $TAR" >&2
  exit 2
fi

# Vacuity guard: the gate is meaningless on a tiny input (native's fixed page
# tax dominates and the ratio is noise). Require > 1 MiB.
TAR_BYTES="$(wc -c < "$TAR")"
if [ "$TAR_BYTES" -le 1048576 ]; then
  echo "FAIL: tar too small (${TAR_BYTES} B <= 1 MiB); gate needs a large corpus" >&2
  exit 2
fi

# Locate the built bench exe. Resolve relative to this script so it works from
# any CWD, and fall back to the current dir's build tree.
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
BENCH=""
for cand in \
  "$SCRIPT_DIR/.lake/build/bin/bench" \
  "$SCRIPT_DIR/../bench/.lake/build/bin/bench" \
  ".lake/build/bin/bench" \
  "bench/.lake/build/bin/bench"; do
  if [ -x "$cand" ]; then BENCH="$cand"; break; fi
done
if [ -z "$BENCH" ]; then
  echo "FAIL: could not find the built 'bench' exe (looked under $SCRIPT_DIR/.lake/build/bin)" >&2
  exit 2
fi

echo "== L6 cold whole-tar gate =="
echo "tar     : $TAR (${TAR_BYTES} B)"
echo "bench   : $BENCH"
echo "reps    : $N"
echo

# Parse `out=<n>` from a `size=... lvl=6: out=<n> ratio=...%` line.
parse_out() { awk 'match($0, /out=[0-9]+/) { print substr($0, RSTART+4, RLENGTH-4); exit }'; }

# --- (a) size dominance: one run of each, capture out-sizes ---
NATIVE_LINE="$("$BENCH" csize 0 "@$TAR" 6)"
MINIZ_LINE="$("$BENCH" compress-miniz 0 "@$TAR" 6)"
NATIVE_SIZE="$(printf '%s\n' "$NATIVE_LINE" | parse_out)"
MINIZ_SIZE="$(printf '%s\n' "$MINIZ_LINE"  | parse_out)"

if ! [[ "$NATIVE_SIZE" =~ ^[0-9]+$ ]] || ! [[ "$MINIZ_SIZE" =~ ^[0-9]+$ ]]; then
  echo "FAIL: could not parse out-sizes" >&2
  echo "  native line: $NATIVE_LINE" >&2
  echo "  miniz  line: $MINIZ_LINE" >&2
  exit 1
fi

echo "size: native L6 out=$NATIVE_SIZE  miniz L6 out=$MINIZ_SIZE"
if [ "$NATIVE_SIZE" -ge "$MINIZ_SIZE" ]; then
  echo "FAIL: native L6 does not strictly beat miniz L6 on size"
  echo "  native=$NATIVE_SIZE  miniz=$MINIZ_SIZE  (need native < miniz)"
  exit 1
fi
SIZE_MARGIN="$(awk -v a="$NATIVE_SIZE" -v b="$MINIZ_SIZE" 'BEGIN{printf "%.3f", 100.0*(b-a)/b}')"
echo "  -> native is ${SIZE_MARGIN}% smaller. size dominance OK."
echo

# nanosecond wall clock around a fresh subprocess.
run_native() { "$BENCH" csize 0 "@$TAR" 6 >/dev/null; }
run_miniz()  { "$BENCH" compress-miniz 0 "@$TAR" 6 >/dev/null; }

now() { date +%s.%N; }

echo "cold reps (native_wall / miniz_wall):"
printf "  %-4s %-12s %-12s %-8s %-6s\n" "rep" "native(s)" "miniz(s)" "ratio" "first"

RATIOS=()
for ((i=1; i<=N; i++)); do
  # alternate ordering to cancel any first-mover cache/turbo bias.
  if (( i % 2 == 1 )); then
    t0="$(now)"; run_native; t1="$(now)"; run_miniz; t2="$(now)"
    nat="$(awk -v a="$t0" -v b="$t1" 'BEGIN{printf "%.6f", b-a}')"
    miz="$(awk -v a="$t1" -v b="$t2" 'BEGIN{printf "%.6f", b-a}')"
    first="nat"
  else
    t0="$(now)"; run_miniz; t1="$(now)"; run_native; t2="$(now)"
    miz="$(awk -v a="$t0" -v b="$t1" 'BEGIN{printf "%.6f", b-a}')"
    nat="$(awk -v a="$t1" -v b="$t2" 'BEGIN{printf "%.6f", b-a}')"
    first="miz"
  fi
  r="$(awk -v n="$nat" -v m="$miz" 'BEGIN{printf "%.4f", n/m}')"
  RATIOS+=("$r")
  printf "  %-4s %-12s %-12s %-8s %-6s\n" "$i" "$nat" "$miz" "$r" "$first"
done
echo

# --- (c) median ratio + stats ---
STATS="$(printf '%s\n' "${RATIOS[@]}" | sort -n | awk '
  { v[NR]=$1; s+=$1; if(NR==1||$1<mn)mn=$1; if(NR==1||$1>mx)mx=$1 }
  END {
    n=NR
    if (n % 2 == 1) med = v[(n+1)/2]
    else            med = (v[n/2] + v[n/2+1]) / 2.0
    mean = s/n
    ss=0; for (i=1;i<=n;i++){ d=v[i]-mean; ss+=d*d }
    sd = (n>1) ? sqrt(ss/(n-1)) : 0
    printf "%.4f %.4f %.4f %.4f %.4f", med, mean, mn, mx, sd
  }')"
read -r MED MEAN MIN MAX SD <<<"$STATS"

echo "ratio distribution (native_wall / miniz_wall):"
echo "  median=$MED  mean=$MEAN  min=$MIN  max=$MAX  stdev=$SD"
echo

# Median < 1.0 means native is cold-faster on the median rep.
if awk -v m="$MED" 'BEGIN{exit !(m < 1.0)}'; then
  echo "PASS: median ratio $MED < 1.0 — native L6 strictly dominates miniz L6 (size + cold time)."
  exit 0
else
  echo "FAIL: median ratio $MED >= 1.0 — native L6 is NOT cold-faster than miniz L6."
  exit 1
fi
