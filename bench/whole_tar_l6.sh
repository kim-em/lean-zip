#!/usr/bin/env bash
# Record the cold single-shot L6 whole-tar comparison: lean native DEFLATE vs
# miniz_oxide on the whole silesia.tar, in BOTH compressed size and cold time.
#
#   bench/whole_tar_l6.sh <corpusDir> [N=9] [outJson=bench/results/whole_tar_l6.json]
#
# WHY THIS EXISTS: the per-file dashboard (bench/results/latest.json) tracks
# per-file WARM throughput. That amortizes native's page-fault / CAF-build tax
# after the first rep and measures small files where the split/probe economics
# differ — so a config that regresses the whole 202 MB `zip silesia.tar` COLD
# stream (a deeper L6 probe, rolling deferral) can look fine per-file while the
# real workload regresses. Three PRs slipped through exactly this gap. This
# script RECORDS the whole-tar L6 number as committed dashboard data
# (bench/results/whole_tar_l6.json) so a regression surfaces in the perf-graphs
# review already mandatory for perf PRs.
#
# WHY COLD: Kim's headline `hyperfine zip silesia.tar` benchmark is cold — a
# fresh process each run, so native pays its full page-fault / CAF-build tax
# every time (~0.24 s). An in-process warm loop amortizes that tax after the
# first rep and inflates native's apparent time margin from ~2% (cold) to
# ~4.5% (warm) — enough to green-light a config that is actually ~2.8% SLOWER
# cold. So every timed rep here spawns FRESH `bench` subprocesses.
#
# Native side : `bench csize 0 @<tar> 6`          — prints native L6 out-size
# miniz side  : `bench compress-miniz 0 @<tar> 6` — prints miniz L6 out-size
# Both are single-shot: one compress of the whole tar, then exit.
#
# This is a MEASUREMENT that RECORDS — it is NOT a pass/fail gate. It never
# asserts dominance and never exits nonzero on a regression; the perf-graphs
# review reads the recorded numbers. It exits nonzero only on real errors
# (missing exe/corpus, unparseable output). The dedicated CI gate this replaces
# was removed on this branch.
#
# Pinning: keep this script simple; bench/run.sh wraps it in bench/pin_core.sh
# so the whole process tree inherits one idle core, like the other measurement
# steps.
set -euo pipefail

CORPUS="${1:-}"
N="${2:-9}"
OUT="${3:-bench/results/whole_tar_l6.json}"

if [ -z "$CORPUS" ]; then
  echo "usage: bench/whole_tar_l6.sh <corpusDir> [N=9] [outJson=bench/results/whole_tar_l6.json]" >&2
  exit 2
fi
if [ ! -d "$CORPUS" ]; then
  echo "ERROR: corpus dir not found: $CORPUS" >&2
  exit 2
fi

# The 12 Silesia corpus files, in a fixed order. `tar --sort=name` sorts the
# members regardless, but list them explicitly so a missing file is caught here.
FILES=(dickens mozilla mr nci ooffice osdb reymont samba sao webster x-ray xml)
for f in "${FILES[@]}"; do
  if [ ! -f "$CORPUS/$f" ]; then
    echo "ERROR: corpus file missing: $CORPUS/$f" >&2
    exit 2
  fi
done

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
  echo "ERROR: could not find the built 'bench' exe (looked under $SCRIPT_DIR/.lake/build/bin)" >&2
  exit 2
fi

# Assemble a DETERMINISTIC silesia.tar in a temp dir (cleaned on exit). Same
# command the removed l6_tar_gate used — reuse it exactly for reproducibility.
TMPDIR_TAR="$(mktemp -d)"
cleanup() { rm -rf "$TMPDIR_TAR"; }
trap cleanup EXIT
TAR="$TMPDIR_TAR/silesia.tar"
tar --sort=name --owner=0 --group=0 --numeric-owner \
  --mtime='2020-01-01 00:00:00' \
  -cf "$TAR" -C "$CORPUS" "${FILES[@]}"

TAR_BYTES="$(wc -c < "$TAR")"

echo "== whole-tar L6 measurement (native vs miniz, cold) =="
echo "corpus  : $CORPUS"
echo "tar     : $TAR (${TAR_BYTES} B)"
echo "bench   : $BENCH"
echo "reps    : $N"
echo "out     : $OUT"
echo

# Parse `out=<n>` from a `size=... lvl=6: out=<n> ratio=...%` line.
parse_out() { awk 'match($0, /out=[0-9]+/) { print substr($0, RSTART+4, RLENGTH-4); exit }'; }

# --- sizes: one run of each, capture out-sizes ---
NATIVE_LINE="$("$BENCH" csize 0 "@$TAR" 6)"
MINIZ_LINE="$("$BENCH" compress-miniz 0 "@$TAR" 6)"
NATIVE_SIZE="$(printf '%s\n' "$NATIVE_LINE" | parse_out)"
MINIZ_SIZE="$(printf '%s\n' "$MINIZ_LINE"  | parse_out)"

if ! [[ "$NATIVE_SIZE" =~ ^[0-9]+$ ]] || ! [[ "$MINIZ_SIZE" =~ ^[0-9]+$ ]]; then
  echo "ERROR: could not parse out-sizes" >&2
  echo "  native line: $NATIVE_LINE" >&2
  echo "  miniz  line: $MINIZ_LINE" >&2
  exit 1
fi

SIZE_MARGIN="$(awk -v a="$NATIVE_SIZE" -v b="$MINIZ_SIZE" 'BEGIN{printf "%.4f", 100.0*(b-a)/b}')"
echo "size: native L6 out=$NATIVE_SIZE  miniz L6 out=$MINIZ_SIZE  (native ${SIZE_MARGIN}% smaller)"
echo

# nanosecond wall clock around a fresh subprocess.
run_native() { "$BENCH" csize 0 "@$TAR" 6 >/dev/null; }
run_miniz()  { "$BENCH" compress-miniz 0 "@$TAR" 6 >/dev/null; }
now() { date +%s.%N; }

echo "cold reps (native_ms / miniz_ms):"
printf "  %-4s %-12s %-12s %-8s %-6s\n" "rep" "native(ms)" "miniz(ms)" "ratio" "first"

NAT_MS=()
MIZ_MS=()
RATIOS=()
for ((i=1; i<=N; i++)); do
  # alternate ordering to cancel any first-mover cache/turbo bias.
  if (( i % 2 == 1 )); then
    t0="$(now)"; run_native; t1="$(now)"; run_miniz; t2="$(now)"
    nat="$(awk -v a="$t0" -v b="$t1" 'BEGIN{printf "%.3f", 1000.0*(b-a)}')"
    miz="$(awk -v a="$t1" -v b="$t2" 'BEGIN{printf "%.3f", 1000.0*(b-a)}')"
    first="nat"
  else
    t0="$(now)"; run_miniz; t1="$(now)"; run_native; t2="$(now)"
    miz="$(awk -v a="$t0" -v b="$t1" 'BEGIN{printf "%.3f", 1000.0*(b-a)}')"
    nat="$(awk -v a="$t1" -v b="$t2" 'BEGIN{printf "%.3f", 1000.0*(b-a)}')"
    first="miz"
  fi
  r="$(awk -v n="$nat" -v m="$miz" 'BEGIN{printf "%.4f", n/m}')"
  NAT_MS+=("$nat")
  MIZ_MS+=("$miz")
  RATIOS+=("$r")
  printf "  %-4s %-12s %-12s %-8s %-6s\n" "$i" "$nat" "$miz" "$r" "$first"
done
echo

# median + min of a list of floats (args), printed as "<min> <median>".
best_median() {
  printf '%s\n' "$@" | sort -n | awk '
    { v[NR]=$1 }
    END {
      n=NR
      if (n % 2 == 1) med = v[(n+1)/2]
      else            med = (v[n/2] + v[n/2+1]) / 2.0
      printf "%.3f %.3f", v[1], med
    }'
}

read -r NAT_BEST NAT_MED  <<<"$(best_median "${NAT_MS[@]}")"
read -r MIZ_BEST MIZ_MED  <<<"$(best_median "${MIZ_MS[@]}")"

# median of the per-rep ratios.
RATIO_MED="$(printf '%s\n' "${RATIOS[@]}" | sort -n | awk '
  { v[NR]=$1 }
  END {
    n=NR
    if (n % 2 == 1) print v[(n+1)/2]
    else            printf "%.4f", (v[n/2] + v[n/2+1]) / 2.0
  }')"

echo "native : size=$NATIVE_SIZE  ms_best=$NAT_BEST  ms_median=$NAT_MED"
echo "miniz  : size=$MINIZ_SIZE  ms_best=$MIZ_BEST  ms_median=$MIZ_MED"
echo "size_margin_pct=$SIZE_MARGIN  time_ratio_median=$RATIO_MED"
echo

# --- write JSON (meta style mirrors bench/results/latest.json) ---
DATE_UTC="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
MACHINE="$(uname -mns)"
GIT_COMMIT="$(git rev-parse --short HEAD 2>/dev/null || echo unknown)"
NOTE="cold single-shot best-of-${N} L6 whole silesia.tar (${TAR_BYTES} B); native vs miniz_oxide; ms are wall-clock of fresh subprocesses; time_ratio_median is median per-rep native_ms/miniz_ms (<1.0 = native cold-faster)"

mkdir -p "$(dirname "$OUT")"
cat > "$OUT" <<EOF
{
 "meta": {
  "date": "$DATE_UTC",
  "machine": "$MACHINE",
  "git_commit": "$GIT_COMMIT",
  "note": "$NOTE"
 },
 "native": {
  "size": $NATIVE_SIZE,
  "ms_best": $NAT_BEST,
  "ms_median": $NAT_MED
 },
 "miniz": {
  "size": $MINIZ_SIZE,
  "ms_best": $MIZ_BEST,
  "ms_median": $MIZ_MED
 },
 "size_margin_pct": $SIZE_MARGIN,
 "time_ratio_median": $RATIO_MED
}
EOF

echo "wrote $OUT"
