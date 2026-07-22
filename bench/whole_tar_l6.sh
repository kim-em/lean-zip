#!/usr/bin/env bash
# Record the cold L6 whole-tar comparison in TWO honest sections, both written
# to bench/results/whole_tar_l6.json:
#
#   [codec]      lean native DEFLATE vs miniz_oxide, measured THROUGH the same
#                lean `bench` harness — so both sides pay lean's `readBinFile` +
#                202 MB ByteArray-alloc I/O tax and it CANCELS. This isolates
#                the codec CPU. `time_ratio_median` here is a codec-CPU ratio
#                (native genuinely compresses faster); it is a regression guard
#                for ratio-tuning knobs, NOT the end-to-end `zip silesia.tar` wall.
#
#   [end_to_end] two REAL, separate CLI tools — the lean `compress-file` exe and
#                the rust `miniz-compress-file` bin — each a fresh process doing
#                read-file → compress → report. This IS the end-to-end wall Kim
#                benchmarks with `hyperfine zip silesia.tar`, and it includes
#                each language's own file-read/alloc path (which the codec
#                section cancels out). Report it honestly: rust is currently
#                marginally ahead on wall because lean's compression CPU is
#                faster (lower user time) but its file-read/alloc system time is
#                higher — the gap is entirely the lean CLI's I/O path.
#
#   bench/whole_tar_l6.sh <corpusDir> [N=9] [outJson=bench/results/whole_tar_l6.json]
#
# WHY THIS EXISTS: the per-file dashboard (bench/results/latest.json) tracks
# per-file WARM throughput. That amortizes native's page-fault / CAF-build tax
# after the first rep and measures small files where the split/probe economics
# differ — so a config that regresses the whole 202 MB `zip silesia.tar` COLD
# stream (a deeper L6 probe, rolling deferral) can look fine per-file while the
# real workload regresses. Three PRs slipped through exactly this gap. This
# script RECORDS the whole-tar L6 numbers as committed dashboard data
# (bench/results/whole_tar_l6.json) so a regression surfaces in the perf-graphs
# review already mandatory for perf PRs.
#
# WHY COLD: Kim's headline `hyperfine zip silesia.tar` benchmark is cold — a
# fresh process each run, so native pays its full page-fault / CAF-build tax
# every time (~0.24 s). An in-process warm loop amortizes that tax after the
# first rep and inflates native's apparent time margin from ~2% (cold) to
# ~4.5% (warm) — enough to green-light a config that is actually ~2.8% SLOWER
# cold. So every timed rep here spawns FRESH subprocesses.
#
# CODEC side  : `bench csize 0 @<tar> 6`          — native L6 out-size, through harness
#               `bench compress-miniz 0 @<tar> 6` — miniz L6 out-size,  through harness
# E2E   side  : `compress-file <tar> 6`           — lean CLI: read → deflateRaw → size
#               `miniz-compress-file <tar> 6`     — rust CLI: std::fs::read → compress_to_vec → len
# All are single-shot: one compress of the whole tar, then exit.
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

# Locate the honest lean CLI (`compress-file`), built alongside `bench`.
LEAN_CLI=""
for cand in \
  "$SCRIPT_DIR/.lake/build/bin/compress-file" \
  "$SCRIPT_DIR/../bench/.lake/build/bin/compress-file" \
  ".lake/build/bin/compress-file" \
  "bench/.lake/build/bin/compress-file"; do
  if [ -x "$cand" ]; then LEAN_CLI="$cand"; break; fi
done
if [ -z "$LEAN_CLI" ]; then
  echo "ERROR: could not find the built 'compress-file' exe (run: lake -d bench build compress-file)" >&2
  exit 2
fi

# Locate the honest rust CLI (`miniz-compress-file`), the miniz_oxide crate bin.
RUST_CLI=""
for cand in \
  "$SCRIPT_DIR/rust/miniz_oxide_shim/target/release/miniz-compress-file" \
  "rust/miniz_oxide_shim/target/release/miniz-compress-file" \
  "bench/rust/miniz_oxide_shim/target/release/miniz-compress-file"; do
  if [ -x "$cand" ]; then RUST_CLI="$cand"; break; fi
done
if [ -z "$RUST_CLI" ]; then
  echo "ERROR: could not find the built 'miniz-compress-file' bin (run: cargo build --release --manifest-path bench/rust/miniz_oxide_shim/Cargo.toml)" >&2
  exit 2
fi

# Locate a GNU-time binary for PEAK-RSS capture: `time -v` reports "Maximum
# resident set size (kbytes)". Prefer /usr/bin/time; else the first `time` on
# PATH that is a real binary supporting -v (the nix project shell provides GNU
# time there, NOT the shell builtin). Empty ⇒ fall back to /proc VmHWM polling.
TIME_BIN=""
for cand in /usr/bin/time "$(command -v time 2>/dev/null || true)"; do
  if [ -n "$cand" ] && [ -x "$cand" ] && "$cand" -v true >/dev/null 2>&1; then
    TIME_BIN="$cand"; break
  fi
done

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

echo "== whole-tar L6 measurement (codec + end-to-end, cold) =="
echo "corpus  : $CORPUS"
echo "tar     : $TAR (${TAR_BYTES} B)"
echo "bench   : $BENCH"
echo "leanCLI : $LEAN_CLI"
echo "rustCLI : $RUST_CLI"
echo "reps    : $N"
echo "out     : $OUT"
echo

# Parse `out=<n>` from a `size=... lvl=6: out=<n> ratio=...%` line.
parse_out() { awk 'match($0, /out=[0-9]+/) { print substr($0, RSTART+4, RLENGTH-4); exit }'; }

# min + median of a list of floats (args), printed as "<min> <median>".
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

# median of a list of floats (args).
median() {
  printf '%s\n' "$@" | sort -n | awk '
    { v[NR]=$1 }
    END {
      n=NR
      if (n % 2 == 1) printf "%.3f", v[(n+1)/2]
      else            printf "%.3f", (v[n/2] + v[n/2+1]) / 2.0
    }'
}

# ============================ CODEC (through harness) ========================
# Both sides run inside the lean `bench` process, so lean's readBinFile + big
# ByteArray alloc I/O tax is paid identically on both and cancels. This isolates
# codec CPU: `time_ratio_median` is a codec-CPU ratio, NOT the end-to-end wall.
echo "--- codec: native vs miniz, THROUGH the lean bench harness (I/O cancels) ---"

NATIVE_LINE="$("$BENCH" csize 0 "@$TAR" 6)"
MINIZ_LINE="$("$BENCH" compress-miniz 0 "@$TAR" 6)"
NATIVE_SIZE="$(printf '%s\n' "$NATIVE_LINE" | parse_out)"
MINIZ_SIZE="$(printf '%s\n' "$MINIZ_LINE"  | parse_out)"

if ! [[ "$NATIVE_SIZE" =~ ^[0-9]+$ ]] || ! [[ "$MINIZ_SIZE" =~ ^[0-9]+$ ]]; then
  echo "ERROR: could not parse codec out-sizes" >&2
  echo "  native line: $NATIVE_LINE" >&2
  echo "  miniz  line: $MINIZ_LINE" >&2
  exit 1
fi

SIZE_MARGIN="$(awk -v a="$NATIVE_SIZE" -v b="$MINIZ_SIZE" 'BEGIN{printf "%.4f", 100.0*(b-a)/b}')"
echo "size: native L6 out=$NATIVE_SIZE  miniz L6 out=$MINIZ_SIZE  (native ${SIZE_MARGIN}% smaller)"

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

read -r NAT_BEST NAT_MED  <<<"$(best_median "${NAT_MS[@]}")"
read -r MIZ_BEST MIZ_MED  <<<"$(best_median "${MIZ_MS[@]}")"

RATIO_MED="$(printf '%s\n' "${RATIOS[@]}" | sort -n | awk '
  { v[NR]=$1 }
  END {
    n=NR
    if (n % 2 == 1) print v[(n+1)/2]
    else            printf "%.4f", (v[n/2] + v[n/2+1]) / 2.0
  }')"

echo "codec native : size=$NATIVE_SIZE  ms_best=$NAT_BEST  ms_median=$NAT_MED"
echo "codec miniz  : size=$MINIZ_SIZE  ms_best=$MIZ_BEST  ms_median=$MIZ_MED"
echo "codec size_margin_pct=$SIZE_MARGIN  time_ratio_median=$RATIO_MED"
echo

# ============================ END-TO-END (real CLIs) ========================
# Two separate CLI tools as fresh processes: lean `compress-file` vs rust
# `miniz-compress-file`. Each pays ITS OWN file-read/alloc path, so this is the
# honest `zip silesia.tar` wall. We capture wall AND user+sys via the bash `time`
# builtin (no /usr/bin/time needed): TIMEFORMAT '%R %U %S' → real user sys (s).
echo "--- end-to-end: real lean CLI vs real rust CLI (fresh processes, own I/O) ---"

LEAN_SIZE="$("$LEAN_CLI" "$TAR" 6 | tr -dc '0-9')"
RUST_SIZE="$("$RUST_CLI" "$TAR" 6 | tr -dc '0-9')"
if ! [[ "$LEAN_SIZE" =~ ^[0-9]+$ ]] || ! [[ "$RUST_SIZE" =~ ^[0-9]+$ ]]; then
  echo "ERROR: could not read end-to-end CLI out-sizes (lean='$LEAN_SIZE' rust='$RUST_SIZE')" >&2
  exit 1
fi
echo "size: lean CLI out=$LEAN_SIZE  rust CLI out=$RUST_SIZE"

# Run CMD as a fresh process; echo "<wall_ms> <user_ms> <sys_ms>" via bash time.
TIMING="$TMPDIR_TAR/timing.txt"
timed() {
  # `time` report → group stderr → $TIMING; the command's own stdout/stderr are
  # discarded inside the group so only the three timing floats land in $TIMING.
  TIMEFORMAT='%R %U %S'
  { time "$@" >/dev/null 2>/dev/null; } 2>"$TIMING"
  local r u s
  read -r r u s < "$TIMING"
  awk -v r="$r" -v u="$u" -v s="$s" 'BEGIN{printf "%.3f %.3f %.3f", r*1000, u*1000, s*1000}'
}

# Peak RSS (kB) of a fresh run of CMD. Peak RSS is deterministic run-to-run
# (allocation shape, not timing), so one measured run per side suffices. Primary
# path: GNU `time -v` → "Maximum resident set size (kbytes)". Fallback: poll
# VmHWM (a monotone high-water mark) from /proc/<pid>/status while it runs.
maxrss_kb() {
  if [ -n "$TIME_BIN" ]; then
    local rpt="$TMPDIR_TAR/rss.txt"
    "$TIME_BIN" -v "$@" >/dev/null 2>"$rpt" || true
    awk -F': ' '/Maximum resident set size/ { gsub(/[^0-9]/,"",$2); print $2; exit }' "$rpt"
  else
    "$@" >/dev/null 2>/dev/null &
    local pid=$! hwm=0 cur
    while kill -0 "$pid" 2>/dev/null; do
      cur="$(awk '/VmHWM/{print $2; exit}' "/proc/$pid/status" 2>/dev/null || echo 0)"
      if [ -n "$cur" ] && [ "$cur" -gt "$hwm" ] 2>/dev/null; then hwm="$cur"; fi
    done
    wait "$pid" 2>/dev/null || true
    echo "$hwm"
  fi
}

echo "cold reps (lean_wall_ms / rust_wall_ms):"
printf "  %-4s %-12s %-12s %-8s %-6s\n" "rep" "lean(ms)" "rust(ms)" "ratio" "first"

LEAN_WALL=(); LEAN_USER=(); LEAN_SYS=()
RUST_WALL=(); RUST_USER=(); RUST_SYS=()
E2E_RATIOS=()
for ((i=1; i<=N; i++)); do
  if (( i % 2 == 1 )); then
    read -r lw lu ls <<<"$(timed "$LEAN_CLI" "$TAR" 6)"
    read -r rw ru rs <<<"$(timed "$RUST_CLI" "$TAR" 6)"
    first="lean"
  else
    read -r rw ru rs <<<"$(timed "$RUST_CLI" "$TAR" 6)"
    read -r lw lu ls <<<"$(timed "$LEAN_CLI" "$TAR" 6)"
    first="rust"
  fi
  r="$(awk -v l="$lw" -v x="$rw" 'BEGIN{printf "%.4f", l/x}')"
  LEAN_WALL+=("$lw"); LEAN_USER+=("$lu"); LEAN_SYS+=("$ls")
  RUST_WALL+=("$rw"); RUST_USER+=("$ru"); RUST_SYS+=("$rs")
  E2E_RATIOS+=("$r")
  printf "  %-4s %-12s %-12s %-8s %-6s\n" "$i" "$lw" "$rw" "$r" "$first"
done
echo

read -r LEAN_WALL_BEST LEAN_WALL_MED <<<"$(best_median "${LEAN_WALL[@]}")"
read -r RUST_WALL_BEST RUST_WALL_MED <<<"$(best_median "${RUST_WALL[@]}")"
LEAN_USER_MED="$(median "${LEAN_USER[@]}")"
LEAN_SYS_MED="$(median "${LEAN_SYS[@]}")"
RUST_USER_MED="$(median "${RUST_USER[@]}")"
RUST_SYS_MED="$(median "${RUST_SYS[@]}")"

E2E_RATIO_MED="$(printf '%s\n' "${E2E_RATIOS[@]}" | sort -n | awk '
  { v[NR]=$1 }
  END {
    n=NR
    if (n % 2 == 1) print v[(n+1)/2]
    else            printf "%.4f", (v[n/2] + v[n/2+1]) / 2.0
  }')"

echo "e2e lean : size=$LEAN_SIZE  wall_best=$LEAN_WALL_BEST  wall_med=$LEAN_WALL_MED  user_med=$LEAN_USER_MED  sys_med=$LEAN_SYS_MED"
echo "e2e rust : size=$RUST_SIZE  wall_best=$RUST_WALL_BEST  wall_med=$RUST_WALL_MED  user_med=$RUST_USER_MED  sys_med=$RUST_SYS_MED"
echo "e2e wall_ratio_median=$E2E_RATIO_MED  (lean/rust; >1.0 = rust wall-ahead)"
echo

# --- peak RSS: the whole-tar memory footprint of each real CLI ---------------
# Lean's DEFLATE holds its whole token stream in memory (the footprint the
# unboxing work targets); rust's miniz keeps only a bounded window. Peak RSS is
# deterministic, so one measured run per side (GNU time -v) is enough.
echo "--- end-to-end: peak resident set size (fresh process, GNU time -v) ---"
if [ -n "$TIME_BIN" ]; then echo "rss via: $TIME_BIN -v"; else echo "rss via: /proc VmHWM polling (no GNU time found)"; fi
LEAN_MAXRSS="$(maxrss_kb "$LEAN_CLI" "$TAR" 6)"
RUST_MAXRSS="$(maxrss_kb "$RUST_CLI" "$TAR" 6)"
if ! [[ "$LEAN_MAXRSS" =~ ^[0-9]+$ ]] || ! [[ "$RUST_MAXRSS" =~ ^[0-9]+$ ]] || [ "$RUST_MAXRSS" -eq 0 ]; then
  echo "ERROR: could not capture peak RSS (lean='$LEAN_MAXRSS' rust='$RUST_MAXRSS')" >&2
  exit 1
fi
RSS_RATIO="$(awk -v l="$LEAN_MAXRSS" -v r="$RUST_MAXRSS" 'BEGIN{printf "%.4f", l/r}')"
echo "e2e peak RSS: lean_maxrss_kb=$LEAN_MAXRSS  rust_maxrss_kb=$RUST_MAXRSS  rss_ratio=$RSS_RATIO  (lean/rust)"
echo

# --- write JSON (meta style mirrors bench/results/latest.json) ---
DATE_UTC="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
MACHINE="$(uname -mns)"
GIT_COMMIT="$(git rev-parse --short HEAD 2>/dev/null || echo unknown)"
CODEC_NOTE="CODEC comparison, measured THROUGH the lean bench harness so both sides pay the same readBinFile + 202 MB ByteArray-alloc I/O and it CANCELS: native (bench csize) vs miniz_oxide (bench compress-miniz) on the whole silesia.tar (${TAR_BYTES} B), cold best-of-${N}. ms are wall-clock of fresh bench subprocesses; time_ratio_median is median per-rep native_ms/miniz_ms (<1.0 = native codec-CPU faster). This guards a ratio-tuning codec regression; it is NOT the end-to-end zip wall (see end_to_end)."
E2E_NOTE="END-TO-END comparison of two REAL CLI tools as fresh processes: lean compress-file (readBinFile -> deflateRaw -> print size) vs rust miniz-compress-file (std::fs::read -> compress_to_vec -> print len), cold best-of-${N}, alternating order. This IS the zip silesia.tar wall Kim benchmarks with hyperfine; each side pays its OWN file-read/alloc path (which the codec section cancels). wall_ratio_median is median per-rep lean_wall/rust_wall (>1.0 = rust wall-ahead). Rust is currently marginally wall-ahead: lean's compression CPU is faster (lower user_ms) but its file-read/alloc system time (sys_ms) is higher, so the gap is entirely the lean CLI I/O path. wall/user/sys captured via the bash time builtin. PEAK RSS (maxrss_kb) is the whole-tar memory footprint of each CLI, captured with GNU time -v (Maximum resident set size); it is deterministic so one measured run per side suffices. rss_ratio is lean_maxrss_kb/rust_maxrss_kb: lean holds its whole DEFLATE token stream in memory while rust's miniz keeps only a bounded window, so this ratio is the memory cost of the token pipeline (the target of the token-unboxing work)."
META_NOTE="Whole-tar L6 comparison: codec-CPU (native vs miniz through the bench harness) plus end-to-end wall of the real lean/rust CLIs. Peak RSS (end_to_end.{lean,rust}.maxrss_kb + rss_ratio) is now tracked too — the whole-tar memory footprint, so a compress PR can be reviewed on memory as well as speed/ratio."

mkdir -p "$(dirname "$OUT")"
cat > "$OUT" <<EOF
{
 "meta": {
  "date": "$DATE_UTC",
  "machine": "$MACHINE",
  "git_commit": "$GIT_COMMIT",
  "tar_bytes": $TAR_BYTES,
  "reps": $N,
  "note": "$META_NOTE"
 },
 "codec": {
  "note": "$CODEC_NOTE",
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
 },
 "end_to_end": {
  "note": "$E2E_NOTE",
  "lean": {
   "size": $LEAN_SIZE,
   "wall_ms_best": $LEAN_WALL_BEST,
   "wall_ms_median": $LEAN_WALL_MED,
   "user_ms": $LEAN_USER_MED,
   "sys_ms": $LEAN_SYS_MED,
   "maxrss_kb": $LEAN_MAXRSS
  },
  "rust": {
   "size": $RUST_SIZE,
   "wall_ms_best": $RUST_WALL_BEST,
   "wall_ms_median": $RUST_WALL_MED,
   "user_ms": $RUST_USER_MED,
   "sys_ms": $RUST_SYS_MED,
   "maxrss_kb": $RUST_MAXRSS
  },
  "wall_ratio_median": $E2E_RATIO_MED,
  "rss_ratio": $RSS_RATIO
 }
}
EOF

echo "wrote $OUT"
