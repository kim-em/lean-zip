---
name: perf-pr-graphs
description: Produce before/after native speed-vs-ratio comparison graphs (against the other-language curves) and show them to Kim BEFORE merging. Use REQUIRED for any lean-zip performance PR (perf:/runtime/throughput change to compress or decode) once it is green and before it merges — Kim must see the graphs first. Most interesting for compression changes.
allowed-tools: Read, Write, Edit, Bash, Glob, Grep
---

# Pre-merge performance comparison graphs

## When this is mandatory

Any PR that changes runtime performance of the native path — anything titled
`perf:`, or any change to `Zip/Native/Deflate*`, `Zip/Native/Inflate*`,
`Zip/Native/LZ77*`, `Zip/Native/DeflateParse*`, the bit reader/writer, or the
Huffman codec. **Do not merge such a PR until you have generated these graphs
and Kim has seen them.** This is a required gate, not an optional nicety.

The graphs show **native before vs after** on the real corpora (Canterbury +
Silesia), overlaid on the existing other-language curves (zlib, miniz_oxide,
libdeflate, Go, JS, Zig, OCaml) for context. They are a **report artifact —
NOT committed** (the routine dashboard in `bench/graphs/*.svg` is regenerated
separately by `bench/run.sh`).

## Which metric

- **Compression PR → `compress_mbps`.** This is the interesting case: a
  compression change can move *both* the ratio and the speed, so the
  speed-vs-ratio Pareto frontier is the thing to read — does native shift up
  (faster at the same ratio) or right (worse ratio)?
- **Decompression PR → `decompress_mbps`.** Decode speed does not trade off
  against ratio, so this is just a throughput-vs-ratio scatter — still worth
  showing, but less rich than the compress view.
- A PR touching both: produce both sets.

## Workflow

Run from the repo root. On NixOS wrap commands in `nix-shell --run "…"` (see the
project `.claude/CLAUDE.md`); elsewhere run them directly.

1. **Confirm the machine matches the dashboard.** The overlay is only honest if
   you measure on the same machine the committed other-language numbers used:
   ```
   uname -mns
   python3 -c "import json;print(json.load(open('bench/results/latest.json'))['meta']['machine'])"
   ```
   If they differ, say so loudly in the report — the before/after delta is still
   valid (same machine), but native-vs-other-language positioning is not.

2. **Materialize the corpora.** Canterbury is committed; Silesia (~203 MB,
   gitignored) is fetched on demand:
   ```
   [ -d bench/corpora/silesia ] && [ -n "$(ls -A bench/corpora/silesia 2>/dev/null)" ] \
     || bash bench/fetch_corpora.sh silesia
   ```

3. **Measure AFTER** (the PR branch, already built):
   ```
   lake build bench-report
   lake env .lake/build/bin/bench-report --native-only /tmp/perf_after.json
   ```
   `--native-only` records native `ratio`, `compress_mbps` and
   `decompress_mbps` and reuses nothing else. For a **decode-only** PR, append a
   level list that skips the slow L9 optimal-parse compress, e.g.
   `… --native-only /tmp/perf_after.json 1,2,3,4,5,6,7,8` (decode is measured at
   every listed level; native L9 *compress* on 203 MB is minutes of pure waste
   when you only care about decode). For a **compress** PR, keep all 9 levels —
   L9 is usually the point.

4. **Measure BEFORE** (master's native path), without disturbing the branch:
   ```
   git fetch origin -q
   # swap in master's versions of ONLY the files this PR changed, e.g.:
   git checkout origin/master -- Zip/Native/Inflate.lean Zip/Spec/InflateBufCorrect.lean
   lake build bench-report
   lake env .lake/build/bin/bench-report --native-only /tmp/perf_before.json   # same level list as step 3
   git checkout HEAD -- Zip/Native/Inflate.lean Zip/Spec/InflateBufCorrect.lean # restore branch
   ```
   Use `git diff --name-only origin/master...HEAD` to see which files to swap.
   Always restore with `git checkout HEAD -- <files>` and confirm `git status`
   is clean afterwards.

5. **Plot** (other-language curves are reused from `latest.json`, never
   re-measured):
   ```
   python3 .claude/skills/perf-pr-graphs/plot_before_after.py \
     /tmp/perf_before.json /tmp/perf_after.json <compress_mbps|decompress_mbps>
   ```
   This writes `bench/graphs/perf_before_after_<metric>_<corpus>.{svg,png}`
   (UNCOMMITTED — they show as untracked; do not `git add` them to the perf PR)
   and prints a per-level before/after geomean table.

6. **Show Kim and wait.** Read the PNGs back so they render, present the
   before/after geomean tables and the per-corpus speedup, and **stop for Kim's
   go-ahead before merging.** State the metric, the machine, and any caveat
   (e.g. machine mismatch, levels skipped, ratio shift on a compress change).

## Notes

- `bench-report --native-only [levels]` lives in `ZipBenchReport.lean`; the plot
  styling mirrors `bench/plot.py` (same colours/markers) for visual continuity.
- The y-axis is log, so a +30% gain reads as a modest visual gap — quote the
  numeric speedup from the printed table, don't rely on the eye alone.
- For a compress PR, also call out any **ratio** change: a speed win that worsens
  the ratio (curve moves right) may not be a net win. zopfli's frozen ratio
  ceiling is in `bench/results/zopfli-ceiling.json` if you want the best-ratio
  reference.
- Keep the temporary jsons in `/tmp`; clean up swapped-in source files before
  finishing (`git status` must be clean on the PR branch).
