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

4. **Measure BEFORE** (the branch's native path *without this PR's commits*),
   without disturbing the branch. **Baseline against the branch's merge-base with
   master — NOT `origin/master` directly.** If the branch is behind master,
   swapping in `origin/master`'s files pulls in *unrelated* perf commits that
   touched the same files, so "before" ends up faster (or slower) for reasons that
   have nothing to do with this PR, and the graph shows a phantom regression. The
   merge-base is the exact point the branch diverged, so swapping its files
   isolates only this PR's changes.

   First check how stale the branch is, then swap in the merge-base versions of
   only the files this PR changed:
   ```
   git fetch origin -q
   base=$(git merge-base origin/master HEAD)
   behind=$(git rev-list --count HEAD..origin/master)
   [ "$behind" -gt 0 ] && echo "NOTE: branch is $behind commits behind master; \
baselining against merge-base ${base:0:8} (NOT origin/master) so unrelated \
commits don't leak into 'before'."
   # files this PR changed, relative to the divergence point:
   git diff --name-only "$base"...HEAD
   # swap ONLY those to their merge-base version, e.g.:
   git checkout "$base" -- Zip/Native/Inflate.lean Zip/Spec/InflateBufCorrect.lean
   lake build bench-report
   lake env .lake/build/bin/bench-report --native-only /tmp/perf_before.json   # same level list as step 3
   git checkout HEAD -- Zip/Native/Inflate.lean Zip/Spec/InflateBufCorrect.lean # restore branch
   ```
   Always restore with `git checkout HEAD -- <files>` and confirm `git status` is
   clean afterwards. (For a single-commit PR, `$base` and `HEAD~1` coincide.)

5. **Sanity-check before plotting.** Two independent checks — they catch
   different failures, so read both:
   - **Output-neutrality (`max |Δratio|`, printed by the plotter).** A PR that
     does not change *output* (a dispatch/escape, a re-timed loop, a proof-side
     refactor) **must** show `max |Δratio| = 0.000000`. A nonzero value means the
     change is not output-neutral after all (or, rarely, the two runs saw
     different corpora). A PR that *intends* to change the parse (better ratio)
     shows a nonzero Δratio — that is the point; confirm it moves the right way.
   - **Baseline correctness (the staleness guard from step 4).** Note that
     `max |Δratio|` does **not** catch a stale-branch baseline: if "before" leaked
     in an unrelated perf commit that touched the same files, both still produce
     identical output, so Δratio stays `0.000000` while the *speed* curve is
     silently wrong (this is the classic phantom regression — "before" looks
     faster than "after" for reasons unrelated to the PR). The only defence is
     step 4's `behind` check: if the branch was behind master and you baselined
     against `origin/master` instead of the merge-base, redo step 4.

6. **Plot** (other-language curves are reused from `latest.json`, never
   re-measured). The graphs are a report artifact — write them to the gitignored
   `/tmp` so they can never be accidentally committed to the perf PR:
   ```
   python3 .claude/skills/perf-pr-graphs/plot_before_after.py \
     /tmp/perf_before.json /tmp/perf_after.json <compress_mbps|decompress_mbps> \
     bench/results/latest.json /tmp
   ```
   This writes `/tmp/perf_before_after_<metric>_<corpus>.{svg,png}` and prints the
   per-level before/after geomean table plus `max |Δratio|`.

7. **Show Kim and wait.** Read the PNGs back so they render, present the
   before/after geomean tables and the per-corpus speedup, and **stop for Kim's
   go-ahead before merging.** State the metric, the machine, and any caveat
   (e.g. machine mismatch, levels skipped, ratio shift on a compress change).
   Quote the numeric speedup — the y-axis is log, so trust the table, not the eye
   (see Notes). **Canterbury is measured median-of-5 and is the row set to read
   for a speed verdict; Silesia is single-pass (`reps=1`), so its per-file MB/s
   carries ±30%+ run-to-run noise even on byte-identical code — use it for ratio
   and coverage, not for a fine speed delta.**

## Notes

- `bench-report --native-only [levels]` lives in `ZipBenchReport.lean`; the plot
  styling mirrors `bench/plot.py` (same colours/markers) for visual continuity.
- The y-axis is log, so a +30% gain reads as a modest visual gap — quote the
  numeric speedup from the printed table, don't rely on the eye alone.
- For a compress PR, also call out any **ratio** change: a speed win that worsens
  the ratio (curve moves right) may not be a net win. zopfli's frozen ratio
  ceiling is in `bench/results/zopfli-ceiling.json` if you want the best-ratio
  reference.
- Keep the temporary jsons and graphs in `/tmp`; restore any swapped-in source
  files before finishing (`git status` must be clean on the PR branch — a leftover
  merge-base checkout or a stray graph under `bench/graphs/` is a real footgun).
