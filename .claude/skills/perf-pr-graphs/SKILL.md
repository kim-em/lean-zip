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

4. **Measure BEFORE** (the branch's native path *without this PR's commits*).
   **Build it in a throwaway worktree checked out at the branch's merge-base with
   master — NOT at `origin/master`, and NOT by swapping files in place.**

   Why the merge-base, not `origin/master`: if the branch is behind master,
   `origin/master` carries *unrelated* perf commits; any touching a file this PR
   also touches leak into "before" — a phantom regression on the speed curve. The
   merge-base is the exact divergence point: master-minus-the-PR with no extra
   commits.

   Why a worktree, not `git checkout <base> -- <files>`: the in-place swap forces
   you to guess which files the PR changed (miss a support module, build file,
   generated table, or rename/delete and "before" is a hybrid of HEAD code against
   base code), and leaves the main worktree's build artifacts stale. A clean
   worktree at `$base` is the whole tree at the divergence point:
   ```
   git fetch origin -q
   base=$(git merge-base origin/master HEAD)
   behind=$(git rev-list --count HEAD..origin/master)
   [ "$behind" -gt 0 ] && echo "NOTE: branch is $behind commits behind master; \
baselining BEFORE at merge-base ${base:0:8} (not origin/master) so unrelated \
commits don't leak in."
   tmp="/tmp/perf-before-${base:0:8}"
   git worktree add --detach "$tmp" "$base"
   ( cd "$tmp" && lake build bench-report \
       && lake env .lake/build/bin/bench-report --native-only /tmp/perf_before.json )  # same level list as step 3
   git worktree remove --force "$tmp"
   ```
   `bench-report` stamps the JSON `meta.git_commit` from the worktree's HEAD, so
   `/tmp/perf_before.json`'s commit should equal `$base` — the plotter prints it
   (step 6) for you to confirm. On NixOS the inner `cd` changes the nix-shell
   working dir; run the whole `( … )` inside one `nix-shell --run "…"`.

5. **Sanity-check before plotting.** Two independent checks — they catch
   different failures, so read both:
   - **Output-neutrality (`max |Δratio|`, printed by the plotter).** A PR that
     does not change *output* (a dispatch/escape, a re-timed loop, a proof-side
     refactor) **must** show `max |Δratio| = 0.000000`. A nonzero value means the
     change is not output-neutral after all (or, rarely, the two runs saw
     different corpora). A PR that *intends* to change the parse (better ratio)
     shows a nonzero Δratio — that is the point; confirm it moves the right way.
   - **Baseline correctness.** `max |Δratio|` does **not** catch a stale-branch
     baseline: if "before" leaked in an unrelated perf commit that touched the
     same files, both still produce identical output, so Δratio stays `0.000000`
     while the *speed* curve is silently wrong (the classic phantom regression —
     "before" looks faster than "after" for reasons unrelated to the PR). The
     defences are the merge-base worktree (step 4, which makes a hybrid tree
     impossible) plus the commit/coverage line the plotter prints: confirm
     BEFORE's `meta.git_commit` equals `$base` and that before/after cover the
     same `(pattern, level)` rows. If BEFORE's commit is `origin/master` rather
     than the merge-base, redo step 4.

6. **Plot** (other-language curves are reused from `latest.json`, never
   re-measured). The graphs are a report artifact — write them to the gitignored
   `/tmp` so they can never be accidentally committed to the perf PR:
   ```
   python3 .claude/skills/perf-pr-graphs/plot_before_after.py \
     /tmp/perf_before.json /tmp/perf_after.json <compress_mbps|decompress_mbps> \
     bench/results/latest.json /tmp
   ```
   This writes `/tmp/perf_before_after_<metric>_<corpus>.{svg,png}` and prints the
   before/after `meta` (machine + git_commit of each run), a row-coverage line
   (any `(pattern, level)` present in one run but not the other), the per-level
   before/after geomean table, and `max |Δratio|`.

7. **Show Kim and wait.** Read the PNGs back so they render, present the
   before/after geomean tables and the per-corpus speedup, and **stop for Kim's
   go-ahead before merging.** State the metric, the machine, and any caveat
   (e.g. machine mismatch, levels skipped, ratio shift on a compress change).
   Quote the numeric speedup — the y-axis is log, so trust the table, not the eye
   (see Notes). **Canterbury is measured median-of-5 and is the row set to read
   for a speed verdict; Silesia is single-pass (`reps=1`), so its per-file MB/s
   carries ±30%+ run-to-run noise even on byte-identical code — use it for ratio
   and coverage, not for a fine speed delta.**

8. **Also post the graphs as a PR comment.** The PNGs otherwise live only in
   `/tmp` — so a session Kim was not watching (or that she reads later) leaves
   her nothing to look at. Make the artifact durable and async-visible by
   embedding the before/after PNGs in a `gh pr comment`, alongside the geomean
   table and the metric/machine/caveat line from step 7. This is in addition to
   the interactive show-and-wait, not a replacement for it.

   `gh` cannot attach images to a comment directly, and the PNGs must **not** be
   committed to the perf PR (step 6 keeps them out of the diff) or to `master`.
   Host them on a dedicated throwaway branch and link the raw URLs — the same
   pattern issue #2634's close comment used:
   ```
   pr=<N>; sha=$(git rev-parse HEAD)
   branch="perf-graphs/pr-${pr}"
   # commit ONLY the PNGs onto a scratch branch, off the PR and off master
   git switch -c "$branch" 2>/dev/null || git switch "$branch"
   mkdir -p perf-graphs && cp /tmp/perf_before_after_*.png perf-graphs/
   git add perf-graphs && git commit -q -m "perf graphs for PR #${pr}"
   git push -u origin "$branch" -q
   gsha=$(git rev-parse HEAD)
   git switch -  # back to the PR branch; leave its diff untouched
   raw="https://raw.githubusercontent.com/kim-em/lean-zip/${gsha}/perf-graphs"
   gh pr comment "$pr" --body "Before/after \`<metric>\` (machine \`<m>\`; <caveat>):

   ![compress pareto](${raw}/perf_before_after_compress_mbps_silesia.png)

   <geomean table>"
   ```
   Pin the raw URL to the pushed commit SHA (`${gsha}`), not a branch name, so the
   image keeps rendering even if the branch is later updated or deleted. Confirm
   the PR branch's own `git status` is still clean afterward (step 6 footgun).

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
