---
name: perf-pr-graphs
description: Produce before/after native speed-vs-ratio comparison graphs (against the other-language curves) and show them to Kim BEFORE merging. Use REQUIRED for any lean-zip performance PR (perf:/runtime/throughput change to compress or decode) once it is green and before it merges — Kim must see the graphs first. Most interesting for compression changes.
allowed-tools: Read, Write, Edit, Bash, Glob, Grep
---

# Pre-merge performance comparison graphs

## TL;DR — this is compulsory, in this exact order

For **every** native-performance PR (see the trigger list below), you **must**,
once the PR is green and before it merges:

1. **Generate** the before/after comparison graphs (steps 1–6). This is not
   optional and not "if Kim asks" — it is automatic for every qualifying PR.
   Never skip it, never ask whether to do it, never merge without it.
2. **Look** at the rendered graphs yourself (step 7) — `Read` the PNGs as images,
   do not reason only from the numeric table.
3. **Post** the graphs as a PR comment with the geomean table and caveats
   (step 8). The `/tmp` PNGs are not durable; the PR comment is the artifact.
4. **Give Kim the link** to that PR comment in your reply, and stop for her
   go-ahead before merging.

If you generated graphs but did not look at them, did not post them, or did not
hand Kim a link, you are **not done** — finish steps 2–4.

## When this is mandatory

Any PR that changes runtime performance of the native path — anything titled
`perf:`, or any change to `Zip/Native/Deflate*`, `Zip/Native/Inflate*`,
`Zip/Native/LZ77*`, `Zip/Native/DeflateParse*`, the bit reader/writer, or the
Huffman codec. **Do not merge such a PR until you have generated these graphs,
posted them to the PR, and Kim has seen them.** This is a required gate, not an
optional nicety.

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

4. **BEFORE is `bench/results/latest.json` — do NOT rebuild it.** Master already
   carries up-to-date native numbers: `bench/results/latest.json` is the
   committed dashboard snapshot (native `ratio` / `compress_mbps` /
   `decompress_mbps`, median-of-5 on Canterbury, same machine), and it is the
   canonical BEFORE. There is **no merge-base worktree build** — that whole step
   was wasted work, because the data it would reproduce is already recorded in
   the tree. Pass `bench/results/latest.json` straight to the plotter as BEFORE
   (step 6).

   **The invariant that makes this valid: `latest.json` must always reflect the
   current native path on master.** It is kept current by the "bench: dashboard
   refresh" commits — every native-perf PR is followed by a dashboard refresh
   that re-records `latest.json`. If a native-perf change ever merges *without*
   that refresh, master's recorded BEFORE goes stale and every subsequent perf PR
   baselines against the wrong code. So keep the dashboard fresh, and run the
   freshness guard below before trusting it.

   **Freshness guard (run it, every time).** Confirm no native-path commit landed
   between the snapshot's recorded commit and this branch's merge-base — if one
   did, `latest.json` predates code your BEFORE must include, and it is stale:
   ```
   git fetch origin -q
   base=$(git merge-base origin/master HEAD)
   rec=$(python3 -c "import json;print(json.load(open('bench/results/latest.json'))['meta']['git_commit'])")
   # native CODE paths only — a `bench/` change (a dashboard refresh, the very
   # commit that re-recorded latest.json) does NOT invalidate the native baseline.
   stale=$(git log --oneline ${rec}..${base} -- Zip/Native ZipCommon 2>/dev/null)
   [ -n "$stale" ] && echo "STALE latest.json (recorded at ${rec}); native commits since:" && echo "$stale"
   ```
   - **Empty → use `latest.json` as BEFORE.** Its native rows already reflect the
     merge-base; nothing to rebuild.
   - **Non-empty → `latest.json` is stale; the dashboard was not refreshed after
     a native merge.** Fix the invariant rather than working around it:
     regenerate it (`bash bench/run.sh`, commit the refreshed
     `bench/results/latest.json`, ideally as its own `bench: dashboard refresh`
     PR) so master is current again, then use it. Only if you genuinely cannot
     refresh now, fall back to a one-off merge-base build as a documented
     workaround (`git worktree add --detach /tmp/before $base && ( cd /tmp/before
     && lake build bench-report && lake env .lake/build/bin/bench-report
     --native-only /tmp/perf_before.json )`, then `git worktree remove --force
     /tmp/before`) and pass `/tmp/perf_before.json` as BEFORE.

   **Cross-session caveat.** BEFORE (recorded earlier) and AFTER (measured now)
   are different sessions, so a small single-digit-% speed delta can be
   cross-session / machine-load noise rather than the PR. Before reading a fine
   speed verdict, make the AFTER run on a quiet machine (no competing `lake`
   builds — check `uptime` / `ps` first), and weight Canterbury's median-of-5
   over Silesia's single pass.

5. **Sanity-check before plotting.** Two independent checks — they catch
   different failures, so read both:
   - **Output-neutrality (`max |Δratio|`, printed by the plotter).** A PR that
     does not change *output* (a dispatch/escape, a re-timed loop, a proof-side
     refactor) **must** show `max |Δratio| = 0.000000`. A nonzero value means the
     change is not output-neutral after all (or, rarely, the two runs saw
     different corpora). A PR that *intends* to change the parse (better ratio)
     shows a nonzero Δratio — that is the point; confirm it moves the right way.
   - **Baseline currency.** The freshness guard in step 4 is what keeps the
     baseline honest now that BEFORE is `latest.json`: if it flagged stale, a
     native commit landed after the snapshot and the *speed* curve would be
     silently wrong even though Δratio stays `0.000000` (the classic phantom
     regression — "before" reflects different code than the merge-base). Confirm
     the guard came back empty, and confirm the plotter's printed BEFORE
     `meta.git_commit` is the snapshot you expect and that before/after cover the
     same `(pattern, level)` rows.

6. **Plot** (other-language curves are reused from `latest.json`, never
   re-measured). The graphs are a report artifact — write them to the gitignored
   `/tmp` so they can never be accidentally committed to the perf PR:
   `<before.json>` is `bench/results/latest.json` (step 4) — pass it twice, once
   as BEFORE and once as the reused other-language source:
   ```
   python3 .claude/skills/perf-pr-graphs/plot_before_after.py \
     bench/results/latest.json /tmp/perf_after.json <compress_mbps|decompress_mbps> \
     bench/results/latest.json /tmp
   ```
   This writes `/tmp/perf_before_after_<metric>_<corpus>.{svg,png}` and prints the
   before/after `meta` (machine + git_commit of each run), a row-coverage line
   (any `(pattern, level)` present in one run but not the other), the per-level
   before/after geomean table, and `max |Δratio|`.

7. **Actually LOOK at the graphs, then show Kim and wait.** This means
   `Read`-ing the PNG files so they render as images in your context and visually
   inspecting them — **not** reading the SVG as text and **not** reasoning only
   from the numeric geomean table. The table gives you the per-level delta; the
   picture gives you what the table cannot — where the native before/after curves
   sit *relative to the other-language curves* (is lean-zip in the fast cluster or
   the slow one? which engines, if any, does this PR move us past?), whether
   before/after visibly separate or sit on top of each other, and whether any
   point is an obvious outlier. A reviewer who only quotes the table has not done
   step 7.
   ```
   # render BOTH corpora as images and look at them — required, not optional
   Read /tmp/perf_before_after_<metric>_canterbury.png
   Read /tmp/perf_before_after_<metric>_silesia.png
   ```
   Present the before/after geomean tables, the per-corpus speedup, **and your
   visual read of where native lands among the other languages**, then **stop for
   Kim's go-ahead before merging.** State the metric, the machine, and any caveat
   (machine mismatch, levels skipped, ratio shift on a compress change, a noisy
   AFTER run). Quote the numeric speedup — the y-axis is log, so trust the table
   for the *magnitude* and the picture for the *positioning*. **Canterbury is
   measured median-of-5 and is the row set to read for a speed verdict; Silesia is
   single-pass (`reps=1`), so its per-file MB/s carries ±30%+ run-to-run noise
   even on byte-identical code — use it for ratio and coverage, not for a fine
   speed delta.**

8. **Always post the graphs as a PR comment — then give Kim the link.** This step
   is compulsory, not "also if convenient": every qualifying PR gets a PR comment
   with the graphs, and your reply to Kim must contain the URL of that comment
   (`gh pr comment` prints it on success — capture it) so she can click straight
   to it. The PNGs otherwise live only in `/tmp` — so a session Kim was not
   watching (or that she reads later) leaves her nothing to look at. Make the
   artifact durable and async-visible by embedding the before/after PNGs in a
   `gh pr comment`, alongside the geomean table and the metric/machine/caveat line
   from step 7. This is in addition to the interactive show-and-wait, not a
   replacement for it.

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
- Keep the temporary jsons and graphs in `/tmp`; `git status` must be clean on
  the PR branch before finishing — a stray graph under `bench/graphs/`, or (if you
  used the step-4 stale fallback) a leftover `git worktree`, is a real footgun.
