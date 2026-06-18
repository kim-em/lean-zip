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
3. **Refresh the dashboard inside this same PR** (step 8): re-record
   `bench/results/latest.json` and `bench/graphs/*.svg` with the AFTER numbers and
   commit them as part of *this* PR's diff. **Kim does not want a follow-up
   "bench: dashboard refresh" PR** — the performance data must be updated within
   the PR that makes the change. A perf PR that does not also refresh the
   dashboard is incomplete.
4. **Post** the graphs as a PR comment with the geomean table and caveats
   (step 9). The `/tmp` PNGs are not durable; the PR comment is the artifact.
5. **Give Kim the link** to that PR comment in your reply, and stop for her
   go-ahead before merging.

If you generated graphs but did not look at them, did not refresh the dashboard
in-PR, did not post them, or did not hand Kim a link, you are **not done** —
finish steps 2–5.

## When this is mandatory

Any PR that changes runtime performance of the native path — anything titled
`perf:`, or any change to `Zip/Native/Deflate*`, `Zip/Native/Inflate*`,
`Zip/Native/LZ77*`, `Zip/Native/DeflateParse*`, the bit reader/writer, or the
Huffman codec. **Do not merge such a PR until you have generated these graphs,
posted them to the PR, and Kim has seen them.** This is a required gate, not an
optional nicety.

The graphs show **native before vs after** on the real corpora (Canterbury +
Silesia), overlaid on the existing other-language curves (zlib, miniz_oxide,
libdeflate, Go, JS, Zig, OCaml) for context. The before/after **overlay** PNGs
(`/tmp/perf_before_after_*`) are a report artifact — NOT committed; they live
only in the PR comment. The **dashboard** (`bench/results/latest.json` and the
routine `bench/graphs/*.svg`), by contrast, **is** refreshed and committed inside
this same PR (step 8) — that is how the recorded BEFORE for the *next* perf PR
stays current.

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

4. **BEFORE is the base branch's committed `bench/results/latest.json` — do NOT
   rebuild it.** Master already carries up-to-date native numbers:
   `bench/results/latest.json` is the committed dashboard snapshot (native
   `ratio` / `compress_mbps` / `decompress_mbps`, median-of-5 on Canterbury, same
   machine), and it is the canonical BEFORE. There is **no merge-base worktree
   build** — that whole step was wasted work, because the data it would reproduce
   is already recorded in the tree.

   Because **this PR refreshes `latest.json` in place** (step 8), capture the
   BEFORE copy *before* you overwrite it — snapshot the base-branch version to a
   scratch path and pass that to the plotter as BEFORE:
   ```
   git show origin/master:bench/results/latest.json > /tmp/perf_before.json
   ```

   **The invariant that makes this valid: `latest.json` must always reflect the
   current native path on master — and the way it stays current is that every
   native-perf PR refreshes it *within the same PR* (step 8).** Kim does not want
   a separate follow-up "bench: dashboard refresh" PR; folding the refresh into
   the change PR means master's recorded BEFORE is current by construction, and
   the stale-baseline failure mode below cannot arise in the first place. The
   freshness guard stays as a backstop for older history.

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
   - **Empty → snapshot `git show origin/master:bench/results/latest.json >
     /tmp/perf_before.json` and use that as BEFORE.** Its native rows already
     reflect the merge-base; nothing to rebuild. (Snapshot it rather than reading
     the working-tree file directly, since step 8 overwrites the working tree.)
   - **Non-empty → `latest.json` is stale** (older history that predates this
     in-PR-refresh policy). The refresh this PR does in step 8 *fixes* the
     invariant going forward, but it cannot reconstruct the merge-base BEFORE.
     Recover a correct BEFORE with a one-off merge-base build (`git worktree add
     --detach /tmp/before $base && ( cd /tmp/before && lake build bench-report &&
     lake env .lake/build/bin/bench-report --native-only /tmp/perf_before.json )`,
     then `git worktree remove --force /tmp/before`) and pass
     `/tmp/perf_before.json` as BEFORE.

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
     baseline honest now that BEFORE is the base-branch `latest.json` snapshot: if
     it flagged stale, a native commit landed after the snapshot and the *speed*
     curve would be silently wrong even though Δratio stays `0.000000` (the
     classic phantom regression — "before" reflects different code than the
     merge-base). Confirm the guard came back empty, and confirm the plotter's
     printed BEFORE `meta.git_commit` is the snapshot you expect and that
     before/after cover the same `(pattern, level)` rows.

6. **Plot** (other-language curves are reused from the base-branch snapshot,
   never re-measured). The overlay graphs are a report artifact — write them to
   the gitignored `/tmp` so they can never be accidentally committed to the perf
   PR: BEFORE is `/tmp/perf_before.json` (the base-branch `latest.json` snapshot
   from step 4) — pass it twice, once as BEFORE and once as the reused
   other-language source:
   ```
   python3 .claude/skills/perf-pr-graphs/plot_before_after.py \
     /tmp/perf_before.json /tmp/perf_after.json <compress_mbps|decompress_mbps> \
     /tmp/perf_before.json /tmp
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
   for the *magnitude* and the picture for the *positioning*.

   **Silesia is the corpus that matters most — weight it above Canterbury for the
   merge decision.** Silesia is large real-world data (10–50 MB files); Canterbury
   is small synthetic files (≤1 MB). They **can and do disagree**, because the
   decode-table access pattern is cache-bound: a change can help on Silesia's
   large hot-loop files while hurting tiny Canterbury files that fit in cache
   regardless (issue #2650's de-box measured **−4.5% Canterbury but +5.8%
   Silesia** — a real split, not noise). **A Silesia win outweighs a Canterbury
   loss.** Do NOT read Canterbury alone and call it the verdict.

   The catch: Canterbury is median-of-5 (low per-run noise) but unrepresentative;
   Silesia is single-pass (`reps=1`), so a *single* Silesia run carries ±30%+
   run-to-run noise and a lone graph cannot resolve a single-digit-% delta on it.
   When the Silesia delta is small or borderline — exactly when the merge decision
   hinges on it — do the controlled interleaved measurement below instead of
   trusting one pass or a cross-session graph.

8. **Refresh the dashboard inside this PR and commit it.** This is compulsory and
   part of *this* PR — Kim does not want a follow-up "bench: dashboard refresh"
   PR. Splice the AFTER native rows you already measured in step 3 into the
   committed dashboard and re-render the routine SVGs, then commit both into the
   perf PR's own diff:
   ```
   nix-shell --run "python3 bench/merge_native.py bench/results/latest.json \
     /tmp/perf_after.json bench/results/latest.json \
     && python bench/plot.py bench/results/latest.json bench/graphs"
   git add bench/results/latest.json bench/graphs
   git commit -m "bench: refresh dashboard for <this PR's change>"
   ```
   `bench/results/latest.json` is the committed source of truth, so its native
   rows must be **consistent across all 9 levels**. If step 3 measured only a
   level subset (e.g. `1,2,3,4,5,6,7,8` for a decode PR), the spliced dashboard
   would keep stale rows on the skipped levels — so for the dashboard refresh,
   either measure all 9 levels, or run the full native-only path that does the
   measure+merge+plot in one shot and records every level:
   ```
   nix-shell --run "taskset -c <free-core> bash bench/run.sh --native-only"
   git add bench/results/latest.json bench/graphs
   ```
   (`--native-only` reuses the reference-language rows — it does not pay the ~2 h
   external-comparator rebuild.) Pin to a free core so the committed numbers are
   not contention-depressed, and confirm `git status` shows only
   `bench/results/latest.json` and `bench/graphs/*.svg` changed by this step.

9. **Always post the graphs as a PR comment — then give Kim the link.** This step
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

## Resolving a small or borderline delta (controlled interleaved measurement)

The routine graph (steps 1–9) compares a fresh AFTER against the base-branch
`latest.json` BEFORE — a *cross-session* comparison whose noise floor is a few
percent, which is fine for visible wins but **cannot** settle a single-digit-%
delta (and single-pass Silesia adds ±30% on top). When the merge decision hinges
on a small delta — especially on Silesia — measure both sides **back-to-back in
one session** so common-mode noise (background load, turbo, thermal) cancels:

- Build a BEFORE binary at the branch merge-base (`git worktree add --detach
  /tmp/before $(git merge-base origin/master HEAD)` then `lake build bench-report`
  in it). The AFTER binary is the PR branch's.
- Run the two binaries **alternately, N times** (≥5 pairs), each pinned to one
  core (`taskset -c <core>`). Consecutive AFTER/BEFORE runs then see near-identical
  machine state, so their *ratio* is robust even on a busy machine — the paired
  ratio + its 95% CI is the verdict, not any single run.
- **Run BOTH binaries from the MAIN worktree's directory.** Silesia is gitignored
  and fetched only into the main worktree, so the merge-base worktree has *only*
  committed Canterbury — running the BEFORE binary from there silently measures
  Canterbury while AFTER measures Silesia, and the two never overlap. (The
  `meta.git_commit` stamp follows the CWD, not the binary, so distinguish the two
  by output filename, not by the stamp.)
- To get **Silesia** rows, set Canterbury aside (`mv bench/corpora/canterbury …`)
  so the matrix is fast enough to repeat; restore it after (a `trap` on EXIT).
  L9's optimal-parse *compress* on 203 MB is minutes/run — measure L9 with fewer
  pairs, or skip it if 1–8 already settles the sign (decode delta was uniform
  across levels in #2650).
- Aggregate paired: for each `(file, level, pair)` take `after/before`, then the
  geomean and a 95% CI on the log-ratios. CI excluding 1.0 → real; spanning 1.0 →
  genuinely within noise. This is what turned #2650's "−3% but maybe noise" into a
  firm "−4.5% Canterbury / +5.8% Silesia".

## Notes

- `bench-report --native-only [levels]` lives in `ZipBenchReport.lean`; the plot
  styling mirrors `bench/plot.py` (same colours/markers) for visual continuity.
- The y-axis is log, so a +30% gain reads as a modest visual gap — quote the
  numeric speedup from the printed table, don't rely on the eye alone.
- For a compress PR, also call out any **ratio** change: a speed win that worsens
  the ratio (curve moves right) may not be a net win. zopfli's frozen ratio
  ceiling is in `bench/results/zopfli-ceiling.json` if you want the best-ratio
  reference.
- Keep the **overlay** jsons and PNGs (`/tmp/perf_before*.json`,
  `/tmp/perf_after.json`, `/tmp/perf_before_after_*`) in `/tmp` — they are the
  report artifact and must never enter the PR diff. The **dashboard**
  (`bench/results/latest.json` + `bench/graphs/*.svg`) is the opposite: step 8
  commits it into this PR on purpose, so those *should* show up staged. Before
  finishing, confirm the only tree changes from the graph workflow are that
  committed dashboard pair — no `/tmp` overlay PNG copied into `bench/graphs/`,
  and (if you used the step-4 stale fallback) no leftover `git worktree`.
