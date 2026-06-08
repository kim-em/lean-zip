---
name: track-d-bench-corpus
description: Use when adding a real corpus (Silesia, enwik*, …) to the Track D benchmark dashboard, or otherwise extending the bench matrix in ZipBenchReport.lean / bench/. Covers the payload-filename↔pattern contract that run_external.py depends on, the workload-list core, the commit-vs-gitignore split, the zopfli cap, and the regenerate-and-commit flow.
allowed-tools: Read, Write, Edit, Bash, Glob, Grep
---

# Track D bench: adding a real corpus

Captures the conventions that converged adding the real-corpus harness +
Canterbury (#2515). Use it whenever a Track D issue asks to add another corpus
(PLAN.md §D names **Silesia** next) or to extend the benchmark matrix.

## The five files that move together

A corpus addition touches exactly these (all under the §D scope guard;
**PLAN.md and .claude/CLAUDE.md stay off-limits**):

1. `bench/fetch_corpora.sh` — add a `fetch_<corpus>` function + a `main` case.
   Verify **file-by-file** against recorded SHA-256 (`sha256sum --check`), fail
   closed. Compute the checksums once by fetching manually, then paste them in.
2. `bench/.gitignore` — `corpora/*` is ignored; **commit small corpora** with a
   `!corpora/<name>/` exception (Canterbury, ~2.8 MB, is committed so CI needs
   no network). **Do NOT commit large corpora** (Silesia ~67 MB, enwik*) — they
   stay fetch-on-demand. PLAN.md §D is explicit about this split.
3. `ZipBenchReport.lean` — add `<corpus>Files`, call `loadCorpus "<corpus>" …`,
   run it through `runWorkloads` for native + every FFI ref + zopfli, and dump
   its payloads in `dumpPayloads`.
4. `bench/comparators/run_external.py` — usually **no change**: `discover_payloads`
   already maps any `payloads/<corpus>/<file>.bin` to pattern `<corpus>/<file>`.
5. `bench/plot.py` — add the corpus to the `CORPORA` list; `corpus_bars` renders
   the per-file grouped bars automatically. Real-corpus files are single-size,
   so they get **bar charts, not the synthetic size-sweep figures**.

Also: `bench/run.sh` fetch step, `bench/README.md` Workloads/graphs sections,
and a `plans/track-d-state.md` Landed row.

## The payload-filename ↔ pattern contract (the subtle part)

Native rows and external-comparator rows must carry the **identical** `pattern`
string or they won't line up in the dashboard. The mechanism:

- Synthetic payloads are flat: `payloads/<pattern>_<size>.bin`; `run_external.py`
  parses `(pattern, size)` via `stem.rpartition("_")`.
- Real-corpus payloads go in a **per-corpus subdir**: `payloads/<corpus>/<file>.bin`.
  `discover_payloads` reconstructs `pattern = "<corpus>/<file>"` (slash and all)
  and takes `size` from the byte length. The native rows use the same
  `s!"{corpus}/{file}"` tag in `ZipBenchReport.loadCorpus`.

Do NOT put a `/` in a flat payload filename, and do NOT encode size in the
corpus filename — keep the subdir convention so the two row sources agree.

## The workload-list core

`runCompressor` (synthetic grid) and the corpus path both delegate to
`runWorkloads name (workloads : List (String × ByteArray)) compress decompress?`,
where each row's `size` is the workload's byte length. To add a workload family,
build a `List (String × ByteArray)` and hand it to `runWorkloads` — don't fork
the timing loop.

## Caps and gotchas

- **zopfli**: level-less and ~100× slower than zlib. On the small committed
  Canterbury it runs at one level (`theLevels := [6]`); on a **large** corpus,
  restrict it to the small files or skip it (PLAN.md §D), or it dominates
  wall-clock.
- **Benchmark individual files, not the concatenation** — otherwise `itersFor`
  collapses to a single iteration and the high levels dominate.
- **`rm -rf .lake` before the first nix-shell build** if the worktree's `.lake`
  was created in a bare shell — its cached `moreLinkArgs` will be missing the
  miniz_oxide / zopfli shim libs and the *exe link* (not the compile) fails with
  `unable to find library -lminiz_oxide_shim`. (Already in project CLAUDE.md; it
  bites here specifically because bench-report links every FFI comparator.)
- Normalize committed corpus file perms to `0644` (tar preserves odd bits;
  e.g. Canterbury's `sum` arrives executable).

## Regenerate-and-commit flow

`bash bench/run.sh` runs the whole pipeline (fetch → Lean matrix + payload dump
→ build + run external comparators → plot). Commit the refreshed
`bench/results/latest.json` **and** `bench/graphs/*.svg` **together** — ratios
are deterministic but throughput is a median-of-5 snapshot of one machine
(recorded in the JSON `meta`). Each comparator self-verifies its roundtrip on
the corpus bytes, and missing toolchains are skipped (graceful degradation).

## Read the data honestly

The synthetic `text` pattern is pathologically compressible (collapses to a few
long matches ⇒ reference-parity ratio, ~100 MB/s). Real corpora routinely
**overturn** synthetic conclusions — on Canterbury native is the worst real
codec on ratio *and* both throughput axes, with the ratio gap largest on big
prose. State the real-corpus read plainly in the Landed row and correct any
synthetic-only "parity" claims in the README.
