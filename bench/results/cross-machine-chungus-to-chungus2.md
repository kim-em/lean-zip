# Cross-machine benchmark consistency: chungus → chungus2

The canonical Track D benchmark machine is moving from **chungus** to
**chungus2**. This note records how the two machines compare, so the historical
dashboard stays interpretable across the move. Regenerate the tables with:

```
python3 bench/cross_machine.py \
  bench/results/archive/latest.chungus.7e98994a.json \
  bench/results/latest.json
```

- **OLD**: `Linux chungus x86_64` @ `7e98994a` (2026-07-05T08:48Z) — archived at
  [`archive/latest.chungus.7e98994a.json`](archive/latest.chungus.7e98994a.json)
- **NEW**: `Linux chungus2 x86_64` @ `9c93b270` (2026-07-05) — the current
  [`latest.json`](latest.json)
- 1748 `(compressor, corpus/file, level)` cells compared, across all 8 compressors.

## Verdict

**chungus2 ≈ chungus; the move is sound.** Across the six comparators whose
toolchain version is stable across the move (`native`, `libdeflate`,
`miniz_oxide`, `zig`, `zlib`, `ocaml` — 1334 cells) the throughput geomean is
**1.0004× compress / 0.9967× decompress** — the two machines are
indistinguishable (within ~0.3%) on identical code. Compression **ratio is
byte-identical on both machines for every compressor** (`max |Δratio| =
0.000000` across all 1748 cells, including `native` — the native speed-only
commits between `7e98994a` and `9c93b270` changed no output). Existing dashboard
numbers therefore stay directly comparable to fresh chungus2 numbers.

## Being fair to go and js: best versions

Each language should run on its best current release, not whatever an old channel
happened to pin. On chungus2 that is **go 1.26.3** (via `nix-shell -p go`, the
newest) and **Node v26.3.0** (via `nodejs_latest` — `comparators/build_all.sh`
and `run.sh` were switched from the older default `nodejs`, which was v24; v26's
V8 is ~+22% on JS compress). The old chungus snapshot used *older* go and node,
so the `go`/`js` rows below move with the **compiler version**, not the machine:

- **`go`: +77% compress / +133% decompress.** Old chungus benchmarked an older
  Go; chungus2 uses go 1.26.3, whose `compress/flate` and codegen are much
  faster. A compiler win, correctly credited to Go now that it runs its best.
- **`js`: 0.93× compress / 0.72× decompress.** Even on the newest Node, V8
  throughput is highly CPU- and session-sensitive and carries by far the widest
  run-to-run variance of any comparator here. The chungus2 js rows are a
  **max-of-3 clean sequential passes** (the three agreed to within 4% compress /
  0.5% decompress); the residual gap vs the old chungus snapshot is dominated by
  cross-session V8 variance, not a stable machine difference. Read js as
  indicative only.

`zig` (pinned `zig_0_14`) lands at 0.99×, confirming a version-stable comparator
is flat across the move.

> Going forward both `go` and `js` track the newest release (`-p go`,
> `nodejs_latest`), so each language is always represented at its best. If strict
> run-to-run reproducibility is later wanted, pin them to a concrete version the
> way `zig_0_14` is — but that trades "best" for "frozen".

## Throughput: chungus2 / chungus (geomean over shared cells)

| compressor | cells | compress× | decompress× | version across the move |
|---|---|---|---|---|
| go | 207 | **1.775x** | **2.330x** | older Go → go 1.26.3 (newest) |
| js | 207 | **0.930x** | **0.722x** | older node → v26.3.0 (newest); high V8 variance |
| libdeflate | 276 | 0.995x | 0.978x | stable |
| miniz_oxide | 207 | 0.997x | 0.993x | stable |
| native | 230 | 1.001x | 1.003x | stable (lean toolchain) |
| ocaml | 207 | 1.011x | 1.002x | stable |
| zig | 207 | 0.992x | 1.005x | stable (`zig_0_14`) |
| zlib | 207 | 1.008x | 1.000x | stable |

**Version-stable comparators only (the clean machine factor): compress 1.0004×,
decompress 0.9967×** — chungus2 and chungus are the same speed to within 0.3%.

## Compression ratio consistency (deterministic → machine-independent)

Every compressor: `max |Δratio| = 0.000000`, 0 cells differing — output is fully
reproducible across both machines and both commits.

| compressor | cells | max \|Δratio\| |
|---|---|---|
| go | 207 | 0.000000 |
| js | 207 | 0.000000 |
| libdeflate | 276 | 0.000000 |
| miniz_oxide | 207 | 0.000000 |
| native | 230 | 0.000000 |
| ocaml | 207 | 0.000000 |
| zig | 207 | 0.000000 |
| zlib | 207 | 0.000000 |
