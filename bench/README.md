# Track D — benchmark dashboard

Native lean-zip vs. reference implementations, on **compression ratio** and
**throughput**, over the **real compression corpora** across every DEFLATE
level. The graphs are regenerated from committed data by a single command.

> **Real corpora only.** Synthetic patterns were removed (see
> [`../plans/track-d-state.md`](../plans/track-d-state.md), D-18): the pseudo-prose
> pattern was pathologically compressible (200:1) and its decode read ~3800 MB/s
> versus ~106 MB/s on real prose in the *same* run, so it flattered native on
> every axis. The headline numbers now rest entirely on representative data.

```
bench/run.sh        # build + run the matrix, build + run the comparators, render the SVGs
```

That runs [`lake exe bench-report`](../ZipBenchReport.lean) (writes
[`results/latest.json`](results/latest.json) and dumps the exact payloads), then
the external-language comparators (see below), then [`plot.py`](plot.py) (writes
the SVGs). Ratios are deterministic; throughput is a **median-of-5 snapshot of
the machine recorded in the JSON `meta`** — commit the JSON and SVGs together.

## Compressors compared

The honest comparison group for a pure-Lean codec is other **language-native**
implementations (no SIMD/asm, or GC'd, or JIT'd) — not just the C + SIMD ceiling.

**C / SIMD references and the ratio ceiling**

| Key | Implementation | Role |
|-----|----------------|------|
| `native` | lean-zip pure-Lean DEFLATE | the thing we are improving |
| `zlib` | system zlib (FFI) | the ubiquitous baseline |
| `miniz_oxide` | Rust miniz_oxide (FFI) | widely-used Rust reimplementation |
| `libdeflate` | libdeflate (FFI) | optimized C + SIMD — the runtime speed bar; swept over its full **levels 1–12** (the others cap at 9), so its densest points (10–12) appear on the Pareto |
| `zopfli` | zopfli (FFI) | maximum-ratio ceiling — **frozen** (see below); never in the routine matrix |

**Language-native peers** (each a self-verifying CLI under
[`comparators/`](comparators), built by
[`comparators/build_all.sh`](comparators/build_all.sh), timed with the *same*
methodology as the Lean matrix — median-of-5, `itersFor(size)` iters, throughput
vs uncompressed bytes — and run over byte-identical dumped payloads):

| Key | Implementation | Notes |
|-----|----------------|-------|
| `go` | Go stdlib `compress/flate` | pure Go, the mature language-native standard |
| `js` | [`fflate`](https://github.com/101arrowz/fflate) on Node | pure JS on V8's JIT (not node's C-zlib binding) |
| `zig` | Zig stdlib `std.compress.flate` (0.14.1) | pure Zig; **levels 1–3 not implemented upstream** → mapped to the fastest real level, so L1–L4 coincide. 0.15's encoder is an unimplemented `@panic("TODO")`, hence 0.14.1. |
| `ocaml` | [`decompress`](https://github.com/mirage/decompress) (mirage) | pure OCaml, MirageOS pedigree; slightly different LZ77/Huffman ⇒ a hair worse ratio |

zopfli is the maximum-ratio reference, but it is compress-only, level-less, and
~100× slower than zlib — at default iteration count it dominated the wall-clock
of the whole matrix. So it is **not** part of the routine `bench-report` run.
Instead it is a **frozen artifact**, [`results/zopfli-ceiling.json`](results/zopfli-ceiling.json),
generated once and overlaid on the ratio graphs by [`plot.py`](plot.py):

```
# One-time only — do NOT run on every regeneration (very slow). Re-run solely
# if the corpora themselves change:
lake env .lake/build/bin/bench-report --zopfli-ceiling bench/results/zopfli-ceiling.json
```

Its `ratio`/`out_size` are deterministic (the meaningful signal); its single-rep
`compress_mbps` is an artifact, not a benchmark. A language-native comparator
whose toolchain is unavailable is skipped, so the dashboard degrades gracefully.

## Workloads

The **real compression corpora** from the literature, swept over levels 1–9
(`libdeflate` over its full 1–12 — see *Compressors compared*).
Each corpus is a subdirectory of [`corpora/`](corpora); every file in it is one
single-size workload tagged `<corpus>/<file>`, and the harness discovers corpora
by directory (nothing hard-codes Canterbury — a new corpus slots in once its
files land).

- **Canterbury corpus** (11 files, ~2.8 MB: English text, HTML, C and Lisp
  source, an Excel spreadsheet, a fax bitmap, a man page, a SPARC binary),
  committed under [`corpora/canterbury/`](corpora/canterbury) (materialized by
  [`fetch_corpora.sh`](fetch_corpora.sh), verified against recorded SHA-256), so
  CI needs no network.
- **Silesia corpus** (12 files, ~202 MB: prose, UNIX binaries, an HTML
  dictionary, a source tarball, XML, databases, medical images, a DLL) — the
  modern standard zstd/brotli/lzma report against. Fetched on demand into a
  gitignored cache (`fetch_corpora.sh silesia`, pinned GitHub mirror,
  SHA-256-verified); its rows slot into the same per-level charts automatically.
  Because it is ~70× larger than Canterbury, it runs a **reduced matrix** —
  a single timing pass — so the regeneration stays tractable.

The synthetic `prng` pattern used to be the only incompressible workload; its
replacement is **real** poorly-compressible files in the corpora (Silesia `sao`,
`x-ray`, `ooffice`). A near-1.0-ratio point, if wanted, comes from a real
already-compressed file (a JPEG/PDF) — never synthetic noise.

## Graphs

Each corpus gets a layered, corpus-generic set (a new corpus slots in with no
code change). The **headline is the speed-vs-ratio Pareto scatter**: x = ratio
(← smaller is better), y = speed (MB/s, log), and each codec is *one line tracing
its levels*, so the whole speed/ratio tradeoff reads at a glance — top-left (fast
*and* small) is best, and a dominated codec sits to the lower-right. Two
complements give precise numbers and per-file detail:

- `<corpus>_compress_pareto.svg` — **headline**: compression speed vs ratio,
  codecs as level-curves (replaces the whole per-level bar set).
- `<corpus>_decode_density.svg` + `<corpus>_decode_ranking.svg` — the
  **decompression analogue** (see *Decoding* below): every decoder timed on
  byte-identical libdeflate streams. The density chart is a per-file scatter
  (x = that file's libdeflate ratio, y = decode MB/s); the ranking chart is the
  precise lollipop ordering. Both carry the `memcpy` bandwidth ceiling. Not a
  Pareto — input density is exogenous to the decoder, so the highest band wins.
- `<corpus>_summary.svg` — colour-graded geomean table (ratio / compress /
  decompress per codec, level 6), sorted by speed.
- `<corpus>_ratio_heatmap.svg` / `_compress_heatmap.svg` — per file, relative to
  zlib (red = worse), showing *where* a codec wins or loses without 100 bars.

### Canterbury corpus (11 small files, levels 1–9; libdeflate 1–12)

![canterbury compression speed vs ratio](graphs/canterbury_compress_pareto.svg)
![canterbury summary table](graphs/canterbury_summary.svg)
![canterbury ratio vs zlib per file](graphs/canterbury_ratio_heatmap.svg)
![canterbury compress speed vs zlib per file](graphs/canterbury_compress_heatmap.svg)

### Silesia corpus (12 large files, levels 1–9; libdeflate 1–12)

![silesia compression speed vs ratio](graphs/silesia_compress_pareto.svg)
![silesia decode throughput vs input density](graphs/silesia_decode_density.svg)
![silesia decode throughput ranking](graphs/silesia_decode_ranking.svg)
![silesia summary table](graphs/silesia_summary.svg)
![silesia ratio vs zlib per file](graphs/silesia_ratio_heatmap.svg)
![silesia compress speed vs zlib per file](graphs/silesia_compress_heatmap.svg)

## Decoding (decode-density)

The compress headline is a *speed-vs-ratio Pareto* because each codec chooses its
own ratio/speed tradeoff. Decompression has no such tradeoff: the input density is
**exogenous** — a property of the stream, not the decoder's choice. So the decode
charts measure **decode throughput vs input density**, with every decoder on
*byte-identical* input (only possible because DEFLATE is one interoperable format
— you genuinely can feed one encoder's stream to every decoder). The fixed encoder
is **libdeflate** (raw DEFLATE, the densest realistic streams); `memcpy` is the
memory-bandwidth ceiling on emitting the output bytes. This is the rigorous way to
isolate a decoder: an own-encoder scatter (the lzbench / Squash convention)
confounds decoder speed with each encoder's ratio.

Two views, both at a representative encode level (libdeflate L6):

- **`<corpus>_decode_density.svg`** — per-file scatter: x = each file's
  compression ratio (wide, from ~0.27 text to ~0.9 incompressible like `sao` /
  `x-ray`), y = decode MB/s. Shows content-dependence — literal-heavy
  incompressible data decodes differently than match-heavy text.
- **`<corpus>_decode_ranking.svg`** — lollipop of geomean decode MB/s per decoder,
  with the memcpy ceiling showing the headroom.

Pipeline (wired into `bench/run.sh` step 3b):

```
# 1. dump libdeflate streams for Silesia + time the in-process decoders + memcpy
lake env .lake/build/bin/bench-report --decode-density \
  bench/results/decode_density.json bench/payloads-deflate
# 2. time the external decoders (Go / JS / Zig / OCaml) on the same streams
python3 bench/decode_density.py bench/payloads-deflate bench/results/decode_density.json
# 3. plot.py auto-detects decode_density.json → graphs/<corpus>_decode_{density,ranking}.svg
```

Each comparator gains a `decode <stream.deflate>` mode (alongside its existing
`<payload> <level>` roundtrip mode) so it decodes a provided stream with the same
median-of-5 / `itersFor` methodology as the Lean side. The streams under
`bench/payloads-deflate/` are gitignored; `decode_density.json` is committed
alongside `latest.json`.

## What the current snapshot shows

> On real data (Canterbury, level 6, geomean over 11 files) native is the
> **worst real codec on all three axes** — ratio 0.323 (zlib 0.299), compress
> 10 MB/s (zlib 55), decompress 92 MB/s (zlib 696) — with the ratio gap
> **largest on big prose** (`plrabn12` +30%, `lcet10` +24% vs zlib). Those two
> findings drive the Track D backlog.

- **Ratio.** Native trails every real codec; the gap is small on
  short/structured files but large on big prose (`plrabn12.txt` 0.525 vs zlib's
  0.405). The language-native peers land within a hair; only OCaml `decompress`
  gives up a little ratio (different LZ77/Huffman). zopfli is the floor (0.279).
- **Compression speed is the gap — but it's a language-native gap, not a chasm.**
  Throughput stratifies by implementation maturity: libdeflate (C+SIMD) on top,
  then Zig / miniz_oxide, then Go / zlib, then the JIT'd JS, then OCaml, then
  `native`. lean-zip is in the pack and at the back, but the distance to the
  *other pure-language* codecs is a small single-digit factor, not the
  order-of-magnitude that the C+SIMD ceiling alone suggests.
- **Decompression is behind too on real data** — native ~94 MB/s vs zlib ~692
  (≈7×) on Canterbury, ~100 vs ~365 (≈4×) on Silesia. (The earlier "competitive"
  read came from the synthetic match-heavy text, which decoded as near-pure
  memcpy; real, literal-heavy data exposes the per-symbol Huffman decode path.)

These observations drive the optimization backlog in
[`../plans/track-d-state.md`](../plans/track-d-state.md).
