# Track D — benchmark dashboard

Native lean-zip vs. reference implementations, on **compression ratio** and
**throughput**, across data patterns × sizes × levels. The graphs use log scales
and are regenerated from committed data by a single command.

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
| `libdeflate` | libdeflate (FFI) | optimized C + SIMD — the runtime speed bar |
| `zopfli` | zopfli (FFI) | maximum-ratio ceiling (compress-only, slow) |

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

zopfli runs a reduced grid (one level, capped at 256 KiB, single rep): it is the
ratio *floor*, not a throughput contender. A comparator whose toolchain is
unavailable is skipped, so the dashboard degrades gracefully.

## Graphs

### Compression throughput vs input size (level 6)
![compression throughput](graphs/compress_throughput.svg)

Per-level set (one figure each, levels 1–9):
[L1](graphs/compress_throughput_L1.svg) ·
[L2](graphs/compress_throughput_L2.svg) ·
[L3](graphs/compress_throughput_L3.svg) ·
[L4](graphs/compress_throughput_L4.svg) ·
[L5](graphs/compress_throughput_L5.svg) ·
[L6](graphs/compress_throughput_L6.svg) ·
[L7](graphs/compress_throughput_L7.svg) ·
[L8](graphs/compress_throughput_L8.svg) ·
[L9](graphs/compress_throughput_L9.svg)

### Decompression throughput vs input size (level 6)
![decompression throughput](graphs/decompress_throughput.svg)

Per-level set:
[L1](graphs/decompress_throughput_L1.svg) ·
[L2](graphs/decompress_throughput_L2.svg) ·
[L3](graphs/decompress_throughput_L3.svg) ·
[L4](graphs/decompress_throughput_L4.svg) ·
[L5](graphs/decompress_throughput_L5.svg) ·
[L6](graphs/decompress_throughput_L6.svg) ·
[L7](graphs/decompress_throughput_L7.svg) ·
[L8](graphs/decompress_throughput_L8.svg) ·
[L9](graphs/decompress_throughput_L9.svg)

### Compression ratio vs input size
![compression ratio](graphs/compression_ratio.svg)

### Compression ratio vs level
![ratio by level](graphs/ratio_by_level.svg)

## What the current snapshot shows

- **Ratio is at parity.** On compressible data native deflate matches the C/Rust
  references byte-for-byte (and is *better* than every implementation at the
  fastest levels on `text`). The language-native peers land within a hair; only
  OCaml `decompress` gives up a little ratio (different LZ77/Huffman).
- **Compression speed is the gap — but it's a language-native gap, not a chasm.**
  At ratio parity, throughput stratifies by implementation maturity: libdeflate
  (C+SIMD) on top, then Zig / miniz_oxide, then Go / zlib, then the JIT'd JS,
  then OCaml, then `native`. lean-zip is in the pack and at the back, but the
  distance to the *other pure-language* codecs is a small single-digit factor,
  not the order-of-magnitude that the C+SIMD ceiling alone suggests.
- **Decompression** is competitive — native inflate runs in the hundreds of
  MB/s, the same order as zlib.

These observations drive the optimization backlog in
[`../plans/track-d-state.md`](../plans/track-d-state.md).
