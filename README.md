# lean-zip

**A formally verified zlib implementation in Lean 4.**

lean-zip contains a from-scratch, pure-Lean DEFLATE encoder and decoder, and
Lean's kernel checks that they are inverse to each other. Compression here is
something the type checker has *proved* cannot silently corrupt your data:

```lean
/-- Decompressing the output of `compress` returns the original data,
    for every input and every compression level. -/
theorem zlib_decompressSingle_compress (data : ByteArray) (level : UInt8)
    (maxOutputSize : Nat) (hsize : data.size ≤ maxOutputSize) :
    ZlibDecode.decompressSingle (ZlibEncode.compress data level) maxOutputSize = .ok data
```

That theorem rests on the DEFLATE round-trip at the core,
`inflate (deflateRaw data level) = .ok data`, and on more than 1,100 theorems
across ~32k lines of proof in [`Zip/Spec/`](Zip/Spec). There are no `sorry`s,
and the proofs are re-checked from scratch on every commit.

Astonishly, both the implementation, and the verification, are written entirely by loosely supervised AIs.
Most of the supervision is simply through a [`PLAN.md`](PLAN.md), and workers iterating on that with no state management beside the Github repository.

(lean-zip also ships thin FFI bindings to system zlib, for when you just want
the C library directly, plus pure-Lean tar and ZIP archives. Jump to
[Using it](#using-it).)

## Verification enables performance

Here is the interesting part.

![Silesia compression: speed vs ratio](bench/graphs/silesia_compress_pareto.svg)

*Silesia corpus. x = compression ratio (← smaller is better), y = throughput
(MB/s, log scale); each line is one codec swept across its levels, so up-and-to-the-left
wins. The full dashboard (decode benchmarks, per-file heatmaps, and methodology)
is in [`bench/`](bench/README.md).*

Once correctness is a *theorem*, you can ambitiously and aggressively optimize.
Rewrite the hot loop, hand-roll the Huffman table walk,
add a block-splitting heuristic, swap a clean fold for a word-at-a-time byte
reader, and the obligation `inflate (deflate x) = x` either still holds or the
build goes red. An optimization *cannot* quietly trade away correctness, because
correctness here isn't a test suite that samples some inputs; it's a statement
about **all** inputs that the kernel insists on.

That makes the optimization work safe to hand to a machine. Much of lean-zip,
including essentially all of the performance work behind that graph, was
written by coding agents working autonomously: each one claims an issue, works
in its own git worktree, opens a pull request, and that PR cannot merge unless
the round-trip proof still goes through. The proof is the ratchet.

And it works. In the graph above, we see the performance of the pure-Lean codec (`native`).
Note that the y-axies is a log scale, so a vertical gap is a *multiplicative* speed factor.
Comparing at matched compression ratios, the Lean implementation:

- **beats** the pure-OCaml [`decompress`](https://github.com/mirage/decompress)
  library outright: 2–3× faster at any given ratio, and it reaches ratios
  OCaml's encoder can't;
- runs **within ~2× of Rust's miniz_oxide and C's zlib at its faster levels**,
  widening to ~4× at the denser settings those codecs reach by default. The
  high-compression end (levels 8–9) is where native is weakest and the current
  optimization frontier sits;
- trails the hand-tuned **C + SIMD** ceiling (libdeflate) by the most, as
  expected for the format.

This codec started out far slower than everything else on the chart. The gap
closed not through one clever human insight but through a long series of small,
individually-verified steps. That is the bet behind
Gwern's ["Lean software scaling laws"](https://gwern.net/lean-scaling):
formally-verifiable languages may start from a worse baseline but scale better,
because verified code is the substrate on which automated optimization can
safely compound.

The author cheerfully admits to being an amateur at performance work, which is
rather the point: she didn't have to be an expert, only to keep the proofs
green. If you know how to make DEFLATE go faster, the proofs are waiting to
catch your mistakes; contributions very welcome.

## Using it

Add to your `lakefile.lean`:

```lean
require "kim-em" / "lean-zip"
```

### Compression

```lean
import Zip

-- Zlib format
let compressed ← Zlib.compress data
let original ← Zlib.decompress compressed

-- Gzip format (compatible with gzip/gunzip)
let gzipped ← Gzip.compress data (level := 6)
let original ← Gzip.decompress gzipped

-- Raw deflate (no header/trailer, used internally by ZIP)
let deflated ← RawDeflate.compress data
let original ← RawDeflate.decompress deflated
```

The high-level `Zlib`/`Gzip`/`RawDeflate` entry points above bind system zlib
through FFI: the fast, ubiquitous baseline. The verified pure-Lean codec that
the proofs and benchmarks are about lives under
[`Zip.Native`](Zip/Native) (`Zip.Native.Deflate.deflateRaw` to compress,
`Zip.Native.InflateBuf.inflate` to decompress); it needs no C library at all.

### Streaming

For data too large to fit in memory:

```lean
-- Stream between IO.FS.Streams (64KB chunks, bounded memory)
Gzip.compressStream inputStream outputStream (level := 6)
Gzip.decompressStream inputStream outputStream

-- File helpers
let gzPath ← Gzip.compressFile "/path/to/file"         -- writes /path/to/file.gz
let outPath ← Gzip.decompressFile "/path/to/file.gz"   -- writes /path/to/file
```

### Low-level streaming state

```lean
let state ← Gzip.DeflateState.new (level := 6)
let compressed ← state.push chunk1
let compressed2 ← state.push chunk2
let final ← state.finish  -- must call exactly once
```

### Checksums

```lean
let crc ← Checksum.crc32 0 data         -- CRC-32
let adler ← Checksum.adler32 1 data     -- Adler-32
-- Incremental: pass previous result as init
let crc2 ← Checksum.crc32 crc moreData
```

CRC-32 and Adler-32 also have verified pure-Lean implementations in
[`Zip.Native`](Zip/Native), each proved equal to its specification.

### Tar archives

```lean
-- Create .tar.gz from a directory (streaming, bounded memory)
Tar.createTarGz "/tmp/archive.tar.gz" "/path/to/dir"

-- Extract .tar.gz
Tar.extractTarGz "/tmp/archive.tar.gz" "/tmp/output"

-- Create/extract raw .tar via IO.FS.Stream
Tar.createFromDir stream dir
Tar.extract stream outDir

-- List entries without extracting
let entries ← Tar.list stream
```

Tar supports UStar, PAX extended headers (for long paths, large files, UTF-8),
and GNU long name/link extensions. Paths exceeding UStar limits are
automatically encoded with PAX headers on creation.

### ZIP archives

```lean
-- Create from explicit file list
Archive.create "/tmp/archive.zip" #[
  ("name-in-zip.txt", "/path/on/disk.txt"),
  ("subdir/file.bin", "/other/file.bin")
]

-- Create from directory
Archive.createFromDir "/tmp/archive.zip" "/path/to/dir"

-- Extract all files
Archive.extract "/tmp/archive.zip" "/tmp/output"

-- Extract a single file by name
let data ← Archive.extractFile "/tmp/archive.zip" "name-in-zip.txt"

-- List entries
let entries ← Archive.list "/tmp/archive.zip"
```

ZIP supports stored (method 0) and deflated (method 8) entries with automatic
method selection, CRC32 verification, and ZIP64 extensions for archives
exceeding 4GB or 65535 entries.

For Zstandard (zstd) support, see [lean-zstd](https://github.com/kim-em/lean-zstd).

## How it's organized

- [`Zip/`](Zip): FFI wrappers and the public API
- [`Zip/Native/`](Zip/Native): the pure-Lean implementations (no FFI)
- [`Zip/Spec/`](Zip/Spec): formal specifications and the correctness proofs
- [`ZipTest/`](ZipTest): per-module conformance tests (native vs FFI)
- [`bench/`](bench/README.md): the benchmark dashboard and methodology

Every source file opens with a module docstring describing its purpose. Shared
utilities (Binary, Handle, BitReader) live in
[lean-zip-common](https://github.com/kim-em/lean-zip-common).

The specifications aim past the tautological. Where possible they characterize
mathematical properties independent of the implementation (`crc32 (a ++ b)`
in terms of `crc32 a` and `crc32 b`, prefix-freeness and the Kraft inequality
for the Huffman codes, invertibility for the codecs) rather than merely
asserting that two pieces of code agree. The round-trip theorem above is the
capstone: it says the encoder and decoder are genuine inverses, not that they
were transcribed from the same RFC.

## Requirements

- Lean 4 (tested with v4.20.0 through v4.30.0)
- zlib development headers (`zlib-dev`, `zlib1g-dev`, or equivalent), for the
  FFI baseline
- `pkg-config` (for header discovery on NixOS and similar)
- Optional comparator toolchains (`cargo`, `libdeflate`, `zopfli`, Go, Node,
  Zig, OCaml) used only by the benchmark harness; absent ones degrade
  gracefully. See [BENCH.md](BENCH.md).

On NixOS (or any system where zlib isn't on the default library path), a
`shell.nix` provides the C dependencies:

```bash
nix-shell    # then run lake build, lake exe test, etc. inside the shell
```

Or use [direnv](https://direnv.net/) for automatic activation (`direnv allow`
once; the environment then activates on `cd`). You can also set `ZLIB_CFLAGS`
manually to point at the headers.

## Building and testing

```bash
lake build                              # library + test executable
lake build test && .lake/build/bin/test # run all tests
```

## Benchmarking

The committed dashboard in [`bench/`](bench/README.md) is regenerated by a
single `bench/run.sh`. For ad-hoc measurements there is also a driver for use
with [hyperfine](https://github.com/sharkdp/hyperfine):

```bash
lake build bench
hyperfine 'lake exe bench inflate 1048576 prng 6'
```

Operations: `inflate`, `deflate`, `gzip`, `zlib`, `crc32`, `adler32`, and their
FFI counterparts. See `lake exe bench` for the full list.

## Known limitations

- **TOCTOU in extraction**: extraction validates every archived path (`..`
  components, absolute paths, and unsafe symlink targets are all rejected), but
  it creates parent directories and writes files in separate steps. A local
  attacker with concurrent write access to the output tree could replace a
  freshly-created directory with a symlink in that window and redirect a write
  outside it. The threat model is therefore narrow: it requires an attacker who
  can already write into the destination during extraction. Closing it fully
  would need an `openat()`/`O_NOFOLLOW` component walk in C (not implemented). If
  you extract untrusted archives into a location other processes can write to,
  stage extraction in a private directory you control.
- **Raw streaming primitives are unbounded**: whole-buffer decompression and
  the stream-piping helpers (`Gzip.decompressStream`, `RawDeflate.decompressStream`)
  enforce a `maxDecompressedSize` cap (default 1 GiB; pass `0` to opt into
  unlimited mode), but the low-level opaque FFI primitives `InflateState.push`
  and `InflateState.finish` accept no limit, so callers building directly on
  them must track total output themselves.

## License

Apache-2.0. See [LICENSE](LICENSE).
