# lean-zlib

Lean 4 bindings for [zlib](https://zlib.net/) compression.

Provides both whole-buffer and streaming APIs for zlib (raw deflate) and gzip formats.

## Requirements

- Lean 4 (v4.20.0+)
- zlib development headers (`zlib-dev`, `zlib1g-dev`, or equivalent)
- `pkg-config` (for header discovery on NixOS and similar)

On NixOS, use `nix-shell -p pkg-config zlib` or set `ZLIB_CFLAGS` manually.

## Usage

Add to your `lakefile.lean`:

```lean
require "kim-em" / "lean-zlib"
```

### Whole-buffer API

```lean
import Zlib

-- Raw zlib (deflate format, no headers)
let compressed ← Zlib.compress data
let original ← Zlib.decompress compressed

-- Gzip format (compatible with gzip/gunzip)
let gzipped ← Gzip.compress data (level := 6)
let original ← Gzip.decompress gzipped
```

Compression level ranges from 0 (no compression) to 9 (best compression), default 6.

### Streaming API

For data too large to fit in memory:

```lean
import Zlib

-- Compress/decompress between IO.FS.Streams (64KB chunks, bounded memory)
Gzip.compressStream inputStream outputStream (level := 6)
Gzip.decompressStream inputStream outputStream

-- File helpers (streaming under the hood)
let gzPath ← Gzip.compressFile "/path/to/file"         -- writes /path/to/file.gz
let outPath ← Gzip.decompressFile "/path/to/file.gz"   -- writes /path/to/file
```

### Streaming state (low-level)

```lean
-- Compression
let state ← Gzip.DeflateState.new (level := 6)
let compressed ← state.push chunk1
let compressed2 ← state.push chunk2
let final ← state.finish  -- must call exactly once

-- Decompression (handles concatenated gzip streams)
let state ← Gzip.InflateState.new
let decompressed ← state.push compressedChunk
let final ← state.finish
```

## Building

```bash
lake build
```

## Testing

```bash
lake build test && .lake/build/bin/test
```

## License

Apache-2.0. See [LICENSE](LICENSE).
