# lean-zlib

Lean 4 bindings for [zlib](https://zlib.net/) compression, plus tar and ZIP archive support.

Provides whole-buffer and streaming APIs for zlib, gzip, and raw deflate formats, CRC32/Adler32 checksums, tar archives (.tar and .tar.gz), and ZIP archives.

## Requirements

- Lean 4 (tested with v4.20.0 through v4.29.0-rc1)
- zlib development headers (`zlib-dev`, `zlib1g-dev`, or equivalent)
- `pkg-config` (for header discovery on NixOS and similar)

On NixOS, use `nix-shell -p pkg-config zlib` or set `ZLIB_CFLAGS` manually.

## Usage

Add to your `lakefile.lean`:

```lean
require "kim-em" / "lean-zlib"
```

### Compression

```lean
import Zlib

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

let state ← Gzip.InflateState.new
let decompressed ← state.push compressedChunk
let final ← state.finish
```

### Checksums

```lean
let crc ← Checksum.crc32 0 data         -- CRC-32
let adler ← Checksum.adler32 1 data     -- Adler-32
-- Incremental: pass previous result as init
let crc2 ← Checksum.crc32 crc moreData
```

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

### ZIP archives

```lean
-- Create from explicit file list
Zip.create "/tmp/archive.zip" #[
  ("name-in-zip.txt", "/path/on/disk.txt"),
  ("subdir/file.bin", "/other/file.bin")
]

-- Create from directory
Zip.createFromDir "/tmp/archive.zip" "/path/to/dir"

-- Extract all files
Zip.extract "/tmp/archive.zip" "/tmp/output"

-- Extract a single file by name
let data ← Zip.extractFile "/tmp/archive.zip" "name-in-zip.txt"

-- List entries
let entries ← Zip.list "/tmp/archive.zip"
```

ZIP supports stored (method 0) and deflated (method 8) entries, with automatic method selection on creation and CRC32 verification on extraction.

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
