# Architecture

lean-zip is a Lean 4 FFI library wrapping zlib and Zstandard, with pure-Lean tar and ZIP archive support built on top.

## File layout

```
c/zlib_ffi.c          -- zlib C FFI code (~625 lines)
c/zstd_ffi.c          -- Zstd C FFI code (~430 lines)
c/io_ffi.c            -- Handle seek/fileSize/symlink shims (~80 lines)
Zip/Basic.lean        -- Raw zlib compress/decompress declarations
Zip/Gzip.lean         -- Gzip declarations + streaming + file helpers
Zip/Checksum.lean     -- CRC32 and Adler32 checksum declarations
Zip/RawDeflate.lean   -- Raw deflate (no header/trailer) declarations
Zip/Zstd.lean         -- Zstandard declarations + streaming + file helpers
Zip/Binary.lean       -- Byte packing helpers (LE integers, octal, strings)
Zip/Handle.lean       -- IO.FS.Handle seek/fileSize + symlink declarations
Zip/Tar.lean          -- Tar archive create/extract/list + .tar.gz composition
Zip/Archive.lean      -- ZIP archive create/extract/list (with ZIP64)
Zip/Spec/Adler32.lean -- Adler-32 formal spec (list-based)
Zip/Spec/Crc32.lean   -- CRC-32 formal spec (bit-by-bit polynomial)
Zip/Spec/Huffman.lean -- Canonical Huffman code construction and prefix-free proofs
Zip/Spec/Deflate.lean -- DEFLATE bitstream spec (RFC 1951)
Zip/Native/Adler32.lean -- Pure Lean Adler-32 (proved equivalent to spec)
Zip/Native/Crc32.lean -- Pure Lean CRC-32 table-driven (proved equivalent to spec)
Zip/Native/BitReader.lean -- LSB-first bit-level reader for DEFLATE streams
Zip/Native/Inflate.lean -- Pure Lean DEFLATE decompressor (all 3 block types)
Zip/Native/Gzip.lean  -- Pure Lean gzip/zlib decompression + format auto-detection
Zip.lean              -- Re-exports all modules
ZipForStd.lean        -- Missing std library lemmas (upstreaming candidates)
lakefile.lean         -- Build config (pkg-config, static libs, extern link)
ZipTest.lean          -- Test runner (imports all test modules)
ZipTest/              -- 17 test modules (Helpers, unit tests, fixture tests, native tests)
```

## Layer 1: Whole-buffer C functions

### zlib (`c/zlib_ffi.c`)

Standalone functions that take an entire `ByteArray`, compress or decompress, and return a new `ByteArray`:

- `lean_zlib_compress` / `lean_zlib_decompress` — raw deflate (zlib format, `inflateInit`/`deflateInit`)
- `lean_gzip_compress` / `lean_gzip_decompress` — gzip format (`deflateInit2` with `MAX_WBITS+16`, `inflateInit2` with `MAX_WBITS+32`)
- `lean_raw_deflate_compress` / `lean_raw_deflate_decompress` — raw deflate with no header (`-MAX_WBITS`)
- `lean_zlib_crc32` / `lean_zlib_adler32` — checksums via zlib's `crc32()` and `adler32()`

Gzip decompression handles concatenated gzip streams: after `Z_STREAM_END`, if input remains, it calls `inflateReset` and continues.

Buffer management: decompression uses a growable buffer (`grow_buffer`) since the output size isn't known in advance. `initial_decompress_buf` picks `max(src_len * 4, 1024)` with an overflow guard.

### Zstd (`c/zstd_ffi.c`)

- `lean_zstd_compress(data, level)` — `ZSTD_compress()` with `ZSTD_compressBound()` for output buffer
- `lean_zstd_decompress(data)` — uses `ZSTD_getFrameContentSize()` for optimal allocation when size is known; falls back to streaming with growable buffer for unknown-size frames

## Layer 2: Streaming C state (external objects)

### zlib streaming

Two opaque types wrapping a `z_stream` plus a `finished` flag:

```c
typedef struct { z_stream strm; int finished; } deflate_state;
typedef struct { z_stream strm; int finished; } inflate_state;
```

These are registered as Lean external classes with finalizers that call `deflateEnd`/`inflateEnd` on GC. The `finished` flag prevents double-free: once `finish` is called (or inflate detects clean stream end), the flag is set and the finalizer becomes a no-op.

Thread safety: external class registration uses `pthread_once`.

**Deflate** (3 functions per format):
- `lean_gzip_deflate_new(level)` / `lean_raw_deflate_new(level)` — allocates state, calls `deflateInit2` with format-specific `windowBits`
- `lean_gzip_deflate_push(state, chunk)` — feeds chunk with `Z_NO_FLUSH`, loops until `avail_in == 0`, returns compressed output
- `lean_gzip_deflate_finish(state)` — calls `deflate` with `Z_FINISH` in a loop until `Z_STREAM_END`, then `deflateEnd`

**Inflate** (3 functions per format):
- `lean_gzip_inflate_new()` / `lean_raw_inflate_new()` — allocates state, calls `inflateInit2` with format-specific `windowBits`
- `lean_gzip_inflate_push(state, chunk)` — feeds chunk, handles concatenated gzip via `inflateReset`, sets `finished` on clean stream end
- `lean_gzip_inflate_finish(state)` — calls `inflateEnd` if not already finished, returns empty ByteArray

### Zstd streaming

Two opaque types wrapping `ZSTD_CStream*` / `ZSTD_DStream*` plus a `finished` flag:

```c
typedef struct { ZSTD_CStream *cstream; int finished; } zstd_compress_state;
typedef struct { ZSTD_DStream *dstream; int finished; } zstd_decompress_state;
```

Same external class pattern with `pthread_once` registration. Finalizers check the stream pointer for null (not the `finished` flag) to handle the case where `push` detects frame completion and frees the stream before `finish` is called.

- `lean_zstd_compress_new(level)` / `lean_zstd_decompress_new()` — create and init stream
- `lean_zstd_compress_push` / `lean_zstd_decompress_push` — feed chunks via `ZSTD_compressStream` / `ZSTD_decompressStream`
- `lean_zstd_compress_finish` — calls `ZSTD_endStream` in a loop, then frees
- `lean_zstd_decompress_finish` — frees the DStream

### Key invariants (shared by zlib and Zstd)

- `push` after `finish` returns an error
- `finish` is idempotent (second call returns empty)
- Finalizers are safe regardless of whether `finish` was called
- `push` never finalizes — only `finish` does

## Layer 3: Lean streaming declarations

Each streaming C function gets an `@[extern]` declaration. The state types use the standard Lean opaque external pattern:

```lean
opaque DeflateState.nonemptyType : NonemptyType
def DeflateState : Type := DeflateState.nonemptyType.type
instance : Nonempty DeflateState := DeflateState.nonemptyType.property
```

Zstd uses `CompressState` / `DecompressState` following the same pattern.

## Layer 4: Stream piping and file helpers

Pure Lean code built on Layer 3:

- `compressStream` / `decompressStream` — read 64KB chunks from an `IO.FS.Stream`, push through streaming state, write output. Memory usage is bounded.
- `compressFile` / `decompressFile` — open files, pipe through streaming. Output naming: `.gz`/`.zst` appended for compress, stripped (or `.ungz`/`.unzst` appended) for decompress.

Available for Gzip, RawDeflate, and Zstd. These are `partial` because `repeat` with `break` can't be shown terminating.

## Layer 5: Binary helpers (`Zip/Binary.lean`)

Pure Lean byte-packing utilities shared by Tar and ZIP:

- **Little-endian integers** (ZIP/ZIP64): `readUInt16LE`, `readUInt32LE`, `readUInt64LE`, `writeUInt16LE`, `writeUInt32LE`, `writeUInt64LE`
- **Octal ASCII** (Tar): `writeOctal`, `readOctal` — NUL-terminated octal fields
- **String fields** (Tar): `writeString` (NUL-padded), `readString` (NUL-terminated)
- **Utility**: `zeros` — creates a ByteArray of n zero bytes

All loop-based functions use `@[noinline]` to prevent compile-time reduction issues.

## Layer 6: Tar archives (`Zip/Tar.lean`)

Pure Lean, no new C code. Implements UStar format with PAX and GNU extension support.

**Key internals**:
- `splitPath` — splits path into prefix (≤155) + name (≤100) at last `/`
- `buildHeader` / `parseHeader` — pack/unpack 512-byte UStar headers
- `computeChecksum` — sum all 512 bytes treating offset 148-155 as spaces
- `paddingFor` — bytes to next 512-byte boundary
- `readNumeric` — reads tar numeric fields; handles both octal ASCII and GNU base-256 encoding (high bit set → big-endian binary)

**PAX/GNU read support**:
- GNU long name (`typeflag 'L'`) and long link (`typeflag 'K'`): reads entry data as the name/link for the next entry
- PAX extended headers (`typeflag 'x'`): parses `<length> key=value\n` records, applies overrides (path, linkpath, size, mtime, uid, gid, uname, gname) to the next entry
- PAX global headers (`typeflag 'g'`): skipped

**PAX write support**:
- `needsPaxHeader` checks if an entry exceeds UStar limits (path too long, size/mtime exceed octal range)
- `buildPaxRecord` builds correctly length-prefixed PAX records (iterative computation since the length field includes itself)
- `buildPaxEntry` constructs a complete PAX extended header block
- `create` automatically emits PAX headers before entries that need them

**Stream composition for .tar.gz**: `createTarGz` constructs a custom `IO.FS.Stream` whose `write` pushes through `Gzip.DeflateState`, and passes it to `createFromDir`. `extractTarGz` constructs a custom stream whose `read` pulls compressed data and decompresses through `Gzip.InflateState` with an internal buffer. Both achieve true streaming with bounded memory.

**Validation**: `parseHeader` verifies the UStar magic and header checksum before accepting a block. Malformed or non-UStar headers are rejected with an error. Truncated archives (short reads during create, extract, or list) raise explicit errors rather than silently producing incomplete results.

**Robust I/O**: all stream reads (headers, entry data, padding) use a looping `readExact` helper that handles short reads from pipes and network streams.

**Path safety**: on extract, paths are rejected if they contain `..` segments or are absolute, preventing zip-slip/tar-slip directory traversal attacks.

## Layer 7: ZIP archives (`Zip/Archive.lean`)

Pure Lean, no new C code. Built on Binary, Checksum, and RawDeflate.

**Structure**: local file headers + data (sequential), central directory, end of central directory record. All integers little-endian.

**Creation**: writes sequentially, tracks byte offset as `UInt64`, streams central directory headers directly to output (no accumulation), writes EOCD at end. No seeking needed.

**ZIP64 support**: Entry sizes, compressed sizes, and offsets are stored as `UInt64`. When any value exceeds `0xFFFFFFFF`, ZIP64 extra fields (ID `0x0001`) are emitted in both local and central headers, with 32-bit fields set to the `0xFFFFFFFF` sentinel. If entry count exceeds 65535 or CD offset/size exceeds 4GB, a ZIP64 EOCD record (sig `0x06064b50`) and locator (sig `0x07064b50`) are written before the standard EOCD. Small archives produce identical output to pre-ZIP64 code.

**Extraction**: reads whole file into memory and indexes into it. `findEndOfCentralDir` searches for the standard EOCD, then checks for a ZIP64 EOCD locator to get 64-bit offsets. `parseCentralDir` detects `0xFFFFFFFF` sentinel values and reads 64-bit sizes from ZIP64 extra fields.

**Method selection**: on creation, raw-deflates each file; if the result is smaller, uses method 8 (deflated), otherwise method 0 (stored).

**CRC32 verification**: always verified on extraction.

**Path safety**: paths are rejected if they contain `..` segments or are absolute, preventing zip-slip/directory traversal attacks. This applies to both file entries and directory entries.

**Bounds checking**: central directory offsets and local header offsets are validated against file size before indexing, preventing crashes on malformed ZIPs. Central directory size is bounded by `maxCentralDirSize` (default 64MB).

**Robust I/O**: `readExact` and `readExactStream` loop on short reads, handling streams that return fewer bytes than requested (pipes, network, etc.).

**Limitations**: no encryption, no spanning.

## Native implementations and formal specs

Parallel to the FFI wrappers, lean-zip has pure Lean implementations with formal proofs of correctness. These serve as verified reference implementations and can be used when C libraries are unavailable.

### Specifications (`Zip/Spec/`)

Formal mathematical specifications of algorithms, independent of any particular implementation strategy:

- **Adler-32** (`Spec/Adler32.lean`): Two Nat-valued sums modulo 65521, defined as a `List.foldl`. Key theorem: `updateList_append` (compositionality).
- **CRC-32** (`Spec/Crc32.lean`): Bit-by-bit polynomial division with polynomial `0xEDB88320`. Defines both the naive bit-by-bit `crcByte` and the table-driven `crcByteTable`. Key theorems: `updateList_append` (compositionality), `updateList_nil`.
- **Huffman** (`Spec/Huffman.lean`): Canonical Huffman code construction from RFC 1951 §3.2.2. Defines `codeFor` (code assignment), `allCodes`, `decode`. Key theorems: `codeFor_injective` (distinct codewords for distinct symbols), `canonical_prefix_free` (prefix-free property — both same-length and different-length cases proved via Kraft inequality).
- **DEFLATE** (`Spec/Deflate.lean`): Complete DEFLATE bitstream spec. Defines `bytesToBits` (LSB-first), `readBitsLSB`, `LZ77Symbol` with `resolveLZ77`, all RFC 1951 tables, block decode pipeline (stored, fixed Huffman, dynamic Huffman), and stream-level `decode`.

### Native implementations (`Zip/Native/`)

Pure Lean implementations operating on `ByteArray` (via `Array.foldl` on `.data`):

- **Adler-32** (`Native/Adler32.lean`): Direct implementation of the spec using `Array.foldl`. Proof: `updateBytes_eq_updateList` via `Array.foldl_toList`.
- **CRC-32** (`Native/Crc32.lean`): Table-driven implementation using a 256-entry lookup table. Proof chain: `crcBits8_split` (8-fold `crcBit` linearity, via `bv_decide`) → `crcByteTable_eq_crcByte` (table lookup = bit-by-bit) → `updateBytes_eq_updateList` (byte array = list spec).
- **BitReader** (`Native/BitReader.lean`): LSB-first bit-level reader for `ByteArray`. Tracks byte position and bit offset within the current byte. Supports reading individual bits, multi-bit values (up to 25 bits), byte-aligned UInt16 LE reads, and bulk byte reads.
- **DEFLATE inflate** (`Native/Inflate.lean`): Complete DEFLATE (RFC 1951) decompressor supporting all three block types: stored (type 0), fixed Huffman (type 1), and dynamic Huffman (type 2). Uses a binary `HuffTree` type with canonical Huffman code construction from code lengths. LZ77 back-references are resolved against the output buffer with correct handling of overlapping copies. Uses a fuel parameter for termination. `maxOutputSize` parameter guards against zip bombs.
- **Gzip/Zlib framing** (`Native/Gzip.lean`): RFC 1952 gzip and RFC 1950 zlib header/trailer parsing with checksum verification (CRC-32 for gzip, Adler-32 for zlib). Supports concatenated gzip members. Auto-detection of gzip, zlib, and raw DEFLATE formats.

### Conformance testing

- `ZipTest/NativeChecksum.lean` tests native checksum implementations against FFI on: known values, large data, incremental computation, empty input, and single bytes.
- `ZipTest/NativeInflate.lean` tests native DEFLATE decompressor against FFI zlib across compression levels 0–9, empty data, single bytes, large repetitive data (124KB), and pseudo-random data.
- `ZipTest/NativeGzip.lean` tests gzip and zlib decompression at multiple levels, concatenated streams, auto-detect, and error cases (truncated, corrupt, bad checksums).
- `ZipTest/NativeIntegration.lean` tests native backend integration for ZIP and tar.gz extraction (stored, deflated, empty, nested).

## Build system

`lakefile.lean` compiles three C FFI files into static libraries:

1. `c/zlib_ffi.c` → `libzlib_ffi.a` (compiled with `pkg-config --cflags zlib`)
2. `c/zstd_ffi.c` → `libzstd_ffi.a` (compiled with `pkg-config --cflags libzstd`)
3. `c/io_ffi.c` → `libio_ffi.a` (no external library deps — uses POSIX `fseeko`/`fstat`/`symlink`)

Link flags are obtained from `pkg-config --libs`. Zstd is linked statically (`-Wl,-Bstatic -lzstd -Wl,-Bdynamic`) to avoid glibc version mismatches with Lean's bundled toolchain.

Header discovery: checks `ZLIB_CFLAGS` / `ZSTD_CFLAGS` env vars first, falls back to `pkg-config`. The `-fPIC` flag is added on non-Windows platforms.

## Error handling

All FFI functions return `IO` results. On zlib errors, `mk_zlib_error` formats the error with the zlib message string (from `strm.msg`) or `zError()` code name as fallback. On Zstd errors, `mk_zstd_error` uses `ZSTD_getErrorName()`. Tar and ZIP use `IO.userError` for format-level errors (path too long, CRC mismatch, unsupported method, etc.).
