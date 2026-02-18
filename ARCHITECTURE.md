# Architecture

lean-zlib is a Lean 4 FFI library wrapping zlib, with pure-Lean tar and ZIP archive support built on top.

## File layout

```
c/zlib_ffi.c          -- All C FFI code (~640 lines)
Zlib/Basic.lean        -- Raw zlib compress/decompress declarations
Zlib/Gzip.lean         -- Gzip declarations + streaming + file helpers
Zlib/Checksum.lean     -- CRC32 and Adler32 checksum declarations
Zlib/RawDeflate.lean   -- Raw deflate (no header/trailer) declarations
Zlib/Binary.lean       -- Byte packing helpers (LE integers, octal, strings)
Zlib/Tar.lean          -- Tar archive create/extract/list + .tar.gz composition
Zlib/Zip.lean          -- ZIP archive create/extract/list
Zlib.lean              -- Re-exports all modules
lakefile.lean          -- Build config (pkg-config, static lib, extern link)
Test.lean              -- Roundtrip tests for all API layers
```

## Layer 1: Whole-buffer C functions

Standalone functions that take an entire `ByteArray`, compress or decompress, and return a new `ByteArray`:

- `lean_zlib_compress` / `lean_zlib_decompress` — raw deflate (zlib format, `inflateInit`/`deflateInit`)
- `lean_gzip_compress` / `lean_gzip_decompress` — gzip format (`deflateInit2` with `MAX_WBITS+16`, `inflateInit2` with `MAX_WBITS+32`)
- `lean_raw_deflate_compress` / `lean_raw_deflate_decompress` — raw deflate with no header (`-MAX_WBITS`)
- `lean_zlib_crc32` / `lean_zlib_adler32` — checksums via zlib's `crc32()` and `adler32()`

Gzip decompression handles concatenated gzip streams: after `Z_STREAM_END`, if input remains, it calls `inflateReset` and continues.

Buffer management: decompression uses a growable buffer (`grow_buffer`) since the output size isn't known in advance. `initial_decompress_buf` picks `max(src_len * 4, 1024)` with an overflow guard.

## Layer 2: Streaming C state (external objects)

Two opaque types wrapping a `z_stream` plus a `finished` flag:

```c
typedef struct { z_stream strm; int finished; } deflate_state;
typedef struct { z_stream strm; int finished; } inflate_state;
```

These are registered as Lean external classes with finalizers that call `deflateEnd`/`inflateEnd` on GC. The `finished` flag prevents double-free: once `finish` is called (or inflate detects clean stream end), the flag is set and the finalizer becomes a no-op.

Thread safety: external class registration uses `pthread_once`.

### FFI functions

**Deflate** (3 functions per format):
- `lean_gzip_deflate_new(level)` / `lean_raw_deflate_new(level)` — allocates state, calls `deflateInit2` with format-specific `windowBits`
- `lean_gzip_deflate_push(state, chunk)` — feeds chunk with `Z_NO_FLUSH`, loops until `avail_in == 0`, returns compressed output
- `lean_gzip_deflate_finish(state)` — calls `deflate` with `Z_FINISH` in a loop until `Z_STREAM_END`, then `deflateEnd`

**Inflate** (3 functions per format):
- `lean_gzip_inflate_new()` / `lean_raw_inflate_new()` — allocates state, calls `inflateInit2` with format-specific `windowBits`
- `lean_gzip_inflate_push(state, chunk)` — feeds chunk, handles concatenated gzip via `inflateReset`, sets `finished` on clean stream end
- `lean_gzip_inflate_finish(state)` — calls `inflateEnd` if not already finished, returns empty ByteArray

Raw deflate reuses the same `deflate_state`/`inflate_state` types and the same `push`/`finish` C functions. Only the `new` constructors differ (different `windowBits`).

### Key invariants

- `push` after `finish` returns an error
- `finish` is idempotent (second call returns empty)
- Finalizers are safe regardless of whether `finish` was called
- `push` never passes `Z_FINISH` to zlib — only `finish` does

## Layer 3: Lean streaming declarations

Each streaming C function gets an `@[extern]` declaration. The state types use the standard Lean opaque external pattern:

```lean
opaque DeflateState.nonemptyType : NonemptyType
def DeflateState : Type := DeflateState.nonemptyType.type
instance : Nonempty DeflateState := DeflateState.nonemptyType.property
```

## Layer 4: Stream piping and file helpers

Pure Lean code built on Layer 3:

- `compressStream` / `decompressStream` — read 64KB chunks from an `IO.FS.Stream`, push through streaming state, write output. Memory usage is bounded.
- `compressFile` / `decompressFile` — open files, pipe through streaming. Output naming: `.gz` appended for compress, `.gz` stripped (or `.ungz` appended) for decompress.

These are `partial` because `repeat` with `break` can't be shown terminating.

## Layer 5: Binary helpers (`Zlib/Binary.lean`)

Pure Lean byte-packing utilities shared by Tar and ZIP:

- **Little-endian integers** (ZIP): `readUInt16LE`, `readUInt32LE`, `writeUInt16LE`, `writeUInt32LE`
- **Octal ASCII** (Tar): `writeOctal`, `readOctal` — NUL-terminated octal fields
- **String fields** (Tar): `writeString` (NUL-padded), `readString` (NUL-terminated)
- **Utility**: `zeros` — creates a ByteArray of n zero bytes

All loop-based functions use `@[noinline]` to prevent compile-time reduction issues.

## Layer 6: Tar archives (`Zlib/Tar.lean`)

Pure Lean, no new C code. Implements UStar format (512-byte headers with octal fields).

**Key internals**:
- `splitPath` — splits path into prefix (≤155) + name (≤100) at last `/`
- `buildHeader` / `parseHeader` — pack/unpack 512-byte UStar headers
- `computeChecksum` — sum all 512 bytes treating offset 148-155 as spaces
- `paddingFor` — bytes to next 512-byte boundary

**Stream composition for .tar.gz**: `createTarGz` constructs a custom `IO.FS.Stream` whose `write` pushes through `Gzip.DeflateState`, and passes it to `createFromDir`. `extractTarGz` constructs a custom stream whose `read` pulls compressed data and decompresses through `Gzip.InflateState` with an internal buffer. Both achieve true streaming with bounded memory.

**Path safety**: on extract, the resolved output path is verified to stay within the target directory to prevent traversal attacks.

## Layer 7: ZIP archives (`Zlib/Zip.lean`)

Pure Lean, no new C code. Built on Binary, Checksum, and RawDeflate.

**Structure**: local file headers + data (sequential), central directory, end of central directory record. All integers little-endian.

**Creation**: writes sequentially, tracks byte offset, accumulates central directory entries in memory (small — just metadata), writes CD + EOCD at end. No seeking needed.

**Extraction**: reads whole file into memory and indexes into it. Lean's `IO.FS.Handle` has no `seek`, so this is the pragmatic approach. Fine given the documented <4GB constraint.

**Method selection**: on creation, raw-deflates each file; if the result is smaller, uses method 8 (deflated), otherwise method 0 (stored).

**CRC32 verification**: always verified on extraction.

**Limitations**: no ZIP64 (<4GB per file, <65535 entries), no encryption, no spanning.

## Build system

`lakefile.lean` compiles `c/zlib_ffi.c` into a static library that gets linked into the Lean executable:

1. `input_file zlib_ffi.c` — declares the C source
2. `target zlib_ffi.o` — compiles it with `cc`, passing `-I$(lean include dir)` and `pkg-config --cflags zlib`
3. `extern_lib libzlib_ffi` — archives into a static library
4. Package links with `-lz`

Header discovery: checks `ZLIB_CFLAGS` env var first, falls back to `pkg-config --cflags zlib`. The `-fPIC` flag is added on non-Windows platforms.

## Error handling

All FFI functions return `IO` results. On zlib errors, `mk_zlib_error` formats the error with the zlib message string (from `strm.msg`) or `zError()` code name as fallback. Tar and ZIP use `IO.userError` for format-level errors (path too long, CRC mismatch, unsupported method, etc.).
