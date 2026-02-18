# Architecture

lean-zlib is a Lean 4 FFI library wrapping zlib. It has four layers, each building on the one below.

## File layout

```
c/zlib_ffi.c      -- All C FFI code (~520 lines)
Zlib/Basic.lean    -- Raw zlib compress/decompress declarations
Zlib/Gzip.lean     -- Gzip declarations + streaming + file helpers
Zlib.lean          -- Re-exports Basic and Gzip
lakefile.lean      -- Build config (pkg-config, static lib, extern link)
Test.lean          -- Roundtrip tests for all API layers
```

## Layer 1: Whole-buffer C functions

Four standalone functions that take an entire `ByteArray`, compress or decompress, and return a new `ByteArray`:

- `lean_zlib_compress` / `lean_zlib_decompress` — raw deflate (zlib format, `inflateInit`/`deflateInit`)
- `lean_gzip_compress` / `lean_gzip_decompress` — gzip format (`deflateInit2` with `MAX_WBITS+16`, `inflateInit2` with `MAX_WBITS+32`)

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

**Deflate** (3 functions):
- `lean_gzip_deflate_new(level)` — allocates state, calls `deflateInit2` with `MAX_WBITS+16`
- `lean_gzip_deflate_push(state, chunk)` — feeds chunk with `Z_NO_FLUSH`, loops until `avail_in == 0`, returns compressed output
- `lean_gzip_deflate_finish(state)` — calls `deflate` with `Z_FINISH` in a loop until `Z_STREAM_END`, then `deflateEnd`

**Inflate** (3 functions):
- `lean_gzip_inflate_new()` — allocates state, calls `inflateInit2` with `MAX_WBITS+32` (auto-detect gzip/zlib)
- `lean_gzip_inflate_push(state, chunk)` — feeds chunk, handles concatenated gzip via `inflateReset`, sets `finished` on clean stream end. Has a progress guard to prevent spinning.
- `lean_gzip_inflate_finish(state)` — calls `inflateEnd` if not already finished, returns empty ByteArray

### Key invariants

- `push` after `finish` returns an error
- `finish` is idempotent (second call returns empty)
- Finalizers are safe regardless of whether `finish` was called
- `push` never passes `Z_FINISH` to zlib — only `finish` does

## Layer 3: Lean streaming declarations

In `Zlib/Gzip.lean`. Each streaming C function gets an `@[extern]` declaration. The state types use the standard Lean opaque external pattern:

```lean
opaque DeflateState.nonemptyType : NonemptyType
def DeflateState : Type := DeflateState.nonemptyType.type
instance : Nonempty DeflateState := DeflateState.nonemptyType.property
```

## Layer 4: Stream piping and file helpers

Pure Lean code in `Zlib/Gzip.lean`, built on Layer 3:

- `compressStream` / `decompressStream` — read 64KB chunks from an `IO.FS.Stream`, push through streaming state, write output. Memory usage is bounded.
- `compressFile` / `decompressFile` — open files, pipe through `compressStream`/`decompressStream`. Output naming: `.gz` appended for compress, `.gz` stripped (or `.ungz` appended) for decompress.

These are `partial` because `repeat` with `break` can't be shown terminating.

## Build system

`lakefile.lean` compiles `c/zlib_ffi.c` into a static library that gets linked into the Lean executable:

1. `input_file zlib_ffi.c` — declares the C source
2. `target zlib_ffi.o` — compiles it with `cc`, passing `-I$(lean include dir)` and `pkg-config --cflags zlib`
3. `extern_lib libzlib_ffi` — archives into a static library
4. Package links with `-lz`

Header discovery: checks `ZLIB_CFLAGS` env var first, falls back to `pkg-config --cflags zlib`. The `-fPIC` flag is added on non-Windows platforms.

## Error handling

All FFI functions return `IO` results. On zlib errors, `mk_zlib_error` formats the error with the zlib message string (from `strm.msg`) or `zError()` code name as fallback.
