/-! # libdeflate FFI (Track D reference comparator)

Bindings to the [libdeflate](https://github.com/ebiggers/libdeflate) C library —
an optimized DEFLATE implementation, used as the runtime "speed bar" in the
Track D benchmark dashboard (see `BENCH.md` / `bench/README.md`).

These are gated at the C level behind `HAVE_LIBDEFLATE`; without the library the
shims raise `IO.userError` containing `"libdeflate: not built with"`, so callers
can treat that substring as a clean skip. Compression is raw DEFLATE at levels
1–12. -/

namespace Libdeflate

@[extern "lean_libdeflate_compress_ffi"]
private opaque compressUnsafe (data : @& ByteArray) (level : UInt8) : IO ByteArray

/-- Raw DEFLATE compression via libdeflate. `level` is clamped to libdeflate's
    valid range (1–12). -/
def compress (data : @& ByteArray) (level : UInt8 := 6) : IO ByteArray :=
  compressUnsafe data (if level == 0 then 1 else if level > 12 then 12 else level)

/-- Raw DEFLATE decompression via libdeflate. `maxDecompressedSize` bounds the
    output buffer. -/
@[extern "lean_libdeflate_decompress_ffi"]
opaque decompress (data : @& ByteArray)
    (maxDecompressedSize : UInt64 := 1024 * 1024 * 1024) : IO ByteArray

end Libdeflate
