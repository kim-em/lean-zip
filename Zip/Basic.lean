/-! FFI bindings to zlib compression/decompression (RFC 1950). -/
namespace Zlib

/-- Compress data using zlib (raw deflate, no gzip header).
    `level` ranges from 0 (no compression) to 9 (best compression), default 6. -/
@[extern "lean_zlib_compress"]
opaque compress (data : @& ByteArray) (level : UInt8 := 6) : IO ByteArray

/-- Decompress zlib-compressed data.
    `maxDecompressedSize` caps output size; default 1 GiB; pass `0` to opt
    into unlimited mode (bomb-unsafe for untrusted input). Overflow raises
    `IO.userError` containing `"decompressed size exceeds limit"`.
    See `SECURITY_INVENTORY.md` *Decompression Limit Inventory*. -/
@[extern "lean_zlib_decompress"]
opaque decompress (data : @& ByteArray)
    (maxDecompressedSize : UInt64 := 1024 * 1024 * 1024) : IO ByteArray

end Zlib
