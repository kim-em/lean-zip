namespace Zlib

/-- Compress data using zlib (raw deflate, no gzip header).
    `level` ranges from 0 (no compression) to 9 (best compression), default 6. -/
@[extern "lean_zlib_compress"]
opaque compress (data : @& ByteArray) (level : UInt8 := 6) : IO ByteArray

/-- Decompress zlib-compressed data. -/
@[extern "lean_zlib_decompress"]
opaque decompress (data : @& ByteArray) : IO ByteArray

end Zlib
