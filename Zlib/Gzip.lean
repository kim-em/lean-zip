namespace Gzip

/-- Compress data in gzip format (with gzip header/trailer, compatible with `gzip`/`gunzip`).
    `level` ranges from 0 (no compression) to 9 (best compression), default 6. -/
@[extern "lean_gzip_compress"]
opaque compress (data : @& ByteArray) (level : UInt8 := 6) : IO ByteArray

/-- Decompress gzip data. Also handles concatenated gzip streams and raw zlib data. -/
@[extern "lean_gzip_decompress"]
opaque decompress (data : @& ByteArray) : IO ByteArray

end Gzip
