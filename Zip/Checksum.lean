/-! CRC32 and Adler32 checksum computation via zlib FFI,
    with support for incremental (chunk-based) checksumming. -/
namespace Checksum

/-- Compute CRC32 checksum. Supports incremental computation:
    pass the result of a previous call as `init` to continue over multiple chunks. -/
@[extern "lean_zlib_crc32"]
opaque crc32 (init : UInt32 := 0) (data : @& ByteArray) : UInt32

/-- Compute Adler32 checksum. Supports incremental computation:
    pass the result of a previous call as `init` to continue over multiple chunks. -/
@[extern "lean_zlib_adler32"]
opaque adler32 (init : UInt32 := 1) (data : @& ByteArray) : UInt32

end Checksum
