/-! FFI bindings for libdeflate (raw DEFLATE only).

    Track D Phase 0a comparator: libdeflate is an optimised C DEFLATE
    library, often faster than zlib at higher compression ratios. Wired
    here as an unverified runtime/ratio reference point — no equivalence
    proofs, no streaming API (libdeflate provides whole-buffer only). -/

namespace Libdeflate

/-- Compress data using raw DEFLATE via libdeflate.
    `level` ranges from 0 (no compression) to 12 (slowest, best). Levels
    0..9 match the zlib scale; 10..12 are libdeflate-only. Default 6. -/
@[extern "lean_libdeflate_compress"]
opaque compress (data : @& ByteArray) (level : UInt8 := 6) : IO ByteArray

/-- Decompress raw DEFLATE data via libdeflate.
    `maxDecompressedSize` caps output size; default 1 GiB; pass `0` to opt
    into unlimited mode (bomb-unsafe for untrusted input). Overflow raises
    `IO.userError` containing `"decompressed size exceeds limit"`. -/
@[extern "lean_libdeflate_decompress"]
opaque decompress (data : @& ByteArray)
    (maxDecompressedSize : UInt64 := 1024 * 1024 * 1024) : IO ByteArray

end Libdeflate
