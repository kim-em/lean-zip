/-! FFI bindings for [`miniz_oxide`](https://crates.io/crates/miniz_oxide), the
    pure-Rust reimplementation of miniz. Used by the Track D bench harness
    as a runtime/ratio comparator alongside zlib, libdeflate, and zopfli;
    not part of the verified DEFLATE pipeline.

    The Rust crate is opt-in: when `lake build` runs without a working
    `cargo`+`rustc` toolchain, the C shim falls back to a stub that raises
    `IO.userError` containing `"miniz_oxide: not built with Rust support"`.
    See `BENCH.md` for the comparator-toolchain matrix. -/

namespace MinizOxide

/-- Compress data using miniz_oxide raw DEFLATE (no zlib header / trailer).
    `level` is the standard DEFLATE level 0–10 that miniz_oxide accepts; we
    cap callers to 0–9 here to match the rest of the bench. Raises
    `IO.userError` containing `"miniz_oxide: not built with Rust support"`
    when the comparator toolchain was unavailable at build time. -/
@[extern "lean_miniz_oxide_compress_ffi"]
opaque compress (data : @& ByteArray) (level : UInt8 := 6) : IO ByteArray

/-- Decompress raw DEFLATE data using miniz_oxide.
    `maxDecompressedSize` caps the output (default 1 GiB; pass `0` to opt
    into unlimited mode — bomb-unsafe for untrusted input). Overflow
    raises `IO.userError` containing `"exceeds limit"`. Disabled
    builds raise an error containing `"miniz_oxide: not built with Rust
    support"`. -/
@[extern "lean_miniz_oxide_decompress_ffi"]
opaque decompress (data : @& ByteArray)
    (maxDecompressedSize : UInt64 := 1024 * 1024 * 1024) : IO ByteArray

end MinizOxide
