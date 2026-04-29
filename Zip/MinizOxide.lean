/-! FFI bindings for [`miniz_oxide`](https://crates.io/crates/miniz_oxide), the
    pure-Rust reimplementation of miniz. Used by the Track D bench harness
    as a runtime/ratio comparator alongside zlib, libdeflate, and zopfli;
    not part of the verified DEFLATE pipeline.

    The Rust crate is opt-in: when `lake build` runs without a working
    `cargo`+`rustc` toolchain, the C shim falls back to a stub that raises
    `IO.userError` containing `"miniz_oxide: not built with Rust support"`.
    See `BENCH.md` for the comparator-toolchain matrix. -/

namespace MinizOxide

/-- Underlying FFI extern for `compress`. Forwards `level` unchanged to the
    Rust shim, which silently treats out-of-range values as level 0 / level
    10. Use `compress` instead — it clamps `level` to the documented 0–9
    range before calling this function. -/
@[extern "lean_miniz_oxide_compress_ffi"]
private opaque compressUnsafe (data : @& ByteArray) (level : UInt8) : IO ByteArray

/-- Compress data using miniz_oxide raw DEFLATE (no zlib header / trailer).
    `level` is the standard DEFLATE level; values above 9 are clamped to 9
    before forwarding to the Rust shim, matching the documented 0–9 range
    used by the rest of the bench. Raises `IO.userError` containing
    `"miniz_oxide: not built with Rust support"` when the comparator
    toolchain was unavailable at build time. -/
def compress (data : @& ByteArray) (level : UInt8 := 6) : IO ByteArray :=
  compressUnsafe data (if level > 9 then 9 else level)

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
