/-! # zopfli FFI (Track D maximum-ratio reference comparator)

Bindings to [zopfli](https://github.com/google/zopfli) — Google's exhaustive
DEFLATE encoder. It is the compression-*ratio* ceiling in the Track D dashboard:
much slower than zlib/libdeflate, but produces the smallest standard-DEFLATE
output. Compression only — its output is ordinary raw DEFLATE, decoded by any
inflate (native, zlib, libdeflate).

Gated at the C level behind `HAVE_ZOPFLI`; without the library the shim raises
`IO.userError` containing `"zopfli: not built with"`. -/

namespace Zopfli

@[extern "lean_zopfli_compress_ffi"]
private opaque compressUnsafe (data : @& ByteArray) (iterations : UInt32) : IO ByteArray

/-- Raw DEFLATE compression via zopfli. `iterations` is zopfli's `numiterations`
    knob (more = smaller + slower); `0` uses zopfli's default of 15. -/
def compress (data : @& ByteArray) (iterations : UInt32 := 0) : IO ByteArray :=
  compressUnsafe data iterations

end Zopfli
