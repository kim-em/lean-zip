import Zip.RawDeflate

/-! FFI binding for [zopfli](https://github.com/google/zopfli) — Google's
maximum-compression DEFLATE encoder.

Zopfli is encode-only (no decompressor) and intentionally ~100× slower than
zlib level 9. It produces strictly DEFLATE-compatible output, just smaller.
Used as the compression-ratio quality ceiling in Track D benchmarks; not on
any production hot path. -/

namespace Zopfli

/-- Compress `data` with zopfli using raw DEFLATE framing (no header/trailer,
    matching `RawDeflate.compress`).

    `iterations` is zopfli's moral equivalent of zlib's compression level:
    more iterations of forward/backward LZ77 cost optimization → better
    compression at the cost of runtime. Defaults to `15` (zopfli's recommended
    default for small files); `1` is fastest, more is better. Must be ≥ 1. -/
@[extern "lean_zopfli_deflate"]
opaque compress (data : @& ByteArray) (iterations : UInt32 := 15) : IO ByteArray

end Zopfli
