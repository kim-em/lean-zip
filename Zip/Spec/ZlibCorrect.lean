import Zip.Native.Gzip
import Zip.Spec.DeflateRoundtrip
import Zip.Spec.BinaryCorrect
import Zip.Spec.DeflateSuffix
import Zip.Spec.InflateComplete

/-!
# Zlib framing roundtrip (RFC 1950)

Pure single-stream zlib decoder and roundtrip theorem connecting
`ZlibEncode.compress` with `ZlibDecode.decompressSingle`.

The encoder always sets FDICT=0 and uses a simple 2-byte header, so
`decompressSingle` only handles that case — it is simpler than the full
`ZlibDecode.decompress` which uses `let mut pos`.
-/

namespace Zip.Native

namespace ZlibDecode

/-- Pure zlib decompressor for single-stream data (no preset dictionary).
    Proof-friendly: no for/while/mut. -/
def decompressSingle (data : ByteArray)
    (maxOutputSize : Nat := 256 * 1024 * 1024) :
    Except String ByteArray := do
  if data.size < 6 then throw "Zlib: input too short"
  let cmf := data[0]!
  let flg := data[1]!
  let check := cmf.toUInt16 * 256 + flg.toUInt16
  unless check % 31 == 0 do throw "Zlib: header check failed"
  unless cmf &&& 0x0F == 8 do throw "Zlib: unsupported compression method"
  unless cmf >>> 4 ≤ 7 do throw "Zlib: invalid window size"
  unless flg &&& 0x20 == 0 do throw "Zlib: preset dictionaries not supported"
  let (decompressed, endPos) ← Inflate.inflateRaw data 2 maxOutputSize
  if endPos + 4 > data.size then throw "Zlib: truncated trailer"
  let b0 := data[endPos]!.toUInt32
  let b1 := data[endPos + 1]!.toUInt32
  let b2 := data[endPos + 2]!.toUInt32
  let b3 := data[endPos + 3]!.toUInt32
  let expectedAdler := (b0 <<< 24) ||| (b1 <<< 16) ||| (b2 <<< 8) ||| b3
  let actualAdler := Adler32.Native.adler32 1 decompressed
  unless actualAdler == expectedAdler do throw "Zlib: Adler32 mismatch"
  return decompressed

end ZlibDecode

namespace ZlibEncode

private theorem zlib_header_size (a b : UInt8) :
    (ByteArray.mk #[a, b]).size = 2 := rfl

private theorem zlib_trailer_size (a b c d : UInt8) :
    (ByteArray.mk #[a, b, c, d]).size = 4 := rfl

/-- Total size of `compress` output. -/
theorem compress_size (data : ByteArray) (level : UInt8) :
    (compress data level).size = 2 + (Deflate.deflateRaw data level).size + 4 := by
  unfold compress
  simp only [ByteArray.size_append]
  rw [zlib_header_size, zlib_trailer_size]

/-- The CMF byte of the compressed output is 0x78. -/
theorem compress_cmf (data : ByteArray) (level : UInt8) :
    (compress data level)[0]! = 0x78 := by
  unfold compress
  rw [Binary.getElem!_append_left _ _ 0 (by
    simp only [ByteArray.size_append]; rw [zlib_header_size]; omega)]
  rw [Binary.getElem!_append_left _ _ 0 (by rw [zlib_header_size]; omega)]
  split <;> first | rfl | (split <;> first | rfl | (split <;> rfl))

/-- The header checksum of the compressed output is valid: (CMF*256 + FLG) % 31 == 0. -/
theorem compress_header_check (data : ByteArray) (level : UInt8) :
    let c := compress data level
    (c[0]!.toUInt16 * (256 : UInt16) + c[1]!.toUInt16) % (31 : UInt16) == (0 : UInt16) := by
  unfold compress
  simp only []
  rw [Binary.getElem!_append_left _ _ 0 (by
        simp only [ByteArray.size_append]; rw [zlib_header_size]; omega),
      Binary.getElem!_append_left _ _ 0 (by rw [zlib_header_size]; omega),
      Binary.getElem!_append_left _ _ 1 (by
        simp only [ByteArray.size_append]; rw [zlib_header_size]; omega),
      Binary.getElem!_append_left _ _ 1 (by rw [zlib_header_size]; omega)]
  -- Split on all four flevel branches to get concrete values
  split
  · decide
  · split
    · decide
    · split
      · decide
      · decide

/-- The CM field (low nibble of CMF) is 8. -/
theorem compress_cm (data : ByteArray) (level : UInt8) :
    (compress data level)[0]! &&& 0x0F == 8 := by
  rw [compress_cmf]; decide

/-- The CINFO field (high nibble of CMF) is 7 ≤ 7. -/
theorem compress_cinfo (data : ByteArray) (level : UInt8) :
    (compress data level)[0]! >>> 4 ≤ 7 := by
  rw [compress_cmf]; decide

/-- FDICT bit is not set. -/
theorem compress_no_fdict (data : ByteArray) (level : UInt8) :
    (compress data level)[1]! &&& 0x20 == 0 := by
  unfold compress
  rw [Binary.getElem!_append_left _ _ 1 (by
        simp only [ByteArray.size_append]; rw [zlib_header_size]; omega),
      Binary.getElem!_append_left _ _ 1 (by rw [zlib_header_size]; omega)]
  split
  · decide
  · split
    · decide
    · split
      · decide
      · decide

end ZlibEncode

/-- Zlib roundtrip: decompressing the output of compress returns the original data.
    The size bound (5M) is inherited from `inflate_deflateRaw`. -/
theorem zlib_decompressSingle_compress (data : ByteArray) (level : UInt8)
    (hsize : data.size < 5000000) :
    ZlibDecode.decompressSingle (ZlibEncode.compress data level) = .ok data := by
  sorry

end Zip.Native
