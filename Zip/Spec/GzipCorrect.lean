import Zip.Native.Gzip
import Zip.Spec.DeflateRoundtrip
import Zip.Spec.BinaryCorrect

/-!
# Gzip framing roundtrip (RFC 1952)

Pure single-member gzip decoder and roundtrip theorem connecting
`GzipEncode.compress` with `GzipDecode.decompressSingle`.

The encoder always sets FLG=0 (no extra fields, no filename, no comment,
no header CRC), so `decompressSingle` only handles that case — it is
simpler than the full `GzipDecode.decompress` which supports flags and
concatenated members.
-/

namespace Zip.Native

namespace GzipDecode

/-- Pure gzip decompressor for single-member streams (no FLG bits set).
    Proof-friendly: no for/while/mut. -/
def decompressSingle (data : ByteArray)
    (maxOutputSize : Nat := 256 * 1024 * 1024) :
    Except String ByteArray := do
  if data.size < 18 then throw "Gzip: input too short"
  unless data[0]! == 0x1f && data[1]! == 0x8b do throw "Gzip: invalid magic"
  unless data[2]! == 8 do throw "Gzip: unsupported compression method"
  let flg := data[3]!
  unless flg == 0 do throw "Gzip: unsupported flags (single-member only)"
  -- Skip MTIME (4) + XFL (1) + OS (1) = 6 bytes at offset 4–9
  -- Inflate the DEFLATE stream starting at byte 10
  let (decompressed, endPos) ← Inflate.inflateRaw data 10 maxOutputSize
  -- Parse trailer at endPos: CRC32 (4 bytes LE) + ISIZE (4 bytes LE)
  if endPos + 8 > data.size then throw "Gzip: truncated trailer"
  let expectedCrc := Binary.readUInt32LE data endPos
  let expectedSize := Binary.readUInt32LE data (endPos + 4)
  let actualCrc := Crc32.Native.crc32 0 decompressed
  unless actualCrc == expectedCrc do throw "Gzip: CRC32 mismatch"
  unless decompressed.size.toUInt32 == expectedSize do throw "Gzip: size mismatch"
  return decompressed

end GzipDecode

private theorem getElem!_ba_append_left (a b : ByteArray) (i : Nat) (h : i < a.size) :
    (a ++ b)[i]! = a[i]! := by
  rw [getElem!_pos (a ++ b) i (by simp [ByteArray.size_append]; omega),
      getElem!_pos a i h]
  exact ByteArray.getElem_append_left h

namespace GzipEncode

private theorem gzip_header_size (x : UInt8) :
    (ByteArray.mk #[0x1f, 0x8b, 8, 0, 0, 0, 0, 0, x, 0xFF]).size = 10 := rfl

private theorem gzip_trailer_size (a b c d e f g h : UInt8) :
    (ByteArray.mk #[a, b, c, d, e, f, g, h]).size = 8 := rfl

/-- Total size of `compress` output. -/
theorem compress_size (data : ByteArray) (level : UInt8) :
    (compress data level).size = 10 + (Deflate.deflateRaw data level).size + 8 := by
  unfold compress
  simp only [ByteArray.size_append]
  rw [gzip_header_size, gzip_trailer_size]

/-- The first four header bytes of the compressed output are [0x1f, 0x8b, 8, 0]. -/
theorem compress_header_bytes (data : ByteArray) (level : UInt8) :
    (compress data level)[0]! = 0x1f ∧
    (compress data level)[1]! = 0x8b ∧
    (compress data level)[2]! = 8 ∧
    (compress data level)[3]! = 0 := by
  unfold compress
  have hhs : ∀ (x : UInt8),
      (ByteArray.mk #[0x1f, 0x8b, 8, 0, 0, 0, 0, 0, x, 0xFF]).size = 10 := fun _ => rfl
  refine ⟨?_, ?_, ?_, ?_⟩ <;> {
    rw [getElem!_ba_append_left _ _ _ (by
      simp only [ByteArray.size_append]; split <;> (rw [hhs]; omega))]
    rw [getElem!_ba_append_left _ _ _ (by split <;> (rw [hhs]; omega))]
    split <;> first | rfl | (split <;> rfl)
  }

end GzipEncode

/-- Gzip roundtrip: decompressing the output of compress returns the original data.
    The size bound (5M) is inherited from `inflate_deflateRaw`. -/
theorem gzip_decompressSingle_compress (data : ByteArray) (level : UInt8)
    (hsize : data.size < 5000000) :
    GzipDecode.decompressSingle (GzipEncode.compress data level) = .ok data := by
  sorry

end Zip.Native
