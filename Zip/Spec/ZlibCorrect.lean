import Zip.Native.Gzip
import Zip.Spec.DeflateRoundtrip
import ZipCommon.Spec.BinaryCorrect
import Zip.Spec.DeflateSuffix
import Zip.Spec.InflateComplete
import Zip.Spec.GzipCorrect

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
    (maxOutputSize : Nat := 1024 * 1024 * 1024) :
    Except String ByteArray := do
  if data.size < 6 then throw "Zlib: input too short"
  let cmf := data[0]!
  let flg := data[1]!
  let check := cmf.toUInt16 * 256 + flg.toUInt16
  unless check % 31 == 0 do throw "Zlib: header check failed"
  unless cmf &&& 0x0F == 8 do throw "Zlib: unsupported compression method"
  unless cmf >>> 4 ≤ 7 do throw "Zlib: invalid window size"
  unless flg &&& 0x20 == 0 do throw "Zlib: preset dictionaries not supported"
  let (decompressed, endPos) ← Inflate.inflateRawReference data 2 maxOutputSize
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
  repeat (first | decide | split)

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
  repeat (first | decide | split)

/-- Decomposition: `compress` = header (2 bytes) ++ deflateRaw ++ trailer (4 bytes). -/
theorem compress_eq (data : ByteArray) (level : UInt8) :
    ∃ (header trailer : ByteArray),
      header.size = 2 ∧ trailer.size = 4 ∧
      compress data level = header ++ Deflate.deflateRaw data level ++ trailer := by
  unfold compress
  repeat (first | exact ⟨_, _, rfl, rfl, rfl⟩ | split)

private theorem compress_trailer (data : ByteArray) (level : UInt8) :
    ∃ (header trailer : ByteArray),
      header.size = 2 ∧ trailer.size = 4 ∧
      compress data level = header ++ Deflate.deflateRaw data level ++ trailer ∧
      (trailer[0]!.toUInt32 <<< 24 ||| trailer[1]!.toUInt32 <<< 16 |||
       trailer[2]!.toUInt32 <<< 8 ||| trailer[3]!.toUInt32) =
      Adler32.Native.adler32 1 data := by
  unfold compress
  repeat (first | exact ⟨_, _, rfl, rfl, rfl, Binary.readUInt32BE_bytes _⟩ | split)

/-- Adler32 trailer match: reading 4 bytes big-endian at endPos gives `adler32 1 data`. -/
theorem compress_adler32 (data : ByteArray) (level : UInt8) :
    let c := compress data level
    let ep := 2 + (Deflate.deflateRaw data level).size
    (c[ep]!.toUInt32 <<< 24 ||| c[ep + 1]!.toUInt32 <<< 16 |||
     c[ep + 2]!.toUInt32 <<< 8 ||| c[ep + 3]!.toUInt32) =
    Adler32.Native.adler32 1 data := by
  obtain ⟨header, trailer, hhsz, htsz, hceq, hadler⟩ := compress_trailer data level
  simp only
  rw [hceq,
    show 2 + (Deflate.deflateRaw data level).size =
      (header ++ Deflate.deflateRaw data level).size + 0 from by
        simp only [ByteArray.size_append, hhsz, Nat.add_zero],
    Binary.readUInt32BE_append_right (header ++ Deflate.deflateRaw data level) trailer 0
      (by omega)]
  exact hadler

end ZlibEncode

/-- Zlib roundtrip: decompressing the output of compress returns the original data.
    Parametric in the decoder's `maxOutputSize`: holds whenever the input fits
    under the cap (`data.size ≤ maxOutputSize`). -/
theorem zlib_decompressSingle_compress (data : ByteArray) (level : UInt8)
    (maxOutputSize : Nat) (hsize : data.size ≤ maxOutputSize) :
    ZlibDecode.decompressSingle (ZlibEncode.compress data level) maxOutputSize = .ok data := by
  -- DEFLATE roundtrip: inflate ∘ deflateRaw = id
  have hinfl : Inflate.inflateReference (Deflate.deflateRaw data level) maxOutputSize = .ok data :=
    Deflate.inflateReference_deflateRaw data level _ hsize
  -- Spec decode on deflated
  have hspec_go : Deflate.Spec.decode.go
      (Deflate.Spec.bytesToBits (Deflate.deflateRaw data level)) [] =
      some data.data.toList :=
    inflate_to_spec_decode _ data maxOutputSize hinfl
  -- Use data.size bound to get result.length ≤ maxOutputSize
  have hdata_le : data.data.toList.length ≤ maxOutputSize := by
    simp only [Array.length_toList, ByteArray.size_data]; omega
  -- compressed size ≥ 6 (from compress = 2 + deflated + 4)
  have hcsz6 : ¬ (ZlibEncode.compress data level).size < 6 := by
    rw [ZlibEncode.compress_size]; omega
  -- Native inflate at offset 2 consumes exactly the DEFLATE stream (framing lemma)
  obtain ⟨header, trailer, hhsz, _, hceq⟩ := ZlibEncode.compress_eq data level
  have hinflRaw : Inflate.inflateRawReference (ZlibEncode.compress data level) 2 maxOutputSize =
      .ok (⟨⟨data.data.toList⟩⟩, 2 + (Deflate.deflateRaw data level).size) := by
    rw [hceq]
    exact inflateRaw_framing data level maxOutputSize header trailer 2 hhsz hdata_le hspec_go
  have hendPos4 : ¬ (2 + (Deflate.deflateRaw data level).size + 4 >
      (ZlibEncode.compress data level).size) := by
    rw [ZlibEncode.compress_size]; omega
  have hba_eq : (⟨⟨data.data.toList⟩⟩ : ByteArray) = data := by simp only [Array.toArray_toList]
  -- Adler32 trailer match: the trailer at 2 + deflated.size reads adler32 1 data
  have hadler : (Adler32.Native.adler32 1 data ==
    (ZlibEncode.compress data level)[2 + (Deflate.deflateRaw data level).size]!.toUInt32 <<< 24 |||
      (ZlibEncode.compress data level)[2 + (Deflate.deflateRaw data level).size + 1]!.toUInt32 <<< 16 |||
      (ZlibEncode.compress data level)[2 + (Deflate.deflateRaw data level).size + 2]!.toUInt32 <<< 8 |||
      (ZlibEncode.compress data level)[2 + (Deflate.deflateRaw data level).size + 3]!.toUInt32) = true := by
    rw [ZlibEncode.compress_adler32]
    simp only [BEq.beq, decide_true]
  set_option maxRecDepth 8192 in
  simp only [ZlibDecode.decompressSingle, - ZlibDecode.decompressSingle.eq_1,
    bind, Except.bind, hcsz6, ↓reduceIte, pure, Except.pure,
    ZlibEncode.compress_header_check data level,
    ZlibEncode.compress_cm data level,
    ZlibEncode.compress_cinfo data level,
    ZlibEncode.compress_no_fdict data level,
    hinflRaw, hendPos4, hba_eq, hadler]

end Zip.Native
