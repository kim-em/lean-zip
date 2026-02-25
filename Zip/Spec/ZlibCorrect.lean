import Zip.Native.Gzip
import Zip.Spec.DeflateRoundtrip
import Zip.Spec.BinaryCorrect
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

/-- Decomposition: `compress` = header (2 bytes) ++ deflateRaw ++ trailer (4 bytes). -/
theorem compress_eq (data : ByteArray) (level : UInt8) :
    ∃ (header trailer : ByteArray),
      header.size = 2 ∧ trailer.size = 4 ∧
      compress data level = header ++ Deflate.deflateRaw data level ++ trailer := by
  unfold compress
  split
  · exact ⟨_, _, rfl, rfl, rfl⟩
  · split
    · exact ⟨_, _, rfl, rfl, rfl⟩
    · split
      · exact ⟨_, _, rfl, rfl, rfl⟩
      · exact ⟨_, _, rfl, rfl, rfl⟩

private theorem compress_trailer (data : ByteArray) (level : UInt8) :
    ∃ (header trailer : ByteArray),
      header.size = 2 ∧ trailer.size = 4 ∧
      compress data level = header ++ Deflate.deflateRaw data level ++ trailer ∧
      (trailer[0]!.toUInt32 <<< 24 ||| trailer[1]!.toUInt32 <<< 16 |||
       trailer[2]!.toUInt32 <<< 8 ||| trailer[3]!.toUInt32) =
      Adler32.Native.adler32 1 data := by
  unfold compress
  split
  · exact ⟨_, _, rfl, rfl, rfl, Binary.readUInt32BE_bytes _⟩
  · split
    · exact ⟨_, _, rfl, rfl, rfl, Binary.readUInt32BE_bytes _⟩
    · split
      · exact ⟨_, _, rfl, rfl, rfl, Binary.readUInt32BE_bytes _⟩
      · exact ⟨_, _, rfl, rfl, rfl, Binary.readUInt32BE_bytes _⟩

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
        simp [ByteArray.size_append, hhsz],
    Binary.readUInt32BE_append_right (header ++ Deflate.deflateRaw data level) trailer 0
      (by omega)]
  exact hadler

end ZlibEncode

/-! ## Bitstream composition lemmas -/

/-- `bytesToBits` distributes over ByteArray append. -/
private theorem bytesToBits_append (a b : ByteArray) :
    Deflate.Spec.bytesToBits (a ++ b) =
    Deflate.Spec.bytesToBits a ++ Deflate.Spec.bytesToBits b := by
  simp only [Deflate.Spec.bytesToBits, ByteArray.data_append, Array.toList_append,
    List.flatMap_append]

/-- Dropping `a.size * 8` bits from `bytesToBits (a ++ b ++ c)` gives
    `bytesToBits b ++ bytesToBits c`. -/
private theorem bytesToBits_drop_prefix_three (a b c : ByteArray) :
    (Deflate.Spec.bytesToBits (a ++ b ++ c)).drop (a.size * 8) =
    Deflate.Spec.bytesToBits b ++ Deflate.Spec.bytesToBits c := by
  rw [bytesToBits_append, bytesToBits_append, List.append_assoc,
    ← Deflate.Spec.bytesToBits_length a, List.drop_left]

/-! ## inflateRaw at offset via correctness + completeness -/

/-- If `inflate deflated = .ok data`, then the spec decode succeeds on
    `bytesToBits deflated` with the default fuel (10001). -/
private theorem inflate_to_spec_decode (deflated : ByteArray) (result : ByteArray)
    (h : Inflate.inflate deflated = .ok result) :
    Deflate.Spec.decode (Deflate.Spec.bytesToBits deflated) =
      some result.data.toList := by
  -- Unfold inflate → inflateRaw
  simp only [Inflate.inflate, bind, Except.bind] at h
  cases hinf : Inflate.inflateRaw deflated 0 (1024 * 1024 * 1024) with
  | error e => simp [hinf] at h
  | ok p =>
    simp [hinf, pure, Except.pure] at h
    -- Get bounded fuel from inflate_correct
    obtain ⟨fuel, hfuel_le, hdec⟩ :=
      Deflate.Correctness.inflate_correct deflated 0 (1024 * 1024 * 1024) p.1 p.2
        (by rw [hinf])
    simp at hdec
    -- hdec : decode (bytesToBits deflated) fuel = some p.1.data.toList
    -- Lift fuel to 10001 via fuel independence
    have h10001 : fuel + (10001 - fuel) = 10001 := by omega
    rw [← h]
    rw [show (10001 : Nat) = fuel + (10001 - fuel) from h10001.symm]
    exact Deflate.Spec.decode_fuel_independent _ _ _ hdec _

/-- Zlib roundtrip: decompressing the output of compress returns the original data.
    The size bound (500M) is inherited from `inflate_deflateRaw`. -/
theorem zlib_decompressSingle_compress (data : ByteArray) (level : UInt8)
    (hsize : data.size < 500000000) :
    ZlibDecode.decompressSingle (ZlibEncode.compress data level) = .ok data := by
  -- DEFLATE roundtrip: inflate ∘ deflateRaw = id
  have hinfl : Inflate.inflate (Deflate.deflateRaw data level) = .ok data :=
    Deflate.inflate_deflateRaw data level hsize
  -- Spec decode on deflated with default fuel (10001)
  have hspec_go : Deflate.Spec.decode.go
      (Deflate.Spec.bytesToBits (Deflate.deflateRaw data level)) [] 10001 =
      some data.data.toList := by
    have := inflate_to_spec_decode _ data hinfl
    simp only [Deflate.Spec.decode] at this; exact this
  -- Suffix invariance: spec decode ignores trailer bits after the DEFLATE stream
  have hspec_compressed : ∀ (header trailer : ByteArray) (hh : header.size = 2),
      Deflate.Spec.decode.go
        ((Deflate.Spec.bytesToBits (header ++ Deflate.deflateRaw data level ++ trailer)).drop
          (2 * 8)) [] 10001 = some data.data.toList := by
    intro header trailer hh
    rw [show 2 * 8 = header.size * 8 from by omega,
        bytesToBits_drop_prefix_three]
    exact Deflate.Spec.decode_go_suffix _ _ [] 10001 _
      (by rw [Deflate.Spec.bytesToBits_length]; omega)
      hspec_go
  -- Use data.size bound to get result.length ≤ maxOutputSize
  have hdata_le : data.data.toList.length ≤ 1024 * 1024 * 1024 := by
    simp [Array.length_toList, ByteArray.size_data]; omega
  -- Spec decode on compressed bits at offset 2 (via compress_eq decomposition)
  have hspec_at2 : Deflate.Spec.decode.go
      ((Deflate.Spec.bytesToBits (ZlibEncode.compress data level)).drop (2 * 8))
      [] 10001 = some data.data.toList := by
    obtain ⟨header, trailer, hhsz, _, hceq⟩ := ZlibEncode.compress_eq data level
    rw [hceq]
    exact hspec_compressed header trailer hhsz
  -- Apply inflateRaw_complete to get native inflateRaw at offset 2
  obtain ⟨endPos, hinflRaw⟩ :=
    inflateRaw_complete _ 2 _ data.data.toList hdata_le 10001 (by omega) hspec_at2
  -- compressed size ≥ 6 (from compress = 2 + deflated + 4)
  have hcsz6 : ¬ (ZlibEncode.compress data level).size < 6 := by
    rw [ZlibEncode.compress_size]; omega
  -- Decompose compress and establish endPos exactness
  obtain ⟨header, trailer, hhsz, htsz, hceq⟩ := ZlibEncode.compress_eq data level
  -- Spec decode on (header ++ deflated) at offset 2
  have hspec_hd : Deflate.Spec.decode.go
      ((Deflate.Spec.bytesToBits (header ++ Deflate.deflateRaw data level)).drop (2 * 8))
      [] 10001 = some data.data.toList := by
    rw [show 2 * 8 = header.size * 8 from by omega]
    rw [bytesToBits_append, ← Deflate.Spec.bytesToBits_length header, List.drop_left]
    exact hspec_go
  -- Apply inflateRaw_complete on (header ++ deflated) to get endPos'
  obtain ⟨endPos', hinflRaw'⟩ :=
    inflateRaw_complete (header ++ Deflate.deflateRaw data level) 2 _
      data.data.toList hdata_le 10001 (by omega) hspec_hd
  -- By suffix invariance, inflateRaw on full compressed data gives same endPos'
  have hinflRaw'' : Inflate.inflateRaw ((header ++ Deflate.deflateRaw data level) ++ trailer)
      2 (1024 * 1024 * 1024) = .ok (⟨⟨data.data.toList⟩⟩, endPos') :=
    inflateRaw_append_suffix _ trailer 2 _ _ _ hinflRaw'
  -- endPos' = endPos by injectivity
  have hep_eq : endPos = endPos' := by
    rw [hceq] at hinflRaw
    have := hinflRaw.symm.trans hinflRaw''
    simp only [Except.ok.injEq, Prod.mk.injEq] at this
    exact this.2
  -- endPos exactness via inflateRaw_endPos_eq
  have hep_exact : endPos' = (header ++ Deflate.deflateRaw data level).size := by
    have h' : Inflate.inflateRaw (header ++ Deflate.deflateRaw data level)
        header.size (1024 * 1024 * 1024) = .ok (⟨⟨data.data.toList⟩⟩, endPos') := by
      rw [hhsz]; exact hinflRaw'
    exact inflateRaw_endPos_eq header (Deflate.deflateRaw data level) _ _ _ h'
      hspec_go (Deflate.deflateRaw_pad data level) hdata_le
  have hep_val : endPos = 2 + (Deflate.deflateRaw data level).size := by
    rw [hep_eq, hep_exact, ByteArray.size_append, hhsz]
  -- Tight endPos bound
  have hendPos_tight : endPos + 4 ≤ (ZlibEncode.compress data level).size := by
    rw [hep_val, hceq]
    simp only [ByteArray.size_append, htsz, hhsz]; omega
  have hendPos4 : ¬ (endPos + 4 > (ZlibEncode.compress data level).size) := by omega
  have hba_eq : (⟨⟨data.data.toList⟩⟩ : ByteArray) = data := by simp
  -- Adler32 trailer match: use endPos = 2 + deflated.size to read trailer bytes
  have hadler : (Adler32.Native.adler32 1 data ==
    (ZlibEncode.compress data level)[endPos]!.toUInt32 <<< 24 |||
      (ZlibEncode.compress data level)[endPos + 1]!.toUInt32 <<< 16 |||
      (ZlibEncode.compress data level)[endPos + 2]!.toUInt32 <<< 8 |||
      (ZlibEncode.compress data level)[endPos + 3]!.toUInt32) = true := by
    rw [hep_val, ZlibEncode.compress_adler32]
    simp [BEq.beq]
  set_option maxRecDepth 8192 in
  simp only [ZlibDecode.decompressSingle, - ZlibDecode.decompressSingle.eq_1,
    bind, Except.bind, hcsz6, ↓reduceIte, pure, Except.pure,
    ZlibEncode.compress_header_check data level,
    ZlibEncode.compress_cm data level,
    ZlibEncode.compress_cinfo data level,
    ZlibEncode.compress_no_fdict data level,
    hinflRaw, hendPos4, hba_eq, hadler]

end Zip.Native
