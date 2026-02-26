import Zip.Native.Gzip
import Zip.Spec.DeflateRoundtrip
import Zip.Spec.BinaryCorrect
import Zip.Spec.DeflateSuffix
import Zip.Spec.InflateLoopBounds
import Zip.Spec.InflateRawSuffix

/-!
# Gzip framing roundtrip (RFC 1952)

Pure single-member gzip decoder and roundtrip theorem connecting
`GzipEncode.compress` with `GzipDecode.decompressSingle`.

The encoder always sets FLG=0 (no extra fields, no filename, no comment,
no header CRC), so `decompressSingle` only handles that case — it is
simpler than the full `GzipDecode.decompress` which supports flags and
concatenated members.

BitReader invariant preservation is in `BitReaderInvariant.lean`.
endPos bounds and completeness are in `InflateLoopBounds.lean`.
Suffix invariance is in `InflateRawSuffix.lean`.
-/

namespace Zip.Native

namespace GzipDecode

/-- Pure gzip decompressor for single-member streams (no FLG bits set).
    Proof-friendly: no for/while/mut. -/
def decompressSingle (data : ByteArray)
    (maxOutputSize : Nat := 1024 * 1024 * 1024) :
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

/-- Decomposition: `compress` = header (10 bytes) ++ deflateRaw ++ trailer (8 bytes). -/
theorem compress_eq (data : ByteArray) (level : UInt8) :
    ∃ (header trailer : ByteArray),
      header.size = 10 ∧ trailer.size = 8 ∧
      compress data level = header ++ Deflate.deflateRaw data level ++ trailer := by
  simp only [compress]
  split
  · exact ⟨_, _, rfl, rfl, rfl⟩
  · split
    · exact ⟨_, _, rfl, rfl, rfl⟩
    · exact ⟨_, _, rfl, rfl, rfl⟩

/-- Decomposition with concrete trailer: `compress` = header(10) ++ deflateRaw ++ trailer
    where `readUInt32LE trailer 0 = crc32 0 data` and `readUInt32LE trailer 4 = isize`. -/
private theorem compress_trailer (data : ByteArray) (level : UInt8) :
    ∃ (header trailer : ByteArray),
      header.size = 10 ∧ trailer.size = 8 ∧
      compress data level = header ++ Deflate.deflateRaw data level ++ trailer ∧
      Binary.readUInt32LE trailer 0 = Crc32.Native.crc32 0 data ∧
      Binary.readUInt32LE trailer 4 = data.size.toUInt32 := by
  unfold compress
  split
  · exact ⟨_, _, rfl, rfl, rfl, Binary.readUInt32LE_bytes _, Binary.readUInt32LE_bytes _⟩
  · split
    · exact ⟨_, _, rfl, rfl, rfl, Binary.readUInt32LE_bytes _, Binary.readUInt32LE_bytes _⟩
    · exact ⟨_, _, rfl, rfl, rfl, Binary.readUInt32LE_bytes _, Binary.readUInt32LE_bytes _⟩

/-- CRC32 trailer match: `readUInt32LE` at endPos reads `crc32 0 data`. -/
theorem compress_crc32 (data : ByteArray) (level : UInt8) :
    Binary.readUInt32LE (compress data level)
      (10 + (Deflate.deflateRaw data level).size) =
    Crc32.Native.crc32 0 data := by
  obtain ⟨header, trailer, hhsz, htsz, hceq, hcrc, _⟩ := compress_trailer data level
  rw [hceq, show 10 + (Deflate.deflateRaw data level).size =
    header.size + (Deflate.deflateRaw data level).size + 0 from by omega,
    Binary.readUInt32LE_append3_right _ _ _ 0 (by omega)]
  exact hcrc

/-- ISIZE trailer match: `readUInt32LE` at endPos+4 reads `data.size.toUInt32`. -/
theorem compress_isize (data : ByteArray) (level : UInt8) :
    Binary.readUInt32LE (compress data level)
      (10 + (Deflate.deflateRaw data level).size + 4) =
    data.size.toUInt32 := by
  obtain ⟨header, trailer, hhsz, htsz, hceq, _, hisize⟩ := compress_trailer data level
  rw [hceq, show 10 + _ + 4 = header.size + (Deflate.deflateRaw data level).size + 4
    from by omega]
  rw [Binary.readUInt32LE_append3_right _ _ _ 4 (by omega)]
  exact hisize

end GzipEncode

/-! ## ByteArray/bitstream composition lemmas -/

/-- `bytesToBits` distributes over ByteArray append. -/
private theorem bytesToBits_append (a b : ByteArray) :
    Deflate.Spec.bytesToBits (a ++ b) =
    Deflate.Spec.bytesToBits a ++ Deflate.Spec.bytesToBits b := by
  simp only [Deflate.Spec.bytesToBits, ByteArray.data_append, Array.toList_append,
    List.flatMap_append]

/-- Dropping `a.size * 8` bits from `bytesToBits (a ++ b ++ c)` gives
    `bytesToBits b ++ bytesToBits c`. -/
theorem bytesToBits_drop_prefix_three (a b c : ByteArray) :
    (Deflate.Spec.bytesToBits (a ++ b ++ c)).drop (a.size * 8) =
    Deflate.Spec.bytesToBits b ++ Deflate.Spec.bytesToBits c := by
  rw [bytesToBits_append, bytesToBits_append, List.append_assoc,
    ← Deflate.Spec.bytesToBits_length a, List.drop_left]

/-! ## Spec decode from inflate success -/

/-- If `inflate deflated = .ok data`, then the spec decode succeeds on
    `bytesToBits deflated` with the default fuel (10001). -/
private theorem inflate_to_spec_decode (deflated : ByteArray) (result : ByteArray)
    (h : Inflate.inflate deflated = .ok result) :
    Deflate.Spec.decode.go
      (Deflate.Spec.bytesToBits deflated) [] 10001 =
      some result.data.toList := by
  simp only [Inflate.inflate, bind, Except.bind] at h
  cases hinf : Inflate.inflateRaw deflated 0 (1024 * 1024 * 1024) with
  | error e => simp [hinf] at h
  | ok p =>
    simp [hinf, pure, Except.pure] at h
    obtain ⟨fuel, hfuel_le, hdec⟩ :=
      Deflate.Correctness.inflate_correct deflated 0 (1024 * 1024 * 1024) p.1 p.2
        (by rw [hinf])
    simp at hdec
    rw [← h]
    show Deflate.Spec.decode (Deflate.Spec.bytesToBits deflated) 10001 =
      some p.1.data.toList
    have h10001 : fuel + (10001 - fuel) = 10001 := by omega
    rw [show (10001 : Nat) = fuel + (10001 - fuel) from h10001.symm]
    exact Deflate.Spec.decode_fuel_independent _ _ _ hdec _

/-! ## Gzip roundtrip -/

/-- Gzip roundtrip: decompressing the output of compress returns the original data.
    The size bound (500M) is inherited from `inflate_deflateRaw`. -/
theorem gzip_decompressSingle_compress (data : ByteArray) (level : UInt8)
    (hsize : data.size < 500000000) :
    GzipDecode.decompressSingle (GzipEncode.compress data level) = .ok data := by
  -- DEFLATE roundtrip: inflate ∘ deflateRaw = id
  have hinfl : Inflate.inflate (Deflate.deflateRaw data level) = .ok data :=
    Deflate.inflate_deflateRaw data level hsize
  -- Spec decode on deflated with default fuel (10001)
  have hspec_go : Deflate.Spec.decode.go
      (Deflate.Spec.bytesToBits (Deflate.deflateRaw data level)) [] 10001 =
      some data.data.toList :=
    inflate_to_spec_decode _ data hinfl
  -- Suffix invariance: spec decode ignores trailer bits after the DEFLATE stream
  have hspec_compressed : ∀ (header trailer : ByteArray) (hh : header.size = 10),
      Deflate.Spec.decode.go
        ((Deflate.Spec.bytesToBits (header ++ Deflate.deflateRaw data level ++ trailer)).drop
          (10 * 8)) [] 10001 = some data.data.toList := by
    intro header trailer hh
    rw [show 10 * 8 = header.size * 8 from by omega,
        bytesToBits_drop_prefix_three]
    exact Deflate.Spec.decode_go_suffix _ _ [] 10001 _
      (by rw [Deflate.Spec.bytesToBits_length]; omega)
      hspec_go
  -- Use data.size bound to get result.length ≤ maxOutputSize
  have hdata_le : data.data.toList.length ≤ 1024 * 1024 * 1024 := by
    simp [Array.length_toList, ByteArray.size_data]; omega
  -- Spec decode on compressed bits at offset 10 (via compress_eq decomposition)
  have hspec_at10 : Deflate.Spec.decode.go
      ((Deflate.Spec.bytesToBits (GzipEncode.compress data level)).drop (10 * 8))
      [] 10001 = some data.data.toList := by
    obtain ⟨header, trailer, hhsz, _, hceq⟩ := GzipEncode.compress_eq data level
    rw [hceq]
    exact hspec_compressed header trailer hhsz
  -- Apply inflateRaw_complete to get native inflateRaw at offset 10
  obtain ⟨endPos, hinflRaw⟩ :=
    inflateRaw_complete _ 10 _ data.data.toList hdata_le 10001 (by omega) hspec_at10
  -- compressed size ≥ 18 (from compress = 10 + deflated + 8)
  have hcsz18 : ¬ (GzipEncode.compress data level).size < 18 := by
    rw [GzipEncode.compress_size]; omega
  -- Tight endPos bound: endPos + 8 ≤ compressed.size
  -- Strategy: run inflateRaw on (header ++ deflated) without trailer, get endPos' ≤ its size.
  -- Then inflateRaw_append_suffix shows the full compressed data gives the same endPos.
  obtain ⟨header, trailer, hhsz, htsz, hceq⟩ := GzipEncode.compress_eq data level
  -- Spec decode on (header ++ deflated) at offset 10
  have hspec_hd : Deflate.Spec.decode.go
      ((Deflate.Spec.bytesToBits (header ++ Deflate.deflateRaw data level)).drop (10 * 8))
      [] 10001 = some data.data.toList := by
    rw [show 10 * 8 = header.size * 8 from by omega]
    rw [bytesToBits_append, ← Deflate.Spec.bytesToBits_length header, List.drop_left]
    exact hspec_go
  -- Apply inflateRaw_complete on (header ++ deflated) to get endPos' and tight bound
  obtain ⟨endPos', hinflRaw'⟩ :=
    inflateRaw_complete (header ++ Deflate.deflateRaw data level) 10 _
      data.data.toList hdata_le 10001 (by omega) hspec_hd
  have hep_le : endPos' ≤ (header ++ Deflate.deflateRaw data level).size :=
    inflateRaw_endPos_le _ _ _ _ _ hinflRaw'
  -- By suffix invariance, inflateRaw on (header ++ deflated) ++ trailer gives same endPos'
  have hinflRaw'' : Inflate.inflateRaw ((header ++ Deflate.deflateRaw data level) ++ trailer)
      10 (1024 * 1024 * 1024) = .ok (⟨⟨data.data.toList⟩⟩, endPos') :=
    inflateRaw_append_suffix _ trailer 10 _ _ _ hinflRaw'
  -- (header ++ deflated) ++ trailer = compress data level
  have hreassoc : (header ++ Deflate.deflateRaw data level) ++ trailer =
      GzipEncode.compress data level := hceq.symm
  rw [hreassoc] at hinflRaw''
  -- endPos' = endPos by injectivity
  have hep_eq : endPos = endPos' := by
    have := hinflRaw.symm.trans hinflRaw''
    simp only [Except.ok.injEq, Prod.mk.injEq] at this
    exact this.2
  -- endPos exactness: endPos = (header ++ deflated).size
  have hep_exact : endPos' = (header ++ Deflate.deflateRaw data level).size := by
    have h' : Inflate.inflateRaw (header ++ Deflate.deflateRaw data level)
        header.size (1024 * 1024 * 1024) = .ok (⟨⟨data.data.toList⟩⟩, endPos') := by
      rw [hhsz]; exact hinflRaw'
    exact inflateRaw_endPos_eq header (Deflate.deflateRaw data level) _ _ _ h'
      hspec_go (Deflate.deflateRaw_goR_pad data level hsize) hdata_le
  have hep_val : endPos = 10 + (Deflate.deflateRaw data level).size := by
    rw [hep_eq, hep_exact, ByteArray.size_append, hhsz]
  have hendPos_tight : endPos + 8 ≤ (GzipEncode.compress data level).size := by
    rw [hep_val, hceq]
    simp only [ByteArray.size_append, htsz, hhsz]; omega
  have hendPos8 : ¬ (endPos + 8 > (GzipEncode.compress data level).size) := by omega
  have hba_eq : (⟨⟨data.data.toList⟩⟩ : ByteArray) = data := by simp
  -- CRC32 trailer match: use endPos = 10 + deflated.size to read trailer bytes
  have hcrc : (Crc32.Native.crc32 0 data ==
    Binary.readUInt32LE (GzipEncode.compress data level) endPos) = true := by
    rw [hep_val, GzipEncode.compress_crc32]
    simp [BEq.beq]
  -- ISIZE trailer match
  have hisize : (data.size.toUInt32 ==
    Binary.readUInt32LE (GzipEncode.compress data level) (endPos + 4)) = true := by
    rw [hep_val, GzipEncode.compress_isize]
    simp [BEq.beq]
  set_option maxRecDepth 8192 in
  simp (config := { decide := true }) only [GzipDecode.decompressSingle,
    - GzipDecode.decompressSingle.eq_1,
    bind, Except.bind, hcsz18, ↓reduceIte, pure, Except.pure,
    GzipEncode.compress_header_bytes data level,
    hinflRaw, hendPos8, hba_eq, hcrc, hisize,
    beq_self_eq_true, Bool.and_self]

end Zip.Native
