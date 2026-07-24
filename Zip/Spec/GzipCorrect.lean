import Zip.Native.Gzip
import Zip.Spec.DeflateRoundtrip
import ZipCommon.Spec.BinaryCorrect
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
  let (decompressed, endPos) ← Inflate.inflateRawReference data 10 maxOutputSize
  -- Parse trailer at endPos: CRC32 (4 bytes LE) + ISIZE (4 bytes LE)
  if endPos + 8 > data.size then throw "Gzip: truncated trailer"
  let expectedCrc := Binary.readUInt32LE data endPos
  let expectedSize := Binary.readUInt32LE data (endPos + 4)
  let actualCrc := Crc32.Native.crc32 0 decompressed
  unless actualCrc == expectedCrc do throw "Gzip: CRC32 mismatch"
  unless decompressed.size.toUInt32 == expectedSize do throw "Gzip: size mismatch"
  return decompressed

end GzipDecode

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
  refine ⟨?_, ?_, ?_, ?_⟩ <;> {
    rw [Binary.getElem!_append_left _ _ _ (by
      simp only [ByteArray.size_append]; split <;> (rw [gzip_header_size]; omega))]
    rw [Binary.getElem!_append_left _ _ _ (by split <;> (rw [gzip_header_size]; omega))]
    split <;> first | rfl | (split <;> rfl)
  }

/-- Decomposition: `compress` = header (10 bytes) ++ deflateRaw ++ trailer (8 bytes). -/
theorem compress_eq (data : ByteArray) (level : UInt8) :
    ∃ (header trailer : ByteArray),
      header.size = 10 ∧ trailer.size = 8 ∧
      compress data level = header ++ Deflate.deflateRaw data level ++ trailer := by
  unfold compress
  repeat (first | exact ⟨_, _, rfl, rfl, rfl⟩ | split)

/-- Decomposition with concrete trailer: `compress` = header(10) ++ deflateRaw ++ trailer
    where `readUInt32LE trailer 0 = crc32 0 data` and `readUInt32LE trailer 4 = isize`. -/
private theorem compress_trailer (data : ByteArray) (level : UInt8) :
    ∃ (header trailer : ByteArray),
      header.size = 10 ∧ trailer.size = 8 ∧
      compress data level = header ++ Deflate.deflateRaw data level ++ trailer ∧
      Binary.readUInt32LE trailer 0 = Crc32.Native.crc32 0 data ∧
      Binary.readUInt32LE trailer 4 = data.size.toUInt32 := by
  unfold compress
  repeat (first | exact ⟨_, _, rfl, rfl, rfl, Binary.readUInt32LE_bytes _, Binary.readUInt32LE_bytes _⟩ | split)

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
    from by omega, Binary.readUInt32LE_append3_right _ _ _ 4 (by omega)]
  exact hisize

end GzipEncode

/-! ## ByteArray/bitstream composition lemmas -/

/-- `bytesToBits` distributes over ByteArray append. -/
theorem bytesToBits_append (a b : ByteArray) :
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
    `bytesToBits deflated`. -/
theorem inflate_to_spec_decode (deflated : ByteArray) (result : ByteArray)
    (maxOutputSize : Nat)
    (h : Inflate.inflateReference deflated maxOutputSize = .ok result) :
    Deflate.Spec.decode.go
      (Deflate.Spec.bytesToBits deflated) [] =
      some result.data.toList := by
  simp only [Inflate.inflateReference, bind, Except.bind] at h
  cases hinf : Inflate.inflateRawReference deflated 0 maxOutputSize with
  | error e => exact nomatch (hinf ▸ h)
  | ok p =>
    simp only [hinf, pure, Except.pure, Except.ok.injEq] at h
    have hdec :=
      Deflate.Correctness.inflate_correct deflated 0 maxOutputSize p.1 p.2
        (by rw [hinf])
    simp only [Nat.zero_mul, List.drop_zero] at hdec
    rw [← h]
    show Deflate.Spec.decode (Deflate.Spec.bytesToBits deflated) =
      some p.1.data.toList
    exact hdec

/-! ## Framing endPos exactness -/

/-- For a stream decomposed as `header ++ deflateRaw data level ++ trailer` with
    `header.size = H`, native `inflateRaw` starting at `H` consumes exactly the
    embedded DEFLATE stream: it returns the original `data` and ends at
    `H + (deflateRaw data level).size`, ignoring the trailing bytes.

    This is the shared core of the gzip (H = 10) and zlib (H = 2) roundtrip
    capstones — the endPos-exactness derivation that would otherwise be
    duplicated in each. -/
theorem inflateRaw_framing (data : ByteArray) (level : UInt8) (maxOutputSize : Nat)
    (header trailer : ByteArray) (H : Nat) (hhsz : header.size = H)
    (hdata_le : data.data.toList.length ≤ maxOutputSize)
    (hspec_go : Deflate.Spec.decode.go
      (Deflate.Spec.bytesToBits (Deflate.deflateRaw data level)) [] =
      some data.data.toList) :
    Inflate.inflateRawReference (header ++ Deflate.deflateRaw data level ++ trailer) H maxOutputSize =
      .ok (⟨⟨data.data.toList⟩⟩, H + (Deflate.deflateRaw data level).size) := by
  -- Spec decode on (header ++ deflated) at offset H, via prefix drop
  have hspec_hd : Deflate.Spec.decode.go
      ((Deflate.Spec.bytesToBits (header ++ Deflate.deflateRaw data level)).drop (H * 8))
      [] = some data.data.toList := by
    rw [show H * 8 = header.size * 8 from by omega,
      bytesToBits_append, ← Deflate.Spec.bytesToBits_length header, List.drop_left]
    exact hspec_go
  obtain ⟨endPos', hinflRaw'⟩ :=
    inflateRaw_complete (header ++ Deflate.deflateRaw data level) H _
      data.data.toList hdata_le hspec_hd
  -- endPos' is exactly the size of (header ++ deflated)
  have hep_exact : endPos' = (header ++ Deflate.deflateRaw data level).size := by
    have h' : Inflate.inflateRawReference (header ++ Deflate.deflateRaw data level)
        header.size maxOutputSize = .ok (⟨⟨data.data.toList⟩⟩, endPos') := by
      rw [hhsz]; exact hinflRaw'
    exact inflateRaw_endPos_eq header (Deflate.deflateRaw data level) _ _ _ h'
      hspec_go (Deflate.deflateRaw_goR_pad data level) hdata_le
  -- Suffix invariance extends the result to the full stream with trailer
  rw [show H + (Deflate.deflateRaw data level).size
      = (header ++ Deflate.deflateRaw data level).size from by
        rw [ByteArray.size_append, hhsz], ← hep_exact]
  exact inflateRaw_append_suffix _ trailer H _ _ _ hinflRaw'

/-! ## Gzip roundtrip -/

/-- Gzip roundtrip: decompressing the output of compress returns the original data.
    Parametric in the decoder's `maxOutputSize`: holds whenever the input fits
    under the cap (`data.size ≤ maxOutputSize`). -/
theorem gzip_decompressSingle_compress (data : ByteArray) (level : UInt8)
    (maxOutputSize : Nat) (hsize : data.size ≤ maxOutputSize) :
    GzipDecode.decompressSingle (GzipEncode.compress data level) maxOutputSize = .ok data := by
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
  -- compressed size ≥ 18 (from compress = 10 + deflated + 8)
  have hcsz18 : ¬ (GzipEncode.compress data level).size < 18 := by
    rw [GzipEncode.compress_size]; omega
  -- Native inflate at offset 10 consumes exactly the DEFLATE stream (framing lemma)
  obtain ⟨header, trailer, hhsz, _, hceq⟩ := GzipEncode.compress_eq data level
  have hinflRaw : Inflate.inflateRawReference (GzipEncode.compress data level) 10 maxOutputSize =
      .ok (⟨⟨data.data.toList⟩⟩, 10 + (Deflate.deflateRaw data level).size) := by
    rw [hceq]
    exact inflateRaw_framing data level maxOutputSize header trailer 10 hhsz hdata_le hspec_go
  have hendPos8 : ¬ (10 + (Deflate.deflateRaw data level).size + 8 >
      (GzipEncode.compress data level).size) := by
    rw [GzipEncode.compress_size]; omega
  have hba_eq : (⟨⟨data.data.toList⟩⟩ : ByteArray) = data := by
    simp only [Array.toArray_toList]
  -- CRC32 trailer match: the trailer at 10 + deflated.size reads crc32 0 data
  have hcrc : (Crc32.Native.crc32 0 data ==
    Binary.readUInt32LE (GzipEncode.compress data level)
      (10 + (Deflate.deflateRaw data level).size)) = true := by
    rw [GzipEncode.compress_crc32]
    simp only [BEq.beq, decide_true]
  -- ISIZE trailer match
  have hisize : (data.size.toUInt32 ==
    Binary.readUInt32LE (GzipEncode.compress data level)
      (10 + (Deflate.deflateRaw data level).size + 4)) = true := by
    rw [GzipEncode.compress_isize]
    simp only [BEq.beq, Nat.toUInt32_eq, decide_true]
  set_option maxRecDepth 8192 in
  simp (config := { decide := true }) only [GzipDecode.decompressSingle,
    - GzipDecode.decompressSingle.eq_1,
    bind, Except.bind, hcsz18, ↓reduceIte, pure, Except.pure,
    GzipEncode.compress_header_bytes data level,
    hinflRaw, hendPos8, hba_eq, hcrc, hisize,
    beq_self_eq_true, Bool.and_self]

end Zip.Native
