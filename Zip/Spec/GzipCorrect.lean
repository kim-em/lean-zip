import Zip.Native.Gzip
import Zip.Spec.DeflateRoundtrip
import Zip.Spec.BinaryCorrect
import Zip.Spec.DeflateSuffix
import Zip.Spec.InflateComplete

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
private theorem bytesToBits_drop_prefix_three (a b c : ByteArray) :
    (Deflate.Spec.bytesToBits (a ++ b ++ c)).drop (a.size * 8) =
    Deflate.Spec.bytesToBits b ++ Deflate.Spec.bytesToBits c := by
  rw [bytesToBits_append, bytesToBits_append, List.append_assoc,
    ← Deflate.Spec.bytesToBits_length a, List.drop_left]

/-- `bytesToBits trailer` has length divisible by 8 (it's 64 bits = 8 bytes). -/
private theorem bytesToBits_length_mod8 (ba : ByteArray) :
    (Deflate.Spec.bytesToBits ba).length % 8 = 0 := by
  rw [Deflate.Spec.bytesToBits_length]; omega

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

/-! ## inflateRaw endPos bound -/

/-- `readBit` preserves the data field and the hpos invariant. -/
private theorem readBit_data_eq (br br' : BitReader) (bit : UInt32)
    (h : br.readBit = .ok (bit, br')) : br'.data = br.data := by
  simp only [BitReader.readBit] at h
  split at h
  · simp at h
  · split at h <;> simp [Except.ok.injEq, Prod.mk.injEq] at h <;>
      obtain ⟨_, rfl⟩ := h <;> rfl

/-- `readBits.go` preserves the data field. -/
private theorem readBits_go_data_eq (br br' : BitReader) (acc : UInt32)
    (shift n : Nat) (val : UInt32)
    (h : BitReader.readBits.go br acc shift n = .ok (val, br')) :
    br'.data = br.data := by
  induction n generalizing br acc shift with
  | zero =>
    simp [BitReader.readBits.go] at h
    obtain ⟨_, rfl⟩ := h; rfl
  | succ n ih =>
    simp only [BitReader.readBits.go, bind, Except.bind] at h
    cases hrb : br.readBit with
    | error e => simp [hrb] at h
    | ok p =>
      obtain ⟨bit, br₁⟩ := p
      simp only [hrb] at h
      have hd₁ := readBit_data_eq br br₁ bit hrb
      have hd' := ih br₁ _ _ h
      rw [hd', hd₁]

/-- `readBits` preserves the data field. -/
private theorem readBits_data_eq (br br' : BitReader) (n : Nat)
    (val : UInt32) (h : br.readBits n = .ok (val, br')) :
    br'.data = br.data := by
  exact readBits_go_data_eq br br' 0 0 n val h

/-- After a successful `readBit`, the hpos invariant `bitOff = 0 ∨ pos < data.size` holds. -/
private theorem readBit_hpos (br br' : BitReader) (bit : UInt32)
    (h : br.readBit = .ok (bit, br'))
    (_hpos : br.bitOff = 0 ∨ br.pos < br.data.size) :
    br'.bitOff = 0 ∨ br'.pos < br'.data.size := by
  simp only [BitReader.readBit] at h
  split at h
  · simp at h
  · rename_i hlt
    split at h <;> simp [Except.ok.injEq, Prod.mk.injEq] at h <;>
      obtain ⟨_, rfl⟩ := h <;> simp_all

/-- `readBits.go` preserves the hpos invariant. -/
private theorem readBits_go_hpos (br br' : BitReader) (acc : UInt32)
    (shift n : Nat) (val : UInt32)
    (h : BitReader.readBits.go br acc shift n = .ok (val, br'))
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size) :
    br'.bitOff = 0 ∨ br'.pos < br'.data.size := by
  induction n generalizing br acc shift with
  | zero =>
    simp [BitReader.readBits.go] at h
    obtain ⟨_, rfl⟩ := h; exact hpos
  | succ n ih =>
    simp only [BitReader.readBits.go, bind, Except.bind] at h
    cases hrb : br.readBit with
    | error e => simp [hrb] at h
    | ok p =>
      obtain ⟨bit, br₁⟩ := p
      simp only [hrb] at h
      have hpos₁ := readBit_hpos br br₁ bit hrb hpos
      have hd₁ := readBit_data_eq br br₁ bit hrb
      exact ih br₁ _ _ h (hd₁ ▸ hpos₁)

/-- `readBits` preserves the hpos invariant. -/
private theorem readBits_hpos (br br' : BitReader) (n : Nat)
    (val : UInt32) (h : br.readBits n = .ok (val, br'))
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size) :
    br'.bitOff = 0 ∨ br'.pos < br'.data.size := by
  exact readBits_go_hpos br br' 0 0 n val h hpos

/-- `alignToByte.pos ≤ data.size` when `pos ≤ data.size`. In the `bitOff ≠ 0` case,
    we need the stronger `pos < data.size` (from the hpos invariant). -/
private theorem alignToByte_pos_le (br : BitReader)
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (hle : br.pos ≤ br.data.size) :
    br.alignToByte.pos ≤ br.data.size := by
  simp only [BitReader.alignToByte]
  split
  · exact hle
  · rename_i hne
    cases hpos with
    | inl h => simp [h] at hne
    | inr h => simp only; omega


/-! ### BitReader invariant preservation

All BitReader operations preserve `data` and the position invariant
`bitOff = 0 ∨ pos < data.size`. We bundle these into combined lemmas
for each function to minimize code. -/

/-- Combined: readBit preserves data, hpos, and gives pos ≤ data.size. -/
private theorem readBit_inv (br br' : BitReader) (bit : UInt32)
    (h : br.readBit = .ok (bit, br'))
    (_hpos : br.bitOff = 0 ∨ br.pos < br.data.size) :
    br'.data = br.data ∧
    (br'.bitOff = 0 ∨ br'.pos < br'.data.size) ∧
    br'.pos ≤ br'.data.size := by
  simp only [BitReader.readBit] at h
  split at h
  · simp at h
  · rename_i hlt
    split at h <;> simp [Except.ok.injEq, Prod.mk.injEq] at h <;>
      obtain ⟨_, rfl⟩ := h <;> simp_all <;> omega

/-- Combined: readBits.go preserves data, hpos, and pos ≤ data.size. -/
private theorem readBits_go_inv (br br' : BitReader) (acc : UInt32)
    (shift n : Nat) (val : UInt32)
    (h : BitReader.readBits.go br acc shift n = .ok (val, br'))
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (hple : br.pos ≤ br.data.size) :
    br'.data = br.data ∧
    (br'.bitOff = 0 ∨ br'.pos < br'.data.size) ∧
    br'.pos ≤ br'.data.size := by
  induction n generalizing br acc shift with
  | zero =>
    simp [BitReader.readBits.go] at h
    obtain ⟨_, rfl⟩ := h; exact ⟨rfl, hpos, hple⟩
  | succ n ih =>
    simp only [BitReader.readBits.go, bind, Except.bind] at h
    cases hrb : br.readBit with
    | error e => simp [hrb] at h
    | ok p =>
      obtain ⟨bit, br₁⟩ := p
      simp only [hrb] at h
      have ⟨hd₁, hpos₁, hple₁⟩ := readBit_inv br br₁ bit hrb hpos
      have ⟨hd', hpos', hple'⟩ := ih br₁ _ _ h hpos₁ hple₁
      exact ⟨hd'.trans hd₁, hpos', hple'⟩

/-- Combined: readBits preserves data, hpos, and pos ≤ data.size. -/
private theorem readBits_inv (br br' : BitReader) (n : Nat)
    (val : UInt32) (h : br.readBits n = .ok (val, br'))
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (hple : br.pos ≤ br.data.size) :
    br'.data = br.data ∧
    (br'.bitOff = 0 ∨ br'.pos < br'.data.size) ∧
    br'.pos ≤ br'.data.size :=
  readBits_go_inv br br' 0 0 n val h hpos hple

/-- Combined: HuffTree.decode.go preserves data, hpos, and pos ≤ data.size. -/
private theorem decode_go_inv (tree : HuffTree) (br br' : BitReader) (n : Nat)
    (sym : UInt16) (h : HuffTree.decode.go tree br n = .ok (sym, br'))
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (hple : br.pos ≤ br.data.size) :
    br'.data = br.data ∧
    (br'.bitOff = 0 ∨ br'.pos < br'.data.size) ∧
    br'.pos ≤ br'.data.size := by
  induction tree generalizing br n with
  | leaf s =>
    simp [HuffTree.decode.go] at h
    obtain ⟨_, rfl⟩ := h; exact ⟨rfl, hpos, hple⟩
  | empty => simp [HuffTree.decode.go] at h
  | node z o ihz iho =>
    simp only [HuffTree.decode.go] at h
    split at h
    · simp at h
    · simp only [bind, Except.bind] at h
      cases hrb : br.readBit with
      | error e => simp [hrb] at h
      | ok p =>
        obtain ⟨bit, br₁⟩ := p
        simp only [hrb] at h
        have ⟨hd₁, hpos₁, hple₁⟩ := readBit_inv br br₁ bit hrb hpos
        split at h
        · have ⟨hd', hp', hl'⟩ := ihz br₁ _ h hpos₁ hple₁
          exact ⟨hd'.trans hd₁, hp', hl'⟩
        · have ⟨hd', hp', hl'⟩ := iho br₁ _ h hpos₁ hple₁
          exact ⟨hd'.trans hd₁, hp', hl'⟩

/-- Combined: HuffTree.decode preserves data, hpos, and pos ≤ data.size. -/
private theorem decode_inv (tree : HuffTree) (br br' : BitReader)
    (sym : UInt16) (h : tree.decode br = .ok (sym, br'))
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (hple : br.pos ≤ br.data.size) :
    br'.data = br.data ∧
    (br'.bitOff = 0 ∨ br'.pos < br'.data.size) ∧
    br'.pos ≤ br'.data.size :=
  decode_go_inv tree br br' 0 sym h hpos hple

/-- readUInt16LE preserves data and sets bitOff = 0. -/
private theorem readUInt16LE_inv (br br' : BitReader) (v : UInt16)
    (h : br.readUInt16LE = .ok (v, br')) :
    br'.data = br.data ∧ br'.bitOff = 0 ∧ br'.pos ≤ br'.data.size := by
  simp only [BitReader.readUInt16LE, BitReader.alignToByte] at h
  split at h
  next hbo =>
    split at h
    · simp at h
    · next hle =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h
      have hbo' : br.bitOff = 0 := eq_of_beq hbo
      exact ⟨rfl, hbo', by dsimp [BitReader.data, BitReader.pos] at hle ⊢; omega⟩
  next hbo =>
    split at h
    · simp at h
    · next hle =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h
      exact ⟨rfl, rfl, by dsimp [BitReader.data, BitReader.pos] at hle ⊢; omega⟩

/-- readBytes preserves data and sets bitOff = 0. -/
private theorem readBytes_inv (br br' : BitReader) (n : Nat) (bytes : ByteArray)
    (h : br.readBytes n = .ok (bytes, br')) :
    br'.data = br.data ∧ br'.bitOff = 0 ∧ br'.pos ≤ br'.data.size := by
  simp only [BitReader.readBytes, BitReader.alignToByte] at h
  split at h
  next hbo =>
    split at h
    · simp at h
    · next hle =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h
      have hbo' : br.bitOff = 0 := eq_of_beq hbo
      exact ⟨rfl, hbo', by dsimp [BitReader.data, BitReader.pos] at hle ⊢; omega⟩
  next hbo =>
    split at h
    · simp at h
    · next hle =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h
      exact ⟨rfl, rfl, by dsimp [BitReader.data, BitReader.pos] at hle ⊢; omega⟩

/-- Combined: decodeStored preserves data, and gives hpos + pos_le. -/
private theorem decodeStored_inv (br br' : BitReader)
    (output output' : ByteArray) (maxOut : Nat)
    (h : Inflate.decodeStored br output maxOut = .ok (output', br')) :
    br'.data = br.data ∧
    (br'.bitOff = 0 ∨ br'.pos < br'.data.size) ∧
    br'.pos ≤ br'.data.size := by
  -- decodeStored chains: readUInt16LE → readUInt16LE → checks → readBytes
  -- All three preserve data and produce bitOff = 0.
  -- Extract that readBytes succeeded from the successful decodeStored call.
  simp only [Inflate.decodeStored, bind, Except.bind] at h
  match h1 : br.readUInt16LE with
  | .error e => simp [h1] at h
  | .ok (len, br₁) =>
    rw [h1] at h; simp only [] at h
    match h2 : br₁.readUInt16LE with
    | .error e => simp [h2] at h
    | .ok (nlen, br₂) =>
      rw [h2] at h; simp only [] at h
      -- h now has: unless (xor check) → unless (size check) → readBytes → return
      -- We need to extract that readBytes succeeded. Use `have` with revert/intro.
      have h_rb : ∃ bytes, br₂.readBytes len.toNat = .ok (bytes, br') := by
        revert h; intro h
        -- The `unless` pattern with `bne`:
        -- unless (len ^^^ nlen != 0xFFFF) => if not cond then pure () else throw
        -- With Except monad this is: if cond then throw else (if cond' then throw else readBytes >>= return)
        -- We handle this by splitting on the conditions
        -- Normalize the `unless` checks: `unless c do throw e` becomes
        -- `if c then throw e else pure ()` and pure PUnit.unit = .ok ()
        simp only [pure, Except.pure] at h
        by_cases hxor : (len ^^^ nlen != 0xFFFF) = true
        · -- xor check fails → throws, contradicts h = .ok
          simp [hxor] at h
        · simp only [hxor] at h
          by_cases hsize : output.size + len.toNat > maxOut
          · simp [hsize] at h
          · simp only [hsize, ite_false] at h
            match h3 : br₂.readBytes len.toNat with
            | .error e => simp [h3] at h
            | .ok (bytes, br₃) =>
              simp [h3] at h
              exact ⟨bytes, by rw [h.2]⟩
      obtain ⟨bytes, h_rb⟩ := h_rb
      have ⟨hd3, hbo3, hple3⟩ := readBytes_inv br₂ br' _ _ h_rb
      have ⟨hd1, _, _⟩ := readUInt16LE_inv br br₁ _ h1
      have ⟨hd2, _, _⟩ := readUInt16LE_inv br₁ br₂ _ h2
      exact ⟨hd3.trans (hd2.trans hd1), Or.inl hbo3, hple3⟩

/-- Combined: decodeHuffman.go preserves data, hpos, and pos ≤ data.size. -/
private theorem decodeHuffman_go_inv (litTree distTree : HuffTree)
    (br br' : BitReader) (output output' : ByteArray)
    (maxOut fuel : Nat)
    (h : Inflate.decodeHuffman.go litTree distTree maxOut br output fuel =
      .ok (output', br'))
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (hple : br.pos ≤ br.data.size) :
    br'.data = br.data ∧
    (br'.bitOff = 0 ∨ br'.pos < br'.data.size) ∧
    br'.pos ≤ br'.data.size := by
  induction fuel generalizing br output with
  | zero => simp [Inflate.decodeHuffman.go] at h
  | succ n ih =>
    unfold Inflate.decodeHuffman.go at h
    cases hlit : litTree.decode br with
    | error e => rw [hlit] at h; simp [Bind.bind, Except.bind] at h
    | ok p =>
      obtain ⟨sym, br₁⟩ := p; rw [hlit] at h; dsimp only [Bind.bind, Except.bind] at h
      -- Reduce `match pure PUnit.unit` to just the ok branch
      simp only [pure, Except.pure] at h
      have ⟨hd₁, hpos₁, hple₁⟩ := decode_inv litTree br br₁ sym hlit hpos hple
      split at h
      · -- sym < 256: literal byte
        split at h
        · simp at h  -- output.size ≥ maxOut → error
        · -- recursive call
          have ⟨hd', hp', hl'⟩ := ih br₁ _ h hpos₁ hple₁
          exact ⟨hd'.trans hd₁, hp', hl'⟩
      · split at h
        · -- sym == 256: end of block
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨_, rfl⟩ := h
          exact ⟨hd₁, hpos₁, hple₁⟩
        · -- sym ≥ 257: length+distance code
          split at h
          · simp at h  -- invalid length code → error
          · -- readBits for length extra → decode dist → readBits dist extra → recursive call
            -- h is a nested match tree; use split to decompose
            split at h
            · simp at h  -- readBits error
            · rename_i v hrb1_eq
              -- v = (extraBits, br₂); hrb1_eq : br₁.readBits ... = .ok v
              split at h
              · simp at h  -- decode dist error
              · rename_i v₁ hdist_eq
                split at h
                · simp at h  -- invalid distance code
                · split at h
                  · simp at h  -- readBits dist extra error
                  · rename_i v₂ hrb2_eq
                    split at h
                    · simp at h  -- distance > output.size
                    · split at h
                      · simp at h  -- output.size + length > maxOut
                      · -- recursive go call remains
                        obtain ⟨extraBits, br₂⟩ := v
                        obtain ⟨distSym, br₃⟩ := v₁
                        obtain ⟨dExtraBits, br₄⟩ := v₂
                        simp only [] at hrb1_eq hdist_eq hrb2_eq h
                        have ⟨hd₂, hpos₂, hple₂⟩ := readBits_inv br₁ br₂ _ _ hrb1_eq hpos₁ hple₁
                        have ⟨hd₃, hpos₃, hple₃⟩ := decode_inv distTree br₂ br₃ distSym hdist_eq hpos₂ hple₂
                        have ⟨hd₄, hpos₄, hple₄⟩ := readBits_inv br₃ br₄ _ _ hrb2_eq hpos₃ hple₃
                        have ⟨hd', hp', hl'⟩ := ih br₄ _ h hpos₄ hple₄
                        exact ⟨hd'.trans (hd₄.trans (hd₃.trans (hd₂.trans hd₁))), hp', hl'⟩

/-- `decodeHuffman` preserves the BitReader invariant. Wrapper around `decodeHuffman_go_inv`. -/
private theorem decodeHuffman_inv (litTree distTree : HuffTree)
    (br br' : BitReader) (output output' : ByteArray) (maxOut : Nat)
    (h : Inflate.decodeHuffman br output litTree distTree maxOut = .ok (output', br'))
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (hple : br.pos ≤ br.data.size) :
    br'.data = br.data ∧
    (br'.bitOff = 0 ∨ br'.pos < br'.data.size) ∧
    br'.pos ≤ br'.data.size :=
  decodeHuffman_go_inv litTree distTree br br' output output' maxOut _ h hpos hple

/-- Combined: readCLCodeLengths preserves data, hpos, and pos ≤ data.size. -/
private theorem readCLCodeLengths_inv (br br' : BitReader)
    (clLengths clLengths' : Array UInt8) (i numCodeLen : Nat)
    (h : Inflate.readCLCodeLengths br clLengths i numCodeLen = .ok (clLengths', br'))
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (hple : br.pos ≤ br.data.size) :
    br'.data = br.data ∧
    (br'.bitOff = 0 ∨ br'.pos < br'.data.size) ∧
    br'.pos ≤ br'.data.size := by
  -- Use strong induction on numCodeLen - i
  suffices ∀ (m : Nat) br (clLengths : Array UInt8) (i numCodeLen : Nat),
      m = numCodeLen - i →
      Inflate.readCLCodeLengths br clLengths i numCodeLen = .ok (clLengths', br') →
      (br.bitOff = 0 ∨ br.pos < br.data.size) → br.pos ≤ br.data.size →
      br'.data = br.data ∧
      (br'.bitOff = 0 ∨ br'.pos < br'.data.size) ∧
      br'.pos ≤ br'.data.size from this _ _ _ _ _ rfl h hpos hple
  intro m
  induction m with
  | zero =>
    intro br cl i ncl heq h hpos hple
    unfold Inflate.readCLCodeLengths at h
    split at h
    · rename_i hlt; omega
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h; exact ⟨rfl, hpos, hple⟩
  | succ k ih =>
    intro br cl i ncl heq h hpos hple
    unfold Inflate.readCLCodeLengths at h
    split at h
    · simp only [bind, Except.bind] at h
      cases hrb : br.readBits 3 with
      | error e => simp [hrb] at h
      | ok p =>
        obtain ⟨v, br₁⟩ := p; simp only [hrb] at h
        have ⟨hd₁, hpos₁, hple₁⟩ := readBits_inv br br₁ 3 v hrb hpos hple
        have ⟨hd', hp', hl'⟩ := ih br₁ _ (i + 1) ncl (by omega) h hpos₁ hple₁
        exact ⟨hd'.trans hd₁, hp', hl'⟩
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h; exact ⟨rfl, hpos, hple⟩

/-- Combined: decodeCLSymbols preserves data, hpos, and pos ≤ data.size. -/
private theorem decodeCLSymbols_inv (clTree : HuffTree) (br br' : BitReader)
    (codeLengths codeLengths' : Array UInt8) (idx totalCodes fuel : Nat)
    (h : Inflate.decodeCLSymbols clTree br codeLengths idx totalCodes fuel =
      .ok (codeLengths', br'))
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (hple : br.pos ≤ br.data.size) :
    br'.data = br.data ∧
    (br'.bitOff = 0 ∨ br'.pos < br'.data.size) ∧
    br'.pos ≤ br'.data.size := by
  induction fuel generalizing br codeLengths idx with
  | zero => simp [Inflate.decodeCLSymbols] at h
  | succ n ih =>
    unfold Inflate.decodeCLSymbols at h
    split at h
    · -- idx ≥ totalCodes: return
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h; exact ⟨rfl, hpos, hple⟩
    · -- idx < totalCodes: do block
      dsimp only [Bind.bind, Except.bind] at h
      split at h
      · simp at h  -- decode error
      · rename_i v hdec_eq
        -- v = (sym, br₁)
        simp only [pure, Except.pure] at h
        obtain ⟨sym, br₁⟩ := v; simp only [] at hdec_eq h
        have ⟨hd₁, hpos₁, hple₁⟩ := decode_inv clTree br br₁ sym hdec_eq hpos hple
        split at h
        · -- sym < 16: literal code length
          have ⟨hd', hp', hl'⟩ := ih br₁ _ _ h hpos₁ hple₁
          exact ⟨hd'.trans hd₁, hp', hl'⟩
        · split at h
          · -- sym == 16: repeat previous
            split at h
            · simp at h  -- idx == 0 error
            · -- readBits 2
              split at h
              · simp at h  -- readBits error
              · rename_i v₁ hrb_eq
                obtain ⟨rep, br₂⟩ := v₁; simp only [] at hrb_eq h
                have ⟨hd₂, hpos₂, hple₂⟩ := readBits_inv br₁ br₂ 2 rep hrb_eq hpos₁ hple₁
                split at h
                · simp at h  -- repeat exceeds total
                · have ⟨hd', hp', hl'⟩ := ih br₂ _ _ h hpos₂ hple₂
                  exact ⟨hd'.trans (hd₂.trans hd₁), hp', hl'⟩
          · split at h
            · -- sym == 17: zero-fill short
              split at h
              · simp at h  -- readBits error
              · rename_i v₂ hrb_eq
                obtain ⟨rep, br₂⟩ := v₂; simp only [] at hrb_eq h
                have ⟨hd₂, hpos₂, hple₂⟩ := readBits_inv br₁ br₂ 3 rep hrb_eq hpos₁ hple₁
                split at h
                · simp at h  -- repeat exceeds total
                · have ⟨hd', hp', hl'⟩ := ih br₂ _ _ h hpos₂ hple₂
                  exact ⟨hd'.trans (hd₂.trans hd₁), hp', hl'⟩
            · split at h
              · -- sym == 18: zero-fill long
                split at h
                · simp at h  -- readBits error
                · rename_i v₃ hrb_eq
                  obtain ⟨rep, br₂⟩ := v₃; simp only [] at hrb_eq h
                  have ⟨hd₂, hpos₂, hple₂⟩ := readBits_inv br₁ br₂ 7 rep hrb_eq hpos₁ hple₁
                  split at h
                  · simp at h  -- repeat exceeds total
                  · have ⟨hd', hp', hl'⟩ := ih br₂ _ _ h hpos₂ hple₂
                    exact ⟨hd'.trans (hd₂.trans hd₁), hp', hl'⟩
              · simp at h  -- invalid symbol

/-- Combined: decodeDynamicTrees preserves data, hpos, and pos ≤ data.size. -/
private theorem decodeDynamicTrees_inv (br br' : BitReader)
    (litTree distTree : HuffTree)
    (h : Inflate.decodeDynamicTrees br = .ok (litTree, distTree, br'))
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (hple : br.pos ≤ br.data.size) :
    br'.data = br.data ∧
    (br'.bitOff = 0 ∨ br'.pos < br'.data.size) ∧
    br'.pos ≤ br'.data.size := by
  -- decodeDynamicTrees is a sequential chain of readBits, readCLCodeLengths, decodeCLSymbols
  simp only [Inflate.decodeDynamicTrees] at h
  dsimp only [Bind.bind, Except.bind] at h
  -- readBits 5 (hlit)
  split at h
  · simp at h
  · rename_i v₁ hrb1_eq
    obtain ⟨hlit_val, br₁⟩ := v₁; simp only [] at hrb1_eq h
    have ⟨hd₁, hpos₁, hple₁⟩ := readBits_inv br br₁ 5 hlit_val hrb1_eq hpos hple
    -- readBits 5 (hdist)
    split at h
    · simp at h
    · rename_i v₂ hrb2_eq
      obtain ⟨hdist_val, br₂⟩ := v₂; simp only [] at hrb2_eq h
      have ⟨hd₂, hpos₂, hple₂⟩ := readBits_inv br₁ br₂ 5 hdist_val hrb2_eq hpos₁ hple₁
      -- readBits 4 (hclen)
      split at h
      · simp at h
      · rename_i v₃ hrb3_eq
        obtain ⟨hclen_val, br₃⟩ := v₃; simp only [] at hrb3_eq h
        have ⟨hd₃, hpos₃, hple₃⟩ := readBits_inv br₂ br₃ 4 hclen_val hrb3_eq hpos₂ hple₂
        -- readCLCodeLengths
        split at h
        · simp at h
        · rename_i v₄ hrcl_eq
          obtain ⟨clLengths, br₄⟩ := v₄; simp only [] at hrcl_eq h
          have ⟨hd₄, hpos₄, hple₄⟩ := readCLCodeLengths_inv br₃ br₄ _ clLengths _ _ hrcl_eq hpos₃ hple₃
          -- HuffTree.fromLengths (pure, no BitReader change)
          split at h
          · simp at h
          · rename_i clTree _
            -- decodeCLSymbols
            split at h
            · simp at h
            · rename_i v₅ hdcl_eq
              obtain ⟨codeLengths, br₅⟩ := v₅; simp only [] at hdcl_eq h
              have ⟨hd₅, hpos₅, hple₅⟩ := decodeCLSymbols_inv clTree br₄ br₅
                _ codeLengths _ _ _ hdcl_eq hpos₄ hple₄
              -- HuffTree.fromLengths (litTree) — pure
              split at h
              · simp at h
              · rename_i litTree' _
                -- HuffTree.fromLengths (distTree) — pure
                split at h
                · simp at h
                · rename_i distTree' _
                  -- h : pure (litTree', distTree', br₅) = Except.ok (litTree, distTree, br')
                  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
                  obtain ⟨_, _, rfl⟩ := h
                  exact ⟨hd₅.trans (hd₄.trans (hd₃.trans (hd₂.trans hd₁))),
                         hpos₅, hple₅⟩

/-! ### inflateLoop endPos bound -/

/-- After a successful `inflateLoop`, the returned endPos ≤ br.data.size.

    The proof tracks three invariants through each operation:
    data preservation, hpos (bitOff=0 ∨ pos<data.size), and pos ≤ data.size.
    Terminal case: alignToByte gives endPos ≤ data.size.
    Recursive case: chain data_eq back to the original data. -/
theorem inflateLoop_endPos_le (br : BitReader) (output : ByteArray)
    (fixedLit fixedDist : HuffTree) (maxOut fuel : Nat)
    (result : ByteArray) (endPos : Nat)
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (hple : br.pos ≤ br.data.size)
    (h : Inflate.inflateLoop br output fixedLit fixedDist maxOut fuel =
      .ok (result, endPos)) :
    endPos ≤ br.data.size := by
  induction fuel generalizing br output with
  | zero => simp [Inflate.inflateLoop] at h
  | succ n ih =>
    simp only [Inflate.inflateLoop, bind, Except.bind] at h
    cases hbf : br.readBits 1 with
    | error e => simp [hbf] at h
    | ok p =>
      obtain ⟨bfinal, br₁⟩ := p; simp only [hbf] at h
      have ⟨hd₁, hpos₁, hple₁⟩ := readBits_inv br br₁ 1 bfinal hbf hpos hple
      cases hbt : br₁.readBits 2 with
      | error e => simp [hbt] at h
      | ok p =>
        obtain ⟨btype, br₂⟩ := p; simp only [hbt] at h
        have ⟨hd₂, hpos₂, hple₂⟩ := readBits_inv br₁ br₂ 2 btype hbt hpos₁ hple₁
        -- Helper: given br' from block decode + bfinal check → endPos ≤ br.data.size
        have bfinal_or_recurse :
            ∀ (br' : BitReader) (output' : ByteArray),
            br'.data = br.data →
            (br'.bitOff = 0 ∨ br'.pos < br'.data.size) →
            br'.pos ≤ br'.data.size →
            (if (bfinal == 1) = true then pure (output', br'.alignToByte.pos)
             else Inflate.inflateLoop br' output' fixedLit fixedDist maxOut n) =
              .ok (result, endPos) →
            endPos ≤ br.data.size := by
          intro br' output' hd' hpos' hple' hif
          split at hif
          · -- bfinal = 1: endPos = br'.alignToByte.pos
            simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hif
            obtain ⟨_, rfl⟩ := hif
            have := alignToByte_pos_le br' hpos' hple'
            rw [hd'] at this; exact this
          · -- bfinal ≠ 1: recursive call
            have hle := ih br' output' hpos' hple' hif
            rw [hd'] at hle; exact hle
        -- Dispatch by block type
        split at h
        · -- btype = 0: stored
          split at h; · simp at h
          · rename_i v hds; obtain ⟨out', br'⟩ := v; simp only [] at hds h
            have ⟨hd, hp, hl⟩ := decodeStored_inv br₂ br' output out' maxOut hds
            exact bfinal_or_recurse br' out' (hd.trans (hd₂.trans hd₁)) hp hl h
        · -- btype = 1: fixed Huffman
          split at h; · simp at h
          · rename_i v hdh; obtain ⟨out', br'⟩ := v; simp only [] at hdh h
            have ⟨hd, hp, hl⟩ := decodeHuffman_inv fixedLit fixedDist br₂ br' output out'
              maxOut hdh hpos₂ hple₂
            exact bfinal_or_recurse br' out' (hd.trans (hd₂.trans hd₁)) hp hl h
        · -- btype = 2: dynamic Huffman
          split at h; · simp at h
          · rename_i v hdt; obtain ⟨litT, distT, br₃⟩ := v; simp only [] at hdt h
            have ⟨hd₃, hpos₃, hple₃⟩ := decodeDynamicTrees_inv br₂ br₃ litT distT hdt hpos₂ hple₂
            split at h; · simp at h
            · rename_i v₂ hdh; obtain ⟨out', br'⟩ := v₂; simp only [] at hdh h
              unfold Inflate.decodeHuffman at hdh
              have ⟨hd, hp, hl⟩ := decodeHuffman_go_inv litT distT br₃ br' output out'
                maxOut _ hdh hpos₃ hple₃
              exact bfinal_or_recurse br' out' (hd.trans (hd₃.trans (hd₂.trans hd₁))) hp hl h
        · -- btype ≥ 3: reserved → error
          simp at h

/-! ## inflateLoop completeness with final BitReader (extended)

The extended version of `inflateLoop_complete` that also returns the final
`BitReader` state, including `data` preservation and position bounds.
This is needed to prove `inflateRaw_endPos_ge`. -/

/-- Extended completeness for `inflateLoop`: in addition to the basic completeness
    result, this also exposes the final `BitReader` state after decompression.
    The additional properties (data preservation, position bounds) allow us to
    prove `endPos ≥ data.size` when combined with `alignToByte_pos_ge_of_toBits_short`
    and an encoder hypothesis showing remaining bits < 8.

    The proof follows the same structure as `inflateLoop_complete` (in
    InflateComplete.lean) but additionally tracks `br'.data = br.data` and
    `br'.pos ≤ br'.data.size` using the `_inv` lemmas. -/
theorem inflateLoop_complete_ext (br : BitReader) (output : ByteArray)
    (fixedLit fixedDist : HuffTree) (maxOutputSize : Nat)
    (result : List UInt8)
    (hwf : br.bitOff < 8)
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (hple : br.pos ≤ br.data.size)
    (hflit : HuffTree.fromLengths Inflate.fixedLitLengths = .ok fixedLit)
    (hfdist : HuffTree.fromLengths Inflate.fixedDistLengths = .ok fixedDist)
    (hmax : result.length ≤ maxOutputSize)
    (specFuel : Nat)
    (hspec : Deflate.Spec.decode.go br.toBits output.data.toList specFuel =
        some result) :
    ∃ (br_final : BitReader) (endPos : Nat) (remaining : List Bool),
      Inflate.inflateLoop br output fixedLit fixedDist
        maxOutputSize specFuel = .ok (⟨⟨result⟩⟩, endPos) ∧
      endPos = br_final.alignToByte.pos ∧
      br_final.data = br.data ∧
      br_final.bitOff < 8 ∧
      (br_final.bitOff = 0 ∨ br_final.pos < br_final.data.size) ∧
      br_final.pos ≤ br_final.data.size ∧
      br_final.toBits = remaining ∧
      Deflate.Spec.decode.goR br.toBits output.data.toList specFuel =
        some (result, remaining) := by
  -- Use the existing inflateLoop_complete to get that inflateLoop succeeds,
  -- then extract br_final info via _inv lemmas.
  -- We proceed by induction (same structure as inflateLoop_complete).
  induction specFuel generalizing br output with
  | zero => simp [Deflate.Spec.decode.go] at hspec
  | succ n ih =>
    unfold Deflate.Spec.decode.go at hspec
    cases hspec_bf : Deflate.Spec.readBitsLSB 1 br.toBits with
    | none => simp [hspec_bf] at hspec
    | some p =>
      obtain ⟨bfinal_val, bits₁⟩ := p
      simp only [hspec_bf, bind, Option.bind] at hspec
      have hbf_bound := Deflate.Spec.readBitsLSB_bound hspec_bf
      cases hspec_bt : Deflate.Spec.readBitsLSB 2 bits₁ with
      | none => simp [hspec_bt] at hspec
      | some q =>
        obtain ⟨btype_val, bits₂⟩ := q
        simp only [hspec_bt] at hspec
        have hbt_bound := Deflate.Spec.readBitsLSB_bound hspec_bt
        -- Native readBits (completeness + inv)
        have ⟨br₁, hrb1, hrest₁, hwf₁, hpos₁⟩ :=
          Deflate.Correctness.readBits_complete br 1 bfinal_val bits₁
            hwf hpos (by omega) hbf_bound hspec_bf
        have ⟨hd₁, _, hple₁⟩ := readBits_inv br br₁ 1 _ hrb1 hpos hple
        have ⟨br₂, hrb2, hrest₂, hwf₂, hpos₂⟩ :=
          Deflate.Correctness.readBits_complete br₁ 2 btype_val bits₂
            hwf₁ hpos₁ (by omega) hbt_bound (by rw [hrest₁]; exact hspec_bt)
        have ⟨hd₂, _, hple₂⟩ := readBits_inv br₁ br₂ 2 _ hrb2 hpos₁ hple₁
        by_cases hbt0 : btype_val = 0
        · -- btype_val = 0: stored block
          subst hbt0
          cases hspec_st : Deflate.Spec.decodeStored bits₂ with
          | none => simp [hspec_st] at hspec
          | some r =>
            obtain ⟨storedBytes, bits₃⟩ := r
            simp only [hspec_st] at hspec
            have hlen' : output.size + storedBytes.length ≤ maxOutputSize := by
              by_cases hbf1 : (bfinal_val == 1) = true
              · rw [if_pos hbf1] at hspec
                simp only [pure, Pure.pure] at hspec
                have heq := Option.some.inj hspec
                have hlen := congrArg List.length heq
                simp only [List.length_append] at hlen
                have : output.data.toList.length = output.size := Array.length_toList
                omega
              · rw [if_neg hbf1] at hspec
                have hpfx := List.IsPrefix.length_le
                  (Deflate.Spec.decode_go_acc_prefix _ _ _ _ hspec)
                have : output.data.toList.length = output.size := Array.length_toList
                simp only [List.length_append] at hpfx; omega
            have ⟨br', hst_nat, hrest₃, hoff₃, hpos₃⟩ :=
              Deflate.Correctness.decodeStored_complete br₂ output maxOutputSize
                storedBytes bits₃ hwf₂ hpos₂ hlen' (by rw [hrest₂]; exact hspec_st)
            have ⟨hd₃, _, hple₃⟩ := decodeStored_inv br₂ br' output
              (output ++ ⟨⟨storedBytes⟩⟩) maxOutputSize hst_nat
            have hil : Inflate.inflateLoop br output fixedLit fixedDist
                maxOutputSize (n + 1) =
              (if (bfinal_val.toUInt32 == 1) = true
                then .ok (output ++ ⟨⟨storedBytes⟩⟩, br'.alignToByte.pos)
                else Inflate.inflateLoop br' (output ++ ⟨⟨storedBytes⟩⟩)
                  fixedLit fixedDist maxOutputSize n) := by
              simp only [Inflate.inflateLoop, bind, Except.bind, hrb1, hrb2, hst_nat]; rfl
            split at hspec
            · -- bfinal == 1: final block
              rename_i hbf1
              simp only [pure, Pure.pure] at hspec
              have heq := Option.some.inj hspec
              have hba_eq : output ++ ⟨⟨storedBytes⟩⟩ = ⟨⟨result⟩⟩ := by
                apply ByteArray.ext; simp [ByteArray.data_append, heq]
              rw [hil, if_pos (Deflate.Correctness.nat_beq_to_uint32_true _ (by omega) hbf1),
                  hba_eq]
              have hgoR : Deflate.Spec.decode.goR br.toBits output.data.toList (n + 1) =
                  some (result, bits₃) := by
                unfold Deflate.Spec.decode.goR
                simp only [hspec_bf, bind, Option.bind, hspec_bt, hspec_st]
                rw [if_pos hbf1]; simp only [pure, Pure.pure, ← heq]
              exact ⟨br', _, bits₃, rfl, rfl, hd₃.trans (hd₂.trans hd₁),
                by rw [hoff₃]; omega, Or.inl hoff₃, hple₃, hrest₃, hgoR⟩
            · -- bfinal ≠ 1: continue
              rename_i hbf1
              have hspec' : Deflate.Spec.decode.go br'.toBits
                  (output ++ ⟨⟨storedBytes⟩⟩).data.toList n = some result := by
                have : (output ++ ⟨⟨storedBytes⟩⟩).data.toList =
                    output.data.toList ++ storedBytes := by
                  simp [ByteArray.data_append, Array.toList_append]
                rw [this, hrest₃]; exact hspec
              obtain ⟨br_final, endPos, remaining, hloop, hep, hdf, hwff, hposf, hplef, hrestf, hgoR_ih⟩ :=
                ih br' (output ++ ⟨⟨storedBytes⟩⟩) (by rw [hoff₃]; omega)
                  (Or.inl hoff₃) hple₃ hspec'
              have hbf_neg := Deflate.Correctness.nat_beq_to_uint32_false _ (by omega) hbf1
              rw [hil, if_neg hbf_neg]
              have hgoR : Deflate.Spec.decode.goR br.toBits output.data.toList (n + 1) =
                  some (result, remaining) := by
                unfold Deflate.Spec.decode.goR
                simp only [hspec_bf, bind, Option.bind, hspec_bt, hspec_st]
                rw [if_neg hbf1]
                have hconv : (output ++ ⟨⟨storedBytes⟩⟩).data.toList =
                    output.data.toList ++ storedBytes := by
                  simp [ByteArray.data_append, Array.toList_append]
                rw [hrest₃] at hgoR_ih; rw [hconv] at hgoR_ih; exact hgoR_ih
              exact ⟨br_final, endPos, remaining, hloop, hep,
                hdf.trans (hd₃.trans (hd₂.trans hd₁)), hwff, hposf, hplef, hrestf, hgoR⟩
        · by_cases hbt1 : btype_val = 1
          · -- btype_val = 1: fixed Huffman
            subst hbt1
            cases hspec_ds : Deflate.Spec.decodeSymbols
                Deflate.Spec.fixedLitLengths Deflate.Spec.fixedDistLengths bits₂ with
            | none => simp [hspec_ds] at hspec
            | some r =>
              obtain ⟨syms, bits₃⟩ := r
              simp only [hspec_ds] at hspec
              cases hspec_lz : Deflate.Spec.resolveLZ77 syms output.data.toList with
              | none => simp [hspec_lz] at hspec
              | some acc' =>
                simp only [hspec_lz] at hspec
                have hacc_le : acc'.length ≤ maxOutputSize := by
                  split at hspec
                  · simp [pure, Pure.pure] at hspec; rw [hspec]; exact hmax
                  · have hpfx := List.IsPrefix.length_le
                      (Deflate.Spec.decode_go_acc_prefix _ _ _ _ hspec)
                    omega
                have hds_bridge : Deflate.Spec.decodeSymbols
                    (Inflate.fixedLitLengths.toList.map UInt8.toNat)
                    (Inflate.fixedDistLengths.toList.map UInt8.toNat)
                    br₂.toBits 1000000000 = some (syms, bits₃) := by
                  rw [hrest₂, Deflate.Correctness.fixedLitLengths_eq,
                      Deflate.Correctness.fixedDistLengths_eq]; exact hspec_ds
                have ⟨br', hhf_nat, hrest₃, hwf₃, hpos₃⟩ :=
                  Deflate.Correctness.decodeHuffman_complete
                    Inflate.fixedLitLengths Inflate.fixedDistLengths
                    fixedLit fixedDist maxOutputSize br₂ output
                    syms bits₃ acc' hwf₂ hpos₂ hflit hfdist
                    (Deflate.Correctness.fixedLitLengths_eq ▸
                      Deflate.Spec.fixedLitLengths_valid)
                    (Deflate.Correctness.fixedDistLengths_eq ▸
                      Deflate.Spec.fixedDistLengths_valid)
                    Deflate.Correctness.fixedLitLengths_size
                    Deflate.Correctness.fixedDistLengths_size
                    hacc_le 1000000000 hds_bridge hspec_lz
                have hdh : Inflate.decodeHuffman br₂ output fixedLit fixedDist
                    maxOutputSize = .ok (⟨⟨acc'⟩⟩, br') := by
                  simp only [Inflate.decodeHuffman]; exact hhf_nat
                have ⟨hd₃, _, hple₃⟩ := decodeHuffman_inv fixedLit fixedDist
                  br₂ br' output ⟨⟨acc'⟩⟩ maxOutputSize hdh hpos₂ hple₂
                have hil : Inflate.inflateLoop br output fixedLit fixedDist
                    maxOutputSize (n + 1) =
                  (if (bfinal_val.toUInt32 == 1) = true
                    then .ok (⟨⟨acc'⟩⟩, br'.alignToByte.pos)
                    else Inflate.inflateLoop br' ⟨⟨acc'⟩⟩
                      fixedLit fixedDist maxOutputSize n) := by
                  simp only [Inflate.inflateLoop, bind, Except.bind,
                    hrb1, hrb2, hdh]; rfl
                split at hspec
                · -- bfinal == 1: final block
                  rename_i hbf1
                  simp [pure, Pure.pure] at hspec; subst hspec
                  rw [hil, if_pos (Deflate.Correctness.nat_beq_to_uint32_true _
                    (by omega) hbf1)]
                  have hgoR : Deflate.Spec.decode.goR br.toBits output.data.toList (n + 1) =
                      some (acc', bits₃) := by
                    unfold Deflate.Spec.decode.goR
                    simp only [hspec_bf, bind, Option.bind, hspec_bt,
                      hspec_ds, hspec_lz]
                    rw [if_pos hbf1]; rfl
                  exact ⟨br', _, bits₃, rfl, rfl, hd₃.trans (hd₂.trans hd₁), hwf₃, hpos₃, hple₃, hrest₃, hgoR⟩
                · -- bfinal ≠ 1: continue
                  rename_i hbf1
                  have hspec' : Deflate.Spec.decode.go br'.toBits acc' n =
                      some result := by rw [hrest₃]; exact hspec
                  obtain ⟨br_final, endPos, remaining, hloop, hep, hdf, hwff, hposf, hplef, hrestf, hgoR_ih⟩ :=
                    ih br' ⟨⟨acc'⟩⟩ hwf₃ hpos₃ hple₃ hspec'
                  rw [hil, if_neg (Deflate.Correctness.nat_beq_to_uint32_false _
                    (by omega) hbf1)]
                  have hgoR : Deflate.Spec.decode.goR br.toBits output.data.toList (n + 1) =
                      some (result, remaining) := by
                    unfold Deflate.Spec.decode.goR
                    simp only [hspec_bf, bind, Option.bind, hspec_bt,
                      hspec_ds, hspec_lz]
                    rw [if_neg hbf1]
                    rw [hrest₃] at hgoR_ih
                    simp at hgoR_ih; exact hgoR_ih
                  exact ⟨br_final, endPos, remaining, hloop, hep,
                    hdf.trans (hd₃.trans (hd₂.trans hd₁)), hwff, hposf, hplef, hrestf, hgoR⟩
          · by_cases hbt2 : btype_val = 2
            · -- btype_val = 2: dynamic Huffman
              subst hbt2
              cases hspec_dt : Deflate.Spec.decodeDynamicTables bits₂ with
              | none => simp [hspec_dt] at hspec
              | some r =>
                obtain ⟨litLens, distLens, bits₃⟩ := r
                simp only [hspec_dt] at hspec
                cases hspec_ds : Deflate.Spec.decodeSymbols litLens distLens bits₃ with
                | none => simp [hspec_ds] at hspec
                | some s =>
                  obtain ⟨syms, bits₄⟩ := s
                  simp only [hspec_ds] at hspec
                  cases hspec_lz : Deflate.Spec.resolveLZ77 syms output.data.toList with
                  | none => simp [hspec_lz] at hspec
                  | some acc' =>
                    simp only [hspec_lz] at hspec
                    have hacc_le : acc'.length ≤ maxOutputSize := by
                      split at hspec
                      · simp [pure, Pure.pure] at hspec; rw [hspec]; exact hmax
                      · have hpfx := List.IsPrefix.length_le
                          (Deflate.Spec.decode_go_acc_prefix _ _ _ _ hspec)
                        omega
                    have ⟨litTree, distTree, br₃, hdt_nat, hrest_dt, hwf₃, hpos₃,
                      hflit_dyn, hfdist_dyn, hvlit_dyn, hvdist_dyn, hsize_lit,
                      hsize_dist⟩ :=
                      Deflate.Correctness.decodeDynamicTrees_complete br₂ litLens
                        distLens bits₃ hwf₂ hpos₂ (by rw [hrest₂]; exact hspec_dt)
                    have ⟨hd_dt, _, hple₃⟩ := decodeDynamicTrees_inv br₂ br₃ litTree
                      distTree hdt_nat hpos₂ hple₂
                    have hlit_rt := Deflate.Correctness.validLengths_toUInt8_roundtrip
                      litLens hvlit_dyn (by omega)
                    have hdist_rt := Deflate.Correctness.validLengths_toUInt8_roundtrip
                      distLens hvdist_dyn (by omega)
                    have hds_bridge : Deflate.Spec.decodeSymbols
                        ((litLens.map Nat.toUInt8).toArray.toList.map UInt8.toNat)
                        ((distLens.map Nat.toUInt8).toArray.toList.map UInt8.toNat)
                        br₃.toBits 1000000000 = some (syms, bits₄) := by
                      rw [hlit_rt, hdist_rt, hrest_dt]; exact hspec_ds
                    have hvlit_bridge : Huffman.Spec.ValidLengths
                        ((litLens.map Nat.toUInt8).toArray.toList.map UInt8.toNat) 15 := by
                      rw [hlit_rt]; exact hvlit_dyn
                    have hvdist_bridge : Huffman.Spec.ValidLengths
                        ((distLens.map Nat.toUInt8).toArray.toList.map UInt8.toNat) 15 := by
                      rw [hdist_rt]; exact hvdist_dyn
                    have hsize_lit' :
                        (litLens.map Nat.toUInt8).toArray.size ≤ UInt16.size := by
                      simp; exact hsize_lit
                    have hsize_dist' :
                        (distLens.map Nat.toUInt8).toArray.size ≤ UInt16.size := by
                      simp; exact hsize_dist
                    have ⟨br', hhf_nat, hrest₄, hwf₄, hpos₄⟩ :=
                      Deflate.Correctness.decodeHuffman_complete
                        (litLens.map Nat.toUInt8).toArray
                        (distLens.map Nat.toUInt8).toArray
                        litTree distTree maxOutputSize br₃ output
                        syms bits₄ acc' hwf₃ hpos₃ hflit_dyn hfdist_dyn
                        hvlit_bridge hvdist_bridge hsize_lit' hsize_dist'
                        hacc_le 1000000000 hds_bridge hspec_lz
                    have hdh : Inflate.decodeHuffman br₃ output litTree distTree
                        maxOutputSize = .ok (⟨⟨acc'⟩⟩, br') := by
                      simp only [Inflate.decodeHuffman]; exact hhf_nat
                    have ⟨hd₄, _, hple₄⟩ := decodeHuffman_inv litTree distTree
                      br₃ br' output ⟨⟨acc'⟩⟩ maxOutputSize hdh hpos₃ hple₃
                    have hil : Inflate.inflateLoop br output fixedLit fixedDist
                        maxOutputSize (n + 1) =
                      (if (bfinal_val.toUInt32 == 1) = true
                        then .ok (⟨⟨acc'⟩⟩, br'.alignToByte.pos)
                        else Inflate.inflateLoop br' ⟨⟨acc'⟩⟩
                          fixedLit fixedDist maxOutputSize n) := by
                      simp only [Inflate.inflateLoop, bind, Except.bind,
                        hrb1, hrb2, hdt_nat, hdh]; rfl
                    split at hspec
                    · -- bfinal == 1: final block
                      rename_i hbf1
                      simp [pure, Pure.pure] at hspec; subst hspec
                      rw [hil, if_pos (Deflate.Correctness.nat_beq_to_uint32_true _
                        (by omega) hbf1)]
                      have hgoR : Deflate.Spec.decode.goR br.toBits output.data.toList (n + 1) =
                          some (acc', bits₄) := by
                        unfold Deflate.Spec.decode.goR
                        simp only [hspec_bf, bind, Option.bind, hspec_bt,
                          hspec_dt, hspec_ds, hspec_lz]
                        rw [if_pos hbf1]; rfl
                      exact ⟨br', _, bits₄, rfl, rfl,
                        hd₄.trans (hd_dt.trans (hd₂.trans hd₁)), hwf₄, hpos₄, hple₄, hrest₄, hgoR⟩
                    · -- bfinal ≠ 1: continue
                      rename_i hbf1
                      have hspec' : Deflate.Spec.decode.go br'.toBits acc' n =
                          some result := by rw [hrest₄]; exact hspec
                      obtain ⟨br_final, endPos, remaining, hloop, hep, hdf, hwff, hposf, hplef, hrestf, hgoR_ih⟩ :=
                        ih br' ⟨⟨acc'⟩⟩ hwf₄ hpos₄ hple₄ hspec'
                      rw [hil, if_neg (Deflate.Correctness.nat_beq_to_uint32_false _
                        (by omega) hbf1)]
                      have hgoR : Deflate.Spec.decode.goR br.toBits output.data.toList (n + 1) =
                          some (result, remaining) := by
                        unfold Deflate.Spec.decode.goR
                        simp only [hspec_bf, bind, Option.bind, hspec_bt,
                          hspec_dt, hspec_ds, hspec_lz]
                        rw [if_neg hbf1]
                        rw [hrest₄] at hgoR_ih
                        simp at hgoR_ih; exact hgoR_ih
                      exact ⟨br_final, endPos, remaining, hloop, hep,
                        hdf.trans (hd₄.trans (hd_dt.trans (hd₂.trans hd₁))),
                        hwff, hposf, hplef, hrestf, hgoR⟩
            · -- btype_val ≥ 3: reserved (spec returns none)
              have hbt3 : btype_val = 3 := by omega
              subst hbt3; simp at hspec

/-- After a successful `inflateRaw`, the returned endPos ≤ data.size. -/
theorem inflateRaw_endPos_le (data : ByteArray) (startPos maxOut : Nat)
    (result : ByteArray) (endPos : Nat)
    (h : Inflate.inflateRaw data startPos maxOut = .ok (result, endPos)) :
    endPos ≤ data.size := by
  simp only [Inflate.inflateRaw, bind, Except.bind] at h
  cases hflit : HuffTree.fromLengths Inflate.fixedLitLengths with
  | error e => simp [hflit] at h
  | ok fixedLit =>
    simp only [hflit] at h
    cases hfdist : HuffTree.fromLengths Inflate.fixedDistLengths with
    | error e => simp [hfdist] at h
    | ok fixedDist =>
      simp only [hfdist] at h
      have hple : startPos ≤ data.size := by
        -- If startPos > data.size, readBit errors, inflateLoop errors, contradicting h.
        by_cases hle : startPos ≤ data.size
        · exact hle
        · exfalso
          have hgt : startPos ≥ data.size := by omega
          -- inflateLoop fuel+1 starts with readBits 1 → readBit → checks pos ≥ data.size
          -- The first operation in inflateLoop is readBits 1, which calls readBit.
          -- readBit checks pos ≥ data.size and errors if so.
          have hfail : (BitReader.mk data startPos 0).readBit =
              .error "BitReader: unexpected end of input" := by
            simp only [BitReader.readBit]
            simp [show startPos ≥ data.size from hgt]
          -- inflateLoop fuel+1 → readBits 1 → readBit → error
          -- This contradicts h : ... = .ok (result, endPos)
          simp only [Inflate.inflateLoop, bind, Except.bind,
            BitReader.readBits, BitReader.readBits.go, hfail] at h
          simp at h
      exact inflateLoop_endPos_le ⟨data, startPos, 0⟩ .empty fixedLit fixedDist
        maxOut 10001 result endPos (Or.inl rfl) hple h

/-! ## alignToByte lower bound from short remaining bits -/

/-- If the remaining bits `toBits` have length < 8, then `alignToByte.pos ≥ data.size`.
    This is because < 8 remaining bits means we're in the last byte (or past it). -/
private theorem alignToByte_pos_ge_of_toBits_short (br : BitReader)
    (hwf : br.bitOff < 8)
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (hple : br.pos ≤ br.data.size)
    (hshort : br.toBits.length < 8) :
    br.alignToByte.pos ≥ br.data.size := by
  have htl := Deflate.Correctness.toBits_length br
  simp only [BitReader.alignToByte]
  split
  · -- bitOff = 0: alignToByte is no-op, endPos = pos
    rename_i h0
    have h0' : br.bitOff = 0 := by simp_all
    rw [h0', Nat.add_zero] at htl
    have hle8 : br.pos * 8 ≤ br.data.size * 8 := Nat.mul_le_mul_right 8 hple
    have htl_add : br.toBits.length + br.pos * 8 = br.data.size * 8 := by
      rw [htl]; exact Nat.sub_add_cancel hle8
    omega
  · -- bitOff ≠ 0: alignToByte advances pos by 1
    rename_i hne
    cases hpos with
    | inl h => simp [h] at hne
    | inr h =>
      -- pos < data.size, so pos * 8 + bitOff < data.size * 8
      have hlt8 : br.pos * 8 + br.bitOff < br.data.size * 8 := by omega
      -- Convert: toBits.length + (pos * 8 + bitOff) = data.size * 8
      have htl_add : br.toBits.length + (br.pos * 8 + br.bitOff) = br.data.size * 8 := by
        rw [htl]; exact Nat.sub_add_cancel (Nat.le_of_lt hlt8)
      -- data.size * 8 < 8 + pos * 8 + bitOff ≤ 8 + pos * 8 + 7 = (pos+1)*8 - 1
      -- So data.size ≤ pos + 1, i.e. (pos + 1) ≥ data.size
      show br.pos + 1 ≥ br.data.size
      omega

/-! ## endPos exactness: ≥ direction -/

/-- After a successful `inflateRaw` on `prefix ++ deflated` starting at
    `prefix.size`, the endPos ≥ `prefix.size + deflated.size` (i.e., the decoder
    consumes all of `deflated`). Combined with `inflateRaw_endPos_le`, this gives
    endPos = `(prefix ++ deflated).size` exactly.

    The `hpad` hypothesis provides the encoder's padding decomposition: the deflated
    bytes split into content bits plus short padding (< 8 bits), with the spec decoder
    succeeding on just the content bits. This is provided by the encoder correctness
    theorems (`deflateFixed_spec`, `deflateLazy_spec`, `deflateDynamic_spec`).

    The proof uses `inflateLoop_complete_ext` to get the final BitReader state,
    then a counting argument: the native decoder consumes the same bits as the spec
    decoder plus at most 7 padding bits, so it ends within the last byte. -/
theorem inflateRaw_endPos_ge (pfx deflated : ByteArray)
    (maxOut : Nat) (result : ByteArray) (endPos : Nat)
    (h : Inflate.inflateRaw (pfx ++ deflated) pfx.size maxOut =
      .ok (result, endPos))
    (hspec : Deflate.Spec.decode.go
      (Deflate.Spec.bytesToBits deflated) [] 10001 =
      some result.data.toList)
    (hpad : ∃ remaining,
      Deflate.Spec.decode.goR (Deflate.Spec.bytesToBits deflated) [] 10001 =
        some (result.data.toList, remaining) ∧
      remaining.length < 8)
    (hmax : result.data.toList.length ≤ maxOut) :
    endPos ≥ (pfx ++ deflated).size := by
  obtain ⟨pad_remaining, hgoR_pad, hpadlen⟩ := hpad
  simp only [Inflate.inflateRaw, bind, Except.bind] at h
  cases hflit : HuffTree.fromLengths Inflate.fixedLitLengths with
  | error e => simp [hflit] at h
  | ok fixedLit =>
    simp only [hflit] at h
    cases hfdist : HuffTree.fromLengths Inflate.fixedDistLengths with
    | error e => simp [hfdist] at h
    | ok fixedDist =>
      simp only [hfdist] at h
      -- br := BitReader at pfx.size with bitOff = 0
      -- br.toBits = (bytesToBits (pfx ++ deflated)).drop (pfx.size * 8)
      --           = bytesToBits deflated
      have hbr_toBits : (BitReader.mk (pfx ++ deflated) pfx.size 0).toBits =
          Deflate.Spec.bytesToBits deflated := by
        simp only [BitReader.toBits]
        rw [show pfx.size * 8 + 0 = pfx.size * 8 from by omega]
        rw [bytesToBits_append]
        rw [← Deflate.Spec.bytesToBits_length pfx, List.drop_left]
      -- Extract result and endPos from inflateLoop (fuel 10001)
      have hspec' : Deflate.Spec.decode.go
          (BitReader.mk (pfx ++ deflated) pfx.size 0).toBits [] 10001 =
          some result.data.toList := by rw [hbr_toBits]; exact hspec
      obtain ⟨br_final, endPos', remaining, hloop, hep, hdf, hwff, hposf, hplef, hrestf, hgoR⟩ :=
        inflateLoop_complete_ext
          ⟨pfx ++ deflated, pfx.size, 0⟩ .empty fixedLit fixedDist
          maxOut result.data.toList (by simp) (by simp)
          (by simp [ByteArray.size_append])
          hflit hfdist hmax 10001 hspec'
      -- endPos' = endPos (by determinism of inflateLoop)
      have hloop_eq : Inflate.inflateLoop ⟨pfx ++ deflated, pfx.size, 0⟩
          .empty fixedLit fixedDist maxOut 10001 = .ok (result, endPos) := h
      have hep_eq : endPos = endPos' := by
        have : Inflate.inflateLoop ⟨pfx ++ deflated, pfx.size, 0⟩
            .empty fixedLit fixedDist maxOut 10001 =
            .ok (⟨⟨result.data.toList⟩⟩, endPos') := hloop
        rw [show (⟨⟨result.data.toList⟩⟩ : ByteArray) = result from by simp] at this
        have := hloop_eq.symm.trans this
        simp only [Except.ok.injEq, Prod.mk.injEq] at this
        exact this.2
      rw [hep_eq, hep]
      rw [show (pfx ++ deflated).size = br_final.data.size from by
        simp [hdf]]
      apply alignToByte_pos_ge_of_toBits_short br_final hwff hposf hplef
      rw [hrestf]
      -- remaining.length < 8 by determinism of decode.goR:
      -- hgoR gives goR on br.toBits = bytesToBits deflated → some (result, remaining)
      -- hgoR_pad gives goR on bytesToBits deflated → some (result, pad_remaining)
      -- with pad_remaining.length < 8
      -- By injectivity: remaining = pad_remaining
      have hgoR' : Deflate.Spec.decode.goR (Deflate.Spec.bytesToBits deflated) []
          10001 = some (result.data.toList, remaining) := by
        rw [← hbr_toBits]; exact hgoR
      have : some (result.data.toList, remaining) =
          some (result.data.toList, pad_remaining) :=
        hgoR'.symm.trans hgoR_pad
      have heq := (Option.some.inj this)
      have : remaining = pad_remaining := (Prod.mk.inj heq).2
      rw [this]; exact hpadlen

/-- endPos exactness: combining ≤ and ≥ gives equality. -/
theorem inflateRaw_endPos_eq (pfx deflated : ByteArray)
    (maxOut : Nat) (result : ByteArray) (endPos : Nat)
    (h : Inflate.inflateRaw (pfx ++ deflated) pfx.size maxOut =
      .ok (result, endPos))
    (hspec : Deflate.Spec.decode.go
      (Deflate.Spec.bytesToBits deflated) [] 10001 =
      some result.data.toList)
    (hpad : ∃ remaining,
      Deflate.Spec.decode.goR (Deflate.Spec.bytesToBits deflated) [] 10001 =
        some (result.data.toList, remaining) ∧
      remaining.length < 8)
    (hmax : result.data.toList.length ≤ maxOut) :
    endPos = (pfx ++ deflated).size :=
  Nat.le_antisymm
    (inflateRaw_endPos_le _ _ _ _ _ h)
    (inflateRaw_endPos_ge pfx deflated maxOut result endPos h hspec hpad hmax)

/-! ## inflateRaw completeness for non-zero startPos -/

/-- Completeness for `inflateRaw` at arbitrary `startPos`: if the spec decode
    succeeds on the bits starting at `startPos * 8`, then the native inflate
    also succeeds with the same result. The spec fuel must be ≤ 10001 (the
    native inflate's block fuel). -/
theorem inflateRaw_complete (data : ByteArray) (startPos maxOutputSize : Nat)
    (result : List UInt8)
    (hsize : result.length ≤ maxOutputSize)
    (specFuel : Nat) (hfuel : specFuel ≤ 10001)
    (hspec : Deflate.Spec.decode.go
        ((Deflate.Spec.bytesToBits data).drop (startPos * 8)) [] specFuel =
        some result) :
    ∃ endPos,
      Inflate.inflateRaw data startPos maxOutputSize =
        .ok (⟨⟨result⟩⟩, endPos) := by
  simp only [Inflate.inflateRaw, bind, Except.bind]
  obtain ⟨fixedLit, hflit⟩ := Zip.Spec.DeflateStoredCorrect.fromLengths_fixedLit_ok
  obtain ⟨fixedDist, hfdist⟩ := Zip.Spec.DeflateStoredCorrect.fromLengths_fixedDist_ok
  rw [hflit, hfdist]
  have hbr_wf : (BitReader.mk data startPos 0).bitOff < 8 := by simp
  have hbr_pos : (BitReader.mk data startPos 0).bitOff = 0 ∨
      (BitReader.mk data startPos 0).pos <
      (BitReader.mk data startPos 0).data.size := by simp
  have hbr_bits : (BitReader.mk data startPos 0).toBits =
      (Deflate.Spec.bytesToBits data).drop (startPos * 8) := by
    simp [BitReader.toBits]
  -- Lift specFuel to 10001 via fuel independence
  -- decode bits fuel = decode.go bits [] fuel, so we can use the public API
  have hgo : Deflate.Spec.decode.go (BitReader.mk data startPos 0).toBits
      ByteArray.empty.data.toList 10001 = some result := by
    rw [hbr_bits]
    -- decode.go bits [] fuel = decode bits fuel
    show Deflate.Spec.decode
        ((Deflate.Spec.bytesToBits data).drop (startPos * 8)) 10001 = some result
    have h10001 : specFuel + (10001 - specFuel) = 10001 := by omega
    rw [← h10001]
    exact Deflate.Spec.decode_fuel_independent _ _ _ hspec _
  exact Deflate.Correctness.inflateLoop_complete
    ⟨data, startPos, 0⟩ .empty fixedLit fixedDist maxOutputSize result
    hbr_wf hbr_pos hflit hfdist hsize 10001 hgo

/-! ## inflateRaw suffix invariance

If inflateRaw succeeds on `data`, it also succeeds on `data ++ suffix`
with the SAME result and endPos. This is because all BitReader operations
read bytes at positions `pos < data.size`, and appending a suffix
doesn't change those bytes.

We prove this by first establishing suffix invariance for each basic
BitReader operation, then composing through the inflate machinery. -/

private abbrev brAppend (br : BitReader) (suffix : ByteArray) : BitReader :=
  ⟨br.data ++ suffix, br.pos, br.bitOff⟩

/-- readBit with appended suffix produces the same result. -/
private theorem readBit_append (br : BitReader) (suffix : ByteArray)
    (bit : UInt32) (br' : BitReader)
    (h : br.readBit = .ok (bit, br')) :
    (brAppend br suffix).readBit = .ok (bit, brAppend br' suffix) := by
  simp only [brAppend, BitReader.readBit] at h ⊢
  split at h
  · simp at h
  · rename_i hge
    have hlt : br.pos < br.data.size := by omega
    rw [if_neg (show ¬ br.pos ≥ (br.data ++ suffix).size from by
      simp [ByteArray.size_append]; omega)]
    -- Convert getElem! to getElem in both h and goal, then use append lemma
    rw [getElem!_pos (br.data ++ suffix) br.pos (by simp [ByteArray.size_append]; omega)]
    rw [getElem!_pos br.data br.pos hlt] at h
    rw [ByteArray.getElem_append_left hlt]
    -- Now h and goal both have br.data[br.pos], split on bitOff+1 ≥ 8
    split at h <;> {
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨hval, hbr'⟩ := h
      subst hbr'; subst hval
      split <;> simp_all
    }

/-- readBits.go with appended suffix produces the same result. -/
private theorem readBits_go_append (br : BitReader) (suffix : ByteArray)
    (acc : UInt32) (shift n : Nat) (val : UInt32) (br' : BitReader)
    (h : BitReader.readBits.go br acc shift n = .ok (val, br')) :
    BitReader.readBits.go (brAppend br suffix) acc shift n =
    .ok (val, brAppend br' suffix) := by
  induction n generalizing br acc shift with
  | zero =>
    simp only [brAppend, BitReader.readBits.go] at h ⊢
    obtain ⟨rfl, rfl⟩ := h; simp
  | succ n ih =>
    simp only [BitReader.readBits.go, bind, Except.bind] at h ⊢
    cases hrb : br.readBit with
    | error e => simp [hrb] at h
    | ok p =>
      obtain ⟨bit, br₁⟩ := p; simp only [hrb] at h
      rw [readBit_append br suffix bit br₁ hrb]
      exact ih br₁ _ _ h

/-- readBits with appended suffix produces the same result. -/
private theorem readBits_append (br : BitReader) (suffix : ByteArray)
    (n : Nat) (val : UInt32) (br' : BitReader)
    (h : br.readBits n = .ok (val, br')) :
    (brAppend br suffix).readBits n = .ok (val, brAppend br' suffix) :=
  readBits_go_append br suffix 0 0 n val br' h

/-- alignToByte with appended suffix. -/
private theorem alignToByte_append (br : BitReader) (suffix : ByteArray) :
    (brAppend br suffix).alignToByte = brAppend br.alignToByte suffix := by
  simp only [brAppend, BitReader.alignToByte]; split <;> rfl

/-- readUInt16LE with appended suffix produces the same result. -/
private theorem readUInt16LE_append (br : BitReader) (suffix : ByteArray)
    (val : UInt16) (br' : BitReader)
    (h : br.readUInt16LE = .ok (val, br')) :
    (brAppend br suffix).readUInt16LE = .ok (val, brAppend br' suffix) := by
  -- readUInt16LE = alignToByte then read two bytes
  simp only [BitReader.readUInt16LE] at h ⊢
  -- Replace alignToByte on appended reader with appended alignToByte
  rw [alignToByte_append]; simp only []
  -- Now goal has data ++ suffix, pos, bitOff from br.alignToByte
  -- Split on bounds in h
  by_cases hle : br.alignToByte.pos + 2 > br.alignToByte.data.size
  · rw [if_pos hle] at h; simp at h
  · rw [if_neg hle] at h
    rw [if_neg (show ¬ br.alignToByte.pos + 2 > (br.alignToByte.data ++ suffix).size from by
      simp [ByteArray.size_append]; omega)]
    rw [getElem!_ba_append_left _ _ _ (by omega),
        getElem!_ba_append_left _ _ _ (by omega)]
    -- h: .ok (val_expr, {data:=orig, pos:=p+2, bitOff:=bo}) = .ok (val, br')
    -- goal: .ok (val_expr, {data:=orig++suffix, pos:=p+2, bitOff:=bo}) = .ok (val, brAppend br' suffix)
    simp only [Except.ok.injEq, Prod.mk.injEq] at h ⊢
    obtain ⟨hval, hbr'⟩ := h
    subst hbr'; constructor
    · exact hval
    · simp

/-- readBytes with appended suffix produces the same result. -/
private theorem readBytes_append (br : BitReader) (suffix : ByteArray)
    (n : Nat) (bytes : ByteArray) (br' : BitReader)
    (h : br.readBytes n = .ok (bytes, br')) :
    (brAppend br suffix).readBytes n = .ok (bytes, brAppend br' suffix) := by
  simp only [BitReader.readBytes] at h ⊢
  rw [alignToByte_append]; simp only []
  by_cases hle : br.alignToByte.pos + n > br.alignToByte.data.size
  · rw [if_pos hle] at h; simp at h
  · rw [if_neg hle] at h
    rw [if_neg (show ¬ br.alignToByte.pos + n > (br.alignToByte.data ++ suffix).size from by
      simp [ByteArray.size_append]; omega)]
    -- ByteArray.extract on (data ++ suffix) within data bounds
    have hext : (br.alignToByte.data ++ suffix).extract br.alignToByte.pos
        (br.alignToByte.pos + n) =
        br.alignToByte.data.extract br.alignToByte.pos (br.alignToByte.pos + n) := by
      apply ByteArray.ext
      simp [ByteArray.data_extract, ByteArray.data_append, Array.extract_append]
      omega
    rw [hext]
    -- h: .ok (extract_result, {data:=orig, pos:=p+n, bitOff:=bo}) = .ok (bytes, br')
    -- goal: .ok (extract_result, {data:=orig++suffix, pos:=p+n, bitOff:=bo}) = .ok (bytes, brAppend br' suffix)
    simp only [Except.ok.injEq, Prod.mk.injEq] at h ⊢
    obtain ⟨hval, hbr'⟩ := h
    subst hbr'; constructor
    · exact hval
    · simp

/-! ### Higher-level suffix invariance -/

/-- HuffTree.decode.go with appended suffix. -/
private theorem decode_go_append (tree : HuffTree) (br : BitReader) (suffix : ByteArray)
    (n : Nat) (sym : UInt16) (br' : BitReader)
    (h : HuffTree.decode.go tree br n = .ok (sym, br')) :
    HuffTree.decode.go tree (brAppend br suffix) n = .ok (sym, brAppend br' suffix) := by
  induction tree generalizing br n with
  | leaf s =>
    simp only [HuffTree.decode.go] at h ⊢
    obtain ⟨rfl, rfl⟩ := h; simp
  | empty => simp [HuffTree.decode.go] at h
  | node z o ihz iho =>
    simp only [HuffTree.decode.go, bind, Except.bind] at h ⊢
    split at h
    · simp at h
    · rename_i hle
      rw [if_neg hle]
      cases hrb : br.readBit with
      | error e => simp [hrb] at h
      | ok p =>
        obtain ⟨bit, br₁⟩ := p; simp only [hrb] at h
        rw [readBit_append br suffix bit br₁ hrb]; dsimp only []
        split at h
        · rw [if_pos (by assumption)]; exact ihz br₁ _ h
        · rw [if_neg (by assumption)]; exact iho br₁ _ h

/-- HuffTree.decode with appended suffix. -/
private theorem huffDecode_append (tree : HuffTree) (br : BitReader) (suffix : ByteArray)
    (sym : UInt16) (br' : BitReader)
    (h : tree.decode br = .ok (sym, br')) :
    tree.decode (brAppend br suffix) = .ok (sym, brAppend br' suffix) :=
  decode_go_append tree br suffix 0 sym br' h

/-- decodeStored with appended suffix. -/
private theorem decodeStored_append (br : BitReader) (suffix : ByteArray)
    (output : ByteArray) (maxOut : Nat) (result : ByteArray) (br' : BitReader)
    (h : Inflate.decodeStored br output maxOut = .ok (result, br')) :
    Inflate.decodeStored (brAppend br suffix) output maxOut =
      .ok (result, brAppend br' suffix) := by
  simp only [Inflate.decodeStored, bind, Except.bind] at h ⊢
  cases h1 : br.readUInt16LE with
  | error e => simp [h1] at h
  | ok p1 =>
    obtain ⟨len, br₁⟩ := p1; simp only [h1] at h
    rw [readUInt16LE_append br suffix len br₁ h1]; dsimp only []
    cases h2 : br₁.readUInt16LE with
    | error e => simp [h2] at h
    | ok p2 =>
      obtain ⟨nlen, br₂⟩ := p2; simp only [h2] at h
      rw [readUInt16LE_append br₁ suffix nlen br₂ h2]; dsimp only []
      -- handle `len ^^^ nlen != 65535` guard
      by_cases hxor : (len ^^^ nlen != 65535) = true
      · rw [if_pos hxor] at h ⊢; simp at h
      · rw [if_neg hxor] at h ⊢
        -- handle `output.size + len.toNat > maxOut` guard
        by_cases hmaxOut : output.size + len.toNat > maxOut
        · simp only [pure, Except.pure] at h ⊢; rw [if_pos hmaxOut] at h ⊢; simp at h
        · simp only [pure, Except.pure] at h ⊢; rw [if_neg hmaxOut] at h ⊢
          cases h3 : br₂.readBytes len.toNat with
          | error e => simp [h3] at h
          | ok p3 =>
            obtain ⟨bytes, br₃⟩ := p3; simp only [h3] at h
            rw [readBytes_append br₂ suffix len.toNat bytes br₃ h3]; dsimp only []
            simp only [Except.ok.injEq, Prod.mk.injEq] at h ⊢
            obtain ⟨hval, hbr'⟩ := h; subst hbr'; exact ⟨hval, rfl⟩

/-- readCLCodeLengths with appended suffix. -/
private theorem readCLCodeLengths_append (br : BitReader) (suffix : ByteArray)
    (clLengths : Array UInt8) (i numCodeLen : Nat)
    (result : Array UInt8) (br' : BitReader)
    (h : Inflate.readCLCodeLengths br clLengths i numCodeLen = .ok (result, br')) :
    Inflate.readCLCodeLengths (brAppend br suffix) clLengths i numCodeLen =
      .ok (result, brAppend br' suffix) := by
  unfold Inflate.readCLCodeLengths at h ⊢
  by_cases hlt : i < numCodeLen
  · -- i < numCodeLen: recursive case
    rw [if_pos hlt] at h ⊢
    simp only [bind, Except.bind] at h ⊢
    cases hrb : br.readBits 3 with
    | error e => simp [hrb] at h
    | ok p =>
      obtain ⟨v, br₁⟩ := p; simp only [hrb] at h
      rw [readBits_append br suffix 3 v br₁ hrb]; dsimp only []
      exact readCLCodeLengths_append br₁ suffix _ (i + 1) numCodeLen result br' h
  · -- i ≥ numCodeLen: base case
    rw [if_neg hlt] at h ⊢
    simp only [Except.ok.injEq, Prod.mk.injEq] at h ⊢
    obtain ⟨hval, hbr'⟩ := h; subst hbr'; exact ⟨hval, rfl⟩
termination_by numCodeLen - i

/-- decodeCLSymbols with appended suffix. -/
private theorem decodeCLSymbols_append (clTree : HuffTree) (br : BitReader) (suffix : ByteArray)
    (codeLengths : Array UInt8) (idx totalCodes fuel : Nat)
    (result : Array UInt8) (br' : BitReader)
    (h : Inflate.decodeCLSymbols clTree br codeLengths idx totalCodes fuel =
      .ok (result, br')) :
    Inflate.decodeCLSymbols clTree (brAppend br suffix) codeLengths idx totalCodes fuel =
      .ok (result, brAppend br' suffix) := by
  induction fuel generalizing br codeLengths idx with
  | zero => unfold Inflate.decodeCLSymbols at h; simp at h
  | succ n ih =>
    unfold Inflate.decodeCLSymbols at h ⊢
    by_cases hge : idx ≥ totalCodes
    · rw [if_pos hge] at h ⊢
      simp only [Except.ok.injEq, Prod.mk.injEq] at h ⊢
      obtain ⟨hval, hbr'⟩ := h; subst hbr'; exact ⟨hval, rfl⟩
    · rw [if_neg hge] at h ⊢
      simp only [bind, Except.bind] at h ⊢
      cases hd : clTree.decode br with
      | error e => simp [hd] at h
      | ok p =>
        obtain ⟨sym, br₁⟩ := p; simp only [hd] at h
        rw [huffDecode_append clTree br suffix sym br₁ hd]; dsimp only []
        -- sym < 16: literal code length
        by_cases hs16 : sym < 16
        · rw [if_pos hs16] at h ⊢; exact ih br₁ _ (idx + 1) h
        · rw [if_neg hs16] at h ⊢
          -- sym == 16: repeat previous
          by_cases hs16eq : (sym == 16) = true
          · rw [if_pos hs16eq] at h ⊢
            by_cases hidx0 : (idx == 0) = true
            · rw [if_pos hidx0] at h ⊢; simp at h
            · rw [if_neg hidx0] at h ⊢
              simp only [pure, Except.pure] at h ⊢
              cases hrb : br₁.readBits 2 with
              | error e => simp [hrb] at h
              | ok p =>
                obtain ⟨rep, br₂⟩ := p; simp only [hrb] at h
                rw [readBits_append br₁ suffix 2 rep br₂ hrb]; dsimp only []
                by_cases hgt : idx + (rep.toNat + 3) > totalCodes
                · rw [if_pos hgt] at h ⊢; simp at h
                · rw [if_neg hgt] at h ⊢
                  exact ih br₂ _ _ h
          · rw [if_neg hs16eq] at h ⊢
            -- sym == 17: repeat 0 (short)
            by_cases hs17 : (sym == 17) = true
            · rw [if_pos hs17] at h ⊢
              cases hrb : br₁.readBits 3 with
              | error e => simp [hrb] at h
              | ok p =>
                obtain ⟨rep, br₂⟩ := p; simp only [hrb] at h
                rw [readBits_append br₁ suffix 3 rep br₂ hrb]; dsimp only []
                by_cases hgt : idx + (rep.toNat + 3) > totalCodes
                · rw [if_pos hgt] at h ⊢; simp at h
                · rw [if_neg hgt] at h ⊢
                  simp only [pure, Except.pure] at h ⊢
                  exact ih br₂ _ _ h
            · rw [if_neg hs17] at h ⊢
              -- sym == 18: repeat 0 (long)
              by_cases hs18 : (sym == 18) = true
              · rw [if_pos hs18] at h ⊢
                cases hrb : br₁.readBits 7 with
                | error e => simp [hrb] at h
                | ok p =>
                  obtain ⟨rep, br₂⟩ := p; simp only [hrb] at h
                  rw [readBits_append br₁ suffix 7 rep br₂ hrb]; dsimp only []
                  by_cases hgt : idx + (rep.toNat + 11) > totalCodes
                  · rw [if_pos hgt] at h ⊢; simp at h
                  · rw [if_neg hgt] at h ⊢
                    exact ih br₂ _ _ h
              · rw [if_neg hs18] at h ⊢; simp at h

/-- decodeDynamicTrees with appended suffix. -/
private theorem decodeDynamicTrees_append (br : BitReader) (suffix : ByteArray)
    (litTree distTree : HuffTree) (br' : BitReader)
    (h : Inflate.decodeDynamicTrees br = .ok (litTree, distTree, br')) :
    Inflate.decodeDynamicTrees (brAppend br suffix) =
      .ok (litTree, distTree, brAppend br' suffix) := by
  unfold Inflate.decodeDynamicTrees at h ⊢
  simp only [bind, Except.bind] at h ⊢
  -- readBits 5 (hlit)
  cases hlit_eq : br.readBits 5 with
  | error e => simp [hlit_eq] at h
  | ok p =>
    obtain ⟨hlit, br₁⟩ := p; simp only [hlit_eq] at h
    rw [readBits_append br suffix 5 hlit br₁ hlit_eq]; dsimp only []
    -- readBits 5 (hdist)
    cases hdist_eq : br₁.readBits 5 with
    | error e => simp [hdist_eq] at h
    | ok p =>
      obtain ⟨hdist, br₂⟩ := p; simp only [hdist_eq] at h
      rw [readBits_append br₁ suffix 5 hdist br₂ hdist_eq]; dsimp only []
      -- readBits 4 (hclen)
      cases hclen_eq : br₂.readBits 4 with
      | error e => simp [hclen_eq] at h
      | ok p =>
        obtain ⟨hclen, br₃⟩ := p; simp only [hclen_eq] at h
        rw [readBits_append br₂ suffix 4 hclen br₃ hclen_eq]; dsimp only []
        -- readCLCodeLengths
        cases hcl_eq : Inflate.readCLCodeLengths br₃ (.replicate 19 0) 0
            (hclen.toNat + 4) with
        | error e => simp [hcl_eq] at h
        | ok p =>
          obtain ⟨clLengths, br₄⟩ := p; simp only [hcl_eq] at h
          rw [readCLCodeLengths_append br₃ suffix (.replicate 19 0) 0
              (hclen.toNat + 4) clLengths br₄ hcl_eq]; dsimp only []
          -- HuffTree.fromLengths clLengths (pure, no BitReader)
          cases hft_eq : HuffTree.fromLengths clLengths 7 with
          | error e => simp [hft_eq] at h
          | ok clTree =>
            simp only [hft_eq] at h; dsimp only [] at h ⊢
            -- decodeCLSymbols
            have htc : hlit.toNat + 257 + (hdist.toNat + 1) =
                hlit.toNat + 257 + (hdist.toNat + 1) := rfl
            cases hcls_eq : Inflate.decodeCLSymbols clTree br₄
                (.replicate (hlit.toNat + 257 + (hdist.toNat + 1)) 0) 0
                (hlit.toNat + 257 + (hdist.toNat + 1))
                (hlit.toNat + 257 + (hdist.toNat + 1) + 1) with
            | error e => simp [hcls_eq] at h
            | ok p =>
              obtain ⟨codeLengths, br₅⟩ := p; simp only [hcls_eq] at h
              rw [decodeCLSymbols_append clTree br₄ suffix
                  (.replicate (hlit.toNat + 257 + (hdist.toNat + 1)) 0) 0
                  (hlit.toNat + 257 + (hdist.toNat + 1))
                  (hlit.toNat + 257 + (hdist.toNat + 1) + 1)
                  codeLengths br₅ hcls_eq]; dsimp only []
              -- fromLengths litLenLengths (pure)
              cases hlt_eq : HuffTree.fromLengths (codeLengths.extract 0 (hlit.toNat + 257)) with
              | error e => simp [hlt_eq] at h
              | ok litTree' =>
                simp only [hlt_eq] at h; dsimp only [] at h ⊢
                -- fromLengths distLengths (pure)
                cases hdt_eq : HuffTree.fromLengths
                    (codeLengths.extract (hlit.toNat + 257)
                      (hlit.toNat + 257 + (hdist.toNat + 1))) with
                | error e => simp [hdt_eq] at h
                | ok distTree' =>
                  simp only [hdt_eq] at h; dsimp only [] at h ⊢
                  -- Final: pure reduces to Except.ok
                  simp only [pure, Except.pure] at h ⊢
                  have hinj := Except.ok.inj h
                  simp only [Prod.mk.injEq] at hinj
                  obtain ⟨h1, h2, h3⟩ := hinj
                  subst h1; subst h2; subst h3; rfl

set_option maxRecDepth 4096 in
/-- decodeHuffman.go with appended suffix. -/
private theorem decodeHuffman_go_append (litTree distTree : HuffTree)
    (br : BitReader) (suffix : ByteArray) (output : ByteArray) (maxOut fuel : Nat)
    (result : ByteArray) (br' : BitReader)
    (h : Inflate.decodeHuffman.go litTree distTree maxOut br output fuel =
      .ok (result, br')) :
    Inflate.decodeHuffman.go litTree distTree maxOut (brAppend br suffix) output fuel =
      .ok (result, brAppend br' suffix) := by
  induction fuel generalizing br output with
  | zero => unfold Inflate.decodeHuffman.go at h; simp at h
  | succ n ih =>
    unfold Inflate.decodeHuffman.go at h ⊢
    simp only [bind, Except.bind] at h ⊢
    -- Decode literal/length symbol
    cases hd : litTree.decode br with
    | error e => simp [hd] at h
    | ok p =>
      obtain ⟨sym, br₁⟩ := p; simp only [hd] at h
      rw [huffDecode_append litTree br suffix sym br₁ hd]; dsimp only []
      by_cases hsym_lit : sym < 256
      · -- Literal byte
        rw [if_pos hsym_lit] at h ⊢
        by_cases hmax : output.size ≥ maxOut
        · rw [if_pos hmax] at h; simp at h
        · rw [if_neg hmax] at h ⊢
          exact ih br₁ (output.push sym.toUInt8) h
      · rw [if_neg hsym_lit] at h ⊢
        by_cases hsym_end : (sym == 256) = true
        · -- End of block
          rw [if_pos hsym_end] at h ⊢
          simp only [Except.ok.injEq, Prod.mk.injEq] at h ⊢
          obtain ⟨h1, h2⟩ := h; subst h1; subst h2; exact ⟨rfl, rfl⟩
        · -- Length-distance pair
          rw [if_neg hsym_end] at h ⊢
          -- Check idx bounds
          by_cases hidx : sym.toNat - 257 ≥ Inflate.lengthBase.size
          · rw [if_pos hidx] at h; simp at h
          · rw [if_neg hidx] at h ⊢
            simp only [pure, Except.pure] at h ⊢
            -- readBits for extra length bits
            cases hrb1 : br₁.readBits (Inflate.lengthExtra[sym.toNat - 257]!).toNat with
            | error e => simp [hrb1] at h
            | ok p =>
              obtain ⟨extraBits, br₂⟩ := p; simp only [hrb1] at h
              rw [readBits_append br₁ suffix _ extraBits br₂ hrb1]; dsimp only []
              -- Decode distance symbol
              cases hdd : distTree.decode br₂ with
              | error e => simp [hdd] at h
              | ok p =>
                obtain ⟨distSym, br₃⟩ := p; simp only [hdd] at h
                rw [huffDecode_append distTree br₂ suffix distSym br₃ hdd]; dsimp only []
                -- Check dIdx bounds
                by_cases hdidx : distSym.toNat ≥ Inflate.distBase.size
                · rw [if_pos hdidx] at h; simp at h
                · rw [if_neg hdidx] at h ⊢
                  -- readBits for extra distance bits
                  cases hrb2 : br₃.readBits (Inflate.distExtra[distSym.toNat]!).toNat with
                  | error e => simp [hrb2] at h
                  | ok p =>
                    obtain ⟨dExtraBits, br₄⟩ := p; simp only [hrb2] at h
                    rw [readBits_append br₃ suffix _ dExtraBits br₄ hrb2]; dsimp only []
                    -- Check distance > output.size
                    by_cases hdist : (Inflate.distBase[distSym.toNat]!).toNat + dExtraBits.toNat > output.size
                    · rw [if_pos hdist] at h; simp at h
                    · rw [if_neg hdist] at h ⊢
                      -- Check output overflow
                      by_cases hoverflow : output.size + ((Inflate.lengthBase[sym.toNat - 257]!).toNat + extraBits.toNat) > maxOut
                      · rw [if_pos hoverflow] at h; simp at h
                      · rw [if_neg hoverflow] at h ⊢
                        -- Recursive call with copied output
                        exact ih br₄ _ h

/-- inflateLoop with appended suffix. -/
private theorem inflateLoop_append_suffix (br : BitReader) (suffix : ByteArray)
    (output : ByteArray) (fixedLit fixedDist : HuffTree) (maxOut fuel : Nat)
    (result : ByteArray) (endPos : Nat)
    (h : Inflate.inflateLoop br output fixedLit fixedDist maxOut fuel =
      .ok (result, endPos)) :
    Inflate.inflateLoop (brAppend br suffix) output fixedLit fixedDist maxOut fuel =
      .ok (result, endPos) := by
  induction fuel generalizing br output with
  | zero => unfold Inflate.inflateLoop at h; simp at h
  | succ n ih =>
    unfold Inflate.inflateLoop at h ⊢; simp only [bind, Except.bind] at h ⊢
    cases hbf : br.readBits 1 with
    | error e => simp [hbf] at h
    | ok p =>
      obtain ⟨bfinal, br₁⟩ := p; simp only [hbf] at h
      rw [readBits_append br suffix 1 bfinal br₁ hbf]; dsimp only []
      cases hbt : br₁.readBits 2 with
      | error e => simp [hbt] at h
      | ok p =>
        obtain ⟨btype, br₂⟩ := p; simp only [hbt] at h
        rw [readBits_append br₁ suffix 2 btype br₂ hbt]; dsimp only []
        -- Case split on btype (0, 1, 2, or reserved)
        -- We split both h and the goal simultaneously
        split at h <;> rename_i hbt_eq <;> (try (rw [show btype = _ from hbt_eq] at *))
        · -- btype = 0: stored block
          cases hds : Inflate.decodeStored br₂ output maxOut with
          | error e => simp [hds] at h
          | ok v =>
            obtain ⟨out', br'⟩ := v; simp only [hds] at h
            rw [decodeStored_append br₂ suffix _ _ out' br' hds]; dsimp only []
            by_cases hbf1 : (bfinal == 1) = true
            · rw [if_pos hbf1] at h ⊢; simp only [pure, Except.pure] at h ⊢
              rw [alignToByte_append]; exact h
            · rw [if_neg hbf1] at h ⊢; exact ih br' out' h
        · -- btype = 1: fixed Huffman
          simp only [Inflate.decodeHuffman] at h ⊢
          cases hdh : Inflate.decodeHuffman.go fixedLit fixedDist maxOut br₂ output 1000000000 with
          | error e => simp [hdh] at h
          | ok v =>
            obtain ⟨out', br'⟩ := v; simp only [hdh] at h
            rw [decodeHuffman_go_append fixedLit fixedDist br₂ suffix _ _ _ out' br' hdh]
            dsimp only []
            by_cases hbf1 : (bfinal == 1) = true
            · rw [if_pos hbf1] at h ⊢; simp only [pure, Except.pure] at h ⊢
              rw [alignToByte_append]; exact h
            · rw [if_neg hbf1] at h ⊢; exact ih br' out' h
        · -- btype = 2: dynamic Huffman
          cases hdt : Inflate.decodeDynamicTrees br₂ with
          | error e => simp [hdt] at h
          | ok v =>
            obtain ⟨litT, distT, br₃⟩ := v; simp only [hdt] at h
            rw [decodeDynamicTrees_append br₂ suffix litT distT br₃ hdt]; dsimp only []
            simp only [Inflate.decodeHuffman] at h ⊢
            cases hdh : Inflate.decodeHuffman.go litT distT maxOut br₃ output 1000000000 with
            | error e => simp [hdh] at h
            | ok v₂ =>
              obtain ⟨out', br'⟩ := v₂; simp only [hdh] at h
              rw [decodeHuffman_go_append litT distT br₃ suffix _ _ _ out' br' hdh]
              dsimp only []
              by_cases hbf1 : (bfinal == 1) = true
              · rw [if_pos hbf1] at h ⊢; simp only [pure, Except.pure] at h ⊢
                rw [alignToByte_append]; exact h
              · rw [if_neg hbf1] at h ⊢; exact ih br' out' h
        · -- btype ≥ 3: reserved
          exact h

/-- inflateRaw with appended suffix: if inflateRaw succeeds on data, it also
    succeeds on data ++ suffix with the same result and endPos. -/
theorem inflateRaw_append_suffix (data suffix : ByteArray) (startPos maxOut : Nat)
    (result : ByteArray) (endPos : Nat)
    (h : Inflate.inflateRaw data startPos maxOut = .ok (result, endPos)) :
    Inflate.inflateRaw (data ++ suffix) startPos maxOut = .ok (result, endPos) := by
  simp only [Inflate.inflateRaw, bind, Except.bind] at h ⊢
  cases hflit : HuffTree.fromLengths Inflate.fixedLitLengths with
  | error e => simp [hflit] at h
  | ok fixedLit =>
    simp only [hflit] at h
    cases hfdist : HuffTree.fromLengths Inflate.fixedDistLengths with
    | error e => simp [hfdist] at h
    | ok fixedDist =>
      simp only [hfdist] at h
      exact inflateLoop_append_suffix ⟨data, startPos, 0⟩ suffix .empty
        fixedLit fixedDist maxOut 10001 result endPos h

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
