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
  unfold compress
  -- The xfl if-then-else produces three header variants, all of size 10
  split <;> exact ⟨_, _, rfl, rfl, rfl⟩

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
  rw [hflit, hfdist]; simp only []
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

/-! ## Gzip roundtrip -/

/-- If `inflate deflated = .ok data`, then the spec decode succeeds on
    `bytesToBits deflated` with the default fuel (10001). -/
private theorem inflate_to_spec_decode (deflated : ByteArray) (result : ByteArray)
    (h : Inflate.inflate deflated = .ok result) :
    Deflate.Spec.decode (Deflate.Spec.bytesToBits deflated) =
      some result.data.toList := by
  simp only [Inflate.inflate, bind, Except.bind] at h
  cases hinf : Inflate.inflateRaw deflated 0 (256 * 1024 * 1024) with
  | error e => simp [hinf] at h
  | ok p =>
    simp [hinf, pure, Except.pure] at h
    obtain ⟨fuel, hfuel_le, hdec⟩ :=
      Deflate.Correctness.inflate_correct deflated 0 (256 * 1024 * 1024) p.1 p.2
        (by rw [hinf])
    simp at hdec
    have h10001 : fuel + (10001 - fuel) = 10001 := by omega
    rw [← h]
    rw [show (10001 : Nat) = fuel + (10001 - fuel) from h10001.symm]
    exact Deflate.Spec.decode_fuel_independent _ _ _ hdec _

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
      some data.data.toList := by
    have := inflate_to_spec_decode _ data hinfl
    simp only [Deflate.Spec.decode] at this; exact this
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
  have hdata_le : data.data.toList.length ≤ 256 * 1024 * 1024 := by
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
  -- ByteArray identity: ⟨⟨data.data.toList⟩⟩ = data
  have hba_eq : (⟨⟨data.data.toList⟩⟩ : ByteArray) = data := by simp
  -- All three remaining facts require knowing the exact endPos value.
  -- endPos = 10 + (Deflate.deflateRaw data level).size (the trailer start position).
  -- This requires native-level suffix invariance for inflateLoop: inflateRaw on
  -- (header ++ deflated ++ trailer) at header.size stops at header.size + deflated.size.
  -- Not yet proved in the codebase (same blocker as ZlibCorrect.lean's 2 sorry's).
  -- Once `inflateRaw_endPos_eq` is proved, the tight bound follows from compress_size,
  -- and the CRC/size checks follow from readUInt32LE_append3_right + readUInt32LE_bytes.
  have hendPos_tight : endPos + 8 ≤ (GzipEncode.compress data level).size := by sorry
  have hendPos8 : ¬ (endPos + 8 > (GzipEncode.compress data level).size) := by omega
  have hcrc : (Crc32.Native.crc32 0 data ==
    Binary.readUInt32LE (GzipEncode.compress data level) endPos) = true := by sorry
  have hsize_match : (data.size.toUInt32 ==
    Binary.readUInt32LE (GzipEncode.compress data level) (endPos + 4)) = true := by sorry
  -- Assemble the full decompressSingle computation
  -- Extract header byte equalities
  obtain ⟨hb0, hb1, hb2, hb3⟩ := GzipEncode.compress_header_bytes data level
  -- The `unless cond do throw` pattern becomes `if cond then pure () else throw`.
  -- We need to show each guard condition is true.
  have hmagic : ((GzipEncode.compress data level)[0]! == 0x1f &&
    (GzipEncode.compress data level)[1]! == 0x8b) = true := by
    rw [hb0, hb1]; decide
  have hcm : ((GzipEncode.compress data level)[2]! == 8) = true := by
    rw [hb2]; decide
  have hflg : ((GzipEncode.compress data level)[3]! == 0) = true := by
    rw [hb3]; decide
  set_option maxRecDepth 8192 in
  simp only [GzipDecode.decompressSingle, bind, Except.bind,
    hcsz18, ↓reduceIte, pure, Except.pure,
    hmagic, hcm, hflg, hinflRaw, hendPos8, hba_eq, hcrc, hsize_match]

end Zip.Native
