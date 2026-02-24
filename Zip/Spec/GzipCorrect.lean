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
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size) :
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

/-- Combined: decodeStored preserves data, and gives hpos + pos_le. -/
private theorem decodeStored_inv (br br' : BitReader)
    (output output' : ByteArray) (maxOut : Nat)
    (h : Inflate.decodeStored br output maxOut = .ok (output', br')) :
    br'.data = br.data ∧
    (br'.bitOff = 0 ∨ br'.pos < br'.data.size) ∧
    br'.pos ≤ br'.data.size := by
  sorry

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
  sorry

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
  sorry

/-- Combined: decodeDynamicTrees preserves data, hpos, and pos ≤ data.size. -/
private theorem decodeDynamicTrees_inv (br br' : BitReader)
    (litTree distTree : HuffTree)
    (h : Inflate.decodeDynamicTrees br = .ok (litTree, distTree, br'))
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (hple : br.pos ≤ br.data.size) :
    br'.data = br.data ∧
    (br'.bitOff = 0 ∨ br'.pos < br'.data.size) ∧
    br'.pos ≤ br'.data.size := by
  sorry

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
        -- Use sorry for this complex block - will fill in after structure is validated
        sorry

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
        sorry
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

/-- Gzip roundtrip: decompressing the output of compress returns the original data.
    The size bound (5M) is inherited from `inflate_deflateRaw`. -/
theorem gzip_decompressSingle_compress (data : ByteArray) (level : UInt8)
    (hsize : data.size < 5000000) :
    GzipDecode.decompressSingle (GzipEncode.compress data level) = .ok data := by
  sorry

end Zip.Native
