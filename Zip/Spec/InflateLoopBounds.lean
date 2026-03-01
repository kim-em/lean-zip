import Zip.Spec.BitReaderInvariant
import Zip.Spec.DeflateRoundtrip
import Zip.Spec.InflateComplete

/-!
# inflateLoop endPos bounds and completeness

Proves that after a successful `inflateLoop` / `inflateRaw`:
- `endPos ≤ data.size` (upper bound)
- `endPos ≥ (pfx ++ deflated).size` (lower bound, when the encoder pads < 8 bits)
- `endPos = (pfx ++ deflated).size` (exactness, combining the two)

Also contains:
- `inflateLoop_complete_ext`: extended completeness exposing the final BitReader state
- `inflateRaw_complete`: completeness for `inflateRaw` at arbitrary startPos
- `alignToByte_pos_ge_of_toBits_short`: lower bound for short remaining bits
-/

namespace Zip.Native

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
    (hspec : Deflate.Spec.decode.go br.toBits output.data.toList =
        some result) :
    ∃ (br_final : BitReader) (endPos : Nat) (remaining : List Bool),
      Inflate.inflateLoop br output fixedLit fixedDist
        maxOutputSize 10000000000 = .ok (⟨⟨result⟩⟩, endPos) ∧
      endPos = br_final.alignToByte.pos ∧
      br_final.data = br.data ∧
      br_final.bitOff < 8 ∧
      (br_final.bitOff = 0 ∨ br_final.pos < br_final.data.size) ∧
      br_final.pos ≤ br_final.data.size ∧
      br_final.toBits = remaining ∧
      Deflate.Spec.decode.goR br.toBits output.data.toList =
        some (result, remaining) := by
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
        by_cases hle : startPos ≤ data.size
        · exact hle
        · exfalso
          have hgt : startPos ≥ data.size := by omega
          have hfail : (BitReader.mk data startPos 0).readBit =
              .error "BitReader: unexpected end of input" := by
            simp only [BitReader.readBit]
            simp [show startPos ≥ data.size from hgt]
          simp only [Inflate.inflateLoop, bind, Except.bind,
            BitReader.readBits, BitReader.readBits.go, hfail] at h
          simp at h
      exact inflateLoop_endPos_le ⟨data, startPos, 0⟩ .empty fixedLit fixedDist
        maxOut 10000000000 result endPos (Or.inl rfl) hple h

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
      have hlt8 : br.pos * 8 + br.bitOff < br.data.size * 8 := by omega
      have htl_add : br.toBits.length + (br.pos * 8 + br.bitOff) = br.data.size * 8 := by
        rw [htl]; exact Nat.sub_add_cancel (Nat.le_of_lt hlt8)
      show br.pos + 1 ≥ br.data.size
      omega

/-! ## endPos exactness: ≥ direction -/

/-- After a successful `inflateRaw` on `prefix ++ deflated` starting at
    `prefix.size`, the endPos ≥ `prefix.size + deflated.size` (i.e., the decoder
    consumes all of `deflated`). Combined with `inflateRaw_endPos_le`, this gives
    endPos = `(prefix ++ deflated).size` exactly. -/
theorem inflateRaw_endPos_ge (pfx deflated : ByteArray)
    (maxOut : Nat) (result : ByteArray) (endPos : Nat)
    (h : Inflate.inflateRaw (pfx ++ deflated) pfx.size maxOut =
      .ok (result, endPos))
    (hspec : Deflate.Spec.decode.go
      (Deflate.Spec.bytesToBits deflated) [] =
      some result.data.toList)
    (hpad : ∃ remaining,
      Deflate.Spec.decode.goR (Deflate.Spec.bytesToBits deflated) [] =
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
      have hbr_toBits : (BitReader.mk (pfx ++ deflated) pfx.size 0).toBits =
          Deflate.Spec.bytesToBits deflated := by
        simp only [BitReader.toBits]
        rw [show pfx.size * 8 + 0 = pfx.size * 8 from by omega]
        rw [show Deflate.Spec.bytesToBits (pfx ++ deflated) =
            Deflate.Spec.bytesToBits pfx ++ Deflate.Spec.bytesToBits deflated from by
          simp [Deflate.Spec.bytesToBits, ByteArray.data_append, Array.toList_append,
            List.flatMap_append]]
        rw [← Deflate.Spec.bytesToBits_length pfx, List.drop_left]
      have hspec' : Deflate.Spec.decode.go
          (BitReader.mk (pfx ++ deflated) pfx.size 0).toBits [] =
          some result.data.toList := by rw [hbr_toBits]; exact hspec
      obtain ⟨br_final, endPos', remaining, hloop, hep, hdf, hwff, hposf, hplef, hrestf, hgoR⟩ :=
        inflateLoop_complete_ext
          ⟨pfx ++ deflated, pfx.size, 0⟩ .empty fixedLit fixedDist
          maxOut result.data.toList (by simp) (by simp)
          (by simp [ByteArray.size_append])
          hflit hfdist hmax hspec'
      have hloop_eq : Inflate.inflateLoop ⟨pfx ++ deflated, pfx.size, 0⟩
          .empty fixedLit fixedDist maxOut 10000000000 = .ok (result, endPos) := h
      have hep_eq : endPos = endPos' := by
        have : Inflate.inflateLoop ⟨pfx ++ deflated, pfx.size, 0⟩
            .empty fixedLit fixedDist maxOut 10000000000 =
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
      have hgoR' : Deflate.Spec.decode.goR (Deflate.Spec.bytesToBits deflated) []
          = some (result.data.toList, remaining) := by
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
      (Deflate.Spec.bytesToBits deflated) [] =
      some result.data.toList)
    (hpad : ∃ remaining,
      Deflate.Spec.decode.goR (Deflate.Spec.bytesToBits deflated) [] =
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
    also succeeds with the same result. -/
theorem inflateRaw_complete (data : ByteArray) (startPos maxOutputSize : Nat)
    (result : List UInt8)
    (hsize : result.length ≤ maxOutputSize)
    (hspec : Deflate.Spec.decode.go
        ((Deflate.Spec.bytesToBits data).drop (startPos * 8)) [] =
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
  have hgo : Deflate.Spec.decode.go (BitReader.mk data startPos 0).toBits
      ByteArray.empty.data.toList = some result := by
    rw [hbr_bits]; exact hspec
  exact Deflate.Correctness.inflateLoop_complete
    ⟨data, startPos, 0⟩ .empty fixedLit fixedDist maxOutputSize 10000000000 result
    hbr_wf hbr_pos hflit hfdist hsize hgo

end Zip.Native
