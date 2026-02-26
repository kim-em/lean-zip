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
                    br₂.toBits 1000000000000000000 = some (syms, bits₃) := by
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
                    hacc_le 1000000000000000000 hds_bridge hspec_lz
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
                        br₃.toBits 1000000000000000000 = some (syms, bits₄) := by
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
                        hacc_le 1000000000000000000 hds_bridge hspec_lz
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
      (Deflate.Spec.bytesToBits deflated) [] 10000000000 =
      some result.data.toList)
    (hpad : ∃ remaining,
      Deflate.Spec.decode.goR (Deflate.Spec.bytesToBits deflated) [] 10000000000 =
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
          (BitReader.mk (pfx ++ deflated) pfx.size 0).toBits [] 10000000000 =
          some result.data.toList := by rw [hbr_toBits]; exact hspec
      obtain ⟨br_final, endPos', remaining, hloop, hep, hdf, hwff, hposf, hplef, hrestf, hgoR⟩ :=
        inflateLoop_complete_ext
          ⟨pfx ++ deflated, pfx.size, 0⟩ .empty fixedLit fixedDist
          maxOut result.data.toList (by simp) (by simp)
          (by simp [ByteArray.size_append])
          hflit hfdist hmax 10000000000 hspec'
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
          10000000000 = some (result.data.toList, remaining) := by
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
      (Deflate.Spec.bytesToBits deflated) [] 10000000000 =
      some result.data.toList)
    (hpad : ∃ remaining,
      Deflate.Spec.decode.goR (Deflate.Spec.bytesToBits deflated) [] 10000000000 =
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
    also succeeds with the same result. The spec fuel must be ≤ 10000000000 (the
    native inflate's block fuel). -/
theorem inflateRaw_complete (data : ByteArray) (startPos maxOutputSize : Nat)
    (result : List UInt8)
    (hsize : result.length ≤ maxOutputSize)
    (specFuel : Nat) (hfuel : specFuel ≤ 10000000000)
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
  have hgo : Deflate.Spec.decode.go (BitReader.mk data startPos 0).toBits
      ByteArray.empty.data.toList 10000000000 = some result := by
    rw [hbr_bits]
    show Deflate.Spec.decode
        ((Deflate.Spec.bytesToBits data).drop (startPos * 8)) 10000000000 = some result
    have h10000000000 : specFuel + (10000000000 - specFuel) = 10000000000 := by omega
    rw [← h10000000000]
    exact Deflate.Spec.decode_fuel_independent _ _ _ hspec _
  exact Deflate.Correctness.inflateLoop_complete
    ⟨data, startPos, 0⟩ .empty fixedLit fixedDist maxOutputSize result
    hbr_wf hbr_pos hflit hfdist hsize 10000000000 hgo

end Zip.Native
