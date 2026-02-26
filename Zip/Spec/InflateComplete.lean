import Zip.Spec.InflateCorrect
import Zip.Spec.DeflateFuelIndep

/-!
# DEFLATE Stream-Level Completeness

Proves completeness: if the formal bitstream specification (`Deflate.Spec.decode`)
succeeds, then the native pure-Lean DEFLATE decompressor also succeeds and
produces the same output.

This is the reverse direction of `InflateCorrect`. The main theorems are
`decodeDynamicTrees_complete` and `inflateLoop_complete`.
-/

namespace Deflate.Correctness

/-! ## Helpers -/

/-- UInt8→Nat→UInt8 roundtrip: `Nat.toUInt8 ∘ UInt8.toNat = id` pointwise. -/
private theorem uint8_nat_roundtrip (l : List UInt8) :
    l.map (Nat.toUInt8 ∘ UInt8.toNat) = l := by
  rw [List.map_congr_left (fun u _ => by
    show Nat.toUInt8 (UInt8.toNat u) = u
    unfold Nat.toUInt8 UInt8.ofNat UInt8.toNat
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq])]
  simp

/-- Nat→UInt8→Nat roundtrip for lists with elements bounded by `maxBits ≤ 15`. -/
theorem validLengths_toUInt8_roundtrip (lens : List Nat)
    (hv : Huffman.Spec.ValidLengths lens maxBits) (hmb : maxBits ≤ 15) :
    (lens.map Nat.toUInt8).toArray.toList.map UInt8.toNat = lens := by
  simp only [List.map_map]
  rw [List.map_congr_left (fun n hn => by
    show (Nat.toUInt8 n).toNat = n
    simp only [Nat.toUInt8, UInt8.toNat, UInt8.ofNat, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by have := hv.1 n hn; omega))]
  simp

/-! ## Dynamic tree decode completeness -/

/-- **Completeness for dynamic tree decode**: if the spec `decodeDynamicTables`
    succeeds on the bit list, the native `decodeDynamicTrees` also succeeds.

    This is the reverse of `decodeDynamicTrees_correct`. -/
theorem decodeDynamicTrees_complete (br : Zip.Native.BitReader)
    (litLens distLens : List Nat) (rest : List Bool)
    (hwf : br.bitOff < 8)
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (hspec : Deflate.Spec.decodeDynamicTables br.toBits =
        some (litLens, distLens, rest)) :
    ∃ litTree distTree br',
      Zip.Native.Inflate.decodeDynamicTrees br = .ok (litTree, distTree, br') ∧
      br'.toBits = rest ∧
      br'.bitOff < 8 ∧
      (br'.bitOff = 0 ∨ br'.pos < br'.data.size) ∧
      Zip.Native.HuffTree.fromLengths (litLens.map Nat.toUInt8).toArray = .ok litTree ∧
      Zip.Native.HuffTree.fromLengths (distLens.map Nat.toUInt8).toArray = .ok distTree ∧
      Huffman.Spec.ValidLengths litLens 15 ∧
      Huffman.Spec.ValidLengths distLens 15 ∧
      litLens.length ≤ UInt16.size ∧
      distLens.length ≤ UInt16.size := by
  -- Unfold the spec do-block
  unfold Deflate.Spec.decodeDynamicTables at hspec
  -- readBitsLSB 5 (hlit)
  cases hspec1 : Deflate.Spec.readBitsLSB 5 br.toBits with
  | none => simp [hspec1] at hspec
  | some p1 =>
    obtain ⟨hlit_v, bits₁⟩ := p1
    simp [hspec1] at hspec
    have hval1 := Deflate.Spec.readBitsLSB_bound hspec1
    have ⟨br₁, hrb1, hrest₁, hwf₁, hpos₁⟩ :=
      readBits_complete br 5 hlit_v bits₁ hwf hpos (by omega) hval1 hspec1
    -- readBitsLSB 5 (hdist)
    cases hspec2 : Deflate.Spec.readBitsLSB 5 bits₁ with
    | none => simp [hspec2] at hspec
    | some p2 =>
      obtain ⟨hdist_v, bits₂⟩ := p2
      simp [hspec2] at hspec
      have hval2 := Deflate.Spec.readBitsLSB_bound hspec2
      have ⟨br₂, hrb2, hrest₂, hwf₂, hpos₂⟩ :=
        readBits_complete br₁ 5 hdist_v bits₂ hwf₁ hpos₁ (by omega) hval2
          (by rw [hrest₁]; exact hspec2)
      -- readBitsLSB 4 (hclen)
      cases hspec3 : Deflate.Spec.readBitsLSB 4 bits₂ with
      | none => simp [hspec3] at hspec
      | some p3 =>
        obtain ⟨hclen_v, bits₃⟩ := p3
        set_option linter.unusedSimpArgs false in
        simp only [hspec3, letFun, bind, Option.bind] at hspec
        have hval3 := Deflate.Spec.readBitsLSB_bound hspec3
        have ⟨br₃, hrb3, hrest₃, hwf₃, hpos₃⟩ :=
          readBits_complete br₂ 4 hclen_v bits₃ hwf₂ hpos₂ (by omega) hval3
            (by rw [hrest₂]; exact hspec3)
        -- readCLLengths
        have hrep19 : (List.replicate 19 0 : List Nat) =
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := rfl
        cases hspec_rcl : Deflate.Spec.readCLLengths (hclen_v + 4) 0
            (List.replicate 19 0) bits₃ with
        | none => rw [hrep19] at hspec_rcl; simp [hspec_rcl] at hspec
        | some p4 =>
          obtain ⟨clLengths, bits₄⟩ := p4
          rw [hrep19] at hspec_rcl
          simp [hspec_rcl] at hspec
          -- Extract ValidLengths clLengths 7 from the guard
          have hcl_valid : Huffman.Spec.ValidLengths clLengths 7 := by
            by_cases h : Huffman.Spec.ValidLengths clLengths 7
            · exact h
            · simp [guard, h] at hspec
          simp [guard, hcl_valid] at hspec
          -- decodeCLSymbols
          cases hspec_dcl : Deflate.Spec.decodeDynamicTables.decodeCLSymbols
              ((Huffman.Spec.allCodes clLengths 7).map fun (sym, cw) => (cw, sym))
              (hlit_v + 257 + (hdist_v + 1)) [] bits₄
              (hlit_v + 257 + (hdist_v + 1) + 1) with
          | none => simp [hspec_dcl] at hspec
          | some p5 =>
            obtain ⟨codeLengths, bits₅⟩ := p5
            simp [hspec_dcl] at hspec
            -- Extract length guard
            have hlen : codeLengths.length = hlit_v + 257 + (hdist_v + 1) := by
              by_cases h : codeLengths.length = hlit_v + 257 + (hdist_v + 1)
              · exact h
              · simp [h] at hspec
            -- Extract lit ValidLengths guard
            have hlit_valid : Huffman.Spec.ValidLengths
                (codeLengths.take (hlit_v + 257)) 15 := by
              by_cases h : Huffman.Spec.ValidLengths (codeLengths.take (hlit_v + 257)) 15
              · exact h
              · simp [hlen, h] at hspec
            -- Extract dist ValidLengths guard
            have hdist_valid : Huffman.Spec.ValidLengths
                (codeLengths.drop (hlit_v + 257)) 15 := by
              by_cases h : Huffman.Spec.ValidLengths (codeLengths.drop (hlit_v + 257)) 15
              · exact h
              · simp [hlen, hlit_valid, h] at hspec
            -- Now reduce hspec fully
            simp [hlen, hlit_valid, hdist_valid] at hspec
            obtain ⟨hlit_eq, hdist_eq, hrest_eq⟩ := hspec
            -- Now build the native side
            -- Native readCLCodeLengths
            have ⟨br₄, clArr, hrcl_nat, hcl_map, hrest₄, hwf₄, hpos₄⟩ :=
              Deflate.Correctness.readCLCodeLengths_complete br₃
                (.replicate 19 0) 0 (hclen_v + 4) clLengths bits₄ hwf₃ hpos₃
                (by simp)
                (by rw [hrest₃]
                    have : List.map UInt8.toNat (Array.replicate 19 (0 : UInt8)).toList =
                        List.replicate 19 0 := by simp [Array.toList_replicate]
                    rw [this]
                    exact hspec_rcl)
            -- Derive clArr.size = 19 and clLengths.length = 19
            have hcl_sz : clArr.size = 19 := by
              have := Correctness.readCLCodeLengths_size br₃ _ 0 _ clArr br₄ hrcl_nat
              simpa using this
            have hcl_len : clLengths.length = 19 := by
              rw [← hcl_map]; simp [Array.length_toList, hcl_sz]
            -- Native fromLengths for CL tree
            have hcl_vl : Huffman.Spec.ValidLengths
                (clArr.toList.map UInt8.toNat) 7 := by
              rw [hcl_map]; exact hcl_valid
            have ⟨clTree, hft⟩ := fromLengths_complete clArr 7 hcl_vl
            -- Bridge hlit_v/hdist_v/hclen_v.toUInt32.toNat = hlit_v/hdist_v/hclen_v
            have hlit_conv : hlit_v.toUInt32.toNat = hlit_v :=
              Nat.mod_eq_of_lt (by omega)
            have hdist_conv : hdist_v.toUInt32.toNat = hdist_v :=
              Nat.mod_eq_of_lt (by omega)
            have hclen_conv : hclen_v.toUInt32.toNat = hclen_v :=
              Nat.mod_eq_of_lt (by omega)
            -- Bridge spec decodeCLSymbols call to native
            have hspec_dcl_bridge : Deflate.Spec.decodeDynamicTables.decodeCLSymbols
                ((Huffman.Spec.allCodes (clArr.toList.map UInt8.toNat) 7).map
                  fun (sym, cw) => (cw, sym))
                (hlit_v + 257 + (hdist_v + 1))
                [] bits₄ (hlit_v + 257 + (hdist_v + 1) + 1) =
                some (codeLengths, bits₅) := by
              rw [hcl_map]; exact hspec_dcl
            -- Convert bits₄ to br₄.toBits
            have hspec_dcl_native :
                Deflate.Spec.decodeDynamicTables.decodeCLSymbols
                ((Huffman.Spec.allCodes (clArr.toList.map UInt8.toNat) 7).map
                  fun (sym, cw) => (cw, sym))
                (hlit_v + 257 + (hdist_v + 1))
                (((Array.replicate (hlit_v + 257 + (hdist_v + 1)) (0 : UInt8)).extract 0 0).toList.map
                  UInt8.toNat)
                br₄.toBits (hlit_v + 257 + (hdist_v + 1) + 1) =
                some (codeLengths, bits₅) := by
              simp; rw [hrest₄]; exact hspec_dcl_bridge
            have ⟨codeLengths', br₅, hdcl_nat, hcl_res_map, hrest₅, hwf₅, hpos₅⟩ :=
              Deflate.Correctness.decodeCLSymbols_complete clTree clArr br₄
                (.replicate (hlit_v + 257 + (hdist_v + 1)) 0) 0
                (hlit_v + 257 + (hdist_v + 1))
                (hlit_v + 257 + (hdist_v + 1) + 1)
                codeLengths bits₅ hwf₄ hpos₄ hft (by rw [hcl_sz]; simp [UInt16.size])
                (by omega) (by simp) hspec_dcl_native
            -- Bridge native extract to spec take/drop
            have hcl_res_sz : codeLengths'.size =
                hlit_v + 257 + (hdist_v + 1) := by
              have ⟨_, _, hsz⟩ := Correctness.decodeCLSymbols_inv clTree br₄ _ 0 _
                _ codeLengths' br₅ hwf₄ hpos₄ hdcl_nat
              simpa using hsz
            have hlit_bridge :
                (codeLengths'.extract 0 (hlit_v + 257)).toList.map UInt8.toNat = litLens := by
              rw [← hlit_eq, ← hcl_res_map]
              simp only [Array.toList_extract, List.extract, Nat.sub_zero,
                List.drop_zero, List.map_take, List.take_take,
                Nat.min_eq_left (by omega : hlit_v + 257 ≤
                  hlit_v + 257 + (hdist_v + 1))]
            have hdist_bridge :
                (codeLengths'.extract (hlit_v + 257)
                  (hlit_v + 257 + (hdist_v + 1))).toList.map UInt8.toNat = distLens := by
              rw [← hdist_eq, ← hcl_res_map]
              simp only [Array.toList_extract, List.extract,
                Nat.sub_zero, List.drop_zero]
              rw [← List.map_drop, List.drop_take]
            -- ValidLengths for lit/dist through bridge
            have hlit_vl : Huffman.Spec.ValidLengths
                ((codeLengths'.extract 0 (hlit_v + 257)).toList.map UInt8.toNat) 15 := by
              rw [hlit_bridge, ← hlit_eq]; exact hlit_valid
            have hdist_vl : Huffman.Spec.ValidLengths
                ((codeLengths'.extract (hlit_v + 257)
                  (hlit_v + 257 + (hdist_v + 1))).toList.map UInt8.toNat) 15 := by
              rw [hdist_bridge, ← hdist_eq]; exact hdist_valid
            -- fromLengths_complete for lit and dist
            have ⟨litTree, hflit⟩ := fromLengths_complete
              (codeLengths'.extract 0 (hlit_v + 257)) 15 hlit_vl
            have ⟨distTree, hfdist⟩ := fromLengths_complete
              (codeLengths'.extract (hlit_v + 257)
                (hlit_v + 257 + (hdist_v + 1))) 15 hdist_vl
            -- Bridge rest: br₅.toBits = rest
            have hrest_final : br₅.toBits = rest := by rw [hrest₅, hrest_eq]
            -- litLens/distLens back to native arrays
            have hlit_arr : (litLens.map Nat.toUInt8).toArray =
                codeLengths'.extract 0 (hlit_v + 257) := by
              rw [← hlit_bridge, List.map_map, uint8_nat_roundtrip, Array.toArray_toList]
            have hdist_arr : (distLens.map Nat.toUInt8).toArray =
                codeLengths'.extract (hlit_v + 257)
                  (hlit_v + 257 + (hdist_v + 1)) := by
              rw [← hdist_bridge, List.map_map, uint8_nat_roundtrip, Array.toArray_toList]
            -- Assemble the native decodeDynamicTrees
            refine ⟨litTree, distTree, br₅, ?_, hrest_final, hwf₅, hpos₅,
              ?_, ?_, ?_, ?_, ?_, ?_⟩
            · -- decodeDynamicTrees br = .ok (litTree, distTree, br₅)
              simp only [Zip.Native.Inflate.decodeDynamicTrees, bind, Except.bind,
                hrb1, hrb2, hrb3, hlit_conv, hdist_conv, hclen_conv,
                hrcl_nat, hft, hdcl_nat, hflit, hfdist, pure, Except.pure]
            · -- fromLengths (litLens.map Nat.toUInt8).toArray = .ok litTree
              rw [hlit_arr]; exact hflit
            · -- fromLengths (distLens.map Nat.toUInt8).toArray = .ok distTree
              rw [hdist_arr]; exact hfdist
            · -- ValidLengths litLens 15
              rw [← hlit_eq]; exact hlit_valid
            · -- ValidLengths distLens 15
              rw [← hdist_eq]; exact hdist_valid
            · -- litLens.length ≤ UInt16.size
              rw [← hlit_eq]
              simp [List.length_take, hlen, UInt16.size]
              omega
            · -- distLens.length ≤ UInt16.size
              rw [← hdist_eq]
              simp [List.length_drop, hlen, UInt16.size]
              omega

/-! ## Block loop completeness -/

set_option maxRecDepth 2048 in
/-- **Completeness for block loop**: if the spec `decode.go` succeeds,
    the native `inflateLoop` also succeeds with the same result.

    This is the reverse of `inflateLoop_correct`. -/
theorem inflateLoop_complete (br : Zip.Native.BitReader)
    (output : ByteArray)
    (fixedLit fixedDist : Zip.Native.HuffTree)
    (maxOutputSize : Nat)
    (result : List UInt8)
    (hwf : br.bitOff < 8)
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (hflit : Zip.Native.HuffTree.fromLengths
      Zip.Native.Inflate.fixedLitLengths = .ok fixedLit)
    (hfdist : Zip.Native.HuffTree.fromLengths
      Zip.Native.Inflate.fixedDistLengths = .ok fixedDist)
    (hmax : result.length ≤ maxOutputSize)
    (specFuel : Nat)
    (hspec : Deflate.Spec.decode.go br.toBits output.data.toList specFuel =
        some result) :
    ∃ endPos,
      Zip.Native.Inflate.inflateLoop br output fixedLit fixedDist
        maxOutputSize specFuel = .ok (⟨⟨result⟩⟩, endPos) := by
  induction specFuel generalizing br output with
  | zero => simp [Deflate.Spec.decode.go] at hspec
  | succ n ih =>
    -- Unfold spec decode.go to extract readBitsLSB calls
    unfold Deflate.Spec.decode.go at hspec
    -- readBitsLSB 1 (bfinal)
    cases hspec_bf : Deflate.Spec.readBitsLSB 1 br.toBits with
    | none => simp [hspec_bf] at hspec
    | some p =>
      obtain ⟨bfinal_val, bits₁⟩ := p
      simp only [hspec_bf, bind, Option.bind] at hspec
      have hbf_bound := Deflate.Spec.readBitsLSB_bound hspec_bf
      -- readBitsLSB 2 (btype)
      cases hspec_bt : Deflate.Spec.readBitsLSB 2 bits₁ with
      | none => simp [hspec_bt] at hspec
      | some q =>
        obtain ⟨btype_val, bits₂⟩ := q
        simp only [hspec_bt] at hspec
        have hbt_bound := Deflate.Spec.readBitsLSB_bound hspec_bt
        -- Get native readBits via completeness
        have ⟨br₁, hrb1, hrest₁, hwf₁, hpos₁⟩ :=
          readBits_complete br 1 bfinal_val bits₁ hwf hpos (by omega) hbf_bound hspec_bf
        have ⟨br₂, hrb2, hrest₂, hwf₂, hpos₂⟩ :=
          readBits_complete br₁ 2 btype_val bits₂ hwf₁ hpos₁ (by omega) hbt_bound
            (by rw [hrest₁]; exact hspec_bt)
        -- Case split on btype_val (0, 1, 2, or ≥3)
        by_cases hbt0 : btype_val = 0
        · -- btype_val = 0: stored block
          subst hbt0
          cases hspec_st : Deflate.Spec.decodeStored bits₂ with
          | none => simp [hspec_st] at hspec
          | some r =>
            obtain ⟨storedBytes, bits₃⟩ := r
            simp only [hspec_st] at hspec
            -- Get output size bound
            have hlen' : output.size + storedBytes.length ≤ maxOutputSize := by
              by_cases hbf1 : (bfinal_val == 1) = true
              · rw [if_pos hbf1] at hspec
                simp only [pure, Pure.pure] at hspec
                have heq := Option.some.inj hspec
                have hlen := congrArg List.length heq
                simp only [List.length_append] at hlen
                have : output.data.toList.length = output.size :=
                  Array.length_toList
                omega
              · rw [if_neg hbf1] at hspec
                have hpfx := List.IsPrefix.length_le
                  (Deflate.Spec.decode_go_acc_prefix _ _ _ _ hspec)
                have : output.data.toList.length = output.size :=
                  Array.length_toList
                simp only [List.length_append] at hpfx; omega
            have ⟨br', hst_nat, hrest₃, hoff₃, hpos₃⟩ :=
              decodeStored_complete br₂ output maxOutputSize storedBytes bits₃
                hwf₂ hpos₂ hlen'
                (by rw [hrest₂]; exact hspec_st)
            -- The native inflateLoop with btype=0 dispatches to decodeStored
            have hil : Zip.Native.Inflate.inflateLoop br output fixedLit fixedDist
                maxOutputSize (n + 1) =
              (if (bfinal_val.toUInt32 == 1) = true
                then .ok (output ++ ⟨⟨storedBytes⟩⟩, br'.alignToByte.pos)
                else Zip.Native.Inflate.inflateLoop br' (output ++ ⟨⟨storedBytes⟩⟩)
                  fixedLit fixedDist maxOutputSize n) := by
              simp only [Zip.Native.Inflate.inflateLoop, bind, Except.bind,
                hrb1, hrb2, hst_nat]; rfl
            split at hspec
            · -- bfinal == 1: final block
              rename_i hbf1
              simp only [pure, Pure.pure] at hspec
              have heq := Option.some.inj hspec
              have hba_eq : output ++ ⟨⟨storedBytes⟩⟩ = ⟨⟨result⟩⟩ := by
                apply ByteArray.ext
                simp [ByteArray.data_append, heq]
              rw [hil, if_pos (Correctness.nat_beq_to_uint32_true _ (by omega) hbf1), hba_eq]
              exact ⟨_, rfl⟩
            · -- bfinal ≠ 1: continue
              rename_i hbf1
              have hspec' : Deflate.Spec.decode.go br'.toBits
                  (output ++ ⟨⟨storedBytes⟩⟩).data.toList n = some result := by
                have : (output ++ ⟨⟨storedBytes⟩⟩).data.toList =
                    output.data.toList ++ storedBytes := by
                  simp [ByteArray.data_append, Array.toList_append]
                rw [this, hrest₃]; exact hspec
              obtain ⟨endPos, hloop⟩ := ih br' (output ++ ⟨⟨storedBytes⟩⟩)
                (by rw [hoff₃]; omega) (Or.inl hoff₃) hspec'
              have hbf_neg := Correctness.nat_beq_to_uint32_false _ (by omega) hbf1
              rw [hil, if_neg hbf_neg]
              exact ⟨endPos, hloop⟩
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
                -- Bridge spec decodeSymbols to native form
                have hds_bridge : Deflate.Spec.decodeSymbols
                    (Zip.Native.Inflate.fixedLitLengths.toList.map UInt8.toNat)
                    (Zip.Native.Inflate.fixedDistLengths.toList.map UInt8.toNat)
                    br₂.toBits 1000000000000000000 = some (syms, bits₃) := by
                  rw [hrest₂, Correctness.fixedLitLengths_eq, Correctness.fixedDistLengths_eq]; exact hspec_ds
                have ⟨br', hhf_nat, hrest₃, hwf₃, hpos₃⟩ :=
                  decodeHuffman_complete
                    Zip.Native.Inflate.fixedLitLengths
                    Zip.Native.Inflate.fixedDistLengths
                    fixedLit fixedDist maxOutputSize br₂ output
                    syms bits₃ acc'
                    hwf₂ hpos₂ hflit hfdist
                    (Correctness.fixedLitLengths_eq ▸ Deflate.Spec.fixedLitLengths_valid)
                    (Correctness.fixedDistLengths_eq ▸ Deflate.Spec.fixedDistLengths_valid)
                    Correctness.fixedLitLengths_size Correctness.fixedDistLengths_size
                    hacc_le 1000000000000000000 hds_bridge hspec_lz
                -- Wrap decodeHuffman.go into decodeHuffman
                have hdh : Zip.Native.Inflate.decodeHuffman br₂ output fixedLit fixedDist
                    maxOutputSize = .ok (⟨⟨acc'⟩⟩, br') := by
                  simp only [Zip.Native.Inflate.decodeHuffman]; exact hhf_nat
                -- Reduce inflateLoop to the if-bfinal branch
                have hil : Zip.Native.Inflate.inflateLoop br output fixedLit fixedDist
                    maxOutputSize (n + 1) =
                  (if (bfinal_val.toUInt32 == 1) = true
                    then .ok (⟨⟨acc'⟩⟩, br'.alignToByte.pos)
                    else Zip.Native.Inflate.inflateLoop br' ⟨⟨acc'⟩⟩
                      fixedLit fixedDist maxOutputSize n) := by
                  simp only [Zip.Native.Inflate.inflateLoop, bind, Except.bind,
                    hrb1, hrb2, hdh]; rfl
                split at hspec
                · -- bfinal == 1: final block
                  rename_i hbf1
                  simp [pure, Pure.pure] at hspec; subst hspec
                  exact ⟨_, by rw [hil, if_pos (Correctness.nat_beq_to_uint32_true _ (by omega) hbf1)]⟩
                · -- bfinal ≠ 1: continue
                  rename_i hbf1
                  have hspec' : Deflate.Spec.decode.go br'.toBits acc' n =
                      some result := by
                    rw [hrest₃]; exact hspec
                  obtain ⟨endPos, hloop⟩ := ih br' ⟨⟨acc'⟩⟩ hwf₃ hpos₃ hspec'
                  rw [hil, if_neg (Correctness.nat_beq_to_uint32_false _ (by omega) hbf1)]
                  exact ⟨endPos, hloop⟩
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
                    -- decodeDynamicTrees_complete
                    have ⟨litTree, distTree, br₃, hdt_nat, hrest_dt, hwf₃, hpos₃,
                      hflit_dyn, hfdist_dyn, hvlit_dyn, hvdist_dyn, hsize_lit,
                      hsize_dist⟩ :=
                      decodeDynamicTrees_complete br₂ litLens distLens bits₃
                        hwf₂ hpos₂ (by rw [hrest₂]; exact hspec_dt)
                    -- Bridge litLens/distLens through UInt8 roundtrip
                    have hlit_rt := validLengths_toUInt8_roundtrip litLens hvlit_dyn (by omega)
                    have hdist_rt := validLengths_toUInt8_roundtrip distLens hvdist_dyn (by omega)
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
                    have hsize_lit' : (litLens.map Nat.toUInt8).toArray.size ≤ UInt16.size := by
                      simp; exact hsize_lit
                    have hsize_dist' : (distLens.map Nat.toUInt8).toArray.size ≤ UInt16.size := by
                      simp; exact hsize_dist
                    have ⟨br', hhf_nat, hrest₄, hwf₄, hpos₄⟩ :=
                      decodeHuffman_complete
                        (litLens.map Nat.toUInt8).toArray
                        (distLens.map Nat.toUInt8).toArray
                        litTree distTree maxOutputSize br₃ output
                        syms bits₄ acc'
                        hwf₃ hpos₃ hflit_dyn hfdist_dyn
                        hvlit_bridge hvdist_bridge
                        hsize_lit' hsize_dist'
                        hacc_le 1000000000000000000 hds_bridge hspec_lz
                    -- Wrap into decodeHuffman
                    have hdh : Zip.Native.Inflate.decodeHuffman br₃ output litTree distTree
                        maxOutputSize = .ok (⟨⟨acc'⟩⟩, br') := by
                      simp only [Zip.Native.Inflate.decodeHuffman]; exact hhf_nat
                    -- Reduce inflateLoop with btype=2
                    have hil : Zip.Native.Inflate.inflateLoop br output fixedLit fixedDist
                        maxOutputSize (n + 1) =
                      (if (bfinal_val.toUInt32 == 1) = true
                        then .ok (⟨⟨acc'⟩⟩, br'.alignToByte.pos)
                        else Zip.Native.Inflate.inflateLoop br' ⟨⟨acc'⟩⟩
                          fixedLit fixedDist maxOutputSize n) := by
                      simp only [Zip.Native.Inflate.inflateLoop, bind, Except.bind,
                        hrb1, hrb2, hdt_nat, hdh]; rfl
                    split at hspec
                    · -- bfinal == 1: final block
                      rename_i hbf1
                      simp [pure, Pure.pure] at hspec; subst hspec
                      exact ⟨_, by rw [hil, if_pos (Correctness.nat_beq_to_uint32_true _ (by omega) hbf1)]⟩
                    · -- bfinal ≠ 1: continue
                      rename_i hbf1
                      have hspec' : Deflate.Spec.decode.go br'.toBits acc' n =
                          some result := by
                        rw [hrest₄]; exact hspec
                      obtain ⟨endPos, hloop⟩ := ih br' ⟨⟨acc'⟩⟩ hwf₄ hpos₄ hspec'
                      rw [hil, if_neg (Correctness.nat_beq_to_uint32_false _ (by omega) hbf1)]
                      exact ⟨endPos, hloop⟩
            · -- btype_val ≥ 3: reserved (spec returns none)
              have hbt3 : btype_val = 3 := by omega
              subst hbt3; simp at hspec

end Deflate.Correctness
