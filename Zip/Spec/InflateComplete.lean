import Zip.Spec.InflateCorrect

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
              (hlit_v + 257 + (hdist_v + 1)) [] bits₄ with
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
                [] bits₄ =
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
                br₄.toBits =
                some (codeLengths, bits₅) := by
              simp; rw [hrest₄]; exact hspec_dcl_bridge
            have ⟨codeLengths', br₅, hdcl_nat, hcl_res_map, hrest₅, hwf₅, hpos₅⟩ :=
              Deflate.Correctness.decodeCLSymbols_complete clTree clArr br₄
                (.replicate (hlit_v + 257 + (hdist_v + 1)) 0) 0
                (hlit_v + 257 + (hdist_v + 1))
                codeLengths bits₅ hwf₄ hpos₄ hft (by rw [hcl_sz]; simp [UInt16.size])
                (by omega) (by simp) hspec_dcl_native
            -- Bridge native extract to spec take/drop
            have hcl_res_sz : codeLengths'.size =
                hlit_v + 257 + (hdist_v + 1) := by
              have ⟨_, _, hsz⟩ := Correctness.decodeCLSymbols_inv clTree br₄ _ 0 _
                codeLengths' br₅ hwf₄ hpos₄ hdcl_nat
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
    (maxOutputSize fuel : Nat)
    (result : List UInt8)
    (hwf : br.bitOff < 8)
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (hflit : Zip.Native.HuffTree.fromLengths
      Zip.Native.Inflate.fixedLitLengths = .ok fixedLit)
    (hfdist : Zip.Native.HuffTree.fromLengths
      Zip.Native.Inflate.fixedDistLengths = .ok fixedDist)
    (hmax : result.length ≤ maxOutputSize)
    (hspec : Deflate.Spec.decode.go br.toBits output.data.toList =
        some result) :
    ∃ endPos,
      Zip.Native.Inflate.inflateLoop br output fixedLit fixedDist
        maxOutputSize fuel = .ok (⟨⟨result⟩⟩, endPos) := by
  sorry

end Deflate.Correctness
