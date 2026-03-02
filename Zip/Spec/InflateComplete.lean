import Zip.Spec.InflateCorrect

/-!
# DEFLATE Stream-Level Completeness

Proves completeness: if the formal bitstream specification (`Deflate.Spec.decode`)
succeeds, then the native pure-Lean DEFLATE decompressor also succeeds and
produces the same output.

This is the reverse direction of `InflateCorrect`. The main theorem is
`inflateLoop_complete`.
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

/-! ## Fuel monotonicity -/

/-- Fuel monotonicity: if `inflateLoop` succeeds with fuel `n`, it succeeds
    with any `m ≥ n` and produces the same result. -/
theorem inflateLoop_fuel_le
    (br : Zip.Native.BitReader) (output : ByteArray)
    (fixedLit fixedDist : Zip.Native.HuffTree) (maxOut n m : Nat)
    (x : ByteArray × Nat)
    (h : Zip.Native.Inflate.inflateLoop br output fixedLit fixedDist maxOut n = .ok x)
    (hle : n ≤ m) :
    Zip.Native.Inflate.inflateLoop br output fixedLit fixedDist maxOut m = .ok x := by
  induction n generalizing br output m with
  | zero => simp [Zip.Native.Inflate.inflateLoop] at h
  | succ n ih =>
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp only [Zip.Native.Inflate.inflateLoop, bind, Except.bind] at h ⊢
    -- readBits 1
    cases hbf : br.readBits 1 with
    | error e => simp [hbf] at h
    | ok p₁ =>
      obtain ⟨bfinal, br₁⟩ := p₁; simp only [hbf] at h ⊢
      -- readBits 2
      cases hbt : br₁.readBits 2 with
      | error e => simp [hbt] at h
      | ok p₂ =>
        obtain ⟨btype, br₂⟩ := p₂; simp only [hbt] at h ⊢
        -- Both h and ⊢ match on btype; only fuel differs (n vs m')
        -- split at h resolves the shared discriminant in both h and ⊢
        split at h
        · -- btype = 0: stored
          split at h
          · exact h -- error case
          · -- ok case: bfinal check
            split at h <;> split
            · exact h
            · rename_i h1 h2; exact absurd h1 h2
            · rename_i h1 h2; exact absurd h2 h1
            · exact ih _ _ _ h (by omega)
        · -- btype = 1: fixed Huffman
          split at h
          · exact h
          · split at h <;> split
            · exact h
            · rename_i h1 h2; exact absurd h1 h2
            · rename_i h1 h2; exact absurd h2 h1
            · exact ih _ _ _ h (by omega)
        · -- btype = 2: dynamic Huffman
          split at h
          · exact h -- decodeDynamicTrees error
          · split at h
            · exact h -- decodeHuffman error
            · split at h <;> split
              · exact h
              · rename_i h1 h2; exact absurd h1 h2
              · rename_i h1 h2; exact absurd h2 h1
              · exact ih _ _ _ h (by omega)
        · exact h -- btype ≥ 3: reserved error

/-! ## Block loop completeness -/

set_option maxRecDepth 2048 in
/-- **Completeness for block loop**: if the spec `decode.go` succeeds,
    the native `inflateLoop` also succeeds with the same result.

    Note: `fuel` is existentially quantified because `inflateLoop 0` always
    errors. The fuel bound allows transferring to any concrete fuel value
    via `inflateLoop_fuel_le`.

    This is the reverse of `inflateLoop_correct`. -/
theorem inflateLoop_complete (br : Zip.Native.BitReader)
    (output : ByteArray)
    (fixedLit fixedDist : Zip.Native.HuffTree)
    (maxOutputSize : Nat)
    (result : List UInt8)
    (hwf : br.bitOff < 8)
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (hple : br.pos ≤ br.data.size)
    (hflit : Zip.Native.HuffTree.fromLengths
      Zip.Native.Inflate.fixedLitLengths = .ok fixedLit)
    (hfdist : Zip.Native.HuffTree.fromLengths
      Zip.Native.Inflate.fixedDistLengths = .ok fixedDist)
    (hmax : result.length ≤ maxOutputSize)
    (hspec : Deflate.Spec.decode.go br.toBits output.data.toList =
        some result) :
    ∃ fuel endPos,
      fuel ≤ br.toBits.length + 1 ∧
      Zip.Native.Inflate.inflateLoop br output fixedLit fixedDist
        maxOutputSize fuel = .ok (⟨⟨result⟩⟩, endPos) := by
  -- Strong induction on bit stream length
  suffices ∀ len (br : Zip.Native.BitReader) (output : ByteArray)
      (result : List UInt8),
      br.toBits.length = len →
      br.bitOff < 8 →
      (br.bitOff = 0 ∨ br.pos < br.data.size) →
      br.pos ≤ br.data.size →
      result.length ≤ maxOutputSize →
      Deflate.Spec.decode.go br.toBits output.data.toList = some result →
      ∃ fuel endPos,
        fuel ≤ len + 1 ∧
        Zip.Native.Inflate.inflateLoop br output fixedLit fixedDist
          maxOutputSize fuel = .ok (⟨⟨result⟩⟩, endPos) from
    this _ br output result rfl hwf hpos hple hmax hspec
  intro len
  induction len using Nat.strongRecOn with
  | _ len ih =>
    intro br output result hlen hwf hpos hple hmaxout hspec
    -- Unfold spec one step
    unfold Deflate.Spec.decode.go at hspec
    -- Extract readBitsLSB 1 (bfinal)
    cases hspec_bf : Deflate.Spec.readBitsLSB 1 br.toBits with
    | none => simp [hspec_bf] at hspec
    | some p₁ =>
      obtain ⟨bfinal_val, bits₁⟩ := p₁
      simp only [hspec_bf, bind, Option.bind] at hspec
      have hval_bf := Deflate.Spec.readBitsLSB_bound hspec_bf
      have ⟨br₁, hrb_bf, hrest₁, hwf₁, hpos₁⟩ :=
        readBits_complete br 1 bfinal_val bits₁ hwf hpos (by omega) hval_bf hspec_bf
      have ⟨_, _, hple₁⟩ :=
        Zip.Native.readBits_inv br br₁ 1 bfinal_val.toUInt32 hrb_bf hpos hple
      -- Extract readBitsLSB 2 (btype)
      cases hspec_bt : Deflate.Spec.readBitsLSB 2 bits₁ with
      | none => simp [hspec_bt] at hspec
      | some p₂ =>
        obtain ⟨btype_val, bits₂⟩ := p₂
        simp only [hspec_bt] at hspec
        have hval_bt := Deflate.Spec.readBitsLSB_bound hspec_bt
        have ⟨br₂, hrb_bt, hrest₂, hwf₂, hpos₂⟩ :=
          readBits_complete br₁ 2 btype_val bits₂ hwf₁ hpos₁ (by omega) hval_bt
            (by rw [hrest₁]; exact hspec_bt)
        have ⟨_, _, hple₂⟩ :=
          Zip.Native.readBits_inv br₁ br₂ 2 btype_val.toUInt32 hrb_bt hpos₁ hple₁
        -- Dispatch on btype_val in spec
        split at hspec
        · -- btype_val = 0: stored
          -- Extract decodeStored from spec
          cases hspec_ds : Deflate.Spec.decodeStored bits₂ with
          | none => simp [hspec_ds] at hspec
          | some p₃ =>
            obtain ⟨storedBytes, rest⟩ := p₃
            simp only [hspec_ds] at hspec
            -- Use decodeStored_complete for native
            have hspec_ds' : Deflate.Spec.decodeStored br₂.toBits =
                some (storedBytes, rest) := by rw [hrest₂]; exact hspec_ds
            -- Split on bfinal
            split at hspec
            · -- bfinal_val == 1: final block
              rename_i hbf1
              simp only [pure] at hspec
              have hresult : result = output.data.toList ++ storedBytes := by
                cases hspec; rfl
              have hmax_s : output.size + storedBytes.length ≤ maxOutputSize := by
                rw [hresult, List.length_append] at hmaxout
                simp only [ByteArray.size, Array.length_toList] at *; omega
              obtain ⟨br', hds_nat, _, _, _⟩ := decodeStored_complete br₂ output
                maxOutputSize storedBytes rest hwf₂ hpos₂ hmax_s hspec_ds'
              refine ⟨1, br'.alignToByte.pos, by omega, ?_⟩
              simp only [Zip.Native.Inflate.inflateLoop, bind, Except.bind,
                hrb_bf, hrb_bt, hds_nat,
                show Nat.toUInt32 0 = (0 : UInt32) from rfl]
              -- bfinal check
              have hbf_u32 : (bfinal_val.toUInt32 == 1) = true := by
                rw [beq_iff_eq] at hbf1 ⊢; subst hbf1; rfl
              simp only [hbf_u32, ↓reduceIte, pure, Except.pure]
              -- Goal: .ok (output ++ ⟨⟨storedBytes⟩⟩, br'.alignToByte.pos) =
              --       .ok (⟨⟨result⟩⟩, br'.alignToByte.pos)
              rw [hresult]; rfl
            · -- bfinal_val ≠ 1: recursive case
              rename_i hbf_ne1
              -- Split the dite guard (rest.length < br.toBits.length)
              split at hspec
              · rename_i hrest_lt
                -- hspec : decode.go rest (output.data.toList ++ storedBytes) = some result
                -- Derive hmax_s for decodeStored_complete
                have hpre := Deflate.Spec.decode_go_acc_prefix _ _ _ hspec
                have hmax_s : output.size + storedBytes.length ≤ maxOutputSize := by
                  have := hpre.length_le
                  simp only [List.length_append, ByteArray.size, Array.length_toList] at this ⊢
                  omega
                -- Get native decodeStored result
                obtain ⟨br', hds_nat, hrest_br, hbo_0, hpos_br⟩ :=
                  decodeStored_complete br₂ output maxOutputSize storedBytes rest
                    hwf₂ hpos₂ hmax_s hspec_ds'
                have ⟨_, _, hple_br⟩ :=
                  Zip.Native.decodeStored_inv br₂ br' output _ maxOutputSize hds_nat
                -- Apply IH (rest.length < len)
                have hrest_lt' : rest.length < len := by rw [← hlen]; exact hrest_lt
                have hspec_br : Deflate.Spec.decode.go br'.toBits
                    (output ++ ⟨⟨storedBytes⟩⟩).data.toList = some result := by
                  rw [hrest_br]; exact hspec
                obtain ⟨fuel', endPos, hfuel_le, hloop⟩ :=
                  ih rest.length hrest_lt' br' (output ++ ⟨⟨storedBytes⟩⟩) result
                    (by rw [hrest_br])
                    (by rw [hbo_0]; omega) hpos_br hple_br hmaxout hspec_br
                -- Construct fuel = fuel' + 1
                refine ⟨fuel' + 1, endPos, by omega, ?_⟩
                simp only [Zip.Native.Inflate.inflateLoop, bind, Except.bind,
                  hrb_bf, hrb_bt, hds_nat,
                  show Nat.toUInt32 0 = (0 : UInt32) from rfl]
                have hbf_u32 : (bfinal_val.toUInt32 == 1) = false := by
                  have : bfinal_val = 0 := by simp only [beq_iff_eq] at hbf_ne1; omega
                  subst this; rfl
                simp only [hbf_u32, Bool.false_eq_true, ↓reduceIte]
                exact hloop
              · -- ¬(rest.length < br.toBits.length): spec returns none
                simp at hspec

        · -- btype_val = 1: fixed Huffman
          -- Extract decodeSymbols from spec
          cases hspec_ds : Deflate.Spec.decodeSymbols Deflate.Spec.fixedLitLengths
              Deflate.Spec.fixedDistLengths bits₂ with
          | none => simp [hspec_ds] at hspec
          | some p₃ =>
            obtain ⟨syms, rest⟩ := p₃
            simp only [hspec_ds] at hspec
            -- Extract resolveLZ77 from spec
            cases hspec_lz : Deflate.Spec.resolveLZ77 syms output.data.toList with
            | none => simp [hspec_lz] at hspec
            | some blockResult =>
              simp only [hspec_lz] at hspec
              -- Bridge decodeSymbols to native table names
              have hds_bridge : Deflate.Spec.decodeSymbols
                  (Zip.Native.Inflate.fixedLitLengths.toList.map UInt8.toNat)
                  (Zip.Native.Inflate.fixedDistLengths.toList.map UInt8.toNat)
                  br₂.toBits = some (syms, rest) := by
                rw [Deflate.Correctness.fixedLitLengths_eq,
                    Deflate.Correctness.fixedDistLengths_eq, hrest₂]
                exact hspec_ds
              -- Split on bfinal
              split at hspec
              · -- bfinal_val == 1: final block
                rename_i hbf1
                cases hspec -- substitutes blockResult := result
                obtain ⟨br', hdh, hrest_br, hwf_br, hpos_br⟩ :=
                  decodeHuffman_complete
                    Zip.Native.Inflate.fixedLitLengths Zip.Native.Inflate.fixedDistLengths
                    fixedLit fixedDist maxOutputSize br₂ output syms rest result
                    hwf₂ hpos₂ hflit hfdist
                    (by rw [Deflate.Correctness.fixedLitLengths_eq]
                        exact Deflate.Spec.fixedLitLengths_valid)
                    (by rw [Deflate.Correctness.fixedDistLengths_eq]
                        exact Deflate.Spec.fixedDistLengths_valid)
                    Deflate.Correctness.fixedLitLengths_size
                    Deflate.Correctness.fixedDistLengths_size
                    hmaxout br₂.data.size hple₂ (by omega)
                    hds_bridge hspec_lz
                have hdh_native : Zip.Native.Inflate.decodeHuffman br₂ output
                    fixedLit fixedDist maxOutputSize =
                    .ok (⟨⟨result⟩⟩, br') := by
                  unfold Zip.Native.Inflate.decodeHuffman; exact hdh
                refine ⟨1, br'.alignToByte.pos, by omega, ?_⟩
                simp only [Zip.Native.Inflate.inflateLoop, bind, Except.bind,
                  hrb_bf, hrb_bt, hdh_native,
                  show Nat.toUInt32 1 = (1 : UInt32) from rfl]
                have hbf_u32 : (bfinal_val.toUInt32 == 1) = true := by
                  rw [beq_iff_eq] at hbf1 ⊢; subst hbf1; rfl
                simp only [hbf_u32, ↓reduceIte, pure, Except.pure]
              · -- bfinal_val ≠ 1: recursive case
                rename_i hbf_ne1
                split at hspec
                · rename_i hrest_lt
                  -- Derive hmax for decodeHuffman_complete
                  have hmax_block : blockResult.length ≤ maxOutputSize := by
                    have := (Deflate.Spec.decode_go_acc_prefix _ _ _ hspec).length_le; omega
                  obtain ⟨br', hdh, hrest_br, hwf_br, hpos_br⟩ :=
                    decodeHuffman_complete
                      Zip.Native.Inflate.fixedLitLengths Zip.Native.Inflate.fixedDistLengths
                      fixedLit fixedDist maxOutputSize br₂ output syms rest blockResult
                      hwf₂ hpos₂ hflit hfdist
                      (by rw [Deflate.Correctness.fixedLitLengths_eq]
                          exact Deflate.Spec.fixedLitLengths_valid)
                      (by rw [Deflate.Correctness.fixedDistLengths_eq]
                          exact Deflate.Spec.fixedDistLengths_valid)
                      Deflate.Correctness.fixedLitLengths_size
                      Deflate.Correctness.fixedDistLengths_size
                      hmax_block br₂.data.size hple₂ (by omega)
                      hds_bridge hspec_lz
                  have hdh_native : Zip.Native.Inflate.decodeHuffman br₂ output
                      fixedLit fixedDist maxOutputSize =
                      .ok (⟨⟨blockResult⟩⟩, br') := by
                    unfold Zip.Native.Inflate.decodeHuffman; exact hdh
                  have ⟨_, _, hple_br⟩ :=
                    Zip.Native.decodeHuffman_inv fixedLit fixedDist br₂ br' output
                      ⟨⟨blockResult⟩⟩ maxOutputSize hdh_native hpos₂ hple₂
                  -- Apply IH
                  have hrest_lt' : rest.length < len := by rw [← hlen]; exact hrest_lt
                  have hspec_br : Deflate.Spec.decode.go br'.toBits
                      (⟨⟨blockResult⟩⟩ : ByteArray).data.toList = some result := by
                    rw [hrest_br]; exact hspec
                  obtain ⟨fuel', endPos, hfuel_le, hloop⟩ :=
                    ih rest.length hrest_lt' br' ⟨⟨blockResult⟩⟩ result
                      (by rw [hrest_br]) hwf_br hpos_br hple_br hmaxout hspec_br
                  refine ⟨fuel' + 1, endPos, by omega, ?_⟩
                  simp only [Zip.Native.Inflate.inflateLoop, bind, Except.bind,
                    hrb_bf, hrb_bt, hdh_native,
                    show Nat.toUInt32 1 = (1 : UInt32) from rfl]
                  have hbf_u32 : (bfinal_val.toUInt32 == 1) = false := by
                    have : bfinal_val = 0 := by simp only [beq_iff_eq] at hbf_ne1; omega
                    subst this; rfl
                  simp only [hbf_u32, Bool.false_eq_true, ↓reduceIte]
                  exact hloop
                · simp at hspec
        · -- btype_val = 2: dynamic Huffman
          -- Extract decodeDynamicTables from spec
          cases hspec_dt : Deflate.Spec.decodeDynamicTables bits₂ with
          | none => simp [hspec_dt] at hspec
          | some p₃ =>
            obtain ⟨litLens, distLens, bits₃⟩ := p₃
            simp only [hspec_dt] at hspec
            -- Extract decodeSymbols from spec
            cases hspec_ds : Deflate.Spec.decodeSymbols litLens distLens bits₃ with
            | none => simp [hspec_ds] at hspec
            | some p₄ =>
              obtain ⟨syms, rest⟩ := p₄
              simp only [hspec_ds] at hspec
              -- Extract resolveLZ77 from spec
              cases hspec_lz : Deflate.Spec.resolveLZ77 syms output.data.toList with
              | none => simp [hspec_lz] at hspec
              | some blockResult =>
                simp only [hspec_lz] at hspec
                -- Use decodeDynamicTrees_complete
                have hspec_dt' : Deflate.Spec.decodeDynamicTables br₂.toBits =
                    some (litLens, distLens, bits₃) := by rw [hrest₂]; exact hspec_dt
                obtain ⟨litTree, distTree, br₃, hdt_nat, hrest₃, hwf₃, hpos₃,
                    hflit_d, hfdist_d, hvlit, hvdist, hlen_lit, hlen_dist⟩ :=
                  decodeDynamicTrees_complete br₂ litLens distLens bits₃
                    hwf₂ hpos₂ hspec_dt'
                have ⟨hdata₃, _, hple₃⟩ :=
                  Zip.Native.decodeDynamicTrees_inv br₂ br₃ litTree distTree
                    hdt_nat hpos₂ hple₂
                -- Bridge decodeSymbols to native table names
                have hds_bridge : Deflate.Spec.decodeSymbols
                    ((litLens.map Nat.toUInt8).toArray.toList.map UInt8.toNat)
                    ((distLens.map Nat.toUInt8).toArray.toList.map UInt8.toNat)
                    br₃.toBits = some (syms, rest) := by
                  rw [validLengths_toUInt8_roundtrip litLens hvlit (by omega),
                      validLengths_toUInt8_roundtrip distLens hvdist (by omega),
                      hrest₃]
                  exact hspec_ds
                -- Split on bfinal
                split at hspec
                · -- bfinal_val == 1: final block
                  rename_i hbf1
                  cases hspec -- substitutes blockResult := result
                  obtain ⟨br', hdh, hrest_br, hwf_br, hpos_br⟩ :=
                    decodeHuffman_complete
                      (litLens.map Nat.toUInt8).toArray (distLens.map Nat.toUInt8).toArray
                      litTree distTree maxOutputSize br₃ output syms rest result
                      hwf₃ hpos₃ hflit_d hfdist_d
                      (by rw [validLengths_toUInt8_roundtrip litLens hvlit (by omega)]
                          exact hvlit)
                      (by rw [validLengths_toUInt8_roundtrip distLens hvdist (by omega)]
                          exact hvdist)
                      (by simp [List.size_toArray]; exact hlen_lit)
                      (by simp [List.size_toArray]; exact hlen_dist)
                      hmaxout br₃.data.size hple₃ (by omega)
                      hds_bridge hspec_lz
                  have hdh_native : Zip.Native.Inflate.decodeHuffman br₃ output
                      litTree distTree maxOutputSize =
                      .ok (⟨⟨result⟩⟩, br') := by
                    unfold Zip.Native.Inflate.decodeHuffman; exact hdh
                  refine ⟨1, br'.alignToByte.pos, by omega, ?_⟩
                  simp only [Zip.Native.Inflate.inflateLoop, bind, Except.bind,
                    hrb_bf, hrb_bt, hdt_nat, hdh_native,
                    show Nat.toUInt32 2 = (2 : UInt32) from rfl]
                  have hbf_u32 : (bfinal_val.toUInt32 == 1) = true := by
                    rw [beq_iff_eq] at hbf1 ⊢; subst hbf1; rfl
                  simp only [hbf_u32, ↓reduceIte, pure, Except.pure]
                · -- bfinal_val ≠ 1: recursive case
                  rename_i hbf_ne1
                  split at hspec
                  · rename_i hrest_lt
                    have hmax_block : blockResult.length ≤ maxOutputSize := by
                      have := (Deflate.Spec.decode_go_acc_prefix _ _ _ hspec).length_le
                      omega
                    obtain ⟨br', hdh, hrest_br, hwf_br, hpos_br⟩ :=
                      decodeHuffman_complete
                        (litLens.map Nat.toUInt8).toArray (distLens.map Nat.toUInt8).toArray
                        litTree distTree maxOutputSize br₃ output syms rest blockResult
                        hwf₃ hpos₃ hflit_d hfdist_d
                        (by rw [validLengths_toUInt8_roundtrip litLens hvlit (by omega)]
                            exact hvlit)
                        (by rw [validLengths_toUInt8_roundtrip distLens hvdist (by omega)]
                            exact hvdist)
                        (by simp [List.size_toArray]; exact hlen_lit)
                        (by simp [List.size_toArray]; exact hlen_dist)
                        hmax_block br₃.data.size hple₃ (by omega)
                        hds_bridge hspec_lz
                    have hdh_native : Zip.Native.Inflate.decodeHuffman br₃ output
                        litTree distTree maxOutputSize =
                        .ok (⟨⟨blockResult⟩⟩, br') := by
                      unfold Zip.Native.Inflate.decodeHuffman; exact hdh
                    have ⟨_, _, hple_br⟩ :=
                      Zip.Native.decodeHuffman_inv litTree distTree br₃ br' output
                        ⟨⟨blockResult⟩⟩ maxOutputSize hdh_native hpos₃ hple₃
                    -- Apply IH
                    have hrest_lt' : rest.length < len := by rw [← hlen]; exact hrest_lt
                    have hspec_br : Deflate.Spec.decode.go br'.toBits
                        (⟨⟨blockResult⟩⟩ : ByteArray).data.toList = some result := by
                      rw [hrest_br]; exact hspec
                    obtain ⟨fuel', endPos, hfuel_le, hloop⟩ :=
                      ih rest.length hrest_lt' br' ⟨⟨blockResult⟩⟩ result
                        (by rw [hrest_br]) hwf_br hpos_br hple_br hmaxout hspec_br
                    refine ⟨fuel' + 1, endPos, by omega, ?_⟩
                    simp only [Zip.Native.Inflate.inflateLoop, bind, Except.bind,
                      hrb_bf, hrb_bt, hdt_nat, hdh_native,
                      show Nat.toUInt32 2 = (2 : UInt32) from rfl]
                    have hbf_u32 : (bfinal_val.toUInt32 == 1) = false := by
                      have : bfinal_val = 0 := by simp only [beq_iff_eq] at hbf_ne1; omega
                      subst this; rfl
                    simp only [hbf_u32, Bool.false_eq_true, ↓reduceIte]
                    exact hloop
                  · simp at hspec
        · -- btype_val ≥ 3: reserved
          simp at hspec

end Deflate.Correctness
