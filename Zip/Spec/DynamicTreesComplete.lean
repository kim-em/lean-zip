import Zip.Spec.DynamicTreesCorrect

/-!
# Dynamic Huffman Tree Decode Completeness

Proves the completeness direction for dynamic Huffman tree decode:
if the spec's `decodeCLSymbols` / `readCLLengths` succeeds, then
the native implementation also succeeds with corresponding results.

Split from `DynamicTreesCorrect.lean` for file-size management.
-/

namespace Deflate.Correctness

/-- `readCLCodeLengths` completeness: if the spec's `readCLLengths` succeeds,
    then the native `readCLCodeLengths` also succeeds with corresponding results. -/
protected theorem readCLCodeLengths_complete (br : Zip.Native.BitReader)
    (clLengths : Array UInt8) (i numCodeLen : Nat)
    (clLengths' : List Nat) (rest : List Bool)
    (hwf : br.bitOff < 8)
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (hsize : clLengths.size = 19)
    (hspec : Deflate.Spec.readCLLengths (numCodeLen - i) i
        (clLengths.toList.map UInt8.toNat) br.toBits =
        some (clLengths', rest)) :
    ∃ br' clArr,
      Zip.Native.Inflate.readCLCodeLengths br clLengths i numCodeLen =
        .ok (clArr, br') ∧
      clArr.toList.map UInt8.toNat = clLengths' ∧
      br'.toBits = rest ∧
      br'.bitOff < 8 ∧
      (br'.bitOff = 0 ∨ br'.pos < br'.data.size) := by
  induction hd : numCodeLen - i generalizing br clLengths i with
  | zero =>
    -- i ≥ numCodeLen, both sides return immediately
    unfold Deflate.Spec.readCLLengths at hspec
    unfold Deflate.Spec.readCLLengths at hspec
    have hge : ¬(i < numCodeLen) := by omega
    have : numCodeLen - i = 0 := by omega
    rw [this] at hspec
    simp only at hspec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hspec)
    refine ⟨br, clLengths, ?_, rfl, rfl, hwf, hpos⟩
    unfold Zip.Native.Inflate.readCLCodeLengths
    simp [hge]
  | succ n ih =>
    have hi : i < numCodeLen := by omega
    -- Unfold spec
    have hd_succ : numCodeLen - i = n + 1 := hd
    conv at hspec => rw [hd_succ]; unfold Deflate.Spec.readCLLengths
    simp only [bind, Option.bind] at hspec
    -- Spec reads 3 bits
    cases hrb_spec : Deflate.Spec.readBitsLSB 3 br.toBits with
    | none => simp [hrb_spec] at hspec
    | some p =>
      obtain ⟨val, bits₁⟩ := p
      simp only [hrb_spec] at hspec
      -- Apply readBits_complete to get native readBits success
      have hval_bound := Deflate.Spec.readBitsLSB_bound hrb_spec
      have ⟨br₁, hrb_nat, hrest₁, hwf₁, hpos₁⟩ :=
        readBits_complete br 3 val bits₁ hwf hpos (by omega) hval_bound hrb_spec
      -- The spec updates via List.set, native updates via Array.set!
      -- Need to show the accumulator correspondence is preserved
      have h_acc :
          (List.map UInt8.toNat clLengths.toList).set (Deflate.Spec.codeLengthOrder[i]!) val =
          List.map UInt8.toNat
            (clLengths.set! (Zip.Native.Inflate.codeLengthOrder[i]!) val.toUInt32.toUInt8).toList := by
        rw [Array.set!, Array.toList_setIfInBounds, List.map_set]
        congr 1
        simp only [UInt32.toUInt8, UInt8.toNat, UInt8.ofNat, BitVec.toNat_ofNat,
          UInt32.toNat, UInt32.ofNat, BitVec.toNat_ofNat]
        omega
      rw [h_acc] at hspec
      have hsize₁ : (clLengths.set! (Zip.Native.Inflate.codeLengthOrder[i]!) val.toUInt32.toUInt8).size = 19 := by
        simp [Array.size_setIfInBounds, hsize]
      have hd₁ : numCodeLen - (i + 1) = n := by omega
      rw [← hrest₁, show n = numCodeLen - (i + 1) from by omega] at hspec
      have ⟨br', clArr, hrec, heq, hrest', hwf', hpos'⟩ :=
        ih br₁ _ (i + 1) hwf₁ hpos₁ hsize₁ hspec hd₁
      refine ⟨br', clArr, ?_, heq, hrest', hwf', hpos'⟩
      -- Unfold native
      unfold Zip.Native.Inflate.readCLCodeLengths
      simp only [if_pos hi, bind, Except.bind]
      -- readBits 3 succeeds
      rw [hrb_nat]
      exact hrec

-- guard/pure/Pure.pure false positives: removing them breaks the proof
set_option linter.unusedSimpArgs false in
/-- `decodeCLSymbols` completeness: if the spec's `decodeCLSymbols` succeeds,
    then the native `decodeCLSymbols` also succeeds with corresponding results. -/
protected theorem decodeCLSymbols_complete (clTree : Zip.Native.HuffTree)
    (clLengths : Array UInt8)
    (br : Zip.Native.BitReader) (codeLengths : Array UInt8)
    (idx totalCodes fuel : Nat)
    (resultLens : List Nat) (rest : List Bool)
    (hwf : br.bitOff < 8)
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (hcl : Zip.Native.HuffTree.fromLengths clLengths 7 = .ok clTree)
    (hsize_cl : clLengths.size ≤ UInt16.size)
    (hidx : idx ≤ totalCodes)
    (hsize : totalCodes ≤ codeLengths.size)
    (hspec : Deflate.Spec.decodeDynamicTables.decodeCLSymbols
        ((Huffman.Spec.allCodes (clLengths.toList.map UInt8.toNat) 7).map
          fun (sym, cw) => (cw, sym))
        totalCodes
        ((codeLengths.extract 0 idx).toList.map UInt8.toNat)
        br.toBits fuel =
        some (resultLens, rest)) :
    ∃ codeLengths' br',
      Zip.Native.Inflate.decodeCLSymbols clTree br codeLengths idx totalCodes fuel =
        .ok (codeLengths', br') ∧
      (codeLengths'.extract 0 totalCodes).toList.map UInt8.toNat = resultLens ∧
      br'.toBits = rest ∧
      br'.bitOff < 8 ∧
      (br'.bitOff = 0 ∨ br'.pos < br'.data.size) := by
  induction fuel generalizing br codeLengths idx with
  | zero => simp [Deflate.Spec.decodeDynamicTables.decodeCLSymbols] at hspec
  | succ fuel ih =>
    unfold Deflate.Spec.decodeDynamicTables.decodeCLSymbols at hspec
    have hle : idx ≤ codeLengths.size := by omega
    have h_acc_len : (List.map UInt8.toNat (codeLengths.extract 0 idx).toList).length = idx := by
      simp [List.length_map, Array.length_toList, Nat.min_eq_left hle]
    split at hspec
    · -- acc.length ≥ totalCodes: return immediately
      rename_i hge; rw [h_acc_len] at hge
      have heq : idx = totalCodes := by omega
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hspec)
      refine ⟨codeLengths, br, ?_, by rw [heq], rfl, hwf, hpos⟩
      unfold Zip.Native.Inflate.decodeCLSymbols
      simp only [show idx ≥ totalCodes from by omega, ↓reduceIte]
    · -- acc.length < totalCodes: decode a symbol
      rename_i hlt; rw [h_acc_len] at hlt
      have hidx_lt : idx < totalCodes := by omega
      simp only [bind, Option.bind] at hspec
      cases hdec_spec : Huffman.Spec.decode
          ((Huffman.Spec.allCodes (clLengths.toList.map UInt8.toNat) 7).map
            fun (sym, cw) => (cw, sym)) br.toBits with
      | none => simp [hdec_spec] at hspec
      | some p =>
        obtain ⟨sym, bits₁⟩ := p; simp only [hdec_spec] at hspec
        -- sym < clLengths.size from allCodes membership
        have ⟨cw, hmem, _⟩ := Deflate.Correctness.decode_some_mem _ _ _ _ hdec_spec
        have hmem' : (sym, cw) ∈ Huffman.Spec.allCodes (clLengths.toList.map UInt8.toNat) 7 := by
          rw [List.mem_map] at hmem; obtain ⟨⟨c, s⟩, hm, hinj⟩ := hmem
          simp at hinj; obtain ⟨rfl, rfl⟩ := hinj; exact hm
        rw [Huffman.Spec.allCodes_mem_iff] at hmem'
        have hsym_bound : sym < clLengths.size := by
          rw [List.length_map, Array.length_toList] at hmem'; exact hmem'.1
        have hsym_lt_u16 : sym < UInt16.size := by omega
        have hv := fromLengths_valid clLengths 7 clTree hcl
        have ⟨br₁, hdec_nat, hrest₁, hwf₁, hpos₁⟩ :=
          huffTree_decode_complete clLengths 7 (by omega) clTree br sym bits₁
            hwf hpos hcl hv hsize_cl hsym_bound hdec_spec
        -- Helper: sym.toUInt16.toNat = sym
        have hsym_toNat : sym.toUInt16.toNat = sym :=
          show sym % UInt16.size = sym from Nat.mod_eq_of_lt hsym_lt_u16
        split at hspec
        · -- sym < 16: literal
          rename_i hsym_lt
          have hsym_conv : sym.toUInt16.toUInt8.toNat = sym := by
            simp only [UInt16.toUInt8, UInt8.toNat, UInt8.ofNat, BitVec.toNat_ofNat,
              UInt16.toNat, UInt16.ofNat, BitVec.toNat_ofNat, Nat.toUInt16]
            rw [Nat.mod_eq_of_lt (show sym < 2 ^ 16 from by omega)]
            exact Nat.mod_eq_of_lt (by omega)
          have hsize₁ : totalCodes ≤ (codeLengths.set! idx sym.toUInt16.toUInt8).size := by
            simp [Array.size_setIfInBounds]; omega
          have ⟨cl', br', hrec, heq, hrest', hwf', hpos'⟩ :=
            ih br₁ (codeLengths.set! idx sym.toUInt16.toUInt8) (idx + 1) hwf₁ hpos₁
              (by omega) hsize₁ (by
                rw [extract_set_map_append codeLengths idx sym.toUInt16.toUInt8 (by omega),
                    hsym_conv, hrest₁]; exact hspec)
          refine ⟨cl', br', ?_, heq, hrest', hwf', hpos'⟩
          unfold Zip.Native.Inflate.decodeCLSymbols
          simp only [show ¬(idx ≥ totalCodes) from by omega, ↓reduceIte,
            bind, Except.bind, hdec_nat]
          have : sym.toUInt16 < 16 := by
            rw [UInt16.lt_iff_toNat_lt, hsym_toNat]; exact hsym_lt
          simp only [this, ↓reduceIte]; exact hrec
        · -- sym ≥ 16
          rename_i hsym_ge
          have hnat_not_lt : ¬(sym.toUInt16 < 16) := by
            intro hlt
            exact absurd (show sym < 16 by rwa [UInt16.lt_iff_toNat_lt, hsym_toNat] at hlt) hsym_ge
          split at hspec
          · -- sym == 16: repeat previous
            rename_i hsym16
            have hsym16_val : sym = 16 := by simp only [beq_iff_eq] at hsym16; exact hsym16
            simp only [guard, h_acc_len] at hspec
            by_cases hidx0 : idx > 0
            · -- guard passes
              rw [if_pos hidx0] at hspec
              simp only [pure, Pure.pure] at hspec
              -- readBitsLSB 2
              cases hrd_spec : Deflate.Spec.readBitsLSB 2 bits₁ with
              | none => simp [hrd_spec] at hspec
              | some p =>
                obtain ⟨rep, bits₂⟩ := p
                simp only [hrd_spec] at hspec
                have hval_bound := Deflate.Spec.readBitsLSB_bound hrd_spec
                have ⟨br₂, hrd_nat, hrest₂, hwf₂, hpos₂⟩ :=
                  readBits_complete br₁ 2 rep bits₂ hwf₁ hpos₁ (by omega) hval_bound
                    (by rw [hrest₁]; exact hrd_spec)
                -- Split on second guard: idx + (rep + 3) ≤ totalCodes
                have h_acc_len₂ : (List.map UInt8.toNat (codeLengths.extract 0 idx).toList ++
                    List.replicate (rep + 3) (List.map UInt8.toNat (codeLengths.extract 0 idx).toList).getLast!).length
                    = idx + (rep + 3) := by
                  simp [List.length_append, List.length_replicate, List.length_map,
                    Array.length_toList, Nat.min_eq_left hle]
                simp only [guard, h_acc_len₂] at hspec
                by_cases hbound_ok : idx + (rep + 3) ≤ totalCodes
                · rw [if_pos hbound_ok] at hspec
                  simp only [pure, Pure.pure] at hspec
                  have hfill_snd := fillEntries_snd codeLengths idx (rep + 3) totalCodes
                    codeLengths[idx - 1]! hbound_ok
                  have hfill_ext := fillEntries_extract codeLengths idx (rep + 3) totalCodes
                    codeLengths[idx - 1]! hbound_ok (by omega)
                  have hprev_eq := extract_map_getLast_eq codeLengths idx hidx0 (by omega)
                  have ⟨cl', br', hrec, heq, hrest', hwf', hpos'⟩ := ih br₂
                    (Zip.Native.Inflate.fillEntries codeLengths idx (rep + 3) totalCodes
                      codeLengths[idx - 1]!).fst
                    (idx + (rep + 3)) hwf₂ hpos₂
                    (by omega) (by rw [fillEntries_size]; omega) (by
                      rw [hfill_ext, ← hprev_eq, hrest₂]; exact hspec)
                  refine ⟨cl', br', ?_, heq, hrest', hwf', hpos'⟩
                  unfold Zip.Native.Inflate.decodeCLSymbols
                  simp only [show ¬(idx ≥ totalCodes) from by omega, ↓reduceIte,
                    bind, Except.bind, hdec_nat, hnat_not_lt]
                  have h16 : (sym.toUInt16 == 16) = true := by
                    simp only [beq_iff_eq]; rw [hsym16_val]; decide
                  simp only [h16, ↓reduceIte]
                  have hidx_ne0 : ((idx == 0) = false) := by
                    cases h : (idx == 0) <;> simp_all [beq_iff_eq]
                  simp only [hidx_ne0, Bool.false_eq_true, ↓reduceIte, pure, Except.pure]
                  rw [hrd_nat]
                  have hrep_toNat : rep.toUInt32.toNat = rep :=
                    Nat.mod_eq_of_lt (by omega)
                  have hcount : ¬(idx + (rep.toUInt32.toNat + 3) > totalCodes) := by
                    rw [hrep_toNat]; omega
                  simp only [hcount, ↓reduceIte]
                  rw [show rep.toUInt32.toNat + 3 = rep + 3 from by rw [hrep_toNat]]
                  rw [hfill_snd]; exact hrec
                · -- guard fails: none = some contradiction
                  rw [if_neg hbound_ok] at hspec; simp at hspec
            · -- idx = 0, guard fails: none = some contradiction
              rw [if_neg (by omega : ¬(idx > 0))] at hspec; simp at hspec
          · -- sym ≠ 16
            rename_i hsym_ne16
            have h16_false : (sym.toUInt16 == 16) = false := by
              cases h : sym.toUInt16 == 16
              · rfl
              · exfalso; rw [beq_iff_eq] at h
                have := congrArg UInt16.toNat h
                rw [hsym_toNat] at this
                exact absurd (beq_iff_eq.mpr (by simpa using this)) hsym_ne16
            split at hspec
            · -- sym == 17: zero fill short
              rename_i hsym17
              have hsym17_val : sym = 17 := by simp only [beq_iff_eq] at hsym17; exact hsym17
              -- readBitsLSB 3
              cases hrd_spec : Deflate.Spec.readBitsLSB 3 bits₁ with
              | none => simp [hrd_spec] at hspec
              | some p =>
                obtain ⟨rep, bits₂⟩ := p
                simp only [hrd_spec] at hspec
                have hval_bound := Deflate.Spec.readBitsLSB_bound hrd_spec
                have ⟨br₂, hrd_nat, hrest₂, hwf₂, hpos₂⟩ :=
                  readBits_complete br₁ 3 rep bits₂ hwf₁ hpos₁ (by omega) hval_bound
                    (by rw [hrest₁]; exact hrd_spec)
                -- guard (acc.length + (rep + 3) ≤ totalCodes)
                have h_acc_len₂ : (List.map UInt8.toNat (codeLengths.extract 0 idx).toList ++
                    List.replicate (rep + 3) 0).length = idx + (rep + 3) := by
                  simp [List.length_append, List.length_replicate, List.length_map,
                    Array.length_toList, Nat.min_eq_left hle]
                simp only [guard, h_acc_len₂] at hspec
                by_cases hbound_ok : idx + (rep + 3) ≤ totalCodes
                · rw [if_pos hbound_ok] at hspec
                  simp only [pure, Pure.pure] at hspec
                  have hfill_snd := fillEntries_snd codeLengths idx (rep + 3) totalCodes
                    (0 : UInt8) hbound_ok
                  have hfill_ext := fillEntries_extract codeLengths idx (rep + 3) totalCodes
                    (0 : UInt8) hbound_ok (by omega)
                  have ⟨cl', br', hrec, heq, hrest', hwf', hpos'⟩ := ih br₂
                    (Zip.Native.Inflate.fillEntries codeLengths idx (rep + 3) totalCodes 0).fst
                    (idx + (rep + 3)) hwf₂ hpos₂
                    (by omega) (by rw [fillEntries_size]; omega) (by
                      rw [hfill_ext, show (0 : UInt8).toNat = 0 from rfl, hrest₂]
                      exact hspec)
                  refine ⟨cl', br', ?_, heq, hrest', hwf', hpos'⟩
                  unfold Zip.Native.Inflate.decodeCLSymbols
                  simp only [show ¬(idx ≥ totalCodes) from by omega, ↓reduceIte,
                    bind, Except.bind, hdec_nat, hnat_not_lt, h16_false, Bool.false_eq_true]
                  have h17 : (sym.toUInt16 == 17) = true := by
                    simp only [beq_iff_eq]; rw [hsym17_val]; decide
                  simp only [h17, ↓reduceIte]
                  rw [hrd_nat]
                  have hrep_toNat : rep.toUInt32.toNat = rep :=
                    Nat.mod_eq_of_lt (by omega)
                  have hcount : ¬(idx + (rep.toUInt32.toNat + 3) > totalCodes) := by
                    rw [hrep_toNat]; omega
                  simp only [hcount, ↓reduceIte]
                  rw [show rep.toUInt32.toNat + 3 = rep + 3 from by rw [hrep_toNat]]
                  rw [hfill_snd]; exact hrec
                · rw [if_neg hbound_ok] at hspec; simp at hspec
            · -- sym ≠ 17
              rename_i hsym_ne17
              have h17_false : (sym.toUInt16 == 17) = false := by
                cases h : sym.toUInt16 == 17
                · rfl
                · exfalso; rw [beq_iff_eq] at h
                  have := congrArg UInt16.toNat h
                  rw [hsym_toNat] at this
                  exact absurd (beq_iff_eq.mpr (by simpa using this)) hsym_ne17
              split at hspec
              · -- sym == 18: zero fill long
                rename_i hsym18
                have hsym18_val : sym = 18 := by simp only [beq_iff_eq] at hsym18; exact hsym18
                -- readBitsLSB 7
                cases hrd_spec : Deflate.Spec.readBitsLSB 7 bits₁ with
                | none => simp [hrd_spec] at hspec
                | some p =>
                  obtain ⟨rep, bits₂⟩ := p
                  simp only [hrd_spec] at hspec
                  have hval_bound := Deflate.Spec.readBitsLSB_bound hrd_spec
                  have ⟨br₂, hrd_nat, hrest₂, hwf₂, hpos₂⟩ :=
                    readBits_complete br₁ 7 rep bits₂ hwf₁ hpos₁ (by omega) hval_bound
                      (by rw [hrest₁]; exact hrd_spec)
                  -- guard
                  have h_acc_len₂ : (List.map UInt8.toNat (codeLengths.extract 0 idx).toList ++
                      List.replicate (rep + 11) 0).length = idx + (rep + 11) := by
                    simp [List.length_append, List.length_replicate, List.length_map,
                    Array.length_toList, Nat.min_eq_left hle]
                  simp only [guard, h_acc_len₂] at hspec
                  by_cases hbound_ok : idx + (rep + 11) ≤ totalCodes
                  · rw [if_pos hbound_ok] at hspec
                    simp only [pure, Pure.pure] at hspec
                    have hfill_snd := fillEntries_snd codeLengths idx (rep + 11) totalCodes
                      (0 : UInt8) hbound_ok
                    have hfill_ext := fillEntries_extract codeLengths idx (rep + 11) totalCodes
                      (0 : UInt8) hbound_ok (by omega)
                    have ⟨cl', br', hrec, heq, hrest', hwf', hpos'⟩ := ih br₂
                      (Zip.Native.Inflate.fillEntries codeLengths idx (rep + 11) totalCodes 0).fst
                      (idx + (rep + 11)) hwf₂ hpos₂
                      (by omega) (by rw [fillEntries_size]; omega) (by
                        rw [hfill_ext, show (0 : UInt8).toNat = 0 from rfl, hrest₂]
                        exact hspec)
                    refine ⟨cl', br', ?_, heq, hrest', hwf', hpos'⟩
                    unfold Zip.Native.Inflate.decodeCLSymbols
                    simp only [show ¬(idx ≥ totalCodes) from by omega, ↓reduceIte,
                      bind, Except.bind, hdec_nat, hnat_not_lt, h16_false, Bool.false_eq_true,
                      h17_false]
                    have h18 : (sym.toUInt16 == 18) = true := by
                      simp only [beq_iff_eq]; rw [hsym18_val]; decide
                    simp only [h18, ↓reduceIte]
                    rw [hrd_nat]
                    have hrep_toNat : rep.toUInt32.toNat = rep :=
                      Nat.mod_eq_of_lt (by omega)
                    have hcount : ¬(idx + (rep.toUInt32.toNat + 11) > totalCodes) := by
                      rw [hrep_toNat]; omega
                    simp only [hcount, ↓reduceIte]
                    rw [show rep.toUInt32.toNat + 11 = rep + 11 from by rw [hrep_toNat]]
                    rw [hfill_snd]; exact hrec
                  · rw [if_neg hbound_ok] at hspec; simp at hspec
              · -- sym ∉ {<16, 16, 17, 18}: none, contradicts hspec
                simp at hspec

end Deflate.Correctness
