import Zip.Spec.DynamicTreesCorrect
import Zip.Spec.DecodeComplete

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
    simp only [hge, ↓reduceIte]
  | succ n ih =>
    have hi : i < numCodeLen := by omega
    -- Unfold spec
    have hd_succ : numCodeLen - i = n + 1 := hd
    conv at hspec => rw [hd_succ]; unfold Deflate.Spec.readCLLengths
    simp only [bind, Option.bind] at hspec
    -- Spec reads 3 bits
    cases hrb_spec : Deflate.Spec.readBitsLSB 3 br.toBits with
    | none => rw [hrb_spec] at hspec; exact nomatch hspec
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
        simp only [Array.set!, Array.size_setIfInBounds, hsize]
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
    (idx totalCodes : Nat)
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
        br.toBits =
        some (resultLens, rest)) :
    ∃ codeLengths' br',
      Zip.Native.Inflate.decodeCLSymbols clTree br codeLengths idx totalCodes =
        .ok (codeLengths', br') ∧
      (codeLengths'.extract 0 totalCodes).toList.map UInt8.toNat = resultLens ∧
      br'.toBits = rest ∧
      br'.bitOff < 8 ∧
      (br'.bitOff = 0 ∨ br'.pos < br'.data.size) := by
  have ih : ∀ (idx' : Nat) (br_i : Zip.Native.BitReader) (cl : Array UInt8)
      (resultLens' : List Nat) (rest' : List Bool),
      totalCodes - idx' < totalCodes - idx →
      br_i.bitOff < 8 →
      (br_i.bitOff = 0 ∨ br_i.pos < br_i.data.size) →
      idx' ≤ totalCodes →
      totalCodes ≤ cl.size →
      Deflate.Spec.decodeDynamicTables.decodeCLSymbols
          ((Huffman.Spec.allCodes (clLengths.toList.map UInt8.toNat) 7).map
            fun (sym, cw) => (cw, sym))
          totalCodes
          ((cl.extract 0 idx').toList.map UInt8.toNat)
          br_i.toBits =
          some (resultLens', rest') →
      ∃ codeLengths' br',
        Zip.Native.Inflate.decodeCLSymbols clTree br_i cl idx' totalCodes =
          .ok (codeLengths', br') ∧
        (codeLengths'.extract 0 totalCodes).toList.map UInt8.toNat = resultLens' ∧
        br'.toBits = rest' ∧
        br'.bitOff < 8 ∧
        (br'.bitOff = 0 ∨ br'.pos < br'.data.size) :=
    fun idx' br_i cl resultLens' rest' hlt hwf' hpos' hidx' hsize' hspec' =>
      Correctness.decodeCLSymbols_complete clTree clLengths br_i cl idx' totalCodes
        resultLens' rest' hwf' hpos' hcl hsize_cl hidx' hsize' hspec'
  unfold Deflate.Spec.decodeDynamicTables.decodeCLSymbols at hspec
  have hle : idx ≤ codeLengths.size := by omega
  have h_acc_len : (List.map UInt8.toNat (codeLengths.extract 0 idx).toList).length = idx := by
    simp only [List.length_map, Array.length_toList, Array.size_extract, Nat.sub_zero,
      Nat.min_eq_left hle]
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
    cases hdec_spec : Huffman.Spec.decode
        ((Huffman.Spec.allCodes (clLengths.toList.map UInt8.toNat) 7).map
          fun (sym, cw) => (cw, sym)) br.toBits with
    | none => rw [hdec_spec] at hspec; exact nomatch hspec
    | some p =>
      obtain ⟨sym, bits₁⟩ := p; simp only [hdec_spec] at hspec
      -- sym < clLengths.size from allCodes membership
      have ⟨cw, hmem, _⟩ := Deflate.Correctness.decode_some_mem _ _ _ _ hdec_spec
      have hmem' : (sym, cw) ∈ Huffman.Spec.allCodes (clLengths.toList.map UInt8.toNat) 7 := by
        rw [List.mem_map] at hmem; obtain ⟨⟨c, s⟩, hm, hinj⟩ := hmem
        simp only [Prod.mk.injEq] at hinj; obtain ⟨rfl, rfl⟩ := hinj; exact hm
      rw [Huffman.Spec.allCodes_mem_iff] at hmem'
      have hsym_bound : sym < clLengths.size := by
        rw [List.length_map, Array.length_toList] at hmem'; exact hmem'.1
      have hsym_lt_u16 : sym < UInt16.size := by omega
      have hv := fromLengths_valid clLengths 7 clTree hcl
      have ⟨br₁, hdec_nat, hrest₁, hwf₁, hpos₁⟩ :=
        huffTree_decode_complete clLengths 7 (by omega) clTree br sym bits₁
          hwf hpos hcl hv hsym_bound hdec_spec
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
          simp only [Array.set!, Array.size_setIfInBounds]; omega
        have ⟨cl', br', hrec, heq, hrest', hwf', hpos'⟩ :=
          ih (idx + 1) br₁ (codeLengths.set! idx sym.toUInt16.toUInt8) resultLens rest
            (by omega) hwf₁ hpos₁ (by omega) hsize₁ (by
              rw [Array.extract_set_map_append codeLengths idx sym.toUInt16.toUInt8 (by omega),
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
          -- WF: if acc.length == 0 then none else match readBitsLSB 2 ...
          split at hspec
          · -- acc.length == 0: none = some contradiction
            exact nomatch hspec
          · -- acc.length ≠ 0
            rename_i hne0
            have hidx0 : idx > 0 := by
              simp only [h_acc_len, beq_iff_eq] at hne0; omega
            -- readBitsLSB 2
            cases hrd_spec : Deflate.Spec.readBitsLSB 2 bits₁ with
            | none => rw [hrd_spec] at hspec; exact nomatch hspec
            | some p =>
              obtain ⟨rep, bits₂⟩ := p
              simp only [hrd_spec] at hspec
              have hval_bound := Deflate.Spec.readBitsLSB_bound hrd_spec
              have ⟨br₂, hrd_nat, hrest₂, hwf₂, hpos₂⟩ :=
                readBits_complete br₁ 2 rep bits₂ hwf₁ hpos₁ (by omega) hval_bound
                  (by rw [hrest₁]; exact hrd_spec)
              -- Bound check: if acc'.length ≤ totalCodes
              split at hspec
              · -- bound holds
                rename_i h_le
                have hbound_ok : idx + (rep + 3) ≤ totalCodes := by
                  simp only [List.length_append, List.length_replicate, List.length_map,
                    Array.length_toList, Array.size_extract, Nat.sub_zero,
                    Nat.min_eq_left hle] at h_le; exact h_le
                have hfill_ext := fillEntries_extract codeLengths idx (rep + 3) totalCodes
                  codeLengths[idx - 1]! hbound_ok (by omega)
                have hprev_eq := Array.extract_map_getLast_eq codeLengths idx hidx0 (by omega)
                have ⟨cl', br', hrec, heq, hrest', hwf', hpos'⟩ :=
                  ih (idx + (rep + 3)) br₂
                    (Zip.Native.Inflate.fillEntries codeLengths idx (rep + 3) totalCodes
                      codeLengths[idx - 1]!).fst
                    resultLens rest
                    (by omega) hwf₂ hpos₂
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
                  rw [beq_eq_false_iff_ne]; omega
                simp only [hidx_ne0, Bool.false_eq_true, ↓reduceIte, pure, Except.pure]
                rw [hrd_nat]
                have hrep_toNat : rep.toUInt32.toNat = rep :=
                  Nat.mod_eq_of_lt (by omega)
                have hcount : ¬(idx + (rep.toUInt32.toNat + 3) > totalCodes) := by
                  rw [hrep_toNat]; omega
                simp only [hcount, ↓reduceIte]
                rw [show rep.toUInt32.toNat + 3 = rep + 3 from by rw [hrep_toNat]]
                exact hrec
              · -- bound fails: none = some contradiction
                exact nomatch hspec
        · -- sym ≠ 16
          rename_i hsym_ne16
          have h16_false : (sym.toUInt16 == 16) = false := by
            cases h : sym.toUInt16 == 16
            · rfl
            · exact absurd (beq_iff_eq.mpr (by rw [beq_iff_eq] at h; simpa only [hsym_toNat] using congrArg UInt16.toNat h)) hsym_ne16
          split at hspec
          · -- sym == 17: zero fill short
            rename_i hsym17
            have hsym17_val : sym = 17 := by simp only [beq_iff_eq] at hsym17; exact hsym17
            -- readBitsLSB 3
            cases hrd_spec : Deflate.Spec.readBitsLSB 3 bits₁ with
            | none => rw [hrd_spec] at hspec; exact nomatch hspec
            | some p =>
              obtain ⟨rep, bits₂⟩ := p
              simp only [hrd_spec] at hspec
              have hval_bound := Deflate.Spec.readBitsLSB_bound hrd_spec
              have ⟨br₂, hrd_nat, hrest₂, hwf₂, hpos₂⟩ :=
                readBits_complete br₁ 3 rep bits₂ hwf₁ hpos₁ (by omega) hval_bound
                  (by rw [hrest₁]; exact hrd_spec)
              -- Bound check: if acc'.length ≤ totalCodes
              split at hspec
              · -- bound holds
                rename_i h_le
                have hbound_ok : idx + (rep + 3) ≤ totalCodes := by
                  simp only [List.length_append, List.length_replicate, List.length_map,
                    Array.length_toList, Array.size_extract, Nat.sub_zero,
                    Nat.min_eq_left hle] at h_le; exact h_le
                have hfill_ext := fillEntries_extract codeLengths idx (rep + 3) totalCodes
                  (0 : UInt8) hbound_ok (by omega)
                have ⟨cl', br', hrec, heq, hrest', hwf', hpos'⟩ :=
                  ih (idx + (rep + 3)) br₂
                    (Zip.Native.Inflate.fillEntries codeLengths idx (rep + 3) totalCodes 0).fst
                    resultLens rest
                    (by omega) hwf₂ hpos₂
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
                exact hrec
              · -- bound fails
                exact nomatch hspec
          · -- sym ≠ 17
            rename_i hsym_ne17
            have h17_false : (sym.toUInt16 == 17) = false := by
              cases h : sym.toUInt16 == 17
              · rfl
              · exact absurd (beq_iff_eq.mpr (by rw [beq_iff_eq] at h; simpa only [hsym_toNat] using congrArg UInt16.toNat h)) hsym_ne17
            split at hspec
            · -- sym == 18: zero fill long
              rename_i hsym18
              have hsym18_val : sym = 18 := by simp only [beq_iff_eq] at hsym18; exact hsym18
              -- readBitsLSB 7
              cases hrd_spec : Deflate.Spec.readBitsLSB 7 bits₁ with
              | none => rw [hrd_spec] at hspec; exact nomatch hspec
              | some p =>
                obtain ⟨rep, bits₂⟩ := p
                simp only [hrd_spec] at hspec
                have hval_bound := Deflate.Spec.readBitsLSB_bound hrd_spec
                have ⟨br₂, hrd_nat, hrest₂, hwf₂, hpos₂⟩ :=
                  readBits_complete br₁ 7 rep bits₂ hwf₁ hpos₁ (by omega) hval_bound
                    (by rw [hrest₁]; exact hrd_spec)
                -- Bound check: if acc'.length ≤ totalCodes
                split at hspec
                · -- bound holds
                  rename_i h_le
                  have hbound_ok : idx + (rep + 11) ≤ totalCodes := by
                    simp only [List.length_append, List.length_replicate, List.length_map,
                      Array.length_toList, Array.size_extract, Nat.sub_zero,
                      Nat.min_eq_left hle] at h_le; exact h_le
                  have hfill_ext := fillEntries_extract codeLengths idx (rep + 11) totalCodes
                    (0 : UInt8) hbound_ok (by omega)
                  have ⟨cl', br', hrec, heq, hrest', hwf', hpos'⟩ :=
                    ih (idx + (rep + 11)) br₂
                      (Zip.Native.Inflate.fillEntries codeLengths idx (rep + 11) totalCodes 0).fst
                      resultLens rest
                      (by omega) hwf₂ hpos₂
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
                  exact hrec
                · -- bound fails
                  exact nomatch hspec
            · -- sym ∉ {<16, 16, 17, 18}: none, contradicts hspec
              exact nomatch hspec
termination_by totalCodes - idx

/-- If the spec's `decodeDynamicTables` succeeds, the native
    `decodeDynamicTrees` also succeeds with corresponding Huffman trees. -/
protected theorem decodeDynamicTrees_complete (br : Zip.Native.BitReader)
    (litLens distLens : List Nat) (bits' : List Bool)
    (hwf : br.bitOff < 8)
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (hspec : Deflate.Spec.decodeDynamicTables br.toBits = some (litLens, distLens, bits')) :
    ∃ (litTree distTree : Zip.Native.HuffTree) (br' : Zip.Native.BitReader),
      Zip.Native.Inflate.decodeDynamicTrees br = .ok (litTree, distTree, br') ∧
      br'.toBits = bits' ∧
      br'.bitOff < 8 ∧
      (br'.bitOff = 0 ∨ br'.pos < br'.data.size) ∧
      Huffman.Spec.ValidLengths litLens 15 ∧
      Huffman.Spec.ValidLengths distLens 15 ∧
      ∃ (litLengths distLengths : Array UInt8),
        Zip.Native.HuffTree.fromLengths litLengths = .ok litTree ∧
        Zip.Native.HuffTree.fromLengths distLengths = .ok distTree ∧
        litLengths.toList.map UInt8.toNat = litLens ∧
        distLengths.toList.map UInt8.toNat = distLens ∧
        litLengths.size ≤ UInt16.size ∧
        distLengths.size ≤ UInt16.size := by
  -- Unfold the spec function using `unfold` to avoid normalizing List.replicate
  unfold Deflate.Spec.decodeDynamicTables at hspec
  simp only [bind, Option.bind] at hspec
  -- Step 1: Read HLIT (5 bits)
  cases hrb1_spec : Deflate.Spec.readBitsLSB 5 br.toBits with
  | none => rw [hrb1_spec] at hspec; simp only [] at hspec; exact nomatch hspec
  | some p1 =>
    obtain ⟨hlit_v, bits₁⟩ := p1
    simp only [hrb1_spec] at hspec
    have hval1 := Deflate.Spec.readBitsLSB_bound hrb1_spec
    have ⟨br₁, hrb1_nat, hrest₁, hwf₁, hpos₁⟩ :=
      readBits_complete br 5 hlit_v bits₁ hwf hpos (by omega) hval1 hrb1_spec
    -- Step 2: Read HDIST (5 bits)
    cases hrb2_spec : Deflate.Spec.readBitsLSB 5 bits₁ with
    | none => rw [hrb2_spec] at hspec; simp only [] at hspec; exact nomatch hspec
    | some p2 =>
      obtain ⟨hdist_v, bits₂⟩ := p2
      simp only [hrb2_spec] at hspec
      have hval2 := Deflate.Spec.readBitsLSB_bound hrb2_spec
      have ⟨br₂, hrb2_nat, hrest₂, hwf₂, hpos₂⟩ :=
        readBits_complete br₁ 5 hdist_v bits₂ hwf₁ hpos₁ (by omega) hval2
          (by rw [hrest₁]; exact hrb2_spec)
      -- Step 3: Read HCLEN (4 bits)
      cases hrb3_spec : Deflate.Spec.readBitsLSB 4 bits₂ with
      | none => rw [hrb3_spec] at hspec; simp only [] at hspec; exact nomatch hspec
      | some p3 =>
        obtain ⟨hclen_v, bits₃⟩ := p3
        simp only [hrb3_spec] at hspec
        have hval3 := Deflate.Spec.readBitsLSB_bound hrb3_spec
        have ⟨br₃, hrb3_nat, hrest₃, hwf₃, hpos₃⟩ :=
          readBits_complete br₂ 4 hclen_v bits₃ hwf₂ hpos₂ (by omega) hval3
            (by rw [hrest₂]; exact hrb3_spec)
        -- Step 4: Read CL code lengths
        cases hrcl_spec : Deflate.Spec.readCLLengths (hclen_v + 4) 0
            (List.replicate 19 0) bits₃ with
        | none => rw [hrcl_spec] at hspec; simp only [] at hspec; exact nomatch hspec
        | some p4 =>
          obtain ⟨clLengths, bits₄⟩ := p4
          simp only [hrcl_spec] at hspec
          -- Use readCLCodeLengths_complete
          have hsize_repl : (Array.replicate 19 (0 : UInt8)).size = 19 := by simp only [Array.size_replicate]
          have hrcl_rewrite : Deflate.Spec.readCLLengths (hclen_v + 4 - 0) 0
              ((Array.replicate 19 (0 : UInt8)).toList.map UInt8.toNat) br₃.toBits =
              some (clLengths, bits₄) := by
            simp only [Nat.sub_zero, Array.toList_replicate, List.map_replicate,
              show (0 : UInt8).toNat = 0 from rfl]
            rw [hrest₃]; exact hrcl_spec
          have ⟨br₄, clArr, hrcl_nat, hcl_eq, hrest₄, hwf₄, hpos₄⟩ :=
            Correctness.readCLCodeLengths_complete br₃ (.replicate 19 0) 0
              (hclen_v + 4) clLengths bits₄ hwf₃ hpos₃ hsize_repl hrcl_rewrite
          have hcl_sz : clArr.size = 19 := by
            simpa only [] using Correctness.readCLCodeLengths_size br₃ _ 0 _ clArr br₄ hrcl_nat
          -- Step 5: ValidLengths guard for CL tree
          have hcl_valid : Huffman.Spec.ValidLengths clLengths 7 := by
            by_cases h : Huffman.Spec.ValidLengths clLengths 7
            · exact h
            · simp only [guard, h, ↓reduceIte] at hspec; exact nomatch hspec
          simp only [guard, hcl_valid, ↓reduceIte, pure, Pure.pure] at hspec
          -- Step 6: Build CL Huffman tree (fromLengths_complete)
          have hcl_vl : Huffman.Spec.ValidLengths (clArr.toList.map UInt8.toNat) 7 := by
            rw [hcl_eq]; exact hcl_valid
          have ⟨clTree, hft⟩ := fromLengths_complete clArr 7 hcl_vl
          -- Step 7: Decode CL symbols
          cases hdcl_spec : Deflate.Spec.decodeDynamicTables.decodeCLSymbols
              ((Huffman.Spec.allCodes clLengths 7).map fun (sym, cw) => (cw, sym))
              (hlit_v + 257 + (hdist_v + 1))
              [] bits₄ with
          | none => rw [hdcl_spec] at hspec; simp only [] at hspec; exact nomatch hspec
          | some p6 =>
            obtain ⟨codeLengths_list, bits₅⟩ := p6
            simp only [hdcl_spec] at hspec
            -- Step 8: Extract length, litVL, distVL guards
            have hlen_eq : codeLengths_list.length = hlit_v + 257 + (hdist_v + 1) := by
              by_cases h : codeLengths_list.length = hlit_v + 257 + (hdist_v + 1)
              · exact h
              · simp only [beq_iff_eq, h, ↓reduceIte] at hspec; exact nomatch hspec
            have hlit_valid : Huffman.Spec.ValidLengths
                (codeLengths_list.take (hlit_v + 257)) 15 := by
              by_cases h : Huffman.Spec.ValidLengths
                  (codeLengths_list.take (hlit_v + 257)) 15
              · exact h
              · simp only [beq_iff_eq, hlen_eq, h, ↓reduceIte] at hspec; exact nomatch hspec
            have hdist_valid : Huffman.Spec.ValidLengths
                (codeLengths_list.drop (hlit_v + 257)) 15 := by
              by_cases h : Huffman.Spec.ValidLengths
                  (codeLengths_list.drop (hlit_v + 257)) 15
              · exact h
              · simp only [beq_iff_eq, hlen_eq, hlit_valid, h, ↓reduceIte] at hspec
                exact nomatch hspec
            simp only [beq_iff_eq, hlen_eq, ↓reduceIte, hlit_valid,
              hdist_valid] at hspec
            -- Extract the final result
            obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hspec)
            -- Use decodeCLSymbols_complete
            have hdcl_rewrite : Deflate.Spec.decodeDynamicTables.decodeCLSymbols
                ((Huffman.Spec.allCodes (clArr.toList.map UInt8.toNat) 7).map
                  fun (sym, cw) => (cw, sym))
                (hlit_v + 257 + (hdist_v + 1))
                (((Array.replicate (hlit_v + 257 + (hdist_v + 1)) (0 : UInt8)).extract 0 0).toList.map UInt8.toNat)
                br₄.toBits =
                some (codeLengths_list, bits') := by
              simp only [Array.toList_extract, List.extract, Nat.sub_self,
                List.take_zero, List.drop_zero, List.map_nil]
              rw [hcl_eq, hrest₄]; exact hdcl_spec
            have hsize_cl : clArr.size ≤ UInt16.size := by
              rw [hcl_sz]; decide
            have ⟨clResults, br₅, hdcl_nat, hcl_res_eq, hrest₅, hwf₅, hpos₅⟩ :=
              Correctness.decodeCLSymbols_complete clTree clArr br₄
                (.replicate (hlit_v + 257 + (hdist_v + 1)) 0) 0
                (hlit_v + 257 + (hdist_v + 1))
                codeLengths_list bits' hwf₄ hpos₄ hft hsize_cl
                (by omega) (by simp only [Array.size_replicate]; omega) hdcl_rewrite
            -- Size of clResults
            have ⟨_, _, hcl_res_sz⟩ :=
              Correctness.decodeCLSymbols_inv clTree br₄ _
                0 _ clResults br₅ hwf₄ hpos₄ hdcl_nat
            simp only [Array.size_replicate] at hcl_res_sz
            -- Extract lit and dist lengths as arrays
            let litArr := clResults.extract 0 (hlit_v + 257)
            let distArr := clResults.extract (hlit_v + 257)
              (hlit_v + 257 + (hdist_v + 1))
            -- Establish full array correspondence (extract of full size = whole array)
            have hfull : clResults.toList.map UInt8.toNat = codeLengths_list := by
              have h := hcl_res_eq
              simp only [Array.toList_extract, List.extract,
                Nat.sub_zero, List.drop_zero] at h
              rwa [List.take_of_length_le
                (by rw [Array.length_toList, hcl_res_sz]; omega)] at h
            -- Relate mapped array extract to list take/drop
            have hlit_arr_eq : litArr.toList.map UInt8.toNat =
                codeLengths_list.take (hlit_v + 257) := by
              show (clResults.extract 0 (hlit_v + 257)).toList.map UInt8.toNat = _
              rw [Array.toList_extract, ← hfull]
              simp only [List.extract, Nat.sub_zero, List.drop_zero, List.map_take]
            have hdist_arr_eq : distArr.toList.map UInt8.toNat =
                codeLengths_list.drop (hlit_v + 257) := by
              show (clResults.extract (hlit_v + 257)
                (hlit_v + 257 + (hdist_v + 1))).toList.map UInt8.toNat = _
              rw [Array.toList_extract, ← hfull]
              simp only [List.extract]
              rw [List.map_take, List.map_drop]
              exact List.take_of_length_le
                (by rw [List.length_drop, List.length_map, Array.length_toList,
                    hcl_res_sz]; omega)
            -- ValidLengths for lit and dist arrays
            have hlit_vl : Huffman.Spec.ValidLengths
                (litArr.toList.map UInt8.toNat) 15 := by
              rw [hlit_arr_eq]; exact hlit_valid
            have hdist_vl : Huffman.Spec.ValidLengths
                (distArr.toList.map UInt8.toNat) 15 := by
              rw [hdist_arr_eq]; exact hdist_valid
            -- Build lit and dist trees
            have ⟨litTree, hflit⟩ := fromLengths_complete litArr 15 hlit_vl
            have ⟨distTree, hfdist⟩ := fromLengths_complete distArr 15 hdist_vl
            -- Assemble the result
            refine ⟨litTree, distTree, br₅, ?_, hrest₅, hwf₅, hpos₅,
                    ?_, ?_, litArr, distArr, hflit, hfdist,
                    hlit_arr_eq, hdist_arr_eq, ?_, ?_⟩
            · -- Native decodeDynamicTrees succeeds
              simp only [Zip.Native.Inflate.decodeDynamicTrees, bind, Except.bind]
              have hlit_toNat : hlit_v.toUInt32.toNat = hlit_v :=
                Nat.mod_eq_of_lt (by omega)
              have hdist_toNat : hdist_v.toUInt32.toNat = hdist_v :=
                Nat.mod_eq_of_lt (by omega)
              have hclen_toNat : hclen_v.toUInt32.toNat = hclen_v :=
                Nat.mod_eq_of_lt (by omega)
              rw [hrb1_nat]; simp only []
              rw [hrb2_nat]; simp only []
              rw [hrb3_nat]; simp only []
              simp only [hclen_toNat, hlit_toNat, hdist_toNat]
              rw [hrcl_nat]; simp only []
              rw [hft]; simp only []
              rw [hdcl_nat]; simp only []
              rw [show Zip.Native.HuffTree.fromLengths
                    (clResults.extract 0 (hlit_v + 257)) 15 = .ok litTree from hflit]
              simp only []
              rw [show Zip.Native.HuffTree.fromLengths
                    (clResults.extract (hlit_v + 257) (hlit_v + 257 + (hdist_v + 1))) 15
                    = .ok distTree from hfdist]; rfl
            · exact hlit_valid
            · exact hdist_valid
            · -- litArr.size ≤ UInt16.size
              show (clResults.extract 0 (hlit_v + 257)).size ≤ UInt16.size
              simp only [Array.size_extract, hcl_res_sz, UInt16.size]
              have := Deflate.Spec.readBitsLSB_bound hrb1_spec
              omega
            · -- distArr.size ≤ UInt16.size
              show (clResults.extract (hlit_v + 257)
                (hlit_v + 257 + (hdist_v + 1))).size ≤ UInt16.size
              simp only [Array.size_extract, hcl_res_sz, UInt16.size]
              have := Deflate.Spec.readBitsLSB_bound hrb2_spec
              omega

end Deflate.Correctness
