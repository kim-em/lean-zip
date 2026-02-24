import Zip.Spec.DecodeCorrect

/-!
# Dynamic Huffman Tree Decode Correctness

Proves that the native dynamic Huffman tree decoder
(`Zip.Native.Inflate.decodeDynamicTrees`) agrees with the formal
bitstream specification (`Deflate.Spec.decodeDynamicTables`).

Also proves `fromLengths_valid`: if `HuffTree.fromLengths` succeeds,
the code lengths satisfy `ValidLengths`.

Split from `InflateCorrect.lean` for file-size management.
-/

namespace Deflate.Correctness

/-! ## fromLengths validity -/

/-- If `fromLengths` succeeds, the code lengths satisfy `ValidLengths`. -/
theorem fromLengths_valid (lengths : Array UInt8) (maxBits : Nat)
    (tree : Zip.Native.HuffTree)
    (h : Zip.Native.HuffTree.fromLengths lengths maxBits = .ok tree) :
    Huffman.Spec.ValidLengths (lengths.toList.map UInt8.toNat) maxBits := by
  simp only [Zip.Native.HuffTree.fromLengths] at h
  split at h
  · simp at h
  · rename_i hany
    split at h
    · simp at h
    · rename_i hkraft
      simp only [Huffman.Spec.ValidLengths]
      constructor
      · intro l hl
        simp only [List.mem_map] at hl
        obtain ⟨u, hu, rfl⟩ := hl
        rw [Array.mem_toList_iff, Array.mem_iff_getElem] at hu
        obtain ⟨i, hi, rfl⟩ := hu
        rw [Bool.not_eq_true, Array.any_eq_false] at hany
        simpa using hany i hi
      · exact Nat.le_of_not_lt hkraft

/-! ## Dynamic trees correspondence -/

/-- `readCLCodeLengths` preserves well-formedness. -/
private theorem readCLCodeLengths_wf (br : Zip.Native.BitReader)
    (clLengths : Array UInt8) (i numCodeLen : Nat)
    (clLengths' : Array UInt8) (br' : Zip.Native.BitReader)
    (hwf : br.bitOff < 8)
    (h : Zip.Native.Inflate.readCLCodeLengths br clLengths i numCodeLen =
      .ok (clLengths', br')) :
    br'.bitOff < 8 := by
  induction hd : numCodeLen - i generalizing br clLengths i with
  | zero =>
    unfold Zip.Native.Inflate.readCLCodeLengths at h
    have : ¬(i < numCodeLen) := by omega
    simp [this] at h; obtain ⟨_, rfl⟩ := h; exact hwf
  | succ n ih =>
    unfold Zip.Native.Inflate.readCLCodeLengths at h
    split at h
    · rename_i hi
      simp only [bind, Except.bind] at h
      cases hrb : br.readBits 3 with
      | error e => simp [hrb] at h
      | ok p =>
        obtain ⟨v, br₁⟩ := p
        simp only [hrb] at h
        exact ih br₁ _ (i + 1) (readBits_wf br 3 v br₁ hwf hrb) h (by omega)
    · obtain ⟨_, rfl⟩ := Except.ok.inj h; exact hwf

/-- `readCLCodeLengths` preserves the position invariant. -/
private theorem readCLCodeLengths_pos_inv (br : Zip.Native.BitReader)
    (clLengths : Array UInt8) (i numCodeLen : Nat)
    (clLengths' : Array UInt8) (br' : Zip.Native.BitReader)
    (hwf : br.bitOff < 8)
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (h : Zip.Native.Inflate.readCLCodeLengths br clLengths i numCodeLen =
      .ok (clLengths', br')) :
    br'.bitOff = 0 ∨ br'.pos < br'.data.size := by
  induction hd : numCodeLen - i generalizing br clLengths i with
  | zero =>
    unfold Zip.Native.Inflate.readCLCodeLengths at h
    have : ¬(i < numCodeLen) := by omega
    simp [this] at h; obtain ⟨_, rfl⟩ := h; exact hpos
  | succ n ih =>
    unfold Zip.Native.Inflate.readCLCodeLengths at h
    split at h
    · rename_i hi
      simp only [bind, Except.bind] at h
      cases hrb : br.readBits 3 with
      | error e => simp [hrb] at h
      | ok p =>
        obtain ⟨v, br₁⟩ := p
        simp only [hrb] at h
        exact ih br₁ _ (i + 1) (readBits_wf br 3 v br₁ hwf hrb)
          (readBits_pos_inv br 3 v br₁ hwf hpos hrb) h (by omega)
    · obtain ⟨_, rfl⟩ := Except.ok.inj h; exact hpos

/-- `readCLCodeLengths` preserves array size. -/
private theorem readCLCodeLengths_size (br : Zip.Native.BitReader)
    (clLengths : Array UInt8) (i numCodeLen : Nat)
    (clLengths' : Array UInt8) (br' : Zip.Native.BitReader)
    (h : Zip.Native.Inflate.readCLCodeLengths br clLengths i numCodeLen =
      .ok (clLengths', br')) :
    clLengths'.size = clLengths.size := by
  induction hd : numCodeLen - i generalizing br clLengths i with
  | zero =>
    unfold Zip.Native.Inflate.readCLCodeLengths at h
    have : ¬(i < numCodeLen) := by omega
    simp [this] at h; obtain ⟨rfl, _⟩ := h; rfl
  | succ n ih =>
    have hi : i < numCodeLen := by omega
    unfold Zip.Native.Inflate.readCLCodeLengths at h
    simp only [if_pos hi, bind, Except.bind] at h
    cases hrb : br.readBits 3 with
    | error e => simp [hrb] at h
    | ok p =>
      obtain ⟨v, br₁⟩ := p
      simp only [hrb] at h
      have := ih br₁ _ (i + 1) h (by omega)
      simpa [Array.size_setIfInBounds] using this

/-- `decodeCLSymbols` preserves well-formedness. -/
private theorem decodeCLSymbols_wf (clTree : Zip.Native.HuffTree)
    (br : Zip.Native.BitReader) (codeLengths : Array UInt8)
    (idx totalCodes fuel : Nat)
    (codeLengths' : Array UInt8) (br' : Zip.Native.BitReader)
    (hwf : br.bitOff < 8)
    (h : Zip.Native.Inflate.decodeCLSymbols clTree br codeLengths idx totalCodes fuel =
      .ok (codeLengths', br')) :
    br'.bitOff < 8 := by
  induction fuel generalizing br codeLengths idx with
  | zero => simp [Zip.Native.Inflate.decodeCLSymbols] at h
  | succ n ih =>
    unfold Zip.Native.Inflate.decodeCLSymbols at h
    split at h
    · obtain ⟨_, rfl⟩ := Except.ok.inj h; exact hwf
    · simp only [bind, Except.bind] at h
      cases hdec : clTree.decode br with
      | error e => simp [hdec] at h
      | ok p =>
        obtain ⟨sym, br₁⟩ := p
        simp only [hdec] at h
        have hwf₁ := decode_wf clTree br sym br₁ hwf hdec
        split at h
        · exact ih br₁ _ _ hwf₁ h
        · split at h
          · -- sym == 16
            split at h
            · simp at h
            · simp only [pure, Except.pure] at h
              cases hrb : br₁.readBits 2 with
              | error e => simp [hrb] at h
              | ok p =>
                obtain ⟨rep, br₂⟩ := p
                simp only [hrb] at h
                split at h
                · simp at h
                · exact ih br₂ _ _ (readBits_wf br₁ 2 rep br₂ hwf₁ hrb) h
          · split at h
            · -- sym == 17
              cases hrb : br₁.readBits 3 with
              | error e => simp [hrb] at h
              | ok p =>
                obtain ⟨rep, br₂⟩ := p
                simp only [hrb] at h
                split at h
                · simp at h
                · simp only [pure, Except.pure] at h
                  exact ih br₂ _ _ (readBits_wf br₁ 3 rep br₂ hwf₁ hrb) h
            · split at h
              · -- sym == 18
                cases hrb : br₁.readBits 7 with
                | error e => simp [hrb] at h
                | ok p =>
                  obtain ⟨rep, br₂⟩ := p
                  simp only [hrb] at h
                  split at h
                  · simp at h
                  · simp only [pure, Except.pure] at h
                    exact ih br₂ _ _ (readBits_wf br₁ 7 rep br₂ hwf₁ hrb) h
              · simp at h

/-- `decodeCLSymbols` preserves the position invariant. -/
private theorem decodeCLSymbols_pos_inv (clTree : Zip.Native.HuffTree)
    (br : Zip.Native.BitReader) (codeLengths : Array UInt8)
    (idx totalCodes fuel : Nat)
    (codeLengths' : Array UInt8) (br' : Zip.Native.BitReader)
    (hwf : br.bitOff < 8)
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (h : Zip.Native.Inflate.decodeCLSymbols clTree br codeLengths idx totalCodes fuel =
      .ok (codeLengths', br')) :
    br'.bitOff = 0 ∨ br'.pos < br'.data.size := by
  induction fuel generalizing br codeLengths idx with
  | zero => simp [Zip.Native.Inflate.decodeCLSymbols] at h
  | succ n ih =>
    unfold Zip.Native.Inflate.decodeCLSymbols at h
    split at h
    · obtain ⟨_, rfl⟩ := Except.ok.inj h; exact hpos
    · simp only [bind, Except.bind] at h
      cases hdec : clTree.decode br with
      | error e => simp [hdec] at h
      | ok p =>
        obtain ⟨sym, br₁⟩ := p
        simp only [hdec] at h
        have hwf₁ := decode_wf clTree br sym br₁ hwf hdec
        have hpos₁ := decode_pos_inv clTree br sym br₁ hwf hpos hdec
        split at h
        · exact ih br₁ _ _ hwf₁ hpos₁ h
        · split at h
          · -- sym == 16
            split at h
            · simp at h
            · simp only [pure, Except.pure] at h
              cases hrb : br₁.readBits 2 with
              | error e => simp [hrb] at h
              | ok p =>
                obtain ⟨rep, br₂⟩ := p
                simp only [hrb] at h
                split at h
                · simp at h
                · exact ih br₂ _ _ (readBits_wf br₁ 2 rep br₂ hwf₁ hrb)
                    (readBits_pos_inv br₁ 2 rep br₂ hwf₁ hpos₁ hrb) h
          · split at h
            · -- sym == 17
              cases hrb : br₁.readBits 3 with
              | error e => simp [hrb] at h
              | ok p =>
                obtain ⟨rep, br₂⟩ := p
                simp only [hrb] at h
                split at h
                · simp at h
                · simp only [pure, Except.pure] at h
                  exact ih br₂ _ _ (readBits_wf br₁ 3 rep br₂ hwf₁ hrb)
                    (readBits_pos_inv br₁ 3 rep br₂ hwf₁ hpos₁ hrb) h
            · split at h
              · -- sym == 18
                cases hrb : br₁.readBits 7 with
                | error e => simp [hrb] at h
                | ok p =>
                  obtain ⟨rep, br₂⟩ := p
                  simp only [hrb] at h
                  split at h
                  · simp at h
                  · simp only [pure, Except.pure] at h
                    exact ih br₂ _ _ (readBits_wf br₁ 7 rep br₂ hwf₁ hrb)
                      (readBits_pos_inv br₁ 7 rep br₂ hwf₁ hpos₁ hrb) h
              · simp at h

/-- `readCLCodeLengths` corresponds to the spec's `readCLLengths`:
    native Array-based reading matches spec List-based reading. -/
private theorem readCLCodeLengths_correct (br : Zip.Native.BitReader)
    (clLengths : Array UInt8) (i numCodeLen : Nat)
    (clLengths' : Array UInt8) (br' : Zip.Native.BitReader)
    (hwf : br.bitOff < 8)
    (hsize : clLengths.size = 19)
    (h : Zip.Native.Inflate.readCLCodeLengths br clLengths i numCodeLen =
      .ok (clLengths', br')) :
    ∃ rest,
      Deflate.Spec.readCLLengths (numCodeLen - i) i
        (clLengths.toList.map UInt8.toNat) br.toBits =
        some (clLengths'.toList.map UInt8.toNat, rest) ∧
      br'.toBits = rest := by
  induction hd : numCodeLen - i generalizing br clLengths i with
  | zero =>
    -- i ≥ numCodeLen, so native returns immediately
    have hge : ¬(i < numCodeLen) := by omega
    unfold Zip.Native.Inflate.readCLCodeLengths at h
    simp only [if_neg hge, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨br.toBits, by rfl, rfl⟩
  | succ n ih =>
    -- i < numCodeLen
    have hi : i < numCodeLen := by omega
    unfold Zip.Native.Inflate.readCLCodeLengths at h
    simp only [if_pos hi, bind, Except.bind] at h
    cases hrb : br.readBits 3 with
    | error e => simp [hrb] at h
    | ok p =>
      obtain ⟨v, br₁⟩ := p
      simp only [hrb] at h
      have ⟨rest₁, hspec_rb, hrest₁⟩ := readBits_toBits br 3 v br₁ hwf (by omega) hrb
      have hwf₁ := readBits_wf br 3 v br₁ hwf hrb
      have hsize₁ : (clLengths.set! Zip.Native.Inflate.codeLengthOrder[i]! v.toUInt8).size = 19 := by
        simp [Array.size_setIfInBounds, hsize]
      have hd₁ : numCodeLen - (i + 1) = n := by omega
      have ⟨rest₂, hspec_rec, hrest₂⟩ := ih br₁ _ (i + 1) hwf₁ hsize₁ h hd₁
      refine ⟨rest₂, ?_, hrest₂⟩
      show Deflate.Spec.readCLLengths (n + 1) i
        (List.map UInt8.toNat clLengths.toList) br.toBits =
        some (List.map UInt8.toNat clLengths'.toList, rest₂)
      rw [Deflate.Spec.readCLLengths]
      simp only [bind, Option.bind, hspec_rb]
      have h_acc :
        (List.map UInt8.toNat clLengths.toList).set (Deflate.Spec.codeLengthOrder[i]!) v.toNat =
        List.map UInt8.toNat
          (clLengths.set! (Zip.Native.Inflate.codeLengthOrder[i]!) v.toUInt8).toList := by
        rw [Array.set!, Array.toList_setIfInBounds, List.map_set]
        congr 1
        have hbound := Deflate.Spec.readBitsLSB_bound hspec_rb
        show v.toNat = v.toNat % 256; omega
      rw [h_acc, ← hrest₁]
      exact hspec_rec

/-! ### Array extract/set helpers -/

private theorem take_set_succ (l : List UInt8) (idx : Nat) (val : UInt8)
    (hidx : idx < l.length) :
    (l.set idx val).take (idx + 1) = l.take idx ++ [val] := by
  rw [List.take_set, List.take_add_one]
  simp only [List.getElem?_eq_getElem (by omega)]
  rw [List.set_append]
  have h_take_len : (l.take idx).length = idx := List.length_take_of_le (by omega)
  simp only [h_take_len, Nat.lt_irrefl, ↓reduceIte, Nat.sub_self,
             Option.toList, List.set_cons_zero]

private theorem extract_set_map_append (arr : Array UInt8) (idx : Nat) (val : UInt8)
    (hidx : idx < arr.size) :
    ((arr.set! idx val).extract 0 (idx + 1)).toList.map UInt8.toNat =
    (arr.extract 0 idx).toList.map UInt8.toNat ++ [val.toNat] := by
  rw [Array.set!, Array.toList_extract, Array.toList_setIfInBounds, Array.toList_extract]
  simp only [List.extract, Nat.sub_zero, List.drop_zero]
  rw [take_set_succ _ _ _ (by rw [Array.length_toList]; exact hidx)]
  simp [List.map_append]

/-! ### getLast! helper -/

private theorem extract_map_getLast_eq (arr : Array UInt8) (idx : Nat)
    (hidx : 0 < idx) (hle : idx ≤ arr.size) :
    ((arr.extract 0 idx).toList.map UInt8.toNat).getLast! = arr[idx - 1]!.toNat := by
  simp only [Array.toList_extract, List.extract, Nat.sub_zero, List.drop_zero, List.map_take]
  have hlen : (List.take idx (List.map UInt8.toNat arr.toList)).length = idx := by
    simp [List.length_take, List.length_map, Array.length_toList, Nat.min_eq_left hle]
  rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_getElem?, hlen,
    List.getElem?_eq_getElem (by omega)]
  simp only [Option.getD_some]
  rw [getElem!_pos arr _ (by omega),
    @List.getElem_take _ (arr.toList.map UInt8.toNat) idx (idx - 1) (by rw [hlen]; omega)]
  simp [List.getElem_map]

/-! ### fillEntries helpers -/

private theorem fillEntries_size (arr : Array UInt8) (idx count bound : Nat) (val : UInt8) :
    (Zip.Native.Inflate.fillEntries arr idx count bound val).fst.size = arr.size := by
  induction count generalizing arr idx with
  | zero => simp [Zip.Native.Inflate.fillEntries]
  | succ n ih =>
    unfold Zip.Native.Inflate.fillEntries
    simp only [Nat.succ_ne_zero, false_or]
    split
    · rfl
    · simp only [Nat.add_sub_cancel]; rw [ih]; simp [Array.size_setIfInBounds]

private theorem fillEntries_snd (arr : Array UInt8) (idx count bound : Nat) (val : UInt8)
    (h : idx + count ≤ bound) :
    (Zip.Native.Inflate.fillEntries arr idx count bound val).snd = idx + count := by
  induction count generalizing arr idx with
  | zero => simp [Zip.Native.Inflate.fillEntries]
  | succ n ih =>
    unfold Zip.Native.Inflate.fillEntries
    simp only [Nat.succ_ne_zero, false_or, show ¬(idx ≥ bound) from by omega,
               ↓reduceIte, Nat.add_sub_cancel]
    rw [ih (arr.set! idx val) (idx + 1) (by omega)]; omega

private theorem fillEntries_extract (arr : Array UInt8) (idx count bound : Nat) (val : UInt8)
    (hcb : idx + count ≤ bound) (hba : bound ≤ arr.size) :
    let result := Zip.Native.Inflate.fillEntries arr idx count bound val
    (result.fst.extract 0 (idx + count)).toList.map UInt8.toNat =
    (arr.extract 0 idx).toList.map UInt8.toNat ++ List.replicate count val.toNat := by
  induction count generalizing arr idx with
  | zero => simp [Zip.Native.Inflate.fillEntries, List.replicate]
  | succ n ih =>
    unfold Zip.Native.Inflate.fillEntries
    simp only [Nat.succ_ne_zero, false_or, show ¬(idx ≥ bound) from by omega, ↓reduceIte,
               Nat.add_sub_cancel]
    have h_ih := ih (arr.set! idx val) (idx + 1) (by omega)
      (by simp [Array.size_setIfInBounds]; omega)
    simp only [show idx + 1 + n = idx + (n + 1) from by omega] at h_ih
    rw [h_ih]
    rw [Array.set!, Array.toList_extract, Array.toList_setIfInBounds, Array.toList_extract]
    simp only [List.extract, Nat.sub_zero, List.drop_zero]
    rw [take_set_succ _ _ _ (by rw [Array.length_toList]; omega)]
    simp [List.map_append, List.replicate_succ, List.append_assoc]

/-- `decodeCLSymbols` preserves array size. -/
private theorem decodeCLSymbols_size (clTree : Zip.Native.HuffTree)
    (br : Zip.Native.BitReader) (codeLengths : Array UInt8)
    (idx totalCodes fuel : Nat)
    (codeLengths' : Array UInt8) (br' : Zip.Native.BitReader)
    (h : Zip.Native.Inflate.decodeCLSymbols clTree br codeLengths idx totalCodes fuel =
      .ok (codeLengths', br')) :
    codeLengths'.size = codeLengths.size := by
  induction fuel generalizing br codeLengths idx with
  | zero => simp [Zip.Native.Inflate.decodeCLSymbols] at h
  | succ n ih =>
    unfold Zip.Native.Inflate.decodeCLSymbols at h
    split at h
    · obtain ⟨rfl, _⟩ := Except.ok.inj h; rfl
    · simp only [bind, Except.bind] at h
      cases hdec : clTree.decode br with
      | error e => simp [hdec] at h
      | ok p =>
        obtain ⟨sym, br₁⟩ := p
        simp only [hdec] at h
        split at h
        · -- sym < 16: set! preserves size
          have := ih br₁ _ _ h
          simpa [Array.size_setIfInBounds] using this
        · split at h
          · -- sym == 16
            split at h
            · simp at h
            · simp only [pure, Except.pure] at h
              cases hrb : br₁.readBits 2 with
              | error e => simp [hrb] at h
              | ok p =>
                obtain ⟨rep, br₂⟩ := p
                simp only [hrb] at h
                split at h
                · simp at h
                · have := ih br₂ _ _ h
                  rw [this, fillEntries_size]
          · split at h
            · -- sym == 17
              cases hrb : br₁.readBits 3 with
              | error e => simp [hrb] at h
              | ok p =>
                obtain ⟨rep, br₂⟩ := p
                simp only [hrb] at h
                split at h
                · simp at h
                · simp only [pure, Except.pure] at h
                  have := ih br₂ _ _ h
                  rw [this, fillEntries_size]
            · split at h
              · -- sym == 18
                cases hrb : br₁.readBits 7 with
                | error e => simp [hrb] at h
                | ok p =>
                  obtain ⟨rep, br₂⟩ := p
                  simp only [hrb] at h
                  split at h
                  · simp at h
                  · simp only [pure, Except.pure] at h
                    have := ih br₂ _ _ h
                    rw [this, fillEntries_size]
              · simp at h

/-- The length of the accumulated code lengths list equals `min idx codeLengths.size`. -/
private theorem accLen_eq_min (codeLengths : Array UInt8) (idx : Nat) :
    (List.map UInt8.toNat (codeLengths.extract 0 idx).toList).length =
    min idx codeLengths.size := by
  simp [List.length_map, Array.length_toList]

/-- `decodeCLSymbols` corresponds to the spec's `decodeDynamicTables.decodeCLSymbols`:
    native Array-based decoding matches spec List-based decoding. -/
private theorem decodeCLSymbols_correct (clTree : Zip.Native.HuffTree)
    (clLengths : Array UInt8)
    (br : Zip.Native.BitReader) (codeLengths : Array UInt8)
    (idx totalCodes fuel : Nat)
    (codeLengths' : Array UInt8) (br' : Zip.Native.BitReader)
    (hwf : br.bitOff < 8)
    (hcl : Zip.Native.HuffTree.fromLengths clLengths 7 = .ok clTree)
    (hsize_cl : clLengths.size ≤ UInt16.size)
    (hidx : idx ≤ totalCodes)
    (hsize : totalCodes ≤ codeLengths.size)
    (h : Zip.Native.Inflate.decodeCLSymbols clTree br codeLengths idx totalCodes fuel =
      .ok (codeLengths', br')) :
    let specLengths := clLengths.toList.map UInt8.toNat
    let specCodes := Huffman.Spec.allCodes specLengths 7
    let specTable := specCodes.map fun (sym, cw) => (cw, sym)
    let acc := (codeLengths.extract 0 idx).toList.map UInt8.toNat
    ∃ rest,
      Deflate.Spec.decodeDynamicTables.decodeCLSymbols specTable totalCodes
        acc br.toBits fuel =
        some ((codeLengths'.extract 0 totalCodes).toList.map UInt8.toNat, rest) ∧
      br'.toBits = rest := by
  induction fuel generalizing br codeLengths idx with
  | zero => simp [Zip.Native.Inflate.decodeCLSymbols] at h
  | succ fuel ih =>
    unfold Zip.Native.Inflate.decodeCLSymbols at h
    simp only [bind, Except.bind] at h
    split at h
    · -- idx ≥ totalCodes: return immediately
      rename_i hge
      simp [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨br.toBits, ?_, rfl⟩
      have heq : idx = totalCodes := by omega
      rw [heq]
      simp only [Deflate.Spec.decodeDynamicTables.decodeCLSymbols, bind, Option.bind,
        if_pos (show totalCodes ≤
          (List.map UInt8.toNat (codeLengths.extract 0 totalCodes).toList).length from by
          simp [List.length_map, Array.length_toList]; omega)]
    · -- idx < totalCodes: decode a symbol
      rename_i hlt
      have hidx_lt : idx < totalCodes := by omega
      cases hdec : clTree.decode br with
      | error e => simp [hdec] at h
      | ok p =>
        obtain ⟨sym, br₁⟩ := p
        simp only [hdec] at h
        have hv := fromLengths_valid clLengths 7 clTree hcl
        have hwf₁ := decode_wf clTree br sym br₁ hwf hdec
        have ⟨rest₁, hspec_dec, hrest₁⟩ :=
          huffTree_decode_correct clLengths 7 (by omega) clTree br sym br₁
            hwf hcl hv hsize_cl hdec
        simp only [Deflate.Spec.decodeDynamicTables.decodeCLSymbols, bind, Option.bind]
        have h_acc_len : ¬(totalCodes ≤
            (List.map UInt8.toNat (codeLengths.extract 0 idx).toList).length) := by
          simp only [List.length_map, Array.length_toList, Array.size_extract]; omega
        simp only [h_acc_len, ↓reduceIte, hspec_dec]
        have hle : idx ≤ codeLengths.size := by omega
        split at h
        · -- sym < 16: literal
          rename_i hsym_lt
          have hsym_nat : sym.toNat < 16 := hsym_lt
          simp only [hsym_nat, ↓reduceIte]
          have hsize₁ : totalCodes ≤ (codeLengths.set! idx sym.toUInt8).size := by
            simp [Array.size_setIfInBounds]; omega
          have hidx₁ : idx + 1 ≤ totalCodes := by omega
          have ⟨rest₂, hspec_rec, hrest₂⟩ :=
            ih br₁ (codeLengths.set! idx sym.toUInt8) (idx + 1) hwf₁ hidx₁ hsize₁ h
          refine ⟨rest₂, ?_, hrest₂⟩
          have hsym_conv : sym.toUInt8.toNat = sym.toNat := by
            show sym.toNat % 256 = sym.toNat; omega
          rw [hrest₁, extract_set_map_append codeLengths idx sym.toUInt8 (by omega),
            hsym_conv] at hspec_rec
          exact hspec_rec
        · -- sym ≥ 16
          rename_i hsym_ge
          have hsym_nat_ge : ¬(sym.toNat < 16) := hsym_ge
          simp only [hsym_nat_ge, ↓reduceIte]
          split at h
          · -- sym == 16
            rename_i hsym16
            have hsym16_val : sym.toNat = 16 := Deflate.Correctness.symVal_of_beq hsym16
            simp only [hsym16_val, show ((16 : Nat) == 16) = true from rfl, ↓reduceIte]
            split at h
            · simp at h
            · rename_i hidx_ne
              simp only [pure, Except.pure] at h
              have hidx_pos : 0 < idx := by
                simp only [beq_iff_eq] at hidx_ne; omega
              cases hrd : br₁.readBits 2 with
              | error e => simp [hrd] at h
              | ok p =>
                obtain ⟨rep, br₂⟩ := p
                simp only [hrd] at h
                split at h
                · simp at h
                · rename_i hbound
                  have hwf₂ := readBits_wf br₁ 2 rep br₂ hwf₁ hrd
                  have ⟨rest₂, hspec_rd, hrest₂⟩ :=
                    readBits_toBits br₁ 2 rep br₂ hwf₁ (by omega) hrd
                  have hfill_snd := fillEntries_snd codeLengths idx (rep.toNat + 3) totalCodes
                    codeLengths[idx - 1]! (by omega)
                  have hfill_ext := fillEntries_extract codeLengths idx (rep.toNat + 3) totalCodes
                    codeLengths[idx - 1]! (by omega) (by omega)
                  have ⟨rest₃, hspec_rec, hrest₃⟩ := ih br₂
                    (Zip.Native.Inflate.fillEntries codeLengths idx (rep.toNat + 3) totalCodes
                      codeLengths[idx - 1]!).fst
                    (Zip.Native.Inflate.fillEntries codeLengths idx (rep.toNat + 3) totalCodes
                      codeLengths[idx - 1]!).snd
                    hwf₂ (by rw [hfill_snd]; omega) (by rw [fillEntries_size]; omega) h
                  refine ⟨rest₃, ?_, hrest₃⟩
                  rw [hfill_snd, hfill_ext, hrest₂] at hspec_rec
                  have h_rd : Deflate.Spec.readBitsLSB 2 rest₁ = some (rep.toNat, rest₂) := by
                    rw [← hrest₁]; exact hspec_rd
                  have hprev_eq := extract_map_getLast_eq codeLengths idx hidx_pos (by omega)
                  have hacc_len := accLen_eq_min codeLengths idx
                  have hguard1 : 0 < min idx codeLengths.size := by
                    simp [Nat.min_eq_left hle]; omega
                  have hguard2 : min idx codeLengths.size + (rep.toNat + 3) ≤ totalCodes := by
                    simp [Nat.min_eq_left hle]; omega
                  simp only [guard, h_rd, hprev_eq,
                    hguard1, hguard2, hacc_len,
                    List.length_append, List.length_replicate,
                    ↓reduceIte] at hspec_rec ⊢
                  exact hspec_rec
          · -- sym ≠ 16
            rename_i hsym_ne16
            split at h
            · -- sym == 17
              rename_i hsym17
              have hsym17_val : sym.toNat = 17 := Deflate.Correctness.symVal_of_beq hsym17
              simp only [hsym17_val, show ((17 : Nat) == 16) = false from rfl,
                show ((17 : Nat) == 17) = true from rfl, ↓reduceIte]
              cases hrd : br₁.readBits 3 with
              | error e => simp [hrd] at h
              | ok p =>
                obtain ⟨rep, br₂⟩ := p
                simp only [hrd] at h
                split at h
                · simp at h
                · rename_i hbound
                  simp only [pure, Except.pure] at h
                  have hwf₂ := readBits_wf br₁ 3 rep br₂ hwf₁ hrd
                  have ⟨rest₂, hspec_rd, hrest₂⟩ :=
                    readBits_toBits br₁ 3 rep br₂ hwf₁ (by omega) hrd
                  have hfill_snd := fillEntries_snd codeLengths idx (rep.toNat + 3) totalCodes
                    (0 : UInt8) (by omega)
                  have hfill_ext := fillEntries_extract codeLengths idx (rep.toNat + 3) totalCodes
                    (0 : UInt8) (by omega) (by omega)
                  have ⟨rest₃, hspec_rec, hrest₃⟩ := ih br₂
                    (Zip.Native.Inflate.fillEntries codeLengths idx (rep.toNat + 3) totalCodes 0).fst
                    (Zip.Native.Inflate.fillEntries codeLengths idx (rep.toNat + 3) totalCodes 0).snd
                    hwf₂ (by rw [hfill_snd]; omega) (by rw [fillEntries_size]; omega) h
                  refine ⟨rest₃, ?_, hrest₃⟩
                  rw [hfill_snd, hfill_ext, hrest₂] at hspec_rec
                  have h_rd : Deflate.Spec.readBitsLSB 3 rest₁ = some (rep.toNat, rest₂) := by
                    rw [← hrest₁]; exact hspec_rd
                  have hacc_len := accLen_eq_min codeLengths idx
                  have hguard : min idx codeLengths.size + (rep.toNat + 3) ≤ totalCodes := by
                    simp [Nat.min_eq_left hle]; omega
                  simp only [guard, h_rd, hguard, hacc_len,
                    List.length_append, List.length_replicate,
                    ↓reduceIte,
                    show (0 : UInt8).toNat = 0 from rfl] at hspec_rec ⊢
                  exact hspec_rec
            · -- sym ≠ 17
              rename_i hsym_ne17
              split at h
              · -- sym == 18
                rename_i hsym18
                have hsym18_val : sym.toNat = 18 := Deflate.Correctness.symVal_of_beq hsym18
                simp only [hsym18_val, show ((18 : Nat) == 16) = false from rfl,
                  show ((18 : Nat) == 17) = false from rfl]
                cases hrd : br₁.readBits 7 with
                | error e => simp [hrd] at h
                | ok p =>
                  obtain ⟨rep, br₂⟩ := p
                  simp only [hrd] at h
                  split at h
                  · simp at h
                  · rename_i hbound
                    simp only [pure, Except.pure] at h
                    have hwf₂ := readBits_wf br₁ 7 rep br₂ hwf₁ hrd
                    have ⟨rest₂, hspec_rd, hrest₂⟩ :=
                      readBits_toBits br₁ 7 rep br₂ hwf₁ (by omega) hrd
                    have hfill_snd := fillEntries_snd codeLengths idx (rep.toNat + 11) totalCodes
                      (0 : UInt8) (by omega)
                    have hfill_ext := fillEntries_extract codeLengths idx (rep.toNat + 11) totalCodes
                      (0 : UInt8) (by omega) (by omega)
                    have ⟨rest₃, hspec_rec, hrest₃⟩ := ih br₂
                      (Zip.Native.Inflate.fillEntries codeLengths idx (rep.toNat + 11) totalCodes
                        0).fst
                      (Zip.Native.Inflate.fillEntries codeLengths idx (rep.toNat + 11) totalCodes
                        0).snd
                      hwf₂ (by rw [hfill_snd]; omega) (by rw [fillEntries_size]; omega) h
                    refine ⟨rest₃, ?_, hrest₃⟩
                    rw [hfill_snd, hfill_ext, hrest₂] at hspec_rec
                    have h_rd : Deflate.Spec.readBitsLSB 7 rest₁ = some (rep.toNat, rest₂) := by
                      rw [← hrest₁]; exact hspec_rd
                    have hacc_len := accLen_eq_min codeLengths idx
                    have hguard : min idx codeLengths.size + (rep.toNat + 11) ≤ totalCodes := by
                      simp [Nat.min_eq_left hle]; omega
                    simp only [guard, h_rd, hguard, hacc_len,
                      List.length_append, List.length_replicate,
                      ↓reduceIte,
                      show (0 : UInt8).toNat = 0 from rfl] at hspec_rec ⊢
                    exact hspec_rec
              · -- sym ∉ {16,17,18}: throw, contradicts .ok
                simp at h

/-- If the native dynamic tree decoder succeeds, the spec's
    `decodeDynamicTables` also succeeds with corresponding code lengths. -/
protected theorem decodeDynamicTrees_correct (br : Zip.Native.BitReader)
    (litTree distTree : Zip.Native.HuffTree) (br' : Zip.Native.BitReader)
    (hwf : br.bitOff < 8)
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (h : Zip.Native.Inflate.decodeDynamicTrees br = .ok (litTree, distTree, br')) :
    ∃ litLengths distLengths rest,
      Deflate.Spec.decodeDynamicTables br.toBits =
        some (litLengths.toList.map UInt8.toNat,
              distLengths.toList.map UInt8.toNat, rest) ∧
      br'.toBits = rest ∧
      br'.bitOff < 8 ∧
      (br'.bitOff = 0 ∨ br'.pos < br'.data.size) ∧
      Zip.Native.HuffTree.fromLengths litLengths = .ok litTree ∧
      Zip.Native.HuffTree.fromLengths distLengths = .ok distTree ∧
      Huffman.Spec.ValidLengths (litLengths.toList.map UInt8.toNat) 15 ∧
      Huffman.Spec.ValidLengths (distLengths.toList.map UInt8.toNat) 15 ∧
      litLengths.size ≤ UInt16.size ∧
      distLengths.size ≤ UInt16.size := by
  simp only [Zip.Native.Inflate.decodeDynamicTrees, bind, Except.bind] at h
  cases hrb1 : br.readBits 5 with
  | error e => simp [hrb1] at h
  | ok p1 =>
    obtain ⟨hlit_v, br₁⟩ := p1; simp only [hrb1] at h
    have hwf₁ := readBits_wf br 5 hlit_v br₁ hwf hrb1
    have hpos₁ := readBits_pos_inv br 5 hlit_v br₁ hwf hpos hrb1
    have ⟨rest₁, hspec1, hrest₁⟩ := readBits_toBits br 5 hlit_v br₁ hwf (by omega) hrb1
    cases hrb2 : br₁.readBits 5 with
    | error e => simp [hrb2] at h
    | ok p2 =>
      obtain ⟨hdist_v, br₂⟩ := p2; simp only [hrb2] at h
      have hwf₂ := readBits_wf br₁ 5 hdist_v br₂ hwf₁ hrb2
      have hpos₂ := readBits_pos_inv br₁ 5 hdist_v br₂ hwf₁ hpos₁ hrb2
      have ⟨rest₂, hspec2, hrest₂⟩ := readBits_toBits br₁ 5 hdist_v br₂ hwf₁ (by omega) hrb2
      cases hrb3 : br₂.readBits 4 with
      | error e => simp [hrb3] at h
      | ok p3 =>
        obtain ⟨hclen_v, br₃⟩ := p3; simp only [hrb3] at h
        have hwf₃ := readBits_wf br₂ 4 hclen_v br₃ hwf₂ hrb3
        have hpos₃ := readBits_pos_inv br₂ 4 hclen_v br₃ hwf₂ hpos₂ hrb3
        have ⟨rest₃, hspec3, hrest₃⟩ := readBits_toBits br₂ 4 hclen_v br₃ hwf₂ (by omega) hrb3
        cases hrcl : Zip.Native.Inflate.readCLCodeLengths br₃
            (.replicate 19 0) 0 (hclen_v.toNat + 4) with
        | error e => simp [hrcl] at h
        | ok p4 =>
          obtain ⟨clArr, br₄⟩ := p4; simp only [hrcl] at h
          have hwf₄ := readCLCodeLengths_wf br₃ _ 0 _ clArr br₄ hwf₃ hrcl
          have hpos₄ := readCLCodeLengths_pos_inv br₃ _ 0 _ clArr br₄ hwf₃ hpos₃ hrcl
          have hcl_sz : clArr.size = 19 :=
            by simpa using readCLCodeLengths_size br₃ _ 0 _ clArr br₄ hrcl
          have ⟨rest₄, hspec_rcl, hrest₄⟩ :=
            readCLCodeLengths_correct br₃ _ 0 _ clArr br₄ hwf₃ (by simp) hrcl
          cases hft : Zip.Native.HuffTree.fromLengths clArr 7 with
          | error e => simp [hft] at h
          | ok clTree₀ =>
            simp only [hft] at h
            cases hdcl : Zip.Native.Inflate.decodeCLSymbols clTree₀ br₄
                (.replicate (hlit_v.toNat + 257 + (hdist_v.toNat + 1)) 0)
                0 (hlit_v.toNat + 257 + (hdist_v.toNat + 1))
                (hlit_v.toNat + 257 + (hdist_v.toNat + 1)) with
            | error e => simp [hdcl] at h
            | ok p6 =>
              obtain ⟨clResults, br₅⟩ := p6; simp only [hdcl] at h
              have hwf₅ := decodeCLSymbols_wf clTree₀ br₄ _ 0 _ _
                clResults br₅ hwf₄ hdcl
              have hpos₅ := decodeCLSymbols_pos_inv clTree₀ br₄ _ 0 _ _
                clResults br₅ hwf₄ hpos₄ hdcl
              have hcl_res_sz : clResults.size =
                  hlit_v.toNat + 257 + (hdist_v.toNat + 1) :=
                by simpa using decodeCLSymbols_size clTree₀ br₄ _ 0 _ _ clResults br₅ hdcl
              have ⟨rest₅, hspec_dcl, hrest₅⟩ :=
                decodeCLSymbols_correct clTree₀ clArr br₄ _ 0 _
                  (hlit_v.toNat + 257 + (hdist_v.toNat + 1))
                  clResults br₅ hwf₄ hft
                  (by rw [hcl_sz]; simp [UInt16.size]) (by omega) (by simp) hdcl
              cases hflit : Zip.Native.HuffTree.fromLengths
                  (clResults.extract 0 (hlit_v.toNat + 257)) with
              | error e => simp [hflit] at h
              | ok litTree₀ =>
                simp only [hflit] at h
                cases hfdist : Zip.Native.HuffTree.fromLengths
                    (clResults.extract (hlit_v.toNat + 257)
                      (hlit_v.toNat + 257 + (hdist_v.toNat + 1))) with
                | error e => simp [hfdist] at h
                | ok distTree₀ =>
                  simp only [hfdist] at h
                  have hinj := Except.ok.inj h
                  simp only [Prod.mk.injEq] at hinj
                  obtain ⟨rfl, rfl, rfl⟩ := hinj
                  refine ⟨clResults.extract 0 (hlit_v.toNat + 257),
                          clResults.extract (hlit_v.toNat + 257)
                            (hlit_v.toNat + 257 + (hdist_v.toNat + 1)),
                          rest₅, ?_, hrest₅, hwf₅, hpos₅,
                          hflit, hfdist,
                          fromLengths_valid _ _ _ hflit,
                          fromLengths_valid _ _ _ hfdist,
                          ?_, ?_⟩
                  · -- Spec correspondence
                    simp only [Deflate.Spec.decodeDynamicTables, bind,
                      Option.bind, hspec1, hrest₁ ▸ hspec2, hrest₂ ▸ hspec3]
                    have hrcl_spec : Deflate.Spec.readCLLengths
                        (hclen_v.toNat + 4) 0
                        (List.replicate 19 0) rest₃ =
                        some (clArr.toList.map UInt8.toNat, rest₄) := by
                      rw [← hrest₃]
                      have : List.replicate 19 (0 : Nat) =
                          List.map UInt8.toNat (Array.replicate 19 0).toList := by
                        simp [Array.toList_replicate]
                      rw [this]
                      exact hspec_rcl
                    simp only [hrcl_spec]
                    have hdcl_spec : Deflate.Spec.decodeDynamicTables.decodeCLSymbols
                        ((Huffman.Spec.allCodes
                          (clArr.toList.map UInt8.toNat) 7).map
                          fun (sym, cw) => (cw, sym))
                        (hlit_v.toNat + 257 + (hdist_v.toNat + 1))
                        [] rest₄ (hlit_v.toNat + 257 + (hdist_v.toNat + 1)) =
                        some ((clResults.extract 0
                          (hlit_v.toNat + 257 + (hdist_v.toNat + 1))).toList.map
                          UInt8.toNat, rest₅) := by
                      rw [← hrest₄]
                      have : ([] : List Nat) = List.map UInt8.toNat
                          ((Array.replicate (hlit_v.toNat + 257 + (hdist_v.toNat + 1))
                            (0 : UInt8)).extract 0 0).toList := by
                        simp
                      rw [this]
                      exact hspec_dcl
                    simp only [hdcl_spec]
                    have hlen_eq : ((clResults.extract 0
                        (hlit_v.toNat + 257 + (hdist_v.toNat + 1))).toList.map
                        UInt8.toNat).length =
                        hlit_v.toNat + 257 + (hdist_v.toNat + 1) := by
                      simp [List.length_map, Array.length_toList, hcl_res_sz]
                    simp only [hlen_eq, beq_self_eq_true, guard, ite_true,
                      pure, Pure.pure]
                    refine congrArg some (Prod.ext ?_ (Prod.ext ?_ rfl))
                    · simp [Array.toList_extract, List.extract, List.map_take,
                        List.take_take]
                    · simp only [Array.toList_extract, List.extract,
                        Nat.sub_zero, List.drop_zero]
                      rw [← List.map_drop, List.drop_take]
                  · -- litLengths.size ≤ UInt16.size
                    have := Deflate.Spec.readBitsLSB_bound hspec1
                    have := Deflate.Spec.readBitsLSB_bound hspec2
                    simp [Array.size_extract, hcl_res_sz, UInt16.size]; omega
                  · -- distLengths.size ≤ UInt16.size
                    have := Deflate.Spec.readBitsLSB_bound hspec1
                    have := Deflate.Spec.readBitsLSB_bound hspec2
                    simp [Array.size_extract, hcl_res_sz, UInt16.size]; omega

end Deflate.Correctness
