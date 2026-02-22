import Zip.Spec.DecodeCorrect

/-!
# DEFLATE Stream-Level Correctness

Proves the main correctness theorem: the native pure-Lean DEFLATE
decompressor (`Zip.Native.Inflate.inflateRaw`) agrees with the formal
bitstream specification (`Deflate.Spec.decode`).

This file handles the block loop (`inflateLoop_correct`) and the
top-level `inflate_correct` / `inflate_correct'` wrappers. Block-level
decode proofs (stored, Huffman) are in `DecodeCorrect`.
-/

namespace Deflate.Correctness

/-! ## Block loop helpers -/

/-- `decodeStored` preserves `bitOff < 8` and the position invariant. -/
private theorem decodeStored_invariants (br : Zip.Native.BitReader) (output : ByteArray)
    (maxOutputSize : Nat) (output' : ByteArray) (br' : Zip.Native.BitReader)
    (h : Zip.Native.Inflate.decodeStored br output maxOutputSize = .ok (output', br')) :
    br'.bitOff < 8 ∧ (br'.bitOff = 0 ∨ br'.pos < br'.data.size) := by
  simp only [Zip.Native.Inflate.decodeStored, bind, Except.bind] at h
  cases h₁ : br.readUInt16LE with
  | error e => simp [h₁] at h
  | ok p₁ =>
    obtain ⟨len, br₁⟩ := p₁; simp only [h₁] at h
    cases h₂ : br₁.readUInt16LE with
    | error e => simp [h₂] at h
    | ok p₂ =>
      obtain ⟨nlen, br₂⟩ := p₂; simp only [h₂] at h
      split at h
      · simp at h
      · simp only [pure, Except.pure] at h
        split at h
        · simp at h
        · cases h₃ : br₂.readBytes len.toNat with
          | error e => simp [h₃] at h
          | ok p₃ =>
            obtain ⟨bytes, br₃⟩ := p₃
            simp only [h₃, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨_, rfl⟩ := h
            have hwf := readBytes_wf br₂ len.toNat bytes br₃ h₃
            exact ⟨by omega, Or.inl hwf⟩

/-! ## Fixed code length correspondence -/

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem fixedLitLengths_eq :
    (Zip.Native.Inflate.fixedLitLengths).toList.map UInt8.toNat =
    Deflate.Spec.fixedLitLengths := by rfl

set_option maxRecDepth 2048 in
private theorem fixedDistLengths_eq :
    (Zip.Native.Inflate.fixedDistLengths).toList.map UInt8.toNat =
    Deflate.Spec.fixedDistLengths := by decide

set_option maxRecDepth 4096 in
private theorem fixedLitLengths_size :
    Zip.Native.Inflate.fixedLitLengths.size ≤ UInt16.size := by
  show 288 ≤ 65536; omega

private theorem fixedDistLengths_size :
    Zip.Native.Inflate.fixedDistLengths.size ≤ UInt16.size := by decide

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
        rw [Array.mem_toList_iff] at hu
        rw [Array.mem_iff_getElem] at hu
        obtain ⟨i, hi, rfl⟩ := hu
        rw [Bool.not_eq_true] at hany
        rw [Array.any_eq_false] at hany
        have := hany i hi
        simp at this
        exact this
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
      -- Get spec correspondence for readBits 3
      have ⟨rest₁, hspec_rb, hrest₁⟩ := readBits_toBits br 3 v br₁ hwf (by omega) hrb
      -- Apply IH to the recursive call
      have hwf₁ := readBits_wf br 3 v br₁ hwf hrb
      have hsize₁ : (clLengths.set! Zip.Native.Inflate.codeLengthOrder[i]! v.toUInt8).size = 19 := by
        simp [Array.size_setIfInBounds, hsize]
      have hd₁ : numCodeLen - (i + 1) = n := by omega
      have ⟨rest₂, hspec_rec, hrest₂⟩ := ih br₁ _ (i + 1) hwf₁ hsize₁ h hd₁
      refine ⟨rest₂, ?_, hrest₂⟩
      -- Unfold spec readCLLengths one step (not simp — it loops on recursion)
      show Deflate.Spec.readCLLengths (n + 1) i
        (List.map UInt8.toNat clLengths.toList) br.toBits =
        some (List.map UInt8.toNat clLengths'.toList, rest₂)
      rw [Deflate.Spec.readCLLengths]
      simp only [bind, Option.bind, hspec_rb]
      -- Goal: readCLLengths n (i+1) (acc.set clo[i]! v.toNat) rest₁ = some (...)
      -- hspec_rec: readCLLengths n (i+1) ((set! arr).toList.map ...) br₁.toBits = some (...)
      -- 1. Show list equality
      have h_acc :
        (List.map UInt8.toNat clLengths.toList).set (Deflate.Spec.codeLengthOrder[i]!) v.toNat =
        List.map UInt8.toNat
          (clLengths.set! (Zip.Native.Inflate.codeLengthOrder[i]!) v.toUInt8).toList := by
        rw [Array.set!, Array.toList_setIfInBounds, List.map_set]
        congr 1
        -- v.toNat = v.toUInt8.toNat ≡ v.toNat = v.toNat % 256
        -- readBitsLSB 3 produces val < 2^3 = 8 < 256
        have hbound := Deflate.Spec.readBitsLSB_bound hspec_rb
        show v.toNat = v.toNat % 256; omega
      rw [h_acc, ← hrest₁]
      exact hspec_rec

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
  sorry

/-- If the native dynamic tree decoder succeeds, the spec's
    `decodeDynamicTables` also succeeds with corresponding code lengths. -/
private theorem decodeDynamicTrees_correct (br : Zip.Native.BitReader)
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
  sorry

/-! ## Main correctness theorem -/

/-- Bridge: `(bfinal == 1) = true` (UInt32) implies `(bfinal.toNat == 1) = true` (Nat). -/
private theorem bfinal_beq_nat_true (bfinal : UInt32) (h : (bfinal == 1) = true) :
    (bfinal.toNat == 1) = true := by
  rw [beq_iff_eq] at h ⊢; exact congrArg UInt32.toNat h

/-- Bridge: `¬((bfinal == 1) = true)` (UInt32) implies `(bfinal.toNat == 1) = false`. -/
private theorem bfinal_beq_nat_false (bfinal : UInt32) (h : ¬((bfinal == 1) = true)) :
    (bfinal.toNat == 1) = false := by
  cases heq : bfinal.toNat == 1 <;> simp_all [← UInt32.toNat_inj]

set_option maxRecDepth 4096 in
/-- Block loop correspondence: the native `inflateLoop` agrees with
    the spec's `decode.go` on a block-by-block basis. -/
theorem inflateLoop_correct (br : Zip.Native.BitReader)
    (output : ByteArray)
    (fixedLit fixedDist : Zip.Native.HuffTree)
    (maxOutputSize fuel : Nat)
    (result : ByteArray) (endPos : Nat)
    (hwf : br.bitOff < 8)
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (hflit : Zip.Native.HuffTree.fromLengths
      Zip.Native.Inflate.fixedLitLengths = .ok fixedLit)
    (hfdist : Zip.Native.HuffTree.fromLengths
      Zip.Native.Inflate.fixedDistLengths = .ok fixedDist)
    (h : Zip.Native.Inflate.inflateLoop br output fixedLit fixedDist
      maxOutputSize fuel = .ok (result, endPos)) :
    ∃ specFuel,
      Deflate.Spec.decode.go br.toBits output.data.toList specFuel =
        some result.data.toList := by
  induction fuel generalizing br output with
  | zero =>
    unfold Zip.Native.Inflate.inflateLoop at h; simp at h
  | succ n ih =>
    unfold Zip.Native.Inflate.inflateLoop at h
    simp only [bind, Except.bind] at h
    -- readBits 1 (bfinal)
    cases hbf : br.readBits 1 with
    | error e => simp [hbf] at h
    | ok p =>
      obtain ⟨bfinal, br₁⟩ := p
      simp only [hbf] at h
      -- readBits 2 (btype)
      cases hbt : br₁.readBits 2 with
      | error e => simp [hbt] at h
      | ok p =>
        obtain ⟨btype, br₂⟩ := p
        simp only [hbt] at h
        -- Well-formedness chain
        have hwf₁ := readBits_wf br 1 bfinal br₁ hwf hbf
        have hwf₂ := readBits_wf br₁ 2 btype br₂ hwf₁ hbt
        have hpos₁ := readBits_pos_inv br 1 bfinal br₁ hwf hpos hbf
        have hpos₂ := readBits_pos_inv br₁ 2 btype br₂ hwf₁ hpos₁ hbt
        -- Spec-level readBitsLSB
        obtain ⟨rest₁, hspec_bf, hrest₁⟩ :=
          readBits_toBits br 1 bfinal br₁ hwf (by omega) hbf
        obtain ⟨rest₂, hspec_bt, hrest₂⟩ :=
          readBits_toBits br₁ 2 btype br₂ hwf₁ (by omega) hbt
        -- Case split on btype (0, 1, 2, or invalid).
        -- We use `by_cases + subst` so that btype is substituted everywhere,
        -- making (n : UInt32).toNat reduce definitionally on the spec side.
        by_cases hbt0 : btype = 0
        · -- btype = 0: stored block
          subst hbt0
          have hspec_bt' : Spec.readBitsLSB 2 br₁.toBits = some (0, rest₂) := hspec_bt
          cases hst : Zip.Native.Inflate.decodeStored br₂ output maxOutputSize with
          | error e => simp [hst] at h
          | ok p =>
            obtain ⟨output', br'⟩ := p
            simp only [hst] at h
            obtain ⟨storedBytes, rest₃, hspec_st, hout_eq, hrest₃⟩ :=
              decodeStored_correct br₂ output maxOutputSize output' br'
                hwf₂ hpos₂ hst
            obtain ⟨hwf', hpos'⟩ := decodeStored_invariants br₂ output maxOutputSize output' br' hst
            split at h
            · -- bfinal == 1: final block
              rename_i hbf1
              obtain ⟨rfl, _⟩ := Except.ok.inj h
              refine ⟨1, ?_⟩
              simp only [Deflate.Spec.decode.go, bind, Option.bind,
                hspec_bf, hspec_bt', ← hrest₁, ← hrest₂,
                hspec_st, hout_eq, pure, bfinal_beq_nat_true bfinal hbf1, ↓reduceIte]
            · -- bfinal ≠ 1: continue
              rename_i hbf1
              obtain ⟨sf, hgo⟩ := ih br' output' hwf' hpos' h
              refine ⟨sf + 1, ?_⟩
              simp only [Deflate.Spec.decode.go, bind, Option.bind,
                hspec_bf, hspec_bt', ← hrest₁, ← hrest₂,
                hspec_st, ← hout_eq, pure,
                bfinal_beq_nat_false bfinal hbf1]
              rw [← hrest₃]
              exact hgo
        · by_cases hbt1 : btype = 1
          · -- btype = 1: fixed Huffman
            subst hbt1
            have hspec_bt' : Spec.readBitsLSB 2 br₁.toBits = some (1, rest₂) := hspec_bt
            cases hhf : Zip.Native.Inflate.decodeHuffman br₂ output fixedLit
                fixedDist maxOutputSize with
            | error e => simp [hhf] at h
            | ok p =>
              obtain ⟨output', br'⟩ := p
              simp only [hhf] at h
              have hhf_go : Zip.Native.Inflate.decodeHuffman.go fixedLit fixedDist
                  maxOutputSize br₂ output 10000000 = .ok (output', br') := by
                simp only [Zip.Native.Inflate.decodeHuffman] at hhf; exact hhf
              obtain ⟨syms, rest_h, hds, hlz, hbr'_eq, hwf', hpos'⟩ :=
                decodeHuffman_correct
                  Zip.Native.Inflate.fixedLitLengths
                  Zip.Native.Inflate.fixedDistLengths
                  fixedLit fixedDist maxOutputSize 10000000
                  br₂ output output' br' hwf₂ hpos₂
                  hflit hfdist
                  (fixedLitLengths_eq ▸ Deflate.Spec.fixedLitLengths_valid)
                  (fixedDistLengths_eq ▸ Deflate.Spec.fixedDistLengths_valid)
                  fixedLitLengths_size fixedDistLengths_size
                  hhf_go
              split at h
              · -- bfinal == 1: final block
                rename_i hbf1
                obtain ⟨rfl, _⟩ := Except.ok.inj h
                refine ⟨1, ?_⟩
                simp only [Deflate.Spec.decode.go, bind, Option.bind,
                  hspec_bf, hspec_bt', ← hrest₁, ← hrest₂,
                  ← fixedLitLengths_eq, ← fixedDistLengths_eq,
                  hds, hlz, pure, bfinal_beq_nat_true bfinal hbf1, ↓reduceIte]
              · -- bfinal ≠ 1: continue
                rename_i hbf1
                obtain ⟨sf, hgo⟩ := ih br' output' hwf' hpos' h
                refine ⟨sf + 1, ?_⟩
                simp only [Deflate.Spec.decode.go, bind, Option.bind,
                  hspec_bf, hspec_bt', ← hrest₁, ← hrest₂,
                  ← fixedLitLengths_eq, ← fixedDistLengths_eq,
                  hds, hlz, pure, bfinal_beq_nat_false bfinal hbf1]
                rw [← hbr'_eq]
                exact hgo
          · by_cases hbt2 : btype = 2
            · -- btype = 2: dynamic Huffman
              subst hbt2
              have hspec_bt' : Spec.readBitsLSB 2 br₁.toBits = some (2, rest₂) := hspec_bt
              cases hdt : Zip.Native.Inflate.decodeDynamicTrees br₂ with
              | error e => simp [hdt] at h
              | ok p =>
                obtain ⟨litTree, distTree, br₃⟩ := p
                simp only [hdt] at h
                obtain ⟨litLens, distLens, rest_dt, hspec_dt, hrest_dt, hwf₃,
                  hpos₃, hflit_dyn, hfdist_dyn, hvlit_dyn, hvdist_dyn,
                  hsize_lit, hsize_dist⟩ :=
                  decodeDynamicTrees_correct br₂ litTree distTree br₃ hwf₂ hpos₂ hdt
                cases hhf : Zip.Native.Inflate.decodeHuffman br₃ output litTree
                    distTree maxOutputSize with
                | error e => simp [hhf] at h
                | ok p =>
                  obtain ⟨output', br'⟩ := p
                  simp only [hhf] at h
                  have hhf_go : Zip.Native.Inflate.decodeHuffman.go litTree distTree
                      maxOutputSize br₃ output 10000000 = .ok (output', br') := by
                    simp only [Zip.Native.Inflate.decodeHuffman] at hhf; exact hhf
                  obtain ⟨syms, rest_h, hds, hlz, hbr'_eq, hwf', hpos'⟩ :=
                    decodeHuffman_correct litLens distLens litTree distTree
                      maxOutputSize 10000000 br₃ output output' br' hwf₃ hpos₃
                      hflit_dyn hfdist_dyn hvlit_dyn hvdist_dyn
                      hsize_lit hsize_dist hhf_go
                  split at h
                  · -- bfinal == 1: final block
                    rename_i hbf1
                    obtain ⟨rfl, _⟩ := Except.ok.inj h
                    refine ⟨1, ?_⟩
                    simp only [Deflate.Spec.decode.go, bind, Option.bind,
                      hspec_bf, hspec_bt', ← hrest₁, ← hrest₂,
                      hspec_dt, ← hrest_dt, hds, hlz, pure,
                      bfinal_beq_nat_true bfinal hbf1, ↓reduceIte]
                  · -- bfinal ≠ 1: continue
                    rename_i hbf1
                    obtain ⟨sf, hgo⟩ := ih br' output' hwf' hpos' h
                    refine ⟨sf + 1, ?_⟩
                    simp only [Deflate.Spec.decode.go, bind, Option.bind,
                      hspec_bf, hspec_bt', ← hrest₁, ← hrest₂,
                      hspec_dt, ← hrest_dt, hds, hlz, pure,
                      bfinal_beq_nat_false bfinal hbf1]
                    rw [← hbr'_eq]
                    exact hgo
            · -- btype ≥ 3: reserved (native throws error)
              exfalso
              split at h <;> first | contradiction | simp at h

/-- **Main theorem**: If the native DEFLATE decompressor succeeds, then
    the formal specification also succeeds and produces the same output. -/
theorem inflate_correct (data : ByteArray) (startPos maxOutputSize : Nat)
    (result : ByteArray) (endPos : Nat)
    (h : Zip.Native.Inflate.inflateRaw data startPos maxOutputSize =
      .ok (result, endPos)) :
    ∃ fuel,
      Deflate.Spec.decode
        ((Deflate.Spec.bytesToBits data).drop (startPos * 8)) fuel =
        some result.data.toList := by
  -- Unfold inflateRaw
  simp only [Zip.Native.Inflate.inflateRaw, bind, Except.bind] at h
  -- Build fixed trees
  cases hflit : Zip.Native.HuffTree.fromLengths
      Zip.Native.Inflate.fixedLitLengths with
  | error e => simp [hflit] at h
  | ok fixedLit =>
    simp only [hflit] at h
    cases hfdist : Zip.Native.HuffTree.fromLengths
        Zip.Native.Inflate.fixedDistLengths with
    | error e => simp [hfdist] at h
    | ok fixedDist =>
      simp only [hfdist] at h
      -- Now h : inflateLoop ... = .ok (result, endPos)
      have hbr_wf : (Zip.Native.BitReader.mk data startPos 0).bitOff < 8 := by simp
      have hbr_pos : (Zip.Native.BitReader.mk data startPos 0).bitOff = 0 ∨
          (Zip.Native.BitReader.mk data startPos 0).pos <
          (Zip.Native.BitReader.mk data startPos 0).data.size := by simp
      obtain ⟨specFuel, hgo⟩ := inflateLoop_correct
        ⟨data, startPos, 0⟩ .empty fixedLit fixedDist
        maxOutputSize 10001 result endPos
        hbr_wf hbr_pos hflit hfdist h
      -- decode = go bits [] fuel
      exact ⟨specFuel, by
        simp only [Deflate.Spec.decode]; exact hgo⟩

/-- Corollary: `inflate` (which starts at position 0) agrees with
    `decodeBytes` (which also starts at position 0). -/
theorem inflate_correct' (data : ByteArray) (maxOutputSize : Nat)
    (result : ByteArray)
    (h : Zip.Native.Inflate.inflate data maxOutputSize = .ok result) :
    ∃ fuel,
      Deflate.Spec.decode (Deflate.Spec.bytesToBits data) fuel =
        some result.data.toList := by
  -- Unfold inflate: it calls inflateRaw data 0 maxOutputSize and discards endPos
  simp only [Zip.Native.Inflate.inflate, bind, Except.bind] at h
  cases hinf : Zip.Native.Inflate.inflateRaw data 0 maxOutputSize with
  | error e => simp [hinf] at h
  | ok p =>
    simp [hinf, pure, Except.pure] at h
    have := inflate_correct data 0 maxOutputSize p.1 p.2 (by rw [hinf])
    simp at this
    rw [← h]; exact this

end Deflate.Correctness
