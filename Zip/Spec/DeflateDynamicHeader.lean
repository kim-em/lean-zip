import Zip.Spec.DeflateDynamicEmit

/-!
# writeDynamicHeader ↔ encodeDynamicTrees correspondence

Proves that the native `writeDynamicHeader` produces the same bit sequence
as the spec-level `encodeDynamicTrees`.

## Key results

- `writeDynamicHeader_spec`: correspondence with spec `encodeDynamicTrees`
- `writeDynamicHeader_wf`: well-formedness preservation
-/

namespace Zip.Native.Deflate

/-! ## writeDynamicHeader ↔ encodeDynamicTrees correspondence -/

/-- `writeCLLengths` loop produces the same bits as spec `writeCLLengths`.
    Note: starts from position `i`, so produces the suffix from `i`. -/
private theorem writeCLLengths_go_spec (bw : BitWriter) (clLens : List Nat)
    (numCodeLen i : Nat) (hwf : bw.wf) (hn : numCodeLen ≤ 19)
    (hcl_bound : ∀ x ∈ clLens, x ≤ 7) :
    (writeDynamicHeader.writeCLLengths bw clLens numCodeLen i).toBits =
    bw.toBits ++ ((Deflate.Spec.clPermutation.take numCodeLen).drop i).flatMap
      (fun pos => Deflate.Spec.writeBitsLSB 3 (clLens.getD pos 0)) := by
  suffices ∀ k, k = numCodeLen - i →
      (writeDynamicHeader.writeCLLengths bw clLens numCodeLen i).toBits =
      bw.toBits ++ ((Deflate.Spec.clPermutation.take numCodeLen).drop i).flatMap
        (fun pos => Deflate.Spec.writeBitsLSB 3 (clLens.getD pos 0)) by
    exact this _ rfl
  intro k
  induction k generalizing bw i with
  | zero =>
    intro heq
    have hge : i ≥ numCodeLen := by omega
    have hdrop : (Deflate.Spec.clPermutation.take numCodeLen).drop i = [] := by
      simp [List.drop_eq_nil_iff, List.length_take]; omega
    unfold writeDynamicHeader.writeCLLengths
    simp [show ¬(i < numCodeLen) from by omega, hdrop]
  | succ n ih =>
    intro heq
    have hlt : i < numCodeLen := by omega
    unfold writeDynamicHeader.writeCLLengths
    rw [if_pos hlt]
    have hwf' := BitWriter.writeBits_wf bw 3 (clLens.getD (Deflate.Spec.clPermutation.getD i 0) 0).toUInt32 hwf (by omega)
    have hbits := BitWriter.writeBits_toBits bw 3 (clLens.getD (Deflate.Spec.clPermutation.getD i 0) 0).toUInt32 hwf (by omega)
    rw [ih _ (i + 1) hwf' (by omega)]
    rw [hbits]
    have hperm_len : Deflate.Spec.clPermutation.length = 19 := by
      simp [Deflate.Spec.clPermutation]
    have hi_bound : i < (Deflate.Spec.clPermutation.take numCodeLen).length := by
      simp [List.length_take]; omega
    rw [List.drop_eq_getElem_cons hi_bound]
    simp only [List.flatMap_cons, List.append_assoc]
    congr 1
    · -- Show the element matches
      have hi_perm : i < Deflate.Spec.clPermutation.length := by
        simp [Deflate.Spec.clPermutation]; omega
      have hgetD : Deflate.Spec.clPermutation.getD i 0 =
          (Deflate.Spec.clPermutation.take numCodeLen)[i] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi_perm, Option.getD_some]
        simp
      rw [hgetD]
      simp only [Nat.toUInt32, UInt32.ofNat, UInt32.toNat, BitVec.toNat_ofNat]
      have hmod : clLens.getD (Deflate.Spec.clPermutation.take numCodeLen)[i] 0 % 2 ^ 32 =
          clLens.getD (Deflate.Spec.clPermutation.take numCodeLen)[i] 0 := by
        apply Nat.mod_eq_of_lt
        have : clLens.getD (Deflate.Spec.clPermutation.take numCodeLen)[i] 0 ≤ 7 := by
          rw [List.getD_eq_getElem?_getD]
          by_cases hb : (Deflate.Spec.clPermutation.take numCodeLen)[i] < clLens.length
          · rw [List.getElem?_eq_getElem hb, Option.getD_some]
            exact hcl_bound _ (List.getElem_mem ..)
          · rw [List.getElem?_eq_none (by omega)]; simp
        omega
      rw [hmod]

/-- `writeCLLengths` preserves `BitWriter.wf`. -/
private theorem writeCLLengths_go_wf (bw : BitWriter) (clLens : List Nat)
    (numCodeLen i : Nat) (hwf : bw.wf) :
    (writeDynamicHeader.writeCLLengths bw clLens numCodeLen i).wf := by
  suffices ∀ k, k = numCodeLen - i →
      (writeDynamicHeader.writeCLLengths bw clLens numCodeLen i).wf by
    exact this _ rfl
  intro k
  induction k generalizing bw i with
  | zero =>
    intro heq
    unfold writeDynamicHeader.writeCLLengths
    simp [show ¬(i < numCodeLen) from by omega]; exact hwf
  | succ n ih =>
    intro heq
    unfold writeDynamicHeader.writeCLLengths
    by_cases hlt : i < numCodeLen
    · rw [if_pos hlt]
      exact ih _ (i + 1)
        (BitWriter.writeBits_wf bw 3 _ hwf (by omega)) (by omega)
    · rw [if_neg hlt]; exact hwf

private theorem writeCLEntries_wf (bw : BitWriter) (clCodes : Array (UInt16 × UInt8))
    (entries : List (Nat × Nat)) (hwf : bw.wf)
    (hlen : ∀ j, j < clCodes.size → clCodes[j]!.2.toNat ≤ 15)
    (hvalid : ∀ p ∈ entries, p.1 < clCodes.size) :
    (writeDynamicHeader.writeCLEntries bw clCodes entries).wf := by
  induction entries generalizing bw with
  | nil => simp [writeDynamicHeader.writeCLEntries]; exact hwf
  | cons entry rest ih =>
    obtain ⟨code, extra⟩ := entry
    have hcode_lt : code < clCodes.size := hvalid ⟨code, extra⟩ (.head _)
    have hvalid_rest : ∀ p ∈ rest, p.1 < clCodes.size :=
      fun p hp => hvalid p (.tail _ hp)
    simp only [writeDynamicHeader.writeCLEntries, array_get!Internal_eq]
    have hlen15 : clCodes[code]!.2.toNat ≤ 15 := hlen code hcode_lt
    have hwf1 := BitWriter.writeHuffCode_wf bw clCodes[code]!.1 clCodes[code]!.2 hwf hlen15
    by_cases h16 : code == 16
    · simp only [h16, ↓reduceIte]
      exact ih _ (BitWriter.writeBits_wf _ 2 _ hwf1 (by omega)) hvalid_rest
    · by_cases h17 : code == 17
      · simp only [h16, h17, ↓reduceIte, Bool.false_eq_true]
        exact ih _ (BitWriter.writeBits_wf _ 3 _ hwf1 (by omega)) hvalid_rest
      · by_cases h18 : code == 18
        · simp only [h16, h17, h18, ↓reduceIte, Bool.false_eq_true]
          exact ih _ (BitWriter.writeBits_wf _ 7 _ hwf1 (by omega)) hvalid_rest
        · simp only [h16, h17, h18, ↓reduceIte, Bool.false_eq_true]
          exact ih _ hwf1 hvalid_rest

/-- `writeCLEntries` produces the same bits as spec `encodeCLEntries`. -/
private theorem writeCLEntries_spec (bw : BitWriter) (clLengths : Array UInt8)
    (clCodes : Array (UInt16 × UInt8))
    (entries : List (Nat × Nat))
    (bits : List Bool) (hwf : bw.wf)
    (hc : clCodes = canonicalCodes clLengths 7)
    (hv : Huffman.Spec.ValidLengths (clLengths.toList.map UInt8.toNat) 7)
    (hext : ∀ p ∈ entries, p.2 < 2 ^ 32)
    (henc : Deflate.Spec.encodeCLEntries
        ((Huffman.Spec.allCodes (clLengths.toList.map UInt8.toNat) 7).map
          fun p => (p.2, p.1))
        entries = some bits) :
    (writeDynamicHeader.writeCLEntries bw clCodes entries).toBits =
    bw.toBits ++ bits := by
  induction entries generalizing bw bits with
  | nil =>
    simp [Deflate.Spec.encodeCLEntries] at henc
    simp [writeDynamicHeader.writeCLEntries, henc]
  | cons entry rest ih =>
    obtain ⟨code, extra⟩ := entry
    simp only [Deflate.Spec.encodeCLEntries] at henc
    cases hencsym : Deflate.Spec.encodeSymbol
        ((Huffman.Spec.allCodes (clLengths.toList.map UInt8.toNat) 7).map
          fun p => (p.2, p.1))
        code with
    | none => simp [hencsym] at henc
    | some cwBits =>
      cases hencrest : Deflate.Spec.encodeCLEntries
          ((Huffman.Spec.allCodes (clLengths.toList.map UInt8.toNat) 7).map
            fun p => (p.2, p.1))
          rest with
      | none => simp [hencsym, hencrest] at henc
      | some restBits =>
        simp [hencsym, hencrest] at henc
        subst henc
        -- Bridge encodeSymbol ↔ canonicalCodes
        have ⟨hcw, hlen⟩ := encodeSymbol_canonicalCodes_eq clLengths 7
          clCodes hc hv (by omega) code cwBits hencsym
        -- Unfold native
        simp only [writeDynamicHeader.writeCLEntries, array_get!Internal_eq]
        -- writeHuffCode correspondence
        have hlen15 : clCodes[code]!.2.toNat ≤ 15 := by omega
        have hwf1 := BitWriter.writeHuffCode_wf bw
          clCodes[code]!.1 clCodes[code]!.2 hwf hlen15
        have hbits1 := BitWriter.writeHuffCode_toBits bw
          clCodes[code]!.1 clCodes[code]!.2 hwf hlen15
        have hext_rest : ∀ p ∈ rest, p.2 < 2 ^ 32 :=
          fun p hp => hext p (List.mem_cons_of_mem _ hp)
        have hextra_bound : extra < 2 ^ 32 := hext (code, extra) List.mem_cons_self
        -- Extra bits
        by_cases h16 : code == 16
        · simp only [h16, ↓reduceIte]
          have hwf2 := BitWriter.writeBits_wf _ 2 extra.toUInt32 hwf1 (by omega)
          have hbits2 := BitWriter.writeBits_toBits _ 2 extra.toUInt32 hwf1 (by omega)
          rw [ih _ _ hwf2 hext_rest hencrest, hbits2, hbits1, hcw]
          simp only [Deflate.Spec.encodeCLExtra, h16, ↓reduceIte]
          simp only [Nat.toUInt32, UInt32.ofNat, UInt32.toNat, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt hextra_bound, List.append_assoc]
        · by_cases h17 : code == 17
          · simp only [h16, h17, ↓reduceIte, Bool.false_eq_true]
            have hwf2 := BitWriter.writeBits_wf _ 3 extra.toUInt32 hwf1 (by omega)
            have hbits2 := BitWriter.writeBits_toBits _ 3 extra.toUInt32 hwf1 (by omega)
            rw [ih _ _ hwf2 hext_rest hencrest, hbits2, hbits1, hcw]
            simp only [Deflate.Spec.encodeCLExtra, h16, h17, ↓reduceIte, Bool.false_eq_true]
            simp only [Nat.toUInt32, UInt32.ofNat, UInt32.toNat, BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt hextra_bound, List.append_assoc]
          · by_cases h18 : code == 18
            · simp only [h16, h17, h18, ↓reduceIte, Bool.false_eq_true]
              have hwf2 := BitWriter.writeBits_wf _ 7 extra.toUInt32 hwf1 (by omega)
              have hbits2 := BitWriter.writeBits_toBits _ 7 extra.toUInt32 hwf1 (by omega)
              rw [ih _ _ hwf2 hext_rest hencrest, hbits2, hbits1, hcw]
              simp only [Deflate.Spec.encodeCLExtra, h16, h17, h18, ↓reduceIte, Bool.false_eq_true]
              simp only [Nat.toUInt32, UInt32.ofNat, UInt32.toNat, BitVec.toNat_ofNat,
                Nat.mod_eq_of_lt hextra_bound, List.append_assoc]
            · simp only [h16, h17, h18, ↓reduceIte, Bool.false_eq_true]
              rw [ih _ _ hwf1 hext_rest hencrest, hbits1, hcw]
              simp only [Deflate.Spec.encodeCLExtra, h16, h17, h18, ↓reduceIte, Bool.false_eq_true,
                List.nil_append, List.append_assoc]

/-- `writeDynamicHeader` produces the same bits as spec `encodeDynamicTrees`,
    given that `encodeDynamicTrees` succeeds. -/
theorem writeDynamicHeader_spec (bw : BitWriter) (litLens distLens : List Nat)
    (headerBits : List Bool) (hwf : bw.wf)
    (hlit_bound : ∀ x ∈ litLens, x ≤ 15)
    (hdist_bound : ∀ x ∈ distLens, x ≤ 15)
    (hlitLen : litLens.length ≥ 257 ∧ litLens.length ≤ 288)
    (hdistLen : distLens.length ≥ 1 ∧ distLens.length ≤ 32)
    (henc : Deflate.Spec.encodeDynamicTrees litLens distLens = some headerBits) :
    (writeDynamicHeader bw litLens distLens).toBits = bw.toBits ++ headerBits := by
  -- Extract shared intermediate computations (same in native and spec)
  let allLens := litLens ++ distLens
  let clEntries := Deflate.Spec.rlEncodeLengths allLens
  let clFreqs := Deflate.Spec.clSymbolFreqs clEntries
  let clFreqPairs := (List.range clFreqs.length).map fun i => (i, clFreqs.getD i 0)
  let clLens := Huffman.Spec.computeCodeLengths clFreqPairs 19 7
  let numCodeLen := Deflate.Spec.computeHCLEN clLens
  -- CL codes: spec vs native
  let clTable := (Huffman.Spec.allCodes clLens 7).map fun (sym, cw) => (cw, sym)
  let clLengthsArr : Array UInt8 := clLens.toArray.map Nat.toUInt8
  let nativeClCodes := canonicalCodes clLengthsArr 7
  -- Extract symbolBits from encodeDynamicTrees
  have henc_cl : ∃ symbolBits, Deflate.Spec.encodeCLEntries clTable clEntries = some symbolBits ∧
      headerBits = Deflate.Spec.writeBitsLSB 5 (litLens.length - 257) ++
        Deflate.Spec.writeBitsLSB 5 (distLens.length - 1) ++
        Deflate.Spec.writeBitsLSB 4 (numCodeLen - 4) ++
        Deflate.Spec.writeCLLengths clLens numCodeLen ++
        symbolBits := by
    unfold Deflate.Spec.encodeDynamicTrees at henc
    simp only [show (litLens.length ≥ 257 ∧ litLens.length ≤ 288) = true from by simp [hlitLen],
               show (distLens.length ≥ 1 ∧ distLens.length ≤ 32) = true from by simp [hdistLen],
               guard, ↓reduceIte, pure, Pure.pure] at henc
    cases hcle : Deflate.Spec.encodeCLEntries clTable clEntries with
    | none => rw [hcle] at henc; simp at henc
    | some sb => rw [hcle] at henc; simp at henc; exact ⟨sb, rfl, henc.symm⟩
  obtain ⟨symbolBits, hcle_eq, hbits_eq⟩ := henc_cl
  subst hbits_eq
  -- Bounds needed throughout
  have hnum_le : numCodeLen ≤ 19 := Deflate.Spec.computeHCLEN_le_nineteen clLens
  have hclLens_bounded : ∀ l ∈ clLens, l ≤ 7 :=
    Huffman.Spec.computeCodeLengths_bounded clFreqPairs 19 7 (by omega)
  -- writeDynamicHeader unfolds to the chain of BitWriter operations
  -- All intermediate let bindings match the proof context, so this is definitional
  show (writeDynamicHeader.writeCLEntries
    (writeDynamicHeader.writeCLLengths
      (bw.writeBits 5 (litLens.length - 257).toUInt32
        |>.writeBits 5 (distLens.length - 1).toUInt32
        |>.writeBits 4 (numCodeLen - 4).toUInt32)
      clLens numCodeLen 0)
    nativeClCodes clEntries).toBits =
    bw.toBits ++ (Deflate.Spec.writeBitsLSB 5 (litLens.length - 257) ++
      Deflate.Spec.writeBitsLSB 5 (distLens.length - 1) ++
      Deflate.Spec.writeBitsLSB 4 (numCodeLen - 4) ++
      Deflate.Spec.writeCLLengths clLens numCodeLen ++
      symbolBits)
  -- Chain BitWriter.writeBits for HLIT (5 bits)
  have hwf1 := BitWriter.writeBits_wf bw 5 (litLens.length - 257).toUInt32 hwf (by omega)
  have h1 := BitWriter.writeBits_toBits bw 5 (litLens.length - 257).toUInt32 hwf (by omega)
  -- Chain BitWriter.writeBits for HDIST (5 bits)
  let bw1 := bw.writeBits 5 (litLens.length - 257).toUInt32
  have hwf2 := BitWriter.writeBits_wf bw1 5 (distLens.length - 1).toUInt32 hwf1 (by omega)
  have h2 := BitWriter.writeBits_toBits bw1 5 (distLens.length - 1).toUInt32 hwf1 (by omega)
  -- Chain BitWriter.writeBits for HCLEN (4 bits)
  let bw2 := bw1.writeBits 5 (distLens.length - 1).toUInt32
  have hwf3 := BitWriter.writeBits_wf bw2 4 (numCodeLen - 4).toUInt32 hwf2 (by omega)
  have h3 := BitWriter.writeBits_toBits bw2 4 (numCodeLen - 4).toUInt32 hwf2 (by omega)
  -- Chain writeCLLengths
  let bw3 := bw2.writeBits 4 (numCodeLen - 4).toUInt32
  have hwf4 := writeCLLengths_go_wf bw3 clLens numCodeLen 0 hwf3
  have h4 := writeCLLengths_go_spec bw3 clLens numCodeLen 0 hwf3 hnum_le hclLens_bounded
  -- Chain writeCLEntries
  let bw4 := writeDynamicHeader.writeCLLengths bw3 clLens numCodeLen 0
  -- CL code lengths roundtrip: clLens = clLengthsArr.toList.map UInt8.toNat
  have hrt : clLens = (clLengthsArr.toList.map UInt8.toNat) := by
    simp only [clLengthsArr, Array.toList_map, List.map_map]; symm
    rw [List.map_congr_left (fun n hn => by
      show UInt8.toNat (Nat.toUInt8 n) = n
      simp only [Nat.toUInt8, UInt8.toNat, UInt8.ofNat, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by have := hclLens_bounded n hn; omega))]
    simp
  -- CL ValidLengths for writeCLEntries_spec
  have hv_cl : Huffman.Spec.ValidLengths (clLengthsArr.toList.map UInt8.toNat) 7 :=
    hrt ▸ Huffman.Spec.computeCodeLengths_valid clFreqPairs 19 7 (by omega) (by omega)
  -- Convert hcle_eq to use clLengthsArr-based table
  have hcle_eq' : Deflate.Spec.encodeCLEntries
      ((Huffman.Spec.allCodes (clLengthsArr.toList.map UInt8.toNat) 7).map
        fun p => (p.2, p.1))
      clEntries = some symbolBits := hrt ▸ hcle_eq
  -- Entry extras are < 2^32
  have hext : ∀ p ∈ clEntries, p.2 < 2 ^ 32 := by
    intro p hp
    have hvalid := Deflate.Spec.rlEncodeLengths_valid allLens (by
      intro x hx; simp only [allLens, List.mem_append] at hx
      cases hx with
      | inl h => exact hlit_bound x h
      | inr h => exact hdist_bound x h) p hp
    rcases hvalid with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> omega
  have h5 := writeCLEntries_spec bw4 clLengthsArr nativeClCodes clEntries symbolBits
    hwf4 rfl hv_cl hext hcle_eq'
  -- Combine all the chains
  rw [h5, h4, h3, h2, h1]
  -- Normalize UInt32 conversions
  simp only [Nat.toUInt32, UInt32.ofNat, UInt32.toNat, BitVec.toNat_ofNat,
    show (litLens.length - 257) % 2 ^ 32 = litLens.length - 257 from
      Nat.mod_eq_of_lt (by omega),
    show (distLens.length - 1) % 2 ^ 32 = distLens.length - 1 from
      Nat.mod_eq_of_lt (by omega),
    show (numCodeLen - 4) % 2 ^ 32 = numCodeLen - 4 from
      Nat.mod_eq_of_lt (by omega)]
  -- writeCLLengths is defined as exactly the flatMap expression
  simp only [Deflate.Spec.writeCLLengths, List.drop_zero, List.append_assoc]

/-- `writeDynamicHeader` preserves `BitWriter.wf`. -/
theorem writeDynamicHeader_wf (bw : BitWriter) (litLens distLens : List Nat)
    (hwf : bw.wf) (hlit_bound : ∀ x ∈ litLens, x ≤ 15) (hdist_bound : ∀ x ∈ distLens, x ≤ 15) :
    (writeDynamicHeader bw litLens distLens).wf := by
  -- Chain wf through writeBits, writeCLLengths, writeCLEntries
  have hwf1 := BitWriter.writeBits_wf bw 5 (litLens.length - 257).toUInt32 hwf (by omega)
  let bw1 := bw.writeBits 5 (litLens.length - 257).toUInt32
  have hwf2 := BitWriter.writeBits_wf bw1 5 (distLens.length - 1).toUInt32 hwf1 (by omega)
  let bw2 := bw1.writeBits 5 (distLens.length - 1).toUInt32
  let allLens := litLens ++ distLens
  let clEntries := Deflate.Spec.rlEncodeLengths allLens
  let clFreqs := Deflate.Spec.clSymbolFreqs clEntries
  let clFreqPairs := (List.range clFreqs.length).map fun i => (i, clFreqs.getD i 0)
  let clLens := Huffman.Spec.computeCodeLengths clFreqPairs 19 7
  let numCodeLen := Deflate.Spec.computeHCLEN clLens
  have hwf3 := BitWriter.writeBits_wf bw2 4 (numCodeLen - 4).toUInt32 hwf2 (by omega)
  let bw3 := bw2.writeBits 4 (numCodeLen - 4).toUInt32
  have hwf4 := writeCLLengths_go_wf bw3 clLens numCodeLen 0 hwf3
  let bw4 := writeDynamicHeader.writeCLLengths bw3 clLens numCodeLen 0
  -- CL code length bound
  let clLengthsArr : Array UInt8 := clLens.toArray.map Nat.toUInt8
  let clCodes := canonicalCodes clLengthsArr 7
  have hcl_bound : ∀ x ∈ clLens, x ≤ 7 :=
    Huffman.Spec.computeCodeLengths_bounded clFreqPairs 19 7 (by omega)
  have hcl_codes_size : clCodes.size = clLengthsArr.size := canonicalCodes_size clLengthsArr 7
  have hcl_arr_size : clLengthsArr.size = clLens.length := by
    simp [clLengthsArr, Array.size_map, List.size_toArray]
  have hcl_len : clLens.length = 19 := Huffman.Spec.computeCodeLengths_length clFreqPairs 19 7
  have hlengths_le : ∀ j, j < clLengthsArr.size → clLengthsArr[j]!.toNat ≤ 7 := by
    intro k hk
    rw [getElem!_pos clLengthsArr k hk]
    simp only [clLengthsArr, Array.getElem_map]
    have hk' : k < clLens.length := by rw [← hcl_arr_size]; exact hk
    have hle := hcl_bound _ (List.getElem_mem hk')
    simp only [Nat.toUInt8, UInt8.toNat, UInt8.ofNat, BitVec.toNat_ofNat]
    exact Nat.le_trans (Nat.mod_le _ _) hle
  have hcl_snd : ∀ j, j < clCodes.size → clCodes[j]!.2.toNat ≤ 15 := by
    intro j hj
    have : clCodes[j]!.2.toNat ≤ 7 := canonicalCodes_snd_le' clLengthsArr 7 7 hlengths_le j hj
    omega
  have hentry_valid : ∀ p ∈ clEntries, p.1 < clCodes.size := by
    intro p hp
    have hv := Deflate.Spec.rlEncodeLengths_valid allLens (by
      intro x hx; simp only [allLens, List.mem_append] at hx
      cases hx with | inl h => exact hlit_bound x h | inr h => exact hdist_bound x h) p hp
    rw [hcl_codes_size, hcl_arr_size, hcl_len]
    rcases hv with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  exact writeCLEntries_wf bw4 clCodes clEntries hwf4 hcl_snd hentry_valid

end Zip.Native.Deflate
