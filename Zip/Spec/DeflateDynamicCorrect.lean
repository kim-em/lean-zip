import Zip.Spec.DeflateFixedCorrect
import Zip.Spec.DeflateEncodeDynamicProps

/-!
# Native DEFLATE Dynamic Huffman Correctness

This file proves the correspondence between the native `emitTokensWithCodes`
(dynamic Huffman compressor) and the spec-level `encodeSymbols`, mirroring
`emitTokens_spec` from `DeflateFixedCorrect.lean` but generalized to
arbitrary `canonicalCodes`-produced tables.

## Key results

- `encodeSymbol_canonicalCodes_eq`: generalized bridge from `encodeSymbol` to
  `canonicalCodes` entries (replaces `encodeSymbol_litTable_eq` / `distTable_eq`)
- `emitTokensWithCodes_spec`: `emitTokensWithCodes` produces the same bits as
  spec `encodeSymbols` for dynamic Huffman codes
-/

namespace Zip.Native.Deflate

/-! ## encodeSymbol ↔ canonicalCodes bridge -/

/-- If `encodeSymbol` on the flipped `allCodes` table returns `cw` for symbol `s`,
    and the codes array was produced by `canonicalCodes` from the same lengths,
    then `cw` equals `natToBits` of the `canonicalCodes` entry. -/
theorem encodeSymbol_canonicalCodes_eq (lengths : Array UInt8) (maxBits : Nat)
    (codes : Array (UInt16 × UInt8))
    (hc : codes = canonicalCodes lengths maxBits)
    (hv : Huffman.Spec.ValidLengths (lengths.toList.map UInt8.toNat) maxBits)
    (hmb : maxBits < 16)
    (s : Nat) (cw : List Bool)
    (henc : Deflate.Spec.encodeSymbol
      ((Huffman.Spec.allCodes (lengths.toList.map UInt8.toNat) maxBits).map
        fun p => (p.2, p.1))
      s = some cw) :
    cw = Huffman.Spec.natToBits codes[s]!.1.toNat codes[s]!.2.toNat ∧
    codes[s]!.2.toNat ≤ maxBits := by
  -- encodeSymbol_mem → (cw, s) ∈ table → (s, cw) ∈ allCodes
  have hmem := Deflate.Spec.encodeSymbol_mem _ s cw henc
  have hmem' : (s, cw) ∈ Huffman.Spec.allCodes (lengths.toList.map UInt8.toNat) maxBits := by
    simp only [List.mem_map] at hmem
    obtain ⟨⟨s', cw'⟩, hmem, heq⟩ := hmem
    simp only [Prod.mk.injEq] at heq
    exact heq.1 ▸ heq.2 ▸ hmem
  rw [Huffman.Spec.allCodes_mem_iff] at hmem'
  obtain ⟨hs_len, hcf⟩ := hmem'
  -- Get canonicalCodes_correct_pos
  have hs_arr : s < lengths.size := by
    simp only [List.length_map, Array.length_toList] at hs_len; exact hs_len
  have hs_i : (lengths.toList.map UInt8.toNat)[s] = lengths[s].toNat := by
    simp only [List.getElem_map, Array.getElem_toList]
  have ⟨hne0, hle_mb⟩ := Huffman.Spec.codeFor_len_bounds
    (Huffman.Spec.codeFor_spec hcf).2.1
  have hne0_nat : lengths[s].toNat ≠ 0 := hs_i ▸ hne0
  have hpos : lengths[s] > 0 := by
    simp only [GT.gt, UInt8.lt_iff_toNat_lt, UInt8.toNat_ofNat]; omega
  obtain ⟨cw', hcf', hcw', hlen'⟩ :=
    Deflate.Correctness.canonicalCodes_correct_pos lengths maxBits hv hmb s hs_arr hpos
  -- Match codewords
  have hcw_eq : cw = cw' := Option.some.inj (hcf.symm.trans hcf')
  subst hcw_eq
  subst hc
  have hlen'_nat : (canonicalCodes lengths maxBits)[s]!.2.toNat = lengths[s].toNat :=
    congrArg UInt8.toNat hlen'
  exact ⟨by rw [hlen'_nat]; exact hcw', by omega⟩

private theorem array_get!Internal_eq [Inhabited α] (a : Array α) (i : Nat) :
    a.get!Internal i = a[i]! := rfl

/-! ## Main emitTokensWithCodes ↔ encodeSymbols correspondence -/

set_option maxRecDepth 2048 in
/-- Generalized loop invariant for `emitTokensWithCodes_spec`. -/
private theorem emitTokensWithCodes_spec_go (bw : BitWriter) (tokens : Array LZ77Token)
    (litLengths distLengths : Array UInt8)
    (litCodes distCodes : Array (UInt16 × UInt8))
    (i : Nat) (bits : List Bool) (hwf : bw.wf)
    (hlc : litCodes = canonicalCodes litLengths)
    (hdc : distCodes = canonicalCodes distLengths)
    (hv_lit : Huffman.Spec.ValidLengths (litLengths.toList.map UInt8.toNat) 15)
    (hv_dist : Huffman.Spec.ValidLengths (distLengths.toList.map UInt8.toNat) 15)
    (henc : Deflate.Spec.encodeSymbols
        (litLengths.toList.map UInt8.toNat) (distLengths.toList.map UInt8.toNat)
        ((tokens.toList.drop i).map LZ77Token.toLZ77Symbol) = some bits) :
    (emitTokensWithCodes bw tokens litCodes distCodes i).toBits =
    bw.toBits ++ bits := by
  suffices ∀ k, k = tokens.size - i →
      (emitTokensWithCodes bw tokens litCodes distCodes i).toBits = bw.toBits ++ bits by
    exact this _ rfl
  intro k
  induction k generalizing bw i bits with
  | zero =>
    intro heq
    have hge : i ≥ tokens.size := by omega
    have hdrop : tokens.toList.drop i = [] := by
      simp [List.drop_eq_nil_iff, Array.length_toList]; omega
    rw [hdrop, List.map_nil] at henc
    simp only [Deflate.Spec.encodeSymbols] at henc
    cases henc
    simp only [emitTokensWithCodes, show ¬(i < tokens.size) from by omega, ↓reduceDIte,
      List.append_nil]
  | succ n ih =>
    intro heq
    have hlt : i < tokens.size := by omega
    have hlt_list : i < tokens.toList.length := by simp; exact hlt
    rw [List.drop_eq_getElem_cons hlt_list, List.map_cons] at henc
    obtain ⟨symBits, restBits, hencsym, hencrest, hbits_eq⟩ :=
      Deflate.encodeSymbols_cons_some _ _ _ _ _ henc
    subst hbits_eq
    have htoList : tokens[i] = tokens.toList[i] := by simp [Array.getElem_toList]
    -- Unfold emitTokensWithCodes one step
    unfold emitTokensWithCodes
    simp only [dif_pos hlt]
    cases htok : tokens[i] with
    | literal b =>
      simp only [array_get!Internal_eq]
      -- Spec side
      have htok_list : tokens.toList[i] = .literal b := by rw [← htoList]; exact htok
      simp only [LZ77Token.toLZ77Symbol, htok_list] at hencsym
      simp only [Deflate.Spec.encodeLitLen] at hencsym
      have ⟨hcw, hlen⟩ := encodeSymbol_canonicalCodes_eq litLengths 15
        litCodes hlc hv_lit (by omega) b.toNat symBits hencsym
      -- BitWriter correspondence + IH
      have hwf' := BitWriter.writeHuffCode_wf bw
        litCodes[b.toNat]!.1 litCodes[b.toNat]!.2 hwf hlen
      have hbits := BitWriter.writeHuffCode_toBits bw
        litCodes[b.toNat]!.1 litCodes[b.toNat]!.2 hwf hlen
      rw [ih _ (i + 1) restBits hwf' hencrest (by omega)]
      rw [hbits, hcw, List.append_assoc]
    | reference len dist =>
      simp only [array_get!Internal_eq]
      -- Spec side
      have htok_list : tokens.toList[i] = .reference len dist := by
        rw [← htoList]; exact htok
      simp only [LZ77Token.toLZ77Symbol, htok_list] at hencsym
      simp only [Deflate.Spec.encodeLitLen] at hencsym
      cases hflc : Deflate.Spec.findLengthCode len with
      | none => simp [hflc] at hencsym
      | some lc =>
        obtain ⟨lidx, lextraN, lextraV⟩ := lc
        cases henclen : Deflate.Spec.encodeSymbol
            ((Huffman.Spec.allCodes (litLengths.toList.map UInt8.toNat) 15).map
              fun p => (p.2, p.1))
            (257 + lidx) with
        | none => simp [hflc, henclen] at hencsym
        | some lenBits =>
          cases hfdc : Deflate.Spec.findDistCode dist with
          | none => simp [hflc, hfdc] at hencsym
          | some dc =>
            obtain ⟨didx, dextraN, dextraV⟩ := dc
            cases hencdist : Deflate.Spec.encodeSymbol
                ((Huffman.Spec.allCodes (distLengths.toList.map UInt8.toNat) 15).map
                  fun p => (p.2, p.1))
                didx with
            | none => simp [hflc, hfdc, hencdist] at hencsym
            | some distBits =>
              simp [hflc, henclen, hfdc, hencdist] at hencsym
              subst hencsym
              -- Bridge lemmas
              have hnflc := Deflate.findLengthCode_agree len lidx lextraN lextraV hflc
              have hnfdc := Deflate.findDistCode_agree dist didx dextraN dextraV hfdc
              have ⟨hlcw, hllen⟩ := encodeSymbol_canonicalCodes_eq litLengths 15
                litCodes hlc hv_lit (by omega) (257 + lidx) lenBits henclen
              have ⟨hdcw, hdlen⟩ := encodeSymbol_canonicalCodes_eq distLengths 15
                distCodes hdc hv_dist (by omega) didx distBits hencdist
              have hflc_spec := Deflate.Spec.findLengthCode_spec len lidx lextraN lextraV hflc
              have hfdc_spec := Deflate.Spec.findDistCode_spec dist didx dextraN dextraV hfdc
              -- Extra bits bounds
              have lextraN_le : lextraN ≤ 25 := by
                rw [hflc_spec.2.2.1]
                exact Nat.le_trans (Deflate.lengthExtra_le_5 lidx hflc_spec.1) (by omega)
              have dextraN_le : dextraN ≤ 25 := by
                rw [hfdc_spec.2.2.1]
                exact Nat.le_trans (Deflate.distExtra_le_13 didx hfdc_spec.1) (by omega)
              -- Reduce native findLengthCode/findDistCode matches
              simp only [hnflc, hnfdc]
              -- Normalize lidx + 257 → 257 + lidx
              have h257 : lidx + 257 = 257 + lidx := by omega
              rw [h257]
              -- Chain BitWriter correspondence
              let lcode := litCodes[257 + lidx]!.fst
              let llen := litCodes[257 + lidx]!.snd
              let dcode := distCodes[didx]!.fst
              let dlen := distCodes[didx]!.snd
              have hwf1 := BitWriter.writeHuffCode_wf bw lcode llen hwf hllen
              have hbits1 := BitWriter.writeHuffCode_toBits bw lcode llen hwf hllen
              let bw1 := bw.writeHuffCode lcode llen
              have hwf2 := BitWriter.writeBits_wf bw1 lextraN lextraV.toUInt32 hwf1 lextraN_le
              have hbits2 := BitWriter.writeBits_toBits bw1 lextraN lextraV.toUInt32 hwf1 lextraN_le
              let bw2 := bw1.writeBits lextraN lextraV.toUInt32
              have hwf3 := BitWriter.writeHuffCode_wf bw2 dcode dlen hwf2 hdlen
              have hbits3 := BitWriter.writeHuffCode_toBits bw2 dcode dlen hwf2 hdlen
              let bw3 := bw2.writeHuffCode dcode dlen
              have hwf4 := BitWriter.writeBits_wf bw3 dextraN dextraV.toUInt32 hwf3 dextraN_le
              have hbits4 := BitWriter.writeBits_toBits bw3 dextraN dextraV.toUInt32 hwf3 dextraN_le
              -- Apply IH
              rw [ih _ (i + 1) restBits hwf4 hencrest (by omega)]
              rw [hbits4, hbits3, hbits2, hbits1]
              rw [hlcw, hdcw]
              -- UInt32 faithfulness for extra values
              have hlextraV_small : lextraV < 2 ^ 32 := Nat.lt_of_lt_of_le
                hflc_spec.2.2.2 (Nat.pow_le_pow_right (by omega) (by omega))
              have hdextraV_small : dextraV < 2 ^ 32 := Nat.lt_of_lt_of_le
                hfdc_spec.2.2.2 (Nat.pow_le_pow_right (by omega) (by omega))
              simp only [Nat.toUInt32, UInt32.ofNat, UInt32.toNat, BitVec.toNat_ofNat,
                show lextraV % 2 ^ 32 = lextraV from Nat.mod_eq_of_lt hlextraV_small,
                show dextraV % 2 ^ 32 = dextraV from Nat.mod_eq_of_lt hdextraV_small]
              simp only [List.append_assoc]
              rfl

/-- `emitTokensWithCodes` produces the same bit sequence as spec `encodeSymbols`
    when the code arrays are produced by `canonicalCodes` from valid code lengths. -/
theorem emitTokensWithCodes_spec (bw : BitWriter) (tokens : Array LZ77Token)
    (litLens distLens : List Nat) (litCodes distCodes : Array (UInt16 × UInt8))
    (bits : List Bool) (hwf : bw.wf)
    (hlc : litCodes = canonicalCodes (litLens.toArray.map Nat.toUInt8))
    (hdc : distCodes = canonicalCodes (distLens.toArray.map Nat.toUInt8))
    (hv_lit : Huffman.Spec.ValidLengths litLens 15)
    (hv_dist : Huffman.Spec.ValidLengths distLens 15)
    (henc : Deflate.Spec.encodeSymbols litLens distLens
        (tokens.toList.map LZ77Token.toLZ77Symbol) = some bits) :
    (emitTokensWithCodes bw tokens litCodes distCodes 0).toBits =
    bw.toBits ++ bits := by
  -- Roundtrip: n.toUInt8.toNat = n for all n ∈ litLens/distLens (since all ≤ 15 < 256)
  have hll : litLens = (litLens.toArray.map Nat.toUInt8).toList.map UInt8.toNat := by
    simp only [Array.toList_map, List.map_map]; symm
    rw [List.map_congr_left (fun n hn => by
      show UInt8.toNat (Nat.toUInt8 n) = n
      simp only [Nat.toUInt8, UInt8.toNat, UInt8.ofNat, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by have := hv_lit.1 n hn; omega))]
    simp
  have hdl : distLens = (distLens.toArray.map Nat.toUInt8).toList.map UInt8.toNat := by
    simp only [Array.toList_map, List.map_map]; symm
    rw [List.map_congr_left (fun n hn => by
      show UInt8.toNat (Nat.toUInt8 n) = n
      simp only [Nat.toUInt8, UInt8.toNat, UInt8.ofNat, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by have := hv_dist.1 n hn; omega))]
    simp
  rw [hll, hdl] at henc
  have hv_lit' : Huffman.Spec.ValidLengths
      ((litLens.toArray.map Nat.toUInt8).toList.map UInt8.toNat) 15 := hll ▸ hv_lit
  have hv_dist' : Huffman.Spec.ValidLengths
      ((distLens.toArray.map Nat.toUInt8).toList.map UInt8.toNat) 15 := hdl ▸ hv_dist
  exact emitTokensWithCodes_spec_go bw tokens
    (litLens.toArray.map Nat.toUInt8) (distLens.toArray.map Nat.toUInt8)
    litCodes distCodes 0 bits hwf hlc hdc hv_lit' hv_dist'
    (by rwa [List.drop_zero])

set_option maxRecDepth 2048 in
/-- `emitTokensWithCodes` preserves `BitWriter.wf`. -/
private theorem emitTokensWithCodes_wf_go (bw : BitWriter) (tokens : Array LZ77Token)
    (litCodes distCodes : Array (UInt16 × UInt8))
    (i : Nat) (hwf : bw.wf)
    (hlit_size : litCodes.size ≥ 286)
    (hdist_size : distCodes.size ≥ 30)
    (hlit_le : ∀ j, j < litCodes.size → litCodes[j]!.2.toNat ≤ 15)
    (hdist_le : ∀ j, j < distCodes.size → distCodes[j]!.2.toNat ≤ 15) :
    (emitTokensWithCodes bw tokens litCodes distCodes i).wf := by
  suffices ∀ k, k = tokens.size - i →
      (emitTokensWithCodes bw tokens litCodes distCodes i).wf by
    exact this _ rfl
  intro k
  induction k generalizing bw i with
  | zero =>
    intro heq
    simp only [emitTokensWithCodes, show ¬(i < tokens.size) from by omega, ↓reduceDIte]
    exact hwf
  | succ n ih =>
    intro heq
    have hlt : i < tokens.size := by omega
    unfold emitTokensWithCodes
    simp only [dif_pos hlt]
    match htok : tokens[i] with
    | .literal b =>
      simp only [htok]
      have hb_lt : b.toNat < litCodes.size := by have := UInt8.toNat_lt b; omega
      have hb_le : litCodes[b.toNat]!.2.toNat ≤ 15 := hlit_le b.toNat hb_lt
      exact ih _ (i + 1)
        (BitWriter.writeHuffCode_wf bw _ _ hwf hb_le) (by omega)
    | .reference len dist =>
      simp only [htok]
      match hflc : findLengthCode len with
      | none =>
        simp only [hflc]
        exact ih _ (i + 1) hwf (by omega)
      | some (idx, extraCount, extraVal) =>
        simp only [hflc]
        have hidx := nativeFindLengthCode_idx_bound len idx extraCount extraVal hflc
        have hsym_lt : idx + 257 < litCodes.size := by omega
        have hlen_code : litCodes[idx + 257]!.2.toNat ≤ 15 := hlit_le (idx + 257) hsym_lt
        have hextraN_le : extraCount ≤ 25 := by
          have := nativeFindLengthCode_extraN_bound len idx extraCount extraVal hflc; omega
        have hwf1 := BitWriter.writeHuffCode_wf bw
          litCodes[idx + 257]!.1 litCodes[idx + 257]!.2 hwf hlen_code
        have hwf2 := BitWriter.writeBits_wf
          (bw.writeHuffCode litCodes[idx + 257]!.1 litCodes[idx + 257]!.2)
          extraCount extraVal hwf1 hextraN_le
        match hfdc : findDistCode dist with
        | none =>
          simp only [hfdc]
          exact ih _ (i + 1) hwf2 (by omega)
        | some (dIdx, dExtraCount, dExtraVal) =>
          simp only [hfdc]
          have hdidx := nativeFindDistCode_idx_bound dist dIdx dExtraCount dExtraVal hfdc
          have hdsym_lt : dIdx < distCodes.size := by omega
          have hdlen_code : distCodes[dIdx]!.2.toNat ≤ 15 := hdist_le dIdx hdsym_lt
          have hdextraN_le : dExtraCount ≤ 25 := by
            have := nativeFindDistCode_extraN_bound dist dIdx dExtraCount dExtraVal hfdc; omega
          have hwf3 := BitWriter.writeHuffCode_wf _
            distCodes[dIdx]!.1 distCodes[dIdx]!.2 hwf2 hdlen_code
          have hwf4 := BitWriter.writeBits_wf _ dExtraCount dExtraVal hwf3 hdextraN_le
          exact ih _ (i + 1) hwf4 (by omega)

theorem emitTokensWithCodes_wf (bw : BitWriter) (tokens : Array LZ77Token)
    (litCodes distCodes : Array (UInt16 × UInt8))
    (hwf : bw.wf)
    (hlit_size : litCodes.size ≥ 286)
    (hdist_size : distCodes.size ≥ 30)
    (hlit_le : ∀ j, j < litCodes.size → litCodes[j]!.2.toNat ≤ 15)
    (hdist_le : ∀ j, j < distCodes.size → distCodes[j]!.2.toNat ≤ 15) :
    (emitTokensWithCodes bw tokens litCodes distCodes 0).wf :=
  emitTokensWithCodes_wf_go bw tokens litCodes distCodes 0 hwf
    hlit_size hdist_size hlit_le hdist_le

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
  have hcl_codes_size : clCodes.size = clLengthsArr.size := canonicalCodes_size' clLengthsArr 7
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

/-! ## tokenFreqs properties -/

private theorem findTableCode_go_idx_bound (baseTable : Array UInt16)
    (extraTable : Array UInt8) (value i idx : Nat) (extraN : Nat) (extraV : UInt32)
    (h : findTableCode.go baseTable extraTable value i = some (idx, extraN, extraV)) :
    idx < baseTable.size := by
  unfold findTableCode.go at h
  split at h
  · split at h
    · simp at h; omega
    · exact findTableCode_go_idx_bound baseTable extraTable value (i + 1) idx extraN extraV h
  · split at h
    · simp at h; omega
    · simp at h
termination_by baseTable.size - i

private theorem native_findLengthCode_idx_bound (len idx : Nat) (extraN : Nat) (extraV : UInt32)
    (h : findLengthCode len = some (idx, extraN, extraV)) :
    idx < 29 := by
  have := findTableCode_go_idx_bound Inflate.lengthBase Inflate.lengthExtra len 0 idx extraN extraV h
  simp [Inflate.lengthBase] at this
  exact this

private theorem native_findDistCode_code_bound (dist dCode : Nat) (dExtraN : Nat) (dExtraV : UInt32)
    (h : findDistCode dist = some (dCode, dExtraN, dExtraV)) :
    dCode < 30 := by
  have := findTableCode_go_idx_bound Inflate.distBase Inflate.distExtra dist 0 dCode dExtraN dExtraV h
  simp [Inflate.distBase] at this
  exact this

/-- `tokenFreqs.go` preserves array sizes. -/
private theorem tokenFreqs_go_sizes (tokens : Array LZ77Token)
    (litFreqs distFreqs : Array Nat) (i : Nat)
    (hlit : litFreqs.size = 286) (hdist : distFreqs.size = 30) :
    (tokenFreqs.go tokens litFreqs distFreqs i).1.size = 286 ∧
    (tokenFreqs.go tokens litFreqs distFreqs i).2.size = 30 := by
  unfold tokenFreqs.go
  split
  · rename_i h
    match htok : tokens[i] with
    | .literal b =>
      simp only [htok]
      apply tokenFreqs_go_sizes
      · simp [Array.size_set]; omega
      · exact hdist
    | .reference len dist =>
      simp only [htok]
      apply tokenFreqs_go_sizes
      · cases findLengthCode len with
        | none => exact hlit
        | some p => obtain ⟨idx, _, _⟩ := p; simp [Array.size_set]; omega
      · cases findDistCode dist with
        | none => exact hdist
        | some p => obtain ⟨dIdx, _, _⟩ := p; simp [Array.size_set]; omega
  · exact ⟨hlit, hdist⟩
termination_by tokens.size - i

/-- `tokenFreqs` produces arrays of size 286 and 30. -/
private theorem tokenFreqs_sizes (tokens : Array LZ77Token) :
    (tokenFreqs tokens).1.size = 286 ∧ (tokenFreqs tokens).2.size = 30 := by
  simp only [tokenFreqs]
  apply tokenFreqs_go_sizes
  · simp [Array.size_set]
  · simp

/-- `tokenFreqs.go` only increases frequency values. -/
private theorem tokenFreqs_go_mono (tokens : Array LZ77Token)
    (litFreqs distFreqs : Array Nat) (i idx : Nat)
    (hlit : litFreqs.size = 286) (hdist : distFreqs.size = 30) :
    (idx < 286 → litFreqs[idx]! ≤ (tokenFreqs.go tokens litFreqs distFreqs i).1[idx]!) ∧
    (idx < 30 → distFreqs[idx]! ≤ (tokenFreqs.go tokens litFreqs distFreqs i).2[idx]!) := by
  unfold tokenFreqs.go
  split
  · rename_i h
    match htok : tokens[i] with
    | .literal b =>
      simp only [htok]
      have ih := tokenFreqs_go_mono tokens
        (litFreqs.set! b.toNat (litFreqs[b.toNat]! + 1)) distFreqs (i + 1) idx
        (by simp [Array.size_set]; omega) hdist
      constructor
      · intro hidx
        have hle : litFreqs[idx]! ≤ (litFreqs.set! b.toNat (litFreqs[b.toNat]! + 1))[idx]! := by
          by_cases heq : b.toNat = idx
          · subst heq; rw [Array.getElem!_set!_self litFreqs _ _ (by omega)]; omega
          · rw [Array.getElem!_set!_ne litFreqs _ _ _ heq]; omega
        exact Nat.le_trans hle (ih.1 hidx)
      · exact ih.2
    | .reference length distance =>
      simp only [htok]
      -- Split on findLengthCode and findDistCode
      constructor
      · intro hidx
        cases hflc : findLengthCode length with
        | none =>
          cases hfdc : findDistCode distance with
          | none =>
            have ih := tokenFreqs_go_mono tokens litFreqs distFreqs (i + 1) idx hlit hdist
            exact ih.1 hidx
          | some p =>
            obtain ⟨dIdx, dN, dV⟩ := p
            have ih := tokenFreqs_go_mono tokens litFreqs
              (distFreqs.set! dIdx (distFreqs[dIdx]! + 1)) (i + 1) idx
              hlit (by simp [Array.size_set]; omega)
            exact ih.1 hidx
        | some p =>
          obtain ⟨lIdx, lN, lV⟩ := p
          cases hfdc : findDistCode distance with
          | none =>
            have ih := tokenFreqs_go_mono tokens
              (litFreqs.set! (lIdx + 257) (litFreqs[lIdx + 257]! + 1)) distFreqs (i + 1) idx
              (by simp [Array.size_set]; omega) hdist
            have hle : litFreqs[idx]! ≤ (litFreqs.set! (lIdx + 257) (litFreqs[lIdx + 257]! + 1))[idx]! := by
              by_cases heq : lIdx + 257 = idx
              · subst heq; rw [Array.getElem!_set!_self litFreqs _ _ (by omega)]; omega
              · rw [Array.getElem!_set!_ne litFreqs _ _ _ heq]; omega
            exact Nat.le_trans hle (ih.1 hidx)
          | some q =>
            obtain ⟨dIdx, dN, dV⟩ := q
            have ih := tokenFreqs_go_mono tokens
              (litFreqs.set! (lIdx + 257) (litFreqs[lIdx + 257]! + 1))
              (distFreqs.set! dIdx (distFreqs[dIdx]! + 1)) (i + 1) idx
              (by simp [Array.size_set]; omega) (by simp [Array.size_set]; omega)
            have hle : litFreqs[idx]! ≤ (litFreqs.set! (lIdx + 257) (litFreqs[lIdx + 257]! + 1))[idx]! := by
              by_cases heq : lIdx + 257 = idx
              · subst heq; rw [Array.getElem!_set!_self litFreqs _ _ (by omega)]; omega
              · rw [Array.getElem!_set!_ne litFreqs _ _ _ heq]; omega
            exact Nat.le_trans hle (ih.1 hidx)
      · intro hidx
        cases hflc : findLengthCode length with
        | none =>
          cases hfdc : findDistCode distance with
          | none =>
            have ih := tokenFreqs_go_mono tokens litFreqs distFreqs (i + 1) idx hlit hdist
            exact ih.2 hidx
          | some p =>
            obtain ⟨dIdx, dN, dV⟩ := p
            have ih := tokenFreqs_go_mono tokens litFreqs
              (distFreqs.set! dIdx (distFreqs[dIdx]! + 1)) (i + 1) idx
              hlit (by simp [Array.size_set]; omega)
            have hle : distFreqs[idx]! ≤ (distFreqs.set! dIdx (distFreqs[dIdx]! + 1))[idx]! := by
              by_cases heq : dIdx = idx
              · subst heq; rw [Array.getElem!_set!_self distFreqs _ _ (by omega)]; omega
              · rw [Array.getElem!_set!_ne distFreqs _ _ _ heq]; omega
            exact Nat.le_trans hle (ih.2 hidx)
        | some p =>
          obtain ⟨lIdx, lN, lV⟩ := p
          cases hfdc : findDistCode distance with
          | none =>
            have ih := tokenFreqs_go_mono tokens
              (litFreqs.set! (lIdx + 257) (litFreqs[lIdx + 257]! + 1)) distFreqs (i + 1) idx
              (by simp [Array.size_set]; omega) hdist
            exact ih.2 hidx
          | some q =>
            obtain ⟨dIdx, dN, dV⟩ := q
            have ih := tokenFreqs_go_mono tokens
              (litFreqs.set! (lIdx + 257) (litFreqs[lIdx + 257]! + 1))
              (distFreqs.set! dIdx (distFreqs[dIdx]! + 1)) (i + 1) idx
              (by simp [Array.size_set]; omega) (by simp [Array.size_set]; omega)
            have hle : distFreqs[idx]! ≤ (distFreqs.set! dIdx (distFreqs[dIdx]! + 1))[idx]! := by
              by_cases heq : dIdx = idx
              · subst heq; rw [Array.getElem!_set!_self distFreqs _ _ (by omega)]; omega
              · rw [Array.getElem!_set!_ne distFreqs _ _ _ heq]; omega
            exact Nat.le_trans hle (ih.2 hidx)
  · exact ⟨fun _ => Nat.le.refl, fun _ => Nat.le.refl⟩
termination_by tokens.size - i

set_option maxRecDepth 1024 in
/-- `tokenFreqs` counts end-of-block (symbol 256) with frequency ≥ 1. -/
private theorem tokenFreqs_eob_pos (tokens : Array LZ77Token) :
    (tokenFreqs tokens).1[256]! ≥ 1 := by
  -- tokenFreqs.go monotonically increases frequency values
  -- Initial lit array has [256]! = 1, so result has [256]! ≥ 1
  have hmono : ((Array.replicate 286 (0 : Nat)).set! 256 1)[256]! ≤
      (tokenFreqs tokens).1[256]! :=
    (tokenFreqs_go_mono tokens _ _ 0 256 (by simp [Array.size_set]) (by simp)).1 (by omega)
  have h256 : ((Array.replicate 286 (0 : Nat)).set! 256 1)[256]! = 1 :=
    Array.getElem!_set!_self _ _ _ (by simp)
  omega

/-- `tokenFreqs.go` produces positive lit frequency for literal `b` at position `j ≥ i`. -/
private theorem tokenFreqs_go_literal_pos (tokens : Array LZ77Token) (b : UInt8)
    (litFreqs distFreqs : Array Nat) (i j : Nat)
    (hlit : litFreqs.size = 286) (hdist : distFreqs.size = 30)
    (hj : j ≥ i) (hjlt : j < tokens.size) (htok : tokens[j] = .literal b) :
    (tokenFreqs.go tokens litFreqs distFreqs i).1[b.toNat]! ≥ 1 := by
  unfold tokenFreqs.go
  split
  · rename_i h
    match htoki : tokens[i] with
    | .literal b' =>
      simp only [htoki]
      by_cases hij : i = j
      · -- This is the token we're looking for
        subst hij; simp only [htoki] at htok
        have hbeq : b' = b := LZ77Token.literal.inj htok
        rw [hbeq]
        -- After set, litFreqs[b.toNat]! ≥ 1
        have hle := (tokenFreqs_go_mono tokens
          (litFreqs.set! b.toNat (litFreqs[b.toNat]! + 1)) distFreqs (i + 1) b.toNat
          (by simp [Array.size_set]; omega) hdist).1 (by have := UInt8.toNat_lt b; omega)
        have hblt := UInt8.toNat_lt b
        have hset : (litFreqs.set! b.toNat (litFreqs[b.toNat]! + 1))[b.toNat]! ≥ 1 := by
          rw [Array.getElem!_set!_self litFreqs _ _ (by omega)]; omega
        omega
      · -- Not this token yet, recurse
        exact tokenFreqs_go_literal_pos tokens b
          (litFreqs.set! b'.toNat (litFreqs[b'.toNat]! + 1)) distFreqs (i + 1) j
          (by simp [Array.size_set]; omega) hdist (by omega) hjlt htok
    | .reference len' dist' =>
      simp only [htoki]
      have hij : i ≠ j := by intro heq; subst heq; rw [htoki] at htok; simp at htok
      exact tokenFreqs_go_literal_pos tokens b _ _ (i + 1) j
        (by cases findLengthCode len' with
          | none => exact hlit
          | some p => obtain ⟨idx, _, _⟩ := p; simp [Array.size_set]; omega)
        (by cases findDistCode dist' with
          | none => exact hdist
          | some p => obtain ⟨dIdx, _, _⟩ := p; simp [Array.size_set]; omega)
        (by omega) hjlt htok
  · omega
termination_by tokens.size - i

/-- `tokenFreqs` counts literal byte `b` if it appears in `tokens`. -/
private theorem tokenFreqs_literal_pos (tokens : Array LZ77Token) (b : UInt8)
    (hmem : LZ77Token.literal b ∈ tokens.toList) :
    (tokenFreqs tokens).1[b.toNat]! ≥ 1 := by
  have ⟨j, hjlt, htok⟩ := List.mem_iff_getElem.mp hmem
  simp only [Array.length_toList] at hjlt
  have htok' : tokens[j] = .literal b := by
    simp only [Array.getElem_toList] at htok; exact htok
  exact tokenFreqs_go_literal_pos tokens b _ _ 0 j
    (by simp [Array.size_set]) (by simp) (by omega) hjlt htok'

/-- `tokenFreqs.go` produces positive lit frequency for length code from ref at position `j ≥ i`. -/
private theorem tokenFreqs_go_lengthCode_pos (tokens : Array LZ77Token)
    (len dist : Nat) (idx extraN : Nat) (extraV : UInt32)
    (litFreqs distFreqs : Array Nat) (i j : Nat)
    (hlit : litFreqs.size = 286) (hdist : distFreqs.size = 30)
    (hj : j ≥ i) (hjlt : j < tokens.size)
    (htok : tokens[j] = .reference len dist)
    (hflc : findLengthCode len = some (idx, extraN, extraV)) :
    (tokenFreqs.go tokens litFreqs distFreqs i).1[257 + idx]! ≥ 1 := by
  unfold tokenFreqs.go
  split
  · rename_i h
    match htoki : tokens[i] with
    | .literal b' =>
      simp only [htoki]
      have hij : i ≠ j := by intro heq; subst heq; rw [htoki] at htok; simp at htok
      exact tokenFreqs_go_lengthCode_pos tokens len dist idx extraN extraV
        (litFreqs.set! b'.toNat (litFreqs[b'.toNat]! + 1)) distFreqs (i + 1) j
        (by simp [Array.size_set]; omega) hdist (by omega) hjlt htok hflc
    | .reference len' dist' =>
      simp only [htoki]
      by_cases hij : i = j
      · -- This is the token — i = j
        subst hij
        have heq : LZ77Token.reference len' dist' = LZ77Token.reference len dist :=
          htoki.symm.trans htok
        have hlen_eq : len' = len := (LZ77Token.reference.inj heq).1
        have hdist_eq : dist' = dist := (LZ77Token.reference.inj heq).2
        -- The goal talks about findLengthCode len' and findDistCode dist' (from the match)
        simp only [hlen_eq, hdist_eq, hflc]
        have hidx := native_findLengthCode_idx_bound _ idx extraN extraV hflc
        -- After set, litFreqs[257+idx]! ≥ 1
        have hle := (tokenFreqs_go_mono tokens
          (litFreqs.set! (idx + 257) (litFreqs[idx + 257]! + 1))
          (match findDistCode dist with
           | some (dIdx, _, _) => distFreqs.set! dIdx (distFreqs[dIdx]! + 1)
           | none => distFreqs) (i + 1) (257 + idx)
          (by simp [Array.size_set]; omega)
          (by cases findDistCode dist with
            | none => exact hdist
            | some p => obtain ⟨dIdx, _, _⟩ := p; simp [Array.size_set]; omega)).1
          (by omega)
        have hset : (litFreqs.set! (idx + 257) (litFreqs[idx + 257]! + 1))[257 + idx]! ≥ 1 := by
          rw [show idx + 257 = 257 + idx from by omega]
          rw [Array.getElem!_set!_self litFreqs _ _ (by omega)]; omega
        exact Nat.le_trans hset hle
      · -- Not this token, recurse
        exact tokenFreqs_go_lengthCode_pos tokens len dist idx extraN extraV _ _ (i + 1) j
          (by cases findLengthCode len' with
            | none => exact hlit
            | some p => obtain ⟨lIdx, _, _⟩ := p; simp [Array.size_set]; omega)
          (by cases findDistCode dist' with
            | none => exact hdist
            | some p => obtain ⟨dIdx, _, _⟩ := p; simp [Array.size_set]; omega)
          (by omega) hjlt htok hflc
  · omega
termination_by tokens.size - i

/-- `tokenFreqs` counts length code `idx+257` if `.reference len dist` appears
    in `tokens` and `findLengthCode len = some (idx, ...)`. -/
private theorem tokenFreqs_lengthCode_pos (tokens : Array LZ77Token)
    (len dist : Nat) (idx extraN : Nat) (extraV : UInt32)
    (hmem : LZ77Token.reference len dist ∈ tokens.toList)
    (hflc : findLengthCode len = some (idx, extraN, extraV)) :
    (tokenFreqs tokens).1[257 + idx]! ≥ 1 := by
  have ⟨j, hjlt, htok⟩ := List.mem_iff_getElem.mp hmem
  simp only [Array.length_toList] at hjlt
  have htok' : tokens[j] = .reference len dist := by
    simp only [Array.getElem_toList] at htok; exact htok
  exact tokenFreqs_go_lengthCode_pos tokens len dist idx extraN extraV _ _ 0 j
    (by simp [Array.size_set]) (by simp) (by omega) hjlt htok' hflc

/-- `tokenFreqs.go` produces positive dist frequency for dist code from ref at position `j ≥ i`. -/
private theorem tokenFreqs_go_distCode_pos (tokens : Array LZ77Token)
    (len dist : Nat) (dCode dExtraN : Nat) (dExtraV : UInt32)
    (litFreqs distFreqs : Array Nat) (i j : Nat)
    (hlit : litFreqs.size = 286) (hdist : distFreqs.size = 30)
    (hj : j ≥ i) (hjlt : j < tokens.size)
    (htok : tokens[j] = .reference len dist)
    (hfdc : findDistCode dist = some (dCode, dExtraN, dExtraV)) :
    (tokenFreqs.go tokens litFreqs distFreqs i).2[dCode]! ≥ 1 := by
  unfold tokenFreqs.go
  split
  · rename_i h
    match htoki : tokens[i] with
    | .literal b' =>
      simp only [htoki]
      have hij : i ≠ j := by intro heq; subst heq; rw [htoki] at htok; simp at htok
      exact tokenFreqs_go_distCode_pos tokens len dist dCode dExtraN dExtraV
        (litFreqs.set! b'.toNat (litFreqs[b'.toNat]! + 1)) distFreqs (i + 1) j
        (by simp [Array.size_set]; omega) hdist (by omega) hjlt htok hfdc
    | .reference len' dist' =>
      simp only [htoki]
      by_cases hij : i = j
      · -- This is the token — i = j
        subst hij
        have heq : LZ77Token.reference len' dist' = LZ77Token.reference len dist :=
          htoki.symm.trans htok
        have hlen_eq : len' = len := (LZ77Token.reference.inj heq).1
        have hdist_eq : dist' = dist := (LZ77Token.reference.inj heq).2
        simp only [hlen_eq, hdist_eq, hfdc]
        have hdcode := native_findDistCode_code_bound _ dCode dExtraN dExtraV hfdc
        -- After set, distFreqs[dCode]! ≥ 1
        have hle := (tokenFreqs_go_mono tokens
          (match findLengthCode len with
           | some (lIdx, _, _) => litFreqs.set! (lIdx + 257) (litFreqs[lIdx + 257]! + 1)
           | none => litFreqs)
          (distFreqs.set! dCode (distFreqs[dCode]! + 1)) (i + 1) dCode
          (by cases findLengthCode len with
            | none => exact hlit
            | some p => obtain ⟨lIdx, _, _⟩ := p; simp [Array.size_set]; omega)
          (by simp [Array.size_set]; omega)).2
          (by omega)
        have hset : (distFreqs.set! dCode (distFreqs[dCode]! + 1))[dCode]! ≥ 1 := by
          rw [Array.getElem!_set!_self distFreqs _ _ (by omega)]; omega
        exact Nat.le_trans hset hle
      · -- Not this token, recurse
        exact tokenFreqs_go_distCode_pos tokens len dist dCode dExtraN dExtraV _ _ (i + 1) j
          (by cases findLengthCode len' with
            | none => exact hlit
            | some p => obtain ⟨lIdx, _, _⟩ := p; simp [Array.size_set]; omega)
          (by cases findDistCode dist' with
            | none => exact hdist
            | some p => obtain ⟨dIdx, _, _⟩ := p; simp [Array.size_set]; omega)
          (by omega) hjlt htok hfdc
  · omega
termination_by tokens.size - i

/-- `tokenFreqs` counts distance code `dCode` if `.reference len dist` appears
    in `tokens` and `findDistCode dist = some (dCode, ...)`. -/
private theorem tokenFreqs_distCode_pos (tokens : Array LZ77Token)
    (len dist : Nat) (dCode dExtraN : Nat) (dExtraV : UInt32)
    (hmem : LZ77Token.reference len dist ∈ tokens.toList)
    (hfdc : findDistCode dist = some (dCode, dExtraN, dExtraV)) :
    (tokenFreqs tokens).2[dCode]! ≥ 1 := by
  have ⟨j, hjlt, htok⟩ := List.mem_iff_getElem.mp hmem
  simp only [Array.length_toList] at hjlt
  have htok' : tokens[j] = .reference len dist := by
    simp only [Array.getElem_toList] at htok; exact htok
  exact tokenFreqs_go_distCode_pos tokens len dist dCode dExtraN dExtraV _ _ 0 j
    (by simp [Array.size_set]) (by simp) (by omega) hjlt htok' hfdc

/-- `deflateDynamic` produces a bytestream whose bits correspond to the
    spec-level dynamic Huffman encoding, plus padding to byte alignment. -/
theorem deflateDynamic_spec (data : ByteArray) :
    ∃ (litLens distLens : List Nat) (headerBits symBits : List Bool),
      Huffman.Spec.ValidLengths litLens 15 ∧
      Huffman.Spec.ValidLengths distLens 15 ∧
      litLens.length ≥ 257 ∧ litLens.length ≤ 288 ∧
      distLens.length ≥ 1 ∧ distLens.length ≤ 32 ∧
      (∀ x ∈ litLens, x ≤ 15) ∧ (∀ x ∈ distLens, x ≤ 15) ∧
      Deflate.Spec.encodeDynamicTrees litLens distLens = some headerBits ∧
      Deflate.Spec.encodeSymbols litLens distLens
        (tokensToSymbols (lz77Greedy data 32768)) = some symBits ∧
      Deflate.Spec.bytesToBits (deflateDynamic data) =
        [true, false, true] ++ headerBits ++ symBits ++
        List.replicate
          ((8 - ([true, false, true] ++ headerBits ++ symBits).length % 8) % 8)
          false := by
  -- Extract the intermediate values from deflateDynamic
  let tokens := lz77Greedy data 32768
  let litFreqs := (tokenFreqs tokens).1
  let distFreqs := (tokenFreqs tokens).2
  let litFreqPairs := (List.range litFreqs.size).map fun i => (i, litFreqs[i]!)
  let distFreqPairs := (List.range distFreqs.size).map fun i => (i, distFreqs[i]!)
  let litLens := Huffman.Spec.computeCodeLengths litFreqPairs 286 15
  let distLens₀ := Huffman.Spec.computeCodeLengths distFreqPairs 30 15
  let distLens := if distLens₀.all (fun x => x == 0) then distLens₀.set 0 1 else distLens₀
  -- Properties of computeCodeLengths
  have hlit_len : litLens.length = 286 :=
    Huffman.Spec.computeCodeLengths_length litFreqPairs 286 15
  have hdist₀_len : distLens₀.length = 30 :=
    Huffman.Spec.computeCodeLengths_length distFreqPairs 30 15
  have hlit_valid : Huffman.Spec.ValidLengths litLens 15 :=
    Huffman.Spec.computeCodeLengths_valid litFreqPairs 286 15 (by omega) (by omega)
  have hlit_bound : ∀ x ∈ litLens, x ≤ 15 :=
    Huffman.Spec.computeCodeLengths_bounded litFreqPairs 286 15 (by omega)
  have hdist₀_valid : Huffman.Spec.ValidLengths distLens₀ 15 :=
    Huffman.Spec.computeCodeLengths_valid distFreqPairs 30 15 (by omega) (by omega)
  have hdist₀_bound : ∀ x ∈ distLens₀, x ≤ 15 :=
    Huffman.Spec.computeCodeLengths_bounded distFreqPairs 30 15 (by omega)
  -- distLens properties (with the fixup)
  have hdist_len : distLens.length = 30 := by
    simp only [distLens]; split
    · rw [List.length_set]; exact hdist₀_len
    · exact hdist₀_len
  have hdist_bound : ∀ x ∈ distLens, x ≤ 15 := by
    intro x hx
    simp only [distLens] at hx; split at hx
    · -- distLens₀.set 0 1
      rw [List.mem_iff_getElem] at hx
      obtain ⟨i, hi, hxi⟩ := hx
      rw [List.length_set] at hi
      by_cases h0 : i = 0
      · subst h0; simp at hxi; omega
      · have hne : ¬(0 = i) := fun h => h0 (h.symm)
        simp [hne] at hxi
        exact hxi ▸ hdist₀_bound _ (List.getElem_mem ..)
    · exact hdist₀_bound x hx
  have hdist_valid : Huffman.Spec.ValidLengths distLens 15 := by
    by_cases hall0 : (distLens₀.all (fun x => x == 0)) = true
    · -- When all entries are 0, setting index 0 to 1 gives ValidLengths
      have hdl : distLens = distLens₀.set 0 1 := by
        simp only [distLens, hall0, ↓reduceIte]
      have hall : ∀ x ∈ distLens₀, x = 0 := by
        intro x hx
        have := List.all_eq_true.mp hall0 x hx
        simp [beq_iff_eq] at this; exact this
      have hrepl : distLens₀ = List.replicate 30 0 := by
        rw [← hdist₀_len]; exact List.eq_replicate_iff.mpr ⟨rfl, hall⟩
      rw [hdl, hrepl]
      constructor
      · intro l hl
        rw [List.mem_iff_getElem] at hl
        obtain ⟨i, hi, hli⟩ := hl
        rw [List.length_set, List.length_replicate] at hi
        by_cases h0 : i = 0
        · subst h0; simp at hli; omega
        · have hne : ¬(0 = i) := fun h => h0 h.symm
          rw [List.getElem_set] at hli
          simp only [hne, ↓reduceIte, List.getElem_replicate] at hli
          omega
      · -- Kraft sum for [1, 0, 0, ..., 0] with 30 entries
        -- filter gives [1], fold gives 2^14 ≤ 2^15
        decide
    · have hdl : distLens = distLens₀ := by
        simp only [distLens, hall0, Bool.false_eq_true, ↓reduceIte]
      rw [hdl]; exact hdist₀_valid
  -- encodeDynamicTrees succeeds
  have henc_trees_some : (Deflate.Spec.encodeDynamicTrees litLens distLens).isSome = true := by
    -- encodeDynamicTrees only fails at the encodeCLEntries step (guards pass)
    simp only [Deflate.Spec.encodeDynamicTrees]
    simp only [guard, show litLens.length ≥ 257 ∧ litLens.length ≤ 288 from ⟨by omega, by omega⟩,
      show distLens.length ≥ 1 ∧ distLens.length ≤ 32 from ⟨by omega, by omega⟩,
      pure, Pure.pure, bind, Option.bind]
    -- Set up CL-level abbreviations
    let allLens := litLens ++ distLens
    let clEntries := Deflate.Spec.rlEncodeLengths allLens
    let clFreqs := Deflate.Spec.clSymbolFreqs clEntries
    let clFreqPairs := (List.range clFreqs.length).map fun i => (i, clFreqs.getD i 0)
    let clLens := Huffman.Spec.computeCodeLengths clFreqPairs 19 7
    let clTable := (Huffman.Spec.allCodes clLens 7).map fun (sym, cw) => (cw, sym)
    -- Show encodeCLEntries succeeds
    have hcl_len : clLens.length = 19 := Huffman.Spec.computeCodeLengths_length clFreqPairs 19 7
    have hcl_bound : ∀ x ∈ clLens, x ≤ 7 :=
      Huffman.Spec.computeCodeLengths_bounded clFreqPairs 19 7 (by omega)
    have hcl_freq_len : clFreqs.length = 19 := Deflate.Spec.clSymbolFreqs_length clEntries
    -- Entry validity: all codes ≤ 18 < 19
    have hentry_valid := Deflate.Spec.rlEncodeLengths_valid allLens (by
      intro x hx; simp only [allLens, List.mem_append] at hx
      cases hx with | inl h => exact hlit_bound x h | inr h => exact hdist_bound x h)
    -- For each entry, its code has nonzero CL code length
    have hall : ∀ p ∈ clEntries,
        p.1 < clLens.length ∧ clLens[p.1]! ≠ 0 ∧ clLens[p.1]! ≤ 7 := by
      intro ⟨code, extra⟩ hp
      have hvalid := hentry_valid (code, extra) hp
      have hcode_lt : code < 19 := by rcases hvalid with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> omega
      refine ⟨by omega, ?_, ?_⟩
      · -- code has nonzero frequency
        have hfreq_pos := Deflate.Spec.clSymbolFreqs_pos clEntries code extra hp hcode_lt
        have hfreq_in : ∃ p ∈ clFreqPairs, p.1 = code ∧ p.2 > 0 := by
          refine ⟨(code, clFreqs.getD code 0), ?_, rfl, hfreq_pos⟩
          simp only [clFreqPairs, List.mem_map, List.mem_range]
          exact ⟨code, by omega, rfl⟩
        exact Huffman.Spec.computeCodeLengths_nonzero clFreqPairs 19 7 (by omega)
          code (by omega) hfreq_in
      · have : code < clLens.length := by omega
        rw [getElem!_pos clLens code this]
        exact hcl_bound _ (List.getElem_mem this)
    have hcl_isSome := Deflate.Spec.encodeCLEntries_isSome clLens 7 clEntries hall
    -- The types should match definitionally since clTable = (allCodes clLens 7).map ...
    change (Deflate.Spec.encodeCLEntries
      ((Huffman.Spec.allCodes clLens 7).map fun p => (p.2, p.1))
      clEntries).isSome = true at hcl_isSome
    cases hcl : Deflate.Spec.encodeCLEntries
        ((Huffman.Spec.allCodes clLens 7).map fun p => (p.2, p.1))
        clEntries with
    | none => simp [hcl] at hcl_isSome
    | some _ => simp
  -- encodeSymbols succeeds
  have henc_syms_some : (Deflate.Spec.encodeSymbols litLens distLens
      (tokensToSymbols tokens)).isSome = true := by
    apply Deflate.Spec.encodeSymbols_isSome_of_all
    intro s hs
    simp only [tokensToSymbols, List.mem_append, List.mem_map, List.mem_cons,
      List.mem_nil_iff, or_false] at hs
    -- Helper: litFreqs.size = 286, distFreqs.size = 30
    have hlit_sz : litFreqs.size = 286 := (tokenFreqs_sizes tokens).1
    have hdist_sz : distFreqs.size = 30 := (tokenFreqs_sizes tokens).2
    cases hs with
    | inl hmapped =>
      obtain ⟨t, ht_mem, ht_eq⟩ := hmapped
      have hbounds := lz77Greedy_encodable data 32768 (by omega) (by omega) t ht_mem
      subst ht_eq
      cases t with
      | literal b =>
        -- Need: encodeLitLen litLens distLens (.literal b) succeeds
        simp only [Deflate.Spec.encodeLitLen]
        have hb_lt : b.toNat < litLens.length := by rw [hlit_len]; have := UInt8.toNat_lt b; omega
        have hfreq := tokenFreqs_literal_pos tokens b ht_mem
        have hfreq_pair : ∃ p ∈ litFreqPairs, p.1 = b.toNat ∧ p.2 > 0 :=
          ⟨(b.toNat, litFreqs[b.toNat]!), by
            simp only [litFreqPairs, List.mem_map, List.mem_range]
            exact ⟨b.toNat, by have := UInt8.toNat_lt b; omega, rfl⟩,
            rfl, hfreq⟩
        have hlen_nz := Huffman.Spec.computeCodeLengths_nonzero litFreqPairs 286 15
          (by omega) b.toNat (by have := UInt8.toNat_lt b; omega) hfreq_pair
        have hlen_le : litLens[b.toNat]! ≤ 15 := by
          rw [getElem!_pos litLens b.toNat hb_lt]
          exact hlit_bound _ (List.getElem_mem hb_lt)
        exact Deflate.Spec.encodeSymbol_fixed_isSome litLens 15 b.toNat hb_lt hlen_nz hlen_le
      | reference len dist =>
        -- Need: encodeLitLen litLens distLens (.reference len dist) succeeds
        simp at hbounds
        simp only [Deflate.Spec.encodeLitLen]
        -- findLengthCode succeeds (spec version)
        have hflc_spec := Deflate.Spec.findLengthCode_isSome len hbounds.1 hbounds.2.1
        cases hlc : Deflate.Spec.findLengthCode len with
        | none => simp [hlc] at hflc_spec
        | some p =>
          obtain ⟨idx, extraN, extraV⟩ := p
          have hidx := Deflate.Spec.findLengthCode_idx_bound len idx extraN extraV hlc
          -- Get native findLengthCode for tokenFreqs_lengthCode_pos
          have hflc_native := Zip.Native.Deflate.findLengthCode_agree len idx extraN extraV hlc
          -- encodeSymbol litTable (257 + idx) succeeds
          have hsym : 257 + idx < litLens.length := by rw [hlit_len]; omega
          have hfreq := tokenFreqs_lengthCode_pos tokens len dist idx extraN
            extraV.toUInt32 ht_mem hflc_native
          have hfreq_pair : ∃ p ∈ litFreqPairs, p.1 = (257 + idx) ∧ p.2 > 0 :=
            ⟨(257 + idx, litFreqs[257 + idx]!), by
              simp only [litFreqPairs, List.mem_map, List.mem_range]
              exact ⟨257 + idx, by omega, rfl⟩,
              rfl, hfreq⟩
          have hlen_nz := Huffman.Spec.computeCodeLengths_nonzero litFreqPairs 286 15
            (by omega) (257 + idx) (by omega) hfreq_pair
          have hlen_le' : litLens[257 + idx]! ≤ 15 := by
            rw [getElem!_pos litLens (257 + idx) hsym]
            exact hlit_bound _ (List.getElem_mem hsym)
          have hlit_enc := Deflate.Spec.encodeSymbol_fixed_isSome litLens 15 (257 + idx)
            hsym hlen_nz hlen_le'
          cases hls : Deflate.Spec.encodeSymbol
              ((Huffman.Spec.allCodes litLens).map fun (s, cw) => (cw, s)) (257 + idx) with
          | none => simp [hls] at hlit_enc
          | some lenBits =>
            -- findDistCode succeeds (spec version)
            have hfdc_spec := Deflate.Spec.findDistCode_isSome dist hbounds.2.2.1 hbounds.2.2.2
            cases hdc : Deflate.Spec.findDistCode dist with
            | none => simp [hdc] at hfdc_spec
            | some q =>
              obtain ⟨dCode, dExtraN, dExtraV⟩ := q
              have hdcode := Deflate.Spec.findDistCode_code_bound dist dCode dExtraN dExtraV hdc
              -- Get native findDistCode for tokenFreqs_distCode_pos
              have hfdc_native := Zip.Native.Deflate.findDistCode_agree dist dCode dExtraN dExtraV hdc
              -- encodeSymbol distTable dCode succeeds
              -- First: distLens = distLens₀ because there's a reference token
              have hdist_not_all_zero : ¬(distLens₀.all (fun x => x == 0)) = true := by
                -- There's a reference, so distFreqs has a positive entry
                have hdfreq := tokenFreqs_distCode_pos tokens len dist dCode dExtraN
                  dExtraV.toUInt32 ht_mem hfdc_native
                -- computeCodeLengths gives nonzero for positive freq
                have hdfreq_pair : ∃ p ∈ distFreqPairs, p.1 = dCode ∧ p.2 > 0 :=
                  ⟨(dCode, distFreqs[dCode]!), by
                    simp only [distFreqPairs, List.mem_map, List.mem_range]
                    exact ⟨dCode, by omega, rfl⟩,
                    rfl, hdfreq⟩
                have hdlen_nz := Huffman.Spec.computeCodeLengths_nonzero distFreqPairs 30 15
                  (by omega) dCode (by omega) hdfreq_pair
                -- If all were zero, distLens₀[dCode]! would be 0, contradiction
                intro hall
                have hdc_lt : dCode < distLens₀.length := by omega
                have hmem : distLens₀[dCode] ∈ distLens₀ := List.getElem_mem hdc_lt
                have hzero := List.all_eq_true.mp hall _ hmem
                simp [beq_iff_eq] at hzero
                -- hzero : distLens₀[dCode] = 0
                have : distLens₀[dCode]! = 0 := by
                  rw [getElem!_pos distLens₀ dCode hdc_lt]; exact hzero
                exact hdlen_nz this
              have hdl_eq : distLens = distLens₀ := by
                simp only [distLens, hdist_not_all_zero, Bool.false_eq_true, ↓reduceIte]
              -- Now use distLens₀ properties
              have hdsym : dCode < distLens.length := by rw [hdist_len]; omega
              have hdfreq := tokenFreqs_distCode_pos tokens len dist dCode dExtraN
                dExtraV.toUInt32 ht_mem hfdc_native
              have hdfreq_pair : ∃ p ∈ distFreqPairs, p.1 = dCode ∧ p.2 > 0 :=
                ⟨(dCode, distFreqs[dCode]!), by
                  simp only [distFreqPairs, List.mem_map, List.mem_range]
                  exact ⟨dCode, by omega, rfl⟩,
                  rfl, hdfreq⟩
              have hdlen_nz : distLens[dCode]! ≠ 0 := by
                rw [hdl_eq]
                exact Huffman.Spec.computeCodeLengths_nonzero distFreqPairs 30 15
                  (by omega) dCode (by omega) hdfreq_pair
              have hdlen_le' : distLens[dCode]! ≤ 15 := by
                rw [getElem!_pos distLens dCode hdsym]
                exact hdist_bound _ (List.getElem_mem hdsym)
              have hdist_enc := Deflate.Spec.encodeSymbol_fixed_isSome distLens 15 dCode
                hdsym hdlen_nz hdlen_le'
              cases hds : Deflate.Spec.encodeSymbol
                  ((Huffman.Spec.allCodes distLens).map fun (s, cw) => (cw, s)) dCode with
              | none => simp [hds] at hdist_enc
              | some distBits =>
                -- Close the goal: all four operations succeeded
                simp [LZ77Token.toLZ77Symbol, hlc, hls, hdc, hds]
    | inr heob =>
      subst heob
      -- Need: encodeLitLen litLens distLens .endOfBlock succeeds
      simp only [Deflate.Spec.encodeLitLen]
      have hsym : 256 < litLens.length := by rw [hlit_len]; omega
      have hfreq := tokenFreqs_eob_pos tokens
      have hfreq_pair : ∃ p ∈ litFreqPairs, p.1 = 256 ∧ p.2 > 0 :=
        ⟨(256, litFreqs[256]!), by
          simp only [litFreqPairs, List.mem_map, List.mem_range]
          exact ⟨256, by omega, rfl⟩,
          rfl, hfreq⟩
      have hlen_nz := Huffman.Spec.computeCodeLengths_nonzero litFreqPairs 286 15
        (by omega) 256 (by omega) hfreq_pair
      have hlen_le : litLens[256]! ≤ 15 := by
        rw [getElem!_pos litLens 256 hsym]
        exact hlit_bound _ (List.getElem_mem hsym)
      exact Deflate.Spec.encodeSymbol_fixed_isSome litLens 15 256 hsym hlen_nz hlen_le
  -- Extract the actual values
  cases henc_trees : Deflate.Spec.encodeDynamicTrees litLens distLens with
  | none => simp [henc_trees] at henc_trees_some
  | some headerBits =>
    cases henc_syms : Deflate.Spec.encodeSymbols litLens distLens
        (tokensToSymbols tokens) with
    | none => simp [henc_syms] at henc_syms_some
    | some symBits =>
      refine ⟨litLens, distLens, headerBits, symBits,
        hlit_valid, hdist_valid,
        by omega, by omega, by omega, by omega,
        hlit_bound, hdist_bound,
        henc_trees, henc_syms, ?_⟩
      -- bytesToBits decomposition
      -- Split symBits into tokBits ++ eobBits
      have htoks_eq : tokensToSymbols tokens =
          tokens.toList.map LZ77Token.toLZ77Symbol ++ [.endOfBlock] := rfl
      rw [htoks_eq] at henc_syms
      obtain ⟨tokBits, eobBits, henc_tok, henc_eob_syms, hsymBits_eq⟩ :=
        Deflate.encodeSymbols_append_inv litLens distLens
          (tokens.toList.map LZ77Token.toLZ77Symbol)
          [.endOfBlock] symBits henc_syms
      -- Extract EOB encoding
      simp only [Deflate.Spec.encodeSymbols] at henc_eob_syms
      cases henc_eob : Deflate.Spec.encodeLitLen litLens distLens .endOfBlock with
      | none => simp [henc_eob] at henc_eob_syms
      | some eobBits' =>
        simp [henc_eob] at henc_eob_syms
        have heob_eq : eobBits = eobBits' := by rw [henc_eob_syms]
        -- Build the combined encodeSymbols result
        have henc_combined := Deflate.encodeSymbols_append litLens distLens
          (tokens.toList.map LZ77Token.toLZ77Symbol)
          [.endOfBlock] tokBits eobBits henc_tok
          (by simp [Deflate.Spec.encodeSymbols, henc_eob, henc_eob_syms])
        -- Build canonical codes (same as in deflateDynamic)
        let litCodes := canonicalCodes (litLens.toArray.map Nat.toUInt8)
        let distCodes := canonicalCodes (distLens.toArray.map Nat.toUInt8)
        -- Size properties
        have hlit_codes_size : litCodes.size = litLens.length := by
          simp [litCodes, canonicalCodes_size, Array.size_map, List.size_toArray]
        have hdist_codes_size : distCodes.size = distLens.length := by
          simp [distCodes, canonicalCodes_size, Array.size_map, List.size_toArray]
        -- Code length bounds
        have hlit_lengths_arr_le : ∀ j, j < (litLens.toArray.map Nat.toUInt8).size →
            (litLens.toArray.map Nat.toUInt8)[j]!.toNat ≤ 15 := by
          intro k hk
          rw [getElem!_pos _ k hk]
          simp only [Array.getElem_map, Array.size_map, List.size_toArray] at hk ⊢
          simp only [UInt8.toNat, Nat.toUInt8, UInt8.ofNat, BitVec.toNat_ofNat]
          have hle := hlit_bound _ (List.getElem_mem hk)
          exact Nat.le_trans (Nat.mod_le _ _) hle
        have hdist_lengths_arr_le : ∀ j, j < (distLens.toArray.map Nat.toUInt8).size →
            (distLens.toArray.map Nat.toUInt8)[j]!.toNat ≤ 15 := by
          intro k hk
          rw [getElem!_pos _ k hk]
          simp only [Array.getElem_map, Array.size_map, List.size_toArray] at hk ⊢
          simp only [UInt8.toNat, Nat.toUInt8, UInt8.ofNat, BitVec.toNat_ofNat]
          have hle := hdist_bound _ (List.getElem_mem hk)
          exact Nat.le_trans (Nat.mod_le _ _) hle
        have hlit_le : ∀ j, j < litCodes.size → litCodes[j]!.2.toNat ≤ 15 := by
          intro j hj
          exact canonicalCodes_snd_le _ 15 hlit_lengths_arr_le j hj
        have hdist_le : ∀ j, j < distCodes.size → distCodes[j]!.2.toNat ≤ 15 := by
          intro j hj
          exact canonicalCodes_snd_le _ 15 hdist_lengths_arr_le j hj
        -- EOB codeword
        have ⟨heob_cw, heob_len⟩ := encodeSymbol_canonicalCodes_eq
          (litLens.toArray.map Nat.toUInt8) 15 litCodes rfl
          (by rwa [show (litLens.toArray.map Nat.toUInt8).toList.map UInt8.toNat = litLens from by
            simp only [Array.toList_map, List.map_map]; symm
            rw [List.map_congr_left (fun n hn => by
              show UInt8.toNat (Nat.toUInt8 n) = n
              simp only [Nat.toUInt8, UInt8.toNat, UInt8.ofNat, BitVec.toNat_ofNat]
              exact Nat.mod_eq_of_lt (by have := hlit_valid.1 n hn; omega))]
            simp])
          (by omega) 256 eobBits'
          (by simp only [Deflate.Spec.encodeLitLen] at henc_eob
              rwa [show (litLens.toArray.map Nat.toUInt8).toList.map UInt8.toNat = litLens from by
                simp only [Array.toList_map, List.map_map]; symm
                rw [List.map_congr_left (fun n hn => by
                  show UInt8.toNat (Nat.toUInt8 n) = n
                  simp only [Nat.toUInt8, UInt8.toNat, UInt8.ofNat, BitVec.toNat_ofNat]
                  exact Nat.mod_eq_of_lt (by have := hlit_valid.1 n hn; omega))]
                simp])
        -- BitWriter chain
        have hwf0 := BitWriter.empty_wf
        have hwf1 := BitWriter.writeBits_wf _ 1 1 hwf0 (by omega)
        have hwf2 := BitWriter.writeBits_wf _ 2 2 hwf1 (by omega)
        -- Header bits: [true, false, true]
        have hbw2_bits : (BitWriter.empty.writeBits 1 1 |>.writeBits 2 2).toBits =
            [true, false, true] := by
          have h1 := BitWriter.writeBits_toBits _ 1 1 hwf0 (by omega)
          have h2 := BitWriter.writeBits_toBits _ 2 2 hwf1 (by omega)
          rw [BitWriter.empty_toBits] at h1
          simp only [List.nil_append] at h1
          rw [h1] at h2; exact h2
        -- writeDynamicHeader
        let bw2 := BitWriter.empty.writeBits 1 1 |>.writeBits 2 2
        have hwf_hdr := writeDynamicHeader_wf bw2 litLens distLens hwf2 hlit_bound hdist_bound
        have hbw_hdr := writeDynamicHeader_spec bw2 litLens distLens headerBits hwf2
          hlit_bound hdist_bound ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ henc_trees
        -- emitTokensWithCodes
        let bw3 := writeDynamicHeader bw2 litLens distLens
        have hemit := emitTokensWithCodes_spec bw3 tokens litLens distLens
          litCodes distCodes tokBits hwf_hdr rfl rfl hlit_valid hdist_valid henc_tok
        have hwf_emit := emitTokensWithCodes_wf bw3 tokens litCodes distCodes hwf_hdr
          (by rw [hlit_codes_size]; omega) (by rw [hdist_codes_size]; omega)
          hlit_le hdist_le
        -- writeHuffCode for EOB
        let bw4 := emitTokensWithCodes bw3 tokens litCodes distCodes 0
        have h256_lt : 256 < litCodes.size := by rw [hlit_codes_size]; omega
        have hwf_eob := BitWriter.writeHuffCode_wf bw4
          litCodes[256]!.1 litCodes[256]!.2 hwf_emit (hlit_le 256 h256_lt)
        have hbw_eob := BitWriter.writeHuffCode_toBits bw4
          litCodes[256]!.1 litCodes[256]!.2 hwf_emit (hlit_le 256 h256_lt)
        -- Chain all the bits
        rw [hemit, hbw_hdr, hbw2_bits] at hbw_eob
        -- Show deflateDynamic data equals the flushed writer
        have hdef : deflateDynamic data =
            (bw4.writeHuffCode litCodes[256]!.1 litCodes[256]!.2).flush := by
          unfold deflateDynamic
          -- After unfold, we have `let (litFreqs, distFreqs) := tokenFreqs tokens; ...`
          -- This is definitionally equal to using .1/.2, and `let (code, len) := litCodes[256]!`
          -- is definitionally equal to using .1/.2. So `split` on the `if` suffices.
          split
          · rename_i hzero
            have hzero' : data.size = 0 := by
              rw [beq_iff_eq] at hzero; exact hzero
            have htok_empty : tokens = #[] := by
              simp only [tokens, lz77Greedy]
              rw [if_pos (show data.size < 3 by omega)]
              show (lz77Greedy.trailing data 0).toArray = #[]
              unfold lz77Greedy.trailing
              rw [if_neg (by omega)]
            have hemit_id : bw4 = bw3 := by
              show emitTokensWithCodes bw3 tokens litCodes distCodes 0 = bw3
              rw [htok_empty]; unfold emitTokensWithCodes; simp
            rw [hemit_id]; rfl
          · rfl
        rw [hdef]
        have hflush := BitWriter.flush_toBits _ hwf_eob
        -- The bits decomposition
        have hbits_eq : (bw4.writeHuffCode litCodes[256]!.1 litCodes[256]!.2).toBits =
            [true, false, true] ++ headerBits ++ symBits := by
          rw [hbw_eob]
          rw [hsymBits_eq, heob_eq, heob_cw]
          simp only [List.append_assoc]
        rw [hflush, hbits_eq]
        -- Align the bitCount % 8
        suffices hmod : (bw4.writeHuffCode litCodes[256]!.1 litCodes[256]!.2).bitCount.toNat % 8 =
            ([true, false, true] ++ headerBits ++ symBits).length % 8 by
          simp only [hmod]
        have htoBits_len : (bw4.writeHuffCode litCodes[256]!.1 litCodes[256]!.2).toBits.length =
            (bw4.writeHuffCode litCodes[256]!.1 litCodes[256]!.2).data.data.toList.length * 8 +
            (bw4.writeHuffCode litCodes[256]!.1 litCodes[256]!.2).bitCount.toNat := by
          simp only [BitWriter.toBits, List.length_append, List.length_flatMap,
            Deflate.Spec.bytesToBits.byteToBits_length, List.length_map, List.length_range]
          have hsum : ∀ (l : List UInt8),
              (l.map (fun _ => 8)).sum = l.length * 8 := by
            intro l; induction l with
            | nil => simp
            | cons _ _ ih => simp [ih, Nat.add_mul]; omega
          rw [hsum]
        rw [hbits_eq] at htoBits_len
        omega

/-- Native Level 5 roundtrip: compressing with greedy LZ77 + dynamic Huffman
    codes then decompressing recovers the original data.
    Size bound: same as `inflate_deflateFixed`. -/
theorem inflate_deflateDynamic (data : ByteArray)
    (hsize : data.size < 10000000) :
    Zip.Native.Inflate.inflate (deflateDynamic data) = .ok data := by
  have hspec := deflateDynamic_spec data
  match hspec with
  | ⟨litLens, distLens, headerBits, symBits, hv_lit, hv_dist,
      hlitLen_lo, hlitLen_hi, hdistLen_lo, hdistLen_hi,
      hlit_bound, hdist_bound,
      henc_trees, henc_syms, hbits⟩ =>
    -- Decode roundtrip for dynamic blocks
    have hheader := Deflate.Spec.encodeDynamicTrees_decodeDynamicTables
      litLens distLens headerBits
      (symBits ++ List.replicate
        ((8 - ([true, false, true] ++ headerBits ++ symBits).length % 8) % 8) false)
      hlit_bound hdist_bound
      ⟨hlitLen_lo, hlitLen_hi⟩ ⟨hdistLen_lo, hdistLen_hi⟩
      hv_lit hv_dist henc_trees
    have hdec_padded : Deflate.Spec.decode (Deflate.Spec.bytesToBits (deflateDynamic data)) =
        some data.data.toList := by
      rw [hbits]
      let padding := List.replicate
        ((8 - ([true, false, true] ++ headerBits ++ symBits).length % 8) % 8) false
      have hheader' : Deflate.Spec.decodeDynamicTables (headerBits ++ symBits ++ padding) =
          some (litLens, distLens, symBits ++ padding) := by
        rw [List.append_assoc]; exact hheader
      exact Deflate.Spec.encodeDynamic_decode_append
        (tokensToSymbols (lz77Greedy data 32768)) data.data.toList
        litLens distLens headerBits symBits padding
        hv_lit hv_dist
        hheader'
        henc_syms
        (lz77Greedy_resolves data 32768 (by omega))
        (by have := lz77Greedy_size_le data 32768; rw [tokensToSymbols_length]; omega)
        (tokensToSymbols_validSymbolList _)
    have hlen : data.data.toList.length ≤ 256 * 1024 * 1024 := by
      simp only [Array.length_toList, ByteArray.size_data]; omega
    rw [← show ByteArray.mk ⟨data.data.toList⟩ = data from by simp]
    exact inflate_complete (deflateDynamic data) data.data.toList hlen hdec_padded

end Zip.Native.Deflate
