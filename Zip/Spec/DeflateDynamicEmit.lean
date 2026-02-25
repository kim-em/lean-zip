import Zip.Spec.DeflateFixedCorrect
import Zip.Spec.DeflateEncodeDynamicProps

/-!
# emitTokensWithCodes ↔ encodeSymbols correspondence

Proves that the native `emitTokensWithCodes` (dynamic Huffman compressor)
produces the same bit sequence as the spec-level `encodeSymbols`, generalizing
`emitTokens_spec` from `DeflateFixedCorrect.lean` to arbitrary
`canonicalCodes`-produced tables.

## Key results

- `encodeSymbol_canonicalCodes_eq`: generalized bridge from `encodeSymbol` to
  `canonicalCodes` entries
- `emitTokensWithCodes_spec`: correspondence with spec `encodeSymbols`
- `emitTokensWithCodes_wf`: well-formedness preservation
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
set_option linter.unusedSimpArgs false in
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

end Zip.Native.Deflate
