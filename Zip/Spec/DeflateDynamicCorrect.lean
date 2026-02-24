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
    sorry
  -- encodeSymbols succeeds
  have henc_syms_some : (Deflate.Spec.encodeSymbols litLens distLens
      (tokensToSymbols tokens)).isSome = true := by
    sorry
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
      sorry

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
