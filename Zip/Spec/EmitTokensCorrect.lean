import Zip.Spec.DeflateFixedTables
import Zip.Spec.LZ77NativeCorrect
import Zip.Spec.BitWriterCorrect
import Zip.Spec.HuffmanEncodeCorrect

/-!
# emitTokens ↔ encodeSymbols Correspondence

This file proves that the native `emitTokens` function (which writes LZ77
tokens as Huffman-coded bits using `BitWriter`) produces the same bit sequence
as the spec-level `encodeSymbols`. It also contains helper lemmas for
`canonicalCodes` bounds and `findTableCode` properties used by both the
fixed and dynamic Huffman correctness proofs.

## Key results

- `emitTokens_spec`: native `emitTokens` produces the same bits as spec `encodeSymbols`
- `emitTokens_wf`: `emitTokens` preserves `BitWriter.wf`
- `encodeSymbols_append` / `encodeSymbols_append_inv`: `encodeSymbols` distributes over list append
- `encodeSymbols_singleton`: `encodeSymbols` on a one-element list
- `canonicalCodes_size`: `canonicalCodes` preserves array size
- `fixedLitCodes_snd_le` / `fixedDistCodes_snd_le`: code length bounds
-/

namespace Zip.Native.Deflate

/-! ## emitTokens ↔ encodeSymbols correspondence -/

private theorem array_get!Internal_eq [Inhabited α] (a : Array α) (i : Nat) :
    a.get!Internal i = a[i]! := rfl

set_option maxRecDepth 2048 in
/-- Generalized `emitTokens_spec` with arbitrary start index. -/
private theorem emitTokens_spec_go (bw : BitWriter) (tokens : Array LZ77Token)
    (i : Nat) (bits : List Bool) (hwf : bw.wf)
    (henc : Deflate.Spec.encodeSymbols
        Deflate.Spec.fixedLitLengths Deflate.Spec.fixedDistLengths
        ((tokens.toList.drop i).map LZ77Token.toLZ77Symbol) = some bits) :
    (emitTokens bw tokens i).toBits = bw.toBits ++ bits := by
  -- Induction on tokens.size - i
  suffices ∀ k, k = tokens.size - i →
      (emitTokens bw tokens i).toBits = bw.toBits ++ bits by
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
    simp only [emitTokens, show ¬(i < tokens.size) from by omega, ↓reduceDIte,
      List.append_nil]
  | succ n ih =>
    intro heq
    have hlt : i < tokens.size := by omega
    have hlt_list : i < tokens.toList.length := by simp; exact hlt
    rw [List.drop_eq_getElem_cons hlt_list, List.map_cons] at henc
    obtain ⟨symBits, restBits, hencsym, hencrest, hbits_eq⟩ :=
      Deflate.encodeSymbols_cons_some _ _ _ _ _ henc
    subst hbits_eq
    -- Bridge array ↔ list indexing
    have htoList : tokens[i] = tokens.toList[i] := by simp [Array.getElem_toList]
    -- Unfold emitTokens one step and take the positive branch
    unfold emitTokens
    simp only [dif_pos hlt]
    -- Case split on token type, then reduce let-match pattern
    cases htok : tokens[i] with
    | literal b =>
      simp only [array_get!Internal_eq]  -- normalize get!Internal → [·]!
      -- Spec side
      have htok_list : tokens.toList[i] = .literal b := by rw [← htoList]; exact htok
      simp only [LZ77Token.toLZ77Symbol, htok_list] at hencsym
      simp only [Deflate.Spec.encodeLitLen] at hencsym
      have ⟨hcw, hlen⟩ := Deflate.encodeSymbol_litTable_eq b.toNat symBits hencsym
      -- BitWriter correspondence + IH
      have hwf' := BitWriter.writeHuffCode_wf bw
        fixedLitCodes[b.toNat]!.1 fixedLitCodes[b.toNat]!.2 hwf hlen
      have hbits := BitWriter.writeHuffCode_toBits bw
        fixedLitCodes[b.toNat]!.1 fixedLitCodes[b.toNat]!.2 hwf hlen
      rw [ih _ (i + 1) restBits hwf' hencrest (by omega)]
      rw [hbits, hcw, List.append_assoc]
    | reference len dist =>
      simp only [array_get!Internal_eq]  -- normalize get!Internal → [·]!
      -- Spec side: decompose encodeLitLen for reference
      have htok_list : tokens.toList[i] = .reference len dist := by
        rw [← htoList]; exact htok
      simp only [LZ77Token.toLZ77Symbol, htok_list] at hencsym
      simp only [Deflate.Spec.encodeLitLen] at hencsym
      cases hflc : Deflate.Spec.findLengthCode len with
      | none => simp [hflc] at hencsym
      | some lc =>
        obtain ⟨lidx, lextraN, lextraV⟩ := lc
        cases henclen : Deflate.Spec.encodeSymbol
            ((Huffman.Spec.allCodes Deflate.Spec.fixedLitLengths).map fun p => (p.2, p.1))
            (257 + lidx) with
        | none => simp [hflc, henclen] at hencsym
        | some lenBits =>
          cases hfdc : Deflate.Spec.findDistCode dist with
          | none => simp [hflc, hfdc] at hencsym
          | some dc =>
            obtain ⟨didx, dextraN, dextraV⟩ := dc
            cases hencdist : Deflate.Spec.encodeSymbol
                ((Huffman.Spec.allCodes Deflate.Spec.fixedDistLengths).map fun p => (p.2, p.1))
                didx with
            | none => simp [hflc, hfdc, hencdist] at hencsym
            | some distBits =>
              simp [hflc, henclen, hfdc, hencdist] at hencsym
              subst hencsym
              -- Bridge lemmas
              have hnflc := Deflate.findLengthCode_agree len lidx lextraN lextraV hflc
              have hnfdc := Deflate.findDistCode_agree dist didx dextraN dextraV hfdc
              have ⟨hlcw, hllen⟩ := Deflate.encodeSymbol_litTable_eq (257 + lidx) lenBits henclen
              have ⟨hdcw, hdlen⟩ := Deflate.encodeSymbol_distTable_eq didx distBits hencdist
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
              -- Normalize lidx + 257 → 257 + lidx to match spec convention
              have h257 : lidx + 257 = 257 + lidx := by omega
              rw [h257]
              -- Chain BitWriter correspondence (explicit args to avoid inference failure)
              let lcode := fixedLitCodes[257 + lidx]!.fst
              let llen := fixedLitCodes[257 + lidx]!.snd
              let dcode := fixedDistCodes[didx]!.fst
              let dlen := fixedDistCodes[didx]!.snd
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
              -- Apply IH for remaining tokens
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

/-- `emitTokens` produces the same bit sequence as spec `encodeSymbols`. -/
theorem emitTokens_spec (bw : BitWriter) (tokens : Array LZ77Token)
    (bits : List Bool) (hwf : bw.wf)
    (henc : Deflate.Spec.encodeSymbols
        Deflate.Spec.fixedLitLengths Deflate.Spec.fixedDistLengths
        (tokens.toList.map LZ77Token.toLZ77Symbol) = some bits) :
    (emitTokens bw tokens 0).toBits =
    bw.toBits ++ bits := by
  exact emitTokens_spec_go bw tokens 0 bits hwf (by rwa [List.drop_zero])

/-! ## encodeSymbols append lemmas -/

/-- `encodeSymbols` distributes over append: encoding `xs ++ ys` is the
    concatenation of encoding `xs` and encoding `ys`. -/
protected theorem encodeSymbols_append
    (litLengths distLengths : List Nat)
    (xs ys : List Deflate.Spec.LZ77Symbol)
    (xBits yBits : List Bool)
    (hx : Deflate.Spec.encodeSymbols litLengths distLengths xs = some xBits)
    (hy : Deflate.Spec.encodeSymbols litLengths distLengths ys = some yBits) :
    Deflate.Spec.encodeSymbols litLengths distLengths (xs ++ ys) =
      some (xBits ++ yBits) := by
  induction xs generalizing xBits with
  | nil =>
    simp only [Deflate.Spec.encodeSymbols] at hx
    cases hx; simp only [List.nil_append, List.nil_append]; exact hy
  | cons s rest ih =>
    simp only [List.cons_append, Deflate.Spec.encodeSymbols]
    obtain ⟨symBits, restBits, hencsym, hencrest, hbits_eq⟩ :=
      Deflate.encodeSymbols_cons_some _ _ _ _ _ hx
    subst hbits_eq
    have hrest_ys := ih restBits hencrest
    simp only [hencsym, hrest_ys, bind, Option.bind, List.append_assoc, pure, Pure.pure]

/-- If `encodeSymbols` succeeds on `xs ++ ys`, it succeeds on `xs` and `ys` separately. -/
protected theorem encodeSymbols_append_inv
    (litLengths distLengths : List Nat)
    (xs ys : List Deflate.Spec.LZ77Symbol)
    (bits : List Bool)
    (h : Deflate.Spec.encodeSymbols litLengths distLengths (xs ++ ys) = some bits) :
    ∃ xBits yBits,
      Deflate.Spec.encodeSymbols litLengths distLengths xs = some xBits ∧
      Deflate.Spec.encodeSymbols litLengths distLengths ys = some yBits ∧
      bits = xBits ++ yBits := by
  induction xs generalizing bits with
  | nil =>
    simp only [List.nil_append] at h
    exact ⟨[], bits, rfl, h, (List.nil_append _).symm⟩
  | cons s rest ih =>
    simp only [List.cons_append, Deflate.Spec.encodeSymbols] at h
    cases hes : Deflate.Spec.encodeLitLen litLengths distLengths s with
    | none => simp [hes] at h
    | some sBits =>
      cases her : Deflate.Spec.encodeSymbols litLengths distLengths (rest ++ ys) with
      | none => simp [hes, her] at h
      | some restBits =>
        simp only [hes, her, bind, Option.bind, pure, Pure.pure] at h
        have h := Option.some.inj h
        obtain ⟨xBits, yBits, hx, hy, heq⟩ := ih restBits her
        refine ⟨sBits ++ xBits, yBits, ?_, hy, ?_⟩
        · simp only [Deflate.Spec.encodeSymbols, hes, hx, bind, Option.bind, pure, Pure.pure]
        · rw [← h, heq, List.append_assoc]

/-! ## Helper lemmas for deflateFixed_spec -/

/-- `findTableCode.go` returns an index < baseTable.size. -/
private theorem findTableCode_go_idx_bound (baseTable : Array UInt16)
    (extraTable : Array UInt8) (value i idx extraN : Nat) (extraV : UInt32)
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

/-- `findTableCode.go` returns extraN = extraTable[idx]!.toNat. -/
private theorem findTableCode_go_extraN (baseTable : Array UInt16)
    (extraTable : Array UInt8) (value i idx extraN : Nat) (extraV : UInt32)
    (h : findTableCode.go baseTable extraTable value i = some (idx, extraN, extraV)) :
    extraN = extraTable[idx]!.toNat := by
  unfold findTableCode.go at h
  split at h
  · split at h
    · simp at h; rw [← h.1]; exact h.2.1.symm
    · exact findTableCode_go_extraN baseTable extraTable value (i + 1) idx extraN extraV h
  · split at h
    · simp at h; rw [← h.1]; exact h.2.1.symm
    · simp at h
termination_by baseTable.size - i

/-- Native `findLengthCode` returns idx < 29. -/
private theorem nativeFindLengthCode_idx_bound (len idx extraN : Nat) (extraV : UInt32)
    (h : findLengthCode len = some (idx, extraN, extraV)) :
    idx < 29 := by
  have := findTableCode_go_idx_bound _ _ _ _ _ _ _ h
  have : Inflate.lengthBase.size = 29 := by rfl
  omega

/-- Native `findLengthCode` returns extraN ≤ 5. -/
private theorem nativeFindLengthCode_extraN_bound (len idx extraN : Nat) (extraV : UInt32)
    (h : findLengthCode len = some (idx, extraN, extraV)) :
    extraN ≤ 5 := by
  have hidx := nativeFindLengthCode_idx_bound len idx extraN extraV h
  have hextraN := findTableCode_go_extraN _ _ _ _ _ _ _ h
  rw [hextraN]
  have : ∀ j : Fin 29, Inflate.lengthExtra[j.val]!.toNat ≤ 5 := by decide
  exact this ⟨idx, hidx⟩

/-- Native `findDistCode` returns dIdx < 30. -/
private theorem nativeFindDistCode_idx_bound (dist dIdx dExtraN : Nat) (dExtraV : UInt32)
    (h : findDistCode dist = some (dIdx, dExtraN, dExtraV)) :
    dIdx < 30 := by
  have := findTableCode_go_idx_bound _ _ _ _ _ _ _ h
  have : Inflate.distBase.size = 30 := by rfl
  omega

/-- Native `findDistCode` returns dExtraN ≤ 13. -/
private theorem nativeFindDistCode_extraN_bound (dist dIdx dExtraN : Nat) (dExtraV : UInt32)
    (h : findDistCode dist = some (dIdx, dExtraN, dExtraV)) :
    dExtraN ≤ 13 := by
  have hidx := nativeFindDistCode_idx_bound dist dIdx dExtraN dExtraV h
  have hextraN := findTableCode_go_extraN _ _ _ _ _ _ _ h
  rw [hextraN]
  have : ∀ j : Fin 30, Inflate.distExtra[j.val]!.toNat ≤ 13 := by decide
  exact this ⟨dIdx, hidx⟩

/-- `canonicalCodes` preserves the array size. -/
private theorem canonicalCodes_size (lengths : Array UInt8) :
    (canonicalCodes lengths).size = lengths.size := by
  simp only [canonicalCodes]
  rw [Deflate.Correctness.canonicalCodes_go_size]
  simp [Array.size_replicate]

/-- `fixedLitCodes` has size 288 (= Inflate.fixedLitLengths.size). -/
private theorem fixedLitCodes_size : fixedLitCodes.size = 288 := by
  show (canonicalCodes Inflate.fixedLitLengths).size = 288
  rw [canonicalCodes_size]
  simp [Inflate.fixedLitLengths, Array.size_append, Array.size_replicate]

/-- `fixedDistCodes` has size 32 (= Inflate.fixedDistLengths.size). -/
private theorem fixedDistCodes_size : fixedDistCodes.size = 32 := by
  show (canonicalCodes Inflate.fixedDistLengths).size = 32
  rw [canonicalCodes_size]
  simp [Inflate.fixedDistLengths, Array.size_replicate]

/-- `canonicalCodes.go` preserves a bound on `.snd.toNat`: if all entries in
    `result` have `.snd.toNat ≤ bound` and all entries in `lengths` have
    `.toNat ≤ bound`, then the output has all `.snd.toNat ≤ bound`. -/
private theorem canonicalCodes_go_snd_le (lengths : Array UInt8) (nextCode : Array UInt32)
    (i : Nat) (result : Array (UInt16 × UInt8)) (bound : Nat)
    (hsize : result.size = lengths.size)
    (hresult : ∀ j, j < result.size → result[j]!.2.toNat ≤ bound)
    (hlengths : ∀ j, j < lengths.size → lengths[j]!.toNat ≤ bound)
    (j : Nat) (hj : j < (canonicalCodes.go lengths nextCode i result).size) :
    (canonicalCodes.go lengths nextCode i result)[j]!.2.toNat ≤ bound := by
  unfold canonicalCodes.go at hj ⊢
  by_cases hi : i < lengths.size
  · simp only [hi, ↓reduceDIte] at hj ⊢
    by_cases hlen : lengths[i] > 0
    · simp only [hlen, ↓reduceIte] at hj ⊢
      let val := (nextCode[lengths[i].toNat]!.toUInt16, lengths[i])
      have hsize' : (result.set! i val).size = lengths.size := by
        simp only [Array.set!_eq_setIfInBounds, Array.setIfInBounds]
        split <;> simp_all
      have hresult' : ∀ k, k < (result.set! i val).size →
          (result.set! i val)[k]!.2.toNat ≤ bound := by
        intro k hk
        by_cases heq : k = i
        · rw [heq, getElem!_pos (result.set! i val) i (by rw [hsize']; exact hi)]
          simp only [Array.set!_eq_setIfInBounds, Array.setIfInBounds,
            show i < result.size from by rw [hsize]; exact hi, ↓reduceDIte,
            Array.getElem_set, ↓reduceIte, val]
          rw [← getElem!_pos lengths i hi]
          exact hlengths i hi
        · rw [getElem!_pos (result.set! i val) k (by rw [hsize']; omega)]
          simp only [Array.set!_eq_setIfInBounds, Array.setIfInBounds,
            show i < result.size from by rw [hsize]; exact hi, ↓reduceDIte,
            Array.getElem_set, show ¬(i = k) from (Ne.symm heq), ↓reduceIte]
          rw [← getElem!_pos result k (by rw [hsize]; omega)]
          exact hresult k (by rw [hsize]; omega)
      exact canonicalCodes_go_snd_le lengths _ (i + 1) _ bound hsize' hresult'
        hlengths j hj
    · simp only [show ¬(lengths[i] > 0) from hlen, ↓reduceIte] at hj ⊢
      exact canonicalCodes_go_snd_le lengths nextCode (i + 1) result bound hsize hresult
        hlengths j hj
  · simp only [hi, ↓reduceDIte] at hj ⊢
    exact hresult j hj
termination_by lengths.size - i

/-- `canonicalCodes` entries have `.snd.toNat ≤ bound` when all input lengths
    have `.toNat ≤ bound`. -/
private theorem canonicalCodes_snd_le (lengths : Array UInt8) (bound : Nat)
    (hlengths : ∀ j, j < lengths.size → lengths[j]!.toNat ≤ bound) (i : Nat)
    (hi : i < (canonicalCodes lengths).size) :
    (canonicalCodes lengths)[i]!.2.toNat ≤ bound := by
  simp only [canonicalCodes] at hi ⊢
  apply canonicalCodes_go_snd_le lengths _ 0 _ bound
  · simp [Array.size_replicate]
  · intro j hj
    simp only [Array.size_replicate] at hj
    rw [getElem!_pos _ _ (by simp [Array.size_replicate]; omega)]
    simp [Array.getElem_replicate]
  · exact hlengths
  · exact hi

/-- All entries in `fixedLitLengths` have `.toNat ≤ 15`. -/
private theorem fixedLitLengths_le_15 (j : Nat) (hj : j < Inflate.fixedLitLengths.size) :
    Inflate.fixedLitLengths[j]!.toNat ≤ 15 := by
  -- fixedLitLengths = replicate 144 8 ++ replicate 112 9 ++ replicate 24 7 ++ replicate 8 8
  simp only [Inflate.fixedLitLengths, Array.size_append, Array.size_replicate] at hj
  show (Array.replicate 144 (8 : UInt8) ++ Array.replicate 112 9 ++ Array.replicate 24 7 ++
    Array.replicate 8 8)[j]!.toNat ≤ 15
  rw [getElem!_pos _ _ (by simp [Array.size_append, Array.size_replicate]; omega)]
  by_cases h1 : j < 280
  · have hlt : j < (Array.replicate 144 (8 : UInt8) ++ Array.replicate 112 9 ++
        Array.replicate 24 7).size := by
      simp [Array.size_append, Array.size_replicate]; omega
    rw [Array.getElem_append_left hlt]
    by_cases h2 : j < 256
    · have hlt2 : j < (Array.replicate 144 (8 : UInt8) ++ Array.replicate 112 9).size := by
        simp [Array.size_append, Array.size_replicate]; omega
      rw [Array.getElem_append_left hlt2]
      by_cases h3 : j < 144
      · rw [Array.getElem_append_left (by simp [Array.size_replicate]; omega)]
        simp [Array.getElem_replicate]
      · rw [Array.getElem_append_right (by simp [Array.size_replicate]; omega)]
        simp [Array.size_replicate, Array.getElem_replicate]
    · rw [Array.getElem_append_right (by simp [Array.size_append, Array.size_replicate]; omega)]
      simp [Array.size_append, Array.size_replicate, Array.getElem_replicate]
  · rw [Array.getElem_append_right (by simp [Array.size_append, Array.size_replicate]; omega)]
    simp [Array.size_append, Array.size_replicate, Array.getElem_replicate]

/-- All entries in `fixedDistLengths` have `.toNat ≤ 15`. -/
private theorem fixedDistLengths_le_15 (j : Nat) (hj : j < Inflate.fixedDistLengths.size) :
    Inflate.fixedDistLengths[j]!.toNat ≤ 15 := by
  have hj32 : j < 32 := hj
  show (Array.replicate 32 (5 : UInt8))[j]!.toNat ≤ 15
  rw [getElem!_pos _ _ (by simp [Array.size_replicate]; omega)]
  simp [Array.getElem_replicate]

/-- All entries in `fixedLitCodes` have code length ≤ 15.
    Proof: the fixed Huffman table uses lengths 7, 8, 9 (all ≤ 15). -/
private theorem fixedLitCodes_snd_le (i : Nat) (h : i < fixedLitCodes.size) :
    fixedLitCodes[i]!.2.toNat ≤ 15 :=
  canonicalCodes_snd_le Inflate.fixedLitLengths 15 fixedLitLengths_le_15 i h

/-- All entries in `fixedDistCodes` have code length ≤ 15.
    Proof: the fixed distance table uses uniform length 5. -/
private theorem fixedDistCodes_snd_le (i : Nat) (h : i < fixedDistCodes.size) :
    fixedDistCodes[i]!.2.toNat ≤ 15 :=
  canonicalCodes_snd_le Inflate.fixedDistLengths 15 fixedDistLengths_le_15 i h

/-! ## emitTokens preserves wf -/

set_option maxRecDepth 2048 in
/-- `emitTokens` preserves `BitWriter.wf`. -/
private theorem emitTokens_wf_go (bw : BitWriter) (tokens : Array LZ77Token)
    (i : Nat) (hwf : bw.wf) :
    (emitTokens bw tokens i).wf := by
  suffices ∀ k, k = tokens.size - i → (emitTokens bw tokens i).wf by
    exact this _ rfl
  intro k
  induction k generalizing bw i with
  | zero =>
    intro heq
    simp only [emitTokens, show ¬(i < tokens.size) from by omega, ↓reduceDIte]
    exact hwf
  | succ n ih =>
    intro heq
    have hlt : i < tokens.size := by omega
    unfold emitTokens
    simp only [dif_pos hlt]
    match htok : tokens[i] with
    | .literal b =>
      simp only [htok]
      have hb : b.toNat < fixedLitCodes.size := by
        have := fixedLitCodes_size
        have : b.toNat < 256 := UInt8.toNat_lt b
        omega
      exact ih _ (i + 1)
        (BitWriter.writeHuffCode_wf bw _ _ hwf (fixedLitCodes_snd_le b.toNat hb))
        (by omega)
    | .reference len dist =>
      simp only [htok]
      match hflc : findLengthCode len with
      | none =>
        simp only [hflc]
        exact ih _ (i + 1) hwf (by omega)
      | some (idx, extraCount, extraVal) =>
        simp only [hflc]
        have hidx := nativeFindLengthCode_idx_bound len idx extraCount extraVal hflc
        have hlen_code := fixedLitCodes_snd_le (idx + 257)
          (by have := fixedLitCodes_size; omega)
        have hextraN_le : extraCount ≤ 25 := by
          have := nativeFindLengthCode_extraN_bound len idx extraCount extraVal hflc; omega
        have hwf1 := BitWriter.writeHuffCode_wf bw
          fixedLitCodes[idx + 257]!.1 fixedLitCodes[idx + 257]!.2 hwf hlen_code
        have hwf2 := BitWriter.writeBits_wf
          (bw.writeHuffCode fixedLitCodes[idx + 257]!.1 fixedLitCodes[idx + 257]!.2)
          extraCount extraVal hwf1 hextraN_le
        match hfdc : findDistCode dist with
        | none =>
          simp only [hfdc]
          exact ih _ (i + 1) hwf2 (by omega)
        | some (dIdx, dExtraCount, dExtraVal) =>
          simp only [hfdc]
          have hdidx := nativeFindDistCode_idx_bound dist dIdx dExtraCount dExtraVal hfdc
          have hdlen_code := fixedDistCodes_snd_le dIdx
            (by have := fixedDistCodes_size; omega)
          have hdextraN_le : dExtraCount ≤ 25 := by
            have := nativeFindDistCode_extraN_bound dist dIdx dExtraCount dExtraVal hfdc; omega
          have hwf3 := BitWriter.writeHuffCode_wf _
            fixedDistCodes[dIdx]!.1 fixedDistCodes[dIdx]!.2 hwf2 hdlen_code
          have hwf4 := BitWriter.writeBits_wf _ dExtraCount dExtraVal hwf3 hdextraN_le
          exact ih _ (i + 1) hwf4 (by omega)

theorem emitTokens_wf (bw : BitWriter) (tokens : Array LZ77Token)
    (hwf : bw.wf) :
    (emitTokens bw tokens 0).wf :=
  emitTokens_wf_go bw tokens 0 hwf

/-- `encodeSymbols` on a singleton list returns `encodeLitLen` of that symbol. -/
private theorem encodeSymbols_singleton
    (litLengths distLengths : List Nat) (s : Deflate.Spec.LZ77Symbol)
    (bits : List Bool)
    (h : Deflate.Spec.encodeLitLen litLengths distLengths s = some bits) :
    Deflate.Spec.encodeSymbols litLengths distLengths [s] = some bits := by
  simp only [Deflate.Spec.encodeSymbols, h, bind, Option.bind, List.append_nil, pure, Pure.pure]

end Zip.Native.Deflate
