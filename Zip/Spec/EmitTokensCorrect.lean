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
- `canonicalCodes_size`: `canonicalCodes` preserves array size
- `fixedLitCodes_snd_le` / `fixedDistCodes_snd_le`: code length bounds
-/

namespace Zip.Native.Deflate

/-! ## emitTokens ↔ encodeSymbols correspondence -/

theorem array_get!Internal_eq [Inhabited α] (a : Array α) (i : Nat) :
    a.get!Internal i = a[i]! := rfl

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
      simp only [List.drop_eq_nil_iff, Array.length_toList]; omega
    rw [hdrop, List.map_nil] at henc
    simp only [Deflate.Spec.encodeSymbols] at henc
    cases henc
    simp only [emitTokens, show ¬(i < tokens.size) from by omega, ↓reduceDIte,
      List.append_nil]
  | succ n ih =>
    intro heq
    have hlt : i < tokens.size := by omega
    have hlt_list : i < tokens.toList.length := by simpa only [Array.length_toList]
    rw [List.drop_eq_getElem_cons hlt_list, List.map_cons] at henc
    obtain ⟨symBits, restBits, hencsym, hencrest, hbits_eq⟩ :=
      Deflate.encodeSymbols_cons_some _ _ _ _ _ henc
    subst hbits_eq
    -- Bridge array ↔ list indexing
    have htoList : tokens[i] = tokens.toList[i] := by simp only [Array.getElem_toList]
    -- Unfold emitTokens one step and take the positive branch
    unfold emitTokens
    simp only [dif_pos hlt]
    -- Case split on token type, then reduce let-match pattern
    cases htok : tokens[i] with
    | literal b =>
      simp only []
      -- Spec side
      have htok_list : tokens.toList[i] = .literal b := htoList ▸ htok
      simp only [LZ77Token.toLZ77Symbol, htok_list, Deflate.Spec.encodeLitLen] at hencsym
      have ⟨hcw, hlen⟩ := Deflate.encodeSymbol_litTable_eq b.toNat symBits hencsym
      -- Bridge: convert [·]! hypotheses to [·] (proven-bounds) to match goal
      have hb_lt : b.toNat < fixedLitCodes.size := by
        have := UInt8.toNat_lt b; rw [Deflate.fixedLitCodes_size]; omega
      rw [getElem!_pos fixedLitCodes b.toNat hb_lt] at hcw hlen
      -- BitWriter correspondence + IH (explicit args for getInternal/getElem unification)
      have hwf' := BitWriter.writeHuffCode_wf bw
        (fixedLitCodes[b.toNat]'hb_lt).1 (fixedLitCodes[b.toNat]'hb_lt).2 hwf hlen
      have hbits := BitWriter.writeHuffCode_toBits bw
        (fixedLitCodes[b.toNat]'hb_lt).1 (fixedLitCodes[b.toNat]'hb_lt).2 hwf hlen
      -- Build ih result then rewrite its RHS (avoids getInternal/getElem mismatch in rw)
      have h_ih := ih _ (i + 1) restBits hwf' hencrest (by omega)
      rw [hbits, List.append_assoc] at h_ih
      rw [hcw]; exact h_ih
    | reference len dist =>
      simp only []
      -- Spec side: decompose encodeLitLen for reference
      have htok_list : tokens.toList[i] = .reference len dist := htoList ▸ htok
      simp only [LZ77Token.toLZ77Symbol, htok_list, Deflate.Spec.encodeLitLen] at hencsym
      cases hflc : Deflate.Spec.findLengthCode len with
      | none =>
        simp only [hflc, bind, Option.bind] at hencsym
        exact nomatch hencsym
      | some lc =>
        obtain ⟨lidx, lextraN, lextraV⟩ := lc
        cases henclen : Deflate.Spec.encodeSymbol
            ((Huffman.Spec.allCodes Deflate.Spec.fixedLitLengths).map fun p => (p.2, p.1))
            (257 + lidx) with
        | none =>
          simp only [hflc, henclen, bind, Option.bind] at hencsym
          exact nomatch hencsym
        | some lenBits =>
          cases hfdc : Deflate.Spec.findDistCode dist with
          | none =>
            simp only [hflc, henclen, hfdc, bind, Option.bind] at hencsym
            exact nomatch hencsym
          | some dc =>
            obtain ⟨didx, dextraN, dextraV⟩ := dc
            cases hencdist : Deflate.Spec.encodeSymbol
                ((Huffman.Spec.allCodes Deflate.Spec.fixedDistLengths).map fun p => (p.2, p.1))
                didx with
            | none =>
              simp only [hflc, henclen, hfdc, hencdist, bind, Option.bind] at hencsym
              exact nomatch hencsym
            | some distBits =>
              simp only [hflc, henclen, hfdc, hencdist,
                bind, Option.bind, pure, Pure.pure, Option.some.injEq] at hencsym
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
              -- Bounds for the if-guards in the implementation
              have hlit_bound : lidx + 257 < fixedLitCodes.size := by
                have := hflc_spec.1; rw [Deflate.fixedLitCodes_size]; omega
              have hdist_bound : didx < fixedDistCodes.size := by
                have := hfdc_spec.1; rw [Deflate.fixedDistCodes_size]; omega
              -- Convert [·]! bridge lemma results to [·] (proven-bounds) form
              rw [show 257 + lidx = lidx + 257 from by omega] at hlcw hllen
              rw [getElem!_pos fixedLitCodes (lidx + 257) hlit_bound] at hlcw hllen
              rw [getElem!_pos fixedDistCodes didx hdist_bound] at hdcw hdlen
              -- Reduce native findLengthCode/findDistCode matches and if-guards
              simp only [hnflc, hnfdc, dif_pos hlit_bound, dif_pos hdist_bound]
              -- Chain BitWriter correspondence (explicit args for getInternal unification)
              have hwf1 := BitWriter.writeHuffCode_wf bw
                (fixedLitCodes[lidx + 257]'hlit_bound).1 (fixedLitCodes[lidx + 257]'hlit_bound).2
                hwf hllen
              have hbits1 := BitWriter.writeHuffCode_toBits bw
                (fixedLitCodes[lidx + 257]'hlit_bound).1 (fixedLitCodes[lidx + 257]'hlit_bound).2
                hwf hllen
              have hwf2 := BitWriter.writeBits_wf _ lextraN lextraV.toUInt32 hwf1 lextraN_le
              have hbits2 := BitWriter.writeBits_toBits _ lextraN lextraV.toUInt32 hwf1 lextraN_le
              have hwf3 := BitWriter.writeHuffCode_wf _
                (fixedDistCodes[didx]'hdist_bound).1 (fixedDistCodes[didx]'hdist_bound).2
                hwf2 hdlen
              have hbits3 := BitWriter.writeHuffCode_toBits _
                (fixedDistCodes[didx]'hdist_bound).1 (fixedDistCodes[didx]'hdist_bound).2
                hwf2 hdlen
              have hwf4 := BitWriter.writeBits_wf _ dextraN dextraV.toUInt32 hwf3 dextraN_le
              have hbits4 := BitWriter.writeBits_toBits _ dextraN dextraV.toUInt32 hwf3 dextraN_le
              -- Build IH result, expand BitWriter chain on h_ih
              have h_ih := ih _ (i + 1) restBits hwf4 hencrest (by omega)
              rw [hbits4, hbits3, hbits2, hbits1, List.append_assoc, List.append_assoc,
                List.append_assoc, List.append_assoc] at h_ih
              -- Expand spec symbols on goal, normalize UInt32
              rw [hlcw, hdcw]
              have hlextraV_small : lextraV < 2 ^ 32 := Nat.lt_of_lt_of_le
                hflc_spec.2.2.2 (Nat.pow_le_pow_right (by omega) (by omega))
              have hdextraV_small : dextraV < 2 ^ 32 := Nat.lt_of_lt_of_le
                hfdc_spec.2.2.2 (Nat.pow_le_pow_right (by omega) (by omega))
              simp only [Nat.toUInt32, UInt32.ofNat, UInt32.toNat, BitVec.toNat_ofNat,
                show lextraV % 2 ^ 32 = lextraV from Nat.mod_eq_of_lt hlextraV_small,
                show dextraV % 2 ^ 32 = dextraV from Nat.mod_eq_of_lt hdextraV_small,
                List.append_assoc] at h_ih ⊢
              exact h_ih

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
    | none => simp only [hes, bind, Option.bind] at h; exact nomatch h
    | some sBits =>
      cases her : Deflate.Spec.encodeSymbols litLengths distLengths (rest ++ ys) with
      | none => simp only [hes, her, bind, Option.bind] at h; exact nomatch h
      | some restBits =>
        simp only [hes, her, bind, Option.bind, pure, Pure.pure] at h
        have h := Option.some.inj h
        obtain ⟨xBits, yBits, hx, hy, heq⟩ := ih restBits her
        refine ⟨sBits ++ xBits, yBits, ?_, hy, ?_⟩
        · simp only [Deflate.Spec.encodeSymbols, hes, hx, bind, Option.bind, pure, Pure.pure]
        · rw [← h, heq, List.append_assoc]

/-! ## Helper lemmas for deflateFixed_spec -/

/-- `findTableCode.go` returns an index < baseTable.size. -/
theorem findTableCode_go_idx_bound (baseTable : Array UInt16)
    (extraTable : Array UInt8) (value i idx extraN : Nat) (extraV : UInt32)
    (hsize : baseTable.size ≤ extraTable.size)
    (h : findTableCode.go baseTable extraTable value i hsize = some (idx, extraN, extraV)) :
    idx < baseTable.size := by
  unfold findTableCode.go at h
  split at h
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
    · exact findTableCode_go_idx_bound baseTable extraTable value (i + 1) idx extraN extraV hsize h
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
    · exact nomatch h
termination_by baseTable.size - i

/-- `findTableCode.go` returns extraN = extraTable[idx]!.toNat. -/
theorem findTableCode_go_extraN (baseTable : Array UInt16)
    (extraTable : Array UInt8) (value i idx extraN : Nat) (extraV : UInt32)
    (hsize : baseTable.size ≤ extraTable.size)
    (h : findTableCode.go baseTable extraTable value i hsize = some (idx, extraN, extraV)) :
    extraN = extraTable[idx]!.toNat := by
  unfold findTableCode.go at h
  split at h
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]; exact h.2.1.symm
    · exact findTableCode_go_extraN baseTable extraTable value (i + 1) idx extraN extraV hsize h
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]; exact h.2.1.symm
    · exact nomatch h
termination_by baseTable.size - i

/-- Native `findLengthCode` returns idx < 29. -/
theorem nativeFindLengthCode_idx_bound (len idx extraN : Nat) (extraV : UInt32)
    (h : findLengthCode len = some (idx, extraN, extraV)) :
    idx < 29 := by
  have := findTableCode_go_idx_bound _ _ _ _ _ _ _ _ h
  have : Inflate.lengthBase.size = 29 := by rfl
  omega

/-- Native `findLengthCode` returns extraN ≤ 5. -/
theorem nativeFindLengthCode_extraN_bound (len idx extraN : Nat) (extraV : UInt32)
    (h : findLengthCode len = some (idx, extraN, extraV)) :
    extraN ≤ 5 := by
  have hidx := nativeFindLengthCode_idx_bound len idx extraN extraV h
  have hextraN := findTableCode_go_extraN _ _ _ _ _ _ _ _ h
  rw [hextraN]
  have : ∀ j : Fin 29, Inflate.lengthExtra[j.val]!.toNat ≤ 5 := by decide
  exact this ⟨idx, hidx⟩

/-- Native `findDistCode` returns dIdx < 30. -/
theorem nativeFindDistCode_idx_bound (dist dIdx dExtraN : Nat) (dExtraV : UInt32)
    (h : findDistCode dist = some (dIdx, dExtraN, dExtraV)) :
    dIdx < 30 := by
  have := findTableCode_go_idx_bound _ _ _ _ _ _ _ _ h
  have : Inflate.distBase.size = 30 := by rfl
  omega

/-- Native `findDistCode` returns dExtraN ≤ 13. -/
theorem nativeFindDistCode_extraN_bound (dist dIdx dExtraN : Nat) (dExtraV : UInt32)
    (h : findDistCode dist = some (dIdx, dExtraN, dExtraV)) :
    dExtraN ≤ 13 := by
  have hidx := nativeFindDistCode_idx_bound dist dIdx dExtraN dExtraV h
  have hextraN := findTableCode_go_extraN _ _ _ _ _ _ _ _ h
  rw [hextraN]
  have : ∀ j : Fin 30, Inflate.distExtra[j.val]!.toNat ≤ 13 := by decide
  exact this ⟨dIdx, hidx⟩

/-- `canonicalCodes` preserves the array size. -/
theorem canonicalCodes_size (lengths : Array UInt8) (maxBits : Nat := 15) :
    (canonicalCodes lengths maxBits).size = lengths.size := by
  simp only [canonicalCodes]
  rw [Deflate.Correctness.canonicalCodes_go_size]
  simp only [Array.size_replicate]

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
        split <;> simp only [Array.size_set, hsize]
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

/-- `canonicalCodes` entries have `.snd.toNat ≤ bound` (explicit maxBits version). -/
theorem canonicalCodes_snd_le' (lengths : Array UInt8) (maxBits : Nat) (bound : Nat)
    (hlengths : ∀ j, j < lengths.size → lengths[j]!.toNat ≤ bound) (i : Nat)
    (hi : i < (canonicalCodes lengths maxBits).size) :
    (canonicalCodes lengths maxBits)[i]!.2.toNat ≤ bound := by
  simp only [canonicalCodes] at hi ⊢
  apply canonicalCodes_go_snd_le lengths _ 0 _ bound
  · simp only [Array.size_replicate]
  · intro j hj
    simp only [Array.size_replicate] at hj
    rw [getElem!_pos _ _ (by simp only [Array.size_replicate]; omega)]
    simp only [Array.getElem_replicate]; exact Nat.zero_le _
  · exact hlengths
  · exact hi

/-- `canonicalCodes` entries have `.snd.toNat ≤ bound` when all input lengths
    have `.toNat ≤ bound`. -/
theorem canonicalCodes_snd_le (lengths : Array UInt8) (bound : Nat)
    (hlengths : ∀ j, j < lengths.size → lengths[j]!.toNat ≤ bound) (i : Nat)
    (hi : i < (canonicalCodes lengths).size) :
    (canonicalCodes lengths)[i]!.2.toNat ≤ bound :=
  canonicalCodes_snd_le' lengths 15 bound hlengths i hi

/-- All entries in `fixedLitLengths` have `.toNat ≤ 15`. -/
private theorem fixedLitLengths_le_15 (j : Nat) (hj : j < Inflate.fixedLitLengths.size) :
    Inflate.fixedLitLengths[j]!.toNat ≤ 15 := by
  -- fixedLitLengths = replicate 144 8 ++ replicate 112 9 ++ replicate 24 7 ++ replicate 8 8
  simp only [Inflate.fixedLitLengths, Array.size_append, Array.size_replicate] at hj
  show ((Array.replicate 144 (8 : UInt8) ++ Array.replicate 112 9 ++
    Array.replicate 24 7 ++ Array.replicate 8 8)[j]!).toNat ≤ 15
  rw [getElem!_pos _ _ (by simp only [Array.size_append, Array.size_replicate]; omega)]
  simp only [Array.getElem_append, Array.size_append, Array.size_replicate]
  split
  · split
    · split
      · simp only [Array.getElem_replicate]; decide
      · simp only [Array.getElem_replicate]; decide
    · simp only [Array.getElem_replicate]; decide
  · simp only [Array.getElem_replicate]; decide

/-- All entries in `fixedDistLengths` have `.toNat ≤ 15`. -/
private theorem fixedDistLengths_le_15 (j : Nat) (hj : j < Inflate.fixedDistLengths.size) :
    Inflate.fixedDistLengths[j]!.toNat ≤ 15 := by
  simp only [Inflate.fixedDistLengths, Array.size_replicate] at hj ⊢
  rw [getElem!_pos _ _ (by simp only [Array.size_replicate]; omega)]
  simp only [Array.getElem_replicate]; decide

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
      simp only []
      have hb : b.toNat < fixedLitCodes.size := by
        have := Deflate.fixedLitCodes_size
        have : b.toNat < 256 := UInt8.toNat_lt b
        omega
      have hsnd := fixedLitCodes_snd_le b.toNat hb
      rw [getElem!_pos fixedLitCodes b.toNat hb] at hsnd
      exact ih _ (i + 1)
        (BitWriter.writeHuffCode_wf bw
          (fixedLitCodes[b.toNat]'hb).1 (fixedLitCodes[b.toNat]'hb).2 hwf hsnd)
        (by omega)
    | .reference len dist =>
      simp only []
      match hflc_pf : findLengthCode len with
      | none =>
        exact ih _ (i + 1) hwf (by omega)
      | some (idx, extraCount, extraVal) =>
        have hidx := nativeFindLengthCode_idx_bound len idx extraCount extraVal hflc_pf
        have hlit_bound : idx + 257 < fixedLitCodes.size := by
          have := Deflate.fixedLitCodes_size; omega
        -- Resolve the if-guard for lit code bounds
        simp only [dif_pos hlit_bound]
        have hlen_code := fixedLitCodes_snd_le (idx + 257) hlit_bound
        rw [getElem!_pos fixedLitCodes (idx + 257) hlit_bound] at hlen_code
        have hextraN_le : extraCount ≤ 25 := by
          have := nativeFindLengthCode_extraN_bound len idx extraCount extraVal hflc_pf; omega
        have hwf1 := BitWriter.writeHuffCode_wf bw
          (fixedLitCodes[idx + 257]'hlit_bound).1 (fixedLitCodes[idx + 257]'hlit_bound).2
          hwf hlen_code
        have hwf2 := BitWriter.writeBits_wf _ extraCount extraVal hwf1 hextraN_le
        match hfdc_pf : findDistCode dist with
        | none =>
          simp only []
          exact ih _ (i + 1) hwf2 (by omega)
        | some (dIdx, dExtraCount, dExtraVal) =>
          have hdidx := nativeFindDistCode_idx_bound dist dIdx dExtraCount dExtraVal hfdc_pf
          have hdist_bound : dIdx < fixedDistCodes.size := by
            have := Deflate.fixedDistCodes_size; omega
          -- Resolve the if-guard for dist code bounds
          simp only [dif_pos hdist_bound]
          have hdlen_code := fixedDistCodes_snd_le dIdx hdist_bound
          rw [getElem!_pos fixedDistCodes dIdx hdist_bound] at hdlen_code
          have hdextraN_le : dExtraCount ≤ 25 := by
            have := nativeFindDistCode_extraN_bound dist dIdx dExtraCount dExtraVal hfdc_pf; omega
          have hwf3 := BitWriter.writeHuffCode_wf _
            (fixedDistCodes[dIdx]'hdist_bound).1 (fixedDistCodes[dIdx]'hdist_bound).2
            hwf2 hdlen_code
          have hwf4 := BitWriter.writeBits_wf _ dExtraCount dExtraVal hwf3 hdextraN_le
          exact ih _ (i + 1) hwf4 (by omega)

theorem emitTokens_wf (bw : BitWriter) (tokens : Array LZ77Token)
    (hwf : bw.wf) :
    (emitTokens bw tokens 0).wf :=
  emitTokens_wf_go bw tokens 0 hwf

end Zip.Native.Deflate
