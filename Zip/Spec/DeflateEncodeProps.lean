import Zip.Spec.DeflateEncode

/-!
# DEFLATE Encoding Success Properties

Proofs that encoding functions succeed for symbols within valid ranges:
- `encodeSymbol_isSome`: encoding succeeds when symbol is in the table
- `encodeLitLen_literal_isSome`, `encodeLitLen_endOfBlock_isSome`,
  `encodeLitLen_reference_isSome`: fixed Huffman encoding succeeds for each symbol type
- `encodeSymbols_isSome_of_all`: bulk encoding succeeds when each symbol is encodable
- Fixed table entry bounds (`fixedLitLengths_entry_bounds`, etc.)
- `findLengthCode_isSome`, `findDistCode_isSome`: code table coverage
-/

namespace Deflate.Spec

/-! ## encodeSymbol succeeds when symbol is in the table -/

/-- `encodeSymbol` succeeds when the symbol is in the table. -/
theorem encodeSymbol_isSome (table : List (Huffman.Spec.Codeword × Nat))
    (sym : Nat) (cw : Huffman.Spec.Codeword)
    (h : (cw, sym) ∈ table) :
    (encodeSymbol table sym).isSome = true := by
  induction table with
  | nil => simp only [List.not_mem_nil] at h
  | cons entry rest ih =>
    obtain ⟨cw', s'⟩ := entry
    simp only [encodeSymbol]
    split
    · simp only [Option.isSome_some]
    · rename_i hne
      simp only [beq_iff_eq] at hne
      simp only [List.mem_cons, Prod.mk.injEq] at h
      exact h.elim (fun heq => absurd heq.2.symm hne) ih

/-- `encodeSymbol` on a flipped `allCodes` table succeeds when the symbol
    has a non-zero code length. -/
theorem encodeSymbol_fixed_isSome (lengths : List Nat) (maxBits : Nat)
    (sym : Nat) (hsym : sym < lengths.length)
    (hlen : lengths[sym]! ≠ 0) (hmb : lengths[sym]! ≤ maxBits) :
    (encodeSymbol
      ((Huffman.Spec.allCodes lengths maxBits).map fun (s, cw) => (cw, s))
      sym).isSome = true := by
  have hcf : Huffman.Spec.codeFor lengths maxBits sym ≠ none := by
    simp only [Huffman.Spec.codeFor, dif_pos hsym]
    rw [getElem!_pos lengths sym hsym] at hlen hmb
    simp only [gt_iff_lt, Bool.or_eq_true, beq_iff_eq, hlen, decide_eq_true_eq, false_or, ne_eq,
      ite_eq_left_iff, Nat.not_lt, hmb, reduceCtorEq, imp_false, not_true_eq_false,
      not_false_eq_true]
  obtain ⟨cw, hcw⟩ := Option.ne_none_iff_exists'.mp hcf
  have hmem : (sym, cw) ∈ Huffman.Spec.allCodes lengths maxBits :=
    (Huffman.Spec.allCodes_mem_iff ..).mpr ⟨hsym, hcw⟩
  have : (cw, sym) ∈ (Huffman.Spec.allCodes lengths maxBits).map fun (s, cw) => (cw, s) := by
    simp only [List.mem_map]
    exact ⟨(sym, cw), hmem, rfl⟩
  exact encodeSymbol_isSome _ _ _ this

/-! ## Fixed table properties -/

/-- All entries in `fixedLitLengths` are between 1 and 15. -/
theorem fixedLitLengths_entry_bounds :
    ∀ x ∈ fixedLitLengths, 1 ≤ x ∧ x ≤ 15 := by
  simp only [fixedLitLengths, List.mem_append, List.mem_replicate]
  intro x hx
  obtain ((h | h) | h) | h := hx <;> omega

/-- All entries in `fixedDistLengths` are between 1 and 15. -/
theorem fixedDistLengths_entry_bounds :
    ∀ x ∈ fixedDistLengths, 1 ≤ x ∧ x ≤ 15 := by
  simp only [fixedDistLengths, List.mem_replicate]
  omega

/-- For any valid index into fixedLitLengths, the entry is non-zero. -/
theorem fixedLitLengths_getElem_pos (i : Nat) (h : i < fixedLitLengths.length) :
    fixedLitLengths[i]! ≥ 1 := by
  rw [getElem!_pos fixedLitLengths i h]
  exact (fixedLitLengths_entry_bounds _ (List.getElem_mem h)).1

/-- For any valid index into fixedLitLengths, the entry is ≤ 15. -/
theorem fixedLitLengths_getElem_le (i : Nat) (h : i < fixedLitLengths.length) :
    fixedLitLengths[i]! ≤ 15 := by
  rw [getElem!_pos fixedLitLengths i h]
  exact (fixedLitLengths_entry_bounds _ (List.getElem_mem h)).2

/-- For any valid index into fixedDistLengths, the entry is non-zero. -/
theorem fixedDistLengths_getElem_pos (i : Nat) (h : i < fixedDistLengths.length) :
    fixedDistLengths[i]! ≥ 1 := by
  rw [getElem!_pos fixedDistLengths i h]
  exact (fixedDistLengths_entry_bounds _ (List.getElem_mem h)).1

/-- For any valid index into fixedDistLengths, the entry is ≤ 15. -/
theorem fixedDistLengths_getElem_le (i : Nat) (h : i < fixedDistLengths.length) :
    fixedDistLengths[i]! ≤ 15 := by
  rw [getElem!_pos fixedDistLengths i h]
  exact (fixedDistLengths_entry_bounds _ (List.getElem_mem h)).2

/-! ## encodeLitLen succeeds for matchLZ77 symbols -/

/-- `encodeLitLen` succeeds for literal bytes with fixed Huffman tables. -/
theorem encodeLitLen_literal_isSome (b : UInt8) :
    (encodeLitLen fixedLitLengths fixedDistLengths (.literal b)).isSome = true := by
  simp only [encodeLitLen]
  have hlt : b.toNat < 288 := by have := UInt8.toNat_lt b; omega
  have hsym : b.toNat < fixedLitLengths.length := by rw [fixedLitLengths_length]; exact hlt
  exact encodeSymbol_fixed_isSome fixedLitLengths 15 b.toNat hsym
    (by have := fixedLitLengths_getElem_pos b.toNat hsym; omega)
    (fixedLitLengths_getElem_le b.toNat hsym)

/-- `encodeLitLen` succeeds for endOfBlock with fixed Huffman tables. -/
theorem encodeLitLen_endOfBlock_isSome :
    (encodeLitLen fixedLitLengths fixedDistLengths .endOfBlock).isSome = true := by
  simp only [encodeLitLen]
  have hsym : 256 < fixedLitLengths.length := by rw [fixedLitLengths_length]; omega
  exact encodeSymbol_fixed_isSome fixedLitLengths 15 256 hsym
    (by have := fixedLitLengths_getElem_pos 256 hsym; omega)
    (fixedLitLengths_getElem_le 256 hsym)

/-! ## findLengthCode and findDistCode coverage -/

/-- Helper: `findLengthCode.go i` succeeds when some entry at index ≥ i covers len. -/
private theorem findLengthCode.go_isSome_of_covered (len i : Nat)
    (hi : i < lengthBase.size)
    (hcov : lengthBase[i] ≤ len)
    (hle : len ≤ 258) :
    (findLengthCode.go len i).isSome = true := by
  unfold findLengthCode.go
  simp only [show ¬(i ≥ lengthBase.size) from by omega, dif_neg, not_false_eq_true]
  by_cases hbucket : (decide (lengthBase[i] ≤ len) && decide (len < (lengthBase[i + 1]?.getD 259))) = true
  · simp only [hbucket, ↓reduceIte, Option.isSome_some]
  · simp only [hbucket, Bool.false_eq_true, ↓reduceIte]
    -- Not in this bucket, so len ≥ nextBase
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hbucket
    have hge_next : (lengthBase[i + 1]?.getD 259) ≤ len := by
      by_cases h : lengthBase[i] ≤ len
      · simp only [h, true_and, Nat.not_lt] at hbucket; omega
      · omega
    -- nextBase = lengthBase[i+1] if i+1 < size, else 259
    have hi1 : i + 1 < lengthBase.size := by
      by_cases h : i + 1 < lengthBase.size
      · exact h
      · exfalso
        have : (lengthBase[i + 1]?.getD 259) = 259 := by
          simp only [getElem?_neg lengthBase (i + 1) (by omega), Option.getD_none]
        omega
    have hcov' : lengthBase[i + 1] ≤ len := by
      have : lengthBase[i + 1]? = some lengthBase[i + 1] :=
        getElem?_pos lengthBase (i + 1) hi1
      simp only [this, Option.getD_some] at hge_next
      exact hge_next
    exact findLengthCode.go_isSome_of_covered len (i + 1) hi1 hcov' hle
  termination_by lengthBase.size - i

/-- `findLengthCode` succeeds for lengths 3–258. -/
theorem findLengthCode_isSome (len : Nat) (hge : len ≥ 3) (hle : len ≤ 258) :
    (findLengthCode len).isSome = true := by
  simp only [findLengthCode]
  exact findLengthCode.go_isSome_of_covered len 0
    (by simp only [lengthBase, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add,
      Nat.reduceAdd, Nat.zero_lt_succ])
    (by simp only [lengthBase, List.getElem_toArray, List.getElem_cons_zero]; omega) hle

/-- Helper: `findLengthCode.go` returns indices in [i, size). -/
private theorem findLengthCode.go_idx_bound (len i idx extraN extraV : Nat)
    (h : findLengthCode.go len i = some (idx, extraN, extraV)) :
    i ≤ idx ∧ idx < lengthBase.size := by
  unfold findLengthCode.go at h
  split at h
  · simp only [reduceCtorEq] at h
  · rename_i hsz; simp only [ge_iff_le, Nat.not_le] at hsz
    by_cases hbucket : (decide (lengthBase[i] ≤ len) && decide (len < (lengthBase[i + 1]?.getD 259))) = true
    · simp only [hbucket, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _, _⟩ := h
      exact ⟨Nat.le.refl, hsz⟩
    · simp only [hbucket, Bool.false_eq_true, ↓reduceIte] at h
      have := findLengthCode.go_idx_bound len (i + 1) idx extraN extraV h
      exact ⟨by omega, this.2⟩
  termination_by lengthBase.size - i

/-- When `findLengthCode` succeeds, the returned index is < 29. -/
theorem findLengthCode_idx_bound (len idx extraN extraV : Nat)
    (h : findLengthCode len = some (idx, extraN, extraV)) :
    idx < 29 := by
  have := (findLengthCode.go_idx_bound len 0 idx extraN extraV h).2
  simp only [lengthBase, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add,
    Nat.reduceAdd] at this
  exact this

/-- Helper: `findDistCode.go i` succeeds when distBase[i] ≤ dist ≤ 32768. -/
private theorem findDistCode.go_isSome_of_covered (dist i : Nat)
    (hi : i < distBase.size)
    (hcov : distBase[i] ≤ dist)
    (hle : dist ≤ 32768) :
    (findDistCode.go dist i).isSome = true := by
  unfold findDistCode.go
  simp only [show ¬(i ≥ distBase.size) from by omega, dif_neg, not_false_eq_true]
  by_cases hbucket : (decide (distBase[i] ≤ dist) && decide (dist < (distBase[i + 1]?.getD 32769))) = true
  · simp only [hbucket, ↓reduceIte, Option.isSome_some]
  · simp only [hbucket, Bool.false_eq_true, ↓reduceIte]
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hbucket
    have hge_next : (distBase[i + 1]?.getD 32769) ≤ dist := by
      by_cases h : distBase[i] ≤ dist
      · simp only [h, true_and, Nat.not_lt] at hbucket; omega
      · omega
    have hi1 : i + 1 < distBase.size := by
      by_cases h : i + 1 < distBase.size
      · exact h
      · exfalso
        have := getElem?_neg distBase (i + 1) (by omega)
        simp only [this, Option.getD_none] at hge_next
        omega
    have hcov' : distBase[i + 1] ≤ dist := by
      have : distBase[i + 1]? = some distBase[i + 1] :=
        getElem?_pos distBase (i + 1) hi1
      simp only [this, Option.getD_some] at hge_next
      exact hge_next
    exact findDistCode.go_isSome_of_covered dist (i + 1) hi1 hcov' hle
  termination_by distBase.size - i

/-- `findDistCode` succeeds for distances 1–32768. -/
theorem findDistCode_isSome (dist : Nat) (hge : dist ≥ 1) (hle : dist ≤ 32768) :
    (findDistCode dist).isSome = true := by
  simp only [findDistCode]
  exact findDistCode.go_isSome_of_covered dist 0
    (by simp only [distBase, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add,
      Nat.reduceAdd, Nat.zero_lt_succ])
    (by simp only [distBase, List.getElem_toArray, List.getElem_cons_zero]; omega) hle

/-- Helper: `findDistCode.go` returns codes in [i, size). -/
private theorem findDistCode.go_code_bound (dist i dCode dExtraN dExtraV : Nat)
    (h : findDistCode.go dist i = some (dCode, dExtraN, dExtraV)) :
    i ≤ dCode ∧ dCode < distBase.size := by
  unfold findDistCode.go at h
  split at h
  · simp only [reduceCtorEq] at h
  · rename_i hsz; simp only [ge_iff_le, Nat.not_le] at hsz
    by_cases hbucket : (decide (distBase[i] ≤ dist) && decide (dist < (distBase[i + 1]?.getD 32769))) = true
    · simp only [hbucket, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _, _⟩ := h
      exact ⟨Nat.le.refl, hsz⟩
    · simp only [hbucket, Bool.false_eq_true, ↓reduceIte] at h
      have := findDistCode.go_code_bound dist (i + 1) dCode dExtraN dExtraV h
      exact ⟨by omega, this.2⟩
  termination_by distBase.size - i

/-- When `findDistCode` succeeds, the returned code is < 30. -/
theorem findDistCode_code_bound (dist dCode dExtraN dExtraV : Nat)
    (h : findDistCode dist = some (dCode, dExtraN, dExtraV)) :
    dCode < 30 := by
  have := (findDistCode.go_code_bound dist 0 dCode dExtraN dExtraV h).2
  simp only [distBase, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add,
    Nat.reduceAdd] at this
  exact this

/-- `encodeLitLen` succeeds for references with appropriate bounds. -/
theorem encodeLitLen_reference_isSome (len dist : Nat)
    (hlen_ge : len ≥ 3) (hlen_le : len ≤ 258)
    (hdist_ge : dist ≥ 1) (hdist_le : dist ≤ 32768) :
    (encodeLitLen fixedLitLengths fixedDistLengths
      (.reference len dist)).isSome = true := by
  simp only [encodeLitLen]
  -- findLengthCode succeeds
  have hflc := findLengthCode_isSome len hlen_ge hlen_le
  cases hlc : findLengthCode len with
  | none => simp only [hlc, Option.isSome_none, Bool.false_eq_true] at hflc
  | some p =>
    obtain ⟨idx, extraN, extraV⟩ := p
    have hidx := findLengthCode_idx_bound len idx extraN extraV hlc
    simp only [bind, Option.bind]
    -- encodeSymbol litTable (257 + idx) succeeds
    have hsym : 257 + idx < fixedLitLengths.length := by
      rw [fixedLitLengths_length]; omega
    have hlit := encodeSymbol_fixed_isSome fixedLitLengths 15 (257 + idx) hsym
      (by have := fixedLitLengths_getElem_pos (257 + idx) hsym; omega)
      (fixedLitLengths_getElem_le (257 + idx) hsym)
    cases hls : encodeSymbol
        ((Huffman.Spec.allCodes fixedLitLengths).map fun (s, cw) => (cw, s)) (257 + idx) with
    | none => simp only [hls, Option.isSome_none, Bool.false_eq_true] at hlit
    | some lenBits =>
      dsimp only [bind, Option.bind]
      -- findDistCode succeeds
      have hfdc := findDistCode_isSome dist hdist_ge hdist_le
      cases hdc : findDistCode dist with
      | none => simp only [hdc, Option.isSome_none, Bool.false_eq_true] at hfdc
      | some q =>
        obtain ⟨dCode, dExtraN, dExtraV⟩ := q
        have hdcode := findDistCode_code_bound dist dCode dExtraN dExtraV hdc
        dsimp only [bind]
        -- encodeSymbol distTable dCode succeeds
        have hdsym : dCode < fixedDistLengths.length := by
          rw [fixedDistLengths_length]; omega
        have hdist := encodeSymbol_fixed_isSome fixedDistLengths 15 dCode hdsym
          (by have := fixedDistLengths_getElem_pos dCode hdsym; omega)
          (fixedDistLengths_getElem_le dCode hdsym)
        cases hds : encodeSymbol
            ((Huffman.Spec.allCodes fixedDistLengths).map fun (s, cw) => (cw, s)) dCode with
        | none => simp only [hds, Option.isSome_none, Bool.false_eq_true] at hdist
        | some distBits =>
          simp only [pure, List.append_assoc, Option.isSome_some]

/-- `matchLength` returns at most 258 (the default maxLen). -/
theorem matchLength_le_258 (data : List UInt8) (pos dist : Nat) :
    matchLength data pos dist ≤ 258 := by
  unfold matchLength
  split
  · omega
  · exact (matchLength.go_bounds data pos dist 0 258 (by omega)).2

/-- `encodeSymbols` succeeds when `encodeLitLen` succeeds for each symbol. -/
theorem encodeSymbols_isSome_of_all (litLengths distLengths : List Nat)
    (syms : List LZ77Symbol)
    (h : ∀ s ∈ syms, (encodeLitLen litLengths distLengths s).isSome = true) :
    (encodeSymbols litLengths distLengths syms).isSome = true := by
  induction syms with
  | nil => simp only [encodeSymbols, Option.isSome_some]
  | cons s rest ih =>
    simp only [encodeSymbols]
    have hs := h s (List.mem_cons_self ..)
    cases hes : encodeLitLen litLengths distLengths s with
    | none => simp only [hes, Option.isSome_none, Bool.false_eq_true] at hs
    | some bits =>
      simp only [bind, Option.bind]
      have hrest := ih (fun s' hs' => h s' (List.mem_cons_of_mem s hs'))
      cases her : encodeSymbols litLengths distLengths rest with
      | none => simp only [her, Option.isSome_none, Bool.false_eq_true] at hrest
      | some restBits => simp only [pure, Option.isSome_some]

end Deflate.Spec
