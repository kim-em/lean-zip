import Zip.Spec.Deflate
import Zip.Spec.BitstreamCorrect

/-!
# DEFLATE Fixed Huffman Encoding and Level 1 Roundtrip

This file defines the spec-level fixed Huffman block encoder and proves
the end-to-end roundtrip: encoding with greedy LZ77 + fixed Huffman then
decoding recovers the original data.
-/

namespace Deflate.Spec

/-! ## Fixed Huffman block encoding -/

/-- Encode a list of LZ77 symbols as a single fixed-Huffman DEFLATE block.
    Produces BFINAL=1 + BTYPE=01 header followed by Huffman-coded symbols.
    Returns `none` if any symbol cannot be encoded. -/
def encodeFixed (syms : List LZ77Symbol) : Option (List Bool) := do
  let bits ← encodeSymbols fixedLitLengths fixedDistLengths syms
  return [true, true, false] ++ bits

/-! ## Header readback lemmas -/

private theorem readBitsLSB_1_true (rest : List Bool) :
    readBitsLSB 1 (true :: rest) = some (1, rest) := by
  simp [readBitsLSB]

private theorem readBitsLSB_2_true_false (rest : List Bool) :
    readBitsLSB 2 (true :: false :: rest) = some (1, rest) := by
  simp [readBitsLSB]

/-! ## Encoding roundtrip theorems -/

/-- Encoding with fixed Huffman then decoding recovers the original data. -/
theorem encodeFixed_decode (syms : List LZ77Symbol) (data : List UInt8)
    (bits : List Bool)
    (henc : encodeSymbols fixedLitLengths fixedDistLengths syms = some bits)
    (hresolve : resolveLZ77 syms [] = some data)
    (hfuel : 10000000 ≥ syms.length)
    (hvalid : ValidSymbolList syms) :
    decode ([true, true, false] ++ bits) = some data := by
  -- Unfold one step of decode.go
  show decode.go ([true, true, false] ++ bits) [] 10001 = some data
  unfold decode.go
  -- readBitsLSB 1 ([true, true, false] ++ bits) = some (1, [true, false] ++ bits)
  simp only [List.cons_append, readBitsLSB_1_true, bind, Option.bind]
  -- readBitsLSB 2 ([true, false] ++ bits) = some (1, bits)
  simp only [readBitsLSB_2_true_false]
  -- Now in btype = 1 (fixed Huffman) branch
  have hdec : decodeSymbols fixedLitLengths fixedDistLengths bits
      10000000 = some (syms, []) := by
    have := encodeSymbols_decodeSymbols fixedLitLengths fixedDistLengths syms bits []
      10000000 henc fixedLitLengths_valid fixedDistLengths_valid hfuel hvalid
    rwa [List.append_nil] at this
  simp only [List.nil_append]
  rw [hdec]
  simp only [hresolve]
  simp [pure, Pure.pure]

/-! ## encodeSymbol succeeds when symbol is in the table -/

/-- `encodeSymbol` succeeds when the symbol is in the table. -/
theorem encodeSymbol_isSome (table : List (Huffman.Spec.Codeword × Nat))
    (sym : Nat) (cw : Huffman.Spec.Codeword)
    (h : (cw, sym) ∈ table) :
    (encodeSymbol table sym).isSome = true := by
  induction table with
  | nil => simp at h
  | cons entry rest ih =>
    obtain ⟨cw', s'⟩ := entry
    simp only [encodeSymbol]
    split
    · simp
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
    simp [hlen, hmb]
  obtain ⟨cw, hcw⟩ := Option.ne_none_iff_exists'.mp hcf
  have hmem : (sym, cw) ∈ Huffman.Spec.allCodes lengths maxBits :=
    (Huffman.Spec.allCodes_mem_iff ..).mpr ⟨hsym, hcw⟩
  have : (cw, sym) ∈ (Huffman.Spec.allCodes lengths maxBits).map fun (s, cw) => (cw, s) := by
    simp only [List.mem_map]
    exact ⟨(sym, cw), hmem, rfl⟩
  exact encodeSymbol_isSome _ _ _ this

/-! ## findLengthCode and findDistCode coverage -/

/-! ## Fixed table properties -/

/-- All entries in `fixedLitLengths` are between 1 and 15. -/
theorem fixedLitLengths_entry_bounds :
    ∀ x ∈ fixedLitLengths, 1 ≤ x ∧ x ≤ 15 := by
  simp only [fixedLitLengths, List.mem_append, List.mem_replicate]
  intro x hx
  cases hx with
  | inl h => cases h with
    | inl h => cases h with
      | inl h => exact ⟨by omega, by omega⟩
      | inr h => exact ⟨by omega, by omega⟩
    | inr h => exact ⟨by omega, by omega⟩
  | inr h => exact ⟨by omega, by omega⟩

/-- All entries in `fixedDistLengths` are between 1 and 15. -/
theorem fixedDistLengths_entry_bounds :
    ∀ x ∈ fixedDistLengths, 1 ≤ x ∧ x ≤ 15 := by
  simp only [fixedDistLengths, List.mem_replicate]
  omega

/-- For any valid index into fixedLitLengths, the entry is non-zero. -/
theorem fixedLitLengths_getElem_pos (i : Nat) (h : i < fixedLitLengths.length) :
    fixedLitLengths[i]! ≥ 1 := by
  rw [getElem!_pos fixedLitLengths i h]
  have := fixedLitLengths_entry_bounds (fixedLitLengths[i]) (List.getElem_mem h)
  exact this.1

/-- For any valid index into fixedLitLengths, the entry is ≤ 15. -/
theorem fixedLitLengths_getElem_le (i : Nat) (h : i < fixedLitLengths.length) :
    fixedLitLengths[i]! ≤ 15 := by
  rw [getElem!_pos fixedLitLengths i h]
  have := fixedLitLengths_entry_bounds (fixedLitLengths[i]) (List.getElem_mem h)
  exact this.2

/-- For any valid index into fixedDistLengths, the entry is non-zero. -/
theorem fixedDistLengths_getElem_pos (i : Nat) (h : i < fixedDistLengths.length) :
    fixedDistLengths[i]! ≥ 1 := by
  rw [getElem!_pos fixedDistLengths i h]
  have := fixedDistLengths_entry_bounds (fixedDistLengths[i]) (List.getElem_mem h)
  exact this.1

/-- For any valid index into fixedDistLengths, the entry is ≤ 15. -/
theorem fixedDistLengths_getElem_le (i : Nat) (h : i < fixedDistLengths.length) :
    fixedDistLengths[i]! ≤ 15 := by
  rw [getElem!_pos fixedDistLengths i h]
  have := fixedDistLengths_entry_bounds (fixedDistLengths[i]) (List.getElem_mem h)
  exact this.2

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

/-- Helper: `findLengthCode.go i` succeeds when some entry at index ≥ i covers len. -/
private theorem findLengthCode.go_isSome_of_covered (len i : Nat)
    (hi : i < lengthBase.size)
    (hcov : lengthBase[i] ≤ len)
    (hle : len ≤ 258) :
    (findLengthCode.go len i).isSome = true := by
  unfold findLengthCode.go
  simp only [show ¬(i ≥ lengthBase.size) from by omega, dif_neg, not_false_eq_true]
  by_cases hbucket : (decide (lengthBase[i] ≤ len) && decide (len < (lengthBase[i + 1]?.getD 259))) = true
  · simp [hbucket]
  · simp [hbucket]
    -- Not in this bucket, so len ≥ nextBase
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hbucket
    have hge_next : (lengthBase[i + 1]?.getD 259) ≤ len := by
      by_cases h : lengthBase[i] ≤ len
      · simp [h] at hbucket; omega
      · omega
    -- nextBase = lengthBase[i+1] if i+1 < size, else 259
    have hi1 : i + 1 < lengthBase.size := by
      by_cases h : i + 1 < lengthBase.size
      · exact h
      · exfalso
        -- i is the last entry, nextBase = 259
        have hout : ¬(i + 1 < lengthBase.size) := h
        have : (lengthBase[i + 1]?.getD 259) = 259 := by
          have := getElem?_neg lengthBase (i + 1) (by omega)
          simp [this]
        omega
    have hcov' : lengthBase[i + 1] ≤ len := by
      have : lengthBase[i + 1]? = some lengthBase[i + 1] :=
        getElem?_pos lengthBase (i + 1) hi1
      simp [this] at hge_next
      exact hge_next
    exact findLengthCode.go_isSome_of_covered len (i + 1) hi1 hcov' hle
  termination_by lengthBase.size - i

/-- `findLengthCode` succeeds for lengths 3–258. -/
theorem findLengthCode_isSome (len : Nat) (hge : len ≥ 3) (hle : len ≤ 258) :
    (findLengthCode len).isSome = true := by
  simp only [findLengthCode]
  exact findLengthCode.go_isSome_of_covered len 0
    (by simp [lengthBase]) (by simp [lengthBase]; omega) hle

/-- Helper: `findLengthCode.go` returns indices in [i, size). -/
private theorem findLengthCode.go_idx_bound (len i idx extraN extraV : Nat)
    (h : findLengthCode.go len i = some (idx, extraN, extraV)) :
    i ≤ idx ∧ idx < lengthBase.size := by
  unfold findLengthCode.go at h
  split at h
  · simp at h
  · rename_i hsz; simp at hsz
    by_cases hbucket : (decide (lengthBase[i] ≤ len) && decide (len < (lengthBase[i + 1]?.getD 259))) = true
    · simp [hbucket] at h
      obtain ⟨rfl, _, _⟩ := h
      exact ⟨Nat.le.refl, hsz⟩
    · simp [hbucket] at h
      have := findLengthCode.go_idx_bound len (i + 1) idx extraN extraV h
      exact ⟨by omega, this.2⟩
  termination_by lengthBase.size - i

/-- When `findLengthCode` succeeds, the returned index is < 29. -/
theorem findLengthCode_idx_bound (len idx extraN extraV : Nat)
    (h : findLengthCode len = some (idx, extraN, extraV)) :
    idx < 29 := by
  have := (findLengthCode.go_idx_bound len 0 idx extraN extraV h).2
  simp [lengthBase] at this
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
  · simp [hbucket]
  · simp [hbucket]
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hbucket
    have hge_next : (distBase[i + 1]?.getD 32769) ≤ dist := by
      by_cases h : distBase[i] ≤ dist
      · simp [h] at hbucket; omega
      · omega
    have hi1 : i + 1 < distBase.size := by
      by_cases h : i + 1 < distBase.size
      · exact h
      · exfalso
        have := getElem?_neg distBase (i + 1) (by omega)
        simp [this] at hge_next
        omega
    have hcov' : distBase[i + 1] ≤ dist := by
      have : distBase[i + 1]? = some distBase[i + 1] :=
        getElem?_pos distBase (i + 1) hi1
      simp [this] at hge_next
      exact hge_next
    exact findDistCode.go_isSome_of_covered dist (i + 1) hi1 hcov' hle
  termination_by distBase.size - i

/-- `findDistCode` succeeds for distances 1–32768. -/
theorem findDistCode_isSome (dist : Nat) (hge : dist ≥ 1) (hle : dist ≤ 32768) :
    (findDistCode dist).isSome = true := by
  simp only [findDistCode]
  exact findDistCode.go_isSome_of_covered dist 0
    (by simp [distBase]) (by simp [distBase]; omega) hle

/-- Helper: `findDistCode.go` returns codes in [i, size). -/
private theorem findDistCode.go_code_bound (dist i dCode dExtraN dExtraV : Nat)
    (h : findDistCode.go dist i = some (dCode, dExtraN, dExtraV)) :
    i ≤ dCode ∧ dCode < distBase.size := by
  unfold findDistCode.go at h
  split at h
  · simp at h
  · rename_i hsz; simp at hsz
    by_cases hbucket : (decide (distBase[i] ≤ dist) && decide (dist < (distBase[i + 1]?.getD 32769))) = true
    · simp [hbucket] at h
      obtain ⟨rfl, _, _⟩ := h
      exact ⟨Nat.le.refl, hsz⟩
    · simp [hbucket] at h
      have := findDistCode.go_code_bound dist (i + 1) dCode dExtraN dExtraV h
      exact ⟨by omega, this.2⟩
  termination_by distBase.size - i

/-- When `findDistCode` succeeds, the returned code is < 30. -/
theorem findDistCode_code_bound (dist dCode dExtraN dExtraV : Nat)
    (h : findDistCode dist = some (dCode, dExtraN, dExtraV)) :
    dCode < 30 := by
  have := (findDistCode.go_code_bound dist 0 dCode dExtraN dExtraV h).2
  simp [distBase] at this
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
  | none => simp [hlc] at hflc
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
    | none => simp [hls] at hlit
    | some lenBits =>
      simp only [bind, Option.bind]
      -- findDistCode succeeds
      have hfdc := findDistCode_isSome dist hdist_ge hdist_le
      cases hdc : findDistCode dist with
      | none => simp [hdc] at hfdc
      | some q =>
        obtain ⟨dCode, dExtraN, dExtraV⟩ := q
        have hdcode := findDistCode_code_bound dist dCode dExtraN dExtraV hdc
        simp only [bind, Option.bind]
        -- encodeSymbol distTable dCode succeeds
        have hdsym : dCode < fixedDistLengths.length := by
          rw [fixedDistLengths_length]; omega
        have hdist := encodeSymbol_fixed_isSome fixedDistLengths 15 dCode hdsym
          (by have := fixedDistLengths_getElem_pos dCode hdsym; omega)
          (fixedDistLengths_getElem_le dCode hdsym)
        cases hds : encodeSymbol
            ((Huffman.Spec.allCodes fixedDistLengths).map fun (s, cw) => (cw, s)) dCode with
        | none => simp [hds] at hdist
        | some distBits =>
          simp [pure, Pure.pure]

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
  | nil => simp [encodeSymbols]
  | cons s rest ih =>
    simp only [encodeSymbols]
    have hs := h s (List.mem_cons_self ..)
    cases hes : encodeLitLen litLengths distLengths s with
    | none => simp [hes] at hs
    | some bits =>
      simp only [bind, Option.bind]
      have hrest := ih (fun s' hs' => h s' (List.mem_cons_of_mem s hs'))
      cases her : encodeSymbols litLengths distLengths rest with
      | none => simp [her] at hrest
      | some restBits => simp [pure, Pure.pure]

/-! ## matchLZ77 encodability -/

/-- Each symbol emitted by `matchLZ77.go` can be encoded with fixed Huffman. -/
private theorem matchLZ77.go_encodable (data : List UInt8) (pos windowSize : Nat)
    (hws : windowSize ≤ 32768) :
    ∀ s ∈ matchLZ77.go data pos windowSize,
      (encodeLitLen fixedLitLengths fixedDistLengths s).isSome = true := by
  unfold matchLZ77.go
  split
  · -- pos ≥ data.length → [.endOfBlock]
    intro s hs
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hs
    subst hs
    exact encodeLitLen_endOfBlock_isSome
  · -- pos < data.length
    rename_i hlt; simp at hlt
    split
    · -- findLongestMatch = some (len, dist)
      rename_i len dist hfind
      split
      · -- len ≥ 3 → .reference :: go ...
        rename_i hlen3
        intro s hs
        simp only [List.mem_cons] at hs
        cases hs with
        | inl heq =>
          subst heq
          have ⟨hdist_pos, _⟩ := findLongestMatch_dist_bounds _ _ _ _ _ hfind
          have hdist_ws := findLongestMatch_dist_le_windowSize _ _ _ _ _ hfind
          have hml := findLongestMatch_matchLength _ _ _ _ _ hfind
          have hlen_le := matchLength_le_258 data pos dist
          have hlen_ge := findLongestMatch_len_ge _ _ _ _ _ hfind
          exact encodeLitLen_reference_isSome len dist
            (by omega) (by rw [← hml]; exact hlen_le) (by omega) (by omega)
        | inr hmem =>
          exact matchLZ77.go_encodable data _ windowSize hws s hmem
      · -- ¬(len ≥ 3) → literal
        intro s hs
        simp only [List.mem_cons] at hs
        cases hs with
        | inl heq => subst heq; exact encodeLitLen_literal_isSome _
        | inr hmem => exact matchLZ77.go_encodable data _ windowSize hws s hmem
    · -- findLongestMatch = none → literal
      intro s hs
      simp only [List.mem_cons] at hs
      cases hs with
      | inl heq => subst heq; exact encodeLitLen_literal_isSome _
      | inr hmem => exact matchLZ77.go_encodable data _ windowSize hws s hmem
termination_by data.length - pos
decreasing_by all_goals omega

/-- The greedy LZ77 matcher produces symbols that can be encoded with
    fixed Huffman tables (symbols 0–285 for lit/len, 0–29 for dist). -/
theorem matchLZ77_encodable (data : List UInt8) (windowSize : Nat)
    (hws : windowSize ≤ 32768) :
    (encodeSymbols fixedLitLengths fixedDistLengths
      (matchLZ77 data windowSize)).isSome = true :=
  encodeSymbols_isSome_of_all _ _ _ (matchLZ77.go_encodable data 0 windowSize hws)

/-! ## matchLZ77 produces valid symbol lists -/

private theorem matchLZ77.go_validSymbolList (data : List UInt8) (pos windowSize : Nat) :
    ValidSymbolList (matchLZ77.go data pos windowSize) := by
  unfold matchLZ77.go
  split
  · -- pos ≥ data.length → [.endOfBlock]
    exact trivial
  · -- pos < data.length
    split
    · -- findLongestMatch = some (len, dist)
      split
      · -- len ≥ 3 → .reference :: go ...
        exact matchLZ77.go_validSymbolList data _ windowSize
      · -- ¬(len ≥ 3) → .literal :: go ...
        exact matchLZ77.go_validSymbolList data _ windowSize
    · -- findLongestMatch = none → .literal :: go ...
      exact matchLZ77.go_validSymbolList data _ windowSize
termination_by data.length - pos
decreasing_by all_goals omega

/-- The greedy LZ77 matcher produces a valid symbol list
    (ends with exactly one endOfBlock). -/
theorem matchLZ77_validSymbolList (data : List UInt8) (windowSize : Nat) :
    ValidSymbolList (matchLZ77 data windowSize) :=
  matchLZ77.go_validSymbolList data 0 windowSize

/-! ## matchLZ77 symbol list length bound -/

private theorem matchLZ77.go_length_le (data : List UInt8) (pos windowSize : Nat) :
    (matchLZ77.go data pos windowSize).length ≤ data.length - pos + 1 := by
  unfold matchLZ77.go
  split
  · -- pos ≥ data.length → [.endOfBlock]
    simp
  · -- pos < data.length
    rename_i hlt; simp at hlt
    split
    · -- findLongestMatch = some (len, dist)
      rename_i len dist hfind
      split
      · -- len ≥ 3
        rename_i hlen3
        simp only [List.length_cons]
        have ih := matchLZ77.go_length_le data (pos + len) windowSize
        omega
      · -- ¬(len ≥ 3) → literal
        simp only [List.length_cons]
        have ih := matchLZ77.go_length_le data (pos + 1) windowSize
        omega
    · -- findLongestMatch = none → literal
      simp only [List.length_cons]
      have ih := matchLZ77.go_length_le data (pos + 1) windowSize
      omega
termination_by data.length - pos
decreasing_by all_goals omega

/-- `matchLZ77` produces at most `data.length + 1` symbols. -/
theorem matchLZ77_length_le (data : List UInt8) (windowSize : Nat) :
    (matchLZ77 data windowSize).length ≤ data.length + 1 := by
  have := matchLZ77.go_length_le data 0 windowSize
  simp at this
  exact this

/-- Level 1 roundtrip (conditional): greedy LZ77 + fixed Huffman encoding
    then decoding recovers the original data. Requires explicit encoding
    hypothesis. -/
theorem deflateLevel1_spec_roundtrip (data : List UInt8)
    (windowSize : Nat) (hw : windowSize > 0)
    (bits : List Bool)
    (henc : encodeSymbols fixedLitLengths fixedDistLengths
      (matchLZ77 data windowSize) = some bits)
    (hfuel : 10000000 ≥ (matchLZ77 data windowSize).length)
    (hvalid : ValidSymbolList (matchLZ77 data windowSize)) :
    decode ([true, true, false] ++ bits) = some data :=
  encodeFixed_decode (matchLZ77 data windowSize) data bits henc
    (resolveLZ77_matchLZ77 data windowSize hw) hfuel hvalid

/-- Level 1 spec roundtrip (existential form): for any data, encoding with
    greedy LZ77 + fixed Huffman produces bits that decode back to the
    original data. Uses `matchLZ77_encodable` and `matchLZ77_validSymbolList`
    to eliminate all side conditions.
    Note: the `hfuel` hypothesis requires `data.length < 10000000`
    (about 10MB), which is easily satisfied in practice. -/
theorem deflateLevel1_spec_roundtrip' (data : List UInt8)
    (windowSize : Nat) (hw : windowSize > 0) (hws : windowSize ≤ 32768)
    (hsize : data.length < 10000000) :
    ∃ bits, encodeFixed (matchLZ77 data windowSize) = some bits ∧
            decode bits = some data := by
  have henc_some := matchLZ77_encodable data windowSize hws
  cases henc : encodeSymbols fixedLitLengths fixedDistLengths (matchLZ77 data windowSize) with
  | none => simp [henc] at henc_some
  | some bits =>
    refine ⟨[true, true, false] ++ bits, ?_, ?_⟩
    · simp [encodeFixed, henc]
    · exact deflateLevel1_spec_roundtrip data windowSize hw bits henc
        (by have := matchLZ77_length_le data windowSize; omega)
        (matchLZ77_validSymbolList data windowSize)

/-! ## matchLZ77Lazy validity and symbol list properties -/

private theorem matchLZ77Lazy.go_validSymbolList (data : List UInt8) (pos windowSize : Nat) :
    ValidSymbolList (matchLZ77Lazy.go data pos windowSize) := by
  unfold matchLZ77Lazy.go
  split
  · exact trivial
  · split
    · split
      · exact matchLZ77Lazy.go_validSymbolList data _ windowSize
      · split
        · split
          · split
            · exact matchLZ77Lazy.go_validSymbolList data _ windowSize
            · exact matchLZ77Lazy.go_validSymbolList data _ windowSize
          · exact matchLZ77Lazy.go_validSymbolList data _ windowSize
        · exact matchLZ77Lazy.go_validSymbolList data _ windowSize
    · exact matchLZ77Lazy.go_validSymbolList data _ windowSize
termination_by data.length - pos
decreasing_by all_goals omega

/-- The lazy LZ77 matcher produces a valid symbol list
    (ends with exactly one endOfBlock). -/
theorem matchLZ77Lazy_validSymbolList (data : List UInt8) (windowSize : Nat) :
    ValidSymbolList (matchLZ77Lazy data windowSize) :=
  matchLZ77Lazy.go_validSymbolList data 0 windowSize

/-! ## matchLZ77Lazy symbol list length bound -/

private theorem matchLZ77Lazy.go_length_le (data : List UInt8) (pos windowSize : Nat) :
    (matchLZ77Lazy.go data pos windowSize).length ≤ 2 * (data.length - pos) + 1 := by
  unfold matchLZ77Lazy.go
  split
  · simp
  · rename_i hlt; simp at hlt
    split
    · rename_i len1 dist1 _
      split
      · simp only [List.length_cons]
        have ih := matchLZ77Lazy.go_length_le data (pos + 1) windowSize
        omega
      · split
        · split
          · rename_i len2 dist2 _
            split
            · simp only [List.length_cons]
              have ih := matchLZ77Lazy.go_length_le data (pos + 1 + len2) windowSize
              omega
            · simp only [List.length_cons]
              have ih := matchLZ77Lazy.go_length_le data (pos + len1) windowSize
              omega
          · simp only [List.length_cons]
            have ih := matchLZ77Lazy.go_length_le data (pos + len1) windowSize
            omega
        · simp only [List.length_cons]
          have ih := matchLZ77Lazy.go_length_le data (pos + len1) windowSize
          omega
    · simp only [List.length_cons]
      have ih := matchLZ77Lazy.go_length_le data (pos + 1) windowSize
      omega
termination_by data.length - pos
decreasing_by all_goals omega

/-- `matchLZ77Lazy` produces at most `2 * data.length + 1` symbols. -/
theorem matchLZ77Lazy_length_le (data : List UInt8) (windowSize : Nat) :
    (matchLZ77Lazy data windowSize).length ≤ 2 * data.length + 1 := by
  have := matchLZ77Lazy.go_length_le data 0 windowSize
  simp at this
  exact this

/-! ## matchLZ77Lazy encodability -/

/-- Each symbol emitted by `matchLZ77Lazy.go` can be encoded with fixed Huffman. -/
private theorem matchLZ77Lazy.go_encodable (data : List UInt8) (pos windowSize : Nat)
    (hws : windowSize ≤ 32768) :
    ∀ s ∈ matchLZ77Lazy.go data pos windowSize,
      (encodeLitLen fixedLitLengths fixedDistLengths s).isSome = true := by
  unfold matchLZ77Lazy.go
  split
  · -- pos ≥ data.length → [.endOfBlock]
    intro s hs
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hs
    subst hs; exact encodeLitLen_endOfBlock_isSome
  · -- pos < data.length
    split
    · -- findLongestMatch = some (len1, dist1)
      rename_i len1 dist1 hfind1
      split
      · -- len1 < 3 → literal :: go ...
        intro s hs; simp only [List.mem_cons] at hs
        cases hs with
        | inl heq => subst heq; exact encodeLitLen_literal_isSome _
        | inr hmem => exact matchLZ77Lazy.go_encodable data _ windowSize hws s hmem
      · -- len1 ≥ 3
        split
        · -- pos + 1 < data.length
          split
          · -- some (len2, dist2)
            rename_i len2 dist2 hfind2
            split
            · -- len2 > len1 → literal :: reference :: go ...
              intro s hs; simp only [List.mem_cons] at hs
              cases hs with
              | inl heq => subst heq; exact encodeLitLen_literal_isSome _
              | inr hmem =>
                cases hmem with
                | inl heq =>
                  subst heq
                  have ⟨hdist2_pos, _⟩ := findLongestMatch_dist_bounds _ _ _ _ _ hfind2
                  have hdist2_ws := findLongestMatch_dist_le_windowSize _ _ _ _ _ hfind2
                  have hml2 := findLongestMatch_matchLength _ _ _ _ _ hfind2
                  have hlen2_ge := findLongestMatch_len_ge _ _ _ _ _ hfind2
                  exact encodeLitLen_reference_isSome len2 dist2
                    (by omega) (by rw [← hml2]; exact matchLength_le_258 data _ _)
                    (by omega) (by omega)
                | inr hmem => exact matchLZ77Lazy.go_encodable data _ windowSize hws s hmem
            · -- len2 ≤ len1 → reference :: go ...
              intro s hs; simp only [List.mem_cons] at hs
              cases hs with
              | inl heq =>
                subst heq
                have ⟨hdist1_pos, _⟩ := findLongestMatch_dist_bounds _ _ _ _ _ hfind1
                have hdist1_ws := findLongestMatch_dist_le_windowSize _ _ _ _ _ hfind1
                have hml1 := findLongestMatch_matchLength _ _ _ _ _ hfind1
                have hlen1_ge := findLongestMatch_len_ge _ _ _ _ _ hfind1
                exact encodeLitLen_reference_isSome len1 dist1
                  (by omega) (by rw [← hml1]; exact matchLength_le_258 data _ _)
                  (by omega) (by omega)
              | inr hmem => exact matchLZ77Lazy.go_encodable data _ windowSize hws s hmem
          · -- none → reference :: go ...
            intro s hs; simp only [List.mem_cons] at hs
            cases hs with
            | inl heq =>
              subst heq
              have ⟨hdist1_pos, _⟩ := findLongestMatch_dist_bounds _ _ _ _ _ hfind1
              have hdist1_ws := findLongestMatch_dist_le_windowSize _ _ _ _ _ hfind1
              have hml1 := findLongestMatch_matchLength _ _ _ _ _ hfind1
              have hlen1_ge := findLongestMatch_len_ge _ _ _ _ _ hfind1
              exact encodeLitLen_reference_isSome len1 dist1
                (by omega) (by rw [← hml1]; exact matchLength_le_258 data _ _)
                (by omega) (by omega)
            | inr hmem => exact matchLZ77Lazy.go_encodable data _ windowSize hws s hmem
        · -- ¬(pos + 1 < data.length) → reference :: go ...
          intro s hs; simp only [List.mem_cons] at hs
          cases hs with
          | inl heq =>
            subst heq
            have ⟨hdist1_pos, _⟩ := findLongestMatch_dist_bounds _ _ _ _ _ hfind1
            have hdist1_ws := findLongestMatch_dist_le_windowSize _ _ _ _ _ hfind1
            have hml1 := findLongestMatch_matchLength _ _ _ _ _ hfind1
            have hlen1_ge := findLongestMatch_len_ge _ _ _ _ _ hfind1
            exact encodeLitLen_reference_isSome len1 dist1
              (by omega) (by rw [← hml1]; exact matchLength_le_258 data _ _)
              (by omega) (by omega)
          | inr hmem => exact matchLZ77Lazy.go_encodable data _ windowSize hws s hmem
    · -- findLongestMatch = none → literal :: go ...
      intro s hs; simp only [List.mem_cons] at hs
      cases hs with
      | inl heq => subst heq; exact encodeLitLen_literal_isSome _
      | inr hmem => exact matchLZ77Lazy.go_encodable data _ windowSize hws s hmem
termination_by data.length - pos
decreasing_by all_goals omega

/-- The lazy LZ77 matcher produces symbols that can be encoded with
    fixed Huffman tables. -/
theorem matchLZ77Lazy_encodable (data : List UInt8) (windowSize : Nat)
    (hws : windowSize ≤ 32768) :
    (encodeSymbols fixedLitLengths fixedDistLengths
      (matchLZ77Lazy data windowSize)).isSome = true :=
  encodeSymbols_isSome_of_all _ _ _ (matchLZ77Lazy.go_encodable data 0 windowSize hws)

/-! ## Level 2 spec roundtrip -/

/-- Level 2 spec roundtrip (existential form): for any data, encoding with
    lazy LZ77 + fixed Huffman produces bits that decode back to the
    original data. -/
theorem deflateLevel2_spec_roundtrip (data : List UInt8)
    (windowSize : Nat) (hw : windowSize > 0) (hws : windowSize ≤ 32768)
    (hsize : data.length < 5000000) :
    ∃ bits, encodeFixed (matchLZ77Lazy data windowSize) = some bits ∧
            decode bits = some data := by
  have henc_some := matchLZ77Lazy_encodable data windowSize hws
  cases henc : encodeSymbols fixedLitLengths fixedDistLengths (matchLZ77Lazy data windowSize) with
  | none => simp [henc] at henc_some
  | some bits =>
    refine ⟨[true, true, false] ++ bits, ?_, ?_⟩
    · simp [encodeFixed, henc]
    · exact encodeFixed_decode (matchLZ77Lazy data windowSize) data bits henc
        (resolveLZ77_matchLZ77Lazy data windowSize hw)
        (by have := matchLZ77Lazy_length_le data windowSize; omega)
        (matchLZ77Lazy_validSymbolList data windowSize)

end Deflate.Spec
