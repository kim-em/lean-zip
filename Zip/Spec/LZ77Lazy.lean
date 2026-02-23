import Zip.Spec.DeflateEncode
import Zip.Spec.LZ77

/-!
# LZ77→Encode Bridge and Lazy LZ77 Matcher

Proofs connecting LZ77 matchers to DEFLATE encoding:
- `matchLZ77_encodable`: greedy matcher symbols are encodable with fixed Huffman
- `matchLZ77_validSymbolList`, `matchLZ77_length_le`: structural properties
- `deflateLevel1_spec_roundtrip`: Level 1 (greedy) encode/decode roundtrip
- `matchLZ77Lazy_*`: lazy matcher validity, length bounds, encodability
- `deflateLevel2_spec_roundtrip`: Level 2 (lazy) encode/decode roundtrip
-/

namespace Deflate.Spec

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
        -- Factor out: reference M1 is always encodable
        have henc_m1 : (encodeLitLen fixedLitLengths fixedDistLengths
            (.reference len1 dist1)).isSome = true := by
          have ⟨hdist1_pos, _⟩ := findLongestMatch_dist_bounds _ _ _ _ _ hfind1
          have hdist1_ws := findLongestMatch_dist_le_windowSize _ _ _ _ _ hfind1
          have hml1 := findLongestMatch_matchLength _ _ _ _ _ hfind1
          exact encodeLitLen_reference_isSome len1 dist1
            (findLongestMatch_len_ge _ _ _ _ _ hfind1)
            (by rw [← hml1]; exact matchLength_le_258 data _ _)
            (by omega) (by omega)
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
                  exact encodeLitLen_reference_isSome len2 dist2
                    (findLongestMatch_len_ge _ _ _ _ _ hfind2)
                    (by rw [← hml2]; exact matchLength_le_258 data _ _)
                    (by omega) (by omega)
                | inr hmem => exact matchLZ77Lazy.go_encodable data _ windowSize hws s hmem
            · -- len2 ≤ len1 → reference :: go ...
              intro s hs; simp only [List.mem_cons] at hs
              cases hs with
              | inl heq => subst heq; exact henc_m1
              | inr hmem => exact matchLZ77Lazy.go_encodable data _ windowSize hws s hmem
          · -- none → reference :: go ...
            intro s hs; simp only [List.mem_cons] at hs
            cases hs with
            | inl heq => subst heq; exact henc_m1
            | inr hmem => exact matchLZ77Lazy.go_encodable data _ windowSize hws s hmem
        · -- ¬(pos + 1 < data.length) → reference :: go ...
          intro s hs; simp only [List.mem_cons] at hs
          cases hs with
          | inl heq => subst heq; exact henc_m1
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
