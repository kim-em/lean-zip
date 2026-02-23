/-!
# LZ77 Symbol Algebra and Greedy Matching

Defines the LZ77 symbol alphabet used by DEFLATE (literals, back-references,
end-of-block), the `resolveLZ77` function that resolves symbols to output
bytes, and a greedy LZ77 matcher with its correctness proof
(`resolveLZ77_matchLZ77`).
-/

namespace Deflate.Spec

/-! ## LZ77 symbol alphabet -/

/-- The symbols produced by DEFLATE Huffman decoding, before LZ77
    back-reference resolution. -/
inductive LZ77Symbol where
  /-- A literal byte (codes 0–255). -/
  | literal (byte : UInt8)
  /-- A length-distance back-reference (length codes 257–285 + distance). -/
  | reference (length : Nat) (distance : Nat)
  /-- End of block marker (code 256). -/
  | endOfBlock
  deriving Repr, BEq

/-- Resolve a sequence of LZ77 symbols to produce output bytes.
    Returns `none` if any back-reference is invalid (distance exceeds
    current output size). -/
def resolveLZ77 : List LZ77Symbol → List UInt8 → Option (List UInt8)
  | [], acc => some acc
  | .literal b :: rest, acc => resolveLZ77 rest (acc ++ [b])
  | .endOfBlock :: _, acc => some acc
  | .reference len dist :: rest, acc =>
    if dist == 0 || dist > acc.length then none
    else
      let start := acc.length - dist
      let copied := List.ofFn fun (i : Fin len) =>
        acc[start + (i.val % dist)]!
      resolveLZ77 rest (acc ++ copied)

/-! ## resolveLZ77 properties -/

/-- Empty symbol list returns the accumulator unchanged. -/
@[simp] theorem resolveLZ77_nil (acc : List UInt8) :
    resolveLZ77 [] acc = some acc := rfl

/-- End-of-block marker returns the accumulator, ignoring remaining symbols. -/
@[simp] theorem resolveLZ77_endOfBlock (rest : List LZ77Symbol) (acc : List UInt8) :
    resolveLZ77 (.endOfBlock :: rest) acc = some acc := rfl

/-- A literal symbol appends the byte and continues resolving. -/
@[simp] theorem resolveLZ77_literal (b : UInt8) (rest : List LZ77Symbol) (acc : List UInt8) :
    resolveLZ77 (.literal b :: rest) acc = resolveLZ77 rest (acc ++ [b]) := rfl

/-- A reference with distance 0 fails. -/
theorem resolveLZ77_reference_dist_zero (len : Nat) (rest : List LZ77Symbol)
    (acc : List UInt8) :
    resolveLZ77 (.reference len 0 :: rest) acc = none := by
  simp [resolveLZ77]

/-- A reference with distance exceeding the accumulator length fails. -/
theorem resolveLZ77_reference_dist_too_large (len dist : Nat)
    (rest : List LZ77Symbol) (acc : List UInt8)
    (h : dist > acc.length) :
    resolveLZ77 (.reference len dist :: rest) acc = none := by
  simp [resolveLZ77]
  intro hd
  omega

/-- A sequence of literal symbols resolves to the accumulator followed
    by those bytes. -/
theorem resolveLZ77_literals (bytes : List UInt8) (acc : List UInt8) :
    resolveLZ77 (bytes.map .literal ++ [.endOfBlock]) acc =
      some (acc ++ bytes) := by
  induction bytes generalizing acc with
  | nil => simp
  | cons b bs ih =>
    simp only [List.map_cons, List.cons_append, resolveLZ77_literal]
    rw [ih]; congr 1; simp [List.append_assoc]

/-- `resolveLZ77` with only literals (no endOfBlock) continues processing.
    If the remaining symbols resolve, so does the whole list. -/
theorem resolveLZ77_literal_cons (b : UInt8) (rest : List LZ77Symbol)
    (acc output : List UInt8) :
    resolveLZ77 (.literal b :: rest) acc = some output ↔
    resolveLZ77 rest (acc ++ [b]) = some output := by
  simp [resolveLZ77]

/-- `resolveLZ77` starting from empty accumulator with just an endOfBlock
    returns the empty list. -/
theorem resolveLZ77_endOfBlock_empty :
    resolveLZ77 [.endOfBlock] [] = some [] := rfl

/-- A valid back-reference unfolds to copying and continuing resolution. -/
theorem resolveLZ77_reference_valid (len dist : Nat) (rest : List LZ77Symbol)
    (acc : List UInt8) (hd : dist ≠ 0) (hdist : dist ≤ acc.length) :
    resolveLZ77 (.reference len dist :: rest) acc =
      let start := acc.length - dist
      let copied := List.ofFn fun (i : Fin len) =>
        acc[start + (i.val % dist)]!
      resolveLZ77 rest (acc ++ copied) := by
  have h1 : ¬(dist = 0) := hd
  have h2 : ¬(acc.length < dist) := by omega
  simp [resolveLZ77, h1, h2]

/-- If `resolveLZ77` succeeds, the output extends the initial accumulator. -/
theorem resolveLZ77_extends (syms : List LZ77Symbol) (acc output : List UInt8)
    (h : resolveLZ77 syms acc = some output) :
    acc <+: output := by
  induction syms generalizing acc with
  | nil => simp [resolveLZ77] at h; exact h ▸ List.prefix_refl _
  | cons sym rest ih =>
    cases sym with
    | literal b =>
      simp [resolveLZ77] at h
      have := ih _ h
      exact List.IsPrefix.trans (List.prefix_append _ _) this
    | endOfBlock =>
      simp [resolveLZ77] at h; exact h ▸ List.prefix_refl _
    | reference len dist =>
      simp only [resolveLZ77] at h
      split at h
      · contradiction
      · have := ih _ h
        exact List.IsPrefix.trans (List.prefix_append _ _) this

/-! ## LZ77 matching (greedy encoder) -/

/-- Count consecutive matching bytes at position `pos` with source at
    distance `dist` back, using DEFLATE's overlapping-copy semantics.
    Returns 0 if `dist > pos` or `dist = 0`. -/
def matchLength (data : List UInt8) (pos dist : Nat)
    (maxLen : Nat := 258) : Nat :=
  if dist == 0 || dist > pos then 0
  else matchLength.go data pos dist 0 maxLen
where
  go (data : List UInt8) (pos dist count maxLen : Nat) : Nat :=
    if count ≥ maxLen then count
    else
      match data[pos + count]?, data[pos - dist + (count % dist)]? with
      | some a, some b =>
        if a == b then go data pos dist (count + 1) maxLen else count
      | _, _ => count
  termination_by maxLen - count

/-- Find the longest match at position `pos`, scanning distances
    1 to `min pos windowSize`. Returns `(length, distance)` if a
    match of length ≥ 3 is found. -/
def findLongestMatch (data : List UInt8) (pos : Nat)
    (windowSize : Nat := 32768) : Option (Nat × Nat) :=
  go data pos 1 (min pos windowSize) none
where
  go (data : List UInt8) (pos d maxDist : Nat)
      (best : Option (Nat × Nat)) : Option (Nat × Nat) :=
    if d > maxDist then best
    else
      let len := matchLength data pos d
      let best' := match best with
        | some (bestLen, _) => if len > bestLen then some (len, d) else best
        | none => if len ≥ 3 then some (len, d) else none
      go data pos (d + 1) maxDist best'
  termination_by maxDist + 1 - d

/-- Greedy LZ77 matching: at each position, emit the longest match
    or a literal. Terminates with endOfBlock. -/
def matchLZ77 (data : List UInt8) (windowSize : Nat := 32768) :
    List LZ77Symbol :=
  go data 0 windowSize
where
  go (data : List UInt8) (pos windowSize : Nat) : List LZ77Symbol :=
    if pos ≥ data.length then [.endOfBlock]
    else
      match findLongestMatch data pos windowSize with
      | some (len, dist) =>
        if len ≥ 3 then
          .reference len dist :: go data (pos + len) windowSize
        else
          .literal data[pos]! :: go data (pos + 1) windowSize
      | none =>
        .literal data[pos]! :: go data (pos + 1) windowSize
  termination_by data.length - pos
  decreasing_by all_goals omega

/-! ## LZ77 matching properties -/

/-- `matchLength.go` returns a value between `count` and `maxLen`. -/
theorem matchLength.go_bounds (data : List UInt8) (pos dist count maxLen : Nat)
    (hle : count ≤ maxLen) :
    count ≤ matchLength.go data pos dist count maxLen ∧
    matchLength.go data pos dist count maxLen ≤ maxLen := by
  unfold matchLength.go
  split
  · constructor <;> omega
  · rename_i hlt
    simp at hlt
    split
    · split
      · have := matchLength.go_bounds data pos dist (count + 1) maxLen (by omega)
        constructor <;> omega
      · constructor <;> omega
    · constructor <;> omega
termination_by maxLen - count

/-- `matchLength.go` only counts positions where bytes match. -/
theorem matchLength.go_correct (data : List UInt8) (pos dist count maxLen : Nat)
    (_ : count ≤ maxLen)
    (n : Nat) (hgo : matchLength.go data pos dist count maxLen = n) :
    ∀ i, count ≤ i → i < n →
      data[pos + i]? = data[pos - dist + (i % dist)]? := by
  unfold matchLength.go at hgo
  split at hgo
  · omega
  · rename_i hlt; simp at hlt
    cases hpa : data[pos + count]? with
    | none => simp [hpa] at hgo; subst hgo; intro i hi hlt; omega
    | some a =>
      cases hpb : data[pos - dist + (count % dist)]? with
      | none => simp [hpa, hpb] at hgo; subst hgo; intro i hi hlt; omega
      | some b =>
        simp [hpa, hpb] at hgo
        split at hgo
        · rename_i hab
          have ih := matchLength.go_correct data pos dist (count + 1) maxLen
            (by omega) n hgo
          intro i hi hilt
          by_cases heq : i = count
          · rw [heq, hpa, hpb]; simp_all
          · exact ih i (by omega) hilt
        · subst hgo; intro i hi hilt; omega
termination_by maxLen - count

/-- `matchLength.go` ensures all counted positions are in bounds. -/
theorem matchLength.go_in_bounds (data : List UInt8) (pos dist count maxLen : Nat)
    (_ : count ≤ maxLen)
    (n : Nat) (hgo : matchLength.go data pos dist count maxLen = n) :
    ∀ i, count ≤ i → i < n → pos + i < data.length := by
  unfold matchLength.go at hgo
  split at hgo
  · omega
  · rename_i hlt; simp at hlt
    cases hpa : data[pos + count]? with
    | none =>
      simp [hpa] at hgo; subst hgo; intro i hi hlt; omega
    | some a =>
      cases hpb : data[pos - dist + (count % dist)]? with
      | none => simp [hpa, hpb] at hgo; subst hgo; intro i hi hlt; omega
      | some b =>
        simp [hpa, hpb] at hgo
        split at hgo
        · have ih := matchLength.go_in_bounds data pos dist (count + 1) maxLen
            (by omega) n hgo
          intro i hi hilt
          by_cases heq : i = count
          · rw [heq]
            have ⟨h, _⟩ := List.getElem?_eq_some_iff.mp hpa
            exact h
          · exact ih i (by omega) hilt
        · subst hgo; intro i hi hilt; omega
termination_by maxLen - count

/-- `matchLength` only counts verified matching positions. -/
theorem matchLength_correct (data : List UInt8) (pos dist : Nat)
    (maxLen n : Nat) (h : matchLength data pos dist maxLen = n) :
    ∀ i : Fin n, data[pos + i.val]? =
      data[pos - dist + (i.val % dist)]? := by
  intro ⟨i, hi⟩
  unfold matchLength at h
  split at h
  · omega
  · exact matchLength.go_correct data pos dist 0 maxLen (by omega) n h i (by omega) hi

/-- All positions counted by `matchLength` are in bounds. -/
theorem matchLength_in_bounds (data : List UInt8) (pos dist : Nat)
    (maxLen n : Nat) (h : matchLength data pos dist maxLen = n) :
    ∀ i : Fin n, pos + i.val < data.length := by
  intro ⟨i, hi⟩
  unfold matchLength at h
  split at h
  · omega
  · exact matchLength.go_in_bounds data pos dist 0 maxLen (by omega) n h i (by omega) hi

/-- Invariant for `findLongestMatch.go`: if it returns `some (len, dist)`,
    then `len ≥ 3`, `1 ≤ dist ≤ maxDist`, and `matchLength data pos dist = len`. -/
private theorem findLongestMatch.go_inv (data : List UInt8) (pos d maxDist : Nat)
    (best : Option (Nat × Nat))
    (hbest : ∀ l d', best = some (l, d') →
       l ≥ 3 ∧ 1 ≤ d' ∧ d' ≤ maxDist ∧ matchLength data pos d' = l)
    (hd : d ≥ 1)
    (len dist : Nat)
    (hgo : findLongestMatch.go data pos d maxDist best = some (len, dist)) :
    len ≥ 3 ∧ 1 ≤ dist ∧ dist ≤ maxDist ∧ matchLength data pos dist = len := by
  unfold findLongestMatch.go at hgo
  split at hgo
  · exact hbest len dist hgo
  · rename_i hdgt; simp at hdgt
    apply findLongestMatch.go_inv data pos (d + 1) maxDist _ _ (by omega)
      _ _ hgo
    intro l d' hbd'
    simp only at hbd'
    cases hm : best with
    | none =>
      simp [hm] at hbd'
      obtain ⟨hge, heql, heqd⟩ := hbd'
      exact ⟨by omega, by omega, by omega, by rw [← heqd]; exact heql⟩
    | some p =>
      obtain ⟨bestLen, bestDist⟩ := p
      simp [hm] at hbd'
      split at hbd'
      · simp at hbd'; obtain ⟨rfl, rfl⟩ := hbd'
        have hbl := hbest bestLen bestDist hm
        exact ⟨by omega, by omega, by omega, rfl⟩
      · exact hbest l d' (hm ▸ hbd')
termination_by maxDist + 1 - d

/-- If `findLongestMatch` returns `some (len, dist)`, then `len ≥ 3`. -/
theorem findLongestMatch_len_ge (data : List UInt8) (pos windowSize : Nat)
    (len dist : Nat)
    (h : findLongestMatch data pos windowSize = some (len, dist)) :
    len ≥ 3 :=
  (findLongestMatch.go_inv data pos 1 (min pos windowSize) none
    (by simp) (by omega) len dist h).1

/-- If `findLongestMatch` returns `some (len, dist)`, then `1 ≤ dist ≤ pos`. -/
theorem findLongestMatch_dist_bounds (data : List UInt8) (pos windowSize : Nat)
    (len dist : Nat)
    (h : findLongestMatch data pos windowSize = some (len, dist)) :
    1 ≤ dist ∧ dist ≤ pos := by
  have inv := findLongestMatch.go_inv data pos 1 (min pos windowSize) none
    (by simp) (by omega) len dist h
  exact ⟨inv.2.1, by omega⟩

/-- If `findLongestMatch` returns `some (len, dist)`, then
    `matchLength data pos dist = len`. -/
theorem findLongestMatch_matchLength (data : List UInt8) (pos windowSize : Nat)
    (len dist : Nat)
    (h : findLongestMatch data pos windowSize = some (len, dist)) :
    matchLength data pos dist = len :=
  (findLongestMatch.go_inv data pos 1 (min pos windowSize) none
    (by simp) (by omega) len dist h).2.2.2

/-- Key lemma: the accumulator after resolving a back-reference produced
    by `matchLength` equals `data.take (pos + len)`. This connects the
    modular-copy semantics in `resolveLZ77` with the matching check in
    `matchLength`. -/
private theorem take_append_copied_eq_take
    (data : List UInt8) (pos dist len : Nat)
    (hdist_pos : dist ≥ 1) (hdist_le : dist ≤ pos)
    (hlen_eq : matchLength data pos dist = len)
    (hpos_le : pos ≤ data.length)
    (hlen_le : pos + len ≤ data.length) :
    data.take pos ++ (List.ofFn fun (i : Fin len) =>
      (data.take pos)[pos - dist + (i.val % dist)]!) =
    data.take (pos + len) := by
  rw [List.take_add]
  congr 1
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_take, List.length_drop]
    omega
  · intro i h1 h2
    simp only [List.length_ofFn] at h1
    simp only [List.length_take, List.length_drop,
               Nat.min_eq_left (by omega : len ≤ data.length - pos)] at h2
    rw [List.getElem_ofFn]
    rw [List.getElem_take, List.getElem_drop]
    have hidx_lt : pos - dist + (i % dist) < pos := by
      have : i % dist < dist := Nat.mod_lt _ (by omega)
      omega
    rw [getElem!_pos (data.take pos) _ (by
      simp [Nat.min_eq_left hpos_le]; exact hidx_lt)]
    rw [List.getElem_take]
    have hmatch := matchLength_correct data pos dist 258 len hlen_eq ⟨i, h1⟩
    simp only at hmatch
    rw [List.getElem?_eq_getElem (h := by omega)] at hmatch
    rw [List.getElem?_eq_getElem (h := by
      have : i % dist < dist := Nat.mod_lt _ (by omega); omega)] at hmatch
    simp at hmatch
    exact hmatch.symm

/-- Inner correctness lemma for `matchLZ77.go`: resolving the symbols
    produced from position `pos` with accumulator `data.take pos` gives
    back the original data. -/
private theorem matchLZ77.go_correct (data : List UInt8) (pos windowSize : Nat)
    (hw : windowSize > 0) (hpos : pos ≤ data.length) :
    resolveLZ77 (matchLZ77.go data pos windowSize) (data.take pos) =
      some data := by
  unfold matchLZ77.go
  split
  · rename_i hge
    have heq : pos = data.length := by omega
    subst heq; simp [List.take_length, resolveLZ77]
  · rename_i hlt
    simp at hlt
    have lit_step : data.take pos ++ [data[pos]!] = data.take (pos + 1) := by
      rw [getElem!_pos data pos hlt]
      exact (List.take_succ_eq_append_getElem hlt).symm
    split
    · rename_i len dist hfind
      split
      · rename_i hlen3
        simp only [resolveLZ77]
        have ⟨hdist_pos, hdist_le⟩ := findLongestMatch_dist_bounds _ _ _ _ _ hfind
        have hml := findLongestMatch_matchLength _ _ _ _ _ hfind
        have hlen_in := matchLength_in_bounds data pos dist 258 len hml
        have hlen_le : pos + len ≤ data.length := by
          by_cases hlen0 : len = 0
          · omega
          · have := hlen_in ⟨len - 1, by omega⟩; simp at this; omega
        have hdneq : dist ≠ 0 := by omega
        rw [show (dist == 0 || decide (List.length (List.take pos data) < dist)) = false
          from by simp [hdneq, Nat.min_eq_left hpos]; omega]
        simp only [Bool.false_eq_true, ↓reduceIte]
        have hcopy := take_append_copied_eq_take data pos dist len
          hdist_pos hdist_le hml hpos hlen_le
        conv => lhs; rw [show (List.take pos data).length = pos
          from by simp [Nat.min_eq_left hpos]]
        rw [hcopy]
        exact matchLZ77.go_correct data (pos + len) windowSize hw hlen_le
      · simp only [resolveLZ77]
        rw [lit_step]
        exact matchLZ77.go_correct data (pos + 1) windowSize hw (by omega)
    · simp only [resolveLZ77]
      rw [lit_step]
      exact matchLZ77.go_correct data (pos + 1) windowSize hw (by omega)
termination_by data.length - pos

/-- The greedy LZ77 matcher is correct: resolving the produced symbols
    reconstructs the original data. -/
theorem resolveLZ77_matchLZ77 (data : List UInt8)
    (windowSize : Nat) (hw : windowSize > 0) :
    resolveLZ77 (matchLZ77 data windowSize) [] = some data := by
  show resolveLZ77 (matchLZ77.go data 0 windowSize) (data.take 0) = some data
  exact matchLZ77.go_correct data 0 windowSize hw (by omega)

end Deflate.Spec
