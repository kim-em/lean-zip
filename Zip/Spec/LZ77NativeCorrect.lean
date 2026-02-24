import Zip.Native.Deflate
import Zip.Spec.LZ77
import ZipForStd.ByteArray

namespace Zip.Native.Deflate

/-- Convert a native LZ77Token to a spec LZ77Symbol. -/
def LZ77Token.toLZ77Symbol : LZ77Token → Deflate.Spec.LZ77Symbol
  | .literal b => .literal b
  | .reference len dist => .reference len dist

/-- Convert native LZ77 token array to spec symbol list with end-of-block. -/
def tokensToSymbols (tokens : Array LZ77Token) : List Deflate.Spec.LZ77Symbol :=
  tokens.toList.map LZ77Token.toLZ77Symbol ++ [.endOfBlock]

/-! ## countMatch correctness -/

/-- The inner `go` loop of `countMatch` counts consecutive matching bytes
    between positions `p1+i..` and `p2+i..` in `data`. Returns a count `n`
    such that `i ≤ n ≤ maxLen` and all positions in `[i, n)` have matching
    bytes. -/
theorem lz77Greedy.go_matches (data : ByteArray) (p1 p2 i maxLen : Nat)
    (hle : i ≤ maxLen) :
    let n := lz77Greedy.go data p1 p2 i maxLen
    (∀ j, i ≤ j → j < n → data[p1 + j]! = data[p2 + j]!) ∧
    i ≤ n ∧ n ≤ maxLen := by
  unfold lz77Greedy.go
  split
  · rename_i hlt
    split
    · rename_i heq
      have ih := lz77Greedy.go_matches data p1 p2 (i + 1) maxLen (by omega)
      refine ⟨fun j hj hjn => ?_, by omega, ih.2.2⟩
      by_cases hji : j = i
      · subst hji; exact beq_iff_eq.mp heq
      · exact ih.1 j (by omega) hjn
    · exact ⟨fun j hj hjn => by omega, by omega, by omega⟩
  · exact ⟨fun j hj hjn => by omega, by omega, by omega⟩
termination_by maxLen - i

/-- `countMatch` returns a count of consecutive matching bytes starting from
    position 0, with all counted positions verified equal. -/
theorem lz77Greedy.countMatch_matches (data : ByteArray) (p1 p2 maxLen : Nat) :
    let n := lz77Greedy.countMatch data p1 p2 maxLen
    (∀ j, j < n → data[p1 + j]! = data[p2 + j]!) ∧ n ≤ maxLen := by
  simp only [lz77Greedy.countMatch]
  have h := lz77Greedy.go_matches data p1 p2 0 maxLen (by omega)
  exact ⟨fun j hj => h.1 j (by omega) hj, h.2.2⟩

/-! ## ValidDecomp predicate -/

/-- A token list is a valid decomposition of `data` starting at position `pos`.
    Each literal has the correct byte, each reference has matching bytes in the
    lookback window, and tokens cover `data[pos..]` contiguously. -/
inductive ValidDecomp (data : ByteArray) : Nat → List LZ77Token → Prop where
  | done (h : pos ≥ data.size) : ValidDecomp data pos []
  | literal {b : UInt8} {tokens : List LZ77Token}
      (hpos : pos < data.size)
      (hb : data[pos]! = b)
      (rest : ValidDecomp data (pos + 1) tokens) :
      ValidDecomp data pos (.literal b :: tokens)
  | reference {len dist : Nat} {tokens : List LZ77Token}
      (hlen : len ≥ 3) (hdist_pos : dist ≥ 1) (hdist_le : dist ≤ pos)
      (hlen_le : pos + len ≤ data.size)
      (hmatch : ∀ i, i < len → data[pos + i]! = data[pos - dist + i]!)
      (rest : ValidDecomp data (pos + len) tokens) :
      ValidDecomp data pos (.reference len dist :: tokens)

/-! ## Bridge lemma: direct match → modular copy -/

/-- If bytes at `data[pos..pos+len]` match `data[pos-dist..pos-dist+len]` directly,
    then each byte equals the modular-copy byte used by `resolveLZ77`. -/
theorem direct_match_implies_modular (data : ByteArray) (pos dist len : Nat)
    (hdist_pos : dist ≥ 1) (hdist_le : dist ≤ pos)
    (hmatch : ∀ i, i < len → data[pos + i]! = data[pos - dist + i]!) :
    ∀ i, i < len → data[pos + i]! = data[pos - dist + (i % dist)]! := by
  intro i
  induction i using Nat.strongRecOn with
  | _ i ih =>
    intro hi
    by_cases hid : i < dist
    · rw [Nat.mod_eq_of_lt hid]; exact hmatch i hi
    · have hge : i ≥ dist := by omega
      rw [Nat.mod_eq_sub_mod hge]
      have h1 := hmatch i hi
      have h2 : pos - dist + i = pos + (i - dist) := by omega
      rw [h2] at h1; rw [h1]
      exact ih (i - dist) (by omega) (by omega)

/-! ## validDecomp_resolves -/

/-- Generalized `validDecomp_resolves`: at position `pos` with accumulator
    `data.data.toList.take pos`, resolving the tokens recovers the full data. -/
theorem validDecomp_resolves_aux (data : ByteArray) (pos : Nat) (tokens : List LZ77Token)
    (hv : ValidDecomp data pos tokens) :
    Deflate.Spec.resolveLZ77 (tokens.map LZ77Token.toLZ77Symbol ++ [.endOfBlock])
      (data.data.toList.take pos) = some data.data.toList := by
  induction hv with
  | done h =>
    simp only [List.map_nil, List.nil_append, Deflate.Spec.resolveLZ77_endOfBlock]
    exact congrArg some (List.take_of_length_le (by rw [ByteArray.data_toList_length]; omega))
  | @literal pos b tokens hpos hb rest ih =>
    simp only [List.map_cons, List.cons_append, LZ77Token.toLZ77Symbol,
               Deflate.Spec.resolveLZ77_literal]
    suffices h : data.data.toList.take pos ++ [b] =
        data.data.toList.take (pos + 1) by rw [h]; exact ih
    rw [← hb, ByteArray.getElem!_toList data pos hpos]
    exact (List.take_succ_eq_append_getElem (by rw [ByteArray.data_toList_length]; exact hpos)).symm
  | @reference pos len dist tokens hlen hdist_pos hdist_le hlen_le hmatch rest ih =>
    simp only [List.map_cons, List.cons_append, LZ77Token.toLZ77Symbol]
    have hmod := direct_match_implies_modular data pos dist len hdist_pos hdist_le hmatch
    simp only [Deflate.Spec.resolveLZ77]
    have hdneq : dist ≠ 0 := by omega
    have hacclen : (data.data.toList.take pos).length = pos := by
      simp [List.length_take]; omega
    rw [show (dist == 0 || decide ((data.data.toList.take pos).length < dist)) = false
      from by simp [hdneq, hacclen]; omega]
    simp only [Bool.false_eq_true, ↓reduceIte, hacclen]
    suffices h : data.data.toList.take pos ++
        (List.ofFn fun (i : Fin len) =>
          (data.data.toList.take pos)[pos - dist + (↑i % dist)]!) =
        data.data.toList.take (pos + len) by rw [h]; exact ih
    have hdllen : data.data.toList.length = data.size := ByteArray.data_toList_length data
    apply List.ext_getElem
    · simp [List.length_append, List.length_ofFn, List.length_take, hdllen]; omega
    · intro i h1 h2
      simp only [List.length_take, hdllen, Nat.min_eq_left (by omega)] at h2
      simp only [List.getElem_take]
      by_cases hip : i < pos
      · -- Element from the take pos part
        rw [List.getElem_append_left (by simp [List.length_take, hdllen]; omega)]
        simp only [List.getElem_take]
      · -- Element from the ofFn part
        rw [List.getElem_append_right (by simp [List.length_take, hdllen]; omega)]
        simp only [List.length_take, hdllen]
        rw [List.getElem_ofFn]
        -- Goal: (take pos dl)[pos - dist + ((i - pos) % dist)]! = dl[i]
        have hmin : min pos data.size = pos := Nat.min_eq_left (by omega)
        have hk : (i - pos) % dist < dist := Nat.mod_lt _ (by omega)
        have hm := hmod (i - pos) (by omega)
        rw [show pos + (i - pos) = i from by omega] at hm
        rw [ByteArray.getElem!_toList data i (by omega)] at hm
        rw [ByteArray.getElem!_toList data (pos - dist + ((i - pos) % dist))
          (by omega)] at hm
        -- Simplify min in getElem! bounds
        show (data.data.toList.take pos)[pos - dist +
          ((i - min pos data.size) % dist)]! = data.data.toList[i]
        rw [hmin]
        rw [getElem!_pos (data.data.toList.take pos) _ (by
          simp [List.length_take, hdllen, hmin]; omega)]
        simp only [List.getElem_take]
        exact hm.symm

/-- Resolving the tokens from any valid decomposition recovers the original data. -/
theorem validDecomp_resolves (data : ByteArray) (tokens : List LZ77Token)
    (hv : ValidDecomp data 0 tokens) :
    Deflate.Spec.resolveLZ77 (tokens.map LZ77Token.toLZ77Symbol ++ [.endOfBlock]) [] =
      some data.data.toList := by
  have := validDecomp_resolves_aux data 0 tokens hv
  simp at this; exact this

/-! ## Explicit recursion validity -/

theorem trailing_valid (data : ByteArray) (pos : Nat) :
    ValidDecomp data pos (lz77Greedy.trailing data pos) := by
  unfold lz77Greedy.trailing
  split
  · rename_i hlt
    exact .literal hlt rfl (trailing_valid data (pos + 1))
  · exact .done (by omega)
termination_by data.size - pos

theorem mainLoop_valid (data : ByteArray) (windowSize hashSize : Nat)
    (hashTable : Array Nat) (hashValid : Array Bool) (pos : Nat)
    (hw : windowSize > 0) :
    ValidDecomp data pos
      (lz77Greedy.mainLoop data windowSize hashSize hashTable hashValid pos) := by
  unfold lz77Greedy.mainLoop
  split
  · rename_i hlt
    dsimp only
    split
    · rename_i hcond
      split
      · rename_i hge
        split
        · rename_i hle
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
          have hmp_lt := hcond.1.2
          have hcm := lz77Greedy.countMatch_matches data
            hashTable[lz77Greedy.hash3 data pos hashSize]! pos (min 258 (data.size - pos))
          apply ValidDecomp.reference hge
          · omega
          · exact Nat.sub_le _ _
          · exact hle
          · intro i hi
            have hmpeq : pos - (pos - hashTable[lz77Greedy.hash3 data pos hashSize]!) =
                hashTable[lz77Greedy.hash3 data pos hashSize]! := by omega
            rw [hmpeq]
            exact (hcm.1 i hi).symm
          · exact mainLoop_valid _ _ _ _ _ _ hw
        · exact .literal (by omega) rfl (mainLoop_valid _ _ _ _ _ _ hw)
      · exact .literal (by omega) rfl (mainLoop_valid _ _ _ _ _ _ hw)
    · exact .literal (by omega) rfl (mainLoop_valid _ _ _ _ _ _ hw)
  · exact trailing_valid data pos
termination_by data.size - pos

/-! ## lz77Greedy validity -/

/-- `lz77Greedy` produces a valid decomposition of the input data. -/
theorem lz77Greedy_valid (data : ByteArray) (windowSize : Nat) (hw : windowSize > 0) :
    ValidDecomp data 0 (lz77Greedy data windowSize).toList := by
  simp only [lz77Greedy]
  split
  · simp
    exact trailing_valid data 0
  · simp
    exact mainLoop_valid data windowSize 65536 _ _ 0 hw

/-- Resolving the LZ77 tokens produced by `lz77Greedy` recovers the original data.
    This is the BB1 analog for the native compressor. -/
theorem lz77Greedy_resolves (data : ByteArray)
    (windowSize : Nat) (hw : windowSize > 0) :
    Deflate.Spec.resolveLZ77
      (tokensToSymbols (lz77Greedy data windowSize)) [] =
      some data.data.toList :=
  validDecomp_resolves data _ (lz77Greedy_valid data windowSize hw)

/-! ## lz77Greedy encodability -/

private def Encodable (t : LZ77Token) : Prop :=
  match t with
  | .literal _ => True
  | .reference len dist => 3 ≤ len ∧ len ≤ 258 ∧ 1 ≤ dist ∧ dist ≤ 32768

theorem trailing_encodable (data : ByteArray) (pos : Nat) :
    ∀ t ∈ lz77Greedy.trailing data pos, Encodable t := by
  unfold lz77Greedy.trailing
  split
  · intro t ht
    cases ht with
    | head => trivial
    | tail _ h => exact trailing_encodable data (pos + 1) t h
  · simp
termination_by data.size - pos

theorem mainLoop_encodable (data : ByteArray) (windowSize hashSize : Nat)
    (hashTable : Array Nat) (hashValid : Array Bool) (pos : Nat)
    (hw : windowSize > 0) (hws : windowSize ≤ 32768) :
    ∀ t ∈ lz77Greedy.mainLoop data windowSize hashSize hashTable hashValid pos,
      Encodable t := by
  unfold lz77Greedy.mainLoop
  split
  · rename_i hlt
    dsimp only
    split
    · rename_i hcond
      split
      · rename_i hge
        split
        · rename_i hle
          -- Reference case
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
          obtain ⟨⟨_, hmp_lt⟩, hmp_ws⟩ := hcond
          intro t ht
          cases ht with
          | head =>
            show 3 ≤ _ ∧ _ ≤ 258 ∧ 1 ≤ _ ∧ _ ≤ 32768
            have hcm := lz77Greedy.countMatch_matches data
              hashTable[lz77Greedy.hash3 data pos hashSize]! pos (min 258 (data.size - pos))
            exact ⟨hge, by omega, by omega, by omega⟩
          | tail _ h => exact mainLoop_encodable _ _ _ _ _ _ hw hws t h
        · intro t ht
          cases ht with
          | head => trivial
          | tail _ h => exact mainLoop_encodable _ _ _ _ _ _ hw hws t h
      · intro t ht
        cases ht with
        | head => trivial
        | tail _ h => exact mainLoop_encodable _ _ _ _ _ _ hw hws t h
    · intro t ht
      cases ht with
      | head => trivial
      | tail _ h => exact mainLoop_encodable _ _ _ _ _ _ hw hws t h
  · exact trailing_encodable data pos
termination_by data.size - pos

/-! ## Length bounds -/

/-- `trailing` emits at most `data.size - pos` tokens. -/
theorem trailing_length (data : ByteArray) (pos : Nat) :
    (lz77Greedy.trailing data pos).length ≤ data.size - pos := by
  unfold lz77Greedy.trailing
  split
  · simp only [List.length_cons]
    have ih := trailing_length data (pos + 1)
    omega
  · simp
termination_by data.size - pos

/-- `mainLoop` emits at most `data.size - pos` tokens. -/
private theorem length_cons_le_of_advance {n k s pos : Nat}
    (ih : n ≤ s - (pos + k)) (hk : k ≥ 1) (hle : pos + k ≤ s) :
    n + 1 ≤ s - pos := by omega

theorem mainLoop_length (data : ByteArray) (windowSize hashSize : Nat)
    (hashTable : Array Nat) (hashValid : Array Bool) (pos : Nat) :
    (lz77Greedy.mainLoop data windowSize hashSize hashTable hashValid pos).length
      ≤ data.size - pos := by
  unfold lz77Greedy.mainLoop
  split
  · rename_i hlt
    dsimp only
    split
    · rename_i hcond
      split
      · rename_i hge
        split
        · rename_i hle
          simp only [List.length_cons]
          exact length_cons_le_of_advance (mainLoop_length _ _ _ _ _ _) (by omega) hle
        · simp only [List.length_cons]
          exact length_cons_le_of_advance (mainLoop_length _ _ _ _ _ _) (by omega) (by omega)
      · simp only [List.length_cons]
        exact length_cons_le_of_advance (mainLoop_length _ _ _ _ _ _) (by omega) (by omega)
    · simp only [List.length_cons]
      exact length_cons_le_of_advance (mainLoop_length _ _ _ _ _ _) (by omega) (by omega)
  · exact trailing_length data pos
termination_by data.size - pos

/-- All tokens from `lz77Greedy` have valid ranges for fixed Huffman encoding:
    lengths in 3–258 and distances in 1–32768 (so `findLengthCode`/`findDistCode`
    always succeed). -/
theorem lz77Greedy_encodable (data : ByteArray)
    (windowSize : Nat) (hw : windowSize > 0) (hws : windowSize ≤ 32768) :
    ∀ t ∈ (lz77Greedy data windowSize).toList,
      match t with
      | .literal _ => True
      | .reference len dist => 3 ≤ len ∧ len ≤ 258 ∧ 1 ≤ dist ∧ dist ≤ 32768 := by
  intro t ht
  have henc : Encodable t := by
    simp only [lz77Greedy] at ht
    split at ht
    · simp at ht; exact trailing_encodable data 0 t ht
    · simp at ht; exact mainLoop_encodable data windowSize 65536 _ _ 0 hw hws t ht
  exact henc

/-! ## Lazy LZ77 correctness -/

/-! ### countMatch / trailing for lz77Lazy

These are structurally identical to the lz77Greedy versions
(defined as separate `where` functions with the same bodies). -/

theorem lz77Lazy.go_matches (data : ByteArray) (p1 p2 i maxLen : Nat)
    (hle : i ≤ maxLen) :
    let n := lz77Lazy.go data p1 p2 i maxLen
    (∀ j, i ≤ j → j < n → data[p1 + j]! = data[p2 + j]!) ∧
    i ≤ n ∧ n ≤ maxLen := by
  unfold lz77Lazy.go
  split
  · rename_i hlt
    split
    · rename_i heq
      have ih := lz77Lazy.go_matches data p1 p2 (i + 1) maxLen (by omega)
      refine ⟨fun j hj hjn => ?_, by omega, ih.2.2⟩
      by_cases hji : j = i
      · subst hji; exact beq_iff_eq.mp heq
      · exact ih.1 j (by omega) hjn
    · exact ⟨fun j hj hjn => by omega, by omega, by omega⟩
  · exact ⟨fun j hj hjn => by omega, by omega, by omega⟩
termination_by maxLen - i

theorem lz77Lazy.countMatch_matches (data : ByteArray) (p1 p2 maxLen : Nat) :
    let n := lz77Lazy.countMatch data p1 p2 maxLen
    (∀ j, j < n → data[p1 + j]! = data[p2 + j]!) ∧ n ≤ maxLen := by
  simp only [lz77Lazy.countMatch]
  have h := lz77Lazy.go_matches data p1 p2 0 maxLen (by omega)
  exact ⟨fun j hj => h.1 j (by omega) hj, h.2.2⟩

theorem lz77Lazy.trailing_valid (data : ByteArray) (pos : Nat) :
    ValidDecomp data pos (lz77Lazy.trailing data pos) := by
  unfold lz77Lazy.trailing
  split
  · rename_i hlt
    exact .literal hlt rfl (lz77Lazy.trailing_valid data (pos + 1))
  · exact .done (by omega)
termination_by data.size - pos

theorem lz77Lazy.trailing_encodable (data : ByteArray) (pos : Nat) :
    ∀ t ∈ lz77Lazy.trailing data pos, Encodable t := by
  unfold lz77Lazy.trailing
  split
  · intro t ht
    cases ht with
    | head => trivial
    | tail _ h => exact lz77Lazy.trailing_encodable data (pos + 1) t h
  · simp
termination_by data.size - pos

theorem lz77Lazy.trailing_length (data : ByteArray) (pos : Nat) :
    (lz77Lazy.trailing data pos).length ≤ data.size - pos := by
  unfold lz77Lazy.trailing
  split
  · simp only [List.length_cons]
    have ih := lz77Lazy.trailing_length data (pos + 1)
    omega
  · simp
termination_by data.size - pos

/-! ### Lazy mainLoop validity

The proof follows the lazy mainLoop case structure. Helper for the recurring
"reference at pos with the first match" pattern. -/

/-- Common proof step: reference from a valid countMatch at pos. -/
private theorem lazyRef_at_pos (data : ByteArray) (windowSize hashSize : Nat)
    (hashTable : Array Nat) (hashValid : Array Bool) (pos : Nat)
    (_hw : windowSize > 0)
    (hlt : pos + 2 < data.size)
    (hcond : (hashValid[lz77Lazy.hash3 data pos hashSize]! &&
        decide (hashTable[lz77Lazy.hash3 data pos hashSize]! < pos) &&
        decide (pos - hashTable[lz77Lazy.hash3 data pos hashSize]! ≤ windowSize)) = true)
    (hge : lz77Lazy.countMatch data (hashTable[lz77Lazy.hash3 data pos hashSize]!) pos
        (min 258 (data.size - pos)) ≥ 3)
    (hle : pos + lz77Lazy.countMatch data (hashTable[lz77Lazy.hash3 data pos hashSize]!) pos
        (min 258 (data.size - pos)) ≤ data.size)
    {rest : List LZ77Token}
    (hrest : ValidDecomp data (pos + lz77Lazy.countMatch data
        (hashTable[lz77Lazy.hash3 data pos hashSize]!) pos (min 258 (data.size - pos))) rest) :
    ValidDecomp data pos
      (.reference (lz77Lazy.countMatch data (hashTable[lz77Lazy.hash3 data pos hashSize]!) pos
          (min 258 (data.size - pos)))
        (pos - hashTable[lz77Lazy.hash3 data pos hashSize]!) :: rest) := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
  have hmp_lt := hcond.1.2
  have hcm := lz77Lazy.countMatch_matches data
    hashTable[lz77Lazy.hash3 data pos hashSize]! pos (min 258 (data.size - pos))
  exact .reference hge (by omega) (Nat.sub_le _ _) hle
    (fun i hi => by
      have hmpeq : pos - (pos - hashTable[lz77Lazy.hash3 data pos hashSize]!) =
          hashTable[lz77Lazy.hash3 data pos hashSize]! := by omega
      rw [hmpeq]; exact (hcm.1 i hi).symm)
    hrest

theorem lz77Lazy.mainLoop_valid (data : ByteArray) (windowSize hashSize : Nat)
    (hashTable : Array Nat) (hashValid : Array Bool) (pos : Nat)
    (hw : windowSize > 0) :
    ValidDecomp data pos
      (lz77Lazy.mainLoop data windowSize hashSize hashTable hashValid pos) := by
  unfold lz77Lazy.mainLoop
  split
  · rename_i hlt
    dsimp only
    split
    · rename_i hcond
      split
      · -- matchLen ≥ 3 (positive)
        rename_i hge
        split
        · -- pos + matchLen ≤ data.size (positive)
          rename_i hle
          split
          · -- pos + 3 < data.size (positive) → lazy check
            split
            · -- isValid2 && ... (positive)
              rename_i hcond2
              split
              · -- matchLen2 > matchLen (positive) → try longer match
                rename_i hlen2_gt
                split
                · -- pos + 1 + matchLen2 ≤ data.size (positive)
                  rename_i hle2
                  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond2
                  have hmp2_lt := hcond2.1.2
                  -- Use UPDATED hash table for countMatch at pos+1
                  have hcm2 := lz77Lazy.countMatch_matches data
                    (hashTable.set! (lz77Lazy.hash3 data pos hashSize) pos)[lz77Lazy.hash3 data (pos + 1) hashSize]!
                    (pos + 1) (min 258 (data.size - (pos + 1)))
                  exact .literal (by omega) rfl
                    (.reference (by omega)
                      (by omega) (Nat.sub_le _ _) hle2
                      (fun i hi => by
                        rw [show pos + 1 -
                            (pos + 1 - (hashTable.set! (lz77Lazy.hash3 data pos hashSize) pos)[lz77Lazy.hash3 data (pos + 1) hashSize]!) =
                            (hashTable.set! (lz77Lazy.hash3 data pos hashSize) pos)[lz77Lazy.hash3 data (pos + 1) hashSize]! from by omega]
                        exact (hcm2.1 i hi).symm)
                      (lz77Lazy.mainLoop_valid _ _ _ _ _ _ hw))
                · -- pos + 1 + matchLen2 > data.size → fall back to match at pos
                  exact lazyRef_at_pos data windowSize hashSize hashTable hashValid pos hw
                    hlt hcond hge hle (lz77Lazy.mainLoop_valid _ _ _ _ _ _ hw)
              · -- matchLen2 ≤ matchLen → keep match at pos
                exact lazyRef_at_pos data windowSize hashSize hashTable hashValid pos hw
                  hlt hcond hge hle (lz77Lazy.mainLoop_valid _ _ _ _ _ _ hw)
            · -- ¬(isValid2 && ...) → keep match at pos
              exact lazyRef_at_pos data windowSize hashSize hashTable hashValid pos hw
                hlt hcond hge hle (lz77Lazy.mainLoop_valid _ _ _ _ _ _ hw)
          · -- ¬(pos + 3 < data.size) → keep match at pos (near end)
            exact lazyRef_at_pos data windowSize hashSize hashTable hashValid pos hw
              hlt hcond hge hle (lz77Lazy.mainLoop_valid _ _ _ _ _ _ hw)
        · -- ¬(pos + matchLen ≤ data.size) → literal
          exact .literal (by omega) rfl (lz77Lazy.mainLoop_valid _ _ _ _ _ _ hw)
      · -- ¬(matchLen ≥ 3) → literal
        exact .literal (by omega) rfl (lz77Lazy.mainLoop_valid _ _ _ _ _ _ hw)
    · -- ¬(isValid && ...) → literal
      exact .literal (by omega) rfl (lz77Lazy.mainLoop_valid _ _ _ _ _ _ hw)
  · exact lz77Lazy.trailing_valid data pos
termination_by data.size - pos
decreasing_by all_goals omega

/-- `lz77Lazy` produces a valid decomposition of the input data. -/
theorem lz77Lazy_valid (data : ByteArray) (windowSize : Nat) (hw : windowSize > 0) :
    ValidDecomp data 0 (lz77Lazy data windowSize).toList := by
  simp only [lz77Lazy]
  split
  · simp; exact lz77Lazy.trailing_valid data 0
  · simp; exact lz77Lazy.mainLoop_valid data windowSize 65536 _ _ 0 hw

/-- Resolving the LZ77 tokens produced by `lz77Lazy` recovers the original data. -/
theorem lz77Lazy_resolves (data : ByteArray)
    (windowSize : Nat) (hw : windowSize > 0) :
    Deflate.Spec.resolveLZ77
      (tokensToSymbols (lz77Lazy data windowSize)) [] =
      some data.data.toList :=
  validDecomp_resolves data _ (lz77Lazy_valid data windowSize hw)

/-! ### Lazy mainLoop encodability -/

theorem lz77Lazy.mainLoop_encodable (data : ByteArray) (windowSize hashSize : Nat)
    (hashTable : Array Nat) (hashValid : Array Bool) (pos : Nat)
    (hw : windowSize > 0) (hws : windowSize ≤ 32768) :
    ∀ t ∈ lz77Lazy.mainLoop data windowSize hashSize hashTable hashValid pos,
      Encodable t := by
  unfold lz77Lazy.mainLoop
  split
  · rename_i hlt
    dsimp only
    split
    · rename_i hcond
      -- Destructure hcond early so hmp_lt, hmp_ws, hcm are available in all sub-cases
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      have hcm := lz77Lazy.countMatch_matches data
        hashTable[lz77Lazy.hash3 data pos hashSize]! pos (min 258 (data.size - pos))
      split
      · -- matchLen ≥ 3 (positive)
        rename_i hge
        split
        · -- pos + matchLen ≤ data.size (positive)
          rename_i hle
          split
          · -- pos + 3 < data.size (positive) → lazy check
            split
            · -- isValid2 && ... (positive)
              rename_i hcond2
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond2
              have hcm2 := lz77Lazy.countMatch_matches data
                (hashTable.set! (lz77Lazy.hash3 data pos hashSize) pos)[lz77Lazy.hash3 data (pos + 1) hashSize]!
                (pos + 1) (min 258 (data.size - (pos + 1)))
              split
              · -- matchLen2 > matchLen (positive)
                rename_i hlen2_gt
                split
                · -- pos + 1 + matchLen2 ≤ data.size (positive)
                  -- literal + reference(matchLen2, dist2) + recursive
                  intro t ht; cases ht with
                  | head => trivial
                  | tail _ h =>
                    cases h with
                    | head =>
                      show 3 ≤ _ ∧ _ ≤ 258 ∧ 1 ≤ _ ∧ _ ≤ 32768
                      exact ⟨by omega, by omega, by omega, by omega⟩
                    | tail _ h => exact lz77Lazy.mainLoop_encodable _ _ _ _ _ _ hw hws t h
                · -- fall back to ref(matchLen, dist)
                  intro t ht; cases ht with
                  | head =>
                    show 3 ≤ _ ∧ _ ≤ 258 ∧ 1 ≤ _ ∧ _ ≤ 32768
                    exact ⟨hge, by omega, by omega, by omega⟩
                  | tail _ h => exact lz77Lazy.mainLoop_encodable _ _ _ _ _ _ hw hws t h
              · -- matchLen2 ≤ matchLen → ref(matchLen, dist)
                intro t ht; cases ht with
                | head =>
                  show 3 ≤ _ ∧ _ ≤ 258 ∧ 1 ≤ _ ∧ _ ≤ 32768
                  exact ⟨hge, by omega, by omega, by omega⟩
                | tail _ h => exact lz77Lazy.mainLoop_encodable _ _ _ _ _ _ hw hws t h
            · -- ¬(isValid2 && ...) → ref(matchLen, dist)
              intro t ht; cases ht with
              | head =>
                show 3 ≤ _ ∧ _ ≤ 258 ∧ 1 ≤ _ ∧ _ ≤ 32768
                exact ⟨hge, by omega, by omega, by omega⟩
              | tail _ h => exact lz77Lazy.mainLoop_encodable _ _ _ _ _ _ hw hws t h
          · -- ¬(pos + 3 < data.size) → ref(matchLen, dist)
            intro t ht; cases ht with
            | head =>
              show 3 ≤ _ ∧ _ ≤ 258 ∧ 1 ≤ _ ∧ _ ≤ 32768
              exact ⟨hge, by omega, by omega, by omega⟩
            | tail _ h => exact lz77Lazy.mainLoop_encodable _ _ _ _ _ _ hw hws t h
        · -- ¬(pos + matchLen ≤ data.size) → literal
          intro t ht; cases ht with
          | head => trivial
          | tail _ h => exact lz77Lazy.mainLoop_encodable _ _ _ _ _ _ hw hws t h
      · -- ¬(matchLen ≥ 3) → literal
        intro t ht; cases ht with
        | head => trivial
        | tail _ h => exact lz77Lazy.mainLoop_encodable _ _ _ _ _ _ hw hws t h
    · -- ¬(isValid && ...) → literal
      intro t ht; cases ht with
      | head => trivial
      | tail _ h => exact lz77Lazy.mainLoop_encodable _ _ _ _ _ _ hw hws t h
  · exact lz77Lazy.trailing_encodable data pos
termination_by data.size - pos
decreasing_by all_goals omega

/-- All tokens from `lz77Lazy` have valid ranges for fixed Huffman encoding. -/
theorem lz77Lazy_encodable (data : ByteArray)
    (windowSize : Nat) (hw : windowSize > 0) (hws : windowSize ≤ 32768) :
    ∀ t ∈ (lz77Lazy data windowSize).toList,
      match t with
      | .literal _ => True
      | .reference len dist => 3 ≤ len ∧ len ≤ 258 ∧ 1 ≤ dist ∧ dist ≤ 32768 := by
  intro t ht
  have henc : Encodable t := by
    simp only [lz77Lazy] at ht
    split at ht
    · simp at ht; exact lz77Lazy.trailing_encodable data 0 t ht
    · simp at ht; exact lz77Lazy.mainLoop_encodable data windowSize 65536 _ _ 0 hw hws t ht
  exact henc

/-! ### Lazy mainLoop length bounds -/

private theorem lazy_length_one {n s pos pos' : Nat}
    (ih : n ≤ 2 * (s - pos')) (hlt : pos < pos') (hle : pos' ≤ s) :
    n + 1 ≤ 2 * (s - pos) := by omega

private theorem lazy_length_two {n s pos pos' : Nat}
    (ih : n ≤ 2 * (s - pos')) (hlt : pos < pos') (hle : pos' ≤ s) :
    n + 2 ≤ 2 * (s - pos) := by omega

theorem lz77Lazy.mainLoop_length (data : ByteArray) (windowSize hashSize : Nat)
    (hashTable : Array Nat) (hashValid : Array Bool) (pos : Nat) :
    (lz77Lazy.mainLoop data windowSize hashSize hashTable hashValid pos).length
      ≤ 2 * (data.size - pos) := by
  unfold lz77Lazy.mainLoop
  split
  · rename_i hlt
    dsimp only
    split
    · rename_i hcond
      split
      · -- matchLen ≥ 3 (positive)
        rename_i hge
        split
        · -- pos + matchLen ≤ data.size (positive)
          rename_i hle
          split
          · -- pos + 3 < data.size (positive) → lazy check
            split
            · -- isValid2 && ... (positive)
              split
              · -- matchLen2 > matchLen (positive)
                split
                · -- pos + 1 + matchLen2 ≤ data.size (positive)
                  rename_i hle2
                  simp only [List.length_cons]
                  exact lazy_length_two (lz77Lazy.mainLoop_length _ _ _ _ _ _) (by omega) hle2
                · -- fall back to ref(matchLen, dist)
                  simp only [List.length_cons]
                  exact lazy_length_one (lz77Lazy.mainLoop_length _ _ _ _ _ _) (by omega) hle
              · -- matchLen2 ≤ matchLen → ref(matchLen, dist)
                simp only [List.length_cons]
                exact lazy_length_one (lz77Lazy.mainLoop_length _ _ _ _ _ _) (by omega) hle
            · -- ¬(isValid2 && ...) → ref(matchLen, dist)
              simp only [List.length_cons]
              exact lazy_length_one (lz77Lazy.mainLoop_length _ _ _ _ _ _) (by omega) hle
          · -- ¬(pos + 3 < data.size) → ref(matchLen, dist)
            simp only [List.length_cons]
            exact lazy_length_one (lz77Lazy.mainLoop_length _ _ _ _ _ _) (by omega) hle
        · -- ¬(pos + matchLen ≤ data.size) → literal
          simp only [List.length_cons]
          exact lazy_length_one (lz77Lazy.mainLoop_length _ _ _ _ _ _) (by omega) (by omega)
      · -- ¬(matchLen ≥ 3) → literal
        simp only [List.length_cons]
        exact lazy_length_one (lz77Lazy.mainLoop_length _ _ _ _ _ _) (by omega) (by omega)
    · -- ¬(isValid && ...) → literal
      simp only [List.length_cons]
      exact lazy_length_one (lz77Lazy.mainLoop_length _ _ _ _ _ _) (by omega) (by omega)
  · have := lz77Lazy.trailing_length data pos; omega
termination_by data.size - pos
decreasing_by all_goals omega

/-- The token count from `lz77Lazy` is at most `2 * data.size`. In the worst
    case every position emits a literal + reference. -/
theorem lz77Lazy_size_le (data : ByteArray) (windowSize : Nat) :
    (lz77Lazy data windowSize).size ≤ 2 * data.size := by
  simp only [lz77Lazy]
  split
  · simp only [List.size_toArray]
    have := lz77Lazy.trailing_length data 0; omega
  · simp only [List.size_toArray]
    exact lz77Lazy.mainLoop_length data windowSize 65536
      (Array.replicate 65536 0) (Array.replicate 65536 false) 0

end Zip.Native.Deflate
