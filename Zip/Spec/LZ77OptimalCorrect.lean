import Zip.Spec.LZ77NativeCorrect
import Zip.Native.DeflateParse

/-!
# Correctness of the near-optimal LZ parser (`lz77Optimal`)

The DP machinery in `Zip.Native.DeflateParse` (candidate cache, cost tables,
cost/choice arrays) is entirely heuristic: `optimalEmit` re-establishes
validity for every match it emits — the `lz77Chain` guards plus a fresh
`countMatch` confirming the stored length — and falls back to a literal
otherwise. Accordingly, every theorem here is stated for **arbitrary**
`chLen`/`chDist` choice arrays: nothing about the DP enters the proofs, which
makes them immune to any future tuning of the parser.

What is proven: validity (`ValidDecomp`, hence `lz77Optimal_resolves`) and
encodability — the two contracts the encoders consume for any token stream.
What is *not* proven (and intentionally so, per the project's spec-quality
discipline): optimality of the parse. The cost model is a heuristic estimate;
compression quality is measured (benchmarks + the ratio canary in
`ZipTest.OptimalParse`), not certified.
-/

namespace Zip.Native.Deflate

/-- `optimalEmit` produces a valid decomposition from `pos`, for arbitrary
    choice arrays: the emission guard + `countMatch` re-verification hand
    over every `ValidDecomp.reference` hypothesis directly. -/
theorem optimalEmit_valid (data : ByteArray) (chLen chDist : Array Nat) (pos : Nat) :
    ValidDecomp data pos (optimalEmit data chLen chDist pos) := by
  unfold optimalEmit
  split
  · rename_i hpos
    dsimp only
    -- The literal fallback is shared by both the guard-fail and
    -- countMatch-fail branches; bind it once.
    have hlit : ValidDecomp data pos
        (.literal (data[pos]'hpos) :: optimalEmit data chLen chDist (pos + 1)) :=
      .literal hpos (getElem!_pos data pos hpos)
        (optimalEmit_valid data chLen chDist (pos + 1))
    split
    · rename_i hg
      split
      · rename_i hml
        refine ValidDecomp.reference hg.1 hg.2.2.2.1 hg.2.2.2.2.1 hg.2.2.1 ?_ ?_
        · intro i hi
          have hcm := lz77Greedy.countMatch_matches data (pos - chDist[pos]!) pos
            chLen[pos]! (by omega) hg.2.2.1
          exact (hcm.1 i (by omega)).symm
        · exact optimalEmit_valid data chLen chDist (pos + chLen[pos]!)
      · exact hlit
    · exact hlit
  · exact .done (by omega)
termination_by data.size - pos
decreasing_by all_goals omega

/-- Every token `optimalEmit` emits satisfies the encoder bounds, for
    arbitrary choice arrays (read straight off the emission guard). -/
theorem optimalEmit_encodable (data : ByteArray) (chLen chDist : Array Nat) (pos : Nat) :
    ∀ t ∈ optimalEmit data chLen chDist pos,
      match t with
      | .literal _ => True
      | .reference len dist => 3 ≤ len ∧ len ≤ 258 ∧ 1 ≤ dist ∧ dist ≤ 32768 := by
  unfold optimalEmit
  split
  · rename_i hpos
    dsimp only
    -- Each branch is a cons whose tail is handled by the IH; only the head
    -- differs (reference bounds off the guard, or a trivial literal).
    split
    · rename_i hg
      split
      · exact List.forall_mem_cons.2 ⟨⟨hg.1, hg.2.1, hg.2.2.2.1, hg.2.2.2.2.2⟩,
          optimalEmit_encodable data chLen chDist _⟩
      · exact List.forall_mem_cons.2 ⟨trivial, optimalEmit_encodable data chLen chDist _⟩
    · exact List.forall_mem_cons.2 ⟨trivial, optimalEmit_encodable data chLen chDist _⟩
  · intro t ht; cases ht
termination_by data.size - pos
decreasing_by all_goals omega

/-- The iterative emitter is the accumulator form of the recursive one. -/
private theorem optimalEmitIter_eq_emit (data : ByteArray) (chLen chDist : Array Nat)
    (pos : Nat) (acc : Array LZ77Token) :
    optimalEmitIter data chLen chDist pos acc =
      acc ++ (optimalEmit data chLen chDist pos).toArray := by
  induction h : data.size - pos using Nat.strongRecOn generalizing pos acc with
  | _ n ih =>
    unfold optimalEmitIter optimalEmit
    by_cases hpos : pos < data.size
    · simp only [hpos, ↓reduceDIte]
      split
      · rename_i hg
        split
        · rw [ih _ (by omega) _ _ rfl, List.toArray_cons,
            ← Array.append_assoc, Array.push_eq_append]
        · rw [ih _ (by omega) _ _ rfl, List.toArray_cons,
            ← Array.append_assoc, Array.push_eq_append]
      · rw [ih _ (by omega) _ _ rfl, List.toArray_cons,
          ← Array.append_assoc, Array.push_eq_append]
    · simp only [hpos, ↓reduceDIte, List.toArray, Array.append_empty]

/-- `lz77OptimalIter` produces exactly the same tokens as `lz77Optimal`. -/
theorem lz77OptimalIter_eq_lz77Optimal (data : ByteArray) :
    lz77OptimalIter data = lz77Optimal data := by
  unfold lz77OptimalIter lz77Optimal
  obtain ⟨chLen, chDist⟩ := computeChoices data
  dsimp only
  rw [optimalEmitIter_eq_emit]
  simp only [List.append_toArray, List.nil_append]

/-- `lz77Optimal` produces a valid decomposition of the input data. -/
theorem lz77Optimal_valid (data : ByteArray) :
    ValidDecomp data 0 (lz77Optimal data).toList := by
  unfold lz77Optimal
  obtain ⟨chLen, chDist⟩ := computeChoices data
  dsimp only
  exact optimalEmit_valid data chLen chDist 0

/-- Resolving the LZ77 tokens produced by `lz77Optimal` recovers the data. -/
theorem lz77Optimal_resolves (data : ByteArray) :
    Deflate.Spec.resolveLZ77 (tokensToSymbols (lz77Optimal data)) [] =
      some data.data.toList :=
  validDecomp_resolves data _ (lz77Optimal_valid data)

/-- Every token `lz77Optimal` emits satisfies the encoder bounds. -/
theorem lz77Optimal_encodable (data : ByteArray) :
    ∀ t ∈ (lz77Optimal data).toList,
      match t with
      | .literal _ => True
      | .reference len dist => 3 ≤ len ∧ len ≤ 258 ∧ 1 ≤ dist ∧ dist ≤ 32768 := by
  unfold lz77Optimal
  obtain ⟨chLen, chDist⟩ := computeChoices data
  intro t ht
  dsimp only at ht
  exact optimalEmit_encodable data chLen chDist 0 t ht

/-- The optimal parser emits no tokens on empty input. -/
theorem lz77Optimal_empty (data : ByteArray) (hzero : data.size = 0) :
    lz77Optimal data = #[] := by
  unfold lz77Optimal
  obtain ⟨chLen, chDist⟩ := computeChoices data
  dsimp only
  unfold optimalEmit
  simp only [show ¬(0 < data.size) from by omega, ↓reduceDIte, List.toArray]

/-! ## Iterative-version contracts (the runtime entry point) -/

theorem lz77OptimalIter_valid (data : ByteArray) :
    ValidDecomp data 0 (lz77OptimalIter data).toList := by
  rw [lz77OptimalIter_eq_lz77Optimal]; exact lz77Optimal_valid data

theorem lz77OptimalIter_resolves (data : ByteArray) :
    Deflate.Spec.resolveLZ77 (tokensToSymbols (lz77OptimalIter data)) [] =
      some data.data.toList := by
  rw [lz77OptimalIter_eq_lz77Optimal]; exact lz77Optimal_resolves data

theorem lz77OptimalIter_encodable (data : ByteArray) :
    ∀ t ∈ (lz77OptimalIter data).toList,
      match t with
      | .literal _ => True
      | .reference len dist => 3 ≤ len ∧ len ≤ 258 ∧ 1 ≤ dist ∧ dist ≤ 32768 := by
  rw [lz77OptimalIter_eq_lz77Optimal]; exact lz77Optimal_encodable data

theorem lz77OptimalIter_empty (data : ByteArray) (hzero : data.size = 0) :
    lz77OptimalIter data = #[] := by
  rw [lz77OptimalIter_eq_lz77Optimal]; exact lz77Optimal_empty data hzero

/-! ## L9-fast parser contracts (#2638)

`lz77OptimalFast` shares the *arbitrary*-choice-array emitter `optimalEmit` with
`lz77Optimal`; only the (heuristic) choice arrays differ (`computeChoicesFast`).
So every contract transfers verbatim — the proofs are byte-for-byte the exact
ones with `computeChoicesFast` substituted, exactly as the file's opening note
promises ("immune to any future tuning of the parser"). -/

theorem lz77OptimalFastIter_eq_lz77OptimalFast (data : ByteArray) :
    lz77OptimalFastIter data = lz77OptimalFast data := by
  unfold lz77OptimalFastIter lz77OptimalFast
  obtain ⟨chLen, chDist⟩ := computeChoicesFast data
  dsimp only
  rw [optimalEmitIter_eq_emit]
  simp only [List.append_toArray, List.nil_append]

theorem lz77OptimalFast_valid (data : ByteArray) :
    ValidDecomp data 0 (lz77OptimalFast data).toList := by
  unfold lz77OptimalFast
  obtain ⟨chLen, chDist⟩ := computeChoicesFast data
  dsimp only
  exact optimalEmit_valid data chLen chDist 0

theorem lz77OptimalFast_resolves (data : ByteArray) :
    Deflate.Spec.resolveLZ77 (tokensToSymbols (lz77OptimalFast data)) [] =
      some data.data.toList :=
  validDecomp_resolves data _ (lz77OptimalFast_valid data)

theorem lz77OptimalFast_encodable (data : ByteArray) :
    ∀ t ∈ (lz77OptimalFast data).toList,
      match t with
      | .literal _ => True
      | .reference len dist => 3 ≤ len ∧ len ≤ 258 ∧ 1 ≤ dist ∧ dist ≤ 32768 := by
  unfold lz77OptimalFast
  obtain ⟨chLen, chDist⟩ := computeChoicesFast data
  intro t ht
  dsimp only at ht
  exact optimalEmit_encodable data chLen chDist 0 t ht

theorem lz77OptimalFast_empty (data : ByteArray) (hzero : data.size = 0) :
    lz77OptimalFast data = #[] := by
  unfold lz77OptimalFast
  obtain ⟨chLen, chDist⟩ := computeChoicesFast data
  dsimp only
  unfold optimalEmit
  simp only [show ¬(0 < data.size) from by omega, ↓reduceDIte, List.toArray]

theorem lz77OptimalFastIter_valid (data : ByteArray) :
    ValidDecomp data 0 (lz77OptimalFastIter data).toList := by
  rw [lz77OptimalFastIter_eq_lz77OptimalFast]; exact lz77OptimalFast_valid data

theorem lz77OptimalFastIter_resolves (data : ByteArray) :
    Deflate.Spec.resolveLZ77 (tokensToSymbols (lz77OptimalFastIter data)) [] =
      some data.data.toList := by
  rw [lz77OptimalFastIter_eq_lz77OptimalFast]; exact lz77OptimalFast_resolves data

theorem lz77OptimalFastIter_encodable (data : ByteArray) :
    ∀ t ∈ (lz77OptimalFastIter data).toList,
      match t with
      | .literal _ => True
      | .reference len dist => 3 ≤ len ∧ len ≤ 258 ∧ 1 ≤ dist ∧ dist ≤ 32768 := by
  rw [lz77OptimalFastIter_eq_lz77OptimalFast]; exact lz77OptimalFast_encodable data

theorem lz77OptimalFastIter_empty (data : ByteArray) (hzero : data.size = 0) :
    lz77OptimalFastIter data = #[] := by
  rw [lz77OptimalFastIter_eq_lz77OptimalFast]; exact lz77OptimalFast_empty data hzero

end Zip.Native.Deflate
