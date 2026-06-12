import Zip.Spec.LZ77NativeCorrect

/-!
# Correctness of the hash-chain LZ77 matcher (`lz77Chain`)

`lz77Chain` walks a bounded-depth `prev` chain to find longer matches than the
single-probe `lz77Greedy`/`lz77Lazy`. The chain is only a heuristic for *finding*
candidates: validity is re-established at emission by `countMatch` + the explicit
window guards, so the `prev`/`hashTable` contents never enter the proof. This
file proves `ValidDecomp` (→ `lz77Chain_resolves`) and encodability, exactly the
two contracts the dynamic/fixed encoders consume for any token stream.
-/

namespace Zip.Native.Deflate

open Zip.Native.Deflate (lz77Chain lz77Greedy)

/-- The match the chain walk returns is always a real in-window backward match
    (or empty): the invariant `Q` on `(bestLen, bestPos)` is preserved because
    every update records `countMatch`'s verified result at a guarded candidate. -/
theorem chainWalk_spec (data : ByteArray) (prev : Array Nat)
    (windowSize pos maxLen : Nat) (hpm : pos + maxLen ≤ data.size)
    (cand fuel bestLen bestPos : Nat)
    (hb : bestLen = 0 ∨ (bestPos < pos ∧ pos - bestPos ≤ windowSize ∧
        bestPos + maxLen ≤ data.size ∧
        (∀ i, i < bestLen → data[pos + i]! = data[bestPos + i]!) ∧ bestLen ≤ maxLen)) :
    let r := lz77Chain.chainWalk data prev windowSize pos maxLen hpm cand fuel bestLen bestPos
    r.1 = 0 ∨ (r.2 < pos ∧ pos - r.2 ≤ windowSize ∧ r.2 + maxLen ≤ data.size ∧
        (∀ i, i < r.1 → data[pos + i]! = data[r.2 + i]!) ∧ r.1 ≤ maxLen) := by
  induction fuel generalizing cand bestLen bestPos with
  | zero => rw [lz77Chain.chainWalk]; exact hb
  | succ k ih =>
    rw [lz77Chain.chainWalk, if_neg (by omega : ¬ (k + 1 = 0))]
    split
    · rename_i hc
      have hcand : cand + maxLen ≤ data.size := by omega
      have hcm := lz77Greedy.countMatch_matches data cand pos maxLen hcand hpm
      by_cases hml : lz77Greedy.countMatch data cand pos maxLen hcand hpm > bestLen
      · simp only [hml, ↓reduceIte]
        split
        · exact Or.inr ⟨hc.1, hc.2, hcand, fun i hi => (hcm.1 i hi).symm, hcm.2⟩
        · exact ih (prev[cand]!) _ _
            (Or.inr ⟨hc.1, hc.2, hcand, fun i hi => (hcm.1 i hi).symm, hcm.2⟩)
      · simp only [hml, ↓reduceIte]
        split
        · exact hb
        · exact ih (prev[cand]!) _ _ hb
    · exact hb

/-! ## Guarded per-position head insertion (Wave 3 Step 0.2)

The mainLoops perform their per-position chain-head insertion (and, in the
lazy variants, the lookahead head probe) through `headInsertGuarded`/
`headProbeGuarded`, which trade the panic-checked `[..]!`/`set!` operations
for one runtime bounds check. The lemmas below rewrite them back to the
original panic-checked operations, so every proof that unfolds a mainLoop
proceeds exactly as before the conversion. -/

/-- The guarded head insertion computes exactly the panic-checked triple:
    in bounds, `getElem!_pos` and `setIfInBounds_def` bridge `[..]'h`/`set`
    to `[..]!`/`set!`; out of bounds, the fallback *is* the panic-checked
    sequence. -/
theorem headInsertGuarded_eq (hashTable prev : Array Nat) (h pos : Nat) :
    headInsertGuarded hashTable prev h pos =
      (hashTable[h]!, hashTable.set! h pos, prev.set! pos hashTable[h]!) := by
  unfold headInsertGuarded
  split
  · rename_i hg
    simp only [getElem!_pos hashTable h hg.1, Array.set!_eq_setIfInBounds,
      Array.setIfInBounds_def, dif_pos hg.1, dif_pos hg.2]
  · rfl

/-- The guarded head probe computes exactly the panic-checked read. -/
theorem headProbeGuarded_eq (hashTable : Array Nat) (h : Nat) :
    headProbeGuarded hashTable h = hashTable[h]! := by
  unfold headProbeGuarded
  split
  · rename_i hb; exact (getElem!_pos hashTable h hb).symm
  · rfl

/-- `lz77Chain.mainLoop` produces a valid decomposition from `pos`. Mirrors
    `lz77Greedy.mainLoop_valid`; the reference case uses `chainWalk_spec` (which
    holds for *any* `prev` array) in place of the inline single-probe match. -/
theorem lz77Chain_mainLoop_valid (data : ByteArray) (windowSize hashSize maxChain : Nat)
    (hashTable prev : Array Nat) (pos insertCap : Nat) (hw : windowSize > 0) :
    ValidDecomp data pos
      (lz77Chain.mainLoop data windowSize hashSize maxChain hashTable prev pos insertCap) := by
  unfold lz77Chain.mainLoop
  split
  · rename_i hlt
    dsimp only
    simp only [headInsertGuarded_eq]
    have hspec := chainWalk_spec data
      (prev.set! pos hashTable[lz77Greedy.hash3 data pos hashSize hlt]!)
      windowSize pos (min 258 (data.size - pos)) (by omega)
      hashTable[lz77Greedy.hash3 data pos hashSize hlt]! maxChain 0 0 (Or.inl rfl)
    split
    · rename_i hge
      split
      · rename_i hle
        obtain h0 | hQ := hspec
        · omega
        · refine ValidDecomp.reference hge (by omega) (by omega) hle ?_ ?_
          · intro i hi
            rw [Nat.sub_sub_self (Nat.le_of_lt hQ.1)]
            exact hQ.2.2.2.1 i hi
          · exact lz77Chain_mainLoop_valid _ _ _ _ _ _ _ _ hw
      · exact .literal (by omega) (getElem!_pos data pos (by omega))
          (lz77Chain_mainLoop_valid _ _ _ _ _ _ _ _ hw)
    · exact .literal (by omega) (getElem!_pos data pos (by omega))
        (lz77Chain_mainLoop_valid _ _ _ _ _ _ _ _ hw)
  · exact trailing_valid data pos
termination_by data.size - pos
decreasing_by all_goals omega

/-- `lz77Chain` produces a valid decomposition of the input data. -/
theorem lz77Chain_valid (data : ByteArray) (maxChain windowSize insertCap : Nat)
    (hw : windowSize > 0) :
    ValidDecomp data 0 (lz77Chain data maxChain windowSize insertCap).toList := by
  simp only [lz77Chain]
  split
  · simp only; exact trailing_valid data 0
  · simp only; exact lz77Chain_mainLoop_valid data windowSize 65536 maxChain _ _ 0 insertCap hw

/-- Resolving the LZ77 tokens produced by `lz77Chain` recovers the original data. -/
theorem lz77Chain_resolves (data : ByteArray) (maxChain windowSize insertCap : Nat)
    (hw : windowSize > 0) :
    Deflate.Spec.resolveLZ77 (tokensToSymbols (lz77Chain data maxChain windowSize insertCap)) [] =
      some data.data.toList :=
  validDecomp_resolves data _ (lz77Chain_valid data maxChain windowSize insertCap hw)

/-! ## Encodability -/

/-- The bounds the dynamic/fixed encoders require of every token (inlined to
    match `deflateDynamicBlock_spec`'s `htok_enc` hypothesis). -/
private def Enc (t : LZ77Token) : Prop :=
  match t with
  | .literal _ => True
  | .reference len dist => 3 ≤ len ∧ len ≤ 258 ∧ 1 ≤ dist ∧ dist ≤ 32768

theorem lz77Chain_mainLoop_encodable (data : ByteArray) (windowSize hashSize maxChain : Nat)
    (hashTable prev : Array Nat) (pos insertCap : Nat) (hw : windowSize > 0) (hws : windowSize ≤ 32768) :
    ∀ t ∈ lz77Chain.mainLoop data windowSize hashSize maxChain hashTable prev pos insertCap, Enc t := by
  unfold lz77Chain.mainLoop
  split
  · rename_i hlt
    dsimp only
    simp only [headInsertGuarded_eq]
    have hspec := chainWalk_spec data
      (prev.set! pos hashTable[lz77Greedy.hash3 data pos hashSize hlt]!)
      windowSize pos (min 258 (data.size - pos)) (by omega)
      hashTable[lz77Greedy.hash3 data pos hashSize hlt]! maxChain 0 0 (Or.inl rfl)
    split
    · rename_i hge
      split
      · rename_i hle
        obtain h0 | ⟨hQ1, hQ2, _, _, hQ5⟩ := hspec
        · omega
        · intro t ht
          cases ht with
          | head => exact ⟨hge, by omega, by omega, by omega⟩
          | tail _ h => exact lz77Chain_mainLoop_encodable _ _ _ _ _ _ _ _ hw hws t h
      · intro t ht
        cases ht with
        | head => trivial
        | tail _ h => exact lz77Chain_mainLoop_encodable _ _ _ _ _ _ _ _ hw hws t h
    · intro t ht
      cases ht with
      | head => trivial
      | tail _ h => exact lz77Chain_mainLoop_encodable _ _ _ _ _ _ _ _ hw hws t h
  · intro t ht
    -- `trailing` emits only literals
    exact trailing_encodable data pos t ht
termination_by data.size - pos
decreasing_by all_goals omega

/-- Every token `lz77Chain` emits satisfies the encoder bounds. -/
theorem lz77Chain_encodable (data : ByteArray) (maxChain windowSize insertCap : Nat)
    (hw : windowSize > 0) (hws : windowSize ≤ 32768) :
    ∀ t ∈ (lz77Chain data maxChain windowSize insertCap).toList,
      match t with
      | .literal _ => True
      | .reference len dist => 3 ≤ len ∧ len ≤ 258 ∧ 1 ≤ dist ∧ dist ≤ 32768 := by
  simp only [lz77Chain]
  split
  · intro t ht; simp only [List.toList_toArray] at ht
    exact trailing_encodable data 0 t ht
  · intro t ht; simp only [List.toList_toArray] at ht
    exact lz77Chain_mainLoop_encodable data windowSize 65536 maxChain _ _ 0 insertCap hw hws t ht

/-! ## Proven-bounds matcher equivalences (Wave 2d)

`chainWalkFast`/`updateHashesFast` are the proven-bounds copies that the
iterative matchers run in their hot loops; each is provably equal to the
panic-checked reference helper. The `*Guarded` wrappers add one runtime
size check and fall back to the reference, so they share the reference's
signature and equal it. The iterative-vs-recursive equivalence proofs below
rewrite the guarded wrappers back to the reference helpers and then proceed
exactly as before the conversion. -/

/-- The proven-bounds chain walk computes the same `(bestLen, bestPos)` as the
    panic-checked reference walk: the bodies differ only in how `prev[cand]` is
    accessed (`'h` vs `!`), and `getElem!_pos` bridges the two. -/
theorem chainWalkFast_eq (data : ByteArray) (prev : Array Nat)
    (windowSize pos maxLen : Nat) (hpm : pos + maxLen ≤ data.size) (hps : pos ≤ prev.size)
    (cand fuel bestLen bestPos : Nat) :
    chainWalkFast data prev windowSize pos maxLen hpm hps cand fuel bestLen bestPos =
      lz77Chain.chainWalk data prev windowSize pos maxLen hpm cand fuel bestLen bestPos := by
  induction fuel generalizing cand bestLen bestPos with
  | zero => rw [chainWalkFast, lz77Chain.chainWalk]; simp only [↓reduceIte]
  | succ k ih =>
    rw [chainWalkFast, lz77Chain.chainWalk, if_neg (by omega : ¬ (k + 1 = 0)),
      if_neg (by omega : ¬ (k + 1 = 0))]
    by_cases hc : cand < pos ∧ pos - cand ≤ windowSize
    · simp only [dif_pos hc, Nat.add_sub_cancel, ih]
      rw [getElem!_pos prev cand (by omega)]
    · simp only [dif_neg hc]

/-- One runtime guard collapses to the reference walk. -/
theorem chainWalkGuarded_eq (data : ByteArray) (prev : Array Nat)
    (windowSize pos maxLen : Nat) (hpm : pos + maxLen ≤ data.size)
    (cand fuel bestLen bestPos : Nat) :
    chainWalkGuarded data prev windowSize pos maxLen hpm cand fuel bestLen bestPos =
      lz77Chain.chainWalk data prev windowSize pos maxLen hpm cand fuel bestLen bestPos := by
  unfold chainWalkGuarded
  split
  · exact chainWalkFast_eq ..
  · rfl

/-- The proven-bounds hash-insertion loop computes the same arrays as the
    panic-checked reference: the bodies differ only in how `hashTable[hsh]` is
    accessed, bridged by `getElem!_pos`. -/
theorem updateHashesFast_eq (data : ByteArray) (hashSize : Nat)
    (hashTable prev : Array Nat) (pos j matchLen insertCap : Nat)
    (hhs : 0 < hashSize) (hht : hashSize ≤ hashTable.size) :
    updateHashesFast data hashSize hashTable prev pos j matchLen insertCap hhs hht =
      lz77Chain.updateHashes data hashSize hashTable prev pos j matchLen insertCap := by
  induction hn : matchLen - j using Nat.strongRecOn generalizing j hashTable prev hht with
  | _ n ih =>
    unfold updateHashesFast lz77Chain.updateHashes
    by_cases hcond : j < matchLen ∧ j ≤ insertCap
    · rw [if_pos hcond, if_pos hcond]
      by_cases hd : pos + j + 2 < data.size
      · rw [dif_pos hd, dif_pos hd]
        have hb : lz77Greedy.hash3 data (pos + j) hashSize hd < hashTable.size := by
          have : lz77Greedy.hash3 data (pos + j) hashSize hd < hashSize := Nat.mod_lt _ hhs
          omega
        simp only [getElem!_pos hashTable (lz77Greedy.hash3 data (pos + j) hashSize hd) hb]
        exact ih _ (by omega) _ _ _ (by simpa using hht) rfl
      · rw [dif_neg hd, dif_neg hd]
        exact ih _ (by omega) _ _ _ hht rfl
    · rw [if_neg hcond, if_neg hcond]

/-- One runtime guard collapses to the reference insertion. -/
theorem updateHashesGuarded_eq (data : ByteArray) (hashSize : Nat)
    (hashTable prev : Array Nat) (pos j matchLen insertCap : Nat) :
    updateHashesGuarded data hashSize hashTable prev pos j matchLen insertCap =
      lz77Chain.updateHashes data hashSize hashTable prev pos j matchLen insertCap := by
  unfold updateHashesGuarded
  split
  · exact updateHashesFast_eq ..
  · rfl

/-! ## Iterative version: equivalence + transferred contracts -/

/-- The accumulator `trailing` is the array form of the recursive one. -/
private theorem trailing_eq (data : ByteArray) (pos : Nat) (acc : Array LZ77Token) :
    lz77GreedyIter.trailing data pos acc = acc ++ (lz77Greedy.trailing data pos).toArray := by
  induction h : data.size - pos using Nat.strongRecOn generalizing pos acc with
  | _ n ih =>
    unfold lz77GreedyIter.trailing lz77Greedy.trailing
    by_cases hp : pos < data.size
    · simp only [hp, ↓reduceDIte]
      rw [ih _ (by omega) _ _ rfl, List.toArray_cons, ← Array.append_assoc, Array.push_eq_append]
    · simp only [hp, ↓reduceDIte, List.toArray, Array.append_empty]

/-- The iterative chain `mainLoop` is the accumulator form of the recursive one.
    The `chainWalk`/`updateHashes` helpers are shared, so the only difference is
    push vs. cons at each emission. -/
private theorem mainLoop_eq_chain (data : ByteArray) (windowSize hashSize maxChain insertCap : Nat)
    (hashTable prev : Array Nat) (pos : Nat) (acc : Array LZ77Token) :
    lz77ChainIter.mainLoop data windowSize hashSize maxChain insertCap hashTable prev pos acc =
    acc ++ (lz77Chain.mainLoop data windowSize hashSize maxChain hashTable prev pos insertCap).toArray := by
  induction h : data.size - pos using Nat.strongRecOn generalizing pos acc hashTable prev with
  | _ n ih =>
    unfold lz77ChainIter.mainLoop lz77Chain.mainLoop
    simp only [chainWalkGuarded_eq, updateHashesGuarded_eq, headInsertGuarded_eq]
    by_cases hlt : pos + 2 < data.size
    · simp only [hlt, ↓reduceDIte]
      split
      · split
        · rw [ih _ (by omega) _ _ _ _ rfl, List.toArray_cons,
            ← Array.append_assoc, Array.push_eq_append]
        · rw [ih _ (by omega) _ _ _ _ rfl, List.toArray_cons,
            ← Array.append_assoc, Array.push_eq_append]
      · rw [ih _ (by omega) _ _ _ _ rfl, List.toArray_cons,
          ← Array.append_assoc, Array.push_eq_append]
    · simp only [hlt, ↓reduceDIte]
      exact trailing_eq data pos acc

/-- `lz77ChainIter` produces exactly the same tokens as `lz77Chain`. -/
theorem lz77ChainIter_eq_lz77Chain (data : ByteArray) (maxChain windowSize insertCap : Nat) :
    lz77ChainIter data maxChain windowSize insertCap = lz77Chain data maxChain windowSize insertCap := by
  unfold lz77ChainIter lz77Chain
  split
  · rw [trailing_eq]; simp only [List.append_toArray, List.nil_append]
  · rw [mainLoop_eq_chain]; simp only [List.append_toArray, List.nil_append]

theorem lz77ChainIter_valid (data : ByteArray) (maxChain windowSize insertCap : Nat)
    (hw : windowSize > 0) :
    ValidDecomp data 0 (lz77ChainIter data maxChain windowSize insertCap).toList := by
  rw [lz77ChainIter_eq_lz77Chain]; exact lz77Chain_valid data maxChain windowSize insertCap hw

theorem lz77ChainIter_resolves (data : ByteArray) (maxChain windowSize insertCap : Nat)
    (hw : windowSize > 0) :
    Deflate.Spec.resolveLZ77 (tokensToSymbols (lz77ChainIter data maxChain windowSize insertCap)) [] =
      some data.data.toList := by
  rw [lz77ChainIter_eq_lz77Chain]; exact lz77Chain_resolves data maxChain windowSize insertCap hw

theorem lz77ChainIter_encodable (data : ByteArray) (maxChain windowSize insertCap : Nat)
    (hw : windowSize > 0) (hws : windowSize ≤ 32768) :
    ∀ t ∈ (lz77ChainIter data maxChain windowSize insertCap).toList,
      match t with
      | .literal _ => True
      | .reference len dist => 3 ≤ len ∧ len ≤ 258 ∧ 1 ≤ dist ∧ dist ≤ 32768 := by
  rw [lz77ChainIter_eq_lz77Chain]; exact lz77Chain_encodable data maxChain windowSize insertCap hw hws

/-- The chain matcher emits no tokens on empty input. -/
theorem lz77ChainIter_empty (data : ByteArray) (maxChain windowSize insertCap : Nat)
    (hzero : data.size = 0) : lz77ChainIter data maxChain windowSize insertCap = #[] := by
  rw [lz77ChainIter_eq_lz77Chain]
  simp only [lz77Chain, show data.size < 3 from by omega, ↓reduceIte]
  have htrail : lz77Greedy.trailing data 0 = [] := by
    unfold lz77Greedy.trailing
    simp only [show ¬(0 < data.size) from by omega, ↓reduceDIte]
  rw [htrail]

end Zip.Native.Deflate
