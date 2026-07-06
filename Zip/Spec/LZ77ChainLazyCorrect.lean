import Zip.Spec.LZ77ChainCorrect

/-!
# Correctness of the lazy hash-chain LZ77 matcher (`lz77ChainLazy`)

`lz77ChainLazy` is the one-byte-lookahead (zlib `deflate_slow`-style) variant of
`lz77Chain`: at each position it runs a second `chainWalk` at `pos+1` and, when
that finds a longer match, emits a literal at `pos` and defers. The lookahead is
*only a choice among valid matches* — every emitted reference is re-verified at
emission by `chainWalk_spec` (which holds for any `prev` array), so the
lookahead's chain state never enters the proof. This file proves the same three
contracts the dynamic/fixed encoders consume (`ValidDecomp` → `resolveLZ77`,
encodability, empty), mirroring `LZ77ChainCorrect`; the lookahead emission reuses
`lazyRef_at_pos` from `LZ77NativeCorrect`.
-/

namespace Zip.Native.Deflate

open Zip.Native.Deflate (lz77ChainLazy lz77Chain lz77Greedy)

/-! ## Validity -/

set_option backward.split false in
/-- `lz77ChainLazy.mainLoop` produces a valid decomposition from `pos`. The
    reference cases use `chainWalk_spec` (at `pos`, and again at `pos+1` for the
    lookahead) exactly as `lz77Chain_mainLoop_valid` does for the single match. -/
theorem lz77ChainLazy_mainLoop_valid (data : ByteArray) (windowSize hashSize maxChain : Nat)
    (hashTable : Array Nat) (prev : Array Nat) (pos insertCap goodMatch niceLen lazyDepth : Nat) (hw : windowSize > 0) :
    ValidDecomp data pos
      (lz77ChainLazy.mainLoop data windowSize hashSize maxChain hashTable prev pos insertCap goodMatch niceLen lazyDepth) := by
  unfold lz77ChainLazy.mainLoop
  split
  · rename_i hlt
    dsimp only
    simp only [headProbeGuarded_eq, guardedSet_eq]
    have hspec := chainWalk_spec data
      (prev.set! (pos &&& 0x7FFF) hashTable[lz77Greedy.hash3 data pos hashSize hlt]!)
      windowSize pos (min 258 (data.size - pos)) niceLen (by omega)
      hashTable[lz77Greedy.hash3 data pos hashSize hlt]! maxChain 0 0 (Or.inl rfl)
    split
    · rename_i hge
      split
      · rename_i hle
        obtain h0 | hQ := hspec
        · omega
        · split
          · rename_i h3lt
            -- Lazy gate: matchLen < goodMatch runs the lookahead; otherwise emit M.
            split
            · have hspec2 := chainWalk_spec data
                (prev.set! (pos &&& 0x7FFF) hashTable[lz77Greedy.hash3 data pos hashSize hlt]!)
                windowSize (pos + 1) (min 258 (data.size - (pos + 1))) niceLen (by omega)
                (hashTable.set! (lz77Greedy.hash3 data pos hashSize hlt) pos)[
                  lz77Greedy.hash3 data (pos + 1) hashSize (by omega)]!
                lazyDepth 0 0 (Or.inl rfl)
              split
              · split
                · rename_i hle2
                  obtain h0' | hQ2 := hspec2
                  · omega
                  · exact .literal (by omega) (getElem!_pos data pos (by omega))
                      (lazyRef_at_pos data (pos + 1) _ _ hQ2.1 (by omega) hle2
                        (fun i hi => hQ2.2.2.2.1 i hi)
                        (lz77ChainLazy_mainLoop_valid _ _ _ _ _ _ _ _ _ _ _ hw))
                · exact lazyRef_at_pos data pos _ _ hQ.1 hge hle (fun i hi => hQ.2.2.2.1 i hi)
                    (lz77ChainLazy_mainLoop_valid _ _ _ _ _ _ _ _ _ _ _ hw)
              · exact lazyRef_at_pos data pos _ _ hQ.1 hge hle (fun i hi => hQ.2.2.2.1 i hi)
                  (lz77ChainLazy_mainLoop_valid _ _ _ _ _ _ _ _ _ _ _ hw)
            · exact lazyRef_at_pos data pos _ _ hQ.1 hge hle (fun i hi => hQ.2.2.2.1 i hi)
                (lz77ChainLazy_mainLoop_valid _ _ _ _ _ _ _ _ _ _ _ hw)
          · exact lazyRef_at_pos data pos _ _ hQ.1 hge hle (fun i hi => hQ.2.2.2.1 i hi)
              (lz77ChainLazy_mainLoop_valid _ _ _ _ _ _ _ _ _ _ _ hw)
      · exact .literal (by omega) (getElem!_pos data pos (by omega))
          (lz77ChainLazy_mainLoop_valid _ _ _ _ _ _ _ _ _ _ _ hw)
    · exact .literal (by omega) (getElem!_pos data pos (by omega))
        (lz77ChainLazy_mainLoop_valid _ _ _ _ _ _ _ _ _ _ _ hw)
  · exact trailing_valid data pos
termination_by data.size - pos
decreasing_by all_goals omega

/-- `lz77ChainLazy` produces a valid decomposition of the input data. -/
theorem lz77ChainLazy_valid (data : ByteArray) (maxChain windowSize insertCap goodMatch niceLen lazyDepth : Nat)
    (hw : windowSize > 0) :
    ValidDecomp data 0 (lz77ChainLazy data maxChain windowSize insertCap goodMatch niceLen lazyDepth).toList := by
  simp only [lz77ChainLazy]
  split
  · simp only; exact trailing_valid data 0
  · simp only; exact lz77ChainLazy_mainLoop_valid data windowSize 65536 maxChain _ _ 0 insertCap goodMatch niceLen lazyDepth hw

/-- Resolving the LZ77 tokens produced by `lz77ChainLazy` recovers the original data. -/
theorem lz77ChainLazy_resolves (data : ByteArray) (maxChain windowSize insertCap goodMatch niceLen lazyDepth : Nat)
    (hw : windowSize > 0) :
    Deflate.Spec.resolveLZ77 (tokensToSymbols (lz77ChainLazy data maxChain windowSize insertCap goodMatch niceLen lazyDepth)) [] =
      some data.data.toList :=
  validDecomp_resolves data _ (lz77ChainLazy_valid data maxChain windowSize insertCap goodMatch niceLen lazyDepth hw)

/-! ## Encodability -/

/-- The bounds the dynamic/fixed encoders require of every token. -/
private def Enc (t : LZ77Token) : Prop :=
  match t with
  | .literal _ => True
  | .reference len dist => 3 ≤ len ∧ len ≤ 258 ∧ 1 ≤ dist ∧ dist ≤ 32768

set_option backward.split false in
theorem lz77ChainLazy_mainLoop_encodable (data : ByteArray) (windowSize hashSize maxChain : Nat)
    (hashTable : Array Nat) (prev : Array Nat) (pos insertCap goodMatch niceLen lazyDepth : Nat) (hw : windowSize > 0) (hws : windowSize ≤ 32768) :
    ∀ t ∈ lz77ChainLazy.mainLoop data windowSize hashSize maxChain hashTable prev pos insertCap goodMatch niceLen lazyDepth, Enc t := by
  unfold lz77ChainLazy.mainLoop
  split
  · rename_i hlt
    dsimp only
    simp only [headProbeGuarded_eq, guardedSet_eq]
    have hspec := chainWalk_spec data
      (prev.set! (pos &&& 0x7FFF) hashTable[lz77Greedy.hash3 data pos hashSize hlt]!)
      windowSize pos (min 258 (data.size - pos)) niceLen (by omega)
      hashTable[lz77Greedy.hash3 data pos hashSize hlt]! maxChain 0 0 (Or.inl rfl)
    split
    · rename_i hge
      split
      · rename_i hle
        obtain h0 | ⟨hQ1, hQ2, _, _, hQ5⟩ := hspec
        · omega
        · split
          · rename_i h3lt
            -- Lazy gate: matchLen < goodMatch runs the lookahead; otherwise emit M.
            split
            · have hspec2 := chainWalk_spec data
                (prev.set! (pos &&& 0x7FFF) hashTable[lz77Greedy.hash3 data pos hashSize hlt]!)
                windowSize (pos + 1) (min 258 (data.size - (pos + 1))) niceLen (by omega)
                (hashTable.set! (lz77Greedy.hash3 data pos hashSize hlt) pos)[
                  lz77Greedy.hash3 data (pos + 1) hashSize (by omega)]!
                lazyDepth 0 0 (Or.inl rfl)
              split
              · split
                · rename_i hle2
                  obtain h0' | ⟨hQ2a, hQ2b, _, _, hQ2e⟩ := hspec2
                  · omega
                  · intro t ht
                    cases ht with
                    | head => trivial
                    | tail _ h =>
                      cases h with
                      | head => exact ⟨by omega, by omega, by omega, by omega⟩
                      | tail _ h => exact lz77ChainLazy_mainLoop_encodable _ _ _ _ _ _ _ _ _ _ _ hw hws t h
                · intro t ht
                  cases ht with
                  | head => exact ⟨hge, by omega, by omega, by omega⟩
                  | tail _ h => exact lz77ChainLazy_mainLoop_encodable _ _ _ _ _ _ _ _ _ _ _ hw hws t h
              · intro t ht
                cases ht with
                | head => exact ⟨hge, by omega, by omega, by omega⟩
                | tail _ h => exact lz77ChainLazy_mainLoop_encodable _ _ _ _ _ _ _ _ _ _ _ hw hws t h
            · intro t ht
              cases ht with
              | head => exact ⟨hge, by omega, by omega, by omega⟩
              | tail _ h => exact lz77ChainLazy_mainLoop_encodable _ _ _ _ _ _ _ _ _ _ _ hw hws t h
          · intro t ht
            cases ht with
            | head => exact ⟨hge, by omega, by omega, by omega⟩
            | tail _ h => exact lz77ChainLazy_mainLoop_encodable _ _ _ _ _ _ _ _ _ _ _ hw hws t h
      · intro t ht
        cases ht with
        | head => trivial
        | tail _ h => exact lz77ChainLazy_mainLoop_encodable _ _ _ _ _ _ _ _ _ _ _ hw hws t h
    · intro t ht
      cases ht with
      | head => trivial
      | tail _ h => exact lz77ChainLazy_mainLoop_encodable _ _ _ _ _ _ _ _ _ _ _ hw hws t h
  · intro t ht
    exact trailing_encodable data pos t ht
termination_by data.size - pos
decreasing_by all_goals omega

/-- Every token `lz77ChainLazy` emits satisfies the encoder bounds. -/
theorem lz77ChainLazy_encodable (data : ByteArray) (maxChain windowSize insertCap goodMatch niceLen lazyDepth : Nat)
    (hw : windowSize > 0) (hws : windowSize ≤ 32768) :
    ∀ t ∈ (lz77ChainLazy data maxChain windowSize insertCap goodMatch niceLen lazyDepth).toList,
      match t with
      | .literal _ => True
      | .reference len dist => 3 ≤ len ∧ len ≤ 258 ∧ 1 ≤ dist ∧ dist ≤ 32768 := by
  simp only [lz77ChainLazy]
  split
  · intro t ht
    exact trailing_encodable data 0 t ht
  · intro t ht
    exact lz77ChainLazy_mainLoop_encodable data windowSize 65536 maxChain _ _ 0 insertCap goodMatch niceLen lazyDepth hw hws t ht

/-! ## Iterative version: equivalence + transferred contracts -/

/-- The iterative lazy chain `mainLoop` is the accumulator form of the recursive
    one — identical branch structure, push vs. cons at each emission (two pushes in
    the lookahead arm). -/
private theorem mainLoop_eq_chainLazy (data : ByteArray) (windowSize hashSize maxChain insertCap goodMatch niceLen lazyDepth : Nat)
    (hashTable : Array Nat) (prev : Array Nat) (pos : Nat) (acc : Array LZ77Token) :
    lz77ChainLazyIter.mainLoop data windowSize hashSize maxChain insertCap goodMatch niceLen lazyDepth hashTable prev pos acc =
    acc ++ (lz77ChainLazy.mainLoop data windowSize hashSize maxChain hashTable prev pos insertCap goodMatch niceLen lazyDepth).toArray := by
  induction h : data.size - pos using Nat.strongRecOn generalizing pos acc hashTable prev with
  | _ n ih =>
    unfold lz77ChainLazyIter.mainLoop lz77ChainLazy.mainLoop
    simp only [chainWalkGuardedPacked_mod, chainWalkGuardedPacked_div, min258_le_511,
      updateHashesGuarded_eq]
    by_cases hlt : pos + 2 < data.size
    · simp only [hlt, ↓reduceDIte]
      -- Branch tree: hge / hle / h3lt / gate (matchLen < goodMatch) / (matchLen2 > matchLen) / hle2
      split
      · -- hge : matchLen ≥ 3
        split
        · -- hle : pos + matchLen ≤ data.size
          split
          · -- h3lt : pos + 3 < data.size
            split
            · -- matchLen < goodMatch : lookahead
              split
              · -- matchLen2 > matchLen
                split
                · -- hle2 : lookahead emits literal + reference(matchLen2), two pushes
                  rw [ih _ (by omega) _ _ _ _ rfl,
                    Array.push_eq_append, Array.push_eq_append,
                    Array.append_assoc, Array.append_assoc,
                    ← List.toArray_cons, ← List.toArray_cons]
                · -- ¬hle2 : reference(matchLen) at pos
                  rw [ih _ (by omega) _ _ _ _ rfl, List.toArray_cons,
                    ← Array.append_assoc, Array.push_eq_append]
              · -- matchLen2 ≤ matchLen : reference(matchLen) at pos
                rw [ih _ (by omega) _ _ _ _ rfl, List.toArray_cons,
                  ← Array.append_assoc, Array.push_eq_append]
            · -- matchLen ≥ goodMatch (gated) : reference(matchLen) at pos
              rw [ih _ (by omega) _ _ _ _ rfl, List.toArray_cons,
                ← Array.append_assoc, Array.push_eq_append]
          · -- ¬h3lt : reference(matchLen) at pos (near end)
            rw [ih _ (by omega) _ _ _ _ rfl, List.toArray_cons,
              ← Array.append_assoc, Array.push_eq_append]
        · -- ¬hle : literal
          rw [ih _ (by omega) _ _ _ _ rfl, List.toArray_cons,
            ← Array.append_assoc, Array.push_eq_append]
      · -- ¬hge : literal
        rw [ih _ (by omega) _ _ _ _ rfl, List.toArray_cons,
          ← Array.append_assoc, Array.push_eq_append]
    · simp only [hlt, ↓reduceDIte]
      exact trailing_eq data pos acc

/-- `lz77ChainLazyIter` produces exactly the same tokens as `lz77ChainLazy`. -/
theorem lz77ChainLazyIter_eq_lz77ChainLazy (data : ByteArray) (maxChain windowSize insertCap goodMatch niceLen lazyDepth : Nat) :
    lz77ChainLazyIter data maxChain windowSize insertCap goodMatch niceLen lazyDepth =
      lz77ChainLazy data maxChain windowSize insertCap goodMatch niceLen lazyDepth := by
  unfold lz77ChainLazyIter lz77ChainLazy
  split
  · rw [trailing_eq]; simp only [List.append_toArray, List.nil_append]
  · rw [mainLoop_eq_chainLazy]; simp only [List.append_toArray, List.nil_append]

theorem lz77ChainLazyIter_valid (data : ByteArray) (maxChain windowSize insertCap goodMatch niceLen lazyDepth : Nat)
    (hw : windowSize > 0) :
    ValidDecomp data 0 (lz77ChainLazyIter data maxChain windowSize insertCap goodMatch niceLen lazyDepth).toList := by
  rw [lz77ChainLazyIter_eq_lz77ChainLazy]; exact lz77ChainLazy_valid data maxChain windowSize insertCap goodMatch niceLen lazyDepth hw

theorem lz77ChainLazyIter_resolves (data : ByteArray) (maxChain windowSize insertCap goodMatch niceLen lazyDepth : Nat)
    (hw : windowSize > 0) :
    Deflate.Spec.resolveLZ77 (tokensToSymbols (lz77ChainLazyIter data maxChain windowSize insertCap goodMatch niceLen lazyDepth)) [] =
      some data.data.toList := by
  rw [lz77ChainLazyIter_eq_lz77ChainLazy]; exact lz77ChainLazy_resolves data maxChain windowSize insertCap goodMatch niceLen lazyDepth hw

theorem lz77ChainLazyIter_encodable (data : ByteArray) (maxChain windowSize insertCap goodMatch niceLen lazyDepth : Nat)
    (hw : windowSize > 0) (hws : windowSize ≤ 32768) :
    ∀ t ∈ (lz77ChainLazyIter data maxChain windowSize insertCap goodMatch niceLen lazyDepth).toList,
      match t with
      | .literal _ => True
      | .reference len dist => 3 ≤ len ∧ len ≤ 258 ∧ 1 ≤ dist ∧ dist ≤ 32768 := by
  rw [lz77ChainLazyIter_eq_lz77ChainLazy]
  exact lz77ChainLazy_encodable data maxChain windowSize insertCap goodMatch niceLen lazyDepth hw hws

/-- The lazy chain matcher emits no tokens on empty input. -/
theorem lz77ChainLazyIter_empty (data : ByteArray) (maxChain windowSize insertCap goodMatch niceLen lazyDepth : Nat)
    (hzero : data.size = 0) : lz77ChainLazyIter data maxChain windowSize insertCap goodMatch niceLen lazyDepth = #[] := by
  rw [lz77ChainLazyIter_eq_lz77ChainLazy]
  simp only [lz77ChainLazy, show data.size < 3 from by omega, ↓reduceIte]
  have htrail : lz77Greedy.trailing data 0 = [] := by
    unfold lz77Greedy.trailing
    simp only [show ¬(0 < data.size) from by omega, ↓reduceDIte]
  rw [htrail]

end Zip.Native.Deflate
