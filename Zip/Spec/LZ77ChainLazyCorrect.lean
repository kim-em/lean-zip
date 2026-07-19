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

/-- The pending-match invariant carried through `rollDefer`: exactly
    `chainWalk_spec`'s `Q` at position `mp` with `maxLen = min 258 (data.size - mp)`
    and `(bestLen, bestPos) = (pLen, pMatchPos)`. The caller passes the `Or.inr`
    of the `chainWalk_spec` that found the pending match, so the rolling emission
    re-establishes validity/encodability without ever inspecting the chain state.
    Shared by `rollDefer_valid` and `rollDefer_encodable`; reused unchanged by
    rungs 2-4 as the rolling arm is threaded up the tower. -/
def RollPending (data : ByteArray) (windowSize mp pLen pMatchPos : Nat) : Prop :=
  pMatchPos < mp ∧ mp - pMatchPos ≤ windowSize ∧
    pMatchPos + min 258 (data.size - mp) ≤ data.size ∧
    (∀ i, i < pLen → data[mp + i]! = data[pMatchPos + i]!) ∧ pLen ≤ min 258 (data.size - mp)

/-! `lz77ChainLazy.mainLoop`/`rollDefer` produce valid decompositions. The
    non-rolling reference cases use `chainWalk_spec` (at `pos`, and again at
    `pos+1`) exactly as before; the rolling arm (`rollDefer_valid`) re-probes at
    each defer and carries the fresh match's `chainWalk_spec` `Q` as `RollPending`,
    so it emits a data-dependent number of literals while every reference stays
    re-verified. -/
set_option backward.split false in
mutual
theorem lz77ChainLazy_mainLoop_valid (data : ByteArray) (windowSize hashSize maxChain : Nat) (useH3 : Bool)
    (hashTable : Array Nat) (prev h3tab : Array Nat) (pos insertCap goodMatch niceLen lazyDepth lazy2Steps : Nat) (hw : windowSize > 0) :
    ValidDecomp data pos
      (lz77ChainLazy.mainLoop data windowSize hashSize maxChain useH3 hashTable prev h3tab pos insertCap goodMatch niceLen lazyDepth lazy2Steps) := by
  unfold lz77ChainLazy.mainLoop
  split
  · rename_i hlt
    dsimp only
    simp only [headProbeGuarded_eq, guardedSet_eq]
    have hspec := chainWalk_spec data
      (prev.set! (pos &&& 0x7FFF) hashTable[lz77Greedy.hash3 data pos hashSize hlt]!)
      windowSize pos (min 258 (data.size - pos)) niceLen (by omega)
      hashTable[lz77Greedy.hash3 data pos hashSize hlt]! maxChain
      (h3Seed useH3 data h3tab windowSize pos hlt % 512)
      (h3Seed useH3 data h3tab windowSize pos hlt / 512)
      (h3Seed_spec useH3 data h3tab windowSize pos hlt (min 258 (data.size - pos)) (by omega) (by omega))
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
              · rename_i hacc
                have hlt2 := lazyAcceptCost_lt hacc
                split
                · rename_i hle2
                  obtain h0' | hQ2 := hspec2
                  · omega
                  · -- accept + spill-ok: `if 1 < lazy2Steps` (roll) `else` (single).
                    split
                    · -- rolling: literal at pos, then rollDefer at pos+1 (rung 5:
                      -- `rollDefer` takes no proof-args; `3 ≤ matchLen2` is passed to
                      -- the *theorem* and derived here from `matchLen2 > matchLen ≥ 3`).
                      exact .literal (by omega) (getElem!_pos data pos (by omega))
                        (rollDefer_valid data windowSize hashSize maxChain useH3 _ _ _
                          (pos + 1) _ _ 1 insertCap goodMatch niceLen lazyDepth lazy2Steps
                          (by omega) hQ2 hw)
                    · -- ¬(1 < lazy2Steps): single deferral (original behavior)
                      exact .literal (by omega) (getElem!_pos data pos (by omega))
                        (lazyRef_at_pos data (pos + 1) _ _ hQ2.1 (by omega) hle2
                          (fun i hi => hQ2.2.2.2.1 i hi)
                          (lz77ChainLazy_mainLoop_valid _ _ _ _ _ _ _ _ _ _ _ _ _ _ hw))
                · exact lazyRef_at_pos data pos _ _ hQ.1 hge hle (fun i hi => hQ.2.2.2.1 i hi)
                    (lz77ChainLazy_mainLoop_valid _ _ _ _ _ _ _ _ _ _ _ _ _ _ hw)
              · exact lazyRef_at_pos data pos _ _ hQ.1 hge hle (fun i hi => hQ.2.2.2.1 i hi)
                  (lz77ChainLazy_mainLoop_valid _ _ _ _ _ _ _ _ _ _ _ _ _ _ hw)
            · exact lazyRef_at_pos data pos _ _ hQ.1 hge hle (fun i hi => hQ.2.2.2.1 i hi)
                (lz77ChainLazy_mainLoop_valid _ _ _ _ _ _ _ _ _ _ _ _ _ _ hw)
          · exact lazyRef_at_pos data pos _ _ hQ.1 hge hle (fun i hi => hQ.2.2.2.1 i hi)
              (lz77ChainLazy_mainLoop_valid _ _ _ _ _ _ _ _ _ _ _ _ _ _ hw)
      · exact .literal (by omega) (getElem!_pos data pos (by omega))
          (lz77ChainLazy_mainLoop_valid _ _ _ _ _ _ _ _ _ _ _ _ _ _ hw)
    · exact .literal (by omega) (getElem!_pos data pos (by omega))
        (lz77ChainLazy_mainLoop_valid _ _ _ _ _ _ _ _ _ _ _ _ _ _ hw)
  · exact trailing_valid data pos
termination_by data.size - pos
decreasing_by all_goals omega

theorem rollDefer_valid (data : ByteArray) (windowSize hashSize maxChain : Nat) (useH3 : Bool)
    (hashTable : Array Nat) (prev h3tab : Array Nat)
    (mp pLen pMatchPos step insertCap goodMatch niceLen lazyDepth lazy2Steps : Nat)
    (hpl : 3 ≤ pLen)
    (hQ : RollPending data windowSize mp pLen pMatchPos) (hw : windowSize > 0) :
    ValidDecomp data mp
      (lz77ChainLazy.rollDefer data windowSize hashSize maxChain useH3 hashTable prev h3tab mp pLen pMatchPos step insertCap goodMatch niceLen lazyDepth lazy2Steps) := by
  -- Rung 5: the def no longer carries `hmp`; derive it from `RollPending` (`pLen ≤
  -- min 258 (data.size - mp)`) and `hpl` (`3 ≤ pLen ⇒ mp < data.size`).
  have hmp : mp + pLen ≤ data.size := by have := hQ.2.2.2.2; omega
  unfold lz77ChainLazy.rollDefer
  split
  · rename_i hcan
    dsimp only
    simp only [headProbeGuarded_eq, guardedSet_eq]
    have hspec := chainWalk_spec data
      (prev.set! (mp &&& 0x7FFF) hashTable[lz77Greedy.hash3 data mp hashSize (by omega)]!)
      windowSize (mp + 1) (min 258 (data.size - (mp + 1))) niceLen (by omega)
      (hashTable.set! (lz77Greedy.hash3 data mp hashSize (by omega)) mp)[
        lz77Greedy.hash3 data (mp + 1) hashSize (by omega)]!
      (lazy2ProbeDepth maxChain) 0 0 (Or.inl rfl)
    split
    · rename_i hacc
      have hlt2 := lazyAcceptCost_lt hacc.1
      obtain h0' | hQ' := hspec
      · omega
      · exact .literal (by omega) (getElem!_pos data mp (by omega))
          (rollDefer_valid data windowSize hashSize maxChain useH3 _ _ _
            (mp + 1) _ _ (step + 1) insertCap goodMatch niceLen lazyDepth lazy2Steps
            (by omega) hQ' hw)
    · exact lazyRef_at_pos data mp _ _ hQ.1 hpl hmp (fun i hi => hQ.2.2.2.1 i hi)
        (lz77ChainLazy_mainLoop_valid _ _ _ _ _ _ _ _ _ _ _ _ _ _ hw)
  · exact lazyRef_at_pos data mp _ _ hQ.1 hpl hmp (fun i hi => hQ.2.2.2.1 i hi)
      (lz77ChainLazy_mainLoop_valid _ _ _ _ _ _ _ _ _ _ _ _ _ _ hw)
termination_by data.size - mp
decreasing_by all_goals omega
end

/-- `lz77ChainLazy` produces a valid decomposition of the input data, for any
    `lazy2Steps` (the rolling deferral only ever picks among valid matches). -/
theorem lz77ChainLazy_valid (data : ByteArray) (maxChain windowSize insertCap goodMatch niceLen lazyDepth : Nat) (useH3 : Bool) (lazy2Steps : Nat)
    (hw : windowSize > 0) :
    ValidDecomp data 0 (lz77ChainLazy data maxChain windowSize insertCap goodMatch niceLen lazyDepth useH3 lazy2Steps).toList := by
  simp only [lz77ChainLazy]
  split
  · simp only; exact trailing_valid data 0
  · simp only; exact lz77ChainLazy_mainLoop_valid data windowSize 65536 maxChain useH3 _ _ _ 0 insertCap goodMatch niceLen lazyDepth lazy2Steps hw

/-- Resolving the LZ77 tokens produced by `lz77ChainLazy` recovers the original data. -/
theorem lz77ChainLazy_resolves (data : ByteArray) (maxChain windowSize insertCap goodMatch niceLen lazyDepth : Nat) (useH3 : Bool) (lazy2Steps : Nat)
    (hw : windowSize > 0) :
    Deflate.Spec.resolveLZ77 (tokensToSymbols (lz77ChainLazy data maxChain windowSize insertCap goodMatch niceLen lazyDepth useH3 lazy2Steps)) [] =
      some data.data.toList :=
  validDecomp_resolves data _ (lz77ChainLazy_valid data maxChain windowSize insertCap goodMatch niceLen lazyDepth useH3 lazy2Steps hw)

/-! ## Encodability -/

/-- The bounds the dynamic/fixed encoders require of every token. -/
private def Enc (t : LZ77Token) : Prop :=
  match t with
  | .literal _ => True
  | .reference len dist => 3 ≤ len ∧ len ≤ 258 ∧ 1 ≤ dist ∧ dist ≤ 32768

/-! `lz77ChainLazy.mainLoop`/`rollDefer` emit only encoder-legal tokens. Mirrors
    the validity tower: the rolling arm (`rollDefer_encodable`) reads the pending
    match's length/offset bounds from `RollPending` (chainWalk_spec's `Q`) plus
    `windowSize ≤ 32768`. -/
set_option backward.split false in
mutual
theorem lz77ChainLazy_mainLoop_encodable (data : ByteArray) (windowSize hashSize maxChain : Nat) (useH3 : Bool)
    (hashTable : Array Nat) (prev h3tab : Array Nat) (pos insertCap goodMatch niceLen lazyDepth lazy2Steps : Nat) (hw : windowSize > 0) (hws : windowSize ≤ 32768) :
    ∀ t ∈ lz77ChainLazy.mainLoop data windowSize hashSize maxChain useH3 hashTable prev h3tab pos insertCap goodMatch niceLen lazyDepth lazy2Steps, Enc t := by
  unfold lz77ChainLazy.mainLoop
  split
  · rename_i hlt
    dsimp only
    simp only [headProbeGuarded_eq, guardedSet_eq]
    have hspec := chainWalk_spec data
      (prev.set! (pos &&& 0x7FFF) hashTable[lz77Greedy.hash3 data pos hashSize hlt]!)
      windowSize pos (min 258 (data.size - pos)) niceLen (by omega)
      hashTable[lz77Greedy.hash3 data pos hashSize hlt]! maxChain
      (h3Seed useH3 data h3tab windowSize pos hlt % 512)
      (h3Seed useH3 data h3tab windowSize pos hlt / 512)
      (h3Seed_spec useH3 data h3tab windowSize pos hlt (min 258 (data.size - pos)) (by omega) (by omega))
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
              · rename_i hacc
                have hlt2 := lazyAcceptCost_lt hacc
                split
                · rename_i hle2
                  obtain h0' | ⟨hQ2a, hQ2b, hQ2c, hQ2d, hQ2e⟩ := hspec2
                  · omega
                  · -- accept + spill-ok: `if 1 < lazy2Steps` (roll) `else` (single).
                    split
                    · -- rolling: literal at pos, then rollDefer at pos+1 (rung 5:
                      -- `3 ≤ matchLen2` derived from `matchLen2 > matchLen ≥ 3`).
                      intro t ht
                      cases ht with
                      | head => trivial
                      | tail _ h =>
                        exact rollDefer_encodable data windowSize hashSize maxChain useH3 _ _ _
                          (pos + 1) _ _ 1 insertCap goodMatch niceLen lazyDepth lazy2Steps
                          (by omega) ⟨hQ2a, hQ2b, hQ2c, hQ2d, hQ2e⟩ hw hws t h
                    · -- ¬(1 < lazy2Steps): single deferral (original behavior)
                      intro t ht
                      cases ht with
                      | head => trivial
                      | tail _ h =>
                        cases h with
                        | head => exact ⟨by omega, by omega, by omega, by omega⟩
                        | tail _ h => exact lz77ChainLazy_mainLoop_encodable _ _ _ _ _ _ _ _ _ _ _ _ _ _ hw hws t h
                · intro t ht
                  cases ht with
                  | head => exact ⟨hge, by omega, by omega, by omega⟩
                  | tail _ h => exact lz77ChainLazy_mainLoop_encodable _ _ _ _ _ _ _ _ _ _ _ _ _ _ hw hws t h
              · intro t ht
                cases ht with
                | head => exact ⟨hge, by omega, by omega, by omega⟩
                | tail _ h => exact lz77ChainLazy_mainLoop_encodable _ _ _ _ _ _ _ _ _ _ _ _ _ _ hw hws t h
            · intro t ht
              cases ht with
              | head => exact ⟨hge, by omega, by omega, by omega⟩
              | tail _ h => exact lz77ChainLazy_mainLoop_encodable _ _ _ _ _ _ _ _ _ _ _ _ _ _ hw hws t h
          · intro t ht
            cases ht with
            | head => exact ⟨hge, by omega, by omega, by omega⟩
            | tail _ h => exact lz77ChainLazy_mainLoop_encodable _ _ _ _ _ _ _ _ _ _ _ _ _ _ hw hws t h
      · intro t ht
        cases ht with
        | head => trivial
        | tail _ h => exact lz77ChainLazy_mainLoop_encodable _ _ _ _ _ _ _ _ _ _ _ _ _ _ hw hws t h
    · intro t ht
      cases ht with
      | head => trivial
      | tail _ h => exact lz77ChainLazy_mainLoop_encodable _ _ _ _ _ _ _ _ _ _ _ _ _ _ hw hws t h
  · intro t ht
    exact trailing_encodable data pos t ht
termination_by data.size - pos
decreasing_by all_goals omega

theorem rollDefer_encodable (data : ByteArray) (windowSize hashSize maxChain : Nat) (useH3 : Bool)
    (hashTable : Array Nat) (prev h3tab : Array Nat)
    (mp pLen pMatchPos step insertCap goodMatch niceLen lazyDepth lazy2Steps : Nat)
    (hpl : 3 ≤ pLen)
    (hQ : RollPending data windowSize mp pLen pMatchPos) (hw : windowSize > 0) (hws : windowSize ≤ 32768) :
    ∀ t ∈ lz77ChainLazy.rollDefer data windowSize hashSize maxChain useH3 hashTable prev h3tab mp pLen pMatchPos step insertCap goodMatch niceLen lazyDepth lazy2Steps, Enc t := by
  obtain ⟨hq1, hq2, hq3, hq4, hq5⟩ := hQ
  have hmp : mp + pLen ≤ data.size := by omega
  unfold lz77ChainLazy.rollDefer
  split
  · rename_i hcan
    dsimp only
    simp only [headProbeGuarded_eq, guardedSet_eq]
    have hspec := chainWalk_spec data
      (prev.set! (mp &&& 0x7FFF) hashTable[lz77Greedy.hash3 data mp hashSize (by omega)]!)
      windowSize (mp + 1) (min 258 (data.size - (mp + 1))) niceLen (by omega)
      (hashTable.set! (lz77Greedy.hash3 data mp hashSize (by omega)) mp)[
        lz77Greedy.hash3 data (mp + 1) hashSize (by omega)]!
      (lazy2ProbeDepth maxChain) 0 0 (Or.inl rfl)
    split
    · rename_i hacc
      have hlt2 := lazyAcceptCost_lt hacc.1
      obtain h0' | ⟨hQ'1, hQ'2, hQ'3, hQ'4, hQ'5⟩ := hspec
      · omega
      · intro t ht
        cases ht with
        | head => trivial
        | tail _ h =>
          exact rollDefer_encodable data windowSize hashSize maxChain useH3 _ _ _
            (mp + 1) _ _ (step + 1) insertCap goodMatch niceLen lazyDepth lazy2Steps
            (by omega) ⟨hQ'1, hQ'2, hQ'3, hQ'4, hQ'5⟩ hw hws t h
    · intro t ht
      cases ht with
      | head => exact ⟨hpl, by omega, by omega, by omega⟩
      | tail _ h => exact lz77ChainLazy_mainLoop_encodable _ _ _ _ _ _ _ _ _ _ _ _ _ _ hw hws t h
  · intro t ht
    cases ht with
    | head => exact ⟨hpl, by omega, by omega, by omega⟩
    | tail _ h => exact lz77ChainLazy_mainLoop_encodable _ _ _ _ _ _ _ _ _ _ _ _ _ _ hw hws t h
termination_by data.size - mp
decreasing_by all_goals omega
end

/-- Every token `lz77ChainLazy` emits satisfies the encoder bounds, for any
    `lazy2Steps`. -/
theorem lz77ChainLazy_encodable (data : ByteArray) (maxChain windowSize insertCap goodMatch niceLen lazyDepth : Nat) (useH3 : Bool) (lazy2Steps : Nat)
    (hw : windowSize > 0) (hws : windowSize ≤ 32768) :
    ∀ t ∈ (lz77ChainLazy data maxChain windowSize insertCap goodMatch niceLen lazyDepth useH3 lazy2Steps).toList,
      match t with
      | .literal _ => True
      | .reference len dist => 3 ≤ len ∧ len ≤ 258 ∧ 1 ≤ dist ∧ dist ≤ 32768 := by
  simp only [lz77ChainLazy]
  split
  · intro t ht
    exact trailing_encodable data 0 t ht
  · intro t ht
    exact lz77ChainLazy_mainLoop_encodable data windowSize 65536 maxChain useH3 _ _ _ 0 insertCap goodMatch niceLen lazyDepth lazy2Steps hw hws t ht

/-! ## Iterative version: equivalence + transferred contracts -/

set_option backward.split false in
set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
mutual
/-- Accumulator form of `lz77ChainLazy.rollDefer` equals the boxed twin
    (push vs. cons at each emission). Mutual with `mainLoop_eq_chainLazy`: the
    commit arms re-enter `mainLoop`, the roll arm recurses at `mp+1`. The
    unseeded `(0, 0)` re-probe decodes with `chainWalkGuardedPacked_mod'`/`_div'`
    (`bestLen = 0 ≤ maxLen` via `Nat.zero_le`), which produces the *same*
    `chainWalk` expression on both sides, so the recursive `_eq` applies without
    ever inlining the recursive call. -/
private theorem rollDefer_eq (data : ByteArray) (windowSize hashSize maxChain insertCap goodMatch niceLen lazyDepth : Nat) (useH3 : Bool)
    (hashTable : Array Nat) (prev h3tab : Array Nat) (mp pLen pMatchPos step lazy2Steps : Nat)
    (acc : Array LZ77Token) :
    lz77ChainLazyIter.rollDefer data windowSize hashSize maxChain insertCap goodMatch niceLen lazyDepth lazy2Steps useH3 hashTable prev h3tab mp pLen pMatchPos step acc =
    acc ++ (lz77ChainLazy.rollDefer data windowSize hashSize maxChain useH3 hashTable prev h3tab mp pLen pMatchPos step insertCap goodMatch niceLen lazyDepth lazy2Steps).toArray := by
  unfold lz77ChainLazyIter.rollDefer lz77ChainLazy.rollDefer
  by_cases hcan : step < lazy2Steps ∧ mp + 3 < data.size ∧ pLen < goodMatch
  · rw [dif_pos hcan, dif_pos hcan]
    simp (config := { maxSteps := 4000000 }) only [chainWalkGuardedPacked_mod', chainWalkGuardedPacked_div', min258_le_511,
      Nat.zero_le, updateHashesGuarded_eq]
    split
    · -- roll: literal at mp, then rollDefer at mp+1 (step+1)
      rw [rollDefer_eq, List.toArray_cons, ← Array.append_assoc, Array.push_eq_append]
    · -- no improvement: commit reference(pLen) at mp, then mainLoop at mp+pLen
      rw [mainLoop_eq_chainLazy, List.toArray_cons, ← Array.append_assoc, Array.push_eq_append]
  · rw [dif_neg hcan, dif_neg hcan]
    simp only [updateHashesGuarded_eq]
    rw [mainLoop_eq_chainLazy, List.toArray_cons, ← Array.append_assoc, Array.push_eq_append]
termination_by 2 * (data.size - mp) + 1
decreasing_by all_goals omega

/-- The iterative lazy chain `mainLoop` is the accumulator form of the recursive
    one — identical branch structure, push vs. cons at each emission (two pushes
    in the lookahead arm). Generalized to *all* `lazy2Steps` (rung 3 of #2837):
    the live rolling dispatch (`if 1 < lazy2Steps`) is threaded through the
    walk-decode via the mutual `rollDefer_eq`, no `dif_neg hstep` pruning.

    Rung 3 discoveries (the rung-2 obstruction was a `split` blow-up, not a
    genuine decode divergence):
    * The walk-decode `simp` (`chainWalkGuardedPacked_mod'`/`_div'`) decodes
      *both* sides' walks to the same `chainWalk` expression, so the two
      `rollDefer` calls become syntactically identical up to their `acc`. The
      rolling leaf is then discharged by `rollDefer_eq` (a `rw`, never inlining
      the recursive `rollDefer`). It needs a raised `maxSteps` (the inlined goal
      is large) but terminates.
    * `set_option backward.split false` is load-bearing: the *default* `split`
      builds its motive over the whole inlined goal — including the live
      `rollDefer` subterm — and exceeds `maxSteps`. The backward-split path does
      not. This is the fix the rung-2 note was missing.
    * The `_eq` pair is genuine mutual well-founded recursion (`termination_by
      data.size - pos` / `data.size - mp`), driven by `rw [rollDefer_eq]` /
      `rw [mainLoop_eq_chainLazy]`; `decreasing_by all_goals omega` closes every
      recursive call from the branch hypotheses. -/
private theorem mainLoop_eq_chainLazy (data : ByteArray) (windowSize hashSize maxChain insertCap goodMatch niceLen lazyDepth : Nat) (useH3 : Bool)
    (hashTable : Array Nat) (prev h3tab : Array Nat) (pos lazy2Steps : Nat) (acc : Array LZ77Token) :
    lz77ChainLazyIter.mainLoop data windowSize hashSize maxChain insertCap goodMatch niceLen lazyDepth lazy2Steps useH3 hashTable prev h3tab pos acc =
    acc ++ (lz77ChainLazy.mainLoop data windowSize hashSize maxChain useH3 hashTable prev h3tab pos insertCap goodMatch niceLen lazyDepth lazy2Steps).toArray := by
  unfold lz77ChainLazyIter.mainLoop lz77ChainLazy.mainLoop
  by_cases hlt : pos + 2 < data.size
  · -- Reduce the outer `pos+2 < data.size` dite with `zeta := false`, so the
    -- `let r := chainWalk … seed …` binding is NOT inlined yet — otherwise the
    -- large opaque `h3Seed`/`hash3Single` terms get duplicated across the whole
    -- branch tree (via `matchLen`/`matchPos`) and blow up. Abstract those two
    -- opaque terms to variables first, then the (now cheap) zeta-simp aligns
    -- the two sides' walk decode through `chainWalkGuardedPacked_mod`/`_div`.
    simp (config := { zeta := false }) only [hlt, ↓reduceDIte]
    -- The seed's decoded length is `≤ maxLen` (`h3Seed_spec`); keep that fact
    -- through the abstraction so the seed-general decode lemmas apply.
    have hbnd : h3Seed useH3 data h3tab windowSize pos hlt % 512 ≤ min 258 (data.size - pos) := by
      rcases h3Seed_spec useH3 data h3tab windowSize pos hlt (min 258 (data.size - pos))
        (by omega) (by omega) with hz | hq
      · omega
      · exact hq.2.2.2.2
    generalize hsd : h3Seed useH3 data h3tab windowSize pos hlt = sd
    rw [hsd] at hbnd
    generalize hash3Single data pos hlt = hsg
    simp (config := { maxSteps := 4000000 }) only [chainWalkGuardedPacked_mod', chainWalkGuardedPacked_div', min258_le_511,
      hbnd, Nat.zero_le, updateHashesGuarded_eq]
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
              · -- hle2 : accept + spill-ok
                split
                · -- 1 < lazy2Steps : rolling dispatch — roll (rung 5: no hpl2 dite)
                  rw [rollDefer_eq, List.toArray_cons, ← Array.append_assoc, Array.push_eq_append]
                · -- ¬(1 < lazy2Steps) : single deferral, two pushes
                  rw [mainLoop_eq_chainLazy,
                    Array.push_eq_append, Array.push_eq_append,
                    Array.append_assoc, Array.append_assoc,
                    ← List.toArray_cons, ← List.toArray_cons]
              · -- ¬hle2 : reference(matchLen) at pos
                rw [mainLoop_eq_chainLazy, List.toArray_cons,
                  ← Array.append_assoc, Array.push_eq_append]
            · -- matchLen2 ≤ matchLen : reference(matchLen) at pos
              rw [mainLoop_eq_chainLazy, List.toArray_cons,
                ← Array.append_assoc, Array.push_eq_append]
          · -- matchLen ≥ goodMatch (gated) : reference(matchLen) at pos
            rw [mainLoop_eq_chainLazy, List.toArray_cons,
              ← Array.append_assoc, Array.push_eq_append]
        · -- ¬h3lt : reference(matchLen) at pos (near end)
          rw [mainLoop_eq_chainLazy, List.toArray_cons,
            ← Array.append_assoc, Array.push_eq_append]
      · -- ¬hle : literal
        rw [mainLoop_eq_chainLazy, List.toArray_cons,
          ← Array.append_assoc, Array.push_eq_append]
    · -- ¬hge : literal
      rw [mainLoop_eq_chainLazy, List.toArray_cons,
        ← Array.append_assoc, Array.push_eq_append]
  · simp only [hlt, ↓reduceDIte]
    exact trailing_eq data pos acc
termination_by 2 * (data.size - pos)
decreasing_by all_goals (first | omega | (refine Nat.mul_lt_mul_of_pos_left ?_ (by decide); omega))
end

/-- `lz77ChainLazyIter` produces exactly the same tokens as `lz77ChainLazy`. -/
theorem lz77ChainLazyIter_eq_lz77ChainLazy (data : ByteArray) (maxChain windowSize insertCap goodMatch niceLen lazyDepth : Nat) (useH3 : Bool) (lazy2Steps : Nat) :
    lz77ChainLazyIter data maxChain windowSize insertCap goodMatch niceLen lazyDepth useH3 lazy2Steps =
      lz77ChainLazy data maxChain windowSize insertCap goodMatch niceLen lazyDepth useH3 lazy2Steps := by
  unfold lz77ChainLazyIter lz77ChainLazy
  split
  · rw [trailing_eq]; simp only [List.append_toArray, List.nil_append]
  · rw [mainLoop_eq_chainLazy (lazy2Steps := lazy2Steps)]
    simp only [List.append_toArray, List.nil_append]

theorem lz77ChainLazyIter_valid (data : ByteArray) (maxChain windowSize insertCap goodMatch niceLen lazyDepth : Nat) (useH3 : Bool) (lazy2Steps : Nat)
    (hw : windowSize > 0) :
    ValidDecomp data 0 (lz77ChainLazyIter data maxChain windowSize insertCap goodMatch niceLen lazyDepth useH3 lazy2Steps).toList := by
  rw [lz77ChainLazyIter_eq_lz77ChainLazy]; exact lz77ChainLazy_valid data maxChain windowSize insertCap goodMatch niceLen lazyDepth useH3 lazy2Steps hw

theorem lz77ChainLazyIter_resolves (data : ByteArray) (maxChain windowSize insertCap goodMatch niceLen lazyDepth : Nat) (useH3 : Bool) (lazy2Steps : Nat)
    (hw : windowSize > 0) :
    Deflate.Spec.resolveLZ77 (tokensToSymbols (lz77ChainLazyIter data maxChain windowSize insertCap goodMatch niceLen lazyDepth useH3 lazy2Steps)) [] =
      some data.data.toList := by
  rw [lz77ChainLazyIter_eq_lz77ChainLazy]; exact lz77ChainLazy_resolves data maxChain windowSize insertCap goodMatch niceLen lazyDepth useH3 lazy2Steps hw

theorem lz77ChainLazyIter_encodable (data : ByteArray) (maxChain windowSize insertCap goodMatch niceLen lazyDepth : Nat) (useH3 : Bool) (lazy2Steps : Nat)
    (hw : windowSize > 0) (hws : windowSize ≤ 32768) :
    ∀ t ∈ (lz77ChainLazyIter data maxChain windowSize insertCap goodMatch niceLen lazyDepth useH3 lazy2Steps).toList,
      match t with
      | .literal _ => True
      | .reference len dist => 3 ≤ len ∧ len ≤ 258 ∧ 1 ≤ dist ∧ dist ≤ 32768 := by
  rw [lz77ChainLazyIter_eq_lz77ChainLazy]
  exact lz77ChainLazy_encodable data maxChain windowSize insertCap goodMatch niceLen lazyDepth useH3 lazy2Steps hw hws

/-- The lazy chain matcher emits no tokens on empty input. -/
theorem lz77ChainLazyIter_empty (data : ByteArray) (maxChain windowSize insertCap goodMatch niceLen lazyDepth : Nat) (useH3 : Bool) (lazy2Steps : Nat)
    (hzero : data.size = 0) : lz77ChainLazyIter data maxChain windowSize insertCap goodMatch niceLen lazyDepth useH3 lazy2Steps = #[] := by
  rw [lz77ChainLazyIter_eq_lz77ChainLazy]
  simp only [lz77ChainLazy, show data.size < 3 from by omega, ↓reduceIte]
  have htrail : lz77Greedy.trailing data 0 = [] := by
    unfold lz77Greedy.trailing
    simp only [show ¬(0 < data.size) from by omega, ↓reduceDIte]
  rw [htrail]

end Zip.Native.Deflate
