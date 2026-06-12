import Zip.Spec.LZ77ChainCorrect
import Zip.Spec.LZ77ChainLazyCorrect

/-!
# Correctness of the 32-bit chain-state LZ77 matchers (Wave 3 Step 2)

`lz77ChainIter32`/`lz77ChainLazyIter32` are the `Array UInt32` chain-state
twins of `lz77ChainIter`/`lz77ChainLazyIter`. Exactly as for the Nat kernels,
the chain state is a pure match-finding heuristic: validity is re-established
at emission by `countMatch` + the explicit window guards, so the
`prev`/`hashTable` contents never enter any proof — in particular no
cross-type (`UInt32` vs `Nat`) array-content correspondence is needed or
stated. The only new proof content is the `UInt32`→`Nat` bridge at the walk
guard: `cand < pos32 ∧ pos32 - cand ≤ windowSize` (in `UInt32`) yields
`cand.toNat < pos ∧ pos - cand.toNat ≤ windowSize.toNat` (in `Nat`) via
`UInt32.lt_iff_toNat_lt`/`UInt32.le_iff_toNat_le`/`UInt32.toNat_sub_of_le`,
after which `chainWalkFast32_spec` and everything downstream are line-by-line
copies of the `LZ77ChainCorrect`/`LZ77ChainLazyCorrect` templates. This file
proves the same four contracts per matcher the Nat versions export
(`_valid`, `_resolves`, `_encodable`, `_empty`).
-/

namespace Zip.Native.Deflate

open Zip.Native.Deflate (lz77Chain32 lz77ChainLazy32 lz77Greedy)

/-! ## Guarded helper bridges

Mirrors `headInsertGuarded_eq`/`headProbeGuarded_eq`: rewrite the guarded
32-bit head operations back to the panic-checked forms so the mainLoop proofs
proceed on plain `[..]!`/`set!` terms. -/

/-- The guarded 32-bit head insertion computes exactly the panic-checked triple
    (the threaded `pos32` is `pos.toUInt32` by hypothesis). -/
theorem headInsertGuarded32_eq (hashTable prev : Array UInt32) (h pos : Nat)
    (pos32 : UInt32) (hp32 : pos32 = pos.toUInt32) :
    headInsertGuarded32 hashTable prev h pos pos32 hp32 =
      (hashTable[h]!, hashTable.set! h pos.toUInt32, prev.set! pos hashTable[h]!) := by
  subst hp32
  unfold headInsertGuarded32
  split
  · rename_i hg
    simp only [getElem!_pos hashTable h hg.1, Array.set!_eq_setIfInBounds,
      Array.setIfInBounds_def, dif_pos hg.1, dif_pos hg.2]
  · rfl

/-- The guarded 32-bit head probe computes exactly the panic-checked read. -/
theorem headProbeGuarded32_eq (hashTable : Array UInt32) (h : Nat) :
    headProbeGuarded32 hashTable h = hashTable[h]! := by
  unfold headProbeGuarded32
  split
  · rename_i hb; exact (getElem!_pos hashTable h hb).symm
  · rfl

/-! ## Chain-walk invariant -/

/-- 32-bit copy of `chainWalk_spec`: the match the walk returns is always a
    real in-window backward match (or empty). The `UInt32` walk guard yields
    the `Nat` facts the invariant needs via the `toNat` bridge lemmas. -/
theorem chainWalkFast32_spec (data : ByteArray) (prev : Array UInt32)
    (windowSize : UInt32) (pos maxLen : Nat) (hpm : pos + maxLen ≤ data.size)
    (hps : pos ≤ prev.size) (pos32 : UInt32) (hp32 : pos32.toNat = pos)
    (cand : UInt32) (fuel bestLen bestPos : Nat)
    (hb : bestLen = 0 ∨ (bestPos < pos ∧ pos - bestPos ≤ windowSize.toNat ∧
        bestPos + maxLen ≤ data.size ∧
        (∀ i, i < bestLen → data[pos + i]! = data[bestPos + i]!) ∧ bestLen ≤ maxLen)) :
    let r := chainWalkFast32 data prev windowSize pos maxLen hpm hps pos32 hp32
      cand fuel bestLen bestPos
    r.1 = 0 ∨ (r.2 < pos ∧ pos - r.2 ≤ windowSize.toNat ∧ r.2 + maxLen ≤ data.size ∧
        (∀ i, i < r.1 → data[pos + i]! = data[r.2 + i]!) ∧ r.1 ≤ maxLen) := by
  induction fuel generalizing cand bestLen bestPos with
  | zero => rw [chainWalkFast32]; exact hb
  | succ k ih =>
    rw [chainWalkFast32, if_neg (by omega : ¬ (k + 1 = 0))]
    split
    · rename_i hc
      have h1 := UInt32.lt_iff_toNat_lt.mp hc.1
      have hcn : cand.toNat < pos := by omega
      have hwin : pos - cand.toNat ≤ windowSize.toNat := by
        have h2 := UInt32.le_iff_toNat_le.mp hc.2
        rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (Nat.le_of_lt h1))] at h2
        omega
      have hcand : cand.toNat + maxLen ≤ data.size := by omega
      have hcm := lz77Greedy.countMatch_matches data cand.toNat pos maxLen hcand hpm
      by_cases hml : lz77Greedy.countMatch data cand.toNat pos maxLen hcand hpm > bestLen
      · simp only [hml, ↓reduceIte]
        split
        · exact Or.inr ⟨hcn, hwin, hcand, fun i hi => (hcm.1 i hi).symm, hcm.2⟩
        · exact ih _ _ _
            (Or.inr ⟨hcn, hwin, hcand, fun i hi => (hcm.1 i hi).symm, hcm.2⟩)
      · simp only [hml, ↓reduceIte]
        split
        · exact hb
        · exact ih _ _ _ hb
    · exact hb

/-- The guarded walk satisfies the same invariant: the fast path by
    `chainWalkFast32_spec`, the (dead) fallback trivially — it returns the
    running best, which satisfies the invariant by hypothesis. -/
theorem chainWalkGuarded32_spec (data : ByteArray) (prev : Array UInt32)
    (windowSize : UInt32) (pos maxLen : Nat) (hpm : pos + maxLen ≤ data.size)
    (pos32 : UInt32) (hp32 : pos32 = pos.toUInt32)
    (cand : UInt32) (fuel bestLen bestPos : Nat)
    (hb : bestLen = 0 ∨ (bestPos < pos ∧ pos - bestPos ≤ windowSize.toNat ∧
        bestPos + maxLen ≤ data.size ∧
        (∀ i, i < bestLen → data[pos + i]! = data[bestPos + i]!) ∧ bestLen ≤ maxLen)) :
    let r := chainWalkGuarded32 data prev windowSize pos maxLen hpm pos32 hp32 cand fuel bestLen bestPos
    r.1 = 0 ∨ (r.2 < pos ∧ pos - r.2 ≤ windowSize.toNat ∧ r.2 + maxLen ≤ data.size ∧
        (∀ i, i < r.1 → data[pos + i]! = data[r.2 + i]!) ∧ r.1 ≤ maxLen) := by
  unfold chainWalkGuarded32
  split
  · exact chainWalkFast32_spec data prev windowSize pos maxLen hpm _ _ _
      cand fuel bestLen bestPos hb
  · exact hb

/-! ## Greedy 32-bit matcher: validity -/

/-- `lz77Chain32.mainLoop` produces a valid decomposition from `pos`. Mirrors
    `lz77Chain_mainLoop_valid`; the reference case uses `chainWalkGuarded32_spec`
    (which holds for *any* `prev` array) in place of `chainWalk_spec`. -/
theorem lz77Chain32_mainLoop_valid (data : ByteArray) (windowSize : UInt32)
    (hashSize maxChain : Nat) (hashTable prev : Array UInt32) (pos insertCap : Nat)
    (pos32 : UInt32) (hp32 : pos32 = pos.toUInt32) :
    ValidDecomp data pos
      (lz77Chain32.mainLoop data windowSize hashSize maxChain hashTable prev pos insertCap
        pos32 hp32) := by
  unfold lz77Chain32.mainLoop
  split
  · rename_i hlt
    dsimp only
    simp only [headInsertGuarded32_eq]
    have hspec := chainWalkGuarded32_spec data
      (prev.set! pos hashTable[lz77Greedy.hash3 data pos hashSize hlt]!)
      windowSize pos (min 258 (data.size - pos)) (by omega) pos32 hp32
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
          · exact lz77Chain32_mainLoop_valid _ _ _ _ _ _ _ _ _ _
      · exact .literal (by omega) (getElem!_pos data pos (by omega))
          (lz77Chain32_mainLoop_valid _ _ _ _ _ _ _ _ _ _)
    · exact .literal (by omega) (getElem!_pos data pos (by omega))
        (lz77Chain32_mainLoop_valid _ _ _ _ _ _ _ _ _ _)
  · exact trailing_valid data pos
termination_by data.size - pos
decreasing_by all_goals omega

/-- `lz77Chain32` produces a valid decomposition of the input data. -/
theorem lz77Chain32_valid (data : ByteArray) (maxChain windowSize insertCap : Nat)
    (_hw : windowSize > 0) :
    ValidDecomp data 0 (lz77Chain32 data maxChain windowSize insertCap).toList := by
  simp only [lz77Chain32]
  split
  · simp only; exact trailing_valid data 0
  · simp only
    exact lz77Chain32_mainLoop_valid data windowSize.toUInt32 65536 maxChain _ _ 0 insertCap 0 rfl

/-- Resolving the LZ77 tokens produced by `lz77Chain32` recovers the original data. -/
theorem lz77Chain32_resolves (data : ByteArray) (maxChain windowSize insertCap : Nat)
    (hw : windowSize > 0) :
    Deflate.Spec.resolveLZ77 (tokensToSymbols (lz77Chain32 data maxChain windowSize insertCap)) [] =
      some data.data.toList :=
  validDecomp_resolves data _ (lz77Chain32_valid data maxChain windowSize insertCap hw)

/-! ## Greedy 32-bit matcher: encodability -/

/-- The bounds the dynamic/fixed encoders require of every token. -/
private def Enc (t : LZ77Token) : Prop :=
  match t with
  | .literal _ => True
  | .reference len dist => 3 ≤ len ∧ len ≤ 258 ∧ 1 ≤ dist ∧ dist ≤ 32768

theorem lz77Chain32_mainLoop_encodable (data : ByteArray) (windowSize : UInt32)
    (hashSize maxChain : Nat) (hashTable prev : Array UInt32) (pos insertCap : Nat)
    (pos32 : UInt32) (hp32 : pos32 = pos.toUInt32)
    (hws : windowSize.toNat ≤ 32768) :
    ∀ t ∈ lz77Chain32.mainLoop data windowSize hashSize maxChain hashTable prev pos insertCap
        pos32 hp32,
      Enc t := by
  unfold lz77Chain32.mainLoop
  split
  · rename_i hlt
    dsimp only
    simp only [headInsertGuarded32_eq]
    have hspec := chainWalkGuarded32_spec data
      (prev.set! pos hashTable[lz77Greedy.hash3 data pos hashSize hlt]!)
      windowSize pos (min 258 (data.size - pos)) (by omega) pos32 hp32
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
          | tail _ h => exact lz77Chain32_mainLoop_encodable _ _ _ _ _ _ _ _ _ _ hws t h
      · intro t ht
        cases ht with
        | head => trivial
        | tail _ h => exact lz77Chain32_mainLoop_encodable _ _ _ _ _ _ _ _ _ _ hws t h
    · intro t ht
      cases ht with
      | head => trivial
      | tail _ h => exact lz77Chain32_mainLoop_encodable _ _ _ _ _ _ _ _ _ _ hws t h
  · intro t ht
    exact trailing_encodable data pos t ht
termination_by data.size - pos
decreasing_by all_goals omega

/-- `n.toUInt32.toNat` never exceeds `n` (truncation only shrinks). -/
private theorem toUInt32_toNat_le (n : Nat) : n.toUInt32.toNat ≤ n := by
  have h : n.toUInt32.toNat = n % 4294967296 := by simp [Nat.toUInt32]
  omega

/-- Every token `lz77Chain32` emits satisfies the encoder bounds. -/
theorem lz77Chain32_encodable (data : ByteArray) (maxChain windowSize insertCap : Nat)
    (_hw : windowSize > 0) (hws : windowSize ≤ 32768) :
    ∀ t ∈ (lz77Chain32 data maxChain windowSize insertCap).toList,
      match t with
      | .literal _ => True
      | .reference len dist => 3 ≤ len ∧ len ≤ 258 ∧ 1 ≤ dist ∧ dist ≤ 32768 := by
  simp only [lz77Chain32]
  split
  · intro t ht
    exact trailing_encodable data 0 t ht
  · intro t ht
    exact lz77Chain32_mainLoop_encodable data windowSize.toUInt32 65536 maxChain _ _ 0 insertCap
      0 rfl (Nat.le_trans (toUInt32_toNat_le windowSize) hws) t ht

/-! ## Greedy 32-bit matcher: iterative version -/

/-- The accumulator `trailing` is the array form of the recursive one. (Local
    copy of `LZ77ChainCorrect`'s `private trailing_eq`.) -/
private theorem trailing_eq (data : ByteArray) (pos : Nat) (acc : Array LZ77Token) :
    lz77GreedyIter.trailing data pos acc = acc ++ (lz77Greedy.trailing data pos).toArray := by
  induction h : data.size - pos using Nat.strongRecOn generalizing pos acc with
  | _ n ih =>
    unfold lz77GreedyIter.trailing lz77Greedy.trailing
    by_cases hp : pos < data.size
    · simp only [hp, ↓reduceDIte]
      rw [ih _ (by omega) _ _ rfl, List.toArray_cons, ← Array.append_assoc, Array.push_eq_append]
    · simp only [hp, ↓reduceDIte, List.toArray, Array.append_empty]

/-- The iterative 32-bit chain `mainLoop` is the accumulator form of the
    recursive one: same guarded helpers, push vs. cons at each emission. -/
private theorem mainLoop_eq_chain32 (data : ByteArray) (windowSize : UInt32)
    (hashSize maxChain insertCap : Nat) (hashTable prev : Array UInt32) (pos : Nat)
    (acc : Array LZ77Token) (pos32 : UInt32) (hp32 : pos32 = pos.toUInt32) :
    lz77ChainIter32.mainLoop data windowSize hashSize maxChain insertCap hashTable prev pos acc
      pos32 hp32 =
    acc ++ (lz77Chain32.mainLoop data windowSize hashSize maxChain hashTable prev pos insertCap
      pos32 hp32).toArray := by
  induction h : data.size - pos using Nat.strongRecOn
      generalizing pos acc hashTable prev pos32 hp32 with
  | _ n ih =>
    unfold lz77ChainIter32.mainLoop lz77Chain32.mainLoop
    by_cases hlt : pos + 2 < data.size
    · simp only [hlt, ↓reduceDIte]
      split
      · split
        · rw [ih _ (by omega) _ _ _ _ _ _ rfl, List.toArray_cons,
            ← Array.append_assoc, Array.push_eq_append]
        · rw [ih _ (by omega) _ _ _ _ _ _ rfl, List.toArray_cons,
            ← Array.append_assoc, Array.push_eq_append]
      · rw [ih _ (by omega) _ _ _ _ _ _ rfl, List.toArray_cons,
          ← Array.append_assoc, Array.push_eq_append]
    · simp only [hlt, ↓reduceDIte]
      exact trailing_eq data pos acc

/-- `lz77ChainIter32` produces exactly the same tokens as `lz77Chain32`. -/
theorem lz77ChainIter32_eq_lz77Chain32 (data : ByteArray) (maxChain windowSize insertCap : Nat) :
    lz77ChainIter32 data maxChain windowSize insertCap =
      lz77Chain32 data maxChain windowSize insertCap := by
  unfold lz77ChainIter32 lz77Chain32
  split
  · rw [trailing_eq]; simp only [List.append_toArray, List.nil_append]
  · rw [mainLoop_eq_chain32]; simp only [List.append_toArray, List.nil_append]

theorem lz77ChainIter32_valid (data : ByteArray) (maxChain windowSize insertCap : Nat)
    (hw : windowSize > 0) :
    ValidDecomp data 0 (lz77ChainIter32 data maxChain windowSize insertCap).toList := by
  rw [lz77ChainIter32_eq_lz77Chain32]; exact lz77Chain32_valid data maxChain windowSize insertCap hw

theorem lz77ChainIter32_resolves (data : ByteArray) (maxChain windowSize insertCap : Nat)
    (hw : windowSize > 0) :
    Deflate.Spec.resolveLZ77 (tokensToSymbols (lz77ChainIter32 data maxChain windowSize insertCap)) [] =
      some data.data.toList := by
  rw [lz77ChainIter32_eq_lz77Chain32]; exact lz77Chain32_resolves data maxChain windowSize insertCap hw

theorem lz77ChainIter32_encodable (data : ByteArray) (maxChain windowSize insertCap : Nat)
    (hw : windowSize > 0) (hws : windowSize ≤ 32768) :
    ∀ t ∈ (lz77ChainIter32 data maxChain windowSize insertCap).toList,
      match t with
      | .literal _ => True
      | .reference len dist => 3 ≤ len ∧ len ≤ 258 ∧ 1 ≤ dist ∧ dist ≤ 32768 := by
  rw [lz77ChainIter32_eq_lz77Chain32]
  exact lz77Chain32_encodable data maxChain windowSize insertCap hw hws

/-- The 32-bit chain matcher emits no tokens on empty input. -/
theorem lz77ChainIter32_empty (data : ByteArray) (maxChain windowSize insertCap : Nat)
    (hzero : data.size = 0) : lz77ChainIter32 data maxChain windowSize insertCap = #[] := by
  rw [lz77ChainIter32_eq_lz77Chain32]
  simp only [lz77Chain32, show data.size < 3 from by omega, ↓reduceIte]
  have htrail : lz77Greedy.trailing data 0 = [] := by
    unfold lz77Greedy.trailing
    simp only [show ¬(0 < data.size) from by omega, ↓reduceDIte]
  rw [htrail]

/-! ## Lazy 32-bit matcher: validity -/

set_option backward.split false in
/-- `lz77ChainLazy32.mainLoop` produces a valid decomposition from `pos`.
    Mirrors `lz77ChainLazy_mainLoop_valid`: the reference cases use
    `chainWalkGuarded32_spec` (at `pos`, and again at `pos+1` for the
    lookahead), and the lookahead emission reuses `lazyRef_at_pos`. -/
theorem lz77ChainLazy32_mainLoop_valid (data : ByteArray) (windowSize : UInt32)
    (hashSize maxChain : Nat) (hashTable prev : Array UInt32) (pos insertCap : Nat)
    (pos32 : UInt32) (hp32 : pos32 = pos.toUInt32) :
    ValidDecomp data pos
      (lz77ChainLazy32.mainLoop data windowSize hashSize maxChain hashTable prev pos insertCap
        pos32 hp32) := by
  unfold lz77ChainLazy32.mainLoop
  split
  · rename_i hlt
    dsimp only
    simp only [headInsertGuarded32_eq, headProbeGuarded32_eq]
    have hspec := chainWalkGuarded32_spec data
      (prev.set! pos hashTable[lz77Greedy.hash3 data pos hashSize hlt]!)
      windowSize pos (min 258 (data.size - pos)) (by omega) pos32 hp32
      hashTable[lz77Greedy.hash3 data pos hashSize hlt]! maxChain 0 0 (Or.inl rfl)
    split
    · rename_i hge
      split
      · rename_i hle
        obtain h0 | hQ := hspec
        · omega
        · split
          · rename_i h3lt
            have hspec2 := chainWalkGuarded32_spec data
              (prev.set! pos hashTable[lz77Greedy.hash3 data pos hashSize hlt]!)
              windowSize (pos + 1) (min 258 (data.size - (pos + 1))) (by omega)
              (pos32 + 1) (by rw [hp32]; exact (UInt32.ofNat_add pos 1).symm)
              (hashTable.set! (lz77Greedy.hash3 data pos hashSize hlt) pos.toUInt32)[
                lz77Greedy.hash3 data (pos + 1) hashSize (by omega)]!
              maxChain 0 0 (Or.inl rfl)
            split
            · split
              · rename_i hle2
                obtain h0' | hQ2 := hspec2
                · omega
                · exact .literal (by omega) (getElem!_pos data pos (by omega))
                    (lazyRef_at_pos data (pos + 1) _ _ hQ2.1 (by omega) hle2
                      (fun i hi => hQ2.2.2.2.1 i hi)
                      (lz77ChainLazy32_mainLoop_valid _ _ _ _ _ _ _ _ _ _))
              · exact lazyRef_at_pos data pos _ _ hQ.1 hge hle (fun i hi => hQ.2.2.2.1 i hi)
                  (lz77ChainLazy32_mainLoop_valid _ _ _ _ _ _ _ _ _ _)
            · exact lazyRef_at_pos data pos _ _ hQ.1 hge hle (fun i hi => hQ.2.2.2.1 i hi)
                (lz77ChainLazy32_mainLoop_valid _ _ _ _ _ _ _ _ _ _)
          · exact lazyRef_at_pos data pos _ _ hQ.1 hge hle (fun i hi => hQ.2.2.2.1 i hi)
              (lz77ChainLazy32_mainLoop_valid _ _ _ _ _ _ _ _ _ _)
      · exact .literal (by omega) (getElem!_pos data pos (by omega))
          (lz77ChainLazy32_mainLoop_valid _ _ _ _ _ _ _ _ _ _)
    · exact .literal (by omega) (getElem!_pos data pos (by omega))
        (lz77ChainLazy32_mainLoop_valid _ _ _ _ _ _ _ _ _ _)
  · exact trailing_valid data pos
termination_by data.size - pos
decreasing_by all_goals omega

/-- `lz77ChainLazy32` produces a valid decomposition of the input data. -/
theorem lz77ChainLazy32_valid (data : ByteArray) (maxChain windowSize insertCap : Nat)
    (_hw : windowSize > 0) :
    ValidDecomp data 0 (lz77ChainLazy32 data maxChain windowSize insertCap).toList := by
  simp only [lz77ChainLazy32]
  split
  · simp only; exact trailing_valid data 0
  · simp only
    exact lz77ChainLazy32_mainLoop_valid data windowSize.toUInt32 65536 maxChain _ _ 0 insertCap
      0 rfl

/-- Resolving the LZ77 tokens produced by `lz77ChainLazy32` recovers the original data. -/
theorem lz77ChainLazy32_resolves (data : ByteArray) (maxChain windowSize insertCap : Nat)
    (hw : windowSize > 0) :
    Deflate.Spec.resolveLZ77 (tokensToSymbols (lz77ChainLazy32 data maxChain windowSize insertCap)) [] =
      some data.data.toList :=
  validDecomp_resolves data _ (lz77ChainLazy32_valid data maxChain windowSize insertCap hw)

/-! ## Lazy 32-bit matcher: encodability -/

set_option backward.split false in
theorem lz77ChainLazy32_mainLoop_encodable (data : ByteArray) (windowSize : UInt32)
    (hashSize maxChain : Nat) (hashTable prev : Array UInt32) (pos insertCap : Nat)
    (pos32 : UInt32) (hp32 : pos32 = pos.toUInt32)
    (hws : windowSize.toNat ≤ 32768) :
    ∀ t ∈ lz77ChainLazy32.mainLoop data windowSize hashSize maxChain hashTable prev pos insertCap
        pos32 hp32,
      Enc t := by
  unfold lz77ChainLazy32.mainLoop
  split
  · rename_i hlt
    dsimp only
    simp only [headInsertGuarded32_eq, headProbeGuarded32_eq]
    have hspec := chainWalkGuarded32_spec data
      (prev.set! pos hashTable[lz77Greedy.hash3 data pos hashSize hlt]!)
      windowSize pos (min 258 (data.size - pos)) (by omega) pos32 hp32
      hashTable[lz77Greedy.hash3 data pos hashSize hlt]! maxChain 0 0 (Or.inl rfl)
    split
    · rename_i hge
      split
      · rename_i hle
        obtain h0 | ⟨hQ1, hQ2, _, _, hQ5⟩ := hspec
        · omega
        · split
          · rename_i h3lt
            have hspec2 := chainWalkGuarded32_spec data
              (prev.set! pos hashTable[lz77Greedy.hash3 data pos hashSize hlt]!)
              windowSize (pos + 1) (min 258 (data.size - (pos + 1))) (by omega)
              (pos32 + 1) (by rw [hp32]; exact (UInt32.ofNat_add pos 1).symm)
              (hashTable.set! (lz77Greedy.hash3 data pos hashSize hlt) pos.toUInt32)[
                lz77Greedy.hash3 data (pos + 1) hashSize (by omega)]!
              maxChain 0 0 (Or.inl rfl)
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
                    | tail _ h =>
                      exact lz77ChainLazy32_mainLoop_encodable _ _ _ _ _ _ _ _ _ _ hws t h
              · intro t ht
                cases ht with
                | head => exact ⟨hge, by omega, by omega, by omega⟩
                | tail _ h => exact lz77ChainLazy32_mainLoop_encodable _ _ _ _ _ _ _ _ _ _ hws t h
            · intro t ht
              cases ht with
              | head => exact ⟨hge, by omega, by omega, by omega⟩
              | tail _ h => exact lz77ChainLazy32_mainLoop_encodable _ _ _ _ _ _ _ _ _ _ hws t h
          · intro t ht
            cases ht with
            | head => exact ⟨hge, by omega, by omega, by omega⟩
            | tail _ h => exact lz77ChainLazy32_mainLoop_encodable _ _ _ _ _ _ _ _ _ _ hws t h
      · intro t ht
        cases ht with
        | head => trivial
        | tail _ h => exact lz77ChainLazy32_mainLoop_encodable _ _ _ _ _ _ _ _ _ _ hws t h
    · intro t ht
      cases ht with
      | head => trivial
      | tail _ h => exact lz77ChainLazy32_mainLoop_encodable _ _ _ _ _ _ _ _ _ _ hws t h
  · intro t ht
    exact trailing_encodable data pos t ht
termination_by data.size - pos
decreasing_by all_goals omega

/-- Every token `lz77ChainLazy32` emits satisfies the encoder bounds. -/
theorem lz77ChainLazy32_encodable (data : ByteArray) (maxChain windowSize insertCap : Nat)
    (_hw : windowSize > 0) (hws : windowSize ≤ 32768) :
    ∀ t ∈ (lz77ChainLazy32 data maxChain windowSize insertCap).toList,
      match t with
      | .literal _ => True
      | .reference len dist => 3 ≤ len ∧ len ≤ 258 ∧ 1 ≤ dist ∧ dist ≤ 32768 := by
  simp only [lz77ChainLazy32]
  split
  · intro t ht
    exact trailing_encodable data 0 t ht
  · intro t ht
    exact lz77ChainLazy32_mainLoop_encodable data windowSize.toUInt32 65536 maxChain _ _ 0 insertCap
      0 rfl (Nat.le_trans (toUInt32_toNat_le windowSize) hws) t ht

/-! ## Lazy 32-bit matcher: iterative version -/

/-- The iterative lazy 32-bit `mainLoop` is the accumulator form of the
    recursive one — identical branch structure, push vs. cons at each emission
    (two pushes in the lookahead arm). -/
private theorem mainLoop_eq_chainLazy32 (data : ByteArray) (windowSize : UInt32)
    (hashSize maxChain insertCap : Nat) (hashTable prev : Array UInt32) (pos : Nat)
    (acc : Array LZ77Token) (pos32 : UInt32) (hp32 : pos32 = pos.toUInt32) :
    lz77ChainLazyIter32.mainLoop data windowSize hashSize maxChain insertCap hashTable prev pos acc
      pos32 hp32 =
    acc ++ (lz77ChainLazy32.mainLoop data windowSize hashSize maxChain hashTable prev pos insertCap
      pos32 hp32).toArray := by
  induction h : data.size - pos using Nat.strongRecOn
      generalizing pos acc hashTable prev pos32 hp32 with
  | _ n ih =>
    unfold lz77ChainLazyIter32.mainLoop lz77ChainLazy32.mainLoop
    by_cases hlt : pos + 2 < data.size
    · simp only [hlt, ↓reduceDIte]
      -- Branch tree: hge / hle / h3lt / (matchLen2 > matchLen ∧ no-farther) / hle2
      split
      · -- hge : matchLen ≥ 3
        split
        · -- hle : pos + matchLen ≤ data.size
          split
          · -- h3lt : pos + 3 < data.size
            split
            · -- deferral condition
              split
              · -- hle2 : lookahead emits literal + reference(matchLen2), two pushes
                rw [ih _ (by omega) _ _ _ _ _ _ rfl,
                  Array.push_eq_append, Array.push_eq_append,
                  Array.append_assoc, Array.append_assoc,
                  ← List.toArray_cons, ← List.toArray_cons]
              · -- ¬hle2 : reference(matchLen) at pos
                rw [ih _ (by omega) _ _ _ _ _ _ rfl, List.toArray_cons,
                  ← Array.append_assoc, Array.push_eq_append]
            · -- no deferral : reference(matchLen) at pos
              rw [ih _ (by omega) _ _ _ _ _ _ rfl, List.toArray_cons,
                ← Array.append_assoc, Array.push_eq_append]
          · -- ¬h3lt : reference(matchLen) at pos (near end)
            rw [ih _ (by omega) _ _ _ _ _ _ rfl, List.toArray_cons,
              ← Array.append_assoc, Array.push_eq_append]
        · -- ¬hle : literal
          rw [ih _ (by omega) _ _ _ _ _ _ rfl, List.toArray_cons,
            ← Array.append_assoc, Array.push_eq_append]
      · -- ¬hge : literal
        rw [ih _ (by omega) _ _ _ _ _ _ rfl, List.toArray_cons,
          ← Array.append_assoc, Array.push_eq_append]
    · simp only [hlt, ↓reduceDIte]
      exact trailing_eq data pos acc

/-- `lz77ChainLazyIter32` produces exactly the same tokens as `lz77ChainLazy32`. -/
theorem lz77ChainLazyIter32_eq_lz77ChainLazy32 (data : ByteArray)
    (maxChain windowSize insertCap : Nat) :
    lz77ChainLazyIter32 data maxChain windowSize insertCap =
      lz77ChainLazy32 data maxChain windowSize insertCap := by
  unfold lz77ChainLazyIter32 lz77ChainLazy32
  split
  · rw [trailing_eq]; simp only [List.append_toArray, List.nil_append]
  · rw [mainLoop_eq_chainLazy32]; simp only [List.append_toArray, List.nil_append]

theorem lz77ChainLazyIter32_valid (data : ByteArray) (maxChain windowSize insertCap : Nat)
    (hw : windowSize > 0) :
    ValidDecomp data 0 (lz77ChainLazyIter32 data maxChain windowSize insertCap).toList := by
  rw [lz77ChainLazyIter32_eq_lz77ChainLazy32]
  exact lz77ChainLazy32_valid data maxChain windowSize insertCap hw

theorem lz77ChainLazyIter32_resolves (data : ByteArray) (maxChain windowSize insertCap : Nat)
    (hw : windowSize > 0) :
    Deflate.Spec.resolveLZ77 (tokensToSymbols (lz77ChainLazyIter32 data maxChain windowSize insertCap)) [] =
      some data.data.toList := by
  rw [lz77ChainLazyIter32_eq_lz77ChainLazy32]
  exact lz77ChainLazy32_resolves data maxChain windowSize insertCap hw

theorem lz77ChainLazyIter32_encodable (data : ByteArray) (maxChain windowSize insertCap : Nat)
    (hw : windowSize > 0) (hws : windowSize ≤ 32768) :
    ∀ t ∈ (lz77ChainLazyIter32 data maxChain windowSize insertCap).toList,
      match t with
      | .literal _ => True
      | .reference len dist => 3 ≤ len ∧ len ≤ 258 ∧ 1 ≤ dist ∧ dist ≤ 32768 := by
  rw [lz77ChainLazyIter32_eq_lz77ChainLazy32]
  exact lz77ChainLazy32_encodable data maxChain windowSize insertCap hw hws

/-- The lazy 32-bit chain matcher emits no tokens on empty input. -/
theorem lz77ChainLazyIter32_empty (data : ByteArray) (maxChain windowSize insertCap : Nat)
    (hzero : data.size = 0) : lz77ChainLazyIter32 data maxChain windowSize insertCap = #[] := by
  rw [lz77ChainLazyIter32_eq_lz77ChainLazy32]
  simp only [lz77ChainLazy32, show data.size < 3 from by omega, ↓reduceIte]
  have htrail : lz77Greedy.trailing data 0 = [] := by
    unfold lz77Greedy.trailing
    simp only [show ¬(0 < data.size) from by omega, ↓reduceDIte]
  rw [htrail]

end Zip.Native.Deflate
