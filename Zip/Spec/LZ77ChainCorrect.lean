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
        · exact ih (prev[cand &&& 0x7FFF]!) _ _
            (Or.inr ⟨hc.1, hc.2, hcand, fun i hi => (hcm.1 i hi).symm, hcm.2⟩)
      · simp only [hml, ↓reduceIte]
        split
        · exact hb
        · exact ih (prev[cand &&& 0x7FFF]!) _ _ hb
    · exact hb

/-! ## Guarded per-position head insertion (Wave 3 Step 0.2, Wave 5 de-boxing)

The mainLoops perform their per-position chain-head insertion (and, in the
lazy variants, the lookahead head probe) through `headProbeGuarded` + two
`guardedSet`s — single-value steps that trade the panic-checked `[..]!`/`set!`
operations for one runtime bounds check each without allocating
`headInsertGuarded`'s result tuple. The lemmas below rewrite them back to the
original panic-checked operations, so every proof that unfolds a mainLoop
proceeds exactly as before the conversion. -/

/-- The guarded head insertion computes exactly the panic-checked triple:
    in bounds, `getElem!_pos` and `setIfInBounds_def` bridge `[..]'h`/`set`
    to `[..]!`/`set!`; out of bounds, the fallback *is* the panic-checked
    sequence. -/
theorem headInsertGuarded_eq (hashTable : Array Nat) (prev : Array Nat) (h pos : Nat) :
    headInsertGuarded hashTable prev h pos =
      (hashTable[h]!, hashTable.set! h pos, prev.set! (pos &&& 0x7FFF) hashTable[h]!) := by
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

/-- The guarded single write computes exactly the panic-checked write. -/
theorem guardedSet_eq {α : Type} (a : Array α) (i : Nat) (v : α) :
    guardedSet a i v = a.set! i v := by
  unfold guardedSet
  split
  · rename_i hb
    simp only [Array.set!_eq_setIfInBounds, Array.setIfInBounds_def, dif_pos hb]
  · rfl

/-- `lz77Chain.mainLoop` produces a valid decomposition from `pos`. Mirrors
    `lz77Greedy.mainLoop_valid`; the reference case uses `chainWalk_spec` (which
    holds for *any* `prev` array) in place of the inline single-probe match. -/
theorem lz77Chain_mainLoop_valid (data : ByteArray) (windowSize hashSize maxChain : Nat)
    (hashTable : Array Nat) (prev : Array Nat) (pos insertCap : Nat) (hw : windowSize > 0) :
    ValidDecomp data pos
      (lz77Chain.mainLoop data windowSize hashSize maxChain hashTable prev pos insertCap) := by
  unfold lz77Chain.mainLoop
  split
  · rename_i hlt
    dsimp only
    simp only [headProbeGuarded_eq, guardedSet_eq]
    have hspec := chainWalk_spec data
      (prev.set! (pos &&& 0x7FFF) hashTable[lz77Greedy.hash3 data pos hashSize hlt]!)
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
    (hashTable : Array Nat) (prev : Array Nat) (pos insertCap : Nat) (hw : windowSize > 0) (hws : windowSize ≤ 32768) :
    ∀ t ∈ lz77Chain.mainLoop data windowSize hashSize maxChain hashTable prev pos insertCap, Enc t := by
  unfold lz77Chain.mainLoop
  split
  · rename_i hlt
    dsimp only
    simp only [headProbeGuarded_eq, guardedSet_eq]
    have hspec := chainWalk_spec data
      (prev.set! (pos &&& 0x7FFF) hashTable[lz77Greedy.hash3 data pos hashSize hlt]!)
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
  · intro t ht
    exact trailing_encodable data 0 t ht
  · intro t ht
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
    (windowSize pos maxLen : Nat) (hpm : pos + maxLen ≤ data.size) (hps : min chainWinSize data.size ≤ prev.size)
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
      rw [getElem!_pos prev (cand &&& 0x7FFF) (by have := winMask_lt cand; have := Nat.and_le_left (n := cand) (m := 0x7FFF); omega)]
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

/-! ## Packed chain walk (Wave 5 de-boxing)

`chainWalkPacked` carries and returns the `(bestLen, bestPos)` accumulator as
the single small `Nat` `bestPos * 512 + bestLen` so the hot per-position call
allocates no pair. `chainWalkPacked_eq` is the lockstep equality with
`chainWalkFast`; since the walk's best length never exceeds `maxLen`
(`chainWalk_fst_le`, from `chainWalk_spec`) and every matcher call site clamps
`maxLen` to `min 258 _ < 512`, the `_mod`/`_div` lemmas decode the packed
result back to the reference walk's components exactly. The iterative-vs-
recursive mainLoop proofs rewrite with the decode lemmas (side condition
discharged by `min258_le_511`) and then proceed exactly as before. -/

/-- Contrapositive of `countMatch_matches`: if the byte at offset `k` mismatches,
    the match cannot reach length `k`, so `countMatch ≤ k`. This is what makes the
    `chainWalkPacked` prefilter output-preserving — a candidate whose byte at the
    current best length differs cannot beat it, so skipping its full compare loses
    nothing. -/
theorem countMatch_le_of_byte_ne (data : ByteArray) (cand pos maxLen : Nat)
    (hcand : cand + maxLen ≤ data.size) (hpm : pos + maxLen ≤ data.size)
    (k : Nat) (hne : data[cand + k]! ≠ data[pos + k]!) :
    lz77Greedy.countMatch data cand pos maxLen hcand hpm ≤ k := by
  rcases Nat.lt_or_ge k (lz77Greedy.countMatch data cand pos maxLen hcand hpm) with h | h
  · exact absurd ((lz77Greedy.countMatch_matches data cand pos maxLen hcand hpm).1 k h) hne
  · exact h

/-- The packed walk computes exactly the packed image of the proven-bounds
    walk: identical control flow, with the pair accumulator carried as
    `bestPos * 512 + bestLen` at every step. -/
theorem chainWalkPacked_eq (data : ByteArray) (prev : Array Nat)
    (windowSize pos maxLen : Nat) (hpm : pos + maxLen ≤ data.size) (hps : min chainWinSize data.size ≤ prev.size)
    (cand fuel bestLen bestPos : Nat) :
    chainWalkPacked data prev windowSize pos maxLen hpm hps cand fuel bestLen bestPos =
      (chainWalkFast data prev windowSize pos maxLen hpm hps cand fuel bestLen bestPos).2 * 512 +
        (chainWalkFast data prev windowSize pos maxLen hpm hps cand fuel bestLen bestPos).1 := by
  induction fuel generalizing cand bestLen bestPos with
  | zero => rw [chainWalkPacked, chainWalkFast]; simp only [↓reduceIte]
  | succ k ih =>
    rw [chainWalkPacked, chainWalkFast, if_neg (by omega : ¬ (k + 1 = 0)),
      if_neg (by omega : ¬ (k + 1 = 0))]
    by_cases hc : cand < pos ∧ pos - cand ≤ windowSize
    · have hcand : cand + maxLen ≤ data.size := by omega
      simp only [dif_pos hc, Nat.add_sub_cancel]
      -- The prefilter `skip` only fires when the byte at offset `bestLen`
      -- mismatches; then `countMatch ≤ bestLen` (contrapositive of
      -- `countMatch_matches`), so the un-prefiltered `chainWalkFast` does not
      -- update either and recurses with `(bestLen, bestPos)` — same as the skip.
      by_cases hbl : bestLen < maxLen
      · simp only [dif_pos hbl]
        by_cases hbyte : data[cand + bestLen]'(by omega) = data[pos + bestLen]'(by omega)
        · -- bytes equal → skip = false → the full-compare path
          rw [hbyte]
          simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
          by_cases hml : lz77Greedy.countMatch data cand pos maxLen hcand hpm > bestLen
          · by_cases hb : lz77Greedy.countMatch data cand pos maxLen hcand hpm ≥ maxLen
            · simp only [hml, hb, ↓reduceIte]
            · simp only [hml, hb, ↓reduceIte, ih]
          · by_cases hb : bestLen ≥ maxLen
            · simp only [hml, hb, ↓reduceIte]
            · simp only [hml, hb, ↓reduceIte, ih]
        · -- bytes differ → skip = true → both sides recurse with (bestLen, bestPos)
          have hne! : data[cand + bestLen]! ≠ data[pos + bestLen]! := by
            rw [getElem!_pos data (cand + bestLen) (by omega),
              getElem!_pos data (pos + bestLen) (by omega)]
            exact hbyte
          have hle := countMatch_le_of_byte_ne data cand pos maxLen hcand hpm bestLen hne!
          simp only [bne_iff_ne.mpr hbyte, ↓reduceIte, Nat.not_lt.mpr hle,
            Nat.not_le.mpr hbl, ih]
      · -- bestLen ≥ maxLen → skip = false; countMatch ≤ maxLen ≤ bestLen, no update
        simp only [dif_neg hbl, Bool.false_eq_true, ↓reduceIte]
        have hle : lz77Greedy.countMatch data cand pos maxLen hcand hpm ≤ bestLen :=
          Nat.le_trans (lz77Greedy.countMatch_matches data cand pos maxLen hcand hpm).2
            (Nat.le_of_not_lt hbl)
        simp only [Nat.not_lt.mpr hle, ge_iff_le, Nat.le_of_not_lt hbl, ↓reduceIte]
    · simp only [dif_neg hc]

/-! ### USize chain walk (Wave 7 P1b)

`chainWalkPackedU` is the unboxed `USize` twin of `chainWalkPacked`; under the
invariant that every `prev` entry is `≤ data.size` (so each chain link
round-trips through `USize`), it computes exactly `chainWalkPacked`. The window
clamp `min windowSize data.size` makes the `USize` comparison need no
`windowSize < USize.size` hypothesis: for an in-window candidate
(`cand < pos ≤ data.size`) the `data.size` cap is slack, so the clamped check
agrees with the `Nat` check `pos - cand ≤ windowSize`. -/

/-- The `USize` chain walk equals the `Nat` packed walk, provided every `prev`
    entry — read back as the next loop index — is `≤ data.size` (`hpb`), which
    under the addressability bound `data.size < USize.size` (`hsz`) makes each
    link round-trip through `USize`. The loop scalars (`cand`/`bestLen`/`bestPos`)
    are likewise bounded by `data.size` so their `.toUSize` round-trips. -/
theorem chainWalkPackedU_eq (data : ByteArray) (prev : Array Nat)
    (windowSize pos maxLen : Nat) (hsz : data.size < USize.size)
    (hpm : pos + maxLen ≤ data.size) (hps : min chainWinSize data.size ≤ prev.size)
    (hpb : ∀ i (h : i < prev.size), prev[i] ≤ data.size)
    (cand fuel bestLen bestPos : Nat)
    (hcb : cand ≤ data.size) (hlb : bestLen ≤ data.size) (hpbp : bestPos ≤ data.size) :
    chainWalkPackedU data prev pos.toUSize maxLen.toUSize (min windowSize data.size).toUSize
        hsz (by rw [toUSize_toNat_of_lt (show pos < USize.size by omega),
              toUSize_toNat_of_lt (show maxLen < USize.size by omega)]; exact hpm)
        hps cand.toUSize fuel bestLen.toUSize bestPos.toUSize =
      chainWalkPacked data prev windowSize pos maxLen hpm hps cand fuel bestLen bestPos := by
  have hUS : USize.size = 2 ^ System.Platform.numBits := rfl
  have hposN : (pos.toUSize).toNat = pos := toUSize_toNat_of_lt (by omega)
  have hmaxN : (maxLen.toUSize).toNat = maxLen := toUSize_toNat_of_lt (by omega)
  have hwN : ((min windowSize data.size).toUSize).toNat = min windowSize data.size :=
    toUSize_toNat_of_lt (by omega)
  have e7 : (0x7FFF : USize).toNat = 0x7FFF := USize.toNat_ofNat_of_lt_32 (by decide)
  induction fuel generalizing cand bestLen bestPos with
  | zero =>
    have hcandN : (cand.toUSize).toNat = cand := toUSize_toNat_of_lt (by omega)
    have hbestlenN : (bestLen.toUSize).toNat = bestLen := toUSize_toNat_of_lt (by omega)
    have hbestposN : (bestPos.toUSize).toNat = bestPos := toUSize_toNat_of_lt (by omega)
    rw [chainWalkPackedU, chainWalkPacked]
    simp only [↓reduceIte, hbestlenN, hbestposN]
  | succ k ih =>
    have hcandN : (cand.toUSize).toNat = cand := toUSize_toNat_of_lt (by omega)
    have hbestlenN : (bestLen.toUSize).toNat = bestLen := toUSize_toNat_of_lt (by omega)
    have hbestposN : (bestPos.toUSize).toNat = bestPos := toUSize_toNat_of_lt (by omega)
    have hsub : cand < pos → (pos.toUSize - cand.toUSize).toNat = pos - cand := by
      intro h
      rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr (by rw [hcandN, hposN]; omega)),
        hcandN, hposN]
    have key : (cand.toUSize < pos.toUSize ∧
          pos.toUSize - cand.toUSize ≤ (min windowSize data.size).toUSize)
        ↔ (cand < pos ∧ pos - cand ≤ windowSize) := by
      constructor
      · rintro ⟨h1, h2⟩
        have h1' : cand < pos := by
          have := USize.lt_iff_toNat_lt.mp h1; rwa [hcandN, hposN] at this
        refine ⟨h1', ?_⟩
        have := USize.le_iff_toNat_le.mp h2
        rw [hsub h1', hwN] at this; omega
      · rintro ⟨h1, h2⟩
        refine ⟨USize.lt_iff_toNat_lt.mpr (by rw [hcandN, hposN]; exact h1), ?_⟩
        apply USize.le_iff_toNat_le.mpr
        rw [hsub h1, hwN]; omega
    rw [chainWalkPackedU, chainWalkPacked, if_neg (by omega : ¬ (k + 1 = 0)),
      if_neg (by omega : ¬ (k + 1 = 0))]
    by_cases hc : cand < pos ∧ pos - cand ≤ windowSize
    · rw [dif_pos (key.mpr hc), dif_pos hc]
      have hcandlt : cand < pos := hc.1
      have hcand : cand + maxLen ≤ data.size := by omega
      -- masked chain read: index and value bridge `USize` ↔ `Nat`
      have hidxN : (cand.toUSize &&& 0x7FFF).toNat = cand &&& 0x7FFF := by
        rw [USize.toNat_and, hcandN, e7]
      simp only [hidxN, hcandN, hposN, hmaxN]
      have hmask' : cand &&& 0x7FFF < prev.size := by
        have := winMask_lt cand; have := Nat.and_le_left (n := cand) (m := 0x7FFF); omega
      have he_le : prev[cand &&& 0x7FFF] ≤ data.size := hpb _ hmask'
      -- prefilter byte loads bridge
      have hbliff : (bestLen.toUSize < maxLen.toUSize) = (bestLen < maxLen) := by
        simp only [USize.lt_iff_toNat_lt, hbestlenN, hmaxN]
      by_cases hbl : bestLen < maxLen
      · have haddc : (cand.toUSize + bestLen.toUSize).toNat = cand + bestLen := by
          rw [USize.toNat_add, hcandN, hbestlenN]; apply Nat.mod_eq_of_lt; omega
        have haddp : (pos.toUSize + bestLen.toUSize).toNat = pos + bestLen := by
          rw [USize.toNat_add, hposN, hbestlenN]; apply Nat.mod_eq_of_lt; omega
        simp only [hbliff, dif_pos hbl, uget_eq_getElem, haddc, haddp]
        by_cases hbyte : data[cand + bestLen]'(by omega) = data[pos + bestLen]'(by omega)
        · rw [hbyte]; simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
          have hmliff : (((lz77Greedy.countMatch data cand pos maxLen hcand hpm).toUSize >
              bestLen.toUSize)) = (lz77Greedy.countMatch data cand pos maxLen hcand hpm > bestLen) := by
            have hmle : lz77Greedy.countMatch data cand pos maxLen hcand hpm ≤ maxLen :=
              (lz77Greedy.countMatch_matches data cand pos maxLen hcand hpm).2
            simp only [USize.lt_iff_toNat_lt, hbestlenN,
              toUSize_toNat_of_lt (show lz77Greedy.countMatch data cand pos maxLen hcand hpm
                < USize.size by omega)]
          by_cases hml : lz77Greedy.countMatch data cand pos maxLen hcand hpm > bestLen
          · have hmle : lz77Greedy.countMatch data cand pos maxLen hcand hpm ≤ maxLen :=
              (lz77Greedy.countMatch_matches data cand pos maxLen hcand hpm).2
            have hmcb : lz77Greedy.countMatch data cand pos maxLen hcand hpm ≤ data.size := by omega
            have hmlN : ((lz77Greedy.countMatch data cand pos maxLen hcand hpm).toUSize).toNat
                = lz77Greedy.countMatch data cand pos maxLen hcand hpm :=
              toUSize_toNat_of_lt (by omega)
            simp only [hmliff, hml, ↓reduceIte]
            by_cases hb : lz77Greedy.countMatch data cand pos maxLen hcand hpm ≥ maxLen
            · simp only [ge_iff_le, USize.le_iff_toNat_le, hmlN, hmaxN, hb, ↓reduceIte, hcandN]
            · simp only [ge_iff_le, USize.le_iff_toNat_le, hmlN, hmaxN, hb, ↓reduceIte]
              exact ih _ _ _ he_le hmcb hcb
          · simp only [hmliff, hml, ↓reduceIte]
            by_cases hb : bestLen ≥ maxLen
            · simp only [ge_iff_le, USize.le_iff_toNat_le, hbestlenN, hmaxN, hb, ↓reduceIte,
                hbestposN]
            · simp only [ge_iff_le, USize.le_iff_toNat_le, hbestlenN, hmaxN, hb, ↓reduceIte]
              exact ih _ _ _ he_le hlb hpbp
        · have hne! : data[cand + bestLen]! ≠ data[pos + bestLen]! := by
            rw [getElem!_pos data (cand + bestLen) (by omega),
              getElem!_pos data (pos + bestLen) (by omega)]
            exact hbyte
          have hle := countMatch_le_of_byte_ne data cand pos maxLen hcand hpm bestLen hne!
          simp only [bne_iff_ne.mpr hbyte, ↓reduceIte, Nat.not_lt.mpr hle,
            Nat.not_le.mpr hbl]
          exact ih _ _ _ he_le hlb hpbp
      · simp only [hbliff, dif_neg hbl, Bool.false_eq_true, ↓reduceIte]
        have hle : lz77Greedy.countMatch data cand pos maxLen hcand hpm ≤ bestLen :=
          Nat.le_trans (lz77Greedy.countMatch_matches data cand pos maxLen hcand hpm).2
            (Nat.le_of_not_lt hbl)
        have hmliff : (((lz77Greedy.countMatch data cand pos maxLen hcand hpm).toUSize >
            bestLen.toUSize)) = (lz77Greedy.countMatch data cand pos maxLen hcand hpm > bestLen) := by
          have hmle : lz77Greedy.countMatch data cand pos maxLen hcand hpm ≤ maxLen :=
            (lz77Greedy.countMatch_matches data cand pos maxLen hcand hpm).2
          simp only [USize.lt_iff_toNat_lt, hbestlenN,
            toUSize_toNat_of_lt (show lz77Greedy.countMatch data cand pos maxLen hcand hpm
              < USize.size by omega)]
        simp only [hmliff, Nat.not_lt.mpr hle, ↓reduceIte, ge_iff_le, USize.le_iff_toNat_le,
          hbestlenN, hmaxN, Nat.le_of_not_lt hbl, hbestlenN, hbestposN]
    · rw [dif_neg (fun hh => hc (key.mp hh)), dif_neg hc]
      simp only [hbestlenN, hbestposN]

/-- One runtime guard collapses the packed walk to the packed image of the
    reference walk. The `USize` dispatch (when the buffer is addressable) needs
    the chain state bounded by `data.size`: every `prev` entry (`hpb`) and the
    seed `cand`/`bestLen`/`bestPos` round-trip through `USize`. -/
theorem chainWalkGuardedPacked_eq (data : ByteArray) (prev : Array Nat)
    (windowSize pos maxLen : Nat) (hpm : pos + maxLen ≤ data.size)
    (cand fuel bestLen bestPos : Nat)
    (hpb : ∀ i (h : i < prev.size), prev[i] ≤ data.size)
    (hcb : cand ≤ data.size) (hlb : bestLen ≤ data.size) (hpbp : bestPos ≤ data.size) :
    chainWalkGuardedPacked data prev windowSize pos maxLen hpm cand fuel bestLen bestPos =
      (lz77Chain.chainWalk data prev windowSize pos maxLen hpm cand fuel bestLen bestPos).2 * 512 +
        (lz77Chain.chainWalk data prev windowSize pos maxLen hpm cand fuel bestLen bestPos).1 := by
  unfold chainWalkGuardedPacked
  split
  · rename_i hps
    split
    · rename_i hsz
      have hszU : data.size < USize.size := by
        rw [← hsz]; exact USize.toNat_lt_two_pow_numBits _
      rw [chainWalkPackedU_eq (hpb := hpb) (hcb := hcb) (hlb := hlb) (hpbp := hpbp),
        chainWalkPacked_eq, chainWalkFast_eq]
    · rw [chainWalkPacked_eq, chainWalkFast_eq]
  · rfl

/-- From a zero-initialised best length, the reference walk's best length
    never exceeds `maxLen` (specialisation of `chainWalk_spec`). -/
theorem chainWalk_fst_le (data : ByteArray) (prev : Array Nat)
    (windowSize pos maxLen : Nat) (hpm : pos + maxLen ≤ data.size) (cand fuel : Nat) :
    (lz77Chain.chainWalk data prev windowSize pos maxLen hpm cand fuel 0 0).1 ≤ maxLen := by
  obtain h0 | hQ := chainWalk_spec data prev windowSize pos maxLen hpm cand fuel 0 0 (Or.inl rfl)
  · omega
  · exact hQ.2.2.2.2

/-- Decode the packed walk's best length: with `maxLen < 512` the low bits are
    exactly the reference walk's `bestLen`. -/
theorem chainWalkGuardedPacked_mod (data : ByteArray) (prev : Array Nat)
    (windowSize pos maxLen : Nat) (hpm : pos + maxLen ≤ data.size) (cand fuel : Nat)
    (hml : maxLen ≤ 511)
    (hpb : ∀ i (h : i < prev.size), prev[i] ≤ data.size) (hcb : cand ≤ data.size) :
    chainWalkGuardedPacked data prev windowSize pos maxLen hpm cand fuel 0 0 % 512 =
      (lz77Chain.chainWalk data prev windowSize pos maxLen hpm cand fuel 0 0).1 := by
  rw [chainWalkGuardedPacked_eq (hpb := hpb) (hcb := hcb) (hlb := Nat.zero_le _)
    (hpbp := Nat.zero_le _)]
  have h := chainWalk_fst_le data prev windowSize pos maxLen hpm cand fuel
  omega

/-- Decode the packed walk's best position (the high bits). -/
theorem chainWalkGuardedPacked_div (data : ByteArray) (prev : Array Nat)
    (windowSize pos maxLen : Nat) (hpm : pos + maxLen ≤ data.size) (cand fuel : Nat)
    (hml : maxLen ≤ 511)
    (hpb : ∀ i (h : i < prev.size), prev[i] ≤ data.size) (hcb : cand ≤ data.size) :
    chainWalkGuardedPacked data prev windowSize pos maxLen hpm cand fuel 0 0 / 512 =
      (lz77Chain.chainWalk data prev windowSize pos maxLen hpm cand fuel 0 0).2 := by
  rw [chainWalkGuardedPacked_eq (hpb := hpb) (hcb := hcb) (hlb := Nat.zero_le _)
    (hpbp := Nat.zero_le _)]
  have h := chainWalk_fst_le data prev windowSize pos maxLen hpm cand fuel
  omega

/-- Every matcher call site clamps `maxLen` to `min 258 _`; this discharges
    the `maxLen ≤ 511` side condition when `simp` applies the decode lemmas. -/
theorem min258_le_511 (x : Nat) : min 258 x ≤ 511 := by omega

/-- The proven-bounds hash-insertion loop computes the same arrays as the
    panic-checked reference: the bodies differ only in how `hashTable[hsh]` is
    accessed, bridged by `getElem!_pos`. -/
theorem updateHashesFast_eq (data : ByteArray) (hashSize : Nat)
    (hashTable : Array Nat) (prev : Array Nat) (pos j matchLen insertCap : Nat)
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
        exact ih _ (by omega) _ _ _
          (by simpa only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds] using hht) rfl
      · rw [dif_neg hd, dif_neg hd]
        exact ih _ (by omega) _ _ _ hht rfl
    · rw [if_neg hcond, if_neg hcond]

/-- The `uset`-write insertion walk (`updateHashesFastU`) is the proven-bounds
    `set!` walk: identical control flow, with the two writes' in-bounds `set`
    collapsing to `set!` (`Array.set!_eq_setIfInBounds` + `dif_pos`) at each step. -/
theorem updateHashesFastU_eq (data : ByteArray) (hashSize : Nat)
    (hashTable : Array Nat) (prev : Array Nat) (pos j matchLen insertCap : Nat)
    (hhs : 0 < hashSize) (hht : hashSize ≤ hashTable.size)
    (hpv : min chainWinSize data.size ≤ prev.size) :
    updateHashesFastU data hashSize hashTable prev pos j matchLen insertCap hhs hht hpv =
      updateHashesFast data hashSize hashTable prev pos j matchLen insertCap hhs hht := by
  induction hn : matchLen - j using Nat.strongRecOn generalizing j hashTable prev hht hpv with
  | _ n ih =>
    unfold updateHashesFastU updateHashesFast
    by_cases hcond : j < matchLen ∧ j ≤ insertCap
    · rw [if_pos hcond, if_pos hcond]
      by_cases hd : pos + j + 2 < data.size
      · rw [dif_pos hd, dif_pos hd]
        have hb : lz77Greedy.hash3 data (pos + j) hashSize hd < hashTable.size := by
          have : lz77Greedy.hash3 data (pos + j) hashSize hd < hashSize := Nat.mod_lt _ hhs
          omega
        have hmask : ((pos + j) &&& 0x7FFF) < prev.size := by
          have h1 := winMask_lt (pos + j)
          have h2 := Nat.and_le_left (n := pos + j) (m := 0x7FFF)
          simp only [chainWinSize] at h1 hpv; omega
        have e1 : hashTable.set (lz77Greedy.hash3 data (pos + j) hashSize hd) (pos + j) hb
            = hashTable.set! (lz77Greedy.hash3 data (pos + j) hashSize hd) (pos + j) := by
          rw [Array.set!_eq_setIfInBounds, Array.setIfInBounds, dif_pos hb]
        have e2 : prev.set ((pos + j) &&& 0x7FFF)
              (hashTable[lz77Greedy.hash3 data (pos + j) hashSize hd]'hb) hmask
            = prev.set! ((pos + j) &&& 0x7FFF)
              (hashTable[lz77Greedy.hash3 data (pos + j) hashSize hd]'hb) := by
          rw [Array.set!_eq_setIfInBounds, Array.setIfInBounds, dif_pos hmask]
        simp only [e1, e2]
        exact ih _ (by omega) _ _ _ (by rw [Array.size_set!]; exact hht)
          (by rw [Array.size_set!]; exact hpv) rfl
      · rw [dif_neg hd, dif_neg hd]
        exact ih _ (by omega) _ _ _ hht hpv rfl
    · rw [if_neg hcond, if_neg hcond]

/-- One runtime guard collapses to the reference insertion. -/
theorem updateHashesGuarded_eq (data : ByteArray) (hashSize : Nat)
    (hashTable : Array Nat) (prev : Array Nat) (pos j matchLen insertCap : Nat) :
    updateHashesGuarded data hashSize hashTable prev pos j matchLen insertCap =
      lz77Chain.updateHashes data hashSize hashTable prev pos j matchLen insertCap := by
  unfold updateHashesGuarded
  split
  · split
    · exact (updateHashesFastU_eq ..).trans (updateHashesFast_eq ..)
    · exact updateHashesFast_eq ..
  · rfl

/-! ### `prev`/`hashTable` entries-`≤ data.size` invariant (Wave 7 P1b)

The chain arrays start as `.replicate _ data.size` and are only ever written
positions `≤ data.size` (or a previously-stored entry), so every entry stays
`≤ data.size`. That is exactly the hypothesis the `USize` chain walk needs to
round-trip each link (`chainWalkPackedU_eq`); threaded through the iterative
mainLoops below it discharges the `chainWalkGuardedPacked_mod`/`_div` bound side
conditions. -/

/-- A `Nat` array all of whose entries are `≤ n` has every `getElem!` `≤ n`
    (out-of-bounds reads return the `0` default). -/
theorem getElem!_bounded {n : Nat} (a : Array Nat) (k : Nat)
    (ha : ∀ i (h : i < a.size), a[i] ≤ n) : a[k]! ≤ n := by
  by_cases hk : k < a.size
  · rw [getElem!_pos a k hk]; exact ha k hk
  · rw [getElem!_neg a k hk]; exact Nat.zero_le n

/-- `set!` preserves the entries-`≤ n` invariant when the written value is `≤ n`. -/
theorem set!_bounded {n : Nat} (a : Array Nat) (j v : Nat)
    (ha : ∀ i (h : i < a.size), a[i] ≤ n) (hv : v ≤ n) :
    ∀ i (h : i < (a.set! j v).size), (a.set! j v)[i] ≤ n := by
  intro i hi
  have hia : i < a.size := by
    simpa only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds] using hi
  simp only [Array.set!_eq_setIfInBounds, Array.getElem_setIfInBounds hia]
  split
  · exact hv
  · exact ha i hia

/-- `guardedSet` preserves the entries-`≤ n` invariant when the value is `≤ n`. -/
theorem guardedSet_bounded {n : Nat} (a : Array Nat) (j v : Nat)
    (ha : ∀ i (h : i < a.size), a[i] ≤ n) (hv : v ≤ n) :
    ∀ i (h : i < (guardedSet a j v).size), (guardedSet a j v)[i] ≤ n := by
  simp only [guardedSet_eq]; exact set!_bounded a j v ha hv

/-- A guarded chain-head probe of a bounded table is `≤ n`. -/
theorem headProbeGuarded_bounded {n : Nat} (a : Array Nat) (h : Nat)
    (ha : ∀ i (hi : i < a.size), a[i] ≤ n) : headProbeGuarded a h ≤ n := by
  rw [headProbeGuarded_eq]; exact getElem!_bounded a h ha

/-- The reference hash-insertion loop preserves the entries-`≤ data.size`
    invariant on both arrays: interior positions `pos + j` are inserted only when
    `pos + j + 2 < data.size`, and `prev` only ever receives a previously-stored
    (hence bounded) bucket head. -/
theorem updateHashes_bounded (data : ByteArray) (hashSize : Nat)
    (hashTable prev : Array Nat) (pos j matchLen insertCap : Nat)
    (hht : ∀ i (h : i < hashTable.size), hashTable[i] ≤ data.size)
    (hpv : ∀ i (h : i < prev.size), prev[i] ≤ data.size) :
    (∀ i (h : i < (lz77Chain.updateHashes data hashSize hashTable prev pos j matchLen insertCap).1.size),
        (lz77Chain.updateHashes data hashSize hashTable prev pos j matchLen insertCap).1[i] ≤ data.size) ∧
    (∀ i (h : i < (lz77Chain.updateHashes data hashSize hashTable prev pos j matchLen insertCap).2.size),
        (lz77Chain.updateHashes data hashSize hashTable prev pos j matchLen insertCap).2[i] ≤ data.size) := by
  induction hn : matchLen - j using Nat.strongRecOn generalizing j hashTable prev with
  | _ m ih =>
    unfold lz77Chain.updateHashes
    split
    · split
      · rename_i hd
        exact ih _ (by omega) _ _ _
          (set!_bounded _ _ _ hht (by omega))
          (set!_bounded _ _ _ hpv (getElem!_bounded _ _ hht)) rfl
      · exact ih _ (by omega) _ _ _ hht hpv rfl
    · exact ⟨hht, hpv⟩

/-! ## Iterative version: equivalence + transferred contracts -/

/-- The accumulator `trailing` is the array form of the recursive one. Shared by
    `LZ77ChainLazyCorrect` (which imports this file) so the lazy iterative proof
    reuses it rather than carrying its own copy. -/
theorem trailing_eq (data : ByteArray) (pos : Nat) (acc : Array LZ77Token) :
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
    (hashTable : Array Nat) (prev : Array Nat) (pos : Nat) (acc : Array LZ77Token)
    (hht : ∀ i (h : i < hashTable.size), hashTable[i] ≤ data.size)
    (hpv : ∀ i (h : i < prev.size), prev[i] ≤ data.size) :
    lz77ChainIter.mainLoop data windowSize hashSize maxChain insertCap hashTable prev pos acc =
    acc ++ (lz77Chain.mainLoop data windowSize hashSize maxChain hashTable prev pos insertCap).toArray := by
  induction h : data.size - pos using Nat.strongRecOn generalizing pos acc hashTable prev with
  | _ n ih =>
    unfold lz77ChainIter.mainLoop lz77Chain.mainLoop
    by_cases hlt : pos + 2 < data.size
    · -- entries-`≤ data.size` invariant on the per-position updated chain arrays
      have head_le : headProbeGuarded hashTable (lz77Greedy.hash3 data pos hashSize hlt) ≤ data.size :=
        headProbeGuarded_bounded _ _ hht
      have hht1 := guardedSet_bounded hashTable (lz77Greedy.hash3 data pos hashSize hlt) pos hht
        (by omega)
      have hpv1 := guardedSet_bounded prev (pos &&& 0x7FFF)
        (headProbeGuarded hashTable (lz77Greedy.hash3 data pos hashSize hlt)) hpv head_le
      simp only [hlt, ↓reduceDIte]
      rw [chainWalkGuardedPacked_mod (hml := min258_le_511 _) (hpb := hpv1) (hcb := head_le),
        chainWalkGuardedPacked_div (hml := min258_le_511 _) (hpb := hpv1) (hcb := head_le)]
      simp only [updateHashesGuarded_eq]
      split
      · split
        · rw [ih _ (by omega) _ _ _ _
            (updateHashes_bounded data hashSize _ _ pos 1 _ insertCap hht1 hpv1).1
            (updateHashes_bounded data hashSize _ _ pos 1 _ insertCap hht1 hpv1).2 rfl,
            List.toArray_cons, ← Array.append_assoc, Array.push_eq_append]
        · rw [ih _ (by omega) _ _ _ _ hht1 hpv1 rfl, List.toArray_cons,
            ← Array.append_assoc, Array.push_eq_append]
      · rw [ih _ (by omega) _ _ _ _ hht1 hpv1 rfl, List.toArray_cons,
          ← Array.append_assoc, Array.push_eq_append]
    · simp only [hlt, ↓reduceDIte]
      exact trailing_eq data pos acc

/-- `lz77ChainIter` produces exactly the same tokens as `lz77Chain`. -/
theorem lz77ChainIter_eq_lz77Chain (data : ByteArray) (maxChain windowSize insertCap : Nat) :
    lz77ChainIter data maxChain windowSize insertCap = lz77Chain data maxChain windowSize insertCap := by
  unfold lz77ChainIter lz77Chain
  split
  · rw [trailing_eq]; simp only [List.append_toArray, List.nil_append]
  · rw [mainLoop_eq_chain (hht := by intro i h; simp) (hpv := by intro i h; simp)]
    simp only [List.append_toArray, List.nil_append]

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
