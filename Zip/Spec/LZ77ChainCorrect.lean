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
    (windowSize pos maxLen niceLen : Nat) (hpm : pos + maxLen ≤ data.size)
    (cand fuel bestLen bestPos : Nat)
    (hb : bestLen = 0 ∨ (bestPos < pos ∧ pos - bestPos ≤ windowSize ∧
        bestPos + maxLen ≤ data.size ∧
        (∀ i, i < bestLen → data[pos + i]! = data[bestPos + i]!) ∧ bestLen ≤ maxLen)) :
    let r := lz77Chain.chainWalk data prev windowSize pos maxLen niceLen hpm cand fuel bestLen bestPos
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

/-! ## Hash3-singleton probe (#2742)

The chain walk is seeded with `hash3Probe`'s decoded result (`% 512` /
`/ 512` of the packed seed) instead of `(0, 0)`. The probe *verifies* its
candidate (window guard + three byte compares) before seeding, so the seed
satisfies exactly the invariant `chainWalk_spec` carries — the singleton
table's contents never enter the proof. -/

/-- The hash3-singleton probe's decoded seed is a real in-window match (or
    empty): exactly the initial-accumulator hypothesis `chainWalk_spec` takes
    at `bestLen := seed % 512`, `bestPos := seed / 512`. -/
theorem hash3Probe_spec (data : ByteArray) (windowSize pos cand3 : Nat)
    (hlt : pos + 2 < data.size) (maxLen : Nat) (hml : 3 ≤ maxLen)
    (hpm : pos + maxLen ≤ data.size) :
    hash3Probe data windowSize pos cand3 hlt % 512 = 0 ∨
      (hash3Probe data windowSize pos cand3 hlt / 512 < pos ∧
        pos - hash3Probe data windowSize pos cand3 hlt / 512 ≤ windowSize ∧
        hash3Probe data windowSize pos cand3 hlt / 512 + maxLen ≤ data.size ∧
        (∀ i, i < hash3Probe data windowSize pos cand3 hlt % 512 →
          data[pos + i]! = data[hash3Probe data windowSize pos cand3 hlt / 512 + i]!) ∧
        hash3Probe data windowSize pos cand3 hlt % 512 ≤ maxLen) := by
  unfold hash3Probe
  split
  · rename_i hc
    split
    · rename_i hbytes
      simp only [Bool.and_eq_true, beq_iff_eq] at hbytes
      have hm : (cand3 * 512 + 3) % 512 = 3 := by omega
      have hd : (cand3 * 512 + 3) / 512 = cand3 := by omega
      rw [hm, hd]
      refine Or.inr ⟨hc.1, hc.2, by omega, ?_, by omega⟩
      intro i hi
      have h3i : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      obtain rfl | rfl | rfl := h3i
      · rw [getElem!_pos data (pos + 0) (by omega), getElem!_pos data (cand3 + 0) (by omega)]
        simpa using hbytes.1.1.symm
      · rw [getElem!_pos data (pos + 1) (by omega), getElem!_pos data (cand3 + 1) (by omega)]
        exact hbytes.1.2.symm
      · rw [getElem!_pos data (pos + 2) (by omega), getElem!_pos data (cand3 + 2) (by omega)]
        exact hbytes.2.symm
    · exact Or.inl rfl
  · exact Or.inl rfl

/-- Any packed value decodes to a best length `≤ 511` — discharges
    `chainWalkGuardedPacked_mod`/`_div`'s side condition at the seeded call
    sites (the probe seed is decoded with the same `% 512`). -/
theorem mod512_le (x : Nat) : x % 512 ≤ 511 := by omega

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
theorem lz77Chain_mainLoop_valid (data : ByteArray) (windowSize hashSize maxChain niceLen : Nat)
    (hashTable : Array Nat) (prev : Array Nat) (h3tab : Array Nat) (pos insertCap : Nat)
    (hw : windowSize > 0) :
    ValidDecomp data pos
      (lz77Chain.mainLoop data windowSize hashSize maxChain niceLen hashTable prev h3tab pos insertCap) := by
  unfold lz77Chain.mainLoop
  split
  · rename_i hlt
    dsimp only
    simp only [headProbeGuarded_eq, guardedSet_eq]
    have hspec := chainWalk_spec data
      (prev.set! (pos &&& 0x7FFF) hashTable[lz77Greedy.hash3 data pos hashSize hlt]!)
      windowSize pos (min 258 (data.size - pos)) niceLen (by omega)
      hashTable[lz77Greedy.hash3 data pos hashSize hlt]! maxChain
      (hash3Probe data windowSize pos (h3tab[hash3Single data pos hlt]!) hlt % 512)
      (hash3Probe data windowSize pos (h3tab[hash3Single data pos hlt]!) hlt / 512)
      (hash3Probe_spec data windowSize pos (h3tab[hash3Single data pos hlt]!) hlt
        (min 258 (data.size - pos)) (by omega) (by omega))
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
          · exact lz77Chain_mainLoop_valid _ _ _ _ _ _ _ _ _ _ hw
      · exact .literal (by omega) (getElem!_pos data pos (by omega))
          (lz77Chain_mainLoop_valid _ _ _ _ _ _ _ _ _ _ hw)
    · exact .literal (by omega) (getElem!_pos data pos (by omega))
        (lz77Chain_mainLoop_valid _ _ _ _ _ _ _ _ _ _ hw)
  · exact trailing_valid data pos
termination_by data.size - pos
decreasing_by all_goals omega

/-- `lz77Chain` produces a valid decomposition of the input data. -/
theorem lz77Chain_valid (data : ByteArray) (maxChain windowSize insertCap niceLen : Nat)
    (hw : windowSize > 0) :
    ValidDecomp data 0 (lz77Chain data maxChain windowSize insertCap niceLen).toList := by
  simp only [lz77Chain]
  split
  · simp only; exact trailing_valid data 0
  · simp only; exact lz77Chain_mainLoop_valid data windowSize 65536 maxChain niceLen _ _ _ 0 insertCap hw

/-- Resolving the LZ77 tokens produced by `lz77Chain` recovers the original data. -/
theorem lz77Chain_resolves (data : ByteArray) (maxChain windowSize insertCap niceLen : Nat)
    (hw : windowSize > 0) :
    Deflate.Spec.resolveLZ77 (tokensToSymbols (lz77Chain data maxChain windowSize insertCap niceLen)) [] =
      some data.data.toList :=
  validDecomp_resolves data _ (lz77Chain_valid data maxChain windowSize insertCap niceLen hw)

/-! ## Encodability -/

/-- The bounds the dynamic/fixed encoders require of every token (inlined to
    match `deflateDynamicBlock_spec`'s `htok_enc` hypothesis). -/
private def Enc (t : LZ77Token) : Prop :=
  match t with
  | .literal _ => True
  | .reference len dist => 3 ≤ len ∧ len ≤ 258 ∧ 1 ≤ dist ∧ dist ≤ 32768

theorem lz77Chain_mainLoop_encodable (data : ByteArray) (windowSize hashSize maxChain niceLen : Nat)
    (hashTable : Array Nat) (prev : Array Nat) (h3tab : Array Nat) (pos insertCap : Nat)
    (hw : windowSize > 0) (hws : windowSize ≤ 32768) :
    ∀ t ∈ lz77Chain.mainLoop data windowSize hashSize maxChain niceLen hashTable prev h3tab pos insertCap, Enc t := by
  unfold lz77Chain.mainLoop
  split
  · rename_i hlt
    dsimp only
    simp only [headProbeGuarded_eq, guardedSet_eq]
    have hspec := chainWalk_spec data
      (prev.set! (pos &&& 0x7FFF) hashTable[lz77Greedy.hash3 data pos hashSize hlt]!)
      windowSize pos (min 258 (data.size - pos)) niceLen (by omega)
      hashTable[lz77Greedy.hash3 data pos hashSize hlt]! maxChain
      (hash3Probe data windowSize pos (h3tab[hash3Single data pos hlt]!) hlt % 512)
      (hash3Probe data windowSize pos (h3tab[hash3Single data pos hlt]!) hlt / 512)
      (hash3Probe_spec data windowSize pos (h3tab[hash3Single data pos hlt]!) hlt
        (min 258 (data.size - pos)) (by omega) (by omega))
    split
    · rename_i hge
      split
      · rename_i hle
        obtain h0 | ⟨hQ1, hQ2, _, _, hQ5⟩ := hspec
        · omega
        · intro t ht
          cases ht with
          | head => exact ⟨hge, by omega, by omega, by omega⟩
          | tail _ h => exact lz77Chain_mainLoop_encodable _ _ _ _ _ _ _ _ _ _ hw hws t h
      · intro t ht
        cases ht with
        | head => trivial
        | tail _ h => exact lz77Chain_mainLoop_encodable _ _ _ _ _ _ _ _ _ _ hw hws t h
    · intro t ht
      cases ht with
      | head => trivial
      | tail _ h => exact lz77Chain_mainLoop_encodable _ _ _ _ _ _ _ _ _ _ hw hws t h
  · intro t ht
    -- `trailing` emits only literals
    exact trailing_encodable data pos t ht
termination_by data.size - pos
decreasing_by all_goals omega

/-- Every token `lz77Chain` emits satisfies the encoder bounds. -/
theorem lz77Chain_encodable (data : ByteArray) (maxChain windowSize insertCap niceLen : Nat)
    (hw : windowSize > 0) (hws : windowSize ≤ 32768) :
    ∀ t ∈ (lz77Chain data maxChain windowSize insertCap niceLen).toList,
      match t with
      | .literal _ => True
      | .reference len dist => 3 ≤ len ∧ len ≤ 258 ∧ 1 ≤ dist ∧ dist ≤ 32768 := by
  simp only [lz77Chain]
  split
  · intro t ht
    exact trailing_encodable data 0 t ht
  · intro t ht
    exact lz77Chain_mainLoop_encodable data windowSize 65536 maxChain niceLen _ _ _ 0 insertCap hw hws t ht

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
    (windowSize pos maxLen niceLen : Nat) (hpm : pos + maxLen ≤ data.size) (hps : min chainWinSize data.size ≤ prev.size)
    (cand fuel bestLen bestPos : Nat) :
    chainWalkFast data prev windowSize pos maxLen niceLen hpm hps cand fuel bestLen bestPos =
      lz77Chain.chainWalk data prev windowSize pos maxLen niceLen hpm cand fuel bestLen bestPos := by
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
    (windowSize pos maxLen niceLen : Nat) (hpm : pos + maxLen ≤ data.size)
    (cand fuel bestLen bestPos : Nat) :
    chainWalkGuarded data prev windowSize pos maxLen niceLen hpm cand fuel bestLen bestPos =
      lz77Chain.chainWalk data prev windowSize pos maxLen niceLen hpm cand fuel bestLen bestPos := by
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
    (windowSize pos maxLen niceLen : Nat) (hpm : pos + maxLen ≤ data.size) (hps : min chainWinSize data.size ≤ prev.size)
    (cand fuel bestLen bestPos : Nat) :
    chainWalkPacked data prev windowSize pos maxLen niceLen hpm hps cand fuel bestLen bestPos =
      (chainWalkFast data prev windowSize pos maxLen niceLen hpm hps cand fuel bestLen bestPos).2 * 512 +
        (chainWalkFast data prev windowSize pos maxLen niceLen hpm hps cand fuel bestLen bestPos).1 := by
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
      -- update either and takes the same early-stop / recurse decision on
      -- `bestLen ≥ min niceLen maxLen` — matching the packed skip branch.
      by_cases hbl : bestLen < maxLen
      · simp only [dif_pos hbl]
        by_cases hbyte : data[cand + bestLen]'(by omega) = data[pos + bestLen]'(by omega)
        · -- bytes equal → skip = false → the full-compare path
          rw [hbyte]
          simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
          by_cases hml : lz77Greedy.countMatch data cand pos maxLen hcand hpm > bestLen
          · by_cases hb : lz77Greedy.countMatch data cand pos maxLen hcand hpm ≥ min niceLen maxLen
            · simp only [hml, hb, ↓reduceIte]
            · simp only [hml, hb, ↓reduceIte, ih]
          · by_cases hb : bestLen ≥ min niceLen maxLen
            · simp only [hml, hb, ↓reduceIte]
            · simp only [hml, hb, ↓reduceIte, ih]
        · -- bytes differ → skip = true → both sides take the `bestLen ≥ min niceLen maxLen`
          -- early-stop / recurse decision with `(bestLen, bestPos)` unchanged
          have hne! : data[cand + bestLen]! ≠ data[pos + bestLen]! := by
            rw [getElem!_pos data (cand + bestLen) (by omega),
              getElem!_pos data (pos + bestLen) (by omega)]
            exact hbyte
          have hle := countMatch_le_of_byte_ne data cand pos maxLen hcand hpm bestLen hne!
          by_cases hb : bestLen ≥ min niceLen maxLen
          · simp only [bne_iff_ne.mpr hbyte, ↓reduceIte, Nat.not_lt.mpr hle, hb]
          · simp only [bne_iff_ne.mpr hbyte, ↓reduceIte, Nat.not_lt.mpr hle, hb, ih]
      · -- bestLen ≥ maxLen → skip = false; countMatch ≤ maxLen ≤ bestLen, no update, early stop
        simp only [dif_neg hbl, Bool.false_eq_true, ↓reduceIte]
        have hle : lz77Greedy.countMatch data cand pos maxLen hcand hpm ≤ bestLen :=
          Nat.le_trans (lz77Greedy.countMatch_matches data cand pos maxLen hcand hpm).2
            (Nat.le_of_not_lt hbl)
        have hbmin : min niceLen maxLen ≤ bestLen :=
          Nat.le_trans (Nat.min_le_right _ _) (Nat.le_of_not_lt hbl)
        simp only [Nat.not_lt.mpr hle, ge_iff_le, hbmin, ↓reduceIte]
    · simp only [dif_neg hc]

/-- One runtime guard collapses the packed walk to the packed image of the
    reference walk. -/
theorem chainWalkGuardedPacked_eq (data : ByteArray) (prev : Array Nat)
    (windowSize pos maxLen niceLen : Nat) (hpm : pos + maxLen ≤ data.size)
    (cand fuel bestLen bestPos : Nat) :
    chainWalkGuardedPacked data prev windowSize pos maxLen niceLen hpm cand fuel bestLen bestPos =
      (lz77Chain.chainWalk data prev windowSize pos maxLen niceLen hpm cand fuel bestLen bestPos).2 * 512 +
        (lz77Chain.chainWalk data prev windowSize pos maxLen niceLen hpm cand fuel bestLen bestPos).1 := by
  unfold chainWalkGuardedPacked
  split
  · rw [chainWalkPacked_eq, chainWalkFast_eq]
  · rfl

/-! ## USize-native packed chain walk (Wave 7 P1b)

`chainWalkPackedU` runs `chainWalkPacked`'s per-position bookkeeping — fuel,
the best-length/best-position accumulator, and the `scan_end` prefilter's
index arithmetic — on unboxed `USize`, with the chain link `cand` left on the
`Nat` ring. `chainWalkPackedU_eq` is the lockstep equality: identical control
flow, every `USize` operation the faithful image of its `Nat` twin
(`toUSize_toNat_of_lt` round-trips, `uget_eq_getElem` for the prefilter reads),
so it holds whenever the buffer is `USize`-addressable and the accumulators
round-trip (the wrapper's runtime guard). -/

/-- The packed `USize` walk computes exactly the same `Nat` result as
    `chainWalkPacked`: same branch tree, each `USize` add/compare the image of
    the `Nat` one under the round-trip identities. -/
theorem chainWalkPackedU_eq (data : ByteArray) (prev : Array Nat)
    (windowSize pos maxLen niceLen : Nat) (hpm : pos + maxLen ≤ data.size)
    (hps : min chainWinSize data.size ≤ prev.size) (hsz : data.size < USize.size)
    (posU maxLenU cutoffU : USize) (hposU : posU.toNat = pos) (hmaxU : maxLenU.toNat = maxLen)
    (hcutU : cutoffU.toNat = min niceLen maxLen)
    (cand fuel bestLen bestPos : Nat)
    (hfuel : fuel < USize.size) (hbl : bestLen < USize.size) (hbp : bestPos < USize.size) :
    chainWalkPackedU data prev windowSize pos maxLen niceLen hpm hps hsz posU maxLenU cutoffU
        hposU hmaxU hcutU cand fuel.toUSize bestLen.toUSize bestPos.toUSize =
      chainWalkPacked data prev windowSize pos maxLen niceLen hpm hps cand fuel bestLen bestPos := by
  induction fuel generalizing cand bestLen bestPos hbl hbp with
  | zero =>
    rw [chainWalkPackedU, chainWalkPacked]
    have h0 : ((0 : Nat).toUSize) = 0 := by
      apply USize.toNat_inj.mp; rw [toUSize_toNat_of_lt (by omega), USize.toNat_zero]
    rw [if_pos h0, if_pos rfl, toUSize_toNat_of_lt hbp, toUSize_toNat_of_lt hbl]
  | succ k ih =>
    rw [chainWalkPackedU, chainWalkPacked]
    have hfk : (k + 1 : Nat).toUSize.toNat = k + 1 := toUSize_toNat_of_lt hfuel
    have hfne : ¬ ((k + 1 : Nat).toUSize = 0) := fun h => by
      rw [h, USize.toNat_zero] at hfk; omega
    have h1le : (1 : USize) ≤ (k + 1 : Nat).toUSize := by
      rw [USize.le_iff_toNat_le, USize.toNat_one, hfk]; omega
    have hsub : (k + 1 : Nat).toUSize - 1 = (k : Nat).toUSize := by
      apply USize.toNat_inj.mp
      rw [USize.toNat_sub_of_le _ _ h1le, USize.toNat_one, hfk, toUSize_toNat_of_lt (show k < USize.size by omega)]
      omega
    rw [if_neg hfne, if_neg (by omega : ¬ (k + 1 = 0))]
    by_cases hc : cand < pos ∧ pos - cand ≤ windowSize
    · rw [dif_pos hc, dif_pos hc]
      have hUS : USize.size = 2 ^ System.Platform.numBits := rfl
      have hcand : cand + maxLen ≤ data.size := by omega
      have hcandlt : cand < USize.size := by omega
      have hcU : cand.toUSize.toNat = cand := toUSize_toNat_of_lt hcandlt
      have hblU : bestLen.toUSize.toNat = bestLen := toUSize_toNat_of_lt hbl
      have hbpU : bestPos.toUSize.toNat = bestPos := toUSize_toNat_of_lt hbp
      simp only []
      -- The prefilter condition `bestLen < maxLen` is shared (USize compare = Nat compare).
      have hcond : (bestLen.toUSize < maxLenU) = (bestLen < maxLen) := by
        rw [eq_iff_iff, USize.lt_iff_toNat_lt, hblU, hmaxU]
      -- The cutoff comparison, shared for any `n < USize.size`.
      have hcut : ∀ n : Nat, n < USize.size → (n.toUSize ≥ cutoffU) = (n ≥ min niceLen maxLen) := by
        intro n hn
        rw [eq_iff_iff, ge_iff_le, ge_iff_le, USize.le_iff_toNat_le, hcutU, toUSize_toNat_of_lt hn]
      -- The shared `countMatch` continuation (reached when the prefilter does not skip).
      have hstep :
          (let ml := lz77Greedy.countMatch data cand pos maxLen hcand hpm
           let blU := if ml.toUSize > bestLen.toUSize then ml.toUSize else bestLen.toUSize
           let bpU := if ml.toUSize > bestLen.toUSize then cand.toUSize else bestPos.toUSize
           if blU ≥ cutoffU then bpU.toNat * 512 + blU.toNat
           else chainWalkPackedU data prev windowSize pos maxLen niceLen hpm hps hsz posU maxLenU cutoffU
             hposU hmaxU hcutU
             (prev[cand &&& 0x7FFF]'(by have h1 := winMask_lt cand; have h2 := Nat.and_le_left (n := cand) (m := 0x7FFF); simp only [chainWinSize] at h1 hps; omega))
             ((k + 1 : Nat).toUSize - 1) blU bpU) =
          (let ml := lz77Greedy.countMatch data cand pos maxLen hcand hpm
           let bl := if ml > bestLen then ml else bestLen
           let bp := if ml > bestLen then cand else bestPos
           if bl ≥ min niceLen maxLen then bp * 512 + bl
           else chainWalkPacked data prev windowSize pos maxLen niceLen hpm hps
             (prev[cand &&& 0x7FFF]'(by have := winMask_lt cand; have := Nat.and_le_left (n := cand) (m := 0x7FFF); omega))
             k bl bp) := by
        have hml_le : lz77Greedy.countMatch data cand pos maxLen hcand hpm ≤ maxLen :=
          (lz77Greedy.countMatch_matches data cand pos maxLen hcand hpm).2
        have hmllt : lz77Greedy.countMatch data cand pos maxLen hcand hpm < USize.size := by omega
        have hmlU : (lz77Greedy.countMatch data cand pos maxLen hcand hpm).toUSize.toNat
            = lz77Greedy.countMatch data cand pos maxLen hcand hpm := toUSize_toNat_of_lt hmllt
        have hmlcond : ((lz77Greedy.countMatch data cand pos maxLen hcand hpm).toUSize > bestLen.toUSize)
            = (lz77Greedy.countMatch data cand pos maxLen hcand hpm > bestLen) := by
          rw [eq_iff_iff, gt_iff_lt, gt_iff_lt, USize.lt_iff_toNat_lt, hblU, hmlU]
        simp only [hmlcond]
        by_cases hml : lz77Greedy.countMatch data cand pos maxLen hcand hpm > bestLen
        · simp only [hml, ↓reduceIte, hcut _ hmllt]
          by_cases hge : lz77Greedy.countMatch data cand pos maxLen hcand hpm ≥ min niceLen maxLen
          · simp only [hge, ↓reduceIte, hmlU, hcU]
          · simp only [hge, ↓reduceIte]; rw [hsub]; exact ih _ _ _ (by omega) hmllt hcandlt
        · simp only [hml, ↓reduceIte, hcut _ hbl]
          by_cases hge : bestLen ≥ min niceLen maxLen
          · simp only [hge, ↓reduceIte, hblU, hbpU]
          · simp only [hge, ↓reduceIte]; rw [hsub]; exact ih _ _ _ (by omega) hbl hbp
      -- Reduce the shared `skip` prefilter Bool on both sides.
      by_cases hlt : bestLen < maxLen
      · simp only [dif_pos (show bestLen.toUSize < maxLenU by rw [hcond]; exact hlt), dif_pos hlt,
          uget_eq_getElem]
        have e1 : (cand.toUSize + bestLen.toUSize).toNat = cand + bestLen := by
          rw [USize.toNat_add, hcU, hblU]; apply Nat.mod_eq_of_lt; omega
        have e2 : (posU + bestLen.toUSize).toNat = pos + bestLen := by
          rw [USize.toNat_add, hposU, hblU]; apply Nat.mod_eq_of_lt; omega
        simp only [e1, e2]
        by_cases hbyte : data[cand + bestLen]'(by omega) = data[pos + bestLen]'(by omega)
        · simp only [hbyte, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]; exact hstep
        · simp only [bne_iff_ne.mpr hbyte, ↓reduceIte, hcut _ hbl]
          by_cases hge : bestLen ≥ min niceLen maxLen
          · simp only [hge, ↓reduceIte, hblU, hbpU]
          · simp only [hge, ↓reduceIte]; rw [hsub]; exact ih _ _ _ (by omega) hbl hbp
      · simp only [dif_neg (show ¬ (bestLen.toUSize < maxLenU) by rw [hcond]; exact hlt), dif_neg hlt,
          Bool.false_eq_true, ↓reduceIte]
        exact hstep
    · rw [dif_neg hc, dif_neg hc, toUSize_toNat_of_lt hbp, toUSize_toNat_of_lt hbl]

/-- The runtime-guarded `USize` walk equals the runtime-guarded `Nat` walk
    (`chainWalkGuardedPacked`) unconditionally: when the addressability +
    accumulator-faithfulness check passes it is `chainWalkPackedU_eq`, and every
    other branch is literally `chainWalkGuardedPacked`'s branch. Callers can
    therefore substitute the `USize` walk with no change to any downstream
    contract — its result decodes with the existing `chainWalkGuardedPacked_mod`
    / `_div` lemmas after rewriting through this equation. -/
theorem chainWalkGuardedPackedU_eq (data : ByteArray) (prev : Array Nat)
    (windowSize pos maxLen niceLen : Nat) (hpm : pos + maxLen ≤ data.size)
    (cand fuel bestLen bestPos : Nat) :
    chainWalkGuardedPackedU data prev windowSize pos maxLen niceLen hpm cand fuel bestLen bestPos =
      chainWalkGuardedPacked data prev windowSize pos maxLen niceLen hpm cand fuel bestLen bestPos := by
  unfold chainWalkGuardedPackedU chainWalkGuardedPacked
  split
  · split
    · rename_i _ hg
      rw [chainWalkPackedU_eq]
      · rw [← hg.2.1]; exact USize.toNat_lt_two_pow_numBits _
      · rw [← hg.2.2.1]; exact USize.toNat_lt_two_pow_numBits _
      · rw [← hg.2.2.2]; exact USize.toNat_lt_two_pow_numBits _
    · rfl
  · rfl

/-- The reference walk's best length never exceeds `max bestLen maxLen`:
    every update records a `countMatch` result (`≤ maxLen`), and otherwise the
    seed is kept. Seed-general form (#2742) — the hash3 probe starts the walk
    at `bestLen = 3`. -/
theorem chainWalk_fst_le (data : ByteArray) (prev : Array Nat)
    (windowSize pos maxLen niceLen : Nat) (hpm : pos + maxLen ≤ data.size)
    (cand fuel bestLen bestPos : Nat) :
    (lz77Chain.chainWalk data prev windowSize pos maxLen niceLen hpm cand fuel bestLen bestPos).1 ≤
      max bestLen maxLen := by
  induction fuel generalizing cand bestLen bestPos with
  | zero => rw [lz77Chain.chainWalk]; simp only [↓reduceIte]; omega
  | succ k ih =>
    rw [lz77Chain.chainWalk, if_neg (by omega : ¬ (k + 1 = 0))]
    split
    · rename_i hc
      have hcand : cand + maxLen ≤ data.size := by omega
      have hcm := (lz77Greedy.countMatch_matches data cand pos maxLen hcand hpm).2
      by_cases hml : lz77Greedy.countMatch data cand pos maxLen hcand hpm > bestLen
      · simp only [hml, ↓reduceIte]
        split
        · dsimp only; omega
        · have h := ih (prev[cand &&& 0x7FFF]!)
            (lz77Greedy.countMatch data cand pos maxLen hcand hpm) cand
          simp only [Nat.add_sub_cancel] at *
          omega
      · simp only [hml, ↓reduceIte]
        split
        · dsimp only; omega
        · have h := ih (prev[cand &&& 0x7FFF]!) bestLen bestPos
          simp only [Nat.add_sub_cancel] at *
          omega
    · dsimp only; omega

/-- Decode the packed walk's best length: with `maxLen < 512` and a seed
    `< 512` the low bits are exactly the reference walk's `bestLen`. -/
theorem chainWalkGuardedPacked_mod (data : ByteArray) (prev : Array Nat)
    (windowSize pos maxLen niceLen : Nat) (hpm : pos + maxLen ≤ data.size)
    (cand fuel bestLen bestPos : Nat) (hml : maxLen ≤ 511) (hbl : bestLen ≤ 511) :
    chainWalkGuardedPacked data prev windowSize pos maxLen niceLen hpm cand fuel bestLen bestPos % 512 =
      (lz77Chain.chainWalk data prev windowSize pos maxLen niceLen hpm cand fuel bestLen bestPos).1 := by
  rw [chainWalkGuardedPacked_eq]
  have h := chainWalk_fst_le data prev windowSize pos maxLen niceLen hpm cand fuel bestLen bestPos
  omega

/-- Decode the packed walk's best position (the high bits). -/
theorem chainWalkGuardedPacked_div (data : ByteArray) (prev : Array Nat)
    (windowSize pos maxLen niceLen : Nat) (hpm : pos + maxLen ≤ data.size)
    (cand fuel bestLen bestPos : Nat) (hml : maxLen ≤ 511) (hbl : bestLen ≤ 511) :
    chainWalkGuardedPacked data prev windowSize pos maxLen niceLen hpm cand fuel bestLen bestPos / 512 =
      (lz77Chain.chainWalk data prev windowSize pos maxLen niceLen hpm cand fuel bestLen bestPos).2 := by
  rw [chainWalkGuardedPacked_eq]
  have h := chainWalk_fst_le data prev windowSize pos maxLen niceLen hpm cand fuel bestLen bestPos
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
private theorem mainLoop_eq_chain (data : ByteArray) (windowSize hashSize maxChain insertCap niceLen : Nat)
    (hashTable : Array Nat) (prev : Array Nat) (h3tab : Array Nat) (pos : Nat) (acc : Array LZ77Token) :
    lz77ChainIter.mainLoop data windowSize hashSize maxChain insertCap niceLen hashTable prev h3tab pos acc =
    acc ++ (lz77Chain.mainLoop data windowSize hashSize maxChain niceLen hashTable prev h3tab pos insertCap).toArray := by
  induction h : data.size - pos using Nat.strongRecOn generalizing pos acc hashTable prev h3tab with
  | _ n ih =>
    unfold lz77ChainIter.mainLoop lz77Chain.mainLoop
    simp only [chainWalkGuardedPacked_mod, chainWalkGuardedPacked_div, min258_le_511,
      mod512_le, updateHashesGuarded_eq]
    by_cases hlt : pos + 2 < data.size
    · simp only [hlt, ↓reduceDIte]
      split
      · split
        · rw [ih _ (by omega) _ _ _ _ _ rfl, List.toArray_cons,
            ← Array.append_assoc, Array.push_eq_append]
        · rw [ih _ (by omega) _ _ _ _ _ rfl, List.toArray_cons,
            ← Array.append_assoc, Array.push_eq_append]
      · rw [ih _ (by omega) _ _ _ _ _ rfl, List.toArray_cons,
          ← Array.append_assoc, Array.push_eq_append]
    · simp only [hlt, ↓reduceDIte]
      exact trailing_eq data pos acc

/-- `lz77ChainIter` produces exactly the same tokens as `lz77Chain`. -/
theorem lz77ChainIter_eq_lz77Chain (data : ByteArray) (maxChain windowSize insertCap niceLen : Nat) :
    lz77ChainIter data maxChain windowSize insertCap niceLen = lz77Chain data maxChain windowSize insertCap niceLen := by
  unfold lz77ChainIter lz77Chain
  split
  · rw [trailing_eq]; simp only [List.append_toArray, List.nil_append]
  · rw [mainLoop_eq_chain]; simp only [List.append_toArray, List.nil_append]

theorem lz77ChainIter_valid (data : ByteArray) (maxChain windowSize insertCap niceLen : Nat)
    (hw : windowSize > 0) :
    ValidDecomp data 0 (lz77ChainIter data maxChain windowSize insertCap niceLen).toList := by
  rw [lz77ChainIter_eq_lz77Chain]; exact lz77Chain_valid data maxChain windowSize insertCap niceLen hw

theorem lz77ChainIter_resolves (data : ByteArray) (maxChain windowSize insertCap niceLen : Nat)
    (hw : windowSize > 0) :
    Deflate.Spec.resolveLZ77 (tokensToSymbols (lz77ChainIter data maxChain windowSize insertCap niceLen)) [] =
      some data.data.toList := by
  rw [lz77ChainIter_eq_lz77Chain]; exact lz77Chain_resolves data maxChain windowSize insertCap niceLen hw

theorem lz77ChainIter_encodable (data : ByteArray) (maxChain windowSize insertCap niceLen : Nat)
    (hw : windowSize > 0) (hws : windowSize ≤ 32768) :
    ∀ t ∈ (lz77ChainIter data maxChain windowSize insertCap niceLen).toList,
      match t with
      | .literal _ => True
      | .reference len dist => 3 ≤ len ∧ len ≤ 258 ∧ 1 ≤ dist ∧ dist ≤ 32768 := by
  rw [lz77ChainIter_eq_lz77Chain]; exact lz77Chain_encodable data maxChain windowSize insertCap niceLen hw hws

/-- The chain matcher emits no tokens on empty input. -/
theorem lz77ChainIter_empty (data : ByteArray) (maxChain windowSize insertCap niceLen : Nat)
    (hzero : data.size = 0) : lz77ChainIter data maxChain windowSize insertCap niceLen = #[] := by
  rw [lz77ChainIter_eq_lz77Chain]
  simp only [lz77Chain, show data.size < 3 from by omega, ↓reduceIte]
  have htrail : lz77Greedy.trailing data 0 = [] := by
    unfold lz77Greedy.trailing
    simp only [show ¬(0 < data.size) from by omega, ↓reduceDIte]
  rw [htrail]

end Zip.Native.Deflate
