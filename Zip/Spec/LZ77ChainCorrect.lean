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

/-- The hash3-singleton probe's decoded seed is a real in-window match (or
    empty): exactly the initial-accumulator hypothesis `chainWalk_spec` takes at
    `bestLen := seed % 512`, `bestPos := seed / 512`. `probeWin ≤ windowSize`
    (the TOO_FAR cap) so an in-`probeWin` candidate is a fortiori in-`windowSize`;
    the two byte compares plus the `cand3 < pos` guard establish the length-3
    prefix match. The `h3tab` contents are opaque — only `cand3`'s bytes and the
    window matter, both re-verified here. -/
theorem hash3Probe_spec (data : ByteArray) (probeWin windowSize pos cand3 : Nat)
    (hlt : pos + 2 < data.size) (maxLen : Nat) (hml : 3 ≤ maxLen)
    (hpm : pos + maxLen ≤ data.size) (hpw : probeWin ≤ windowSize) :
    hash3Probe data probeWin pos cand3 hlt % 512 = 0 ∨
      (hash3Probe data probeWin pos cand3 hlt / 512 < pos ∧
        pos - hash3Probe data probeWin pos cand3 hlt / 512 ≤ windowSize ∧
        hash3Probe data probeWin pos cand3 hlt / 512 + maxLen ≤ data.size ∧
        (∀ i, i < hash3Probe data probeWin pos cand3 hlt % 512 →
          data[pos + i]! = data[hash3Probe data probeWin pos cand3 hlt / 512 + i]!) ∧
        hash3Probe data probeWin pos cand3 hlt % 512 ≤ maxLen) := by
  unfold hash3Probe
  split
  · rename_i hc
    split
    · rename_i hbytes
      simp only [Bool.and_eq_true, beq_iff_eq] at hbytes
      have hm : (cand3 * 512 + 3) % 512 = 3 := by omega
      have hd : (cand3 * 512 + 3) / 512 = cand3 := by omega
      rw [hm, hd]
      refine Or.inr ⟨hc.1, by omega, by omega, ?_, by omega⟩
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

/-- The gated split-tier seed `h3Seed` is a real in-window match (or empty): the
    `useH3 := false` seed is `0` (empty), and the `useH3 := true` seed is the
    hash3 probe result, covered by `hash3Probe_spec` under the TOO_FAR cap
    `min windowSize tooFar3 ≤ windowSize`. This is the sole hypothesis the seeded
    chain walk needs to return-and-emit the length-3 candidate as a valid
    reference (`chainWalk_spec` at `bestLen := seed % 512`). -/
theorem h3Seed_spec (useH3 : Bool) (data : ByteArray) (h3tab : Array Nat)
    (windowSize pos : Nat) (hlt : pos + 2 < data.size) (maxLen : Nat) (hml : 3 ≤ maxLen)
    (hpm : pos + maxLen ≤ data.size) :
    h3Seed useH3 data h3tab windowSize pos hlt % 512 = 0 ∨
      (h3Seed useH3 data h3tab windowSize pos hlt / 512 < pos ∧
        pos - h3Seed useH3 data h3tab windowSize pos hlt / 512 ≤ windowSize ∧
        h3Seed useH3 data h3tab windowSize pos hlt / 512 + maxLen ≤ data.size ∧
        (∀ i, i < h3Seed useH3 data h3tab windowSize pos hlt % 512 →
          data[pos + i]! = data[h3Seed useH3 data h3tab windowSize pos hlt / 512 + i]!) ∧
        h3Seed useH3 data h3tab windowSize pos hlt % 512 ≤ maxLen) := by
  unfold h3Seed
  split
  · exact hash3Probe_spec data (min windowSize tooFar3) windowSize pos
      (headProbeGuarded h3tab (hash3Single data pos hlt)) hlt maxLen hml hpm (Nat.min_le_left _ _)
  · exact Or.inl rfl

/-! ## Seeding the chain walk's best length (zlib `prev_length` probe seed)

The lazy lookahead probe at `pos+1` starts its chain walk with the current
`pos`-match length pre-loaded as the best length instead of `0` (zlib's
`deflate_slow` passes `prev_length`), so a candidate shorter than the current
match is never extended. `chainWalk_seed` proves this is *output-neutral* when the
seed is below the walk's own early-stop cutoff (`min niceLen maxLen`): the seeded
walk either agrees with the unseeded one exactly (when the unseeded walk finds a
strictly longer match) or returns the seed unchanged (when it does not — in which
case the unseeded walk's best is `≤` the seed, so the downstream lazy-accept test
rejects it either way). Proven on the reference pair walk; the packed/`USize`
twins inherit it through `chainWalkGuardedPacked_eq`. -/

/-- The chain walk's best length only grows: the returned length is at least the
    seed it started from. -/
theorem chainWalk_fst_mono (data : ByteArray) (prev : Array Nat)
    (windowSize pos maxLen niceLen : Nat) (hpm : pos + maxLen ≤ data.size)
    (cand fuel bestLen bestPos : Nat) :
    bestLen ≤ (lz77Chain.chainWalk data prev windowSize pos maxLen niceLen hpm cand fuel bestLen bestPos).1 := by
  induction fuel generalizing cand bestLen bestPos with
  | zero => rw [lz77Chain.chainWalk]; simp only [↓reduceIte, Nat.le_refl]
  | succ k ih =>
    rw [lz77Chain.chainWalk, if_neg (by omega : ¬ (k + 1 = 0))]
    by_cases hc : cand < pos ∧ pos - cand ≤ windowSize
    · have hcand : cand + maxLen ≤ data.size := by omega
      simp only [dif_pos hc, Nat.add_sub_cancel]
      by_cases hml : lz77Greedy.countMatch data cand pos maxLen hcand hpm > bestLen
      · simp only [hml, ↓reduceIte]
        split
        · omega
        · exact Nat.le_trans (Nat.le_of_lt hml) (ih (prev[cand &&& 0x7FFF]!) _ _)
      · simp only [hml, ↓reduceIte]
        split
        · exact Nat.le_refl _
        · exact ih (prev[cand &&& 0x7FFF]!) _ _
    · simp only [dif_neg hc]
      exact Nat.le_refl _

/-- Seeding the best length with `m` (below the walk's own cutoff) is
    output-neutral: from a seed `(m, s)` the walk either equals the walk from a
    smaller seed `(b, p)` with `b ≤ m` (whenever that walk finds a match strictly
    longer than `m`) or returns `(m, s)` unchanged (whenever it does not — then the
    smaller-seed walk's best length is `≤ m`). Generalised over both accumulators
    for the fuel induction. -/
theorem chainWalk_seed (data : ByteArray) (prev : Array Nat)
    (windowSize pos maxLen niceLen : Nat) (hpm : pos + maxLen ≤ data.size)
    (m : Nat) (hm : m < min niceLen maxLen) (cand fuel b p s : Nat) (hbm : b ≤ m) :
    (m < (lz77Chain.chainWalk data prev windowSize pos maxLen niceLen hpm cand fuel b p).1 →
        lz77Chain.chainWalk data prev windowSize pos maxLen niceLen hpm cand fuel m s =
          lz77Chain.chainWalk data prev windowSize pos maxLen niceLen hpm cand fuel b p) ∧
      ((lz77Chain.chainWalk data prev windowSize pos maxLen niceLen hpm cand fuel b p).1 ≤ m →
        lz77Chain.chainWalk data prev windowSize pos maxLen niceLen hpm cand fuel m s = (m, s)) := by
  induction fuel generalizing cand b p s hbm with
  | zero =>
    rw [lz77Chain.chainWalk, lz77Chain.chainWalk]
    simp only [↓reduceIte]
    exact ⟨fun h => absurd h (Nat.not_lt.mpr hbm), fun _ => trivial⟩
  | succ k ih =>
    rw [lz77Chain.chainWalk, lz77Chain.chainWalk, if_neg (by omega : ¬ (k + 1 = 0)),
      if_neg (by omega : ¬ (k + 1 = 0))]
    by_cases hc : cand < pos ∧ pos - cand ≤ windowSize
    · have hcand : cand + maxLen ≤ data.size := by omega
      simp only [dif_pos hc, Nat.add_sub_cancel]
      by_cases hmlm : lz77Greedy.countMatch data cand pos maxLen hcand hpm > m
      · -- `ml > m ≥ b`: both sides update to `(ml, cand)`, then run in lockstep.
        have hmlb : lz77Greedy.countMatch data cand pos maxLen hcand hpm > b := by omega
        simp only [hmlm, hmlb, ↓reduceIte]
        by_cases hstop : lz77Greedy.countMatch data cand pos maxLen hcand hpm ≥ min niceLen maxLen
        · simp only [hstop, ↓reduceIte]
          exact ⟨fun _ => trivial, fun h => absurd h (by omega)⟩
        · simp only [hstop, ↓reduceIte]
          -- Both recurse from `(ml, cand)`: literally the same call.
          refine ⟨fun _ => trivial, fun h => ?_⟩
          exfalso
          have hmono := chainWalk_fst_mono data prev windowSize pos maxLen niceLen hpm
            (prev[cand &&& 0x7FFF]!) k (lz77Greedy.countMatch data cand pos maxLen hcand hpm) cand
          omega
      · -- `ml ≤ m`: the seeded side never updates (stays `(m, s)`) and does not
        -- early-stop (`m < cutoff`); the unseeded side keeps `b' ≤ m`; recurse.
        have hSeed : ¬ (m ≥ min niceLen maxLen) := by omega
        simp only [hmlm, ↓reduceIte, hSeed]
        by_cases hmlb : lz77Greedy.countMatch data cand pos maxLen hcand hpm > b
        · simp only [hmlb, ↓reduceIte]
          have hstopU : ¬ (lz77Greedy.countMatch data cand pos maxLen hcand hpm ≥ min niceLen maxLen) := by omega
          simp only [hstopU, ↓reduceIte]
          exact ih (prev[cand &&& 0x7FFF]!) _ cand s (by omega)
        · simp only [hmlb, ↓reduceIte]
          have hstopU : ¬ (b ≥ min niceLen maxLen) := by omega
          simp only [hstopU, ↓reduceIte]
          exact ih (prev[cand &&& 0x7FFF]!) b p s hbm
    · rw [dif_neg hc, dif_neg hc]
      exact ⟨fun h => absurd h (Nat.not_lt.mpr hbm), fun _ => rfl⟩

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
    (hashTable : Array Nat) (prev : Array Nat) (pos insertCap : Nat) (hw : windowSize > 0) :
    ValidDecomp data pos
      (lz77Chain.mainLoop data windowSize hashSize maxChain niceLen hashTable prev pos insertCap) := by
  unfold lz77Chain.mainLoop
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
        · refine ValidDecomp.reference hge (by omega) (by omega) hle ?_ ?_
          · intro i hi
            rw [Nat.sub_sub_self (Nat.le_of_lt hQ.1)]
            exact hQ.2.2.2.1 i hi
          · exact lz77Chain_mainLoop_valid _ _ _ _ _ _ _ _ _ hw
      · exact .literal (by omega) (getElem!_pos data pos (by omega))
          (lz77Chain_mainLoop_valid _ _ _ _ _ _ _ _ _ hw)
    · exact .literal (by omega) (getElem!_pos data pos (by omega))
        (lz77Chain_mainLoop_valid _ _ _ _ _ _ _ _ _ hw)
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
  · simp only; exact lz77Chain_mainLoop_valid data windowSize 65536 maxChain niceLen _ _ 0 insertCap hw

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
    (hashTable : Array Nat) (prev : Array Nat) (pos insertCap : Nat) (hw : windowSize > 0) (hws : windowSize ≤ 32768) :
    ∀ t ∈ lz77Chain.mainLoop data windowSize hashSize maxChain niceLen hashTable prev pos insertCap, Enc t := by
  unfold lz77Chain.mainLoop
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
        · intro t ht
          cases ht with
          | head => exact ⟨hge, by omega, by omega, by omega⟩
          | tail _ h => exact lz77Chain_mainLoop_encodable _ _ _ _ _ _ _ _ _ hw hws t h
      · intro t ht
        cases ht with
        | head => trivial
        | tail _ h => exact lz77Chain_mainLoop_encodable _ _ _ _ _ _ _ _ _ hw hws t h
    · intro t ht
      cases ht with
      | head => trivial
      | tail _ h => exact lz77Chain_mainLoop_encodable _ _ _ _ _ _ _ _ _ hw hws t h
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
    exact lz77Chain_mainLoop_encodable data windowSize 65536 maxChain niceLen _ _ 0 insertCap hw hws t ht

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
      have hmllt : lz77Greedy.countMatch data cand pos maxLen hcand hpm < USize.size := by
        have := (lz77Greedy.countMatch_matches data cand pos maxLen hcand hpm).2
        omega
      have hcmU : countMatchUCore data cand.toUSize posU maxLenU hsz
          (by rw [hcU, hmaxU]; exact hcand) (by rw [hposU, hmaxU]; exact hpm) =
          (lz77Greedy.countMatch data cand pos maxLen hcand hpm).toUSize := by
        apply USize.toNat_inj.mp
        calc
          (countMatchUCore data cand.toUSize posU maxLenU hsz _ _).toNat =
              lz77Greedy.countMatch data cand pos maxLen hcand hpm :=
            countMatchUCore_eq data cand pos maxLen cand.toUSize posU maxLenU
              hcU hposU hmaxU hsz hcand hpm _ _
          _ = (lz77Greedy.countMatch data cand pos maxLen hcand hpm).toUSize.toNat :=
            (toUSize_toNat_of_lt hmllt).symm
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
        · simp only [hbyte, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
          rw [hcmU]
          exact hstep
        · simp only [bne_iff_ne.mpr hbyte, ↓reduceIte, hcut _ hbl]
          by_cases hge : bestLen ≥ min niceLen maxLen
          · simp only [hge, ↓reduceIte, hblU, hbpU]
          · simp only [hge, ↓reduceIte]; rw [hsub]; exact ih _ _ _ (by omega) hbl hbp
      · simp only [dif_neg (show ¬ (bestLen.toUSize < maxLenU) by rw [hcond]; exact hlt), dif_neg hlt,
          Bool.false_eq_true, ↓reduceIte]
        rw [hcmU]
        exact hstep
    · rw [dif_neg hc, dif_neg hc, toUSize_toNat_of_lt hbp, toUSize_toNat_of_lt hbl]

/-- Packing a bounded position and length in `USize` agrees with the `Nat`
    spelling when the packed value fits in one machine word. -/
theorem packMatchU_toNat (bestPosU bestLenU : USize) (dataSize : Nat)
    (hpos : bestPosU.toNat ≤ dataSize) (hlen : bestLenU.toNat ≤ 511)
    (hfit : dataSize * 512 + 511 < USize.size) :
    (bestPosU * 512 + bestLenU).toNat = bestPosU.toNat * 512 + bestLenU.toNat := by
  have h512 : (512 : USize).toNat = 512 := by
    rw [USize.toNat_ofNat]
    exact Nat.mod_eq_of_lt
      (Nat.lt_of_lt_of_le (show 512 < 2 ^ 32 by omega) USize.le_size)
  have hdata : dataSize * 512 < USize.size :=
    Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hfit
  have hmul : bestPosU.toNat * 512 < USize.size :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_right 512 hpos) hdata
  have hadd : bestPosU.toNat * 512 + bestLenU.toNat < USize.size :=
    Nat.lt_of_le_of_lt (Nat.add_le_add (Nat.mul_le_mul_right 512 hpos) hlen) hfit
  rw [USize.toNat_add, USize.toNat_mul, h512,
    Nat.mod_eq_of_lt hmul, Nat.mod_eq_of_lt hadd]

/-- The fully-`USize` measurement walk is the mixed `Nat`/`USize` walk whenever
    its scalar inputs and packed result are representable. -/
theorem chainWalkPackedUU_eq (data : ByteArray) (prev : Array Nat)
    (windowSize pos maxLen niceLen : Nat) (hpm : pos + maxLen ≤ data.size)
    (hps : min chainWinSize data.size ≤ prev.size) (hsz : data.size < USize.size)
    (windowSizeU posU maxLenU cutoffU candU fuelU bestLenU bestPosU : USize)
    (hwindowU : windowSizeU.toNat = windowSize) (hposU : posU.toNat = pos)
    (hmaxU : maxLenU.toNat = maxLen) (hcutU : cutoffU.toNat = min niceLen maxLen)
    (hpmU : posU.toNat + maxLenU.toNat ≤ data.size)
    (hmax511 : maxLen ≤ 511) (hblmax : bestLenU.toNat ≤ maxLen)
    (hbpdata : bestPosU.toNat ≤ data.size)
    (hfit : data.size * 512 + 511 < USize.size) :
    (chainWalkPackedUU data prev hps hsz windowSizeU posU maxLenU cutoffU
      candU fuelU bestLenU bestPosU hpmU).toNat =
      chainWalkPackedU data prev windowSize pos maxLen niceLen hpm hps hsz
        posU maxLenU cutoffU hposU hmaxU hcutU candU.toNat fuelU bestLenU bestPosU := by
  induction hn : fuelU.toNat using Nat.strongRecOn generalizing candU fuelU bestLenU bestPosU with
  | _ n ih =>
    rw [chainWalkPackedUU, chainWalkPackedU]
    by_cases hf : fuelU = 0
    · rw [if_pos hf, if_pos hf]
      exact packMatchU_toNat bestPosU bestLenU data.size hbpdata (by omega) hfit
    · rw [if_neg hf, if_neg hf]
      have hfuelPos : 0 < fuelU.toNat := by
        rcases Nat.eq_zero_or_pos fuelU.toNat with hz | hp
        · exact absurd (USize.toNat_inj.mp (by rw [hz, USize.toNat_zero])) hf
        · exact hp
      have hfuelLe : (1 : USize) ≤ fuelU := by
        rw [USize.le_iff_toNat_le, USize.toNat_one]
        omega
      have hfuelSub : (fuelU - 1).toNat = fuelU.toNat - 1 := by
        rw [USize.toNat_sub_of_le _ _ hfuelLe, USize.toNat_one]
      have hciff :
          (candU < posU ∧ posU - candU ≤ windowSizeU) ↔
            (candU.toNat < pos ∧ pos - candU.toNat ≤ windowSize) := by
        constructor
        · intro hc
          have hle : candU ≤ posU := USize.le_iff_toNat_le.mpr
            (Nat.le_of_lt (USize.lt_iff_toNat_lt.mp hc.1))
          constructor
          · rw [← hposU]
            exact USize.lt_iff_toNat_lt.mp hc.1
          · have hh := USize.le_iff_toNat_le.mp hc.2
            rw [USize.toNat_sub_of_le _ _ hle, hposU, hwindowU] at hh
            exact hh
        · intro hc
          have hlt : candU < posU := USize.lt_iff_toNat_lt.mpr (by simpa [hposU] using hc.1)
          constructor
          · exact hlt
          · rw [USize.le_iff_toNat_le, USize.toNat_sub_of_le _ _
                (USize.le_iff_toNat_le.mpr (Nat.le_of_lt (USize.lt_iff_toNat_lt.mp hlt))),
              hposU, hwindowU]
            exact hc.2
      by_cases hc : candU < posU ∧ posU - candU ≤ windowSizeU
      · rw [dif_pos hc, dif_pos (hciff.mp hc)]
        have hcandNat : candU.toNat + maxLen ≤ data.size := by
          have := hc.1
          rw [USize.lt_iff_toNat_lt, hposU] at this
          omega
        have hcandRound : candU.toNat.toUSize = candU := USize.ofNat_toNat
        simp only [hcandRound]
        have hcandData : candU.toNat < data.size := by
          have hcpos := USize.lt_iff_toNat_lt.mp hc.1
          rw [hposU] at hcpos
          omega
        have hidx : candU.toNat &&& 0x7FFF < prev.size := by
          have h1 := winMask_lt candU.toNat
          have h2 := Nat.and_le_left (n := candU.toNat) (m := 0x7FFF)
          exact Nat.lt_of_lt_of_le
            (Nat.lt_min.mpr ⟨h1, Nat.lt_of_le_of_lt h2 hcandData⟩) hps
        let next := prev[candU.toNat &&& 0x7FFF]'hidx
        let nextU := next.toUSize
        have hcont (blU bpU : USize) (hblm : blU.toNat ≤ maxLen)
            (hbpd : bpU.toNat ≤ data.size) :
            (if blU ≥ cutoffU then bpU * 512 + blU
              else if hnext : nextU.toNat = next then
                chainWalkPackedUU data prev hps hsz windowSizeU posU maxLenU cutoffU
                  nextU (fuelU - 1) blU bpU hpmU
              else bpU * 512 + blU).toNat =
            (if blU ≥ cutoffU then bpU.toNat * 512 + blU.toNat
              else chainWalkPackedU data prev windowSize pos maxLen niceLen hpm hps hsz
                posU maxLenU cutoffU hposU hmaxU hcutU next (fuelU - 1) blU bpU) := by
          have hpack : (bpU * 512 + blU).toNat = bpU.toNat * 512 + blU.toNat :=
            packMatchU_toNat bpU blU data.size hbpd (by omega) hfit
          by_cases hge : blU ≥ cutoffU
          · simp only [hge, ↓reduceIte, hpack]
          · simp only [hge, ↓reduceIte]
            by_cases hnext : nextU.toNat = next
            · simp only [hnext, ↓reduceDIte]
              simpa only [hnext] using
                ih (fuelU - 1).toNat (by rw [hfuelSub, hn]; omega)
                  nextU (fuelU - 1) blU bpU hblm hbpd rfl
            · simp only [hnext, ↓reduceDIte, hpack]
              have hnextge : pos ≤ next := by
                apply Nat.le_of_not_lt
                intro hnp
                have hnlt : next < USize.size := by
                  have hpSize : pos < USize.size := by
                    rw [← hposU]
                    exact USize.toNat_lt_two_pow_numBits posU
                  omega
                exact hnext (toUSize_toNat_of_lt hnlt)
              rw [chainWalkPackedU]
              by_cases hf' : fuelU - 1 = 0
              · rw [if_pos hf']
              · rw [if_neg hf', dif_neg (show ¬ (next < pos ∧ pos - next ≤ windowSize) by omega)]
        have hmlLe :
            (countMatchUCore data candU posU maxLenU hsz
              (by rw [hmaxU]; exact hcandNat) hpmU).toNat ≤ maxLen := by
          rw [countMatchUCore_eq data candU.toNat pos maxLen candU posU maxLenU
            rfl hposU hmaxU hsz hcandNat hpm _ _]
          exact (lz77Greedy.countMatch_matches data candU.toNat pos maxLen hcandNat hpm).2
        have hterminal (blU bpU : USize) (hblm : blU.toNat ≤ maxLen)
            (hbpd : bpU.toNat ≤ data.size) (hone : fuelU = 1) :
            (bpU * 512 + blU).toNat =
            (if blU ≥ cutoffU then bpU.toNat * 512 + blU.toNat
              else chainWalkPackedU data prev windowSize pos maxLen niceLen hpm hps hsz
                posU maxLenU cutoffU hposU hmaxU hcutU next (fuelU - 1) blU bpU) := by
          have hpack : (bpU * 512 + blU).toNat = bpU.toNat * 512 + blU.toNat :=
            packMatchU_toNat bpU blU data.size hbpd (by omega) hfit
          by_cases hge : blU ≥ cutoffU
          · simp only [hge, ↓reduceIte, hpack]
          · simp only [hge, ↓reduceIte]
            have hfzero : fuelU - 1 = 0 := by simp [hone]
            rw [chainWalkPackedU, if_pos hfzero]
            exact hpack
        -- Once the candidate's round trip is collapsed, both walks have the
        -- same prefilter and match computation; only their continuation differs.
        by_cases hskip :
            (if hbl : bestLenU < maxLenU then
              data.uget (candU + bestLenU) (by
                have him := USize.lt_iff_toNat_lt.mp hbl
                have e : (candU + bestLenU).toNat = candU.toNat + bestLenU.toNat := by
                  rw [USize.toNat_add]
                  apply Nat.mod_eq_of_lt
                  exact Nat.lt_trans (by omega) hsz
                omega) !=
              data.uget (posU + bestLenU) (by
                have him := USize.lt_iff_toNat_lt.mp hbl
                have e : (posU + bestLenU).toNat = posU.toNat + bestLenU.toNat := by
                  rw [USize.toNat_add]
                  apply Nat.mod_eq_of_lt
                  exact Nat.lt_trans (by omega) hsz
                omega)
            else false) = true
        · rw [if_pos hskip, if_pos hskip, if_pos hskip]
          by_cases hone : fuelU = 1
          · rw [if_pos hone]
            exact hterminal bestLenU bestPosU hblmax hbpdata hone
          · rw [if_neg hone]
            exact hcont bestLenU bestPosU hblmax hbpdata
        · rw [if_neg hskip, if_neg hskip, if_neg hskip]
          by_cases hml : countMatchUCore data candU posU maxLenU hsz
              (by rw [hmaxU]; exact hcandNat) hpmU > bestLenU
          · simp only [hml, ↓reduceIte]
            have hcandLe : candU.toNat ≤ data.size := by
              have hcpos := USize.lt_iff_toNat_lt.mp hc.1
              rw [hposU] at hcpos
              omega
            by_cases hone : fuelU = 1
            · rw [if_pos hone]
              exact hterminal (countMatchUCore data candU posU maxLenU hsz
                (by rw [hmaxU]; exact hcandNat) hpmU) candU hmlLe hcandLe hone
            · rw [if_neg hone]
              exact hcont (countMatchUCore data candU posU maxLenU hsz
                (by rw [hmaxU]; exact hcandNat) hpmU) candU hmlLe hcandLe
          · simp only [hml, ↓reduceIte]
            by_cases hone : fuelU = 1
            · rw [if_pos hone]
              exact hterminal bestLenU bestPosU hblmax hbpdata hone
            · rw [if_neg hone]
              exact hcont bestLenU bestPosU hblmax hbpdata
      · have hcNat : ¬(candU.toNat < pos ∧ pos - candU.toNat ≤ windowSize) :=
          fun h => hc (hciff.mpr h)
        simp only [dif_neg hc, dif_neg hcNat]
        exact packMatchU_toNat bestPosU bestLenU data.size hbpdata (by omega) hfit

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

/-- A `USize` value strictly below the all-ones word shifted right by nine
    leaves enough headroom to append a nine-bit match length. -/
theorem packFit_of_lt_maxShift (n : Nat) (hrt : n.toUSize.toNat = n)
    (h : n.toUSize < ((~~~(0 : USize)) >>> 9)) :
    n * 512 + 511 < USize.size := by
  have hh := USize.lt_iff_toNat_lt.mp h
  rw [hrt] at hh
  rcases System.Platform.numBits_eq with hb | hb <;>
    simp [USize.toNat_shiftRight, USize.size, hb, Nat.shiftRight_eq_div_pow] at hh ⊢ <;>
    omega

/-- On its checked branch, the native-word result is the exact packed result
    of the existing guarded walk. -/
theorem chainWalkPackedUUChecked_toNat (data : ByteArray) (prev : Array Nat)
    (windowSize pos maxLen niceLen : Nat) (hpm : pos + maxLen ≤ data.size)
    (cand fuel : Nat) (hg : chainWalkPackedUUSafe data prev windowSize maxLen cand fuel) :
    (chainWalkPackedUUChecked data prev windowSize pos maxLen niceLen hpm cand fuel hg).toNat =
      chainWalkGuardedPackedU data prev windowSize pos maxLen niceLen hpm cand fuel 0 0 := by
  have hsz : data.size < USize.size := by
    rw [← hg.2.1]
    exact USize.toNat_lt_two_pow_numBits _
  have hposlt : pos < USize.size := by omega
  have hmaxlt : maxLen < USize.size := by omega
  have hcutlt : min niceLen maxLen < USize.size := by omega
  have heq := chainWalkPackedUU_eq data prev windowSize pos maxLen niceLen hpm hg.1 hsz
    windowSize.toUSize pos.toUSize maxLen.toUSize (min niceLen maxLen).toUSize
    cand.toUSize fuel.toUSize 0 0 hg.2.2.1
    (toUSize_toNat_of_lt hposlt) (toUSize_toNat_of_lt hmaxlt)
    (toUSize_toNat_of_lt hcutlt)
    (by
      rw [toUSize_toNat_of_lt hposlt, toUSize_toNat_of_lt hmaxlt]
      exact hpm)
    hg.2.2.2.2.2.1 (by rw [USize.toNat_zero]; omega)
    (by rw [USize.toNat_zero]; omega)
    (packFit_of_lt_maxShift data.size hg.2.1 hg.2.2.2.2.2.2)
  unfold chainWalkPackedUUChecked chainWalkGuardedPackedU
  have hold : data.size.toUSize.toNat = data.size ∧ fuel.toUSize.toNat = fuel ∧
      (0 : Nat).toUSize.toNat = 0 ∧ (0 : Nat).toUSize.toNat = 0 :=
    ⟨hg.2.1, hg.2.2.2.2.1, rfl, rfl⟩
  rw [dif_pos hg.1, dif_pos hold]
  simpa only [hg.2.2.2.1, show ((0 : Nat).toUSize) = 0 from rfl] using heq

/-- Low nine bits of the checked word decode to the old packed walk's length. -/
theorem chainWalkPackedUUChecked_low (data : ByteArray) (prev : Array Nat)
    (windowSize pos maxLen niceLen : Nat) (hpm : pos + maxLen ≤ data.size)
    (cand fuel : Nat) (hg : chainWalkPackedUUSafe data prev windowSize maxLen cand fuel) :
    (chainWalkPackedUUChecked data prev windowSize pos maxLen niceLen hpm cand fuel hg &&&
        0x1FF).toNat =
      chainWalkGuardedPackedU data prev windowSize pos maxLen niceLen hpm cand fuel 0 0 % 512 := by
  rw [USize.toNat_and,
    USize.toNat_ofNat_of_lt (Nat.lt_of_lt_of_le (show 511 < 2 ^ 32 by omega) USize.le_size),
    show 511 = 2 ^ 9 - 1 by omega, Nat.and_two_pow_sub_one_eq_mod,
    show 2 ^ 9 = 512 by omega, chainWalkPackedUUChecked_toNat]

/-- High bits of the checked word decode to the old packed walk's position. -/
theorem chainWalkPackedUUChecked_high (data : ByteArray) (prev : Array Nat)
    (windowSize pos maxLen niceLen : Nat) (hpm : pos + maxLen ≤ data.size)
    (cand fuel : Nat) (hg : chainWalkPackedUUSafe data prev windowSize maxLen cand fuel) :
    (chainWalkPackedUUChecked data prev windowSize pos maxLen niceLen hpm cand fuel hg >>> 9).toNat =
      chainWalkGuardedPackedU data prev windowSize pos maxLen niceLen hpm cand fuel 0 0 / 512 := by
  rw [USize.toNat_shiftRight,
    USize.toNat_ofNat_of_lt (Nat.lt_of_lt_of_le (show 9 < 2 ^ 32 by omega) USize.le_size),
    Nat.mod_eq_of_lt (show 9 < System.Platform.numBits by
      exact Nat.lt_of_lt_of_le (by omega) System.Platform.le_numBits),
    Nat.shiftRight_eq_div_pow, show 2 ^ 9 = 512 by omega,
    chainWalkPackedUUChecked_toNat]

/-- From a zero-initialised best length, the reference walk's best length
    never exceeds `maxLen` (specialisation of `chainWalk_spec`). -/
theorem chainWalk_fst_le (data : ByteArray) (prev : Array Nat)
    (windowSize pos maxLen niceLen : Nat) (hpm : pos + maxLen ≤ data.size) (cand fuel : Nat) :
    (lz77Chain.chainWalk data prev windowSize pos maxLen niceLen hpm cand fuel 0 0).1 ≤ maxLen := by
  obtain h0 | hQ := chainWalk_spec data prev windowSize pos maxLen niceLen hpm cand fuel 0 0 (Or.inl rfl)
  · omega
  · exact hQ.2.2.2.2

/-- Decode the packed walk's best length: with `maxLen < 512` the low bits are
    exactly the reference walk's `bestLen`. -/
theorem chainWalkGuardedPacked_mod (data : ByteArray) (prev : Array Nat)
    (windowSize pos maxLen niceLen : Nat) (hpm : pos + maxLen ≤ data.size) (cand fuel : Nat)
    (hml : maxLen ≤ 511) :
    chainWalkGuardedPacked data prev windowSize pos maxLen niceLen hpm cand fuel 0 0 % 512 =
      (lz77Chain.chainWalk data prev windowSize pos maxLen niceLen hpm cand fuel 0 0).1 := by
  rw [chainWalkGuardedPacked_eq]
  have h := chainWalk_fst_le data prev windowSize pos maxLen niceLen hpm cand fuel
  omega

/-- Decode the packed walk's best position (the high bits). -/
theorem chainWalkGuardedPacked_div (data : ByteArray) (prev : Array Nat)
    (windowSize pos maxLen niceLen : Nat) (hpm : pos + maxLen ≤ data.size) (cand fuel : Nat)
    (hml : maxLen ≤ 511) :
    chainWalkGuardedPacked data prev windowSize pos maxLen niceLen hpm cand fuel 0 0 / 512 =
      (lz77Chain.chainWalk data prev windowSize pos maxLen niceLen hpm cand fuel 0 0).2 := by
  rw [chainWalkGuardedPacked_eq]
  have h := chainWalk_fst_le data prev windowSize pos maxLen niceLen hpm cand fuel
  omega

/-- Every matcher call site clamps `maxLen` to `min 258 _`; this discharges
    the `maxLen ≤ 511` side condition when `simp` applies the decode lemmas. -/
theorem min258_le_511 (x : Nat) : min 258 x ≤ 511 := by omega

/-- Seed-general form of `chainWalk_fst_le`: the walk result never exceeds
    `maxLen` provided the *initial* best length does (candidate matches are
    `countMatch`-bounded by `maxLen`, and a seed already `≤ maxLen` cannot push
    it over). Needed so the split tier's non-zero hash3 seed still decodes with
    the mod/div lemmas below. -/
theorem chainWalk_fst_le' (data : ByteArray) (prev : Array Nat)
    (windowSize pos maxLen niceLen : Nat) (hpm : pos + maxLen ≤ data.size)
    (cand fuel bestLen bestPos : Nat) (hbl : bestLen ≤ maxLen) :
    (lz77Chain.chainWalk data prev windowSize pos maxLen niceLen hpm cand fuel bestLen bestPos).1 ≤ maxLen := by
  induction fuel generalizing cand bestLen bestPos hbl with
  | zero => rw [lz77Chain.chainWalk]; exact hbl
  | succ k ih =>
    rw [lz77Chain.chainWalk, if_neg (by omega : ¬ (k + 1 = 0))]
    split
    · rename_i hc
      have hcand : cand + maxLen ≤ data.size := by omega
      have hcm := (lz77Greedy.countMatch_matches data cand pos maxLen hcand hpm).2
      by_cases hml : lz77Greedy.countMatch data cand pos maxLen hcand hpm > bestLen
      · simp only [hml, ↓reduceIte]
        split
        · exact hcm
        · exact ih _ _ _ hcm
      · simp only [hml, ↓reduceIte]
        split
        · exact hbl
        · exact ih _ _ _ hbl
    · exact hbl

/-- Seed-general `chainWalkGuardedPacked_mod`: decode the low bits for *any*
    initial best length `≤ maxLen` (not just the `0 0` seed). -/
theorem chainWalkGuardedPacked_mod' (data : ByteArray) (prev : Array Nat)
    (windowSize pos maxLen niceLen : Nat) (hpm : pos + maxLen ≤ data.size) (cand fuel bestLen bestPos : Nat)
    (hml : maxLen ≤ 511) (hbl : bestLen ≤ maxLen) :
    chainWalkGuardedPacked data prev windowSize pos maxLen niceLen hpm cand fuel bestLen bestPos % 512 =
      (lz77Chain.chainWalk data prev windowSize pos maxLen niceLen hpm cand fuel bestLen bestPos).1 := by
  rw [chainWalkGuardedPacked_eq]
  have h := chainWalk_fst_le' data prev windowSize pos maxLen niceLen hpm cand fuel bestLen bestPos hbl
  omega

/-- Seed-general `chainWalkGuardedPacked_div`: decode the high bits for *any*
    initial best length `≤ maxLen`. -/
theorem chainWalkGuardedPacked_div' (data : ByteArray) (prev : Array Nat)
    (windowSize pos maxLen niceLen : Nat) (hpm : pos + maxLen ≤ data.size) (cand fuel bestLen bestPos : Nat)
    (hml : maxLen ≤ 511) (hbl : bestLen ≤ maxLen) :
    chainWalkGuardedPacked data prev windowSize pos maxLen niceLen hpm cand fuel bestLen bestPos / 512 =
      (lz77Chain.chainWalk data prev windowSize pos maxLen niceLen hpm cand fuel bestLen bestPos).2 := by
  rw [chainWalkGuardedPacked_eq]
  have h := chainWalk_fst_le' data prev windowSize pos maxLen niceLen hpm cand fuel bestLen bestPos hbl
  omega

/-- Seeding lemma transported to the packed `USize` walk the matcher calls
    (`chainWalkGuardedPackedU`): for a seed `m` below the walk's cutoff, the
    `m`-seeded walk equals the `0`-seeded one when the latter's best length
    exceeds `m`, and returns the raw value `m` (best position `0`) otherwise.
    Proven by decoding both packed results back to `lz77Chain.chainWalk` pairs
    (`chainWalkGuardedPacked_eq`) and applying `chainWalk_seed`. -/
theorem chainWalkGuardedPackedU_seed (data : ByteArray) (prev : Array Nat)
    (windowSize pos maxLen niceLen : Nat) (hpm : pos + maxLen ≤ data.size)
    (hml511 : maxLen ≤ 511) (m : Nat) (hm : m < min niceLen maxLen) (cand fuel : Nat) :
    (m < chainWalkGuardedPackedU data prev windowSize pos maxLen niceLen hpm cand fuel 0 0 % 512 →
        chainWalkGuardedPackedU data prev windowSize pos maxLen niceLen hpm cand fuel m 0 =
          chainWalkGuardedPackedU data prev windowSize pos maxLen niceLen hpm cand fuel 0 0) ∧
      (chainWalkGuardedPackedU data prev windowSize pos maxLen niceLen hpm cand fuel 0 0 % 512 ≤ m →
        chainWalkGuardedPackedU data prev windowSize pos maxLen niceLen hpm cand fuel m 0 = m) := by
  simp only [chainWalkGuardedPackedU_eq, chainWalkGuardedPacked_eq]
  have hU1 : (lz77Chain.chainWalk data prev windowSize pos maxLen niceLen hpm cand fuel 0 0).1 ≤ maxLen :=
    chainWalk_fst_le data prev windowSize pos maxLen niceLen hpm cand fuel
  obtain ⟨hEq, hLe⟩ := chainWalk_seed data prev windowSize pos maxLen niceLen hpm m hm cand fuel 0 0 0 (Nat.zero_le m)
  have hmod : ((lz77Chain.chainWalk data prev windowSize pos maxLen niceLen hpm cand fuel 0 0).2 * 512 +
      (lz77Chain.chainWalk data prev windowSize pos maxLen niceLen hpm cand fuel 0 0).1) % 512 =
      (lz77Chain.chainWalk data prev windowSize pos maxLen niceLen hpm cand fuel 0 0).1 := by omega
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [hmod] at h; rw [hEq h]
  · rw [hmod] at h; rw [hLe h]; simp

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
    (hashTable : Array Nat) (prev : Array Nat) (pos : Nat) (acc : Array LZ77Token) :
    lz77ChainIter.mainLoop data windowSize hashSize maxChain insertCap niceLen hashTable prev pos acc =
    acc ++ (lz77Chain.mainLoop data windowSize hashSize maxChain niceLen hashTable prev pos insertCap).toArray := by
  induction h : data.size - pos using Nat.strongRecOn generalizing pos acc hashTable prev with
  | _ n ih =>
    unfold lz77ChainIter.mainLoop lz77Chain.mainLoop
    simp only [chainWalkGuardedPacked_mod, chainWalkGuardedPacked_div, min258_le_511,
      updateHashesGuarded_eq]
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
