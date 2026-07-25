import Zip.Native.DeflateL5
import Zip.Spec.LZ77ChainCorrect
import Zip.Spec.LZ77MergedCorrect

/-!
Correctness of the isolated large-input level-5 matcher.

Keeping these theorems out of the production matcher dependency chain lets
`Zip.Native.Deflate` and `Zip.Native.DeflateParse` retain their established
native object layout.
-/

namespace Zip.Native.Deflate

private theorem usize_one_ne_zero : (1 : USize) ≠ 0 := by
  intro h
  have h' := congrArg USize.toNat h
  simp at h'

private theorem usize_sub_one_ne_zero {u : USize} (h0 : u ≠ 0) (h1 : u ≠ 1) :
    u - 1 ≠ 0 := by
  have hn0 : u.toNat ≠ 0 := by
    intro h
    apply h0
    exact USize.toNat_inj.mp (by rw [h, USize.toNat_zero])
  have hn1 : u.toNat ≠ 1 := by
    intro h
    apply h1
    exact USize.toNat_inj.mp (by rw [h, USize.toNat_one])
  have htwo : 2 ≤ u.toNat := by omega
  have hle : (1 : USize) ≤ u := by
    rw [USize.le_iff_toNat_le, USize.toNat_one]
    omega
  have hsub : (u - 1).toNat = u.toNat - 1 := by
    rw [USize.toNat_sub_of_le _ _ hle, USize.toNat_one]
  intro h
  have hz := congrArg USize.toNat h
  rw [hsub, USize.toNat_zero] at hz
  omega

private theorem usize_not_le_of_lt {a b : USize} (h : a < b) : ¬b ≤ a := by
  intro hle
  have hlt' := USize.lt_iff_toNat_lt.mp h
  have hle' := USize.le_iff_toNat_le.mp hle
  omega

private theorem usize_roundtrip_contra {n : Nat}
    (hmod : n % 2 ^ System.Platform.numBits = n)
    (hne : ¬n.toUSize.toNat = n) : False := by
  apply hne
  simpa [Nat.toUSize] using hmod

private theorem usize_roundtrip_contra_of_eq {n m : Nat}
    (hmod : m % 2 ^ System.Platform.numBits = m)
    (hne : ¬n.toUSize.toNat = n) (hnm : n = m) : False := by
  subst m
  exact usize_roundtrip_contra hmod hne

private theorem usize_window_contra {cand pos window : USize}
    (hvalid : cand < pos ∧ pos - cand ≤ window)
    (hout : cand < pos → window < pos - cand) : False :=
  usize_not_le_of_lt (hout hvalid.1) hvalid.2

private theorem chainWalkPackedUU_invalid (data : ByteArray) (prev : Array Nat)
    (hps : min chainWinSize data.size ≤ prev.size) (hsz : data.size < USize.size)
    (windowSizeU posU maxLenU cutoffU candU fuelU bestLenU bestPosU : USize)
    (hpm : posU.toNat + maxLenU.toNat ≤ data.size)
    (hc : ¬(candU < posU ∧ posU - candU ≤ windowSizeU)) :
    chainWalkPackedUU data prev hps hsz windowSizeU posU maxLenU cutoffU
        candU fuelU bestLenU bestPosU hpm =
      bestPosU * 512 + bestLenU := by
  rw [chainWalkPackedUU]
  by_cases hf : fuelU = 0
  · simp [hf]
  · simp [hf, hc]

set_option maxHeartbeats 1000000 in
/-- The two-candidate native loop is exactly two unfoldings of the established
    one-candidate loop. -/
theorem chainWalkPackedUU2_eq (data : ByteArray) (prev : Array Nat)
    (hps : min chainWinSize data.size ≤ prev.size) (hsz : data.size < USize.size)
    (windowSizeU posU maxLenU cutoffU candU fuelU bestLenU bestPosU : USize)
    (hpm : posU.toNat + maxLenU.toNat ≤ data.size) :
    chainWalkPackedUU2 data prev hps hsz windowSizeU posU maxLenU cutoffU
        candU fuelU bestLenU bestPosU hpm =
      chainWalkPackedUU data prev hps hsz windowSizeU posU maxLenU cutoffU
        candU fuelU bestLenU bestPosU hpm := by
  fun_induction chainWalkPackedUU2 data prev hps hsz windowSizeU posU maxLenU
      cutoffU candU fuelU bestLenU bestPosU hpm <;>
    rw [chainWalkPackedUU] <;>
    simp_all (config := { zetaDelta := true })
      [usize_one_ne_zero, usize_not_le_of_lt, chainWalkPackedUU_invalid] <;>
    try (conv => rhs; rw [chainWalkPackedUU]) <;>
    simp_all (config := { zetaDelta := true })
      [usize_one_ne_zero, usize_sub_one_ne_zero, usize_not_le_of_lt]
  all_goals
    intros
    first
    | exfalso
      refine usize_roundtrip_contra_of_eq (by assumption) (by assumption) ?_
      simp_all
    | exfalso
      exact usize_window_contra (by assumption) (by assumption)

/-- The seeded checked entry is the existing guarded packed walk. -/
theorem chainWalkPackedUUSeededChecked_toNat (data : ByteArray) (prev : Array Nat)
    (windowSize pos maxLen niceLen : Nat) (hpm : pos + maxLen ≤ data.size)
    (cand fuel bestLen bestPos : Nat)
    (hg : chainWalkPackedUUSeededSafe data prev windowSize maxLen cand fuel bestLen bestPos) :
    (chainWalkPackedUUSeededChecked data prev windowSize pos maxLen niceLen hpm
      cand fuel bestLen bestPos hg).toNat =
      chainWalkGuardedPackedU data prev windowSize pos maxLen niceLen hpm
        cand fuel bestLen bestPos := by
  have hsz : data.size < USize.size := by
    rw [← hg.1.2.1]
    exact USize.toNat_lt_two_pow_numBits _
  have hposlt : pos < USize.size := by omega
  have hmaxlt : maxLen < USize.size := by omega
  have hcutlt : min niceLen maxLen < USize.size := by omega
  have heq := chainWalkPackedUU_eq data prev windowSize pos maxLen niceLen hpm hg.1.1 hsz
    windowSize.toUSize pos.toUSize maxLen.toUSize (min niceLen maxLen).toUSize
    cand.toUSize fuel.toUSize bestLen.toUSize bestPos.toUSize hg.1.2.2.1
    (toUSize_toNat_of_lt hposlt) (toUSize_toNat_of_lt hmaxlt)
    (toUSize_toNat_of_lt hcutlt)
    (by
      rw [toUSize_toNat_of_lt hposlt, toUSize_toNat_of_lt hmaxlt]
      exact hpm)
    hg.1.2.2.2.2.2.1
    (by rw [hg.2.1]; exact hg.2.2.2.1)
    (by rw [hg.2.2.1]; exact hg.2.2.2.2)
    (packFit_of_lt_maxShift data.size hg.1.2.1 hg.1.2.2.2.2.2.2)
  unfold chainWalkPackedUUSeededChecked chainWalkGuardedPackedU
  have hold : data.size.toUSize.toNat = data.size ∧ fuel.toUSize.toNat = fuel ∧
      bestLen.toUSize.toNat = bestLen ∧ bestPos.toUSize.toNat = bestPos :=
    ⟨hg.1.2.1, hg.1.2.2.2.2.1, hg.2.1, hg.2.2.1⟩
  rw [dif_pos hg.1.1, dif_pos hold]
  rw [chainWalkPackedUU2_eq]
  simpa only [hg.1.2.2.2.1, hg.1.2.2.2.2.1, hg.2.1, hg.2.2.1] using heq

/-- The fully-native-word guarded wrapper is observationally identical to the
    existing mixed-`Nat`/`USize` guarded walk. -/
theorem chainWalkGuardedPackedUU_eq (data : ByteArray) (prev : Array Nat)
    (windowSize pos maxLen niceLen : Nat) (hpm : pos + maxLen ≤ data.size)
    (cand fuel bestLen bestPos : Nat) :
    chainWalkGuardedPackedUU data prev windowSize pos maxLen niceLen hpm
      cand fuel bestLen bestPos =
      chainWalkGuardedPackedU data prev windowSize pos maxLen niceLen hpm
        cand fuel bestLen bestPos := by
  unfold chainWalkGuardedPackedUU
  split
  · exact chainWalkPackedUUSeededChecked_toNat data prev windowSize pos maxLen niceLen
      hpm cand fuel bestLen bestPos _
  · rfl

/-! The large-input L5 policy has neither the H3 side table nor rolling
    multi-deferral. Its specialized loop is therefore just the fresh-position
    arm of the general merged loop. -/
set_option maxHeartbeats 2000000 in
private theorem noH3SingleLoop_eq (data : ByteArray)
    (windowSize hashSize prevSize maxChain insertCap goodMatch niceLen lazyDepth
      lazy2Steps : Nat) (hsteps : lazy2Steps ≤ 1)
    (c h3tab : Array Nat) (pos : Nat) (acc : TokenArray) :
    lz77LazyMergedLoopNoH3Single data windowSize hashSize prevSize maxChain
        insertCap goodMatch niceLen lazyDepth c pos acc =
      lz77LazyMergedLoop data windowSize hashSize prevSize maxChain insertCap
        goodMatch niceLen lazyDepth lazy2Steps false c h3tab pos 0 0 0 acc := by
  induction hn : data.size - pos using Nat.strongRecOn
      generalizing pos acc c h3tab with
  | _ n ih =>
    unfold lz77LazyMergedLoopNoH3Single lz77LazyMergedLoop
    simp only [chainWalkGuardedPackedUU_eq]
    have hnot : ¬ 1 < lazy2Steps := by omega
    have ih' (c' h3tab' : Array Nat) (pos' : Nat) (acc' : TokenArray)
        (hlt' : data.size - pos' < data.size - pos) :
        lz77LazyMergedLoopNoH3Single data windowSize hashSize prevSize maxChain
            insertCap goodMatch niceLen lazyDepth c' pos' acc' =
          lz77LazyMergedLoop data windowSize hashSize prevSize maxChain insertCap
            goodMatch niceLen lazyDepth lazy2Steps false c' h3tab' pos' 0 0 0 acc' := by
      exact ih (data.size - pos') (by omega) c' h3tab' pos' acc' rfl
    simp (config := { zeta := false }) only [h3Seed, Bool.false_eq_true, if_false,
      updateHashesMergedH3Guarded, hnot, ↓reduceDIte]
    by_cases hlt : pos + 2 < data.size
    · simp (config := { zeta := false }) only [hlt, ↓reduceDIte]
      generalize hh :
        lz77Greedy.hash3 data pos hashSize hlt = hash at *
      generalize hhead :
        headProbeGuarded c (prevSize + hash) = head at *
      generalize hc1 :
        guardedSet c (prevSize + hash) pos = c1 at *
      generalize hc2 :
        guardedSet c1 (pos &&& 0x7FFF) head = c2 at *
      generalize hr :
        chainWalkGuardedPackedU data c2 windowSize pos
          (min 258 (data.size - pos)) niceLen (by omega) head maxChain 0 0 = r at *
      by_cases hge : r % 512 ≥ 3
      · simp only [hge, ↓reduceDIte]
        by_cases hle : pos + r % 512 ≤ data.size
        · simp only [hle, ↓reduceDIte]
          by_cases h3lt : pos + 3 < data.size
          · simp only [h3lt, ↓reduceDIte]
            by_cases hgood : r % 512 < goodMatch
            · simp only [hgood, if_pos]
              generalize hr2 :
                chainWalkGuardedPackedU data c2 windowSize (pos + 1)
                  (min 258 (data.size - (pos + 1))) niceLen (by omega)
                  (headProbeGuarded c2
                    (prevSize + lz77Greedy.hash3 data (pos + 1) hashSize (by omega)))
                  lazyDepth
                  (if r % 512 < min niceLen (min 258 (data.size - (pos + 1))) then
                    r % 512 else 0) 0 = r2 at *
              by_cases hacc :
                  lazyAcceptCost (r % 512) (pos - r / 512)
                    (r2 % 512) (pos + 1 - r2 / 512) = true
              · simp only [hacc, if_true]
                by_cases hle2 : pos + 1 + r2 % 512 ≤ data.size
                · simp only [hle2, ↓reduceDIte]
                  apply ih' <;> omega
                · simp only [hle2, ↓reduceDIte]
                  apply ih' <;> omega
              · simp only [hacc]
                apply ih' <;> omega
            · simp only [hgood]
              apply ih' <;> omega
          · simp only [h3lt, ↓reduceDIte]
            apply ih' <;> omega
        · simp only [hle, ↓reduceDIte]
          apply ih' <;> omega
      · simp only [hge, ↓reduceDIte]
        apply ih' <;> omega
    · simp only [hlt, ↓reduceDIte]

/-- The large-input L5 entry equals the two-array packed lazy matcher at L5's
    fixed chain depths and no-H3/single-deferral policy. -/
theorem lz77ChainLazyIterPMergedL5Large_eq (data : ByteArray)
    (windowSize insertCap goodMatch niceLen : Nat) :
    lz77ChainLazyIterPMergedL5Large data windowSize insertCap goodMatch niceLen =
      lz77ChainLazyIterP data 22 windowSize insertCap goodMatch niceLen 5 false 1 := by
  calc
    lz77ChainLazyIterPMergedL5Large data windowSize insertCap goodMatch niceLen =
        lz77ChainLazyIterPMerged data 22 windowSize insertCap goodMatch niceLen
          5 false 1 := by
      unfold lz77ChainLazyIterPMergedL5Large lz77ChainLazyIterPMerged
      split
      · rfl
      · dsimp only
        exact noH3SingleLoop_eq data windowSize 65536
          (min chainWinSize data.size) 22 insertCap goodMatch niceLen 5 1
          (by omega) _ (Array.replicate 32768 data.size) 0 _
    _ = lz77ChainLazyIterP data 22 windowSize insertCap goodMatch niceLen
          5 false 1 :=
      lz77ChainLazyIterPMerged_eq data 22 windowSize insertCap goodMatch niceLen
        5 false 1

end Zip.Native.Deflate
