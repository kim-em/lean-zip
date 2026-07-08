import Zip.Native.DeflateFreqs

/-!
# `tokenFreqsP` additivity over concatenation

The split-sizing pass (`sharedPartitionSizedP`) computes `tokenFreqsP` per block,
while the base candidate needs the whole-stream `tokenFreqsP`. This file proves
that the whole-stream histogram is the end-of-block-corrected element-wise sum of
the per-block histograms, so the second whole-stream walk can be replaced by a
cheap `mergeEOBFreqsP` fold over the per-block frequencies.

The core result is `tokenFreqsP_append`:

    tokenFreqsP (a ++ b) = mergeEOBFreqsP (tokenFreqsP a) (tokenFreqsP b)

proven via per-index histogram-counting lemmas: each `tokenFreqsP.go` run bumps
one lit/len index (and, for references, one distance index) per word, so the
final count at index `k` is the initial value plus the number of words that bump
`k` (`litDeltaP`/`distDeltaP`). Those bump-counts are additive over `++`
(`litDeltaP_append`/`distDeltaP_append`); the only correction is the EOB symbol
256, which every histogram pre-counts once and no word ever bumps.
-/

namespace Zip.Native.Deflate

/-- The lit/len index `tokenFreqsP` bumps for the word `ws[i]`: the literal byte
    for a literal token, or the length code `+ 257` for a reference token —
    exactly the index `bumpLitFreqP`/`bumpRefLitFreqP` write. -/
def litBumpIdxP (w : UInt32) : Nat :=
  if w &&& ((1 : UInt32) <<< 31) = 0 then w.toUInt8.toNat
  else codeIdx (lenCodeWord (((w >>> 16) &&& 0x7FFF).toNat)) + 257

/-- Number of words in `ws[i:]` whose lit/len bump lands on index `k`. -/
def litDeltaP (ws : Array UInt32) (i k : Nat) : Nat :=
  if h : i < ws.size then
    (if litBumpIdxP ws[i] = k then 1 else 0) + litDeltaP ws (i + 1) k
  else 0
termination_by ws.size - i

/-- Number of words in `ws[i:]` whose distance bump lands on index `k`
    (literal words bump no distance). -/
def distDeltaP (ws : Array UInt32) (i k : Nat) : Nat :=
  if h : i < ws.size then
    (if ws[i] &&& ((1 : UInt32) <<< 31) = 0 then 0
     else if codeIdx (distCodeWord ((ws[i] &&& 0xFFFF).toNat)) = k then 1 else 0)
      + distDeltaP ws (i + 1) k
  else 0
termination_by ws.size - i

/-- No word ever bumps the end-of-block symbol (256): literals land below 256,
    references at `≥ 257`. -/
theorem litBumpIdxP_ne_256 (w : UInt32) : litBumpIdxP w ≠ 256 := by
  unfold litBumpIdxP
  split
  · have := UInt8.toNat_lt w.toUInt8; omega
  · omega

/-- Consequently `litDeltaP` never counts index 256. -/
theorem litDeltaP_256 (ws : Array UInt32) (i : Nat) : litDeltaP ws i 256 = 0 := by
  induction h : ws.size - i using Nat.strongRecOn generalizing i with
  | _ n ih =>
    unfold litDeltaP
    by_cases hi : i < ws.size
    · rw [dif_pos hi, if_neg (litBumpIdxP_ne_256 _), Nat.zero_add]
      exact ih (ws.size - (i + 1)) (by omega) (i + 1) rfl
    · rw [dif_neg hi]

/-- Single-step unfold of `litDeltaP` at a valid index. -/
theorem litDeltaP_succ (ws : Array UInt32) (i k : Nat) (h : i < ws.size) :
    litDeltaP ws i k = (if litBumpIdxP ws[i] = k then 1 else 0) + litDeltaP ws (i + 1) k := by
  rw [litDeltaP, dif_pos h]

/-- `litDeltaP` past the end is zero. -/
theorem litDeltaP_of_ge (ws : Array UInt32) (i k : Nat) (h : ¬ i < ws.size) :
    litDeltaP ws i k = 0 := by
  rw [litDeltaP, dif_neg h]

/-- Words counted from `a.size + j` in `a ++ b` are exactly `b`'s words from `j`. -/
theorem litDeltaP_shift (a b : Array UInt32) (j k : Nat) :
    litDeltaP (a ++ b) (a.size + j) k = litDeltaP b j k := by
  induction h : b.size - j using Nat.strongRecOn generalizing j with
  | _ n ih =>
    by_cases hj : j < b.size
    · have hij : a.size + j < (a ++ b).size := by rw [Array.size_append]; omega
      rw [litDeltaP_succ _ _ _ hij, litDeltaP_succ _ _ _ hj]
      have hw : (a ++ b)[a.size + j]'hij = b[j]'hj := by
        rw [Array.getElem_append_right (by omega)]
        simp only [Nat.add_sub_cancel_left]
      rw [hw, show a.size + j + 1 = a.size + (j + 1) by omega]
      rw [ih (b.size - (j + 1)) (by omega) (j + 1) rfl]
    · rw [litDeltaP_of_ge _ _ _ (by rw [Array.size_append]; omega),
        litDeltaP_of_ge _ _ _ hj]

/-- `litDeltaP` is additive over `++`: counting from `i ≤ a.size` in `a ++ b`
    splits into `a`'s words from `i` plus all of `b`'s words. -/
theorem litDeltaP_append (a b : Array UInt32) (i k : Nat) (hi : i ≤ a.size) :
    litDeltaP (a ++ b) i k = litDeltaP a i k + litDeltaP b 0 k := by
  induction h : a.size - i using Nat.strongRecOn generalizing i with
  | _ n ih =>
    by_cases hlt : i < a.size
    · have hij : i < (a ++ b).size := by rw [Array.size_append]; omega
      rw [litDeltaP_succ _ _ _ hij, litDeltaP_succ _ _ _ hlt]
      have hw : (a ++ b)[i]'hij = a[i]'hlt := Array.getElem_append_left hlt
      rw [hw, Nat.add_assoc, ih (a.size - (i + 1)) (by omega) (i + 1) (by omega) rfl]
    · have hie : i = a.size := by omega
      subst hie
      rw [litDeltaP_of_ge a a.size k (by omega), Nat.zero_add]
      have := litDeltaP_shift a b 0 k
      rwa [Nat.add_zero] at this

/-- Single-step unfold of `distDeltaP` at a valid index. -/
theorem distDeltaP_succ (ws : Array UInt32) (i k : Nat) (h : i < ws.size) :
    distDeltaP ws i k =
      (if ws[i] &&& ((1 : UInt32) <<< 31) = 0 then 0
       else if codeIdx (distCodeWord ((ws[i] &&& 0xFFFF).toNat)) = k then 1 else 0)
      + distDeltaP ws (i + 1) k := by
  rw [distDeltaP, dif_pos h]

/-- `distDeltaP` past the end is zero. -/
theorem distDeltaP_of_ge (ws : Array UInt32) (i k : Nat) (h : ¬ i < ws.size) :
    distDeltaP ws i k = 0 := by
  rw [distDeltaP, dif_neg h]

/-- Distance-bump analogue of `litDeltaP_shift`. -/
theorem distDeltaP_shift (a b : Array UInt32) (j k : Nat) :
    distDeltaP (a ++ b) (a.size + j) k = distDeltaP b j k := by
  induction h : b.size - j using Nat.strongRecOn generalizing j with
  | _ n ih =>
    by_cases hj : j < b.size
    · have hij : a.size + j < (a ++ b).size := by rw [Array.size_append]; omega
      rw [distDeltaP_succ _ _ _ hij, distDeltaP_succ _ _ _ hj]
      have hw : (a ++ b)[a.size + j]'hij = b[j]'hj := by
        rw [Array.getElem_append_right (by omega)]
        simp only [Nat.add_sub_cancel_left]
      rw [hw, show a.size + j + 1 = a.size + (j + 1) by omega]
      rw [ih (b.size - (j + 1)) (by omega) (j + 1) rfl]
    · rw [distDeltaP_of_ge _ _ _ (by rw [Array.size_append]; omega),
        distDeltaP_of_ge _ _ _ hj]

/-- Distance-bump analogue of `litDeltaP_append`. -/
theorem distDeltaP_append (a b : Array UInt32) (i k : Nat) (hi : i ≤ a.size) :
    distDeltaP (a ++ b) i k = distDeltaP a i k + distDeltaP b 0 k := by
  induction h : a.size - i using Nat.strongRecOn generalizing i with
  | _ n ih =>
    by_cases hlt : i < a.size
    · have hij : i < (a ++ b).size := by rw [Array.size_append]; omega
      rw [distDeltaP_succ _ _ _ hij, distDeltaP_succ _ _ _ hlt]
      have hw : (a ++ b)[i]'hij = a[i]'hlt := Array.getElem_append_left hlt
      rw [hw, Nat.add_assoc, ih (a.size - (i + 1)) (by omega) (i + 1) (by omega) rfl]
    · have hie : i = a.size := by omega
      subst hie
      rw [distDeltaP_of_ge a a.size k (by omega), Nat.zero_add]
      have := distDeltaP_shift a b 0 k
      rwa [Nat.add_zero] at this

/-! ## Histogram = initial + bump-count -/

/-- Every `tokenFreqsP.go` run leaves the lit/len entry at `k` equal to its
    initial value plus the number of processed words that bump `k`. -/
theorem tokenFreqsP_go_lit (ws : Array UInt32) (lf : {a : Array Nat // a.size = 286})
    (df : {a : Array Nat // a.size = 30}) (i k : Nat) :
    (tokenFreqsP.go ws lf df i).1[k]! = lf.val[k]! + litDeltaP ws i k := by
  induction hh : ws.size - i using Nat.strongRecOn generalizing lf df i with
  | _ n ih =>
    unfold tokenFreqsP.go
    by_cases hi : i < ws.size
    · simp only [hi, ↓reduceDIte]
      rw [litDeltaP_succ _ _ _ hi]
      by_cases hc : ws[i] &&& ((1 : UInt32) <<< 31) = 0
      · simp only [hc, ↓reduceIte]
        rw [ih (ws.size - (i + 1)) (by omega) _ _ _ rfl]
        have hidx : ws[i].toUInt8.toNat < lf.val.size := by
          have := UInt8.toNat_lt ws[i].toUInt8; rw [lf.property]; omega
        have hbump : litBumpIdxP ws[i] = ws[i].toUInt8.toNat := by
          unfold litBumpIdxP; rw [if_pos hc]
        simp only [bumpLitFreqP, hbump]
        by_cases hk : k = ws[i].toUInt8.toNat
        · subst hk
          rw [Array.getElem!_set!_self _ _ _ hidx, ← getElem!_pos lf.val _ hidx,
            if_pos rfl]
          omega
        · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hk), if_neg (fun h => hk h.symm)]
          omega
      · simp only [hc, ↓reduceIte]
        rw [ih (ws.size - (i + 1)) (by omega) _ _ _ rfl]
        obtain ⟨⟨li, le, lv⟩, hli⟩ := Option.isSome_iff_exists.mp
          (findLengthCode_isSome (((ws[i] >>> 16) &&& 0x7FFF).toNat))
        have hbnd := nativeFindLengthCode_idx_bound _ _ _ _ hli
        have hidx : codeIdx (lenCodeWord (((ws[i] >>> 16) &&& 0x7FFF).toNat)) + 257 < lf.val.size := by
          have : codeIdx (lenCodeWord (((ws[i] >>> 16) &&& 0x7FFF).toNat)) = li :=
            codeIdx_lenCodeWord _ _ _ _ hli
          rw [lf.property]; omega
        have hbump : litBumpIdxP ws[i] =
            codeIdx (lenCodeWord (((ws[i] >>> 16) &&& 0x7FFF).toNat)) + 257 := by
          unfold litBumpIdxP; rw [if_neg hc]
        simp only [bumpRefLitFreqP, hbump]
        by_cases hk : k = codeIdx (lenCodeWord (((ws[i] >>> 16) &&& 0x7FFF).toNat)) + 257
        · subst hk
          rw [Array.getElem!_set!_self _ _ _ hidx, ← getElem!_pos lf.val _ hidx,
            if_pos rfl]
          omega
        · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hk), if_neg (fun h => hk h.symm)]
          omega
    · rw [dif_neg hi, litDeltaP_of_ge _ _ _ hi]
      simp

/-- Distance analogue of `tokenFreqsP_go_lit`. -/
theorem tokenFreqsP_go_dist (ws : Array UInt32) (lf : {a : Array Nat // a.size = 286})
    (df : {a : Array Nat // a.size = 30}) (i k : Nat) :
    (tokenFreqsP.go ws lf df i).2[k]! = df.val[k]! + distDeltaP ws i k := by
  induction hh : ws.size - i using Nat.strongRecOn generalizing lf df i with
  | _ n ih =>
    unfold tokenFreqsP.go
    by_cases hi : i < ws.size
    · simp only [hi, ↓reduceDIte]
      rw [distDeltaP_succ _ _ _ hi]
      by_cases hc : ws[i] &&& ((1 : UInt32) <<< 31) = 0
      · simp only [hc, ↓reduceIte]
        rw [ih (ws.size - (i + 1)) (by omega) _ _ _ rfl]
        omega
      · simp only [hc, ↓reduceIte]
        rw [ih (ws.size - (i + 1)) (by omega) _ _ _ rfl]
        obtain ⟨⟨di, de, dv⟩, hdi⟩ := Option.isSome_iff_exists.mp
          (findDistCode_isSome ((ws[i] &&& 0xFFFF).toNat))
        have hbnd := nativeFindDistCode_idx_bound _ _ _ _ hdi
        have hidx : codeIdx (distCodeWord ((ws[i] &&& 0xFFFF).toNat)) < df.val.size := by
          have : codeIdx (distCodeWord ((ws[i] &&& 0xFFFF).toNat)) = di :=
            codeIdx_distCodeWord _ _ _ _ hdi
          rw [df.property]; omega
        simp only [bumpRefDistFreqP]
        by_cases hk : k = codeIdx (distCodeWord ((ws[i] &&& 0xFFFF).toNat))
        · subst hk
          rw [Array.getElem!_set!_self _ _ _ hidx, ← getElem!_pos df.val _ hidx,
            if_pos rfl]
          omega
        · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hk), if_neg (fun h => hk h.symm)]
          omega
    · rw [dif_neg hi, distDeltaP_of_ge _ _ _ hi]
      simp

/-- `tokenFreqsP.go` preserves the histogram sizes. -/
theorem tokenFreqsP_go_size (ws : Array UInt32) (lf : {a : Array Nat // a.size = 286})
    (df : {a : Array Nat // a.size = 30}) (i : Nat) :
    (tokenFreqsP.go ws lf df i).1.size = 286 ∧ (tokenFreqsP.go ws lf df i).2.size = 30 := by
  induction hh : ws.size - i using Nat.strongRecOn generalizing lf df i with
  | _ n ih =>
    unfold tokenFreqsP.go
    by_cases hi : i < ws.size
    · simp only [hi, ↓reduceDIte]
      by_cases hc : ws[i] &&& ((1 : UInt32) <<< 31) = 0
      · simp only [hc, ↓reduceIte]; exact ih (ws.size - (i + 1)) (by omega) _ _ _ rfl
      · simp only [hc, ↓reduceIte]; exact ih (ws.size - (i + 1)) (by omega) _ _ _ rfl
    · rw [dif_neg hi]; exact ⟨lf.property, df.property⟩

/-- `tokenFreqsP` produces histograms of size 286 and 30. -/
theorem tokenFreqsP_size (ws : Array UInt32) :
    (tokenFreqsP ws).1.size = 286 ∧ (tokenFreqsP ws).2.size = 30 := by
  unfold tokenFreqsP; exact tokenFreqsP_go_size _ _ _ _

/-- Any index into an all-zero replicate array reads zero (in or out of bounds). -/
theorem replicate_zero_get (n k : Nat) : (Array.replicate n (0 : Nat))[k]! = 0 := by
  by_cases hkk : k < n
  · rw [getElem!_pos _ _ (by rw [Array.size_replicate]; exact hkk), Array.getElem_replicate]
  · rw [getElem!_neg _ _ (by rw [Array.size_replicate]; omega)]; rfl

/-- Value of the pre-seeded lit/len histogram: EOB (256) counted once, else zero. -/
theorem initLit_get (k : Nat) :
    ((Array.replicate 286 (0 : Nat)).set! 256 1)[k]! = if k = 256 then 1 else 0 := by
  by_cases hk : k = 256
  · subst hk
    rw [Array.getElem!_set!_self _ _ _ (by rw [Array.size_replicate]; omega), if_pos rfl]
  · rw [Array.getElem!_set!_ne _ _ _ _ (fun h => hk h.symm), if_neg hk, replicate_zero_get]

/-- Whole-stream lit/len count at `k`: EOB pre-count plus the words that bump `k`. -/
theorem tokenFreqsP_lit (ws : Array UInt32) (k : Nat) :
    (tokenFreqsP ws).1[k]! = (if k = 256 then 1 else 0) + litDeltaP ws 0 k := by
  unfold tokenFreqsP
  rw [tokenFreqsP_go_lit, initLit_get]

/-- Whole-stream distance count at `k`: exactly the words that bump `k`. -/
theorem tokenFreqsP_dist (ws : Array UInt32) (k : Nat) :
    (tokenFreqsP ws).2[k]! = distDeltaP ws 0 k := by
  unfold tokenFreqsP
  rw [tokenFreqsP_go_dist, replicate_zero_get, Nat.zero_add]

/-- Element-wise sum of two equal-size arrays reads as the sum of the elements. -/
theorem zipWithAdd_get (A B : Array Nat) (k : Nat) (hk : k < A.size) (hAB : A.size = B.size) :
    (Array.zipWith (· + ·) A B)[k]! = A[k]! + B[k]! := by
  have hkB : k < B.size := by omega
  have hsz : k < (Array.zipWith (· + ·) A B).size := by rw [Array.size_zipWith]; omega
  rw [getElem!_pos (Array.zipWith (· + ·) A B) k hsz, Array.getElem_zipWith,
    getElem!_pos A k hk, getElem!_pos B k hkB]

/-- **Additivity of `tokenFreqsP` over concatenation.** The whole-stream histogram
    is the element-wise sum of the two sub-stream histograms, correcting the EOB
    symbol (256) that both pre-count. This is what lets the split-sizing pass's
    per-block frequencies be folded (`mergeEOBFreqsP`) into the whole-stream
    frequencies the base candidate needs, with no second whole-stream walk. -/
theorem tokenFreqsP_append (a b : Array UInt32) :
    tokenFreqsP (a ++ b) = mergeEOBFreqsP (tokenFreqsP a) (tokenFreqsP b) := by
  have hsa := tokenFreqsP_size a
  have hsb := tokenFreqsP_size b
  have hsab := tokenFreqsP_size (a ++ b)
  apply Prod.ext
  · -- lit/len component
    apply Array.ext
    · rw [hsab.1]
      simp only [mergeEOBFreqsP, Array.size_set!, Array.size_zipWith, hsa.1, hsb.1, Nat.min_self]
    · intro k hk1 _
      rw [hsab.1] at hk1
      rw [← getElem!_pos _ k (by rw [hsab.1]; exact hk1),
        ← getElem!_pos _ k (by
          simp only [mergeEOBFreqsP, Array.size_set!, Array.size_zipWith, hsa.1, hsb.1]; exact hk1)]
      rw [tokenFreqsP_lit (a ++ b) k, litDeltaP_append a b 0 k (Nat.zero_le _)]
      simp only [mergeEOBFreqsP]
      by_cases hk256 : k = 256
      · subst hk256
        rw [Array.getElem!_set!_self _ _ _ (by rw [Array.size_zipWith, hsa.1, hsb.1]; omega),
          zipWithAdd_get _ _ _ (by rw [hsa.1]; omega) (by rw [hsa.1, hsb.1]),
          tokenFreqsP_lit a 256, tokenFreqsP_lit b 256]
        simp only [↓reduceIte]
        omega
      · rw [Array.getElem!_set!_ne _ _ _ _ (fun h => hk256 h.symm),
          zipWithAdd_get _ _ _ (by rw [hsa.1]; omega) (by rw [hsa.1, hsb.1]),
          tokenFreqsP_lit a k, tokenFreqsP_lit b k]
        simp only [if_neg hk256]
        omega
  · -- distance component
    apply Array.ext
    · rw [hsab.2]
      simp only [mergeEOBFreqsP, Array.size_zipWith, hsa.2, hsb.2, Nat.min_self]
    · intro k hk1 _
      rw [hsab.2] at hk1
      rw [← getElem!_pos _ k (by rw [hsab.2]; exact hk1),
        ← getElem!_pos _ k (by
          simp only [mergeEOBFreqsP, Array.size_zipWith, hsa.2, hsb.2]; exact hk1)]
      rw [tokenFreqsP_dist (a ++ b) k, distDeltaP_append a b 0 k (Nat.zero_le _)]
      simp only [mergeEOBFreqsP]
      rw [zipWithAdd_get _ _ _ (by rw [hsa.2]; omega) (by rw [hsa.2, hsb.2]),
        tokenFreqsP_dist a k, tokenFreqsP_dist b k]

end Zip.Native.Deflate
