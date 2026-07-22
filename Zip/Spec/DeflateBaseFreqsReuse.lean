import Zip.Spec.LZ77PackedCorrect
import Zip.Spec.DeflateFreqsAdditive

/-!
# Reusing the split-sizing frequencies for the base candidate (#2772)

`sharedPartitionSizedFreqsP` computes, in one pass over the clamped partition, the
same `(bits, per-block trees)` as `sharedPartitionSizedP` **and** the whole-stream
frequencies (EOB-corrected sum of the per-block `tokenFreqsP`). This file proves:

* `sharedPartitionSizedFreqsP_fst` — component 1 is exactly `sharedPartitionSizedP`,
  so every sizing/emit theorem transfers unchanged.
* `sharedPartitionSizedFreqsP_snd` — component 2 is `tokenFreqsP (toks.extract pos
  toks.size)` (via `tokenFreqsP_append` over the clamped cuts).
* `deflateObsSplitSizedFreqsP_fst` / `_snd` — the split candidate prep is
  `deflateDynamicBlocksSharedAtSizedP`, and the paired frequencies are
  `tokenFreqsP toks`.
* `deflateRawBasePPrepF_obsFreqs` — feeding those frequencies to the freq-taking
  base prep recovers `deflateRawBasePPrep`, so the base candidate's second
  whole-stream frequency walk is eliminated with no change to its output.
-/

namespace Zip.Native.Deflate

/-- Fuel form of `sharedPartitionSizedFreqsP_fst`. -/
private theorem sharedPartitionSizedFreqsP_fst_fuel (toks : Array UInt32) :
    ∀ (fuel pos : Nat), toks.size - pos < fuel → ∀ (cuts : List Nat),
      (sharedPartitionSizedFreqsP toks cuts pos).1 = sharedPartitionSizedP toks cuts pos := by
  intro fuel
  induction fuel with
  | zero => intro pos hf; omega
  | succ fuel ih =>
    intro pos hf cuts
    by_cases hend : min (max (cuts.headD toks.size) (pos + 1)) toks.size ≥ toks.size
    · conv => lhs; unfold sharedPartitionSizedFreqsP
      conv => rhs; unfold sharedPartitionSizedP
      simp only [if_pos hend]
    · conv => lhs; unfold sharedPartitionSizedFreqsP
      conv => rhs; unfold sharedPartitionSizedP
      simp only [if_neg hend]
      rw [ih (min (max (cuts.headD toks.size) (pos + 1)) toks.size) (by omega) cuts.tail]

/-- Component 1 of `sharedPartitionSizedFreqsP` is exactly `sharedPartitionSizedP`. -/
theorem sharedPartitionSizedFreqsP_fst (toks : Array UInt32) (cuts : List Nat) (pos : Nat) :
    (sharedPartitionSizedFreqsP toks cuts pos).1 = sharedPartitionSizedP toks cuts pos :=
  sharedPartitionSizedFreqsP_fst_fuel toks (toks.size - pos + 1) pos (by omega) cuts

/-- Fuel form of `sharedPartitionSizedFreqsP_snd`. -/
private theorem sharedPartitionSizedFreqsP_snd_fuel (toks : Array UInt32) :
    ∀ (fuel pos : Nat), toks.size - pos < fuel → ∀ (cuts : List Nat),
      (sharedPartitionSizedFreqsP toks cuts pos).2 = tokenFreqsP (toks.extract pos toks.size) := by
  intro fuel
  induction fuel with
  | zero => intro pos hf; omega
  | succ fuel ih =>
    intro pos hf cuts
    by_cases hend : min (max (cuts.headD toks.size) (pos + 1)) toks.size ≥ toks.size
    · conv => lhs; unfold sharedPartitionSizedFreqsP
      simp only [if_pos hend]
      rw [show min (max (cuts.headD toks.size) (pos + 1)) toks.size = toks.size from by omega]
    · conv => lhs; unfold sharedPartitionSizedFreqsP
      simp only [if_neg hend]
      rw [ih (min (max (cuts.headD toks.size) (pos + 1)) toks.size) (by omega) cuts.tail,
        ← tokenFreqsP_append, Array.extract_append_extract,
        show min pos (min (max (cuts.headD toks.size) (pos + 1)) toks.size) = pos from by omega,
        show max (min (max (cuts.headD toks.size) (pos + 1)) toks.size) toks.size = toks.size from by omega]

/-- Component 2 of `sharedPartitionSizedFreqsP` is the whole-stream histogram of the
    covered suffix — the EOB-corrected sum of the per-block frequencies. -/
theorem sharedPartitionSizedFreqsP_snd (toks : Array UInt32) (cuts : List Nat) (pos : Nat) :
    (sharedPartitionSizedFreqsP toks cuts pos).2 = tokenFreqsP (toks.extract pos toks.size) :=
  sharedPartitionSizedFreqsP_snd_fuel toks (toks.size - pos + 1) pos (by omega) cuts

/-- The split candidate prep is exactly `deflateDynamicBlocksSharedAtSizedP`. -/
theorem deflateObsSplitSizedFreqsP_fst (data : ByteArray) (toks : Array UInt32) (cuts : List Nat) :
    (deflateObsSplitSizedFreqsP data toks cuts).1 = deflateDynamicBlocksSharedAtSizedP data toks cuts := by
  unfold deflateObsSplitSizedFreqsP deflateDynamicBlocksSharedAtSizedP
  split
  · rfl
  · dsimp only []
    rw [sharedPartitionSizedFreqsP_fst]

/-- The frequencies paired with the split candidate prep are `tokenFreqsP toks`. -/
theorem deflateObsSplitSizedFreqsP_snd (data : ByteArray) (toks : Array UInt32) (cuts : List Nat) :
    (deflateObsSplitSizedFreqsP data toks cuts).2 = tokenFreqsP toks := by
  unfold deflateObsSplitSizedFreqsP
  split
  · rfl
  · dsimp only []
    rw [sharedPartitionSizedFreqsP_snd, Array.extract_eq_self_of_le (Nat.le_refl _)]

/-- Feeding the split-sizing frequencies to the freq-taking base prep recovers
    `deflateRawBasePPrep`: the base candidate's second whole-stream frequency walk
    is replaced by a reuse of the per-block frequencies, with identical output. -/
theorem deflateRawBasePPrepF_obsFreqs (data : ByteArray) (toks : Array UInt32) (cuts : List Nat) :
    deflateRawBasePPrepF data toks (deflateObsSplitSizedFreqsP data toks cuts).2
      = deflateRawBasePPrep data toks := by
  rw [deflateObsSplitSizedFreqsP_snd, deflateRawBasePPrepF_tokenFreqsP]

/-- **Byte-identity of the reuse dispatch.** The levels-5–8 size-arbitrated pair
    selected by the frequency-reusing dispatch is the *same prepared pair* the
    original dispatch selected: identical prepared sizes, identical tie, identical
    emit thunk. The base candidate reuses the split-sizing frequencies, but nothing
    observable changes, so `deflateRaw`'s output is byte-for-byte unchanged. This is
    the composed statement the roundtrip/padding specs (`inflate_deflateRaw`,
    `deflateRaw_pad`, `deflateRaw_goR_pad`) rewrite through. -/
theorem withObs_reuse_eq (data : ByteArray) (toks : Array UInt32) (cuts : List Nat) :
    (let obsFreqs := deflateObsSplitSizedFreqsP data toks cuts
     let basePrep := deflateRawBasePPrepF data toks obsFreqs.2
     if basePrep.1 < obsFreqs.1.1 then basePrep else obsFreqs.1)
      = (let obsPrep := deflateDynamicBlocksSharedAtSizedP data toks cuts
         if (deflateRawBasePPrep data toks).1 < obsPrep.1 then
           deflateRawBasePPrep data toks else obsPrep) := by
  simp only [deflateRawBasePPrepF_obsFreqs, deflateObsSplitSizedFreqsP_fst]

end Zip.Native.Deflate
