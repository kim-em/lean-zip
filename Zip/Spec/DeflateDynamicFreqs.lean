import Zip.Native.DeflateDynamic
import Zip.Spec.EmitTokensCorrect

/-!
# tokenFreqs properties for dynamic Huffman correctness

This file proves properties of the `tokenFreqs` frequency-counting function
used by the dynamic Huffman compressor. These are internal helpers for
`DeflateDynamicCorrect.lean`.

## Key results

- `tokenFreqs_sizes`: output arrays have size 286 and 30
- `tokenFreqs_eob_pos`: end-of-block symbol always has frequency ≥ 1
- `tokenFreqs_literal_pos`: literal byte frequency is positive when present
- `tokenFreqs_lengthCode_pos`: length code frequency is positive when present
- `tokenFreqs_distCode_pos`: distance code frequency is positive when present
- `toUInt8Array_le`: converting bounded Nat list to UInt8 preserves bounds
- `freqPairs_witness`: positive frequency implies witness in frequency pairs
-/

set_option linter.unusedSimpArgs false

namespace Zip.Native.Deflate

/-- `tokenFreqs.go` preserves array sizes. -/
protected theorem tokenFreqs_go_sizes (tokens : Array LZ77Token)
    (litFreqs distFreqs : Array Nat) (i : Nat)
    (hlit : litFreqs.size = 286) (hdist : distFreqs.size = 30) :
    (tokenFreqs.go tokens litFreqs distFreqs i).1.size = 286 ∧
    (tokenFreqs.go tokens litFreqs distFreqs i).2.size = 30 := by
  unfold tokenFreqs.go
  split
  · rename_i h
    match htok : tokens[i] with
    | .literal b =>
      simp only [htok]
      apply Deflate.tokenFreqs_go_sizes
      · simp; omega
      · exact hdist
    | .reference len dist =>
      simp only [htok]
      apply Deflate.tokenFreqs_go_sizes
      · cases findLengthCode len with
        | none => exact hlit
        | some p => obtain ⟨idx, _, _⟩ := p; simp; omega
      · cases findDistCode dist with
        | none => exact hdist
        | some p => obtain ⟨dIdx, _, _⟩ := p; simp; omega
  · exact ⟨hlit, hdist⟩
termination_by tokens.size - i

/-- `tokenFreqs` produces arrays of size 286 and 30. -/
protected theorem tokenFreqs_sizes (tokens : Array LZ77Token) :
    (tokenFreqs tokens).1.size = 286 ∧ (tokenFreqs tokens).2.size = 30 := by
  simp only [tokenFreqs]
  apply Deflate.tokenFreqs_go_sizes
  · simp
  · simp

/-- `tokenFreqs.go` only increases frequency values. -/
protected theorem tokenFreqs_go_mono (tokens : Array LZ77Token)
    (litFreqs distFreqs : Array Nat) (i idx : Nat)
    (hlit : litFreqs.size = 286) (hdist : distFreqs.size = 30) :
    (idx < 286 → litFreqs[idx]! ≤ (tokenFreqs.go tokens litFreqs distFreqs i).1[idx]!) ∧
    (idx < 30 → distFreqs[idx]! ≤ (tokenFreqs.go tokens litFreqs distFreqs i).2[idx]!) := by
  unfold tokenFreqs.go
  split
  · rename_i h
    match htok : tokens[i] with
    | .literal b =>
      simp only [htok]
      have ih := Deflate.tokenFreqs_go_mono tokens
        (litFreqs.set! b.toNat (litFreqs[b.toNat]! + 1)) distFreqs (i + 1) idx
        (by simp; omega) hdist
      constructor
      · intro hidx
        exact Nat.le_trans (Array.getElem!_le_set!_incr litFreqs b.toNat idx
          (by have := UInt8.toNat_lt b; omega)) (ih.1 hidx)
      · exact ih.2
    | .reference length distance =>
      simp only [htok]
      -- Split on findLengthCode and findDistCode
      constructor
      · intro hidx
        cases hflc : findLengthCode length with
        | none =>
          cases hfdc : findDistCode distance with
          | none =>
            have ih := Deflate.tokenFreqs_go_mono tokens litFreqs distFreqs (i + 1) idx hlit hdist
            exact ih.1 hidx
          | some p =>
            obtain ⟨dIdx, dN, dV⟩ := p
            have ih := Deflate.tokenFreqs_go_mono tokens litFreqs
              (distFreqs.set! dIdx (distFreqs[dIdx]! + 1)) (i + 1) idx
              hlit (by simp; omega)
            exact ih.1 hidx
        | some p =>
          obtain ⟨lIdx, lN, lV⟩ := p
          cases hfdc : findDistCode distance with
          | none =>
            have ih := Deflate.tokenFreqs_go_mono tokens
              (litFreqs.set! (lIdx + 257) (litFreqs[lIdx + 257]! + 1)) distFreqs (i + 1) idx
              (by simp; omega) hdist
            have hlIdx := nativeFindLengthCode_idx_bound _ lIdx lN lV hflc
            exact Nat.le_trans (Array.getElem!_le_set!_incr litFreqs _ idx (by omega)) (ih.1 hidx)
          | some q =>
            obtain ⟨dIdx, dN, dV⟩ := q
            have hlIdx := nativeFindLengthCode_idx_bound _ lIdx lN lV hflc
            have ih := Deflate.tokenFreqs_go_mono tokens
              (litFreqs.set! (lIdx + 257) (litFreqs[lIdx + 257]! + 1))
              (distFreqs.set! dIdx (distFreqs[dIdx]! + 1)) (i + 1) idx
              (by simp; omega) (by simp; omega)
            exact Nat.le_trans (Array.getElem!_le_set!_incr litFreqs _ idx (by omega)) (ih.1 hidx)
      · intro hidx
        cases hflc : findLengthCode length with
        | none =>
          cases hfdc : findDistCode distance with
          | none =>
            have ih := Deflate.tokenFreqs_go_mono tokens litFreqs distFreqs (i + 1) idx hlit hdist
            exact ih.2 hidx
          | some p =>
            obtain ⟨dIdx, dN, dV⟩ := p
            have hdIdx := nativeFindDistCode_idx_bound _ dIdx dN dV hfdc
            have ih := Deflate.tokenFreqs_go_mono tokens litFreqs
              (distFreqs.set! dIdx (distFreqs[dIdx]! + 1)) (i + 1) idx
              hlit (by simp; omega)
            exact Nat.le_trans (Array.getElem!_le_set!_incr distFreqs dIdx idx (by omega)) (ih.2 hidx)
        | some p =>
          obtain ⟨lIdx, lN, lV⟩ := p
          cases hfdc : findDistCode distance with
          | none =>
            have ih := Deflate.tokenFreqs_go_mono tokens
              (litFreqs.set! (lIdx + 257) (litFreqs[lIdx + 257]! + 1)) distFreqs (i + 1) idx
              (by simp; omega) hdist
            exact ih.2 hidx
          | some q =>
            obtain ⟨dIdx, dN, dV⟩ := q
            have hdIdx := nativeFindDistCode_idx_bound _ dIdx dN dV hfdc
            have ih := Deflate.tokenFreqs_go_mono tokens
              (litFreqs.set! (lIdx + 257) (litFreqs[lIdx + 257]! + 1))
              (distFreqs.set! dIdx (distFreqs[dIdx]! + 1)) (i + 1) idx
              (by simp; omega) (by simp; omega)
            exact Nat.le_trans (Array.getElem!_le_set!_incr distFreqs dIdx idx (by omega)) (ih.2 hidx)
  · exact ⟨fun _ => Nat.le.refl, fun _ => Nat.le.refl⟩
termination_by tokens.size - i

/-- `tokenFreqs` counts end-of-block (symbol 256) with frequency ≥ 1. -/
protected theorem tokenFreqs_eob_pos (tokens : Array LZ77Token) :
    (tokenFreqs tokens).1[256]! ≥ 1 := by
  -- tokenFreqs.go monotonically increases frequency values
  -- Initial lit array has [256]! = 1, so result has [256]! ≥ 1
  have hmono : ((Array.replicate 286 (0 : Nat)).set! 256 1)[256]! ≤
      (tokenFreqs tokens).1[256]! :=
    (Deflate.tokenFreqs_go_mono tokens _ _ 0 256 (by simp) (by simp)).1 (by omega)
  have h256 : ((Array.replicate 286 (0 : Nat)).set! 256 1)[256]! = 1 :=
    Array.getElem!_set!_self _ _ _ (by simp)
  omega

/-- `tokenFreqs.go` produces positive lit frequency for literal `b` at position `j ≥ i`. -/
protected theorem tokenFreqs_go_literal_pos (tokens : Array LZ77Token) (b : UInt8)
    (litFreqs distFreqs : Array Nat) (i j : Nat)
    (hlit : litFreqs.size = 286) (hdist : distFreqs.size = 30)
    (hj : j ≥ i) (hjlt : j < tokens.size) (htok : tokens[j] = .literal b) :
    (tokenFreqs.go tokens litFreqs distFreqs i).1[b.toNat]! ≥ 1 := by
  unfold tokenFreqs.go
  split
  · rename_i h
    match htoki : tokens[i] with
    | .literal b' =>
      simp only [htoki]
      by_cases hij : i = j
      · -- This is the token we're looking for
        subst hij; simp only [htoki] at htok
        have hbeq : b' = b := LZ77Token.literal.inj htok
        rw [hbeq]
        -- After set, litFreqs[b.toNat]! ≥ 1
        have hle := (Deflate.tokenFreqs_go_mono tokens
          (litFreqs.set! b.toNat (litFreqs[b.toNat]! + 1)) distFreqs (i + 1) b.toNat
          (by simp; omega) hdist).1 (by have := UInt8.toNat_lt b; omega)
        have hblt := UInt8.toNat_lt b
        have hset : (litFreqs.set! b.toNat (litFreqs[b.toNat]! + 1))[b.toNat]! ≥ 1 := by
          rw [Array.getElem!_set!_self litFreqs _ _ (by omega)]; omega
        omega
      · -- Not this token yet, recurse
        exact Deflate.tokenFreqs_go_literal_pos tokens b
          (litFreqs.set! b'.toNat (litFreqs[b'.toNat]! + 1)) distFreqs (i + 1) j
          (by simp; omega) hdist (by omega) hjlt htok
    | .reference len' dist' =>
      simp only [htoki]
      have hij : i ≠ j := by intro heq; subst heq; rw [htoki] at htok; simp at htok
      exact Deflate.tokenFreqs_go_literal_pos tokens b _ _ (i + 1) j
        (by cases findLengthCode len' with
          | none => exact hlit
          | some p => obtain ⟨idx, _, _⟩ := p; simp; omega)
        (by cases findDistCode dist' with
          | none => exact hdist
          | some p => obtain ⟨dIdx, _, _⟩ := p; simp; omega)
        (by omega) hjlt htok
  · omega
termination_by tokens.size - i

/-- `tokenFreqs` counts literal byte `b` if it appears in `tokens`. -/
protected theorem tokenFreqs_literal_pos (tokens : Array LZ77Token) (b : UInt8)
    (hmem : LZ77Token.literal b ∈ tokens.toList) :
    (tokenFreqs tokens).1[b.toNat]! ≥ 1 := by
  have ⟨j, hjlt, htok⟩ := List.mem_iff_getElem.mp hmem
  simp only [Array.length_toList] at hjlt
  have htok' : tokens[j] = .literal b := by
    simp only [Array.getElem_toList] at htok; exact htok
  exact Deflate.tokenFreqs_go_literal_pos tokens b _ _ 0 j
    (by simp) (by simp) (by omega) hjlt htok'

/-- `tokenFreqs.go` produces positive lit frequency for length code from ref at position `j ≥ i`. -/
protected theorem tokenFreqs_go_lengthCode_pos (tokens : Array LZ77Token)
    (len dist : Nat) (idx extraN : Nat) (extraV : UInt32)
    (litFreqs distFreqs : Array Nat) (i j : Nat)
    (hlit : litFreqs.size = 286) (hdist : distFreqs.size = 30)
    (hj : j ≥ i) (hjlt : j < tokens.size)
    (htok : tokens[j] = .reference len dist)
    (hflc : findLengthCode len = some (idx, extraN, extraV)) :
    (tokenFreqs.go tokens litFreqs distFreqs i).1[257 + idx]! ≥ 1 := by
  unfold tokenFreqs.go
  split
  · rename_i h
    match htoki : tokens[i] with
    | .literal b' =>
      simp only [htoki]
      have hij : i ≠ j := by intro heq; subst heq; rw [htoki] at htok; simp at htok
      exact Deflate.tokenFreqs_go_lengthCode_pos tokens len dist idx extraN extraV
        (litFreqs.set! b'.toNat (litFreqs[b'.toNat]! + 1)) distFreqs (i + 1) j
        (by simp; omega) hdist (by omega) hjlt htok hflc
    | .reference len' dist' =>
      simp only [htoki]
      by_cases hij : i = j
      · -- This is the token — i = j
        subst hij
        have heq : LZ77Token.reference len' dist' = LZ77Token.reference len dist :=
          htoki.symm.trans htok
        have hlen_eq : len' = len := (LZ77Token.reference.inj heq).1
        have hdist_eq : dist' = dist := (LZ77Token.reference.inj heq).2
        -- The goal talks about findLengthCode len' and findDistCode dist' (from the match)
        simp only [hlen_eq, hdist_eq, hflc]
        have hidx := nativeFindLengthCode_idx_bound _ idx extraN extraV hflc
        -- After set, litFreqs[257+idx]! ≥ 1
        have hle := (Deflate.tokenFreqs_go_mono tokens
          (litFreqs.set! (idx + 257) (litFreqs[idx + 257]! + 1))
          (match findDistCode dist with
           | some (dIdx, _, _) => distFreqs.set! dIdx (distFreqs[dIdx]! + 1)
           | none => distFreqs) (i + 1) (257 + idx)
          (by simp; omega)
          (by cases findDistCode dist with
            | none => exact hdist
            | some p => obtain ⟨dIdx, _, _⟩ := p; simp; omega)).1
          (by omega)
        have hset : (litFreqs.set! (idx + 257) (litFreqs[idx + 257]! + 1))[257 + idx]! ≥ 1 := by
          rw [show idx + 257 = 257 + idx from by omega]
          rw [Array.getElem!_set!_self litFreqs _ _ (by omega)]; omega
        exact Nat.le_trans hset hle
      · -- Not this token, recurse
        exact Deflate.tokenFreqs_go_lengthCode_pos tokens len dist idx extraN extraV _ _ (i + 1) j
          (by cases findLengthCode len' with
            | none => exact hlit
            | some p => obtain ⟨lIdx, _, _⟩ := p; simp; omega)
          (by cases findDistCode dist' with
            | none => exact hdist
            | some p => obtain ⟨dIdx, _, _⟩ := p; simp; omega)
          (by omega) hjlt htok hflc
  · omega
termination_by tokens.size - i

/-- `tokenFreqs` counts length code `idx+257` if `.reference len dist` appears
    in `tokens` and `findLengthCode len = some (idx, ...)`. -/
protected theorem tokenFreqs_lengthCode_pos (tokens : Array LZ77Token)
    (len dist : Nat) (idx extraN : Nat) (extraV : UInt32)
    (hmem : LZ77Token.reference len dist ∈ tokens.toList)
    (hflc : findLengthCode len = some (idx, extraN, extraV)) :
    (tokenFreqs tokens).1[257 + idx]! ≥ 1 := by
  have ⟨j, hjlt, htok⟩ := List.mem_iff_getElem.mp hmem
  simp only [Array.length_toList] at hjlt
  have htok' : tokens[j] = .reference len dist := by
    simp only [Array.getElem_toList] at htok; exact htok
  exact Deflate.tokenFreqs_go_lengthCode_pos tokens len dist idx extraN extraV _ _ 0 j
    (by simp) (by simp) (by omega) hjlt htok' hflc

/-- `tokenFreqs.go` produces positive dist frequency for dist code from ref at position `j ≥ i`. -/
protected theorem tokenFreqs_go_distCode_pos (tokens : Array LZ77Token)
    (len dist : Nat) (dCode dExtraN : Nat) (dExtraV : UInt32)
    (litFreqs distFreqs : Array Nat) (i j : Nat)
    (hlit : litFreqs.size = 286) (hdist : distFreqs.size = 30)
    (hj : j ≥ i) (hjlt : j < tokens.size)
    (htok : tokens[j] = .reference len dist)
    (hfdc : findDistCode dist = some (dCode, dExtraN, dExtraV)) :
    (tokenFreqs.go tokens litFreqs distFreqs i).2[dCode]! ≥ 1 := by
  unfold tokenFreqs.go
  split
  · rename_i h
    match htoki : tokens[i] with
    | .literal b' =>
      simp only [htoki]
      have hij : i ≠ j := by intro heq; subst heq; rw [htoki] at htok; simp at htok
      exact Deflate.tokenFreqs_go_distCode_pos tokens len dist dCode dExtraN dExtraV
        (litFreqs.set! b'.toNat (litFreqs[b'.toNat]! + 1)) distFreqs (i + 1) j
        (by simp; omega) hdist (by omega) hjlt htok hfdc
    | .reference len' dist' =>
      simp only [htoki]
      by_cases hij : i = j
      · -- This is the token — i = j
        subst hij
        have heq : LZ77Token.reference len' dist' = LZ77Token.reference len dist :=
          htoki.symm.trans htok
        have hlen_eq : len' = len := (LZ77Token.reference.inj heq).1
        have hdist_eq : dist' = dist := (LZ77Token.reference.inj heq).2
        simp only [hlen_eq, hdist_eq, hfdc]
        have hdcode := nativeFindDistCode_idx_bound _ dCode dExtraN dExtraV hfdc
        -- After set, distFreqs[dCode]! ≥ 1
        have hle := (Deflate.tokenFreqs_go_mono tokens
          (match findLengthCode len with
           | some (lIdx, _, _) => litFreqs.set! (lIdx + 257) (litFreqs[lIdx + 257]! + 1)
           | none => litFreqs)
          (distFreqs.set! dCode (distFreqs[dCode]! + 1)) (i + 1) dCode
          (by cases findLengthCode len with
            | none => exact hlit
            | some p => obtain ⟨lIdx, _, _⟩ := p; simp; omega)
          (by simp; omega)).2
          (by omega)
        have hset : (distFreqs.set! dCode (distFreqs[dCode]! + 1))[dCode]! ≥ 1 := by
          rw [Array.getElem!_set!_self distFreqs _ _ (by omega)]; omega
        exact Nat.le_trans hset hle
      · -- Not this token, recurse
        exact Deflate.tokenFreqs_go_distCode_pos tokens len dist dCode dExtraN dExtraV _ _ (i + 1) j
          (by cases findLengthCode len' with
            | none => exact hlit
            | some p => obtain ⟨lIdx, _, _⟩ := p; simp; omega)
          (by cases findDistCode dist' with
            | none => exact hdist
            | some p => obtain ⟨dIdx, _, _⟩ := p; simp; omega)
          (by omega) hjlt htok hfdc
  · omega
termination_by tokens.size - i

/-- `tokenFreqs` counts distance code `dCode` if `.reference len dist` appears
    in `tokens` and `findDistCode dist = some (dCode, ...)`. -/
protected theorem tokenFreqs_distCode_pos (tokens : Array LZ77Token)
    (len dist : Nat) (dCode dExtraN : Nat) (dExtraV : UInt32)
    (hmem : LZ77Token.reference len dist ∈ tokens.toList)
    (hfdc : findDistCode dist = some (dCode, dExtraN, dExtraV)) :
    (tokenFreqs tokens).2[dCode]! ≥ 1 := by
  have ⟨j, hjlt, htok⟩ := List.mem_iff_getElem.mp hmem
  simp only [Array.length_toList] at hjlt
  have htok' : tokens[j] = .reference len dist := by
    simp only [Array.getElem_toList] at htok; exact htok
  exact Deflate.tokenFreqs_go_distCode_pos tokens len dist dCode dExtraN dExtraV _ _ 0 j
    (by simp) (by simp) (by omega) hjlt htok' hfdc

/-- Converting a List Nat with elements ≤ 15 to Array UInt8 preserves bounds. -/
protected theorem toUInt8Array_le (lens : List Nat) (hbound : ∀ x ∈ lens, x ≤ 15) :
    ∀ j, j < (lens.toArray.map Nat.toUInt8).size →
      (lens.toArray.map Nat.toUInt8)[j]!.toNat ≤ 15 := by
  intro k hk
  rw [getElem!_pos _ k hk]
  simp only [Array.getElem_map, Array.size_map, List.size_toArray] at hk ⊢
  simp only [UInt8.toNat, Nat.toUInt8, UInt8.ofNat, BitVec.toNat_ofNat]
  exact Nat.le_trans (Nat.mod_le _ _) (hbound _ (List.getElem_mem hk))

/-- If `freqs[sym]! ≥ 1` and `sym < freqs.size`, the frequency pairs list
    contains a witness with matching symbol and positive frequency. -/
protected theorem freqPairs_witness (freqs : Array Nat) (sym : Nat)
    (hsym : sym < freqs.size) (hfreq : freqs[sym]! ≥ 1) :
    ∃ p ∈ (List.range freqs.size).map fun i => (i, freqs[i]!),
      p.1 = sym ∧ p.2 > 0 :=
  ⟨(sym, freqs[sym]!), by
    simp only [List.mem_map, List.mem_range]
    exact ⟨sym, hsym, rfl⟩, rfl, hfreq⟩

end Zip.Native.Deflate
