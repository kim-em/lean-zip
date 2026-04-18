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

namespace Zip.Native.Deflate

/-- Incrementing one counter in a Nat frequency array (proven-bounds form)
cannot decrease any entry. -/
private theorem getElem!_le_set!_incr (arr : Array Nat) (k idx : Nat) (hk : k < arr.size) :
    arr[idx]! ≤ (arr.set! k (arr[k] + 1))[idx]! := by
  rw [show arr[k] = arr[k]! from (getElem!_pos arr k hk).symm]
  by_cases heq : k = idx
  · subst heq
    rw [Array.getElem!_set!_self arr _ _ hk]
    omega
  · rw [Array.getElem!_set!_ne arr _ _ _ heq]
    omega

/-- `tokenFreqs.go` preserves array sizes. The size invariants are now
threaded through `go` itself (via `hlit`, `hdist`), so the output sizes
are 286 and 30 by construction; this theorem just exposes them. -/
protected theorem tokenFreqs_go_sizes (tokens : Array LZ77Token)
    (litFreqs distFreqs : Array Nat)
    (hlit : litFreqs.size = 286) (hdist : distFreqs.size = 30) (i : Nat) :
    (tokenFreqs.go tokens litFreqs distFreqs hlit hdist i).1.size = 286 ∧
    (tokenFreqs.go tokens litFreqs distFreqs hlit hdist i).2.size = 30 := by
  unfold tokenFreqs.go
  split
  · rename_i h
    match htok : tokens[i] with
    | .literal b =>
      simp only []
      exact Deflate.tokenFreqs_go_sizes tokens _ _ _ _ (i + 1)
    | .reference len dist =>
      simp only []
      split
      · split
        · exact Deflate.tokenFreqs_go_sizes tokens _ _ _ _ (i + 1)
        · exact Deflate.tokenFreqs_go_sizes tokens _ _ _ _ (i + 1)
      · split
        · exact Deflate.tokenFreqs_go_sizes tokens _ _ _ _ (i + 1)
        · exact Deflate.tokenFreqs_go_sizes tokens _ _ _ _ (i + 1)
  · exact ⟨hlit, hdist⟩
termination_by tokens.size - i

/-- `tokenFreqs` produces arrays of size 286 and 30. -/
protected theorem tokenFreqs_sizes (tokens : Array LZ77Token) :
    (tokenFreqs tokens).1.size = 286 ∧ (tokenFreqs tokens).2.size = 30 := by
  simp only [tokenFreqs]
  exact Deflate.tokenFreqs_go_sizes tokens _ _ _ _ 0

/-- `tokenFreqs.go` only increases frequency values. -/
protected theorem tokenFreqs_go_mono (tokens : Array LZ77Token)
    (litFreqs distFreqs : Array Nat)
    (hlit : litFreqs.size = 286) (hdist : distFreqs.size = 30) (i idx : Nat) :
    (idx < 286 →
      litFreqs[idx]! ≤ (tokenFreqs.go tokens litFreqs distFreqs hlit hdist i).1[idx]!) ∧
    (idx < 30 →
      distFreqs[idx]! ≤ (tokenFreqs.go tokens litFreqs distFreqs hlit hdist i).2[idx]!) := by
  unfold tokenFreqs.go
  split
  · rename_i h
    match htok : tokens[i] with
    | .literal b =>
      simp only []
      have hb : b.toNat < litFreqs.size := by have := UInt8.toNat_lt b; omega
      have ih := Deflate.tokenFreqs_go_mono tokens
        (litFreqs.set! b.toNat (litFreqs[b.toNat]'hb + 1)) distFreqs
        (by rw [Array.size_set!]; omega) hdist (i + 1) idx
      refine ⟨fun hidx => ?_, ih.2⟩
      exact Nat.le_trans
        (getElem!_le_set!_incr litFreqs b.toNat idx hb) (ih.1 hidx)
    | .reference length distance =>
      simp only []
      split
      · -- findLengthCode = none
        rename_i hflc
        split
        · -- findDistCode = none
          exact Deflate.tokenFreqs_go_mono tokens litFreqs distFreqs hlit hdist (i + 1) idx
        · -- findDistCode = some
          rename_i dIdx _ _ hfdc
          have hdIdx := nativeFindDistCode_idx_bound _ dIdx _ _ hfdc
          have hd : dIdx < distFreqs.size := by omega
          have ih := Deflate.tokenFreqs_go_mono tokens litFreqs
            (distFreqs.set! dIdx (distFreqs[dIdx]'hd + 1))
            hlit (by rw [Array.size_set!]; omega) (i + 1) idx
          refine ⟨ih.1, fun hidx => ?_⟩
          exact Nat.le_trans
            (getElem!_le_set!_incr distFreqs dIdx idx hd) (ih.2 hidx)
      · -- findLengthCode = some
        rename_i lIdx _ _ hflc
        have hlIdx := nativeFindLengthCode_idx_bound _ lIdx _ _ hflc
        have hsym : lIdx + 257 < litFreqs.size := by omega
        split
        · -- findDistCode = none
          have ih := Deflate.tokenFreqs_go_mono tokens
            (litFreqs.set! (lIdx + 257) (litFreqs[lIdx + 257]'hsym + 1)) distFreqs
            (by rw [Array.size_set!]; omega) hdist (i + 1) idx
          refine ⟨fun hidx => ?_, ih.2⟩
          exact Nat.le_trans
            (getElem!_le_set!_incr litFreqs _ idx hsym) (ih.1 hidx)
        · -- findDistCode = some
          rename_i dIdx _ _ hfdc
          have hdIdx := nativeFindDistCode_idx_bound _ dIdx _ _ hfdc
          have hd : dIdx < distFreqs.size := by omega
          have ih := Deflate.tokenFreqs_go_mono tokens
            (litFreqs.set! (lIdx + 257) (litFreqs[lIdx + 257]'hsym + 1))
            (distFreqs.set! dIdx (distFreqs[dIdx]'hd + 1))
            (by rw [Array.size_set!]; omega) (by rw [Array.size_set!]; omega)
            (i + 1) idx
          refine ⟨fun hidx => ?_, fun hidx => ?_⟩
          · exact Nat.le_trans
              (getElem!_le_set!_incr litFreqs _ idx hsym) (ih.1 hidx)
          · exact Nat.le_trans
              (getElem!_le_set!_incr distFreqs _ idx hd) (ih.2 hidx)
  · exact ⟨fun _ => Nat.le.refl, fun _ => Nat.le.refl⟩
termination_by tokens.size - i

/-- `tokenFreqs` counts end-of-block (symbol 256) with frequency ≥ 1. -/
protected theorem tokenFreqs_eob_pos (tokens : Array LZ77Token) :
    (tokenFreqs tokens).1[256]! ≥ 1 := by
  -- tokenFreqs.go monotonically increases frequency values
  -- Initial lit array has [256]! = 1, so result has [256]! ≥ 1
  have hmono : ((Array.replicate 286 (0 : Nat)).set! 256 1)[256]! ≤
      (tokenFreqs tokens).1[256]! :=
    (Deflate.tokenFreqs_go_mono tokens _ _
      (by rw [Array.size_set!, Array.size_replicate])
      (by rw [Array.size_replicate]) 0 256).1 (by omega)
  have h256 : ((Array.replicate 286 (0 : Nat)).set! 256 1)[256]! = 1 :=
    Array.getElem!_set!_self _ _ _ (by rw [Array.size_replicate]; omega)
  omega

/-- `tokenFreqs.go` produces positive lit frequency for literal `b` at position `j ≥ i`. -/
protected theorem tokenFreqs_go_literal_pos (tokens : Array LZ77Token) (b : UInt8)
    (litFreqs distFreqs : Array Nat)
    (hlit : litFreqs.size = 286) (hdist : distFreqs.size = 30) (i j : Nat)
    (hj : j ≥ i) (hjlt : j < tokens.size) (htok : tokens[j] = .literal b) :
    (tokenFreqs.go tokens litFreqs distFreqs hlit hdist i).1[b.toNat]! ≥ 1 := by
  unfold tokenFreqs.go
  split
  · rename_i h
    match htoki : tokens[i] with
    | .literal b' =>
      simp only []
      have hb' : b'.toNat < litFreqs.size := by have := UInt8.toNat_lt b'; omega
      by_cases hij : i = j
      · -- This is the token we're looking for
        subst hij; simp only [htoki] at htok
        have hbeq : b' = b := LZ77Token.literal.inj htok
        rw [hbeq] at hb' ⊢
        -- After set, litFreqs[b.toNat]! ≥ 1
        have hle := (Deflate.tokenFreqs_go_mono tokens
          (litFreqs.set! b.toNat (litFreqs[b.toNat]'hb' + 1)) distFreqs
          (by rw [Array.size_set!]; omega) hdist (i + 1) b.toNat).1
          (by have := UInt8.toNat_lt b; omega)
        have hset : (litFreqs.set! b.toNat (litFreqs[b.toNat]'hb' + 1))[b.toNat]! ≥ 1 := by
          rw [Array.getElem!_set!_self litFreqs _ _ hb']; omega
        omega
      · -- Not this token yet, recurse
        exact Deflate.tokenFreqs_go_literal_pos tokens b
          (litFreqs.set! b'.toNat (litFreqs[b'.toNat]'hb' + 1)) distFreqs
          (by rw [Array.size_set!]; omega) hdist (i + 1) j (by omega) hjlt htok
    | .reference len' dist' =>
      simp only []
      have hij : i ≠ j := by intro heq; subst heq; rw [htoki] at htok; exact nomatch htok
      split
      · -- findLengthCode = none
        split
        · -- findDistCode = none
          exact Deflate.tokenFreqs_go_literal_pos tokens b litFreqs distFreqs hlit hdist
            (i + 1) j (by omega) hjlt htok
        · rename_i dIdx _ _ hfdc
          have hdIdx := nativeFindDistCode_idx_bound _ _ _ _ hfdc
          have hd : dIdx < distFreqs.size := by omega
          exact Deflate.tokenFreqs_go_literal_pos tokens b litFreqs
            (distFreqs.set! dIdx (distFreqs[dIdx]'hd + 1))
            hlit (by rw [Array.size_set!]; omega) (i + 1) j (by omega) hjlt htok
      · rename_i lIdx _ _ hflc
        have hlIdx := nativeFindLengthCode_idx_bound _ _ _ _ hflc
        have hsym : lIdx + 257 < litFreqs.size := by omega
        split
        · exact Deflate.tokenFreqs_go_literal_pos tokens b
            (litFreqs.set! (lIdx + 257) (litFreqs[lIdx + 257]'hsym + 1)) distFreqs
            (by rw [Array.size_set!]; omega) hdist (i + 1) j (by omega) hjlt htok
        · rename_i dIdx _ _ hfdc
          have hdIdx := nativeFindDistCode_idx_bound _ _ _ _ hfdc
          have hd : dIdx < distFreqs.size := by omega
          exact Deflate.tokenFreqs_go_literal_pos tokens b
            (litFreqs.set! (lIdx + 257) (litFreqs[lIdx + 257]'hsym + 1))
            (distFreqs.set! dIdx (distFreqs[dIdx]'hd + 1))
            (by rw [Array.size_set!]; omega) (by rw [Array.size_set!]; omega)
            (i + 1) j (by omega) hjlt htok
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
  exact Deflate.tokenFreqs_go_literal_pos tokens b _ _
    (by rw [Array.size_set!, Array.size_replicate])
    (by rw [Array.size_replicate]) 0 j (by omega) hjlt htok'

/-- `tokenFreqs.go` produces positive lit frequency for length code from ref at position `j ≥ i`. -/
protected theorem tokenFreqs_go_lengthCode_pos (tokens : Array LZ77Token)
    (len dist : Nat) (idx extraN : Nat) (extraV : UInt32)
    (litFreqs distFreqs : Array Nat)
    (hlit : litFreqs.size = 286) (hdist : distFreqs.size = 30) (i j : Nat)
    (hj : j ≥ i) (hjlt : j < tokens.size)
    (htok : tokens[j] = .reference len dist)
    (hflc : findLengthCode len = some (idx, extraN, extraV)) :
    (tokenFreqs.go tokens litFreqs distFreqs hlit hdist i).1[257 + idx]! ≥ 1 := by
  unfold tokenFreqs.go
  split
  · rename_i h
    match htoki : tokens[i] with
    | .literal b' =>
      simp only []
      have hij : i ≠ j := by intro heq; subst heq; rw [htoki] at htok; exact nomatch htok
      have hb' : b'.toNat < litFreqs.size := by have := UInt8.toNat_lt b'; omega
      exact Deflate.tokenFreqs_go_lengthCode_pos tokens len dist idx extraN extraV
        (litFreqs.set! b'.toNat (litFreqs[b'.toNat]'hb' + 1)) distFreqs
        (by rw [Array.size_set!]; omega) hdist (i + 1) j (by omega) hjlt htok hflc
    | .reference len' dist' =>
      simp only []
      have hidx := nativeFindLengthCode_idx_bound _ idx extraN extraV hflc
      by_cases hij : i = j
      · -- This is the token — i = j
        subst hij
        have ⟨hlen_eq, _hdist_eq⟩ := LZ77Token.reference.inj (htoki.symm.trans htok)
        subst hlen_eq
        have hsym : idx + 257 < litFreqs.size := by omega
        -- The body chooses on findDistCode dist'. Either way, the lit array
        -- becomes `litFreqs.set! (idx + 257) (litFreqs[idx + 257] + 1)` and the
        -- monotonicity result gives ≥ 1 at position 257 + idx.
        have hset_ge : ∀ (dF : Array Nat) (hd : dF.size = 30),
            (Deflate.tokenFreqs.go tokens
              (litFreqs.set! (idx + 257) (litFreqs[idx + 257]'hsym + 1)) dF
              (by rw [Array.size_set!]; omega) hd (i + 1)).1[257 + idx]! ≥ 1 := by
          intro dF hd
          have hle := (Deflate.tokenFreqs_go_mono tokens
            (litFreqs.set! (idx + 257) (litFreqs[idx + 257]'hsym + 1)) dF
            (by rw [Array.size_set!]; omega) hd (i + 1) (257 + idx)).1 (by omega)
          have hset : (litFreqs.set! (idx + 257)
              (litFreqs[idx + 257]'hsym + 1))[257 + idx]! ≥ 1 := by
            rw [show 257 + idx = idx + 257 from by omega,
              Array.getElem!_set!_self litFreqs _ _ hsym]; omega
          exact Nat.le_trans hset hle
        split
        · rename_i hflc'
          rw [hflc'] at hflc; nomatch hflc
        · rename_i lIdx eN eV hflc'
          have heq : (lIdx, eN, eV) = (idx, extraN, extraV) :=
            Option.some.inj (hflc'.symm.trans hflc)
          obtain ⟨rfl, rfl, rfl⟩ := heq
          split
          · exact hset_ge distFreqs hdist
          · rename_i dIdx _ _ hfdc
            have hdIdx := nativeFindDistCode_idx_bound _ _ _ _ hfdc
            have hd : dIdx < distFreqs.size := by omega
            exact hset_ge _ (by rw [Array.size_set!]; omega)
      · -- Not this token, recurse
        split
        · split
          · exact Deflate.tokenFreqs_go_lengthCode_pos tokens len dist idx extraN extraV
              litFreqs distFreqs hlit hdist (i + 1) j (by omega) hjlt htok hflc
          · rename_i dIdx _ _ hfdc
            have hdIdx := nativeFindDistCode_idx_bound _ _ _ _ hfdc
            have hd : dIdx < distFreqs.size := by omega
            exact Deflate.tokenFreqs_go_lengthCode_pos tokens len dist idx extraN extraV
              litFreqs (distFreqs.set! dIdx (distFreqs[dIdx]'hd + 1))
              hlit (by rw [Array.size_set!]; omega) (i + 1) j (by omega) hjlt htok hflc
        · rename_i lIdx _ _ hflc'
          have hlIdx := nativeFindLengthCode_idx_bound _ _ _ _ hflc'
          have hsym' : lIdx + 257 < litFreqs.size := by omega
          split
          · exact Deflate.tokenFreqs_go_lengthCode_pos tokens len dist idx extraN extraV
              (litFreqs.set! (lIdx + 257) (litFreqs[lIdx + 257]'hsym' + 1)) distFreqs
              (by rw [Array.size_set!]; omega) hdist (i + 1) j (by omega) hjlt htok hflc
          · rename_i dIdx _ _ hfdc
            have hdIdx := nativeFindDistCode_idx_bound _ _ _ _ hfdc
            have hd : dIdx < distFreqs.size := by omega
            exact Deflate.tokenFreqs_go_lengthCode_pos tokens len dist idx extraN extraV
              (litFreqs.set! (lIdx + 257) (litFreqs[lIdx + 257]'hsym' + 1))
              (distFreqs.set! dIdx (distFreqs[dIdx]'hd + 1))
              (by rw [Array.size_set!]; omega) (by rw [Array.size_set!]; omega)
              (i + 1) j (by omega) hjlt htok hflc
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
  exact Deflate.tokenFreqs_go_lengthCode_pos tokens len dist idx extraN extraV _ _
    (by rw [Array.size_set!, Array.size_replicate])
    (by rw [Array.size_replicate]) 0 j (by omega) hjlt htok' hflc

/-- `tokenFreqs.go` produces positive dist frequency for dist code from ref at position `j ≥ i`. -/
protected theorem tokenFreqs_go_distCode_pos (tokens : Array LZ77Token)
    (len dist : Nat) (dCode dExtraN : Nat) (dExtraV : UInt32)
    (litFreqs distFreqs : Array Nat)
    (hlit : litFreqs.size = 286) (hdist : distFreqs.size = 30) (i j : Nat)
    (hj : j ≥ i) (hjlt : j < tokens.size)
    (htok : tokens[j] = .reference len dist)
    (hfdc : findDistCode dist = some (dCode, dExtraN, dExtraV)) :
    (tokenFreqs.go tokens litFreqs distFreqs hlit hdist i).2[dCode]! ≥ 1 := by
  unfold tokenFreqs.go
  split
  · rename_i h
    match htoki : tokens[i] with
    | .literal b' =>
      simp only []
      have hij : i ≠ j := by intro heq; subst heq; rw [htoki] at htok; exact nomatch htok
      have hb' : b'.toNat < litFreqs.size := by have := UInt8.toNat_lt b'; omega
      exact Deflate.tokenFreqs_go_distCode_pos tokens len dist dCode dExtraN dExtraV
        (litFreqs.set! b'.toNat (litFreqs[b'.toNat]'hb' + 1)) distFreqs
        (by rw [Array.size_set!]; omega) hdist (i + 1) j (by omega) hjlt htok hfdc
    | .reference len' dist' =>
      simp only []
      have hdcode := nativeFindDistCode_idx_bound _ dCode dExtraN dExtraV hfdc
      by_cases hij : i = j
      · -- This is the token — i = j
        subst hij
        have ⟨_hlen_eq, hdist_eq⟩ := LZ77Token.reference.inj (htoki.symm.trans htok)
        subst hdist_eq
        -- The body chooses on findLengthCode len'. Either way, the dist array
        -- becomes `distFreqs.set! dCode (distFreqs[dCode] + 1)` and the
        -- monotonicity result gives ≥ 1 at position dCode.
        have hd : dCode < distFreqs.size := by omega
        have hset_ge : ∀ (lF : Array Nat) (hl : lF.size = 286),
            (Deflate.tokenFreqs.go tokens lF
              (distFreqs.set! dCode (distFreqs[dCode]'hd + 1))
              hl (by rw [Array.size_set!]; omega) (i + 1)).2[dCode]! ≥ 1 := by
          intro lF hl
          have hle := (Deflate.tokenFreqs_go_mono tokens lF
            (distFreqs.set! dCode (distFreqs[dCode]'hd + 1))
            hl (by rw [Array.size_set!]; omega) (i + 1) dCode).2 (by omega)
          have hset : (distFreqs.set! dCode (distFreqs[dCode]'hd + 1))[dCode]! ≥ 1 := by
            rw [Array.getElem!_set!_self distFreqs _ _ hd]; omega
          exact Nat.le_trans hset hle
        -- Open the outer match on findLengthCode len. We end up calling go
        -- with the relevant lit array and the updated dist array.
        split
        · -- findLengthCode = none branch:  go uses (distFreqs.set! dCode ..) directly.
          split
          · rename_i hfdc'
            rw [hfdc'] at hfdc; nomatch hfdc
          · rename_i dIdx' eN' eV' hfdc'
            have heq : (dIdx', eN', eV') = (dCode, dExtraN, dExtraV) :=
              Option.some.inj (hfdc'.symm.trans hfdc)
            obtain ⟨rfl, rfl, rfl⟩ := heq
            exact hset_ge litFreqs hlit
        · rename_i lIdx _ _ hflc
          have hlIdx := nativeFindLengthCode_idx_bound _ _ _ _ hflc
          have hsym : lIdx + 257 < litFreqs.size := by omega
          split
          · rename_i hfdc'
            rw [hfdc'] at hfdc; nomatch hfdc
          · rename_i dIdx' eN' eV' hfdc'
            have heq : (dIdx', eN', eV') = (dCode, dExtraN, dExtraV) :=
              Option.some.inj (hfdc'.symm.trans hfdc)
            obtain ⟨rfl, rfl, rfl⟩ := heq
            exact hset_ge _ (by rw [Array.size_set!]; omega)
      · -- Not this token, recurse
        split
        · split
          · exact Deflate.tokenFreqs_go_distCode_pos tokens len dist dCode dExtraN dExtraV
              litFreqs distFreqs hlit hdist (i + 1) j (by omega) hjlt htok hfdc
          · rename_i dIdx _ _ hfdc'
            have hdIdx := nativeFindDistCode_idx_bound _ _ _ _ hfdc'
            have hd : dIdx < distFreqs.size := by omega
            exact Deflate.tokenFreqs_go_distCode_pos tokens len dist dCode dExtraN dExtraV
              litFreqs (distFreqs.set! dIdx (distFreqs[dIdx]'hd + 1))
              hlit (by rw [Array.size_set!]; omega) (i + 1) j (by omega) hjlt htok hfdc
        · rename_i lIdx _ _ hflc'
          have hlIdx := nativeFindLengthCode_idx_bound _ _ _ _ hflc'
          have hsym' : lIdx + 257 < litFreqs.size := by omega
          split
          · exact Deflate.tokenFreqs_go_distCode_pos tokens len dist dCode dExtraN dExtraV
              (litFreqs.set! (lIdx + 257) (litFreqs[lIdx + 257]'hsym' + 1)) distFreqs
              (by rw [Array.size_set!]; omega) hdist (i + 1) j (by omega) hjlt htok hfdc
          · rename_i dIdx _ _ hfdc'
            have hdIdx := nativeFindDistCode_idx_bound _ _ _ _ hfdc'
            have hd : dIdx < distFreqs.size := by omega
            exact Deflate.tokenFreqs_go_distCode_pos tokens len dist dCode dExtraN dExtraV
              (litFreqs.set! (lIdx + 257) (litFreqs[lIdx + 257]'hsym' + 1))
              (distFreqs.set! dIdx (distFreqs[dIdx]'hd + 1))
              (by rw [Array.size_set!]; omega) (by rw [Array.size_set!]; omega)
              (i + 1) j (by omega) hjlt htok hfdc
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
  exact Deflate.tokenFreqs_go_distCode_pos tokens len dist dCode dExtraN dExtraV _ _
    (by rw [Array.size_set!, Array.size_replicate])
    (by rw [Array.size_replicate]) 0 j (by omega) hjlt htok' hfdc

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
    ∃ p ∈ freqsToPairs freqs, p.1 = sym ∧ p.2 > 0 := by
  refine ⟨(sym, freqs[sym]'hsym), ?_, rfl, ?_⟩
  · simp only [freqsToPairs, List.mem_pmap, List.mem_range]
    exact ⟨sym, hsym, rfl⟩
  · rw [getElem!_pos freqs sym hsym] at hfreq; exact hfreq

end Zip.Native.Deflate
