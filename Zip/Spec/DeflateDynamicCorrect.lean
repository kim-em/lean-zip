import Zip.Spec.DeflateDynamicEmit
import Zip.Spec.DeflateDynamicHeader

/-!
# Native DEFLATE Dynamic Huffman Correctness

This file proves that `deflateDynamic` (dynamic Huffman compressor) produces
a valid DEFLATE bitstream, and that `inflate ∘ deflateDynamic` recovers the
original data.

## Key results

- `deflateDynamic_spec`: the dynamic compressor output matches spec encoding
- `inflate_deflateDynamic`: full roundtrip correctness
-/

namespace Zip.Native.Deflate

/-! ## tokenFreqs properties -/

private theorem findTableCode_go_idx_bound (baseTable : Array UInt16)
    (extraTable : Array UInt8) (value i idx : Nat) (extraN : Nat) (extraV : UInt32)
    (h : findTableCode.go baseTable extraTable value i = some (idx, extraN, extraV)) :
    idx < baseTable.size := by
  unfold findTableCode.go at h
  split at h
  · split at h
    · simp at h; omega
    · exact findTableCode_go_idx_bound baseTable extraTable value (i + 1) idx extraN extraV h
  · split at h
    · simp at h; omega
    · simp at h
termination_by baseTable.size - i

private theorem native_findLengthCode_idx_bound (len idx : Nat) (extraN : Nat) (extraV : UInt32)
    (h : findLengthCode len = some (idx, extraN, extraV)) :
    idx < 29 := by
  have := findTableCode_go_idx_bound Inflate.lengthBase Inflate.lengthExtra len 0 idx extraN extraV h
  simp [Inflate.lengthBase] at this
  exact this

private theorem native_findDistCode_code_bound (dist dCode : Nat) (dExtraN : Nat) (dExtraV : UInt32)
    (h : findDistCode dist = some (dCode, dExtraN, dExtraV)) :
    dCode < 30 := by
  have := findTableCode_go_idx_bound Inflate.distBase Inflate.distExtra dist 0 dCode dExtraN dExtraV h
  simp [Inflate.distBase] at this
  exact this

/-- `tokenFreqs.go` preserves array sizes. -/
private theorem tokenFreqs_go_sizes (tokens : Array LZ77Token)
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
      apply tokenFreqs_go_sizes
      · simp; omega
      · exact hdist
    | .reference len dist =>
      simp only [htok]
      apply tokenFreqs_go_sizes
      · cases findLengthCode len with
        | none => exact hlit
        | some p => obtain ⟨idx, _, _⟩ := p; simp; omega
      · cases findDistCode dist with
        | none => exact hdist
        | some p => obtain ⟨dIdx, _, _⟩ := p; simp; omega
  · exact ⟨hlit, hdist⟩
termination_by tokens.size - i

/-- `tokenFreqs` produces arrays of size 286 and 30. -/
private theorem tokenFreqs_sizes (tokens : Array LZ77Token) :
    (tokenFreqs tokens).1.size = 286 ∧ (tokenFreqs tokens).2.size = 30 := by
  simp only [tokenFreqs]
  apply tokenFreqs_go_sizes
  · simp
  · simp

/-- `tokenFreqs.go` only increases frequency values. -/
private theorem tokenFreqs_go_mono (tokens : Array LZ77Token)
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
      have ih := tokenFreqs_go_mono tokens
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
            have ih := tokenFreqs_go_mono tokens litFreqs distFreqs (i + 1) idx hlit hdist
            exact ih.1 hidx
          | some p =>
            obtain ⟨dIdx, dN, dV⟩ := p
            have ih := tokenFreqs_go_mono tokens litFreqs
              (distFreqs.set! dIdx (distFreqs[dIdx]! + 1)) (i + 1) idx
              hlit (by simp; omega)
            exact ih.1 hidx
        | some p =>
          obtain ⟨lIdx, lN, lV⟩ := p
          cases hfdc : findDistCode distance with
          | none =>
            have ih := tokenFreqs_go_mono tokens
              (litFreqs.set! (lIdx + 257) (litFreqs[lIdx + 257]! + 1)) distFreqs (i + 1) idx
              (by simp; omega) hdist
            have hlIdx := native_findLengthCode_idx_bound _ lIdx lN lV hflc
            exact Nat.le_trans (Array.getElem!_le_set!_incr litFreqs _ idx (by omega)) (ih.1 hidx)
          | some q =>
            obtain ⟨dIdx, dN, dV⟩ := q
            have hlIdx := native_findLengthCode_idx_bound _ lIdx lN lV hflc
            have ih := tokenFreqs_go_mono tokens
              (litFreqs.set! (lIdx + 257) (litFreqs[lIdx + 257]! + 1))
              (distFreqs.set! dIdx (distFreqs[dIdx]! + 1)) (i + 1) idx
              (by simp; omega) (by simp; omega)
            exact Nat.le_trans (Array.getElem!_le_set!_incr litFreqs _ idx (by omega)) (ih.1 hidx)
      · intro hidx
        cases hflc : findLengthCode length with
        | none =>
          cases hfdc : findDistCode distance with
          | none =>
            have ih := tokenFreqs_go_mono tokens litFreqs distFreqs (i + 1) idx hlit hdist
            exact ih.2 hidx
          | some p =>
            obtain ⟨dIdx, dN, dV⟩ := p
            have hdIdx := native_findDistCode_code_bound _ dIdx dN dV hfdc
            have ih := tokenFreqs_go_mono tokens litFreqs
              (distFreqs.set! dIdx (distFreqs[dIdx]! + 1)) (i + 1) idx
              hlit (by simp; omega)
            exact Nat.le_trans (Array.getElem!_le_set!_incr distFreqs dIdx idx (by omega)) (ih.2 hidx)
        | some p =>
          obtain ⟨lIdx, lN, lV⟩ := p
          cases hfdc : findDistCode distance with
          | none =>
            have ih := tokenFreqs_go_mono tokens
              (litFreqs.set! (lIdx + 257) (litFreqs[lIdx + 257]! + 1)) distFreqs (i + 1) idx
              (by simp; omega) hdist
            exact ih.2 hidx
          | some q =>
            obtain ⟨dIdx, dN, dV⟩ := q
            have hdIdx := native_findDistCode_code_bound _ dIdx dN dV hfdc
            have ih := tokenFreqs_go_mono tokens
              (litFreqs.set! (lIdx + 257) (litFreqs[lIdx + 257]! + 1))
              (distFreqs.set! dIdx (distFreqs[dIdx]! + 1)) (i + 1) idx
              (by simp; omega) (by simp; omega)
            exact Nat.le_trans (Array.getElem!_le_set!_incr distFreqs dIdx idx (by omega)) (ih.2 hidx)
  · exact ⟨fun _ => Nat.le.refl, fun _ => Nat.le.refl⟩
termination_by tokens.size - i

set_option maxRecDepth 1024 in
/-- `tokenFreqs` counts end-of-block (symbol 256) with frequency ≥ 1. -/
private theorem tokenFreqs_eob_pos (tokens : Array LZ77Token) :
    (tokenFreqs tokens).1[256]! ≥ 1 := by
  -- tokenFreqs.go monotonically increases frequency values
  -- Initial lit array has [256]! = 1, so result has [256]! ≥ 1
  have hmono : ((Array.replicate 286 (0 : Nat)).set! 256 1)[256]! ≤
      (tokenFreqs tokens).1[256]! :=
    (tokenFreqs_go_mono tokens _ _ 0 256 (by simp) (by simp)).1 (by omega)
  have h256 : ((Array.replicate 286 (0 : Nat)).set! 256 1)[256]! = 1 :=
    Array.getElem!_set!_self _ _ _ (by simp)
  omega

/-- `tokenFreqs.go` produces positive lit frequency for literal `b` at position `j ≥ i`. -/
private theorem tokenFreqs_go_literal_pos (tokens : Array LZ77Token) (b : UInt8)
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
        have hle := (tokenFreqs_go_mono tokens
          (litFreqs.set! b.toNat (litFreqs[b.toNat]! + 1)) distFreqs (i + 1) b.toNat
          (by simp; omega) hdist).1 (by have := UInt8.toNat_lt b; omega)
        have hblt := UInt8.toNat_lt b
        have hset : (litFreqs.set! b.toNat (litFreqs[b.toNat]! + 1))[b.toNat]! ≥ 1 := by
          rw [Array.getElem!_set!_self litFreqs _ _ (by omega)]; omega
        omega
      · -- Not this token yet, recurse
        exact tokenFreqs_go_literal_pos tokens b
          (litFreqs.set! b'.toNat (litFreqs[b'.toNat]! + 1)) distFreqs (i + 1) j
          (by simp; omega) hdist (by omega) hjlt htok
    | .reference len' dist' =>
      simp only [htoki]
      have hij : i ≠ j := by intro heq; subst heq; rw [htoki] at htok; simp at htok
      exact tokenFreqs_go_literal_pos tokens b _ _ (i + 1) j
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
private theorem tokenFreqs_literal_pos (tokens : Array LZ77Token) (b : UInt8)
    (hmem : LZ77Token.literal b ∈ tokens.toList) :
    (tokenFreqs tokens).1[b.toNat]! ≥ 1 := by
  have ⟨j, hjlt, htok⟩ := List.mem_iff_getElem.mp hmem
  simp only [Array.length_toList] at hjlt
  have htok' : tokens[j] = .literal b := by
    simp only [Array.getElem_toList] at htok; exact htok
  exact tokenFreqs_go_literal_pos tokens b _ _ 0 j
    (by simp) (by simp) (by omega) hjlt htok'

/-- `tokenFreqs.go` produces positive lit frequency for length code from ref at position `j ≥ i`. -/
private theorem tokenFreqs_go_lengthCode_pos (tokens : Array LZ77Token)
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
      exact tokenFreqs_go_lengthCode_pos tokens len dist idx extraN extraV
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
        have hidx := native_findLengthCode_idx_bound _ idx extraN extraV hflc
        -- After set, litFreqs[257+idx]! ≥ 1
        have hle := (tokenFreqs_go_mono tokens
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
        exact tokenFreqs_go_lengthCode_pos tokens len dist idx extraN extraV _ _ (i + 1) j
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
private theorem tokenFreqs_lengthCode_pos (tokens : Array LZ77Token)
    (len dist : Nat) (idx extraN : Nat) (extraV : UInt32)
    (hmem : LZ77Token.reference len dist ∈ tokens.toList)
    (hflc : findLengthCode len = some (idx, extraN, extraV)) :
    (tokenFreqs tokens).1[257 + idx]! ≥ 1 := by
  have ⟨j, hjlt, htok⟩ := List.mem_iff_getElem.mp hmem
  simp only [Array.length_toList] at hjlt
  have htok' : tokens[j] = .reference len dist := by
    simp only [Array.getElem_toList] at htok; exact htok
  exact tokenFreqs_go_lengthCode_pos tokens len dist idx extraN extraV _ _ 0 j
    (by simp) (by simp) (by omega) hjlt htok' hflc

/-- `tokenFreqs.go` produces positive dist frequency for dist code from ref at position `j ≥ i`. -/
private theorem tokenFreqs_go_distCode_pos (tokens : Array LZ77Token)
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
      exact tokenFreqs_go_distCode_pos tokens len dist dCode dExtraN dExtraV
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
        have hdcode := native_findDistCode_code_bound _ dCode dExtraN dExtraV hfdc
        -- After set, distFreqs[dCode]! ≥ 1
        have hle := (tokenFreqs_go_mono tokens
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
        exact tokenFreqs_go_distCode_pos tokens len dist dCode dExtraN dExtraV _ _ (i + 1) j
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
private theorem tokenFreqs_distCode_pos (tokens : Array LZ77Token)
    (len dist : Nat) (dCode dExtraN : Nat) (dExtraV : UInt32)
    (hmem : LZ77Token.reference len dist ∈ tokens.toList)
    (hfdc : findDistCode dist = some (dCode, dExtraN, dExtraV)) :
    (tokenFreqs tokens).2[dCode]! ≥ 1 := by
  have ⟨j, hjlt, htok⟩ := List.mem_iff_getElem.mp hmem
  simp only [Array.length_toList] at hjlt
  have htok' : tokens[j] = .reference len dist := by
    simp only [Array.getElem_toList] at htok; exact htok
  exact tokenFreqs_go_distCode_pos tokens len dist dCode dExtraN dExtraV _ _ 0 j
    (by simp) (by simp) (by omega) hjlt htok' hfdc

/-- `deflateDynamic` produces a bytestream whose bits correspond to the
    spec-level dynamic Huffman encoding, plus padding to byte alignment. -/
theorem deflateDynamic_spec (data : ByteArray) :
    ∃ (litLens distLens : List Nat) (headerBits symBits : List Bool),
      Huffman.Spec.ValidLengths litLens 15 ∧
      Huffman.Spec.ValidLengths distLens 15 ∧
      litLens.length ≥ 257 ∧ litLens.length ≤ 288 ∧
      distLens.length ≥ 1 ∧ distLens.length ≤ 32 ∧
      (∀ x ∈ litLens, x ≤ 15) ∧ (∀ x ∈ distLens, x ≤ 15) ∧
      Deflate.Spec.encodeDynamicTrees litLens distLens = some headerBits ∧
      Deflate.Spec.encodeSymbols litLens distLens
        (tokensToSymbols (lz77Greedy data 32768)) = some symBits ∧
      Deflate.Spec.bytesToBits (deflateDynamic data) =
        [true, false, true] ++ headerBits ++ symBits ++
        List.replicate
          ((8 - ([true, false, true] ++ headerBits ++ symBits).length % 8) % 8)
          false := by
  -- Extract the intermediate values from deflateDynamic
  let tokens := lz77Greedy data 32768
  let litFreqs := (tokenFreqs tokens).1
  let distFreqs := (tokenFreqs tokens).2
  let litFreqPairs := (List.range litFreqs.size).map fun i => (i, litFreqs[i]!)
  let distFreqPairs := (List.range distFreqs.size).map fun i => (i, distFreqs[i]!)
  let litLens := Huffman.Spec.computeCodeLengths litFreqPairs 286 15
  let distLens₀ := Huffman.Spec.computeCodeLengths distFreqPairs 30 15
  let distLens := if distLens₀.all (fun x => x == 0) then distLens₀.set 0 1 else distLens₀
  -- Properties of computeCodeLengths
  have hlit_len : litLens.length = 286 :=
    Huffman.Spec.computeCodeLengths_length litFreqPairs 286 15
  have hdist₀_len : distLens₀.length = 30 :=
    Huffman.Spec.computeCodeLengths_length distFreqPairs 30 15
  have hlit_valid : Huffman.Spec.ValidLengths litLens 15 :=
    Huffman.Spec.computeCodeLengths_valid litFreqPairs 286 15 (by omega) (by omega)
  have hlit_bound : ∀ x ∈ litLens, x ≤ 15 :=
    Huffman.Spec.computeCodeLengths_bounded litFreqPairs 286 15 (by omega)
  have hdist₀_valid : Huffman.Spec.ValidLengths distLens₀ 15 :=
    Huffman.Spec.computeCodeLengths_valid distFreqPairs 30 15 (by omega) (by omega)
  have hdist₀_bound : ∀ x ∈ distLens₀, x ≤ 15 :=
    Huffman.Spec.computeCodeLengths_bounded distFreqPairs 30 15 (by omega)
  -- distLens properties (with the fixup)
  have hdist_len : distLens.length = 30 := by
    simp only [distLens]; split
    · rw [List.length_set]; exact hdist₀_len
    · exact hdist₀_len
  have hdist_bound : ∀ x ∈ distLens, x ≤ 15 := by
    intro x hx
    simp only [distLens] at hx; split at hx
    · -- distLens₀.set 0 1
      rw [List.mem_iff_getElem] at hx
      obtain ⟨i, hi, hxi⟩ := hx
      rw [List.length_set] at hi
      by_cases h0 : i = 0
      · subst h0; simp at hxi; omega
      · have hne : ¬(0 = i) := fun h => h0 (h.symm)
        simp [hne] at hxi
        exact hxi ▸ hdist₀_bound _ (List.getElem_mem ..)
    · exact hdist₀_bound x hx
  have hdist_valid : Huffman.Spec.ValidLengths distLens 15 := by
    by_cases hall0 : (distLens₀.all (fun x => x == 0)) = true
    · -- When all entries are 0, setting index 0 to 1 gives ValidLengths
      have hdl : distLens = distLens₀.set 0 1 := by
        simp only [distLens, hall0, ↓reduceIte]
      have hall : ∀ x ∈ distLens₀, x = 0 := by
        intro x hx
        have := List.all_eq_true.mp hall0 x hx
        simp [beq_iff_eq] at this; exact this
      have hrepl : distLens₀ = List.replicate 30 0 := by
        rw [← hdist₀_len]; exact List.eq_replicate_iff.mpr ⟨rfl, hall⟩
      rw [hdl, hrepl]
      constructor
      · intro l hl
        rw [List.mem_iff_getElem] at hl
        obtain ⟨i, hi, hli⟩ := hl
        rw [List.length_set, List.length_replicate] at hi
        by_cases h0 : i = 0
        · subst h0; simp at hli; omega
        · have hne : ¬(0 = i) := fun h => h0 h.symm
          rw [List.getElem_set] at hli
          simp only [hne, ↓reduceIte, List.getElem_replicate] at hli
          omega
      · -- Kraft sum for [1, 0, 0, ..., 0] with 30 entries
        -- filter gives [1], fold gives 2^14 ≤ 2^15
        decide
    · have hdl : distLens = distLens₀ := by
        simp only [distLens, hall0, Bool.false_eq_true, ↓reduceIte]
      rw [hdl]; exact hdist₀_valid
  -- encodeDynamicTrees succeeds
  have henc_trees_some : (Deflate.Spec.encodeDynamicTrees litLens distLens).isSome = true := by
    -- encodeDynamicTrees only fails at the encodeCLEntries step (guards pass)
    simp only [Deflate.Spec.encodeDynamicTrees]
    simp only [guard, show litLens.length ≥ 257 ∧ litLens.length ≤ 288 from ⟨by omega, by omega⟩,
      show distLens.length ≥ 1 ∧ distLens.length ≤ 32 from ⟨by omega, by omega⟩,
      pure, Pure.pure, bind, Option.bind]
    -- Set up CL-level abbreviations
    let allLens := litLens ++ distLens
    let clEntries := Deflate.Spec.rlEncodeLengths allLens
    let clFreqs := Deflate.Spec.clSymbolFreqs clEntries
    let clFreqPairs := (List.range clFreqs.length).map fun i => (i, clFreqs.getD i 0)
    let clLens := Huffman.Spec.computeCodeLengths clFreqPairs 19 7
    let clTable := (Huffman.Spec.allCodes clLens 7).map fun (sym, cw) => (cw, sym)
    -- Show encodeCLEntries succeeds
    have hcl_len : clLens.length = 19 := Huffman.Spec.computeCodeLengths_length clFreqPairs 19 7
    have hcl_bound : ∀ x ∈ clLens, x ≤ 7 :=
      Huffman.Spec.computeCodeLengths_bounded clFreqPairs 19 7 (by omega)
    have hcl_freq_len : clFreqs.length = 19 := Deflate.Spec.clSymbolFreqs_length clEntries
    -- Entry validity: all codes ≤ 18 < 19
    have hentry_valid := Deflate.Spec.rlEncodeLengths_valid allLens (by
      intro x hx; simp only [allLens, List.mem_append] at hx
      cases hx with | inl h => exact hlit_bound x h | inr h => exact hdist_bound x h)
    -- For each entry, its code has nonzero CL code length
    have hall : ∀ p ∈ clEntries,
        p.1 < clLens.length ∧ clLens[p.1]! ≠ 0 ∧ clLens[p.1]! ≤ 7 := by
      intro ⟨code, extra⟩ hp
      have hvalid := hentry_valid (code, extra) hp
      have hcode_lt : code < 19 := by rcases hvalid with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> omega
      refine ⟨by omega, ?_, ?_⟩
      · -- code has nonzero frequency
        have hfreq_pos := Deflate.Spec.clSymbolFreqs_pos clEntries code extra hp hcode_lt
        have hfreq_in : ∃ p ∈ clFreqPairs, p.1 = code ∧ p.2 > 0 := by
          refine ⟨(code, clFreqs.getD code 0), ?_, rfl, hfreq_pos⟩
          simp only [clFreqPairs, List.mem_map, List.mem_range]
          exact ⟨code, by omega, rfl⟩
        exact Huffman.Spec.computeCodeLengths_nonzero clFreqPairs 19 7 (by omega)
          code (by omega) hfreq_in
      · have : code < clLens.length := by omega
        rw [getElem!_pos clLens code this]
        exact hcl_bound _ (List.getElem_mem this)
    have hcl_isSome := Deflate.Spec.encodeCLEntries_isSome clLens 7 clEntries hall
    -- The types should match definitionally since clTable = (allCodes clLens 7).map ...
    change (Deflate.Spec.encodeCLEntries
      ((Huffman.Spec.allCodes clLens 7).map fun p => (p.2, p.1))
      clEntries).isSome = true at hcl_isSome
    cases hcl : Deflate.Spec.encodeCLEntries
        ((Huffman.Spec.allCodes clLens 7).map fun p => (p.2, p.1))
        clEntries with
    | none => simp [hcl] at hcl_isSome
    | some _ => simp
  -- encodeSymbols succeeds
  have henc_syms_some : (Deflate.Spec.encodeSymbols litLens distLens
      (tokensToSymbols tokens)).isSome = true := by
    apply Deflate.Spec.encodeSymbols_isSome_of_all
    intro s hs
    simp only [tokensToSymbols, List.mem_append, List.mem_map, List.mem_cons,
      List.mem_nil_iff, or_false] at hs
    -- Helper: litFreqs.size = 286, distFreqs.size = 30
    have hlit_sz : litFreqs.size = 286 := (tokenFreqs_sizes tokens).1
    have hdist_sz : distFreqs.size = 30 := (tokenFreqs_sizes tokens).2
    cases hs with
    | inl hmapped =>
      obtain ⟨t, ht_mem, ht_eq⟩ := hmapped
      have hbounds := lz77Greedy_encodable data 32768 (by omega) (by omega) t ht_mem
      subst ht_eq
      cases t with
      | literal b =>
        -- Need: encodeLitLen litLens distLens (.literal b) succeeds
        simp only [Deflate.Spec.encodeLitLen]
        have hb_lt : b.toNat < litLens.length := by rw [hlit_len]; have := UInt8.toNat_lt b; omega
        have hfreq := tokenFreqs_literal_pos tokens b ht_mem
        have hfreq_pair : ∃ p ∈ litFreqPairs, p.1 = b.toNat ∧ p.2 > 0 :=
          ⟨(b.toNat, litFreqs[b.toNat]!), by
            simp only [litFreqPairs, List.mem_map, List.mem_range]
            exact ⟨b.toNat, by have := UInt8.toNat_lt b; omega, rfl⟩,
            rfl, hfreq⟩
        have hlen_nz := Huffman.Spec.computeCodeLengths_nonzero litFreqPairs 286 15
          (by omega) b.toNat (by have := UInt8.toNat_lt b; omega) hfreq_pair
        have hlen_le : litLens[b.toNat]! ≤ 15 := by
          rw [getElem!_pos litLens b.toNat hb_lt]
          exact hlit_bound _ (List.getElem_mem hb_lt)
        exact Deflate.Spec.encodeSymbol_fixed_isSome litLens 15 b.toNat hb_lt hlen_nz hlen_le
      | reference len dist =>
        -- Need: encodeLitLen litLens distLens (.reference len dist) succeeds
        simp at hbounds
        simp only [Deflate.Spec.encodeLitLen]
        -- findLengthCode succeeds (spec version)
        have hflc_spec := Deflate.Spec.findLengthCode_isSome len hbounds.1 hbounds.2.1
        cases hlc : Deflate.Spec.findLengthCode len with
        | none => simp [hlc] at hflc_spec
        | some p =>
          obtain ⟨idx, extraN, extraV⟩ := p
          have hidx := Deflate.Spec.findLengthCode_idx_bound len idx extraN extraV hlc
          -- Get native findLengthCode for tokenFreqs_lengthCode_pos
          have hflc_native := Zip.Native.Deflate.findLengthCode_agree len idx extraN extraV hlc
          -- encodeSymbol litTable (257 + idx) succeeds
          have hsym : 257 + idx < litLens.length := by rw [hlit_len]; omega
          have hfreq := tokenFreqs_lengthCode_pos tokens len dist idx extraN
            extraV.toUInt32 ht_mem hflc_native
          have hfreq_pair : ∃ p ∈ litFreqPairs, p.1 = (257 + idx) ∧ p.2 > 0 :=
            ⟨(257 + idx, litFreqs[257 + idx]!), by
              simp only [litFreqPairs, List.mem_map, List.mem_range]
              exact ⟨257 + idx, by omega, rfl⟩,
              rfl, hfreq⟩
          have hlen_nz := Huffman.Spec.computeCodeLengths_nonzero litFreqPairs 286 15
            (by omega) (257 + idx) (by omega) hfreq_pair
          have hlen_le' : litLens[257 + idx]! ≤ 15 := by
            rw [getElem!_pos litLens (257 + idx) hsym]
            exact hlit_bound _ (List.getElem_mem hsym)
          have hlit_enc := Deflate.Spec.encodeSymbol_fixed_isSome litLens 15 (257 + idx)
            hsym hlen_nz hlen_le'
          cases hls : Deflate.Spec.encodeSymbol
              ((Huffman.Spec.allCodes litLens).map fun (s, cw) => (cw, s)) (257 + idx) with
          | none => simp [hls] at hlit_enc
          | some lenBits =>
            -- findDistCode succeeds (spec version)
            have hfdc_spec := Deflate.Spec.findDistCode_isSome dist hbounds.2.2.1 hbounds.2.2.2
            cases hdc : Deflate.Spec.findDistCode dist with
            | none => simp [hdc] at hfdc_spec
            | some q =>
              obtain ⟨dCode, dExtraN, dExtraV⟩ := q
              have hdcode := Deflate.Spec.findDistCode_code_bound dist dCode dExtraN dExtraV hdc
              -- Get native findDistCode for tokenFreqs_distCode_pos
              have hfdc_native := Zip.Native.Deflate.findDistCode_agree dist dCode dExtraN dExtraV hdc
              -- encodeSymbol distTable dCode succeeds
              -- First: distLens = distLens₀ because there's a reference token
              have hdist_not_all_zero : ¬(distLens₀.all (fun x => x == 0)) = true := by
                -- There's a reference, so distFreqs has a positive entry
                have hdfreq := tokenFreqs_distCode_pos tokens len dist dCode dExtraN
                  dExtraV.toUInt32 ht_mem hfdc_native
                -- computeCodeLengths gives nonzero for positive freq
                have hdfreq_pair : ∃ p ∈ distFreqPairs, p.1 = dCode ∧ p.2 > 0 :=
                  ⟨(dCode, distFreqs[dCode]!), by
                    simp only [distFreqPairs, List.mem_map, List.mem_range]
                    exact ⟨dCode, by omega, rfl⟩,
                    rfl, hdfreq⟩
                have hdlen_nz := Huffman.Spec.computeCodeLengths_nonzero distFreqPairs 30 15
                  (by omega) dCode (by omega) hdfreq_pair
                -- If all were zero, distLens₀[dCode]! would be 0, contradiction
                intro hall
                have hdc_lt : dCode < distLens₀.length := by omega
                have hmem : distLens₀[dCode] ∈ distLens₀ := List.getElem_mem hdc_lt
                have hzero := List.all_eq_true.mp hall _ hmem
                simp [beq_iff_eq] at hzero
                -- hzero : distLens₀[dCode] = 0
                have : distLens₀[dCode]! = 0 := by
                  rw [getElem!_pos distLens₀ dCode hdc_lt]; exact hzero
                exact hdlen_nz this
              have hdl_eq : distLens = distLens₀ := by
                simp only [distLens, hdist_not_all_zero, Bool.false_eq_true, ↓reduceIte]
              -- Now use distLens₀ properties
              have hdsym : dCode < distLens.length := by rw [hdist_len]; omega
              have hdfreq := tokenFreqs_distCode_pos tokens len dist dCode dExtraN
                dExtraV.toUInt32 ht_mem hfdc_native
              have hdfreq_pair : ∃ p ∈ distFreqPairs, p.1 = dCode ∧ p.2 > 0 :=
                ⟨(dCode, distFreqs[dCode]!), by
                  simp only [distFreqPairs, List.mem_map, List.mem_range]
                  exact ⟨dCode, by omega, rfl⟩,
                  rfl, hdfreq⟩
              have hdlen_nz : distLens[dCode]! ≠ 0 := by
                rw [hdl_eq]
                exact Huffman.Spec.computeCodeLengths_nonzero distFreqPairs 30 15
                  (by omega) dCode (by omega) hdfreq_pair
              have hdlen_le' : distLens[dCode]! ≤ 15 := by
                rw [getElem!_pos distLens dCode hdsym]
                exact hdist_bound _ (List.getElem_mem hdsym)
              have hdist_enc := Deflate.Spec.encodeSymbol_fixed_isSome distLens 15 dCode
                hdsym hdlen_nz hdlen_le'
              cases hds : Deflate.Spec.encodeSymbol
                  ((Huffman.Spec.allCodes distLens).map fun (s, cw) => (cw, s)) dCode with
              | none => simp [hds] at hdist_enc
              | some distBits =>
                -- Close the goal: all four operations succeeded
                simp [LZ77Token.toLZ77Symbol, hlc, hls, hdc, hds]
    | inr heob =>
      subst heob
      -- Need: encodeLitLen litLens distLens .endOfBlock succeeds
      simp only [Deflate.Spec.encodeLitLen]
      have hsym : 256 < litLens.length := by rw [hlit_len]; omega
      have hfreq := tokenFreqs_eob_pos tokens
      have hfreq_pair : ∃ p ∈ litFreqPairs, p.1 = 256 ∧ p.2 > 0 :=
        ⟨(256, litFreqs[256]!), by
          simp only [litFreqPairs, List.mem_map, List.mem_range]
          exact ⟨256, by omega, rfl⟩,
          rfl, hfreq⟩
      have hlen_nz := Huffman.Spec.computeCodeLengths_nonzero litFreqPairs 286 15
        (by omega) 256 (by omega) hfreq_pair
      have hlen_le : litLens[256]! ≤ 15 := by
        rw [getElem!_pos litLens 256 hsym]
        exact hlit_bound _ (List.getElem_mem hsym)
      exact Deflate.Spec.encodeSymbol_fixed_isSome litLens 15 256 hsym hlen_nz hlen_le
  -- Extract the actual values
  cases henc_trees : Deflate.Spec.encodeDynamicTrees litLens distLens with
  | none => simp [henc_trees] at henc_trees_some
  | some headerBits =>
    cases henc_syms : Deflate.Spec.encodeSymbols litLens distLens
        (tokensToSymbols tokens) with
    | none => simp [henc_syms] at henc_syms_some
    | some symBits =>
      refine ⟨litLens, distLens, headerBits, symBits,
        hlit_valid, hdist_valid,
        by omega, by omega, by omega, by omega,
        hlit_bound, hdist_bound,
        henc_trees, henc_syms, ?_⟩
      -- bytesToBits decomposition
      -- Split symBits into tokBits ++ eobBits
      have htoks_eq : tokensToSymbols tokens =
          tokens.toList.map LZ77Token.toLZ77Symbol ++ [.endOfBlock] := rfl
      rw [htoks_eq] at henc_syms
      obtain ⟨tokBits, eobBits, henc_tok, henc_eob_syms, hsymBits_eq⟩ :=
        Deflate.encodeSymbols_append_inv litLens distLens
          (tokens.toList.map LZ77Token.toLZ77Symbol)
          [.endOfBlock] symBits henc_syms
      -- Extract EOB encoding
      simp only [Deflate.Spec.encodeSymbols] at henc_eob_syms
      cases henc_eob : Deflate.Spec.encodeLitLen litLens distLens .endOfBlock with
      | none => simp [henc_eob] at henc_eob_syms
      | some eobBits' =>
        simp [henc_eob] at henc_eob_syms
        have heob_eq : eobBits = eobBits' := by rw [henc_eob_syms]
        -- Build the combined encodeSymbols result
        have henc_combined := Deflate.encodeSymbols_append litLens distLens
          (tokens.toList.map LZ77Token.toLZ77Symbol)
          [.endOfBlock] tokBits eobBits henc_tok
          (by simp [Deflate.Spec.encodeSymbols, henc_eob, henc_eob_syms])
        -- Build canonical codes (same as in deflateDynamic)
        let litCodes := canonicalCodes (litLens.toArray.map Nat.toUInt8)
        let distCodes := canonicalCodes (distLens.toArray.map Nat.toUInt8)
        -- Size properties
        have hlit_codes_size : litCodes.size = litLens.length := by
          simp [litCodes, canonicalCodes_size, List.size_toArray]
        have hdist_codes_size : distCodes.size = distLens.length := by
          simp [distCodes, canonicalCodes_size, List.size_toArray]
        -- Code length bounds
        have hlit_lengths_arr_le : ∀ j, j < (litLens.toArray.map Nat.toUInt8).size →
            (litLens.toArray.map Nat.toUInt8)[j]!.toNat ≤ 15 := by
          intro k hk
          rw [getElem!_pos _ k hk]
          simp only [Array.getElem_map, Array.size_map, List.size_toArray] at hk ⊢
          simp only [UInt8.toNat, Nat.toUInt8, UInt8.ofNat, BitVec.toNat_ofNat]
          have hle := hlit_bound _ (List.getElem_mem hk)
          exact Nat.le_trans (Nat.mod_le _ _) hle
        have hdist_lengths_arr_le : ∀ j, j < (distLens.toArray.map Nat.toUInt8).size →
            (distLens.toArray.map Nat.toUInt8)[j]!.toNat ≤ 15 := by
          intro k hk
          rw [getElem!_pos _ k hk]
          simp only [Array.getElem_map, Array.size_map, List.size_toArray] at hk ⊢
          simp only [UInt8.toNat, Nat.toUInt8, UInt8.ofNat, BitVec.toNat_ofNat]
          have hle := hdist_bound _ (List.getElem_mem hk)
          exact Nat.le_trans (Nat.mod_le _ _) hle
        have hlit_le : ∀ j, j < litCodes.size → litCodes[j]!.2.toNat ≤ 15 := by
          intro j hj
          exact canonicalCodes_snd_le _ 15 hlit_lengths_arr_le j hj
        have hdist_le : ∀ j, j < distCodes.size → distCodes[j]!.2.toNat ≤ 15 := by
          intro j hj
          exact canonicalCodes_snd_le _ 15 hdist_lengths_arr_le j hj
        -- EOB codeword
        have hlit_roundtrip :
            (litLens.toArray.map Nat.toUInt8).toList.map UInt8.toNat = litLens := by
          simp only [Array.toList_map, List.map_map]; symm
          rw [List.map_congr_left (fun n hn => by
            show UInt8.toNat (Nat.toUInt8 n) = n
            simp only [Nat.toUInt8, UInt8.toNat, UInt8.ofNat, BitVec.toNat_ofNat]
            exact Nat.mod_eq_of_lt (by have := hlit_valid.1 n hn; omega))]
          simp
        have ⟨heob_cw, heob_len⟩ := encodeSymbol_canonicalCodes_eq
          (litLens.toArray.map Nat.toUInt8) 15 litCodes rfl
          (by rwa [hlit_roundtrip])
          (by omega) 256 eobBits'
          (by simp only [Deflate.Spec.encodeLitLen] at henc_eob; rwa [hlit_roundtrip])
        -- BitWriter chain
        have hwf0 := BitWriter.empty_wf
        have hwf1 := BitWriter.writeBits_wf _ 1 1 hwf0 (by omega)
        have hwf2 := BitWriter.writeBits_wf _ 2 2 hwf1 (by omega)
        -- Header bits: [true, false, true]
        have hbw2_bits : (BitWriter.empty.writeBits 1 1 |>.writeBits 2 2).toBits =
            [true, false, true] := by
          have h1 := BitWriter.writeBits_toBits _ 1 1 hwf0 (by omega)
          have h2 := BitWriter.writeBits_toBits _ 2 2 hwf1 (by omega)
          rw [BitWriter.empty_toBits] at h1
          simp only [List.nil_append] at h1
          rw [h1] at h2; exact h2
        -- writeDynamicHeader
        let bw2 := BitWriter.empty.writeBits 1 1 |>.writeBits 2 2
        have hwf_hdr := writeDynamicHeader_wf bw2 litLens distLens hwf2 hlit_bound hdist_bound
        have hbw_hdr := writeDynamicHeader_spec bw2 litLens distLens headerBits hwf2
          hlit_bound hdist_bound ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ henc_trees
        -- emitTokensWithCodes
        let bw3 := writeDynamicHeader bw2 litLens distLens
        have hemit := emitTokensWithCodes_spec bw3 tokens litLens distLens
          litCodes distCodes tokBits hwf_hdr rfl rfl hlit_valid hdist_valid henc_tok
        have hwf_emit := emitTokensWithCodes_wf bw3 tokens litCodes distCodes hwf_hdr
          (by rw [hlit_codes_size]; omega) (by rw [hdist_codes_size]; omega)
          hlit_le hdist_le
        -- writeHuffCode for EOB
        let bw4 := emitTokensWithCodes bw3 tokens litCodes distCodes 0
        have h256_lt : 256 < litCodes.size := by rw [hlit_codes_size]; omega
        have hwf_eob := BitWriter.writeHuffCode_wf bw4
          litCodes[256]!.1 litCodes[256]!.2 hwf_emit (hlit_le 256 h256_lt)
        have hbw_eob := BitWriter.writeHuffCode_toBits bw4
          litCodes[256]!.1 litCodes[256]!.2 hwf_emit (hlit_le 256 h256_lt)
        -- Chain all the bits
        rw [hemit, hbw_hdr, hbw2_bits] at hbw_eob
        -- Show deflateDynamic data equals the flushed writer
        have hdef : deflateDynamic data =
            (bw4.writeHuffCode litCodes[256]!.1 litCodes[256]!.2).flush := by
          unfold deflateDynamic
          -- After unfold, we have `let (litFreqs, distFreqs) := tokenFreqs tokens; ...`
          -- This is definitionally equal to using .1/.2, and `let (code, len) := litCodes[256]!`
          -- is definitionally equal to using .1/.2. So `split` on the `if` suffices.
          split
          · rename_i hzero
            have hzero' : data.size = 0 := by
              rw [beq_iff_eq] at hzero; exact hzero
            have htok_empty : tokens = #[] := by
              simp only [tokens, lz77Greedy]
              rw [if_pos (show data.size < 3 by omega)]
              show (lz77Greedy.trailing data 0).toArray = #[]
              unfold lz77Greedy.trailing
              rw [if_neg (by omega)]
            have hemit_id : bw4 = bw3 := by
              show emitTokensWithCodes bw3 tokens litCodes distCodes 0 = bw3
              rw [htok_empty]; unfold emitTokensWithCodes; simp
            rw [hemit_id]; rfl
          · rfl
        rw [hdef]
        have hflush := BitWriter.flush_toBits _ hwf_eob
        -- The bits decomposition
        have hbits_eq : (bw4.writeHuffCode litCodes[256]!.1 litCodes[256]!.2).toBits =
            [true, false, true] ++ headerBits ++ symBits := by
          rw [hbw_eob]
          rw [hsymBits_eq, heob_eq, heob_cw]
          simp only [List.append_assoc]
        rw [hflush, hbits_eq]
        -- Align the bitCount % 8
        suffices hmod : (bw4.writeHuffCode litCodes[256]!.1 litCodes[256]!.2).bitCount.toNat % 8 =
            ([true, false, true] ++ headerBits ++ symBits).length % 8 by
          simp only [hmod]
        have htoBits_len : (bw4.writeHuffCode litCodes[256]!.1 litCodes[256]!.2).toBits.length =
            (bw4.writeHuffCode litCodes[256]!.1 litCodes[256]!.2).data.data.toList.length * 8 +
            (bw4.writeHuffCode litCodes[256]!.1 litCodes[256]!.2).bitCount.toNat := by
          simp only [BitWriter.toBits, List.length_append, List.length_flatMap,
            Deflate.Spec.bytesToBits.byteToBits_length, List.length_map, List.length_range]
          have hsum : ∀ (l : List UInt8),
              (l.map (fun _ => 8)).sum = l.length * 8 := by
            intro l; induction l with
            | nil => simp
            | cons _ _ ih => simp [ih, Nat.add_mul]; omega
          rw [hsum]
        rw [hbits_eq] at htoBits_len
        omega

/-- Native Level 5 roundtrip: compressing with greedy LZ77 + dynamic Huffman
    codes then decompressing recovers the original data.
    Size bound: same as `inflate_deflateFixed`. -/
theorem inflate_deflateDynamic (data : ByteArray)
    (hsize : data.size < 10000000) :
    Zip.Native.Inflate.inflate (deflateDynamic data) = .ok data := by
  have hspec := deflateDynamic_spec data
  match hspec with
  | ⟨litLens, distLens, headerBits, symBits, hv_lit, hv_dist,
      hlitLen_lo, hlitLen_hi, hdistLen_lo, hdistLen_hi,
      hlit_bound, hdist_bound,
      henc_trees, henc_syms, hbits⟩ =>
    -- Decode roundtrip for dynamic blocks
    have hheader := Deflate.Spec.encodeDynamicTrees_decodeDynamicTables
      litLens distLens headerBits
      (symBits ++ List.replicate
        ((8 - ([true, false, true] ++ headerBits ++ symBits).length % 8) % 8) false)
      hlit_bound hdist_bound
      ⟨hlitLen_lo, hlitLen_hi⟩ ⟨hdistLen_lo, hdistLen_hi⟩
      hv_lit hv_dist henc_trees
    have hdec_padded : Deflate.Spec.decode (Deflate.Spec.bytesToBits (deflateDynamic data)) =
        some data.data.toList := by
      rw [hbits]
      let padding := List.replicate
        ((8 - ([true, false, true] ++ headerBits ++ symBits).length % 8) % 8) false
      have hheader' : Deflate.Spec.decodeDynamicTables (headerBits ++ symBits ++ padding) =
          some (litLens, distLens, symBits ++ padding) := by
        rw [List.append_assoc]; exact hheader
      exact Deflate.Spec.encodeDynamic_decode_append
        (tokensToSymbols (lz77Greedy data 32768)) data.data.toList
        litLens distLens headerBits symBits padding
        hv_lit hv_dist
        hheader'
        henc_syms
        (lz77Greedy_resolves data 32768 (by omega))
        (by have := lz77Greedy_size_le data 32768; rw [tokensToSymbols_length]; omega)
        (tokensToSymbols_validSymbolList _)
    have hlen : data.data.toList.length ≤ 256 * 1024 * 1024 := by
      simp only [Array.length_toList, ByteArray.size_data]; omega
    rw [← show ByteArray.mk ⟨data.data.toList⟩ = data from by simp]
    exact inflate_complete (deflateDynamic data) data.data.toList hlen hdec_padded

end Zip.Native.Deflate
