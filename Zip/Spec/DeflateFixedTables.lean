import Zip.Spec.DeflateEncodeProps
import Zip.Spec.HuffmanEncodeCorrect
import Zip.Native.Deflate

/-!
# Fixed Huffman Table Bridge Proofs

This file bridges the native fixed Huffman tables (`fixedLitCodes`,
`fixedDistCodes`, `lengthBase`, `distBase`, etc.) with their spec-level
counterparts. These are stable infrastructure lemmas used by the main
correctness theorems in `DeflateFixedCorrect.lean`.

## Key results

- `fixedLitCodes_agree` / `fixedDistCodes_agree`: canonical codewords match native table entries
- `findLengthCode_agree` / `findDistCode_agree`: native table lookup matches spec
- `encodeSymbol_litTable_eq` / `encodeSymbol_distTable_eq`: spec encoding matches native table entries
- `encodeSymbols_cons_some`: decompose `encodeSymbols` on a cons list
-/

namespace Zip.Native.Deflate

/-! ## Bridge lemmas for fixed Huffman tables -/

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem fixedLitLengths_eq :
    Inflate.fixedLitLengths.toList.map UInt8.toNat =
    Deflate.Spec.fixedLitLengths := by rfl

set_option maxRecDepth 2048 in
private theorem fixedDistLengths_eq :
    Inflate.fixedDistLengths.toList.map UInt8.toNat =
    Deflate.Spec.fixedDistLengths := by decide

private theorem fixedLitLengths_validLengths :
    Huffman.Spec.ValidLengths
      (Inflate.fixedLitLengths.toList.map UInt8.toNat) 15 :=
  fixedLitLengths_eq ▸ Deflate.Spec.fixedLitLengths_valid

private theorem fixedDistLengths_validLengths :
    Huffman.Spec.ValidLengths
      (Inflate.fixedDistLengths.toList.map UInt8.toNat) 15 :=
  fixedDistLengths_eq ▸ Deflate.Spec.fixedDistLengths_valid

set_option maxRecDepth 2048 in
/-- The codeword from `codeFor` on the fixed literal table matches
    the `natToBits` of the corresponding `fixedLitCodes` entry. -/
private theorem fixedLitCodes_agree (s : Nat) (cw : Huffman.Spec.Codeword)
    (hcf : Huffman.Spec.codeFor Deflate.Spec.fixedLitLengths 15 s = some cw) :
    cw = Huffman.Spec.natToBits fixedLitCodes[s]!.1.toNat fixedLitCodes[s]!.2.toNat ∧
    fixedLitCodes[s]!.2.toNat ≤ 15 := by
  have ⟨hs, hlen, _⟩ := Huffman.Spec.codeFor_spec hcf
  have ⟨hne0, hle15⟩ := Huffman.Spec.codeFor_len_bounds hlen
  -- Size bridge
  have hsize_eq : Inflate.fixedLitLengths.size = Deflate.Spec.fixedLitLengths.length := by
    have := congrArg List.length fixedLitLengths_eq
    simp only [List.length_map, Array.length_toList] at this; exact this
  have hsize : s < Inflate.fixedLitLengths.size := by omega
  -- Element-wise bridge
  have hmap_len : s < (Inflate.fixedLitLengths.toList.map UInt8.toNat).length := by
    simp only [List.length_map, Array.length_toList]; exact hsize
  have helem := List.getElem_of_eq fixedLitLengths_eq hmap_len
  simp only [List.getElem_map, Array.getElem_toList] at helem
  -- Get canonical code entry (bridge UInt8 > 0 to Nat > 0 for omega)
  have hpos : 0 < Inflate.fixedLitLengths[s].toNat := by omega
  obtain ⟨cw', hcf', hcw', hlen'⟩ :=
    Deflate.Correctness.canonicalCodes_correct_pos
      Inflate.fixedLitLengths 15 fixedLitLengths_validLengths (by omega) s hsize hpos
  -- Bridge: codeFor on native lengths = codeFor on spec lengths
  have hcf_bridge :
      Huffman.Spec.codeFor (Inflate.fixedLitLengths.toList.map UInt8.toNat) 15 s =
      Huffman.Spec.codeFor Deflate.Spec.fixedLitLengths 15 s :=
    congrArg (Huffman.Spec.codeFor · 15 s) fixedLitLengths_eq
  rw [hcf_bridge] at hcf'
  -- Match codewords
  have hcw_eq : cw = cw' := Option.some.inj (hcf.symm.trans hcf')
  subst hcw_eq
  -- Bridge second component: lengths[s] → fixedLitCodes[s]!.snd
  rw [← hlen'] at hcw'
  -- Bridge from canonicalCodes entry to Inflate.fixedLitLengths element (for omega)
  have hlen'_nat := congrArg UInt8.toNat hlen'
  -- omega sees canonicalCodes and fixedLitCodes as distinct; bridge explicitly
  have : fixedLitCodes[s]!.snd.toNat = (canonicalCodes Inflate.fixedLitLengths)[s]!.snd.toNat := rfl
  exact ⟨hcw', by omega⟩

set_option maxRecDepth 2048 in
/-- The codeword from `codeFor` on the fixed distance table matches
    the `natToBits` of the corresponding `fixedDistCodes` entry. -/
private theorem fixedDistCodes_agree (s : Nat) (cw : Huffman.Spec.Codeword)
    (hcf : Huffman.Spec.codeFor Deflate.Spec.fixedDistLengths 15 s = some cw) :
    cw = Huffman.Spec.natToBits fixedDistCodes[s]!.1.toNat fixedDistCodes[s]!.2.toNat ∧
    fixedDistCodes[s]!.2.toNat ≤ 15 := by
  have ⟨hs, hlen, _⟩ := Huffman.Spec.codeFor_spec hcf
  have ⟨hne0, hle15⟩ := Huffman.Spec.codeFor_len_bounds hlen
  -- Size bridge
  have hsize_eq : Inflate.fixedDistLengths.size = Deflate.Spec.fixedDistLengths.length := by
    have := congrArg List.length fixedDistLengths_eq
    simp only [List.length_map, Array.length_toList] at this; exact this
  have hsize : s < Inflate.fixedDistLengths.size := by omega
  -- Element-wise bridge
  have hmap_len : s < (Inflate.fixedDistLengths.toList.map UInt8.toNat).length := by
    simp only [List.length_map, Array.length_toList]; exact hsize
  have helem := List.getElem_of_eq fixedDistLengths_eq hmap_len
  simp only [List.getElem_map, Array.getElem_toList] at helem
  -- Get canonical code entry (bridge UInt8 > 0 to Nat > 0 for omega)
  have hpos : 0 < Inflate.fixedDistLengths[s].toNat := by omega
  obtain ⟨cw', hcf', hcw', hlen'⟩ :=
    Deflate.Correctness.canonicalCodes_correct_pos
      Inflate.fixedDistLengths 15 fixedDistLengths_validLengths (by omega) s hsize hpos
  -- Bridge: codeFor on native lengths = codeFor on spec lengths
  have hcf_bridge :
      Huffman.Spec.codeFor (Inflate.fixedDistLengths.toList.map UInt8.toNat) 15 s =
      Huffman.Spec.codeFor Deflate.Spec.fixedDistLengths 15 s :=
    congrArg (Huffman.Spec.codeFor · 15 s) fixedDistLengths_eq
  rw [hcf_bridge] at hcf'
  -- Match codewords
  have hcw_eq : cw = cw' := Option.some.inj (hcf.symm.trans hcf')
  subst hcw_eq
  -- Bridge second component: lengths[s] → fixedDistCodes[s]!.snd
  rw [← hlen'] at hcw'
  -- Bridge from canonicalCodes entry to Inflate.fixedDistLengths element (for omega)
  have hlen'_nat := congrArg UInt8.toNat hlen'
  -- omega sees canonicalCodes and fixedDistCodes as distinct; bridge explicitly
  have : fixedDistCodes[s]!.snd.toNat = (canonicalCodes Inflate.fixedDistLengths)[s]!.snd.toNat := rfl
  exact ⟨hcw', by omega⟩

/-! ## findTableCode correctness -/

-- Table element-wise correspondence (native UInt16/UInt8 ↔ spec Nat)
set_option maxRecDepth 1024 in
private theorem nativeLengthBase_eq : ∀ i : Fin 29,
    Inflate.lengthBase[i.val]!.toNat = Deflate.Spec.lengthBase[i.val]! := by decide

set_option maxRecDepth 1024 in
private theorem nativeLengthExtra_eq : ∀ i : Fin 29,
    Inflate.lengthExtra[i.val]!.toNat = Deflate.Spec.lengthExtra[i.val]! := by decide

set_option maxRecDepth 1024 in
private theorem nativeDistBase_eq : ∀ i : Fin 30,
    Inflate.distBase[i.val]!.toNat = Deflate.Spec.distBase[i.val]! := by decide

set_option maxRecDepth 1024 in
private theorem nativeDistExtra_eq : ∀ i : Fin 30,
    Inflate.distExtra[i.val]!.toNat = Deflate.Spec.distExtra[i.val]! := by decide

-- Table monotonicity (step-wise)
set_option maxRecDepth 1024 in
private theorem specLengthBase_step : ∀ i : Fin 28,
    Deflate.Spec.lengthBase[i.val]! ≤ Deflate.Spec.lengthBase[i.val + 1]! := by decide

set_option maxRecDepth 1024 in
private theorem specDistBase_step : ∀ i : Fin 29,
    Deflate.Spec.distBase[i.val]! ≤ Deflate.Spec.distBase[i.val + 1]! := by decide

-- Sizes
private theorem nativeLengthBase_size : Inflate.lengthBase.size = 29 := by rfl
private theorem nativeDistBase_size : Inflate.distBase.size = 30 := by rfl

/-- Monotonicity of the spec length base table (full transitive closure). -/
private theorem specLengthBase_monotone (j k : Nat) (hjk : j ≤ k) (hk : k < 29) :
    Deflate.Spec.lengthBase[j]! ≤ Deflate.Spec.lengthBase[k]! := by
  induction k with
  | zero => simp_all
  | succ k ih =>
    by_cases hjk' : j ≤ k
    · exact Nat.le_trans (ih hjk' (by omega))
        (specLengthBase_step ⟨k, by omega⟩)
    · have : j = k + 1 := by omega
      subst this; exact Nat.le_refl _

/-- Monotonicity of the spec distance base table (full transitive closure). -/
private theorem specDistBase_monotone (j k : Nat) (hjk : j ≤ k) (hk : k < 30) :
    Deflate.Spec.distBase[j]! ≤ Deflate.Spec.distBase[k]! := by
  induction k with
  | zero => simp_all
  | succ k ih =>
    by_cases hjk' : j ≤ k
    · exact Nat.le_trans (ih hjk' (by omega))
        (specDistBase_step ⟨k, by omega⟩)
    · have : j = k + 1 := by omega
      subst this; exact Nat.le_refl _

/-- If `idx` is the first matching index starting from `i`, then
    `findTableCode.go` returns the expected result. -/
private theorem findTableCode_go_of_first_match
    (baseTable : Array UInt16) (extraTable : Array UInt8)
    (value i idx : Nat)
    (hi : i ≤ idx)
    (hidx : idx < baseTable.size)
    (hmatch : idx + 1 < baseTable.size → baseTable[idx + 1]!.toNat > value)
    (hskip : ∀ j, j < idx → j + 1 < baseTable.size ∧
        baseTable[j + 1]!.toNat ≤ value) :
    findTableCode.go baseTable extraTable value i =
    some (idx, extraTable[idx]!.toNat,
          (value - baseTable[idx]!.toNat).toUInt32) := by
  suffices ∀ k, k = baseTable.size - i →
      findTableCode.go baseTable extraTable value i =
      some (idx, extraTable[idx]!.toNat,
            (value - baseTable[idx]!.toNat).toUInt32) by
    exact this _ rfl
  intro k
  induction k generalizing i with
  | zero => intro hk; omega
  | succ n ih =>
    intro hk
    unfold findTableCode.go
    by_cases heq : idx = i
    · -- Match at this index
      subst heq
      by_cases h_next : idx + 1 < baseTable.size
      · -- Has next entry: check upper bound
        have hgt := hmatch h_next
        simp only [show idx + 1 < baseTable.size from h_next, ↓reduceIte,
          show baseTable[idx + 1]!.toNat > value from hgt, ↓reduceIte]
      · -- Last entry
        simp only [show ¬(idx + 1 < baseTable.size) from h_next, ↓reduceIte,
          show idx < baseTable.size from hidx, ↓reduceIte]
    · -- Skip: search passes through this index
      have hlt_idx : i < idx := by omega  -- from ¬(idx = i) and i ≤ idx
      obtain ⟨h_next_i, h_le_i⟩ := hskip i hlt_idx
      simp only [show i + 1 < baseTable.size from h_next_i, ↓reduceIte,
        show ¬(baseTable[i + 1]!.toNat > value) from by omega, ↓reduceIte]
      exact ih (i + 1) (by omega : i + 1 ≤ idx) (by omega)

/-! ## findLengthCode / findDistCode agreement -/

/-- If spec `findLengthCode` succeeds, native `findLengthCode` succeeds with
    the same result (up to UInt32 conversion for the extra value). -/
protected theorem findLengthCode_agree (length idx extraN extraV : Nat)
    (hspec : Deflate.Spec.findLengthCode length = some (idx, extraN, extraV)) :
    findLengthCode length = some (idx, extraN, extraV.toUInt32) := by
  have hgo := Deflate.Spec.findLengthCode_spec length idx extraN extraV hspec
  have hidx := hgo.1
  have hbase := hgo.2.1
  have hextraN := hgo.2.2.1
  show findTableCode.go Inflate.lengthBase Inflate.lengthExtra length 0 =
    some (idx, extraN, extraV.toUInt32)
  have result := findTableCode_go_of_first_match Inflate.lengthBase Inflate.lengthExtra
    length 0 idx (by omega) (by rw [nativeLengthBase_size]; omega)
    (fun h_next => by
      rw [nativeLengthBase_size] at h_next
      have h1 := nativeLengthBase_eq ⟨idx + 1, h_next⟩
      rw [h1]
      exact Deflate.Spec.findLengthCode_upper length idx extraN extraV hspec h_next)
    (fun j hj => by
      have hj_bound : j + 1 < 29 := by omega
      refine ⟨by rw [nativeLengthBase_size]; omega, ?_⟩
      have h1 := nativeLengthBase_eq ⟨j + 1, hj_bound⟩
      rw [h1]
      exact Nat.le_trans (specLengthBase_monotone (j + 1) idx (by omega) hidx) (by omega))
  have h1 := nativeLengthExtra_eq ⟨idx, hidx⟩
  have h2 := nativeLengthBase_eq ⟨idx, hidx⟩
  rw [result, h1, hextraN, h2, show length - Deflate.Spec.lengthBase[idx]! = extraV from by omega]

/-- If spec `findDistCode` succeeds, native `findDistCode` succeeds with
    the same result. -/
protected theorem findDistCode_agree (dist idx extraN extraV : Nat)
    (hspec : Deflate.Spec.findDistCode dist = some (idx, extraN, extraV)) :
    findDistCode dist = some (idx, extraN, extraV.toUInt32) := by
  have hgo := Deflate.Spec.findDistCode_spec dist idx extraN extraV hspec
  have hidx := hgo.1
  have hbase := hgo.2.1
  have hextraN := hgo.2.2.1
  show findTableCode.go Inflate.distBase Inflate.distExtra dist 0 =
    some (idx, extraN, extraV.toUInt32)
  have result := findTableCode_go_of_first_match Inflate.distBase Inflate.distExtra
    dist 0 idx (by omega) (by rw [nativeDistBase_size]; omega)
    (fun h_next => by
      rw [nativeDistBase_size] at h_next
      have h1 := nativeDistBase_eq ⟨idx + 1, h_next⟩
      rw [h1]
      exact Deflate.Spec.findDistCode_upper dist idx extraN extraV hspec h_next)
    (fun j hj => by
      have hj_bound : j + 1 < 30 := by omega
      refine ⟨by rw [nativeDistBase_size]; omega, ?_⟩
      have h1 := nativeDistBase_eq ⟨j + 1, hj_bound⟩
      rw [h1]
      exact Nat.le_trans (specDistBase_monotone (j + 1) idx (by omega) hidx) (by omega))
  have h1 := nativeDistExtra_eq ⟨idx, hidx⟩
  have h2 := nativeDistBase_eq ⟨idx, hidx⟩
  rw [result, h1, hextraN, h2, show dist - Deflate.Spec.distBase[idx]! = extraV from by omega]

/-! ## encodeSymbol ↔ writeHuffCode bridge -/

/-- If `encodeSymbol` on the flipped `allCodes` table returns `cw` for symbol `s`,
    then `cw` equals `natToBits` of the `canonicalCodes` entry. -/
protected theorem encodeSymbol_litTable_eq (s : Nat) (cw : List Bool)
    (henc : Deflate.Spec.encodeSymbol
      ((Huffman.Spec.allCodes Deflate.Spec.fixedLitLengths).map fun p => (p.2, p.1))
      s = some cw) :
    cw = Huffman.Spec.natToBits fixedLitCodes[s]!.1.toNat fixedLitCodes[s]!.2.toNat ∧
    fixedLitCodes[s]!.2.toNat ≤ 15 := by
  -- encodeSymbol_mem → (cw, s) ∈ table → (s, cw) ∈ allCodes
  have hmem := Deflate.Spec.encodeSymbol_mem _ s cw henc
  have hmem' : (s, cw) ∈ Huffman.Spec.allCodes Deflate.Spec.fixedLitLengths := by
    simp only [List.mem_map] at hmem
    obtain ⟨⟨s', cw'⟩, hmem, heq⟩ := hmem
    simp only [Prod.mk.injEq] at heq
    exact heq.1 ▸ heq.2 ▸ hmem
  -- allCodes_mem_iff → codeFor succeeds
  rw [Huffman.Spec.allCodes_mem_iff] at hmem'
  exact fixedLitCodes_agree s cw hmem'.2

/-- Same as `encodeSymbol_litTable_eq` but for the distance table. -/
protected theorem encodeSymbol_distTable_eq (s : Nat) (cw : List Bool)
    (henc : Deflate.Spec.encodeSymbol
      ((Huffman.Spec.allCodes Deflate.Spec.fixedDistLengths).map fun p => (p.2, p.1))
      s = some cw) :
    cw = Huffman.Spec.natToBits fixedDistCodes[s]!.1.toNat fixedDistCodes[s]!.2.toNat ∧
    fixedDistCodes[s]!.2.toNat ≤ 15 := by
  have hmem := Deflate.Spec.encodeSymbol_mem _ s cw henc
  have hmem' : (s, cw) ∈ Huffman.Spec.allCodes Deflate.Spec.fixedDistLengths := by
    simp only [List.mem_map] at hmem
    obtain ⟨⟨s', cw'⟩, hmem, heq⟩ := hmem
    simp only [Prod.mk.injEq] at heq
    exact heq.1 ▸ heq.2 ▸ hmem
  rw [Huffman.Spec.allCodes_mem_iff] at hmem'
  exact fixedDistCodes_agree s cw hmem'.2

/-! ## encodeSymbols decomposition -/

/-- Decompose `encodeSymbols` on a cons list into head and tail encoding. -/
protected theorem encodeSymbols_cons_some
    (litLengths distLengths : List Nat) (s : Deflate.Spec.LZ77Symbol)
    (rest : List Deflate.Spec.LZ77Symbol) (bits : List Bool)
    (h : Deflate.Spec.encodeSymbols litLengths distLengths (s :: rest) = some bits) :
    ∃ symBits restBits,
      Deflate.Spec.encodeLitLen litLengths distLengths s = some symBits ∧
      Deflate.Spec.encodeSymbols litLengths distLengths rest = some restBits ∧
      bits = symBits ++ restBits := by
  simp only [Deflate.Spec.encodeSymbols] at h
  cases hencsym : Deflate.Spec.encodeLitLen litLengths distLengths s with
  | none => simp [hencsym] at h
  | some symBits =>
    cases hencrest : Deflate.Spec.encodeSymbols litLengths distLengths rest with
    | none => simp [hencsym, hencrest] at h
    | some restBits =>
      simp [hencsym, hencrest] at h
      exact ⟨symBits, restBits, rfl, rfl, h.symm⟩

/-! ## Extra bits bounds -/

/-- Extra bits count for length codes is bounded: `lengthExtra[i]! ≤ 5` for `i < 29`. -/
protected theorem lengthExtra_le_5 (idx : Nat) (h : idx < 29) :
    Deflate.Spec.lengthExtra[idx]! ≤ 5 := by
  have : ∀ i : Fin 29, Deflate.Spec.lengthExtra[i.val]! ≤ 5 := by decide
  exact this ⟨idx, h⟩

/-- Extra bits count for distance codes is bounded: `distExtra[i]! ≤ 13` for `i < 30`. -/
protected theorem distExtra_le_13 (idx : Nat) (h : idx < 30) :
    Deflate.Spec.distExtra[idx]! ≤ 13 := by
  have : ∀ i : Fin 30, Deflate.Spec.distExtra[i.val]! ≤ 13 := by decide
  exact this ⟨idx, h⟩

end Zip.Native.Deflate
