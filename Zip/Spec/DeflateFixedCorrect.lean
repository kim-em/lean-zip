import Zip.Spec.DeflateEncodeProps
import Zip.Spec.LZ77NativeCorrect
import Zip.Spec.BitWriterCorrect
import Zip.Spec.InflateCorrect
import Zip.Spec.HuffmanEncodeCorrect
import Zip.Native.DeflateDynamic

/-!
# Native DEFLATE Fixed Huffman Correctness

This file connects the native `deflateFixed` compressor to the spec-level
fixed Huffman encoder, and states the end-to-end roundtrip theorem
`inflate_deflateFixed`.

## Key results

- `tokensToSymbols_validSymbolList`: native LZ77 tokens + endOfBlock form a valid symbol list
- `tokensToSymbols_encodable`: each symbol from `lz77Greedy` can be fixed-Huffman encoded
- `lz77Greedy_spec_decode`: spec decode succeeds on encoded native tokens
- `inflate_deflateFixed`: native inflate ∘ deflateFixed = identity (WIP)
-/

namespace Zip.Native.Deflate

/-! ## ValidSymbolList for tokensToSymbols -/

/-- A mapped token list (no endOfBlock) has `ValidSymbolList` when followed
    by `[.endOfBlock]`. -/
private theorem validSymbolList_map_append_endOfBlock
    (ts : List LZ77Token) :
    Deflate.Spec.ValidSymbolList
      (ts.map LZ77Token.toLZ77Symbol ++ [.endOfBlock]) := by
  induction ts with
  | nil => simp [Deflate.Spec.ValidSymbolList]
  | cons t rest ih =>
    simp only [List.map_cons, List.cons_append]
    cases t with
    | literal b =>
      show Deflate.Spec.ValidSymbolList _
      exact ih
    | reference len dist =>
      show Deflate.Spec.ValidSymbolList _
      exact ih

/-- The symbol list produced by `tokensToSymbols` is always valid:
    it ends with exactly one `.endOfBlock` and contains no `.endOfBlock`
    elsewhere. -/
theorem tokensToSymbols_validSymbolList (tokens : Array LZ77Token) :
    Deflate.Spec.ValidSymbolList (tokensToSymbols tokens) := by
  simp only [tokensToSymbols]
  exact validSymbolList_map_append_endOfBlock tokens.toList

/-! ## Encodability of tokensToSymbols -/

open Deflate.Spec in
/-- Each symbol in `tokensToSymbols (lz77Greedy data)` can be encoded with
    the fixed Huffman tables. -/
theorem tokensToSymbols_encodable (data : ByteArray)
    (windowSize : Nat) (hw : windowSize > 0) (hws : windowSize ≤ 32768) :
    ∀ s ∈ tokensToSymbols (lz77Greedy data windowSize),
      (encodeLitLen fixedLitLengths fixedDistLengths s).isSome = true := by
  intro s hs
  simp only [tokensToSymbols, List.mem_append, List.mem_map, List.mem_cons,
    List.mem_nil_iff, or_false] at hs
  cases hs with
  | inl hmapped =>
    obtain ⟨t, ht_mem, ht_eq⟩ := hmapped
    have hbounds := lz77Greedy_encodable data windowSize hw hws t ht_mem
    subst ht_eq
    cases t with
    | literal b => exact encodeLitLen_literal_isSome b
    | reference len dist =>
      simp at hbounds
      exact encodeLitLen_reference_isSome len dist
        hbounds.1 hbounds.2.1 hbounds.2.2.1 hbounds.2.2.2
  | inr heob =>
    subst heob
    exact encodeLitLen_endOfBlock_isSome

open Deflate.Spec in
/-- `encodeSymbols` succeeds on `tokensToSymbols (lz77Greedy data)`. -/
theorem encodeSymbols_tokensToSymbols_isSome (data : ByteArray)
    (windowSize : Nat) (hw : windowSize > 0) (hws : windowSize ≤ 32768) :
    (encodeSymbols fixedLitLengths fixedDistLengths
      (tokensToSymbols (lz77Greedy data windowSize))).isSome = true :=
  encodeSymbols_isSome_of_all _ _ _
    (tokensToSymbols_encodable data windowSize hw hws)

/-! ## tokensToSymbols length bound -/

/-- `tokensToSymbols` has length `tokens.size + 1`. -/
theorem tokensToSymbols_length (tokens : Array LZ77Token) :
    (tokensToSymbols tokens).length = tokens.size + 1 := by
  simp [tokensToSymbols, List.length_append, List.length_map]

/-- The token count from `lz77Greedy` is at most `data.size`. In the worst
    case every byte is a literal. -/
theorem lz77Greedy_size_le (data : ByteArray) (windowSize : Nat) :
    (lz77Greedy data windowSize).size ≤ data.size := by
  simp only [lz77Greedy]
  split
  · simp only [List.size_toArray]
    exact trailing_length data 0
  · simp only [List.size_toArray]
    exact mainLoop_length data windowSize 65536
      (Array.replicate 65536 0) (Array.replicate 65536 false) 0

/-! ## Spec-level roundtrip for native tokens -/

open Deflate.Spec in
/-- Encoding the native LZ77 tokens with fixed Huffman then decoding
    recovers the original data. This is the spec-level roundtrip using
    the native greedy matcher instead of the spec-level `matchLZ77`. -/
theorem lz77Greedy_spec_decode (data : ByteArray)
    (windowSize : Nat) (hw : windowSize > 0) (hws : windowSize ≤ 32768)
    (hsize : data.size < 10000000) :
    ∃ bits, encodeFixed (tokensToSymbols (lz77Greedy data windowSize)) =
              some bits ∧
            decode bits = some data.data.toList := by
  have henc_some := encodeSymbols_tokensToSymbols_isSome data windowSize hw hws
  cases henc : encodeSymbols fixedLitLengths fixedDistLengths
      (tokensToSymbols (lz77Greedy data windowSize)) with
  | none => simp [henc] at henc_some
  | some bits =>
    refine ⟨[true, true, false] ++ bits, ?_, ?_⟩
    · simp [encodeFixed, henc]
    · exact encodeFixed_decode
        (tokensToSymbols (lz77Greedy data windowSize))
        data.data.toList bits henc
        (lz77Greedy_resolves data windowSize hw)
        (by
          have := lz77Greedy_size_le data windowSize
          rw [tokensToSymbols_length]
          omega)
        (tokensToSymbols_validSymbolList _)

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
private theorem findLengthCode_agree (length idx extraN extraV : Nat)
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
private theorem findDistCode_agree (dist idx extraN extraV : Nat)
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
private theorem encodeSymbol_litTable_eq (s : Nat) (cw : List Bool)
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
private theorem encodeSymbol_distTable_eq (s : Nat) (cw : List Bool)
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

/-! ## Main emitTokens ↔ encodeSymbols correspondence -/

/-- Decompose `encodeSymbols` on a cons list into head and tail encoding. -/
private theorem encodeSymbols_cons_some
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

/-- Extra bits count for length codes is bounded: `lengthExtra[i]! ≤ 5` for `i < 29`. -/
private theorem lengthExtra_le_5 (idx : Nat) (h : idx < 29) :
    Deflate.Spec.lengthExtra[idx]! ≤ 5 := by
  have : ∀ i : Fin 29, Deflate.Spec.lengthExtra[i.val]! ≤ 5 := by decide
  exact this ⟨idx, h⟩

/-- Extra bits count for distance codes is bounded: `distExtra[i]! ≤ 13` for `i < 30`. -/
private theorem distExtra_le_13 (idx : Nat) (h : idx < 30) :
    Deflate.Spec.distExtra[idx]! ≤ 13 := by
  have : ∀ i : Fin 30, Deflate.Spec.distExtra[i.val]! ≤ 13 := by decide
  exact this ⟨idx, h⟩

private theorem array_get!Internal_eq [Inhabited α] (a : Array α) (i : Nat) :
    a.get!Internal i = a[i]! := rfl

set_option maxRecDepth 2048 in
/-- Generalized `emitTokens_spec` with arbitrary start index. -/
private theorem emitTokens_spec_go (bw : BitWriter) (tokens : Array LZ77Token)
    (i : Nat) (bits : List Bool) (hwf : bw.wf)
    (henc : Deflate.Spec.encodeSymbols
        Deflate.Spec.fixedLitLengths Deflate.Spec.fixedDistLengths
        ((tokens.toList.drop i).map LZ77Token.toLZ77Symbol) = some bits) :
    (emitTokens bw tokens i).toBits = bw.toBits ++ bits := by
  -- Induction on tokens.size - i
  suffices ∀ k, k = tokens.size - i →
      (emitTokens bw tokens i).toBits = bw.toBits ++ bits by
    exact this _ rfl
  intro k
  induction k generalizing bw i bits with
  | zero =>
    intro heq
    have hge : i ≥ tokens.size := by omega
    have hdrop : tokens.toList.drop i = [] := by
      simp [List.drop_eq_nil_iff, Array.length_toList]; omega
    rw [hdrop, List.map_nil] at henc
    simp only [Deflate.Spec.encodeSymbols] at henc
    cases henc
    simp only [emitTokens, show ¬(i < tokens.size) from by omega, ↓reduceDIte,
      List.append_nil]
  | succ n ih =>
    intro heq
    have hlt : i < tokens.size := by omega
    have hlt_list : i < tokens.toList.length := by simp; exact hlt
    rw [List.drop_eq_getElem_cons hlt_list, List.map_cons] at henc
    obtain ⟨symBits, restBits, hencsym, hencrest, hbits_eq⟩ :=
      encodeSymbols_cons_some _ _ _ _ _ henc
    subst hbits_eq
    -- Bridge array ↔ list indexing
    have htoList : tokens[i] = tokens.toList[i] := by simp [Array.getElem_toList]
    -- Unfold emitTokens one step and take the positive branch
    unfold emitTokens
    simp only [dif_pos hlt]
    -- Case split on token type, then reduce let-match pattern
    cases htok : tokens[i] with
    | literal b =>
      simp only [array_get!Internal_eq]  -- normalize get!Internal → [·]!
      -- Spec side
      have htok_list : tokens.toList[i] = .literal b := by rw [← htoList]; exact htok
      simp only [LZ77Token.toLZ77Symbol, htok_list] at hencsym
      simp only [Deflate.Spec.encodeLitLen] at hencsym
      have ⟨hcw, hlen⟩ := encodeSymbol_litTable_eq b.toNat symBits hencsym
      -- BitWriter correspondence + IH
      have hwf' := BitWriter.writeHuffCode_wf bw
        fixedLitCodes[b.toNat]!.1 fixedLitCodes[b.toNat]!.2 hwf hlen
      have hbits := BitWriter.writeHuffCode_toBits bw
        fixedLitCodes[b.toNat]!.1 fixedLitCodes[b.toNat]!.2 hwf hlen
      rw [ih _ (i + 1) restBits hwf' hencrest (by omega)]
      rw [hbits, hcw, List.append_assoc]
    | reference len dist =>
      simp only [array_get!Internal_eq]  -- normalize get!Internal → [·]!
      -- Spec side: decompose encodeLitLen for reference
      have htok_list : tokens.toList[i] = .reference len dist := by
        rw [← htoList]; exact htok
      simp only [LZ77Token.toLZ77Symbol, htok_list] at hencsym
      simp only [Deflate.Spec.encodeLitLen] at hencsym
      cases hflc : Deflate.Spec.findLengthCode len with
      | none => simp [hflc] at hencsym
      | some lc =>
        obtain ⟨lidx, lextraN, lextraV⟩ := lc
        cases henclen : Deflate.Spec.encodeSymbol
            ((Huffman.Spec.allCodes Deflate.Spec.fixedLitLengths).map fun p => (p.2, p.1))
            (257 + lidx) with
        | none => simp [hflc, henclen] at hencsym
        | some lenBits =>
          cases hfdc : Deflate.Spec.findDistCode dist with
          | none => simp [hflc, hfdc] at hencsym
          | some dc =>
            obtain ⟨didx, dextraN, dextraV⟩ := dc
            cases hencdist : Deflate.Spec.encodeSymbol
                ((Huffman.Spec.allCodes Deflate.Spec.fixedDistLengths).map fun p => (p.2, p.1))
                didx with
            | none => simp [hflc, hfdc, hencdist] at hencsym
            | some distBits =>
              simp [hflc, henclen, hfdc, hencdist] at hencsym
              subst hencsym
              -- Bridge lemmas
              have hnflc := findLengthCode_agree len lidx lextraN lextraV hflc
              have hnfdc := findDistCode_agree dist didx dextraN dextraV hfdc
              have ⟨hlcw, hllen⟩ := encodeSymbol_litTable_eq (257 + lidx) lenBits henclen
              have ⟨hdcw, hdlen⟩ := encodeSymbol_distTable_eq didx distBits hencdist
              have hflc_spec := Deflate.Spec.findLengthCode_spec len lidx lextraN lextraV hflc
              have hfdc_spec := Deflate.Spec.findDistCode_spec dist didx dextraN dextraV hfdc
              -- Extra bits bounds
              have lextraN_le : lextraN ≤ 25 := by
                rw [hflc_spec.2.2.1]
                exact Nat.le_trans (lengthExtra_le_5 lidx hflc_spec.1) (by omega)
              have dextraN_le : dextraN ≤ 25 := by
                rw [hfdc_spec.2.2.1]
                exact Nat.le_trans (distExtra_le_13 didx hfdc_spec.1) (by omega)
              -- Reduce native findLengthCode/findDistCode matches
              simp only [hnflc, hnfdc]
              -- Normalize lidx + 257 → 257 + lidx to match spec convention
              have h257 : lidx + 257 = 257 + lidx := by omega
              rw [h257]
              -- Chain BitWriter correspondence (explicit args to avoid inference failure)
              let lcode := fixedLitCodes[257 + lidx]!.fst
              let llen := fixedLitCodes[257 + lidx]!.snd
              let dcode := fixedDistCodes[didx]!.fst
              let dlen := fixedDistCodes[didx]!.snd
              have hwf1 := BitWriter.writeHuffCode_wf bw lcode llen hwf hllen
              have hbits1 := BitWriter.writeHuffCode_toBits bw lcode llen hwf hllen
              let bw1 := bw.writeHuffCode lcode llen
              have hwf2 := BitWriter.writeBits_wf bw1 lextraN lextraV.toUInt32 hwf1 lextraN_le
              have hbits2 := BitWriter.writeBits_toBits bw1 lextraN lextraV.toUInt32 hwf1 lextraN_le
              let bw2 := bw1.writeBits lextraN lextraV.toUInt32
              have hwf3 := BitWriter.writeHuffCode_wf bw2 dcode dlen hwf2 hdlen
              have hbits3 := BitWriter.writeHuffCode_toBits bw2 dcode dlen hwf2 hdlen
              let bw3 := bw2.writeHuffCode dcode dlen
              have hwf4 := BitWriter.writeBits_wf bw3 dextraN dextraV.toUInt32 hwf3 dextraN_le
              have hbits4 := BitWriter.writeBits_toBits bw3 dextraN dextraV.toUInt32 hwf3 dextraN_le
              -- Apply IH for remaining tokens
              rw [ih _ (i + 1) restBits hwf4 hencrest (by omega)]
              rw [hbits4, hbits3, hbits2, hbits1]
              rw [hlcw, hdcw]
              -- UInt32 faithfulness for extra values
              have hlextraV_small : lextraV < 2 ^ 32 := Nat.lt_of_lt_of_le
                hflc_spec.2.2.2 (Nat.pow_le_pow_right (by omega) (by omega))
              have hdextraV_small : dextraV < 2 ^ 32 := Nat.lt_of_lt_of_le
                hfdc_spec.2.2.2 (Nat.pow_le_pow_right (by omega) (by omega))
              simp only [Nat.toUInt32, UInt32.ofNat, UInt32.toNat, BitVec.toNat_ofNat,
                show lextraV % 2 ^ 32 = lextraV from Nat.mod_eq_of_lt hlextraV_small,
                show dextraV % 2 ^ 32 = dextraV from Nat.mod_eq_of_lt hdextraV_small]
              simp only [List.append_assoc]
              rfl

/-- `emitTokens` produces the same bit sequence as spec `encodeSymbols`. -/
theorem emitTokens_spec (bw : BitWriter) (tokens : Array LZ77Token)
    (bits : List Bool) (hwf : bw.wf)
    (henc : Deflate.Spec.encodeSymbols
        Deflate.Spec.fixedLitLengths Deflate.Spec.fixedDistLengths
        (tokens.toList.map LZ77Token.toLZ77Symbol) = some bits) :
    (emitTokens bw tokens 0).toBits =
    bw.toBits ++ bits := by
  exact emitTokens_spec_go bw tokens 0 bits hwf (by rwa [List.drop_zero])

/-- `deflateFixed` produces a bytestream whose bits are the spec-level
    fixed Huffman encoding of the LZ77 tokens.
    **Sorry**: depends on `emitTokens_spec` + `flush_toBits` + byte alignment. -/
theorem deflateFixed_spec (data : ByteArray) :
    ∃ bits,
      Deflate.Spec.encodeFixed
        (tokensToSymbols (lz77Greedy data)) = some bits ∧
      Deflate.Spec.bytesToBits (deflateFixed data) =
        bits ++ List.replicate
          ((8 - (Deflate.Spec.bytesToBits (deflateFixed data)).length % 8) % 8)
          false := by
  sorry

/-! ## Inflate completeness (restricted) -/

open Deflate.Spec in
/-- If spec `decode` succeeds on the bits of a bytestream, native `inflate`
    also succeeds with the same result. Restricted to inputs within fuel
    and size limits.
    **Sorry**: this is the reverse direction of `inflate_correct'`. Proving it
    requires constructing a successful native execution from a successful spec
    decode, which involves showing that every native step (readBits, decodeHuffman,
    etc.) succeeds when the spec decode succeeds. -/
theorem inflate_complete (bytes : ByteArray) (result : List UInt8)
    (hsize : result.length ≤ 256 * 1024 * 1024)
    (hdec : decode (bytesToBits bytes) = some result) :
    Zip.Native.Inflate.inflate bytes =
    .ok ⟨⟨result⟩⟩ := by
  sorry

/-! ## Main roundtrip theorem -/

/-- Native Level 1 roundtrip: compressing with fixed Huffman codes then
    decompressing recovers the original data.
    **Sorry**: depends on `inflate_complete` (the reverse direction of
    `inflate_correct'`). Once `inflate_complete` is proved, this theorem
    follows from `lz77Greedy_spec_decode` + `deflateFixed_spec`. -/
theorem inflate_deflateFixed (data : ByteArray)
    (hsize : data.size ≤ 256 * 1024 * 1024) :
    Zip.Native.Inflate.inflate (deflateFixed data) = .ok data := by
  sorry

/-- Native Level 2 roundtrip: compressing with lazy LZ77 + fixed Huffman codes
    then decompressing recovers the original data.
    **Sorry**: same proof strategy as `inflate_deflateFixed`, substituting
    `lz77Lazy` for `lz77Greedy`. -/
theorem inflate_deflateLazy (data : ByteArray)
    (hsize : data.size ≤ 256 * 1024 * 1024) :
    Zip.Native.Inflate.inflate (deflateLazy data) = .ok data := by
  sorry

/-- Native Level 5 roundtrip: compressing with greedy LZ77 + dynamic Huffman
    codes then decompressing recovers the original data.
    **Sorry**: requires proving the dynamic block header written by
    `writeDynamicHeader` is correctly decodable by `inflate`, plus
    `emitTokensWithCodes` correspondence with spec `encodeSymbols` for
    dynamic code tables. -/
theorem inflate_deflateDynamic (data : ByteArray)
    (hsize : data.size ≤ 256 * 1024 * 1024) :
    Zip.Native.Inflate.inflate (deflateDynamic data) = .ok data := by
  sorry

end Zip.Native.Deflate
