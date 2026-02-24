import Zip.Spec.DeflateFixedTables
import Zip.Spec.DeflateStoredCorrect
import Zip.Spec.LZ77NativeCorrect
import Zip.Spec.BitWriterCorrect
import Zip.Spec.InflateCorrect
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

/-! ## Lazy LZ77 bridge lemmas -/

open Deflate.Spec in
/-- Each symbol in `tokensToSymbols (lz77Lazy data)` can be encoded with
    the fixed Huffman tables. -/
theorem tokensToSymbols_lazy_encodable (data : ByteArray)
    (windowSize : Nat) (hw : windowSize > 0) (hws : windowSize ≤ 32768) :
    ∀ s ∈ tokensToSymbols (lz77Lazy data windowSize),
      (encodeLitLen fixedLitLengths fixedDistLengths s).isSome = true := by
  intro s hs
  simp only [tokensToSymbols, List.mem_append, List.mem_map, List.mem_cons,
    List.mem_nil_iff, or_false] at hs
  cases hs with
  | inl hmapped =>
    obtain ⟨t, ht_mem, ht_eq⟩ := hmapped
    have hbounds := lz77Lazy_encodable data windowSize hw hws t ht_mem
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
/-- `encodeSymbols` succeeds on `tokensToSymbols (lz77Lazy data)`. -/
theorem encodeSymbols_tokensToSymbols_lazy_isSome (data : ByteArray)
    (windowSize : Nat) (hw : windowSize > 0) (hws : windowSize ≤ 32768) :
    (encodeSymbols fixedLitLengths fixedDistLengths
      (tokensToSymbols (lz77Lazy data windowSize))).isSome = true :=
  encodeSymbols_isSome_of_all _ _ _
    (tokensToSymbols_lazy_encodable data windowSize hw hws)

open Deflate.Spec in
/-- Encoding the native lazy LZ77 tokens with fixed Huffman then decoding
    recovers the original data. -/
theorem lz77Lazy_spec_decode (data : ByteArray)
    (windowSize : Nat) (hw : windowSize > 0) (hws : windowSize ≤ 32768)
    (hsize : data.size < 5000000) :
    ∃ bits, encodeFixed (tokensToSymbols (lz77Lazy data windowSize)) =
              some bits ∧
            decode bits = some data.data.toList := by
  have henc_some := encodeSymbols_tokensToSymbols_lazy_isSome data windowSize hw hws
  cases henc : encodeSymbols fixedLitLengths fixedDistLengths
      (tokensToSymbols (lz77Lazy data windowSize)) with
  | none => simp [henc] at henc_some
  | some bits =>
    refine ⟨[true, true, false] ++ bits, ?_, ?_⟩
    · simp [encodeFixed, henc]
    · exact encodeFixed_decode
        (tokensToSymbols (lz77Lazy data windowSize))
        data.data.toList bits henc
        (lz77Lazy_resolves data windowSize hw)
        (by
          have := lz77Lazy_size_le data windowSize
          rw [tokensToSymbols_length]
          omega)
        (tokensToSymbols_validSymbolList _)

/-! ## emitTokens ↔ encodeSymbols correspondence -/

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
      Deflate.encodeSymbols_cons_some _ _ _ _ _ henc
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
      have ⟨hcw, hlen⟩ := Deflate.encodeSymbol_litTable_eq b.toNat symBits hencsym
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
              have hnflc := Deflate.findLengthCode_agree len lidx lextraN lextraV hflc
              have hnfdc := Deflate.findDistCode_agree dist didx dextraN dextraV hfdc
              have ⟨hlcw, hllen⟩ := Deflate.encodeSymbol_litTable_eq (257 + lidx) lenBits henclen
              have ⟨hdcw, hdlen⟩ := Deflate.encodeSymbol_distTable_eq didx distBits hencdist
              have hflc_spec := Deflate.Spec.findLengthCode_spec len lidx lextraN lextraV hflc
              have hfdc_spec := Deflate.Spec.findDistCode_spec dist didx dextraN dextraV hfdc
              -- Extra bits bounds
              have lextraN_le : lextraN ≤ 25 := by
                rw [hflc_spec.2.2.1]
                exact Nat.le_trans (Deflate.lengthExtra_le_5 lidx hflc_spec.1) (by omega)
              have dextraN_le : dextraN ≤ 25 := by
                rw [hfdc_spec.2.2.1]
                exact Nat.le_trans (Deflate.distExtra_le_13 didx hfdc_spec.1) (by omega)
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

/-! ## encodeSymbols append lemmas -/

/-- `encodeSymbols` distributes over append: encoding `xs ++ ys` is the
    concatenation of encoding `xs` and encoding `ys`. -/
private theorem encodeSymbols_append
    (litLengths distLengths : List Nat)
    (xs ys : List Deflate.Spec.LZ77Symbol)
    (xBits yBits : List Bool)
    (hx : Deflate.Spec.encodeSymbols litLengths distLengths xs = some xBits)
    (hy : Deflate.Spec.encodeSymbols litLengths distLengths ys = some yBits) :
    Deflate.Spec.encodeSymbols litLengths distLengths (xs ++ ys) =
      some (xBits ++ yBits) := by
  induction xs generalizing xBits with
  | nil =>
    simp only [Deflate.Spec.encodeSymbols] at hx
    cases hx; simp only [List.nil_append, List.nil_append]; exact hy
  | cons s rest ih =>
    simp only [List.cons_append, Deflate.Spec.encodeSymbols]
    obtain ⟨symBits, restBits, hencsym, hencrest, hbits_eq⟩ :=
      Deflate.encodeSymbols_cons_some _ _ _ _ _ hx
    subst hbits_eq
    have hrest_ys := ih restBits hencrest
    simp only [hencsym, hrest_ys, bind, Option.bind, List.append_assoc, pure, Pure.pure]

/-- If `encodeSymbols` succeeds on `xs ++ ys`, it succeeds on `xs` and `ys` separately. -/
private theorem encodeSymbols_append_inv
    (litLengths distLengths : List Nat)
    (xs ys : List Deflate.Spec.LZ77Symbol)
    (bits : List Bool)
    (h : Deflate.Spec.encodeSymbols litLengths distLengths (xs ++ ys) = some bits) :
    ∃ xBits yBits,
      Deflate.Spec.encodeSymbols litLengths distLengths xs = some xBits ∧
      Deflate.Spec.encodeSymbols litLengths distLengths ys = some yBits ∧
      bits = xBits ++ yBits := by
  induction xs generalizing bits with
  | nil =>
    simp only [List.nil_append] at h
    exact ⟨[], bits, rfl, h, (List.nil_append _).symm⟩
  | cons s rest ih =>
    simp only [List.cons_append, Deflate.Spec.encodeSymbols] at h
    cases hes : Deflate.Spec.encodeLitLen litLengths distLengths s with
    | none => simp [hes] at h
    | some sBits =>
      cases her : Deflate.Spec.encodeSymbols litLengths distLengths (rest ++ ys) with
      | none => simp [hes, her] at h
      | some restBits =>
        simp only [hes, her, bind, Option.bind, pure, Pure.pure] at h
        have h := Option.some.inj h
        obtain ⟨xBits, yBits, hx, hy, heq⟩ := ih restBits her
        refine ⟨sBits ++ xBits, yBits, ?_, hy, ?_⟩
        · simp only [Deflate.Spec.encodeSymbols, hes, hx, bind, Option.bind, pure, Pure.pure]
        · rw [← h, heq, List.append_assoc]

/-! ## Helper lemmas for deflateFixed_spec -/

/-- `findTableCode.go` returns an index < baseTable.size. -/
private theorem findTableCode_go_idx_bound (baseTable : Array UInt16)
    (extraTable : Array UInt8) (value i idx extraN : Nat) (extraV : UInt32)
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

/-- `findTableCode.go` returns extraN = extraTable[idx]!.toNat. -/
private theorem findTableCode_go_extraN (baseTable : Array UInt16)
    (extraTable : Array UInt8) (value i idx extraN : Nat) (extraV : UInt32)
    (h : findTableCode.go baseTable extraTable value i = some (idx, extraN, extraV)) :
    extraN = extraTable[idx]!.toNat := by
  unfold findTableCode.go at h
  split at h
  · split at h
    · simp at h; rw [← h.1]; exact h.2.1.symm
    · exact findTableCode_go_extraN baseTable extraTable value (i + 1) idx extraN extraV h
  · split at h
    · simp at h; rw [← h.1]; exact h.2.1.symm
    · simp at h
termination_by baseTable.size - i

/-- Native `findLengthCode` returns idx < 29. -/
private theorem nativeFindLengthCode_idx_bound (len idx extraN : Nat) (extraV : UInt32)
    (h : findLengthCode len = some (idx, extraN, extraV)) :
    idx < 29 := by
  have := findTableCode_go_idx_bound _ _ _ _ _ _ _ h
  have : Inflate.lengthBase.size = 29 := by rfl
  omega

/-- Native `findLengthCode` returns extraN ≤ 5. -/
private theorem nativeFindLengthCode_extraN_bound (len idx extraN : Nat) (extraV : UInt32)
    (h : findLengthCode len = some (idx, extraN, extraV)) :
    extraN ≤ 5 := by
  have hidx := nativeFindLengthCode_idx_bound len idx extraN extraV h
  have hextraN := findTableCode_go_extraN _ _ _ _ _ _ _ h
  rw [hextraN]
  have : ∀ j : Fin 29, Inflate.lengthExtra[j.val]!.toNat ≤ 5 := by decide
  exact this ⟨idx, hidx⟩

/-- Native `findDistCode` returns dIdx < 30. -/
private theorem nativeFindDistCode_idx_bound (dist dIdx dExtraN : Nat) (dExtraV : UInt32)
    (h : findDistCode dist = some (dIdx, dExtraN, dExtraV)) :
    dIdx < 30 := by
  have := findTableCode_go_idx_bound _ _ _ _ _ _ _ h
  have : Inflate.distBase.size = 30 := by rfl
  omega

/-- Native `findDistCode` returns dExtraN ≤ 13. -/
private theorem nativeFindDistCode_extraN_bound (dist dIdx dExtraN : Nat) (dExtraV : UInt32)
    (h : findDistCode dist = some (dIdx, dExtraN, dExtraV)) :
    dExtraN ≤ 13 := by
  have hidx := nativeFindDistCode_idx_bound dist dIdx dExtraN dExtraV h
  have hextraN := findTableCode_go_extraN _ _ _ _ _ _ _ h
  rw [hextraN]
  have : ∀ j : Fin 30, Inflate.distExtra[j.val]!.toNat ≤ 13 := by decide
  exact this ⟨dIdx, hidx⟩

/-- `canonicalCodes` preserves the array size. -/
private theorem canonicalCodes_size (lengths : Array UInt8) :
    (canonicalCodes lengths).size = lengths.size := by
  simp only [canonicalCodes]
  rw [Deflate.Correctness.canonicalCodes_go_size]
  simp [Array.size_replicate]

/-- `fixedLitCodes` has size 288 (= Inflate.fixedLitLengths.size). -/
private theorem fixedLitCodes_size : fixedLitCodes.size = 288 := by
  show (canonicalCodes Inflate.fixedLitLengths).size = 288
  rw [canonicalCodes_size]
  simp [Inflate.fixedLitLengths, Array.size_append, Array.size_replicate]

/-- `fixedDistCodes` has size 32 (= Inflate.fixedDistLengths.size). -/
private theorem fixedDistCodes_size : fixedDistCodes.size = 32 := by
  show (canonicalCodes Inflate.fixedDistLengths).size = 32
  rw [canonicalCodes_size]
  simp [Inflate.fixedDistLengths, Array.size_replicate]

/-- `canonicalCodes.go` preserves a bound on `.snd.toNat`: if all entries in
    `result` have `.snd.toNat ≤ bound` and all entries in `lengths` have
    `.toNat ≤ bound`, then the output has all `.snd.toNat ≤ bound`. -/
private theorem canonicalCodes_go_snd_le (lengths : Array UInt8) (nextCode : Array UInt32)
    (i : Nat) (result : Array (UInt16 × UInt8)) (bound : Nat)
    (hsize : result.size = lengths.size)
    (hresult : ∀ j, j < result.size → result[j]!.2.toNat ≤ bound)
    (hlengths : ∀ j, j < lengths.size → lengths[j]!.toNat ≤ bound)
    (j : Nat) (hj : j < (canonicalCodes.go lengths nextCode i result).size) :
    (canonicalCodes.go lengths nextCode i result)[j]!.2.toNat ≤ bound := by
  unfold canonicalCodes.go at hj ⊢
  by_cases hi : i < lengths.size
  · simp only [hi, ↓reduceDIte] at hj ⊢
    by_cases hlen : lengths[i] > 0
    · simp only [hlen, ↓reduceIte] at hj ⊢
      let val := (nextCode[lengths[i].toNat]!.toUInt16, lengths[i])
      have hsize' : (result.set! i val).size = lengths.size := by
        simp only [Array.set!_eq_setIfInBounds, Array.setIfInBounds]
        split <;> simp_all
      have hresult' : ∀ k, k < (result.set! i val).size →
          (result.set! i val)[k]!.2.toNat ≤ bound := by
        intro k hk
        by_cases heq : k = i
        · rw [heq, getElem!_pos (result.set! i val) i (by rw [hsize']; exact hi)]
          simp only [Array.set!_eq_setIfInBounds, Array.setIfInBounds,
            show i < result.size from by rw [hsize]; exact hi, ↓reduceDIte,
            Array.getElem_set, ↓reduceIte, val]
          rw [← getElem!_pos lengths i hi]
          exact hlengths i hi
        · rw [getElem!_pos (result.set! i val) k (by rw [hsize']; omega)]
          simp only [Array.set!_eq_setIfInBounds, Array.setIfInBounds,
            show i < result.size from by rw [hsize]; exact hi, ↓reduceDIte,
            Array.getElem_set, show ¬(i = k) from (Ne.symm heq), ↓reduceIte]
          rw [← getElem!_pos result k (by rw [hsize]; omega)]
          exact hresult k (by rw [hsize]; omega)
      exact canonicalCodes_go_snd_le lengths _ (i + 1) _ bound hsize' hresult'
        hlengths j hj
    · simp only [show ¬(lengths[i] > 0) from hlen, ↓reduceIte] at hj ⊢
      exact canonicalCodes_go_snd_le lengths nextCode (i + 1) result bound hsize hresult
        hlengths j hj
  · simp only [hi, ↓reduceDIte] at hj ⊢
    exact hresult j hj
termination_by lengths.size - i

/-- `canonicalCodes` entries have `.snd.toNat ≤ bound` when all input lengths
    have `.toNat ≤ bound`. -/
private theorem canonicalCodes_snd_le (lengths : Array UInt8) (bound : Nat)
    (hlengths : ∀ j, j < lengths.size → lengths[j]!.toNat ≤ bound) (i : Nat)
    (hi : i < (canonicalCodes lengths).size) :
    (canonicalCodes lengths)[i]!.2.toNat ≤ bound := by
  simp only [canonicalCodes] at hi ⊢
  apply canonicalCodes_go_snd_le lengths _ 0 _ bound
  · simp [Array.size_replicate]
  · intro j hj
    simp only [Array.size_replicate] at hj
    rw [getElem!_pos _ _ (by simp [Array.size_replicate]; omega)]
    simp [Array.getElem_replicate]
  · exact hlengths
  · exact hi

/-- Helper: all elements of `Array.replicate n v` at valid indices equal `v`. -/
private theorem replicate_getElem!_eq [Inhabited α] (n : Nat) (v : α) (j : Nat) (hj : j < n) :
    (Array.replicate n v)[j]! = v := by
  rw [getElem!_pos _ _ (by simp [Array.size_replicate]; omega)]
  simp [Array.getElem_replicate]

/-- All entries in `fixedLitLengths` have `.toNat ≤ 15`. -/
private theorem fixedLitLengths_le_15 (j : Nat) (hj : j < Inflate.fixedLitLengths.size) :
    Inflate.fixedLitLengths[j]!.toNat ≤ 15 := by
  -- fixedLitLengths = replicate 144 8 ++ replicate 112 9 ++ replicate 24 7 ++ replicate 8 8
  simp only [Inflate.fixedLitLengths, Array.size_append, Array.size_replicate] at hj
  show (Array.replicate 144 (8 : UInt8) ++ Array.replicate 112 9 ++ Array.replicate 24 7 ++
    Array.replicate 8 8)[j]!.toNat ≤ 15
  rw [getElem!_pos _ _ (by simp [Array.size_append, Array.size_replicate]; omega)]
  by_cases h1 : j < 280
  · have hlt : j < (Array.replicate 144 (8 : UInt8) ++ Array.replicate 112 9 ++
        Array.replicate 24 7).size := by
      simp [Array.size_append, Array.size_replicate]; omega
    rw [Array.getElem_append_left hlt]
    by_cases h2 : j < 256
    · have hlt2 : j < (Array.replicate 144 (8 : UInt8) ++ Array.replicate 112 9).size := by
        simp [Array.size_append, Array.size_replicate]; omega
      rw [Array.getElem_append_left hlt2]
      by_cases h3 : j < 144
      · rw [Array.getElem_append_left (by simp [Array.size_replicate]; omega)]
        simp [Array.getElem_replicate]
      · rw [Array.getElem_append_right (by simp [Array.size_replicate]; omega)]
        simp [Array.size_replicate, Array.getElem_replicate]
    · rw [Array.getElem_append_right (by simp [Array.size_append, Array.size_replicate]; omega)]
      simp [Array.size_append, Array.size_replicate, Array.getElem_replicate]
  · rw [Array.getElem_append_right (by simp [Array.size_append, Array.size_replicate]; omega)]
    simp [Array.size_append, Array.size_replicate, Array.getElem_replicate]

/-- All entries in `fixedDistLengths` have `.toNat ≤ 15`. -/
private theorem fixedDistLengths_le_15 (j : Nat) (hj : j < Inflate.fixedDistLengths.size) :
    Inflate.fixedDistLengths[j]!.toNat ≤ 15 := by
  have hj32 : j < 32 := hj
  show (Array.replicate 32 (5 : UInt8))[j]!.toNat ≤ 15
  rw [getElem!_pos _ _ (by simp [Array.size_replicate]; omega)]
  simp [Array.getElem_replicate]

/-- All entries in `fixedLitCodes` have code length ≤ 15.
    Proof: the fixed Huffman table uses lengths 7, 8, 9 (all ≤ 15). -/
private theorem fixedLitCodes_snd_le (i : Nat) (h : i < fixedLitCodes.size) :
    fixedLitCodes[i]!.2.toNat ≤ 15 :=
  canonicalCodes_snd_le Inflate.fixedLitLengths 15 fixedLitLengths_le_15 i h

/-- All entries in `fixedDistCodes` have code length ≤ 15.
    Proof: the fixed distance table uses uniform length 5. -/
private theorem fixedDistCodes_snd_le (i : Nat) (h : i < fixedDistCodes.size) :
    fixedDistCodes[i]!.2.toNat ≤ 15 :=
  canonicalCodes_snd_le Inflate.fixedDistLengths 15 fixedDistLengths_le_15 i h

/-! ## emitTokens preserves wf -/

set_option maxRecDepth 2048 in
/-- `emitTokens` preserves `BitWriter.wf`. -/
private theorem emitTokens_wf_go (bw : BitWriter) (tokens : Array LZ77Token)
    (i : Nat) (hwf : bw.wf) :
    (emitTokens bw tokens i).wf := by
  suffices ∀ k, k = tokens.size - i → (emitTokens bw tokens i).wf by
    exact this _ rfl
  intro k
  induction k generalizing bw i with
  | zero =>
    intro heq
    simp only [emitTokens, show ¬(i < tokens.size) from by omega, ↓reduceDIte]
    exact hwf
  | succ n ih =>
    intro heq
    have hlt : i < tokens.size := by omega
    unfold emitTokens
    simp only [dif_pos hlt]
    match htok : tokens[i] with
    | .literal b =>
      simp only [htok]
      have hb : b.toNat < fixedLitCodes.size := by
        have := fixedLitCodes_size
        have : b.toNat < 256 := UInt8.toNat_lt b
        omega
      exact ih _ (i + 1)
        (BitWriter.writeHuffCode_wf bw _ _ hwf (fixedLitCodes_snd_le b.toNat hb))
        (by omega)
    | .reference len dist =>
      simp only [htok]
      match hflc : findLengthCode len with
      | none =>
        simp only [hflc]
        exact ih _ (i + 1) hwf (by omega)
      | some (idx, extraCount, extraVal) =>
        simp only [hflc]
        have hidx := nativeFindLengthCode_idx_bound len idx extraCount extraVal hflc
        have hlen_code := fixedLitCodes_snd_le (idx + 257)
          (by have := fixedLitCodes_size; omega)
        have hextraN_le : extraCount ≤ 25 := by
          have := nativeFindLengthCode_extraN_bound len idx extraCount extraVal hflc; omega
        have hwf1 := BitWriter.writeHuffCode_wf bw
          fixedLitCodes[idx + 257]!.1 fixedLitCodes[idx + 257]!.2 hwf hlen_code
        have hwf2 := BitWriter.writeBits_wf
          (bw.writeHuffCode fixedLitCodes[idx + 257]!.1 fixedLitCodes[idx + 257]!.2)
          extraCount extraVal hwf1 hextraN_le
        match hfdc : findDistCode dist with
        | none =>
          simp only [hfdc]
          exact ih _ (i + 1) hwf2 (by omega)
        | some (dIdx, dExtraCount, dExtraVal) =>
          simp only [hfdc]
          have hdidx := nativeFindDistCode_idx_bound dist dIdx dExtraCount dExtraVal hfdc
          have hdlen_code := fixedDistCodes_snd_le dIdx
            (by have := fixedDistCodes_size; omega)
          have hdextraN_le : dExtraCount ≤ 25 := by
            have := nativeFindDistCode_extraN_bound dist dIdx dExtraCount dExtraVal hfdc; omega
          have hwf3 := BitWriter.writeHuffCode_wf _
            fixedDistCodes[dIdx]!.1 fixedDistCodes[dIdx]!.2 hwf2 hdlen_code
          have hwf4 := BitWriter.writeBits_wf _ dExtraCount dExtraVal hwf3 hdextraN_le
          exact ih _ (i + 1) hwf4 (by omega)

theorem emitTokens_wf (bw : BitWriter) (tokens : Array LZ77Token)
    (hwf : bw.wf) :
    (emitTokens bw tokens 0).wf :=
  emitTokens_wf_go bw tokens 0 hwf

/-- `encodeSymbols` on a singleton list returns `encodeLitLen` of that symbol. -/
private theorem encodeSymbols_singleton
    (litLengths distLengths : List Nat) (s : Deflate.Spec.LZ77Symbol)
    (bits : List Bool)
    (h : Deflate.Spec.encodeLitLen litLengths distLengths s = some bits) :
    Deflate.Spec.encodeSymbols litLengths distLengths [s] = some bits := by
  simp only [Deflate.Spec.encodeSymbols, h, bind, Option.bind, List.append_nil, pure, Pure.pure]

/-- `deflateFixed` produces a bytestream whose bits are the spec-level
    fixed Huffman encoding of the LZ77 tokens. -/
theorem deflateFixed_spec (data : ByteArray) :
    ∃ bits,
      Deflate.Spec.encodeFixed
        (tokensToSymbols (lz77Greedy data)) = some bits ∧
      Deflate.Spec.bytesToBits (deflateFixed data) =
        bits ++ List.replicate
          ((8 - bits.length % 8) % 8)
          false := by
  -- Step 1: Show encodeSymbols succeeds on tokensToSymbols
  have henc_some := encodeSymbols_tokensToSymbols_isSome data 32768 (by omega) (by omega)
  -- tokensToSymbols = tokens.map toLZ77Symbol ++ [.endOfBlock]
  have htoks_eq : tokensToSymbols (lz77Greedy data) =
      (lz77Greedy data).toList.map LZ77Token.toLZ77Symbol ++ [.endOfBlock] := rfl
  -- Extract allBits
  cases henc_all : Deflate.Spec.encodeSymbols Deflate.Spec.fixedLitLengths
      Deflate.Spec.fixedDistLengths
      (tokensToSymbols (lz77Greedy data)) with
  | none => simp [henc_all] at henc_some
  | some allBits =>
    -- Decompose into token bits and endOfBlock bits
    rw [htoks_eq] at henc_all
    obtain ⟨tokBits, eobBits, henc_tok, henc_eob_syms, hallBits_eq⟩ :=
      encodeSymbols_append_inv _ _
        ((lz77Greedy data).toList.map LZ77Token.toLZ77Symbol)
        [.endOfBlock] allBits henc_all
    -- Extract the single endOfBlock encoding
    simp only [Deflate.Spec.encodeSymbols] at henc_eob_syms
    cases henc_eob : Deflate.Spec.encodeLitLen Deflate.Spec.fixedLitLengths
        Deflate.Spec.fixedDistLengths .endOfBlock with
    | none => simp [henc_eob] at henc_eob_syms
    | some eobBits' =>
      simp [henc_eob] at henc_eob_syms
      have heob_eq : eobBits = eobBits' := by rw [henc_eob_syms]
      -- Step 2: Compute encodeFixed
      have henc_combined := encodeSymbols_append _ _
        ((lz77Greedy data).toList.map LZ77Token.toLZ77Symbol)
        [.endOfBlock] tokBits eobBits henc_tok
        (by simp [Deflate.Spec.encodeSymbols, henc_eob, henc_eob_syms])
      have hencFixed : Deflate.Spec.encodeFixed
          (tokensToSymbols (lz77Greedy data)) =
          some ([true, true, false] ++ allBits) := by
        simp only [Deflate.Spec.encodeFixed, htoks_eq, henc_combined, bind,
          Option.bind, pure, Pure.pure]
        rw [hallBits_eq]
      refine ⟨[true, true, false] ++ allBits, hencFixed, ?_⟩
      -- Step 3: Show bytesToBits (deflateFixed data) = header ++ allBits ++ padding
      -- BitWriter header chain
      have hwf0 := BitWriter.empty_wf
      have hwf1 := BitWriter.writeBits_wf _ 1 1 hwf0 (by omega)
      have hwf2 := BitWriter.writeBits_wf _ 2 1 hwf1 (by omega)
      have hbw2_bits : (BitWriter.empty.writeBits 1 1 |>.writeBits 2 1).toBits =
          [true, true, false] := by
        have h1 := BitWriter.writeBits_toBits _ 1 1 hwf0 (by omega)
        have h2 := BitWriter.writeBits_toBits _ 2 1 hwf1 (by omega)
        rw [BitWriter.empty_toBits] at h1
        simp only [List.nil_append] at h1
        rw [h1] at h2; exact h2
      -- endOfBlock correspondence
      have ⟨heob_cw, heob_len⟩ := Deflate.encodeSymbol_litTable_eq 256 eobBits' henc_eob
      -- Non-zero case: emitTokens bw2 tokens 0 |>.writeHuffCode eob |>.flush
      have hemit := emitTokens_spec
        (BitWriter.empty.writeBits 1 1 |>.writeBits 2 1)
        (lz77Greedy data) tokBits hwf2 henc_tok
      have hwf3 := emitTokens_wf
        (BitWriter.empty.writeBits 1 1 |>.writeBits 2 1)
        (lz77Greedy data) hwf2
      have hwf4 := BitWriter.writeHuffCode_wf
        (emitTokens (BitWriter.empty.writeBits 1 1 |>.writeBits 2 1) (lz77Greedy data) 0)
        fixedLitCodes[256]!.1 fixedLitCodes[256]!.2 hwf3 heob_len
      have hbits4 := BitWriter.writeHuffCode_toBits
        (emitTokens (BitWriter.empty.writeBits 1 1 |>.writeBits 2 1) (lz77Greedy data) 0)
        fixedLitCodes[256]!.1 fixedLitCodes[256]!.2 hwf3 heob_len
      rw [hemit, hbw2_bits] at hbits4
      -- Show deflateFixed data equals the BitWriter chain
      have hdef : deflateFixed data =
          (emitTokens (BitWriter.empty.writeBits 1 1 |>.writeBits 2 1)
            (lz77Greedy data) 0
            |>.writeHuffCode fixedLitCodes[256]!.1 fixedLitCodes[256]!.2).flush := by
        simp only [deflateFixed]
        unfold deflateFixedBlock
        split
        · -- data.size == 0: emitTokens on empty tokens is identity
          rename_i hzero
          have hzero' : data.size = 0 := by
            simp only [beq_iff_eq] at hzero; exact hzero
          have htokens : lz77Greedy data = #[] := by
            simp only [lz77Greedy, show data.size < 3 from by omega, ↓reduceIte]
            have : lz77Greedy.trailing data 0 = [] := by
              unfold lz77Greedy.trailing; simp [show ¬(0 < data.size) from by omega]
            simp [this]
          have hempty : emitTokens
              (BitWriter.empty.writeBits 1 1 |>.writeBits 2 1) #[] 0 =
              (BitWriter.empty.writeBits 1 1 |>.writeBits 2 1) := by
            simp [emitTokens]
          rw [htokens, hempty]; rfl
        · rfl
      rw [hdef]
      -- Apply flush_toBits
      have hflush := BitWriter.flush_toBits _ hwf4
      have hbits_eq : (emitTokens (BitWriter.empty.writeBits 1 1 |>.writeBits 2 1)
          (lz77Greedy data) 0 |>.writeHuffCode fixedLitCodes[256]!.1
          fixedLitCodes[256]!.2).toBits =
          [true, true, false] ++ allBits := by
        rw [hbits4, hallBits_eq, heob_eq, heob_cw, List.append_assoc]
      rw [hflush, hbits_eq]
      suffices hmod : (emitTokens (BitWriter.empty.writeBits 1 1 |>.writeBits 2 1)
          (lz77Greedy data) 0 |>.writeHuffCode fixedLitCodes[256]!.1
          fixedLitCodes[256]!.2).bitCount.toNat % 8 =
          ([true, true, false] ++ allBits).length % 8 by
        simp only [hmod]
      have htoBits_len : (emitTokens (BitWriter.empty.writeBits 1 1 |>.writeBits 2 1)
          (lz77Greedy data) 0 |>.writeHuffCode fixedLitCodes[256]!.1
          fixedLitCodes[256]!.2).toBits.length =
          (emitTokens (BitWriter.empty.writeBits 1 1 |>.writeBits 2 1)
          (lz77Greedy data) 0 |>.writeHuffCode fixedLitCodes[256]!.1
          fixedLitCodes[256]!.2).data.data.toList.length * 8 +
          (emitTokens (BitWriter.empty.writeBits 1 1 |>.writeBits 2 1)
          (lz77Greedy data) 0 |>.writeHuffCode fixedLitCodes[256]!.1
          fixedLitCodes[256]!.2).bitCount.toNat := by
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

/-! ## Inflate completeness (restricted) -/

open Deflate.Spec in
/-- If spec `decode` succeeds on the bits of a bytestream, native `inflate`
    also succeeds with the same result. Restricted to inputs within fuel
    and size limits. -/
theorem inflate_complete (bytes : ByteArray) (result : List UInt8)
    (hsize : result.length ≤ 256 * 1024 * 1024)
    (hdec : decode (bytesToBits bytes) = some result) :
    Zip.Native.Inflate.inflate bytes =
    .ok ⟨⟨result⟩⟩ := by
  -- Unfold inflate: it calls inflateRaw then discards endPos
  simp only [Inflate.inflate, bind, Except.bind]
  -- Unfold inflateRaw
  simp only [Inflate.inflateRaw, bind, Except.bind]
  -- Build fixed Huffman trees (computationally verified to succeed)
  obtain ⟨fixedLit, hflit⟩ := Zip.Spec.DeflateStoredCorrect.fromLengths_fixedLit_ok
  obtain ⟨fixedDist, hfdist⟩ := Zip.Spec.DeflateStoredCorrect.fromLengths_fixedDist_ok
  rw [hflit, hfdist]; simp only []
  -- decode = decode.go bits [] 10001
  have hgo : decode.go (bytesToBits bytes) [] 10001 = some result := by
    simp only [decode] at hdec; exact hdec
  -- Apply inflateLoop_complete
  have hbr_wf : (Zip.Native.BitReader.mk bytes 0 0).bitOff < 8 := by simp
  have hbr_pos : (Zip.Native.BitReader.mk bytes 0 0).bitOff = 0 ∨
      (Zip.Native.BitReader.mk bytes 0 0).pos <
      (Zip.Native.BitReader.mk bytes 0 0).data.size := by simp
  obtain ⟨endPos, hloop⟩ :=
    Deflate.Correctness.inflateLoop_complete
      ⟨bytes, 0, 0⟩ .empty fixedLit fixedDist
      (256 * 1024 * 1024) result
      hbr_wf hbr_pos hflit hfdist hsize 10001 hgo
  rw [hloop]; simp [pure, Except.pure]

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
