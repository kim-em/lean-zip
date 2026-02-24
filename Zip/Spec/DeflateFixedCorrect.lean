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

/-! ## encodeSymbols append lemma -/

open Deflate.Spec in
/-- `encodeSymbols` distributes over append with a singleton. -/
private theorem encodeSymbols_append_singleton
    (ll dl : List Nat) (xs : List LZ77Symbol) (s : LZ77Symbol)
    (bits₁ bits₂ : List Bool)
    (h₁ : encodeSymbols ll dl xs = some bits₁)
    (h₂ : encodeLitLen ll dl s = some bits₂) :
    encodeSymbols ll dl (xs ++ [s]) = some (bits₁ ++ bits₂) := by
  induction xs generalizing bits₁ with
  | nil =>
    simp only [encodeSymbols] at h₁
    obtain rfl := Option.some.inj h₁
    simp only [List.nil_append, encodeSymbols, h₂, bind, Option.bind,
      List.nil_append, List.append_nil, pure, Pure.pure]
  | cons x rest ih =>
    simp only [List.cons_append, encodeSymbols] at h₁ ⊢
    cases hx : encodeLitLen ll dl x with
    | none => simp [hx] at h₁
    | some xBits =>
      cases hrest : encodeSymbols ll dl rest with
      | none => simp [hx, hrest] at h₁
      | some restBits =>
        simp [hx, hrest] at h₁
        have ih' := ih restBits hrest
        simp [hx, ih', bind, Option.bind, ← h₁, List.append_assoc]

open Deflate.Spec in
/-- Inverse of `encodeSymbols_append_singleton`: if the whole succeeds,
    both parts succeed and the bits concatenate. -/
private theorem encodeSymbols_append_singleton_inv
    (ll dl : List Nat) (xs : List LZ77Symbol) (s : LZ77Symbol)
    (bits : List Bool)
    (h : encodeSymbols ll dl (xs ++ [s]) = some bits) :
    ∃ bits₁ bits₂,
      encodeSymbols ll dl xs = some bits₁ ∧
      encodeLitLen ll dl s = some bits₂ ∧
      bits = bits₁ ++ bits₂ := by
  induction xs generalizing bits with
  | nil =>
    simp only [List.nil_append, encodeSymbols] at h
    cases henc : encodeLitLen ll dl s with
    | none => simp [henc] at h
    | some sBits =>
      simp [henc] at h
      exact ⟨[], sBits, rfl, rfl, by simp [← h]⟩
  | cons x rest ih =>
    simp only [List.cons_append, encodeSymbols] at h
    cases hx : encodeLitLen ll dl x with
    | none => simp [hx] at h
    | some xBits =>
      cases hrest_all : encodeSymbols ll dl (rest ++ [s]) with
      | none => simp [hx, hrest_all] at h
      | some restAllBits =>
        simp [hx, hrest_all] at h
        obtain ⟨bits₁, bits₂, hrest, henc_s, hrba⟩ := ih restAllBits hrest_all
        refine ⟨xBits ++ bits₁, bits₂, ?_, henc_s, ?_⟩
        · simp only [encodeSymbols, hx, hrest, bind, Option.bind, pure, Pure.pure]
        · rw [← h, hrba, List.append_assoc]

/-! ## emitTokens preserves wf -/

/-- `encodeSymbol_litTable_eq` for the literal case directly gives the length bound. -/
private theorem litCode_len_from_enc (b : UInt8) (cw : List Bool)
    (henc : Deflate.Spec.encodeSymbol
      ((Huffman.Spec.allCodes Deflate.Spec.fixedLitLengths).map fun p => (p.2, p.1))
      b.toNat = some cw) :
    fixedLitCodes[b.toNat]!.2.toNat ≤ 15 :=
  (Deflate.encodeSymbol_litTable_eq b.toNat cw henc).2

set_option maxRecDepth 4096 in
/-- If `encodeLitLen` succeeds for a `.reference`, then spec `findLengthCode`
    and `findDistCode` both succeed, along with both symbol lookups. -/
private theorem encodeLitLen_ref_decompose (len dist : Nat) (bits : List Bool)
    (h : Deflate.Spec.encodeLitLen
      Deflate.Spec.fixedLitLengths Deflate.Spec.fixedDistLengths
      (.reference len dist) = some bits) :
    ∃ lidx lextraN lextraV didx dextraN dextraV lenBits distBits,
      Deflate.Spec.findLengthCode len = some (lidx, lextraN, lextraV) ∧
      Deflate.Spec.encodeSymbol
        ((Huffman.Spec.allCodes Deflate.Spec.fixedLitLengths).map fun p => (p.2, p.1))
        (257 + lidx) = some lenBits ∧
      Deflate.Spec.findDistCode dist = some (didx, dextraN, dextraV) ∧
      Deflate.Spec.encodeSymbol
        ((Huffman.Spec.allCodes Deflate.Spec.fixedDistLengths).map fun p => (p.2, p.1))
        didx = some distBits := by
  simp only [Deflate.Spec.encodeLitLen] at h
  -- Split on each do-notation bind step; use simp to resolve Option bind
  match hflc : Deflate.Spec.findLengthCode len with
  | none => simp [hflc] at h
  | some (lidx, lextraN, lextraV) =>
    simp [hflc] at h
    -- h now has: (encodeSymbol litTable (257 + lidx)).bind (fun lenBits => ...)
    -- Use match to preserve original hypotheses
    match henclen : Deflate.Spec.encodeSymbol
        ((Huffman.Spec.allCodes Deflate.Spec.fixedLitLengths).map fun p => (p.2, p.1))
        (257 + lidx) with
    | none => simp [henclen] at h
    | some lenBits =>
      simp [henclen] at h
      match hfdc : Deflate.Spec.findDistCode dist with
      | none => simp [hfdc] at h
      | some (didx, dextraN, dextraV) =>
        simp [hfdc] at h
        match hencdist : Deflate.Spec.encodeSymbol
            ((Huffman.Spec.allCodes Deflate.Spec.fixedDistLengths).map fun p => (p.2, p.1))
            didx with
        | none => simp [hencdist] at h
        | some distBits =>
          exact ⟨lidx, lextraN, lextraV, didx, dextraN, dextraV, lenBits, distBits,
            rfl, henclen, rfl, hencdist⟩

set_option maxRecDepth 2048 in
/-- `emitTokens` preserves BitWriter well-formedness when encoding succeeds. -/
private theorem emitTokens_wf_go (bw : BitWriter) (tokens : Array LZ77Token)
    (i : Nat) (bits : List Bool) (hwf : bw.wf)
    (henc : Deflate.Spec.encodeSymbols
        Deflate.Spec.fixedLitLengths Deflate.Spec.fixedDistLengths
        ((tokens.toList.drop i).map LZ77Token.toLZ77Symbol) = some bits) :
    (emitTokens bw tokens i).wf := by
  -- Mirror the structure of emitTokens_spec_go exactly
  suffices ∀ k, k = tokens.size - i → (emitTokens bw tokens i).wf by exact this _ rfl
  intro k
  induction k generalizing bw i bits with
  | zero =>
    intro heq
    simp only [emitTokens, show ¬(i < tokens.size) from by omega, ↓reduceDIte]
    exact hwf
  | succ n ih =>
    intro heq
    have hlt : i < tokens.size := by omega
    have hlt_list : i < tokens.toList.length := by simp; exact hlt
    rw [List.drop_eq_getElem_cons hlt_list, List.map_cons] at henc
    obtain ⟨symBits, restBits, hencsym, hencrest, _⟩ :=
      Deflate.encodeSymbols_cons_some _ _ _ _ _ henc
    have htoList : tokens[i] = tokens.toList[i] := by simp [Array.getElem_toList]
    unfold emitTokens
    simp only [dif_pos hlt]
    cases htok : tokens[i] with
    | literal b =>
      simp only [array_get!Internal_eq]
      -- Extract length bound from encoding success
      have htok_list' : tokens.toList[i] = .literal b := by rw [← htoList]; exact htok
      simp only [LZ77Token.toLZ77Symbol, htok_list'] at hencsym
      simp only [Deflate.Spec.encodeLitLen] at hencsym
      have hllen := litCode_len_from_enc b symBits hencsym
      exact ih _ (i + 1) restBits (BitWriter.writeHuffCode_wf bw _ _ hwf hllen) hencrest (by omega)
    | reference len dist =>
      simp only [array_get!Internal_eq]
      have htok_list : tokens.toList[i] = .reference len dist := by rw [← htoList]; exact htok
      -- Use decomposition: encodeLitLen success ⟹ findLengthCode/findDistCode success
      have hencsym_ref : Deflate.Spec.encodeLitLen
          Deflate.Spec.fixedLitLengths Deflate.Spec.fixedDistLengths
          (.reference len dist) = some symBits := by
        simp only [LZ77Token.toLZ77Symbol, htok_list] at hencsym; exact hencsym
      obtain ⟨lidx, lextraN, lextraV, didx, dextraN, dextraV, lenBits, distBits,
        hflc, henclen, hfdc, hencdist⟩ :=
        encodeLitLen_ref_decompose len dist symBits hencsym_ref
      -- Bridge spec → native
      have hnflc := Deflate.findLengthCode_agree len lidx lextraN lextraV hflc
      have hnfdc := Deflate.findDistCode_agree dist didx dextraN dextraV hfdc
      -- Rewrite native matches using the bridge results
      simp only [hnflc, hnfdc]
      -- Get bounds from spec
      have hflc_spec := Deflate.Spec.findLengthCode_spec len lidx lextraN lextraV hflc
      have hfdc_spec := Deflate.Spec.findDistCode_spec dist didx dextraN dextraV hfdc
      -- Get length bounds for writeHuffCode_wf
      have ⟨_, hllen⟩ := Deflate.encodeSymbol_litTable_eq (257 + lidx) lenBits henclen
      have ⟨_, hdlen⟩ := Deflate.encodeSymbol_distTable_eq didx distBits hencdist
      have lextraN_le : lextraN ≤ 25 := by
        rw [hflc_spec.2.2.1]
        exact Nat.le_trans (Deflate.lengthExtra_le_5 lidx hflc_spec.1) (by omega)
      have dextraN_le : dextraN ≤ 25 := by
        rw [hfdc_spec.2.2.1]
        exact Nat.le_trans (Deflate.distExtra_le_13 didx hfdc_spec.1) (by omega)
      -- Align 257 + lidx ↔ lidx + 257
      have h257 : 257 + lidx = lidx + 257 := by omega
      rw [h257] at hllen
      -- Chain wf through all BitWriter operations
      have hwf1 : (bw.writeHuffCode fixedLitCodes[lidx + 257]!.1 fixedLitCodes[lidx + 257]!.2).wf :=
        BitWriter.writeHuffCode_wf bw _ _ hwf hllen
      have hwf2 := BitWriter.writeBits_wf _ lextraN lextraV.toUInt32 hwf1 lextraN_le
      have hwf3 : (((bw.writeHuffCode fixedLitCodes[lidx + 257]!.1 fixedLitCodes[lidx + 257]!.2).writeBits
            lextraN lextraV.toUInt32).writeHuffCode fixedDistCodes[didx]!.1 fixedDistCodes[didx]!.2).wf :=
        BitWriter.writeHuffCode_wf _ _ _ hwf2 hdlen
      have hwf4 := BitWriter.writeBits_wf _ dextraN dextraV.toUInt32 hwf3 dextraN_le
      exact ih _ (i + 1) restBits hwf4 hencrest (by omega)

/-- `deflateFixed` produces a bytestream whose bits are the spec-level
    fixed Huffman encoding of the LZ77 tokens. -/
theorem deflateFixed_spec (data : ByteArray) :
    ∃ bits,
      Deflate.Spec.encodeFixed
        (tokensToSymbols (lz77Greedy data)) = some bits ∧
      Deflate.Spec.bytesToBits (deflateFixed data) =
        bits ++ List.replicate
          ((8 - (Deflate.Spec.bytesToBits (deflateFixed data)).length % 8) % 8)
          false := by
  -- Step 1: encodeSymbols succeeds on tokensToSymbols
  have henc_some := encodeSymbols_tokensToSymbols_isSome data 32768 (by omega) (by omega)
  -- Step 2: split into tokenBits and eobBits
  -- tokensToSymbols = tokens.map toLZ77Symbol ++ [.endOfBlock]
  have htoks : tokensToSymbols (lz77Greedy data) =
      (lz77Greedy data).toList.map LZ77Token.toLZ77Symbol ++ [.endOfBlock] := rfl
  -- Get the full encoding
  cases hfull : Deflate.Spec.encodeSymbols Deflate.Spec.fixedLitLengths
      Deflate.Spec.fixedDistLengths (tokensToSymbols (lz77Greedy data)) with
  | none => simp [hfull] at henc_some
  | some fullBits =>
    -- encodeFixed succeeds
    have hencFixed : Deflate.Spec.encodeFixed (tokensToSymbols (lz77Greedy data)) =
        some ([true, true, false] ++ fullBits) := by
      simp [Deflate.Spec.encodeFixed, hfull]
    refine ⟨[true, true, false] ++ fullBits, hencFixed, ?_⟩
    -- Now prove bytesToBits (deflateFixed data) = [true, true, false] ++ fullBits ++ replicate 0 false
    -- Since bytesToBits always gives length divisible by 8, replicate 0 = []
    have hpad : List.replicate ((8 - (Deflate.Spec.bytesToBits (deflateFixed data)).length % 8) % 8) false = [] := by
      rw [Deflate.Spec.bytesToBits_length]
      simp [Nat.mul_mod_right]
    rw [hpad, List.append_nil]
    -- Now prove: bytesToBits (deflateFixed data) = [true, true, false] ++ fullBits
    -- Split fullBits via tokensToSymbols = map toLZ77Symbol ++ [.endOfBlock]
    rw [htoks] at hfull
    -- Decompose: encodeSymbols on (map toLZ77Symbol ++ [endOfBlock]) = tokenBits ++ eobBits
    obtain ⟨tokenBits, eobBits, henc_toks, henc_eob, hfull_eq⟩ :=
      encodeSymbols_append_singleton_inv _ _ _ _ _ hfull
    rw [hfull_eq]
    -- Remaining: bytesToBits (deflateFixed data) = [true, true, false] ++ tokenBits ++ eobBits
    -- This requires chaining BitWriter lemmas:
    -- 1. flush_toBits on the final bw.flush
    -- 2. writeHuffCode_toBits for endOfBlock (code 256)
    -- 3. emitTokens_spec for the tokens
    -- 4. writeBits_toBits for the header (BFINAL=1, BTYPE=01)
    -- 5. Show writeBitsLSB 1 1 ++ writeBitsLSB 2 1 = [true, true, false]
    sorry

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
