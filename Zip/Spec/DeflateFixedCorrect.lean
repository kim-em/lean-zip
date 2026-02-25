import Zip.Spec.EmitTokensCorrect
import Zip.Spec.DeflateStoredCorrect
import Zip.Spec.LZ77NativeCorrect
import Zip.Spec.InflateComplete
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
- `deflateFixed_spec`: native `deflateFixed` produces spec-level fixed Huffman encoding
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
    (hsize : data.size < 1000000000) :
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
    (hsize : data.size < 500000000) :
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

/-- `deflateFixedBlock` produces a bytestream whose bits are the spec-level
    fixed Huffman encoding of the LZ77 tokens. Generalized over token array. -/
theorem deflateFixedBlock_spec (data : ByteArray) (tokens : Array LZ77Token)
    (henc_some : (Deflate.Spec.encodeSymbols Deflate.Spec.fixedLitLengths
        Deflate.Spec.fixedDistLengths
        (tokensToSymbols tokens)).isSome = true)
    (hempty : data.size = 0 → tokens = #[]) :
    ∃ bits,
      Deflate.Spec.encodeFixed
        (tokensToSymbols tokens) = some bits ∧
      Deflate.Spec.bytesToBits (deflateFixedBlock data tokens) =
        bits ++ List.replicate
          ((8 - bits.length % 8) % 8)
          false := by
  have htoks_eq : tokensToSymbols tokens =
      tokens.toList.map LZ77Token.toLZ77Symbol ++ [.endOfBlock] := rfl
  cases henc_all : Deflate.Spec.encodeSymbols Deflate.Spec.fixedLitLengths
      Deflate.Spec.fixedDistLengths
      (tokensToSymbols tokens) with
  | none => simp [henc_all] at henc_some
  | some allBits =>
    rw [htoks_eq] at henc_all
    obtain ⟨tokBits, eobBits, henc_tok, henc_eob_syms, hallBits_eq⟩ :=
      Deflate.encodeSymbols_append_inv _ _
        (tokens.toList.map LZ77Token.toLZ77Symbol)
        [.endOfBlock] allBits henc_all
    simp only [Deflate.Spec.encodeSymbols] at henc_eob_syms
    cases henc_eob : Deflate.Spec.encodeLitLen Deflate.Spec.fixedLitLengths
        Deflate.Spec.fixedDistLengths .endOfBlock with
    | none => simp [henc_eob] at henc_eob_syms
    | some eobBits' =>
      simp [henc_eob] at henc_eob_syms
      have heob_eq : eobBits = eobBits' := by rw [henc_eob_syms]
      have henc_combined := Deflate.encodeSymbols_append _ _
        (tokens.toList.map LZ77Token.toLZ77Symbol)
        [.endOfBlock] tokBits eobBits henc_tok
        (by simp [Deflate.Spec.encodeSymbols, henc_eob, henc_eob_syms])
      have hencFixed : Deflate.Spec.encodeFixed
          (tokensToSymbols tokens) =
          some ([true, true, false] ++ allBits) := by
        simp only [Deflate.Spec.encodeFixed, htoks_eq, henc_combined, bind,
          Option.bind, pure, Pure.pure]
        rw [hallBits_eq]
      refine ⟨[true, true, false] ++ allBits, hencFixed, ?_⟩
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
      have ⟨heob_cw, heob_len⟩ := Deflate.encodeSymbol_litTable_eq 256 eobBits' henc_eob
      have hemit := emitTokens_spec
        (BitWriter.empty.writeBits 1 1 |>.writeBits 2 1)
        tokens tokBits hwf2 henc_tok
      have hwf3 := emitTokens_wf
        (BitWriter.empty.writeBits 1 1 |>.writeBits 2 1)
        tokens hwf2
      have hwf4 := BitWriter.writeHuffCode_wf
        (emitTokens (BitWriter.empty.writeBits 1 1 |>.writeBits 2 1) tokens 0)
        fixedLitCodes[256]!.1 fixedLitCodes[256]!.2 hwf3 heob_len
      have hbits4 := BitWriter.writeHuffCode_toBits
        (emitTokens (BitWriter.empty.writeBits 1 1 |>.writeBits 2 1) tokens 0)
        fixedLitCodes[256]!.1 fixedLitCodes[256]!.2 hwf3 heob_len
      rw [hemit, hbw2_bits] at hbits4
      have hdef : deflateFixedBlock data tokens =
          (emitTokens (BitWriter.empty.writeBits 1 1 |>.writeBits 2 1)
            tokens 0
            |>.writeHuffCode fixedLitCodes[256]!.1 fixedLitCodes[256]!.2).flush := by
        unfold deflateFixedBlock
        split
        · rename_i hzero
          have hzero' : data.size = 0 := by
            simp only [beq_iff_eq] at hzero; exact hzero
          have htokens : tokens = #[] := hempty hzero'
          have hempty_emit : emitTokens
              (BitWriter.empty.writeBits 1 1 |>.writeBits 2 1) #[] 0 =
              (BitWriter.empty.writeBits 1 1 |>.writeBits 2 1) := by
            simp [emitTokens]
          rw [htokens, hempty_emit]; rfl
        · rfl
      rw [hdef]
      have hflush := BitWriter.flush_toBits _ hwf4
      have hbits_eq : (emitTokens (BitWriter.empty.writeBits 1 1 |>.writeBits 2 1)
          tokens 0 |>.writeHuffCode fixedLitCodes[256]!.1
          fixedLitCodes[256]!.2).toBits =
          [true, true, false] ++ allBits := by
        rw [hbits4, hallBits_eq, heob_eq, heob_cw, List.append_assoc]
      rw [hflush, hbits_eq]
      suffices hmod : (emitTokens (BitWriter.empty.writeBits 1 1 |>.writeBits 2 1)
          tokens 0 |>.writeHuffCode fixedLitCodes[256]!.1
          fixedLitCodes[256]!.2).bitCount.toNat % 8 =
          ([true, true, false] ++ allBits).length % 8 by
        simp only [hmod]
      have htoBits_len : (emitTokens (BitWriter.empty.writeBits 1 1 |>.writeBits 2 1)
          tokens 0 |>.writeHuffCode fixedLitCodes[256]!.1
          fixedLitCodes[256]!.2).toBits.length =
          (emitTokens (BitWriter.empty.writeBits 1 1 |>.writeBits 2 1)
          tokens 0 |>.writeHuffCode fixedLitCodes[256]!.1
          fixedLitCodes[256]!.2).data.data.toList.length * 8 +
          (emitTokens (BitWriter.empty.writeBits 1 1 |>.writeBits 2 1)
          tokens 0 |>.writeHuffCode fixedLitCodes[256]!.1
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
  simp only [deflateFixed]
  exact deflateFixedBlock_spec data (lz77Greedy data)
    (encodeSymbols_tokensToSymbols_isSome data 32768 (by omega) (by omega))
    (fun hzero => by
      simp only [lz77Greedy, show data.size < 3 from by omega, ↓reduceIte]
      have : lz77Greedy.trailing data 0 = [] := by
        unfold lz77Greedy.trailing; simp [show ¬(0 < data.size) from by omega]
      simp [this])

/-! ## Inflate completeness (restricted) -/

open Deflate.Spec in
/-- If spec `decode` succeeds on the bits of a bytestream, native `inflate`
    also succeeds with the same result. Restricted to inputs within fuel
    and size limits. -/
theorem inflate_complete (bytes : ByteArray) (result : List UInt8)
    (hsize : result.length ≤ 1024 * 1024 * 1024)
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
      (1024 * 1024 * 1024) result
      hbr_wf hbr_pos hflit hfdist hsize 10001 hgo
  rw [hloop]; simp [pure, Except.pure]

/-! ## Main roundtrip theorem -/

/-- Native Level 1 roundtrip: compressing with fixed Huffman codes then
    decompressing recovers the original data. The size bound comes from the
    spec decoder's per-block fuel limit (1B symbols, one per byte worst case). -/
theorem inflate_deflateFixed (data : ByteArray)
    (hsize : data.size < 1000000000) :
    Zip.Native.Inflate.inflate (deflateFixed data) = .ok data := by
  -- Step 1: deflateFixed_spec gives bits and bytesToBits relationship
  obtain ⟨bits_enc, henc_fixed, hbytes⟩ := deflateFixed_spec data
  -- Step 2: Extract allBits from encodeFixed
  simp only [Deflate.Spec.encodeFixed] at henc_fixed
  cases henc_syms : Deflate.Spec.encodeSymbols Deflate.Spec.fixedLitLengths
      Deflate.Spec.fixedDistLengths
      (tokensToSymbols (lz77Greedy data)) with
  | none => simp [henc_syms] at henc_fixed
  | some allBits =>
    simp only [henc_syms, bind, Option.bind, pure, Pure.pure] at henc_fixed
    -- bits_enc = [true, true, false] ++ allBits
    have hbits_eq : bits_enc = [true, true, false] ++ allBits :=
      (Option.some.inj henc_fixed).symm
    subst hbits_eq
    -- Step 3: decode succeeds on bytesToBits (deflateFixed data)
    have hdec : Deflate.Spec.decode
        (Deflate.Spec.bytesToBits (deflateFixed data)) =
        some data.data.toList := by
      rw [hbytes]
      exact Deflate.Spec.encodeFixed_decode_append
        (tokensToSymbols (lz77Greedy data))
        data.data.toList allBits _ henc_syms
        (lz77Greedy_resolves data 32768 (by omega))
        (by rw [tokensToSymbols_length]; have := lz77Greedy_size_le data 32768; omega)
        (tokensToSymbols_validSymbolList _)
    -- Step 4: inflate_complete bridges spec decode to native inflate
    have hinf := inflate_complete (deflateFixed data) data.data.toList
      (by simp [Array.length_toList, ByteArray.size_data]; omega) hdec
    simp only at hinf ⊢; exact hinf

/-! ## Iterative LZ77 equivalence -/

/-- The `go` helper is identical between `lz77GreedyIter` and `lz77Greedy`. -/
private theorem go_eq (data : ByteArray) (p1 p2 i maxLen : Nat) :
    lz77GreedyIter.go data p1 p2 i maxLen = lz77Greedy.go data p1 p2 i maxLen := by
  induction h : maxLen - i using Nat.strongRecOn generalizing i with
  | _ n ih =>
    unfold lz77GreedyIter.go lz77Greedy.go
    split
    · split
      · exact ih _ (by omega) _ rfl
      · rfl
    · rfl

/-- The `countMatch` helper is identical between `lz77GreedyIter` and `lz77Greedy`. -/
private theorem countMatch_eq (data : ByteArray) (p1 p2 maxLen : Nat) :
    lz77GreedyIter.countMatch data p1 p2 maxLen =
    lz77Greedy.countMatch data p1 p2 maxLen := by
  simp only [lz77GreedyIter.countMatch, lz77Greedy.countMatch]
  exact go_eq data p1 p2 0 maxLen

/-- The `updateHashes` helper is identical between `lz77GreedyIter` and `lz77Greedy`. -/
private theorem updateHashes_eq (data : ByteArray) (hashSize : Nat)
    (hashTable : Array Nat) (hashValid : Array Bool)
    (pos j matchLen : Nat) :
    lz77GreedyIter.updateHashes data hashSize hashTable hashValid pos j matchLen =
    lz77Greedy.updateHashes data hashSize hashTable hashValid pos j matchLen := by
  induction h : matchLen - j using Nat.strongRecOn generalizing j hashTable hashValid with
  | _ n ih =>
    unfold lz77GreedyIter.updateHashes lz77Greedy.updateHashes
    split
    · split
      · exact ih _ (by omega) _ _ _ rfl
      · exact ih _ (by omega) _ _ _ rfl
    · rfl

/-- The iterative `trailing` is the accumulator version of recursive `trailing`. -/
private theorem trailing_eq (data : ByteArray) (pos : Nat) (acc : Array LZ77Token) :
    lz77GreedyIter.trailing data pos acc =
    acc ++ (lz77Greedy.trailing data pos).toArray := by
  induction h : data.size - pos using Nat.strongRecOn generalizing pos acc with
  | _ n ih =>
    unfold lz77GreedyIter.trailing lz77Greedy.trailing
    split
    · rw [ih _ (by omega) _ _ rfl]
      rw [List.toArray_cons]
      rw [← Array.append_assoc, Array.push_eq_append]
    · simp

/-- The iterative `mainLoop` is the accumulator version of recursive `mainLoop`. -/
private theorem mainLoop_eq (data : ByteArray) (windowSize hashSize : Nat)
    (hashTable : Array Nat) (hashValid : Array Bool) (pos : Nat)
    (acc : Array LZ77Token) :
    lz77GreedyIter.mainLoop data windowSize hashSize hashTable hashValid pos acc =
    acc ++ (lz77Greedy.mainLoop data windowSize hashSize hashTable hashValid pos).toArray := by
  induction h : data.size - pos using Nat.strongRecOn generalizing pos acc hashTable hashValid with
  | _ n ih =>
    unfold lz77GreedyIter.mainLoop lz77Greedy.mainLoop
    simp only [show @lz77GreedyIter.hash3 = @lz77Greedy.hash3 from rfl,
      countMatch_eq, updateHashes_eq]
    split
    · split
      · split
        · split
          · rw [ih _ (by omega) _ _ _ _ rfl]
            rw [List.toArray_cons]
            rw [← Array.append_assoc, Array.push_eq_append]
          · rw [ih _ (by omega) _ _ _ _ rfl]
            rw [List.toArray_cons]
            rw [← Array.append_assoc, Array.push_eq_append]
        · rw [ih _ (by omega) _ _ _ _ rfl]
          rw [List.toArray_cons]
          rw [← Array.append_assoc, Array.push_eq_append]
      · rw [ih _ (by omega) _ _ _ _ rfl]
        rw [List.toArray_cons]
        rw [← Array.append_assoc, Array.push_eq_append]
    · exact trailing_eq data pos acc

/-- The iterative LZ77 greedy matcher produces the same tokens as the
    recursive version. -/
theorem lz77GreedyIter_eq_lz77Greedy (data : ByteArray) (ws : Nat) :
    lz77GreedyIter data ws = lz77Greedy data ws := by
  unfold lz77GreedyIter lz77Greedy
  split
  · rw [trailing_eq]
    simp
  · rw [mainLoop_eq]
    simp

/-- Roundtrip for the iterative fixed Huffman compressor.
    Follows from `lz77GreedyIter_eq_lz77Greedy` + `inflate_deflateFixed`. -/
theorem inflate_deflateFixedIter (data : ByteArray)
    (hsize : data.size < 1000000000) :
    Zip.Native.Inflate.inflate (deflateFixedIter data) = .ok data := by
  unfold deflateFixedIter
  rw [lz77GreedyIter_eq_lz77Greedy]
  exact inflate_deflateFixed data hsize

/-- `deflateLazy` produces a bytestream whose bits are the spec-level
    fixed Huffman encoding of the lazy LZ77 tokens. -/
theorem deflateLazy_spec (data : ByteArray) :
    ∃ bits,
      Deflate.Spec.encodeFixed
        (tokensToSymbols (lz77Lazy data)) = some bits ∧
      Deflate.Spec.bytesToBits (deflateLazy data) =
        bits ++ List.replicate
          ((8 - bits.length % 8) % 8)
          false := by
  simp only [deflateLazy]
  exact deflateFixedBlock_spec data (lz77Lazy data)
    (encodeSymbols_tokensToSymbols_lazy_isSome data 32768 (by omega) (by omega))
    (fun hzero => by
      simp only [lz77Lazy, show data.size < 3 from by omega, ↓reduceIte]
      have : lz77Lazy.trailing data 0 = [] := by
        unfold lz77Lazy.trailing; simp [show ¬(0 < data.size) from by omega]
      simp [this])

/-- Native Level 2 roundtrip: compressing with lazy LZ77 + fixed Huffman codes
    then decompressing recovers the original data. The size bound comes from the
    spec decoder's fuel limit (1B symbols, up to 2 per byte for lazy). -/
theorem inflate_deflateLazy (data : ByteArray)
    (hsize : data.size < 500000000) :
    Zip.Native.Inflate.inflate (deflateLazy data) = .ok data := by
  obtain ⟨bits_enc, henc_fixed, hbytes⟩ := deflateLazy_spec data
  simp only [Deflate.Spec.encodeFixed] at henc_fixed
  cases henc_syms : Deflate.Spec.encodeSymbols Deflate.Spec.fixedLitLengths
      Deflate.Spec.fixedDistLengths
      (tokensToSymbols (lz77Lazy data)) with
  | none => simp [henc_syms] at henc_fixed
  | some allBits =>
    simp only [henc_syms, bind, Option.bind, pure, Pure.pure] at henc_fixed
    have hbits_eq : bits_enc = [true, true, false] ++ allBits :=
      (Option.some.inj henc_fixed).symm
    subst hbits_eq
    have hdec : Deflate.Spec.decode
        (Deflate.Spec.bytesToBits (deflateLazy data)) =
        some data.data.toList := by
      rw [hbytes]
      exact Deflate.Spec.encodeFixed_decode_append
        (tokensToSymbols (lz77Lazy data))
        data.data.toList allBits _ henc_syms
        (lz77Lazy_resolves data 32768 (by omega))
        (by rw [tokensToSymbols_length]; have := lz77Lazy_size_le data 32768; omega)
        (tokensToSymbols_validSymbolList _)
    have hinf := inflate_complete (deflateLazy data) data.data.toList
      (by simp [Array.length_toList, ByteArray.size_data]; omega) hdec
    simp only at hinf ⊢; exact hinf

-- inflate_deflateDynamic is proved in DeflateDynamicCorrect.lean
-- (to avoid circular imports)

end Zip.Native.Deflate
