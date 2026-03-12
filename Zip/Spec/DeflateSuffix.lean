import Zip.Spec.Deflate

/-!
# DEFLATE Suffix Invariance Theorems

Proves that spec decode functions are suffix-invariant: appending extra bits
to the input appends them to the remainder without affecting the decoded result.
This property is essential for roundtrip proofs, where the compressor output
is decoded as a prefix of a longer bitstream.

The key theorem is `decode_go_suffix`, which shows that the top-level block
decoder ignores trailing bits (provided the suffix length is a multiple of 8,
needed for stored blocks).
-/

namespace Deflate.Spec

/-- `readBitsLSB` is suffix-invariant: appending bits to the input
    appends them to the remainder. -/
theorem readBitsLSB_append (n : Nat) (bits suffix : List Bool)
    (val : Nat) (rest : List Bool)
    (h : readBitsLSB n bits = some (val, rest)) :
    readBitsLSB n (bits ++ suffix) = some (val, rest ++ suffix) := by
  induction n generalizing bits val rest with
  | zero =>
    simp only [readBitsLSB, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; simp only [readBitsLSB]
  | succ k ih =>
    cases bits with
    | nil => simp only [readBitsLSB] at h; contradiction
    | cons b bs =>
      simp only [readBitsLSB, List.cons_append] at h ⊢
      cases hk : readBitsLSB k bs with
      | none => simp only [hk] at h; contradiction
      | some p =>
        obtain ⟨v, rem⟩ := p
        simp only [hk] at h; obtain ⟨rfl, rfl⟩ := h
        rw [ih bs v rem hk]; rfl

/-- Prefix-free condition for a swapped `allCodes` table. -/
private theorem allCodes_swapped_prefix_free (lengths : List Nat) (maxBits : Nat)
    (hv : Huffman.Spec.ValidLengths lengths maxBits) :
    ∀ cw₁ s₁ cw₂ s₂,
      (cw₁, s₁) ∈ (Huffman.Spec.allCodes lengths maxBits).map (fun (sym, cw) => (cw, sym)) →
      (cw₂, s₂) ∈ (Huffman.Spec.allCodes lengths maxBits).map (fun (sym, cw) => (cw, sym)) →
      (cw₁, s₁) ≠ (cw₂, s₂) → ¬cw₁.IsPrefix cw₂ := by
  intro cw₁ s₁ cw₂ s₂ h₁ h₂ hne
  simp only [List.mem_map, Prod.mk.injEq] at h₁ h₂
  obtain ⟨⟨sym₁, cw₁'⟩, hmem₁, rfl, rfl⟩ := h₁
  obtain ⟨⟨sym₂, cw₂'⟩, hmem₂, rfl, rfl⟩ := h₂
  have hne_sym : sym₁ ≠ sym₂ := by
    intro heq; subst heq
    have h₁' := hmem₁; have h₂' := hmem₂
    rw [Huffman.Spec.allCodes_mem_iff] at h₁' h₂'
    have := Option.some.inj (h₁'.2.symm.trans h₂'.2)
    exact hne (by subst this; rfl)
  exact Huffman.Spec.allCodes_prefix_free_of_ne lengths maxBits hv sym₁ sym₂ _ _ hmem₁ hmem₂ hne_sym

set_option maxRecDepth 2048 in
/-- `decodeLitLen` is suffix-invariant. -/
theorem decodeLitLen_append (litLengths distLengths : List Nat)
    (bits suffix : List Bool) (sym : LZ77Symbol) (rest : List Bool)
    (hvl : Huffman.Spec.ValidLengths litLengths 15)
    (hvd : Huffman.Spec.ValidLengths distLengths 15)
    (h : decodeLitLen litLengths distLengths bits = some (sym, rest)) :
    decodeLitLen litLengths distLengths (bits ++ suffix) = some (sym, rest ++ suffix) := by
  simp only [decodeLitLen] at h ⊢
  -- Thread through the Huffman lit decode
  cases hld : Huffman.Spec.decode ((Huffman.Spec.allCodes litLengths).map fun (sym, cw) => (cw, sym)) bits with
  | none => simp only [hld] at h; contradiction
  | some p =>
    obtain ⟨litSym, bits₁⟩ := p
    rw [hld] at h; dsimp only [bind, Option.bind] at h ⊢
    rw [Huffman.Spec.decode_suffix _ bits suffix litSym bits₁ hld
        (allCodes_swapped_prefix_free litLengths 15 hvl)]
    dsimp only [bind, Option.bind] at h ⊢
    by_cases hlit : litSym < 256
    · rw [if_pos hlit] at h ⊢
      obtain ⟨rfl, rfl⟩ := Option.some.inj h; rfl
    · rw [if_neg hlit] at h ⊢
      by_cases heob : (litSym == 256) = true
      · rw [if_pos heob] at h ⊢
        obtain ⟨rfl, rfl⟩ := Option.some.inj h; rfl
      · rw [if_neg heob] at h ⊢
        -- length/distance code — thread through do-notation
        cases hlb : lengthBase[litSym - 257]? with
        | none => simp only [hlb] at h; contradiction
        | some base =>
          simp only [hlb] at h ⊢
          cases hle : lengthExtra[litSym - 257]? with
          | none => simp only [hle] at h; contradiction
          | some extra =>
            simp only [hle] at h ⊢
            cases hrb : readBitsLSB extra bits₁ with
            | none => simp only [hrb] at h; contradiction
            | some q =>
              obtain ⟨extraVal, bits₂⟩ := q
              simp only [hrb] at h ⊢
              rw [readBitsLSB_append extra bits₁ suffix extraVal bits₂ hrb]
              cases hdd : Huffman.Spec.decode ((Huffman.Spec.allCodes distLengths).map fun (s, cw) => (cw, s)) bits₂ with
              | none => simp only [hdd] at h; contradiction
              | some r =>
                obtain ⟨dSym, bits₃⟩ := r
                simp only [hdd] at h ⊢
                rw [Huffman.Spec.decode_suffix _ bits₂ suffix dSym bits₃ hdd
                    (allCodes_swapped_prefix_free distLengths 15 hvd)]
                cases hdb : distBase[dSym]? with
                | none => simp only [hdb] at h; contradiction
                | some dBase =>
                  simp only [hdb] at h ⊢
                  cases hde : distExtra[dSym]? with
                  | none => simp only [hde] at h; contradiction
                  | some dExtra =>
                    simp only [hde] at h ⊢
                    cases hrbd : readBitsLSB dExtra bits₃ with
                    | none => simp only [hrbd] at h; contradiction
                    | some s =>
                      obtain ⟨dExtraVal, bits₄⟩ := s
                      simp only [hrbd] at h ⊢
                      rw [readBitsLSB_append dExtra bits₃ suffix dExtraVal bits₄ hrbd]
                      obtain ⟨rfl, rfl⟩ := Option.some.inj h; rfl

/-- `decodeSymbols` is suffix-invariant. -/
theorem decodeSymbols_append (litLengths distLengths : List Nat)
    (bits suffix : List Bool)
    (syms : List LZ77Symbol) (rest : List Bool)
    (hvl : Huffman.Spec.ValidLengths litLengths 15)
    (hvd : Huffman.Spec.ValidLengths distLengths 15)
    (h : decodeSymbols litLengths distLengths bits = some (syms, rest)) :
    decodeSymbols litLengths distLengths (bits ++ suffix) =
      some (syms, rest ++ suffix) := by
  unfold decodeSymbols at h ⊢
  cases hlit : decodeLitLen litLengths distLengths bits with
  | none => simp only [hlit] at h; contradiction
  | some p =>
    obtain ⟨sym, bits'⟩ := p
    rw [hlit] at h; dsimp only [bind, Option.bind] at h ⊢
    rw [decodeLitLen_append litLengths distLengths bits suffix sym bits' hvl hvd hlit]
    dsimp only [bind, Option.bind]
    match hsym : sym with
    | .endOfBlock =>
      obtain ⟨rfl, rfl⟩ := Option.some.inj h; rfl
    | .literal _ | .reference .. =>
      by_cases hlt : bits'.length < bits.length
      · simp only [dif_pos hlt] at h
        have hlt' : (bits' ++ suffix).length < (bits ++ suffix).length := by
          simp only [List.length_append]; omega
        rw [dif_pos hlt']
        cases hrec : decodeSymbols litLengths distLengths bits' with
        | none => simp only [hrec] at h; contradiction
        | some q =>
          obtain ⟨restSyms, bits''⟩ := q
          rw [hrec] at h; dsimp only [bind, Option.bind] at h
          have ih := decodeSymbols_append litLengths distLengths bits' suffix
            restSyms bits'' hvl hvd hrec
          rw [ih]; dsimp only [bind, Option.bind]
          obtain ⟨rfl, rfl⟩ := Option.some.inj h; rfl
      · simp only [dif_neg hlt] at h
        contradiction
termination_by bits.length

/-- `readNBytes` is suffix-invariant. -/
private theorem readNBytes_append (n : Nat) (bits suffix : List Bool)
    (acc bytes : List UInt8) (rest : List Bool)
    (h : decodeStored.readNBytes n bits acc = some (bytes, rest)) :
    decodeStored.readNBytes n (bits ++ suffix) acc = some (bytes, rest ++ suffix) := by
  induction n generalizing bits acc bytes rest with
  | zero =>
    simp only [decodeStored.readNBytes, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; simp only [decodeStored.readNBytes]
  | succ k ih =>
    unfold decodeStored.readNBytes at h ⊢
    cases hrb : readBitsLSB 8 bits with
    | none => simp only [hrb] at h; contradiction
    | some p =>
      obtain ⟨v, bits'⟩ := p
      rw [hrb] at h; dsimp only [bind, Option.bind] at h ⊢
      rw [readBitsLSB_append 8 bits suffix v bits' hrb]
      dsimp only [bind, Option.bind]
      exact ih bits' (acc ++ [v.toUInt8]) bytes rest h

/-- `alignToByte (bits ++ suffix) = alignToByte bits ++ suffix`
    when `suffix.length % 8 = 0`. -/
private theorem alignToByte_append (bits suffix : List Bool)
    (hsuf : suffix.length % 8 = 0) :
    alignToByte (bits ++ suffix) = alignToByte bits ++ suffix := by
  simp only [alignToByte, List.length_append]
  rw [show (bits.length + suffix.length) % 8 = bits.length % 8 by omega]
  exact List.drop_append_of_le_length (Nat.mod_le _ _)

/-- `decodeStored` is suffix-invariant when suffix is byte-aligned. -/
theorem decodeStored_append (bits suffix : List Bool)
    (bytes : List UInt8) (rest : List Bool)
    (hsuf : suffix.length % 8 = 0)
    (h : decodeStored bits = some (bytes, rest)) :
    decodeStored (bits ++ suffix) = some (bytes, rest ++ suffix) := by
  simp only [decodeStored] at h ⊢
  rw [alignToByte_append bits suffix hsuf]
  -- Thread readBitsLSB 16 for LEN
  cases hrl : readBitsLSB 16 (alignToByte bits) with
  | none => simp only [hrl] at h; contradiction
  | some p =>
    obtain ⟨len, bits₁⟩ := p
    rw [hrl] at h; dsimp only [bind, Option.bind] at h ⊢
    rw [readBitsLSB_append 16 (alignToByte bits) suffix len bits₁ hrl]
    dsimp only [bind, Option.bind]
    -- Thread readBitsLSB 16 for NLEN
    cases hrn : readBitsLSB 16 bits₁ with
    | none => simp only [hrn] at h; contradiction
    | some q =>
      obtain ⟨nlen, bits₂⟩ := q
      rw [hrn] at h; dsimp only [bind, Option.bind] at h ⊢
      rw [readBitsLSB_append 16 bits₁ suffix nlen bits₂ hrn]
      dsimp only [bind, Option.bind]
      -- Guard passes identically
      by_cases hg : (len ^^^ nlen == 0xFFFF) = true
      · simp only [guard, hg] at h ⊢
        exact readNBytes_append len bits₂ suffix [] bytes rest h
      · simp only [guard, hg] at h; contradiction

/-- `readCLLengths` is suffix-invariant. -/
private theorem readCLLengths_append (n idx : Nat) (acc : List Nat)
    (bits suffix : List Bool)
    (result : List Nat) (rest : List Bool)
    (h : Deflate.Spec.readCLLengths n idx acc bits = some (result, rest)) :
    Deflate.Spec.readCLLengths n idx acc (bits ++ suffix) = some (result, rest ++ suffix) := by
  induction n generalizing idx acc bits result rest with
  | zero =>
    simp only [Deflate.Spec.readCLLengths, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; simp only [Deflate.Spec.readCLLengths]
  | succ k ih =>
    unfold Deflate.Spec.readCLLengths at h ⊢
    cases hrb : readBitsLSB 3 bits with
    | none => simp only [hrb] at h; contradiction
    | some p =>
      obtain ⟨v, bits'⟩ := p
      rw [hrb] at h; dsimp only [bind, Option.bind] at h ⊢
      rw [readBitsLSB_append 3 bits suffix v bits' hrb]
      exact ih (idx + 1) (acc.set (codeLengthOrder[idx]!) v) bits' result rest h

/-- `decodeCLSymbols` is suffix-invariant. -/
private theorem decodeCLSymbols_append
    (clTable : List (Huffman.Spec.Codeword × Nat))
    (totalCodes : Nat) (acc : List Nat) (bits suffix : List Bool)
    (result : List Nat) (rest : List Bool)
    (hpf : ∀ cw₁ s₁ cw₂ s₂, (cw₁, s₁) ∈ clTable → (cw₂, s₂) ∈ clTable →
      (cw₁, s₁) ≠ (cw₂, s₂) → ¬cw₁.IsPrefix cw₂)
    (h : decodeDynamicTables.decodeCLSymbols clTable totalCodes acc bits =
      some (result, rest)) :
    decodeDynamicTables.decodeCLSymbols clTable totalCodes acc (bits ++ suffix) =
      some (result, rest ++ suffix) := by
  have hrec : ∀ (acc' : List Nat) (bits' : List Bool)
      (result' : List Nat) (rest' : List Bool),
      totalCodes - acc'.length < totalCodes - acc.length →
      decodeDynamicTables.decodeCLSymbols clTable totalCodes acc' bits' =
        some (result', rest') →
      decodeDynamicTables.decodeCLSymbols clTable totalCodes acc' (bits' ++ suffix) =
        some (result', rest' ++ suffix) :=
    fun acc' bits' result' rest' hlt h' =>
      decodeCLSymbols_append clTable totalCodes acc' bits' suffix result' rest' hpf h'
  unfold decodeDynamicTables.decodeCLSymbols at h ⊢
  by_cases hge : acc.length ≥ totalCodes
  · rw [if_pos hge] at h ⊢
    obtain ⟨rfl, rfl⟩ := Option.some.inj h; rfl
  · rw [if_neg hge] at h ⊢
    cases hdec : Huffman.Spec.decode clTable bits with
    | none => simp only [hdec] at h; contradiction
    | some p =>
      obtain ⟨sym, bits'⟩ := p
      rw [hdec] at h; dsimp only [bind, Option.bind] at h ⊢
      rw [Huffman.Spec.decode_suffix clTable bits suffix sym bits' hdec hpf]
      dsimp only [bind, Option.bind]
      by_cases hsym16 : sym < 16
      · rw [if_pos hsym16] at h ⊢
        exact hrec _ _ _ _ (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) h
      · rw [if_neg hsym16] at h ⊢
        by_cases hsym16eq : (sym == 16) = true
        · rw [if_pos hsym16eq] at h ⊢
          by_cases hg : acc.length == 0
          · simp only [if_pos hg] at h; contradiction
          · rw [if_neg hg] at h ⊢
            cases hrb : readBitsLSB 2 bits' with
            | none => simp only [hrb] at h; contradiction
            | some q =>
              obtain ⟨rep, bits''⟩ := q
              rw [hrb] at h; dsimp only [bind, Option.bind] at h ⊢
              rw [readBitsLSB_append 2 bits' suffix rep bits'' hrb]
              dsimp only [bind, Option.bind]
              by_cases hg2 : (acc ++ List.replicate (rep + 3) acc.getLast!).length ≤ totalCodes
              · simp only [hg2, ↓reduceIte] at h ⊢
                exact hrec _ _ _ _ (by simp only [List.length_append, List.length_replicate]; omega) h
              · simp only [hg2, ↓reduceIte] at h; contradiction
        · rw [if_neg hsym16eq] at h ⊢
          by_cases hsym17 : (sym == 17) = true
          · rw [if_pos hsym17] at h ⊢
            cases hrb : readBitsLSB 3 bits' with
            | none => simp only [hrb] at h; contradiction
            | some q =>
              obtain ⟨rep, bits''⟩ := q
              rw [hrb] at h; dsimp only [bind, Option.bind] at h ⊢
              rw [readBitsLSB_append 3 bits' suffix rep bits'' hrb]
              dsimp only [bind, Option.bind]
              by_cases hg : (acc ++ List.replicate (rep + 3) 0).length ≤ totalCodes
              · simp only [hg, ↓reduceIte] at h ⊢
                exact hrec _ _ _ _ (by simp only [List.length_append, List.length_replicate]; omega) h
              · simp only [hg, ↓reduceIte] at h; contradiction
          · rw [if_neg hsym17] at h ⊢
            by_cases hsym18 : (sym == 18) = true
            · rw [if_pos hsym18] at h ⊢
              cases hrb : readBitsLSB 7 bits' with
              | none => simp only [hrb] at h; contradiction
              | some q =>
                obtain ⟨rep, bits''⟩ := q
                rw [hrb] at h; dsimp only [bind, Option.bind] at h ⊢
                rw [readBitsLSB_append 7 bits' suffix rep bits'' hrb]
                dsimp only [bind, Option.bind]
                by_cases hg : (acc ++ List.replicate (rep + 11) 0).length ≤ totalCodes
                · simp only [hg, ↓reduceIte] at h ⊢
                  exact hrec _ _ _ _ (by simp only [List.length_append, List.length_replicate]; omega) h
                · simp only [hg, ↓reduceIte] at h; contradiction
            · rw [if_neg hsym18] at h ⊢
              contradiction
termination_by totalCodes - acc.length

private theorem replicate_19_zero :
    List.replicate 19 0 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide

/-- `decodeDynamicTables` is suffix-invariant. -/
theorem decodeDynamicTables_append (bits suffix : List Bool)
    (litLens distLens : List Nat) (rest : List Bool)
    (h : decodeDynamicTables bits = some (litLens, distLens, rest)) :
    decodeDynamicTables (bits ++ suffix) = some (litLens, distLens, rest ++ suffix) := by
  unfold decodeDynamicTables at h ⊢
  cases h5 : readBitsLSB 5 bits with
  | none =>
    simp only [h5, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at h
  | some p₁ =>
    obtain ⟨hlit, bits₁⟩ := p₁
    cases h5d : readBitsLSB 5 bits₁ with
    | none =>
      simp only [h5, h5d, Option.bind_eq_bind, Option.bind_some,
        Option.bind_none, reduceCtorEq] at h
    | some p₂ =>
      obtain ⟨hdist, bits₂⟩ := p₂
      cases h4 : readBitsLSB 4 bits₂ with
      | none =>
        simp only [h5, h5d, h4, Option.bind_eq_bind, Option.bind_some,
          Option.bind_none, reduceCtorEq] at h
      | some p₃ =>
        obtain ⟨hclen, bits₃⟩ := p₃
        cases hcl : Deflate.Spec.readCLLengths (hclen + 4) 0
            (List.replicate 19 0) bits₃ with
        | none =>
          rw [replicate_19_zero] at hcl
          simp only [h5, h5d, h4, hcl, replicate_19_zero,
            Option.bind_eq_bind, Option.bind_some,
            Option.bind_none, reduceCtorEq] at h
        | some p₄ =>
          obtain ⟨clLengths, bits₄⟩ := p₄
          have hcl' := replicate_19_zero ▸ hcl
          by_cases hvCL : Huffman.Spec.ValidLengths clLengths 7
          · cases hcls : decodeDynamicTables.decodeCLSymbols
                ((Huffman.Spec.allCodes clLengths 7).map fun (sym, cw) => (cw, sym))
                (hlit + 257 + (hdist + 1)) [] bits₄ with
            | none =>
              simp only [h5, h5d, h4, hcl', hvCL, hcls, replicate_19_zero,
                guard, pure, Pure.pure, failure, Alternative.failure,
                Option.bind_eq_bind, Option.bind_some, Option.bind_none,
                ↓reduceIte, reduceCtorEq] at h
            | some p₅ =>
              obtain ⟨codeLengths, bits₅⟩ := p₅
              by_cases hlen : codeLengths.length = hlit + 257 + (hdist + 1)
              · by_cases hvLL : Huffman.Spec.ValidLengths
                    (codeLengths.take (hlit + 257)) 15
                · by_cases hvDL : Huffman.Spec.ValidLengths
                      (codeLengths.drop (hlit + 257)) 15
                  · simp only [h5, h5d, h4, hcl', hvCL, hcls, hlen, hvLL, hvDL,
                      replicate_19_zero,
                      guard, pure, Pure.pure, failure, Alternative.failure,
                      Option.bind_eq_bind, Option.bind_some,
                      ↓reduceIte, beq_iff_eq, Option.some.injEq,
                      Prod.mk.injEq] at h
                    obtain ⟨rfl, rfl, rfl⟩ := h
                    have h5' := readBitsLSB_append 5 bits suffix hlit bits₁ h5
                    have h5d' := readBitsLSB_append 5 bits₁ suffix hdist bits₂ h5d
                    have h4' := readBitsLSB_append 4 bits₂ suffix hclen bits₃ h4
                    have hcl_a := replicate_19_zero ▸
                      readCLLengths_append _ 0 _ bits₃ suffix clLengths bits₄ hcl
                    have hcls' := decodeCLSymbols_append _ _ [] bits₄ suffix
                        codeLengths bits₅
                        (allCodes_swapped_prefix_free clLengths 7 hvCL) hcls
                    simp only [h5', h5d', h4', hcl_a, hvCL, hcls', hlen, hvLL, hvDL,
                      replicate_19_zero,
                      guard, pure, Pure.pure, failure, Alternative.failure,
                      Option.bind_eq_bind, Option.bind_some,
                      ↓reduceIte, beq_iff_eq]
                  · simp only [h5, h5d, h4, hcl', hvCL, hcls, hlen, hvLL, hvDL,
                      replicate_19_zero,
                      guard, pure, Pure.pure, failure, Alternative.failure,
                      Option.bind_eq_bind, Option.bind_some, Option.bind_none,
                      ↓reduceIte, beq_iff_eq, reduceCtorEq] at h
                · simp only [h5, h5d, h4, hcl', hvCL, hcls, hlen, hvLL,
                    replicate_19_zero,
                    guard, pure, Pure.pure, failure, Alternative.failure,
                    Option.bind_eq_bind, Option.bind_some, Option.bind_none,
                    ↓reduceIte, beq_iff_eq, reduceCtorEq] at h
              · simp only [h5, h5d, h4, hcl', hvCL, hcls, hlen,
                  replicate_19_zero,
                  guard, pure, Pure.pure, failure, Alternative.failure,
                  Option.bind_eq_bind, Option.bind_some, Option.bind_none,
                  ↓reduceIte, beq_iff_eq, reduceCtorEq] at h
          · simp only [h5, h5d, h4, hcl', hvCL,
              replicate_19_zero,
              guard, pure, Pure.pure, failure, Alternative.failure,
              Option.bind_eq_bind, Option.bind_some, Option.bind_none,
              ↓reduceIte, reduceCtorEq] at h

/-- If `decodeDynamicTables` succeeds, both returned length lists are valid. -/
private theorem decodeDynamicTables_valid_both (bits : List Bool)
    (litLens distLens : List Nat) (rest : List Bool)
    (h : decodeDynamicTables bits = some (litLens, distLens, rest)) :
    Huffman.Spec.ValidLengths litLens 15 ∧ Huffman.Spec.ValidLengths distLens 15 := by
  unfold decodeDynamicTables at h
  cases h5 : readBitsLSB 5 bits with
  | none =>
    simp only [h5, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at h
  | some p₁ =>
    obtain ⟨hlit, bits₁⟩ := p₁
    cases h5d : readBitsLSB 5 bits₁ with
    | none =>
      simp only [h5, h5d, Option.bind_eq_bind, Option.bind_some,
        Option.bind_none, reduceCtorEq] at h
    | some p₂ =>
      obtain ⟨hdist, bits₂⟩ := p₂
      cases h4 : readBitsLSB 4 bits₂ with
      | none =>
        simp only [h5, h5d, h4, Option.bind_eq_bind, Option.bind_some,
          Option.bind_none, reduceCtorEq] at h
      | some p₃ =>
        obtain ⟨hclen, bits₃⟩ := p₃
        cases hcl : Deflate.Spec.readCLLengths (hclen + 4) 0
            (List.replicate 19 0) bits₃ with
        | none =>
          rw [replicate_19_zero] at hcl
          simp only [h5, h5d, h4, hcl, replicate_19_zero,
            Option.bind_eq_bind, Option.bind_some,
            Option.bind_none, reduceCtorEq] at h
        | some p₄ =>
          obtain ⟨clLengths, bits₄⟩ := p₄
          have hcl' := replicate_19_zero ▸ hcl
          by_cases hvCL : Huffman.Spec.ValidLengths clLengths 7
          · cases hcls : decodeDynamicTables.decodeCLSymbols
                ((Huffman.Spec.allCodes clLengths 7).map fun (sym, cw) => (cw, sym))
                (hlit + 257 + (hdist + 1)) [] bits₄ with
            | none =>
              simp only [h5, h5d, h4, hcl', hvCL, hcls, replicate_19_zero,
                guard, pure, Pure.pure, failure, Alternative.failure,
                Option.bind_eq_bind, Option.bind_some, Option.bind_none,
                ↓reduceIte, reduceCtorEq] at h
            | some p₅ =>
              obtain ⟨codeLengths, bits₅⟩ := p₅
              by_cases hlen : codeLengths.length = hlit + 257 + (hdist + 1)
              · by_cases hvLL : Huffman.Spec.ValidLengths
                    (codeLengths.take (hlit + 257)) 15
                · by_cases hvDL : Huffman.Spec.ValidLengths
                      (codeLengths.drop (hlit + 257)) 15
                  · simp only [h5, h5d, h4, hcl', hvCL, hcls, hlen, hvLL, hvDL,
                      replicate_19_zero,
                      guard, pure, Pure.pure, failure, Alternative.failure,
                      Option.bind_eq_bind, Option.bind_some,
                      ↓reduceIte, beq_iff_eq, Option.some.injEq,
                      Prod.mk.injEq] at h
                    exact ⟨h.1 ▸ hvLL, h.2.1 ▸ hvDL⟩
                  · simp only [h5, h5d, h4, hcl', hvCL, hcls, hlen, hvLL, hvDL,
                      replicate_19_zero,
                      guard, pure, Pure.pure, failure, Alternative.failure,
                      Option.bind_eq_bind, Option.bind_some, Option.bind_none,
                      ↓reduceIte, beq_iff_eq, reduceCtorEq] at h
                · simp only [h5, h5d, h4, hcl', hvCL, hcls, hlen, hvLL,
                    replicate_19_zero,
                    guard, pure, Pure.pure, failure, Alternative.failure,
                    Option.bind_eq_bind, Option.bind_some, Option.bind_none,
                    ↓reduceIte, beq_iff_eq, reduceCtorEq] at h
              · simp only [h5, h5d, h4, hcl', hvCL, hcls, hlen,
                  replicate_19_zero,
                  guard, pure, Pure.pure, failure, Alternative.failure,
                  Option.bind_eq_bind, Option.bind_some, Option.bind_none,
                  ↓reduceIte, beq_iff_eq, reduceCtorEq] at h
          · simp only [h5, h5d, h4, hcl', hvCL,
              replicate_19_zero,
              guard, pure, Pure.pure, failure, Alternative.failure,
              Option.bind_eq_bind, Option.bind_some, Option.bind_none,
              ↓reduceIte, reduceCtorEq] at h

/-- If `decodeDynamicTables` succeeds, the returned litLen lengths are valid. -/
theorem decodeDynamicTables_valid_lit (bits : List Bool)
    (litLens distLens : List Nat) (rest : List Bool)
    (h : decodeDynamicTables bits = some (litLens, distLens, rest)) :
    Huffman.Spec.ValidLengths litLens 15 :=
  (decodeDynamicTables_valid_both bits litLens distLens rest h).1

/-- If `decodeDynamicTables` succeeds, the returned distance lengths are valid. -/
theorem decodeDynamicTables_valid_dist (bits : List Bool)
    (litLens distLens : List Nat) (rest : List Bool)
    (h : decodeDynamicTables bits = some (litLens, distLens, rest)) :
    Huffman.Spec.ValidLengths distLens 15 :=
  (decodeDynamicTables_valid_both bits litLens distLens rest h).2

/-- `decode.go` is suffix-invariant: appending bits after a valid stream
    yields the same decoded result with the extra bits ignored.
    Requires `suffix.length % 8 = 0` for stored blocks (btype = 0). -/
theorem decode_go_suffix
    (bits suffix : List Bool) (acc : List UInt8) (result : List UInt8)
    (hsuf : suffix.length % 8 = 0)
    (h : decode.go bits acc = some result) :
    decode.go (bits ++ suffix) acc = some result := by
  suffices ∀ n (bits : List Bool) (acc : List UInt8) (result : List UInt8),
      bits.length = n → decode.go bits acc = some result →
      decode.go (bits ++ suffix) acc = some result from
    this _ bits acc result rfl h
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro bits acc result hlen hgo
  unfold decode.go at hgo ⊢
  simp only [bind, Option.bind] at hgo ⊢
  cases h1 : readBitsLSB 1 bits with
  | none => simp only [h1] at hgo; contradiction
  | some p1 =>
    obtain ⟨bfinal, bits1⟩ := p1
    simp only [h1] at hgo
    rw [readBitsLSB_append 1 bits suffix bfinal bits1 h1]
    simp only
    cases h2 : readBitsLSB 2 bits1 with
    | none => simp only [h2] at hgo; contradiction
    | some p2 =>
      obtain ⟨btype, bits2⟩ := p2
      simp only [h2] at hgo
      rw [readBitsLSB_append 2 bits1 suffix btype bits2 h2]
      simp only
      match btype, hgo with
      | 0, hgo =>
        -- Stored block
        cases hs : decodeStored bits2 with
        | none => simp only [hs] at hgo; contradiction
        | some ps =>
          obtain ⟨bytes, bits3⟩ := ps
          simp only [hs] at hgo
          rw [decodeStored_append bits2 suffix bytes bits3 hsuf hs]
          simp only
          by_cases hf : bfinal == 1
          · simp only [hf, ↓reduceIte, Option.pure_def, Option.some.injEq] at hgo ⊢; exact hgo
          · simp only [hf, Bool.false_eq_true, ↓reduceIte, dite_eq_ite,
              Option.ite_none_right_eq_some, List.length_append,
              Nat.add_lt_add_iff_right] at hgo ⊢
            by_cases hblen : bits3.length < bits.length
            · simp only [hblen, true_and] at hgo
              exact ⟨hblen, ih bits3.length (hlen ▸ hblen) bits3 (acc ++ bytes) result rfl hgo⟩
            · simp only [hblen, false_and] at hgo
      | 1, hgo =>
        -- Fixed Huffman
        cases hd : decodeSymbols fixedLitLengths fixedDistLengths bits2 with
        | none => simp only [hd] at hgo; contradiction
        | some pd =>
          obtain ⟨syms, bits3⟩ := pd
          simp only [hd] at hgo
          rw [decodeSymbols_append fixedLitLengths fixedDistLengths bits2 suffix
              syms bits3 fixedLitLengths_valid fixedDistLengths_valid hd]
          simp only
          cases hr : resolveLZ77 syms acc with
          | none => simp only [hr] at hgo; contradiction
          | some acc' =>
            simp only [hr] at hgo ⊢
            by_cases hf : bfinal == 1
            · simp only [hf, ↓reduceIte, Option.pure_def, Option.some.injEq] at hgo ⊢; exact hgo
            · simp only [hf, Bool.false_eq_true, ↓reduceIte, dite_eq_ite,
                Option.ite_none_right_eq_some, List.length_append,
                Nat.add_lt_add_iff_right] at hgo ⊢
              by_cases hblen : bits3.length < bits.length
              · simp only [hblen, true_and] at hgo
                exact ⟨hblen, ih bits3.length (hlen ▸ hblen) bits3 acc' result rfl hgo⟩
              · simp only [hblen, false_and] at hgo
      | 2, hgo =>
        -- Dynamic Huffman
        cases hdt : decodeDynamicTables bits2 with
        | none => simp only [hdt] at hgo; contradiction
        | some pdt =>
          obtain ⟨litLens, distLens, bits3⟩ := pdt
          simp only [hdt] at hgo
          rw [decodeDynamicTables_append bits2 suffix litLens distLens bits3 hdt]
          simp only
          have hvl := decodeDynamicTables_valid_lit bits2 litLens distLens bits3 hdt
          have hvd := decodeDynamicTables_valid_dist bits2 litLens distLens bits3 hdt
          cases hds : decodeSymbols litLens distLens bits3 with
          | none => simp only [hds] at hgo; contradiction
          | some pds =>
            obtain ⟨syms, bits4⟩ := pds
            simp only [hds] at hgo
            rw [decodeSymbols_append litLens distLens bits3 suffix syms bits4 hvl hvd hds]
            simp only
            cases hr : resolveLZ77 syms acc with
            | none => simp only [hr] at hgo; contradiction
            | some acc' =>
              simp only [hr] at hgo ⊢
              by_cases hf : bfinal == 1
              · simp only [hf, ↓reduceIte, Option.pure_def, Option.some.injEq] at hgo ⊢; exact hgo
              · simp only [hf, Bool.false_eq_true, ↓reduceIte, dite_eq_ite,
                  Option.ite_none_right_eq_some, List.length_append,
                  Nat.add_lt_add_iff_right] at hgo ⊢
                by_cases hblen : bits4.length < bits.length
                · simp only [hblen, true_and] at hgo
                  exact ⟨hblen, ih bits4.length (hlen ▸ hblen) bits4 acc' result rfl hgo⟩
                · simp only [hblen, false_and] at hgo
      | n + 3, hgo => contradiction

/-! ## decode.go with remaining bits

`decode.goR` is a variant of `decode.go` that also returns the remaining
(unprocessed) bits after decoding. This allows tracking how many bits
the decoder consumed, which is needed for endPos exactness proofs.

Defined in `Deflate.lean` alongside `decode.go`; theorems about it live here. -/

/-- `decode.goR` agrees with `decode.go` on the result: if `decode.goR` returns
    `(result, rest)`, then `decode.go` returns `result`. -/
theorem decode_goR_fst (bits : List Bool) (acc : List UInt8)
    (result : List UInt8) (rest : List Bool)
    (h : decode.goR bits acc = some (result, rest)) :
    decode.go bits acc = some result := by
  suffices ∀ n (bits : List Bool) (acc : List UInt8)
      (result : List UInt8) (rest : List Bool),
      bits.length = n → decode.goR bits acc = some (result, rest) →
      decode.go bits acc = some result from
    this _ bits acc result rest rfl h
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro bits acc result rest hlen hgoR
  unfold decode.goR at hgoR
  unfold decode.go
  simp only [bind, Option.bind] at hgoR ⊢
  cases h1 : readBitsLSB 1 bits with
  | none => simp only [h1] at hgoR; contradiction
  | some p1 =>
    obtain ⟨bfinal, bits1⟩ := p1
    simp only [h1] at hgoR ⊢
    cases h2 : readBitsLSB 2 bits1 with
    | none => simp only [h2] at hgoR; contradiction
    | some p2 =>
      obtain ⟨btype, bits2⟩ := p2
      simp only [h2] at hgoR ⊢
      match btype, hgoR with
      | 0, hgoR =>
        cases hs : decodeStored bits2 with
        | none => simp only [hs] at hgoR; contradiction
        | some ps =>
          obtain ⟨bytes, bits3⟩ := ps
          simp only [hs] at hgoR ⊢
          by_cases hf : bfinal == 1
          · simp only [hf, ↓reduceIte, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hgoR ⊢
            exact hgoR.1
          · simp only [hf, Bool.false_eq_true, ↓reduceIte, dite_eq_ite,
                Option.ite_none_right_eq_some] at hgoR ⊢
            by_cases hblen : bits3.length < bits.length
            · simp only [hblen, true_and] at hgoR ⊢
              exact ih bits3.length (hlen ▸ hblen) bits3 (acc ++ bytes) result rest rfl hgoR
            · simp only [hblen, false_and] at hgoR
      | 1, hgoR =>
        cases hd : decodeSymbols fixedLitLengths fixedDistLengths bits2 with
        | none => simp only [hd] at hgoR; contradiction
        | some pd =>
          obtain ⟨syms, bits3⟩ := pd
          simp only [hd] at hgoR ⊢
          cases hr : resolveLZ77 syms acc with
          | none => simp only [hr] at hgoR; contradiction
          | some acc' =>
            simp only [hr] at hgoR ⊢
            by_cases hf : bfinal == 1
            · simp only [hf, ↓reduceIte, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hgoR ⊢
              exact hgoR.1
            · simp only [hf, Bool.false_eq_true, ↓reduceIte, dite_eq_ite,
                  Option.ite_none_right_eq_some] at hgoR ⊢
              by_cases hblen : bits3.length < bits.length
              · simp only [hblen, true_and] at hgoR ⊢
                exact ih bits3.length (hlen ▸ hblen) bits3 acc' result rest rfl hgoR
              · simp only [hblen, false_and] at hgoR
      | 2, hgoR =>
        cases hdt : decodeDynamicTables bits2 with
        | none => simp only [hdt] at hgoR; contradiction
        | some pdt =>
          obtain ⟨litLens, distLens, bits3⟩ := pdt
          simp only [hdt] at hgoR ⊢
          cases hds : decodeSymbols litLens distLens bits3 with
          | none => simp only [hds] at hgoR; contradiction
          | some pds =>
            obtain ⟨syms, bits4⟩ := pds
            simp only [hds] at hgoR ⊢
            cases hr : resolveLZ77 syms acc with
            | none => simp only [hr] at hgoR; contradiction
            | some acc' =>
              simp only [hr] at hgoR ⊢
              by_cases hf : bfinal == 1
              · simp only [hf, ↓reduceIte, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hgoR ⊢
                exact hgoR.1
              · simp only [hf, Bool.false_eq_true, ↓reduceIte, dite_eq_ite,
                    Option.ite_none_right_eq_some] at hgoR ⊢
                by_cases hblen : bits4.length < bits.length
                · simp only [hblen, true_and] at hgoR ⊢
                  exact ih bits4.length (hlen ▸ hblen) bits4 acc' result rest rfl hgoR
                · simp only [hblen, false_and] at hgoR
      | n + 3, hgoR => contradiction

/-- If `decode.go` succeeds, `decode.goR` also succeeds with some remaining bits. -/
theorem decode_goR_exists (bits : List Bool) (acc : List UInt8)
    (result : List UInt8) (h : decode.go bits acc = some result) :
    ∃ rest, decode.goR bits acc = some (result, rest) := by
  suffices ∀ n (bits : List Bool) (acc : List UInt8)
      (result : List UInt8),
      bits.length = n → decode.go bits acc = some result →
      ∃ rest, decode.goR bits acc = some (result, rest) from
    this _ bits acc result rfl h
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro bits acc result hlen hgo
  unfold decode.go at hgo
  unfold decode.goR
  simp only [bind, Option.bind] at hgo ⊢
  cases h1 : readBitsLSB 1 bits with
  | none => simp only [h1] at hgo; contradiction
  | some p1 =>
    obtain ⟨bfinal, bits1⟩ := p1
    simp only [h1] at hgo ⊢
    cases h2 : readBitsLSB 2 bits1 with
    | none => simp only [h2] at hgo; contradiction
    | some p2 =>
      obtain ⟨btype, bits2⟩ := p2
      simp only [h2] at hgo ⊢
      match btype, hgo with
      | 0, hgo =>
        cases hs : decodeStored bits2 with
        | none => simp only [hs] at hgo; contradiction
        | some ps =>
          obtain ⟨bytes, bits3⟩ := ps
          simp only [hs] at hgo ⊢
          by_cases hf : bfinal == 1
          · simp only [hf, ↓reduceIte, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hgo ⊢
            exact ⟨bits3, hgo, rfl⟩
          · simp only [hf, Bool.false_eq_true, ↓reduceIte, dite_eq_ite,
                Option.ite_none_right_eq_some] at hgo ⊢
            by_cases hblen : bits3.length < bits.length
            · simp only [hblen, true_and] at hgo ⊢
              exact ih bits3.length (hlen ▸ hblen) bits3 (acc ++ bytes) result rfl hgo
            · simp only [hblen, false_and] at hgo
      | 1, hgo =>
        cases hd : decodeSymbols fixedLitLengths fixedDistLengths bits2 with
        | none => simp only [hd] at hgo; contradiction
        | some pd =>
          obtain ⟨syms, bits3⟩ := pd
          simp only [hd] at hgo ⊢
          cases hr : resolveLZ77 syms acc with
          | none => simp only [hr] at hgo; contradiction
          | some acc' =>
            simp only [hr] at hgo ⊢
            by_cases hf : bfinal == 1
            · simp only [hf, ↓reduceIte, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hgo ⊢
              exact ⟨bits3, hgo, rfl⟩
            · simp only [hf, Bool.false_eq_true, ↓reduceIte, dite_eq_ite,
                  Option.ite_none_right_eq_some] at hgo ⊢
              by_cases hblen : bits3.length < bits.length
              · simp only [hblen, true_and] at hgo ⊢
                exact ih bits3.length (hlen ▸ hblen) bits3 acc' result rfl hgo
              · simp only [hblen, false_and] at hgo
      | 2, hgo =>
        cases hdt : decodeDynamicTables bits2 with
        | none => simp only [hdt] at hgo; contradiction
        | some pdt =>
          obtain ⟨litLens, distLens, bits3⟩ := pdt
          simp only [hdt] at hgo ⊢
          cases hds : decodeSymbols litLens distLens bits3 with
          | none => simp only [hds] at hgo; contradiction
          | some pds =>
            obtain ⟨syms, bits4⟩ := pds
            simp only [hds] at hgo ⊢
            cases hr : resolveLZ77 syms acc with
            | none => simp only [hr] at hgo; contradiction
            | some acc' =>
              simp only [hr] at hgo ⊢
              by_cases hf : bfinal == 1
              · simp only [hf, ↓reduceIte, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hgo ⊢
                exact ⟨bits4, hgo, rfl⟩
              · simp only [hf, Bool.false_eq_true, ↓reduceIte, dite_eq_ite,
                    Option.ite_none_right_eq_some] at hgo ⊢
                by_cases hblen : bits4.length < bits.length
                · simp only [hblen, true_and] at hgo ⊢
                  exact ih bits4.length (hlen ▸ hblen) bits4 acc' result rfl hgo
                · simp only [hblen, false_and] at hgo
      | n + 3, hgo => contradiction

end Deflate.Spec
