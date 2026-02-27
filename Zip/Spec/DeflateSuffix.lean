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
  | zero => simp_all [readBitsLSB]
  | succ k ih =>
    cases bits with
    | nil => simp [readBitsLSB] at h
    | cons b bs =>
      simp only [readBitsLSB, List.cons_append] at h ⊢
      cases hk : readBitsLSB k bs with
      | none => simp [hk] at h
      | some p =>
        obtain ⟨v, rem⟩ := p
        simp [hk] at h; obtain ⟨rfl, rfl⟩ := h
        simp [ih bs v rem hk]

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
    have hnd := Huffman.Spec.allCodes_nodup lengths maxBits
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
  | none => simp [hld] at h
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
        | none => simp [hlb] at h
        | some base =>
          simp only [hlb] at h ⊢
          cases hle : lengthExtra[litSym - 257]? with
          | none => simp [hle] at h
          | some extra =>
            simp only [hle] at h ⊢
            cases hrb : readBitsLSB extra bits₁ with
            | none => simp [hrb] at h
            | some q =>
              obtain ⟨extraVal, bits₂⟩ := q
              simp only [hrb] at h ⊢
              rw [readBitsLSB_append extra bits₁ suffix extraVal bits₂ hrb]
              cases hdd : Huffman.Spec.decode ((Huffman.Spec.allCodes distLengths).map fun (s, cw) => (cw, s)) bits₂ with
              | none => simp [hdd] at h
              | some r =>
                obtain ⟨dSym, bits₃⟩ := r
                simp only [hdd] at h ⊢
                rw [Huffman.Spec.decode_suffix _ bits₂ suffix dSym bits₃ hdd
                    (allCodes_swapped_prefix_free distLengths 15 hvd)]
                cases hdb : distBase[dSym]? with
                | none => simp [hdb] at h
                | some dBase =>
                  simp only [hdb] at h ⊢
                  cases hde : distExtra[dSym]? with
                  | none => simp [hde] at h
                  | some dExtra =>
                    simp only [hde] at h ⊢
                    cases hrbd : readBitsLSB dExtra bits₃ with
                    | none => simp [hrbd] at h
                    | some s =>
                      obtain ⟨dExtraVal, bits₄⟩ := s
                      simp only [hrbd] at h ⊢
                      rw [readBitsLSB_append dExtra bits₃ suffix dExtraVal bits₄ hrbd]
                      obtain ⟨rfl, rfl⟩ := Option.some.inj h; rfl

/-- `decodeSymbols` is suffix-invariant. -/
theorem decodeSymbols_append (litLengths distLengths : List Nat)
    (bits suffix : List Bool) (fuel : Nat)
    (syms : List LZ77Symbol) (rest : List Bool)
    (hvl : Huffman.Spec.ValidLengths litLengths 15)
    (hvd : Huffman.Spec.ValidLengths distLengths 15)
    (h : decodeSymbols litLengths distLengths bits fuel = some (syms, rest)) :
    decodeSymbols litLengths distLengths (bits ++ suffix) fuel =
      some (syms, rest ++ suffix) := by
  induction fuel generalizing bits syms rest with
  | zero => simp [decodeSymbols] at h
  | succ n ih =>
    unfold decodeSymbols at h ⊢
    cases hlit : decodeLitLen litLengths distLengths bits with
    | none => simp [hlit] at h
    | some p =>
      obtain ⟨sym, bits'⟩ := p
      rw [hlit] at h; dsimp only [bind, Option.bind] at h ⊢
      rw [decodeLitLen_append litLengths distLengths bits suffix sym bits' hvl hvd hlit]
      dsimp only [bind, Option.bind]
      match hsym : sym with
      | .endOfBlock =>
        obtain ⟨rfl, rfl⟩ := Option.some.inj h; rfl
      | .literal _ | .reference .. =>
        cases hrec : decodeSymbols litLengths distLengths bits' n with
        | none => simp [hrec] at h
        | some q =>
          obtain ⟨restSyms, bits''⟩ := q
          rw [hrec] at h; dsimp only [bind, Option.bind] at h
          simp only [ih bits' restSyms bits'' hrec]
          obtain ⟨rfl, rfl⟩ := Option.some.inj h; rfl

/-- `readNBytes` is suffix-invariant. -/
private theorem readNBytes_append (n : Nat) (bits suffix : List Bool)
    (acc bytes : List UInt8) (rest : List Bool)
    (h : decodeStored.readNBytes n bits acc = some (bytes, rest)) :
    decodeStored.readNBytes n (bits ++ suffix) acc = some (bytes, rest ++ suffix) := by
  induction n generalizing bits acc bytes rest with
  | zero => simp_all [decodeStored.readNBytes]
  | succ k ih =>
    unfold decodeStored.readNBytes at h ⊢
    cases hrb : readBitsLSB 8 bits with
    | none => simp [hrb] at h
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
  | none => simp [hrl] at h
  | some p =>
    obtain ⟨len, bits₁⟩ := p
    rw [hrl] at h; dsimp only [bind, Option.bind] at h ⊢
    rw [readBitsLSB_append 16 (alignToByte bits) suffix len bits₁ hrl]
    dsimp only [bind, Option.bind]
    -- Thread readBitsLSB 16 for NLEN
    cases hrn : readBitsLSB 16 bits₁ with
    | none => simp [hrn] at h
    | some q =>
      obtain ⟨nlen, bits₂⟩ := q
      rw [hrn] at h; dsimp only [bind, Option.bind] at h ⊢
      rw [readBitsLSB_append 16 bits₁ suffix nlen bits₂ hrn]
      dsimp only [bind, Option.bind]
      -- Guard passes identically
      by_cases hg : (len ^^^ nlen == 0xFFFF) = true
      · simp only [guard, hg, ↓reduceIte] at h ⊢
        exact readNBytes_append len bits₂ suffix [] bytes rest h
      · simp only [guard, hg] at h; simp at h

/-- `readCLLengths` is suffix-invariant. -/
private theorem readCLLengths_append (n idx : Nat) (acc : List Nat)
    (bits suffix : List Bool)
    (result : List Nat) (rest : List Bool)
    (h : Deflate.Spec.readCLLengths n idx acc bits = some (result, rest)) :
    Deflate.Spec.readCLLengths n idx acc (bits ++ suffix) = some (result, rest ++ suffix) := by
  induction n generalizing idx acc bits result rest with
  | zero => simp_all [Deflate.Spec.readCLLengths]
  | succ k ih =>
    unfold Deflate.Spec.readCLLengths at h ⊢
    cases hrb : readBitsLSB 3 bits with
    | none => simp [hrb] at h
    | some p =>
      obtain ⟨v, bits'⟩ := p
      rw [hrb] at h; dsimp only [bind, Option.bind] at h ⊢
      rw [readBitsLSB_append 3 bits suffix v bits' hrb]
      exact ih (idx + 1) (acc.set (codeLengthOrder[idx]!) v) bits' result rest h

/-- `decodeCLSymbols` is suffix-invariant. -/
private theorem decodeCLSymbols_append
    (clTable : List (Huffman.Spec.Codeword × Nat))
    (totalCodes : Nat) (acc : List Nat) (bits suffix : List Bool)
    (fuel : Nat) (result : List Nat) (rest : List Bool)
    (hpf : ∀ cw₁ s₁ cw₂ s₂, (cw₁, s₁) ∈ clTable → (cw₂, s₂) ∈ clTable →
      (cw₁, s₁) ≠ (cw₂, s₂) → ¬cw₁.IsPrefix cw₂)
    (h : decodeDynamicTables.decodeCLSymbols clTable totalCodes acc bits fuel =
      some (result, rest)) :
    decodeDynamicTables.decodeCLSymbols clTable totalCodes acc (bits ++ suffix) fuel =
      some (result, rest ++ suffix) := by
  induction fuel generalizing acc bits result rest with
  | zero => simp [decodeDynamicTables.decodeCLSymbols] at h
  | succ n ih =>
    unfold decodeDynamicTables.decodeCLSymbols at h ⊢
    by_cases hge : acc.length ≥ totalCodes
    · rw [if_pos hge] at h ⊢
      obtain ⟨rfl, rfl⟩ := Option.some.inj h; rfl
    · rw [if_neg hge] at h ⊢
      cases hdec : Huffman.Spec.decode clTable bits with
      | none => simp [hdec] at h
      | some p =>
        obtain ⟨sym, bits'⟩ := p
        rw [hdec] at h; dsimp only [bind, Option.bind] at h ⊢
        rw [Huffman.Spec.decode_suffix clTable bits suffix sym bits' hdec hpf]
        dsimp only [bind, Option.bind]
        by_cases hsym16 : sym < 16
        · rw [if_pos hsym16] at h ⊢
          exact ih (acc ++ [sym]) bits' result rest h
        · rw [if_neg hsym16] at h ⊢
          by_cases hsym16eq : (sym == 16) = true
          · rw [if_pos hsym16eq] at h ⊢
            by_cases hg : (0 : Nat) < acc.length
            · simp only [guard, hg, ↓reduceIte] at h ⊢
              cases hrb : readBitsLSB 2 bits' with
              | none => simp [hrb] at h
              | some q =>
                obtain ⟨rep, bits''⟩ := q
                rw [hrb] at h; dsimp only [bind, Option.bind] at h ⊢
                rw [readBitsLSB_append 2 bits' suffix rep bits'' hrb]
                dsimp only [bind, Option.bind]
                by_cases hg2 : (acc ++ List.replicate (rep + 3) acc.getLast!).length ≤ totalCodes
                · simp only [hg2, ↓reduceIte] at h ⊢
                  exact ih _ bits'' result rest h
                · simp only [hg2, ↓reduceIte] at h; simp at h
            · simp only [guard, hg, ↓reduceIte] at h; simp at h
          · rw [if_neg hsym16eq] at h ⊢
            by_cases hsym17 : (sym == 17) = true
            · rw [if_pos hsym17] at h ⊢
              cases hrb : readBitsLSB 3 bits' with
              | none => simp [hrb] at h
              | some q =>
                obtain ⟨rep, bits''⟩ := q
                rw [hrb] at h; dsimp only [bind, Option.bind] at h ⊢
                rw [readBitsLSB_append 3 bits' suffix rep bits'' hrb]
                dsimp only [bind, Option.bind]
                by_cases hg : (acc ++ List.replicate (rep + 3) 0).length ≤ totalCodes
                · simp only [guard, hg, ↓reduceIte] at h ⊢
                  exact ih _ bits'' result rest h
                · simp only [guard, hg, ↓reduceIte] at h; simp at h
            · rw [if_neg hsym17] at h ⊢
              by_cases hsym18 : (sym == 18) = true
              · rw [if_pos hsym18] at h ⊢
                cases hrb : readBitsLSB 7 bits' with
                | none => simp [hrb] at h
                | some q =>
                  obtain ⟨rep, bits''⟩ := q
                  rw [hrb] at h; dsimp only [bind, Option.bind] at h ⊢
                  rw [readBitsLSB_append 7 bits' suffix rep bits'' hrb]
                  dsimp only [bind, Option.bind]
                  by_cases hg : (acc ++ List.replicate (rep + 11) 0).length ≤ totalCodes
                  · simp only [guard, hg, ↓reduceIte] at h ⊢
                    exact ih _ bits'' result rest h
                  · simp only [guard, hg, ↓reduceIte] at h; simp at h
              · rw [if_neg hsym18] at h ⊢
                simp at h

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
  | none => simp [h5] at h
  | some p₁ =>
    obtain ⟨hlit, bits₁⟩ := p₁
    cases h5d : readBitsLSB 5 bits₁ with
    | none => simp [h5, h5d] at h
    | some p₂ =>
      obtain ⟨hdist, bits₂⟩ := p₂
      cases h4 : readBitsLSB 4 bits₂ with
      | none => simp [h5, h5d, h4] at h
      | some p₃ =>
        obtain ⟨hclen, bits₃⟩ := p₃
        cases hcl : Deflate.Spec.readCLLengths (hclen + 4) 0
            (List.replicate 19 0) bits₃ with
        | none =>
          rw [replicate_19_zero] at hcl
          simp [h5, h5d, h4, hcl] at h
        | some p₄ =>
          obtain ⟨clLengths, bits₄⟩ := p₄
          have hcl' := replicate_19_zero ▸ hcl
          by_cases hvCL : Huffman.Spec.ValidLengths clLengths 7
          · cases hcls : decodeDynamicTables.decodeCLSymbols
                ((Huffman.Spec.allCodes clLengths 7).map fun (sym, cw) => (cw, sym))
                (hlit + 257 + (hdist + 1)) [] bits₄
                (hlit + 257 + (hdist + 1) + 1) with
            | none =>
              simp [h5, h5d, h4, hcl', hvCL, hcls, guard, pure, Pure.pure] at h
            | some p₅ =>
              obtain ⟨codeLengths, bits₅⟩ := p₅
              by_cases hlen : codeLengths.length = hlit + 257 + (hdist + 1)
              · by_cases hvLL : Huffman.Spec.ValidLengths
                    (codeLengths.take (hlit + 257)) 15
                · by_cases hvDL : Huffman.Spec.ValidLengths
                      (codeLengths.drop (hlit + 257)) 15
                  · simp [h5, h5d, h4, hcl', hvCL, hcls, hlen, hvLL, hvDL,
                          guard, pure, Pure.pure] at h
                    obtain ⟨rfl, rfl, rfl⟩ := h
                    have h5' := readBitsLSB_append 5 bits suffix hlit bits₁ h5
                    have h5d' := readBitsLSB_append 5 bits₁ suffix hdist bits₂ h5d
                    have h4' := readBitsLSB_append 4 bits₂ suffix hclen bits₃ h4
                    have hcl_a := replicate_19_zero ▸
                      readCLLengths_append _ 0 _ bits₃ suffix clLengths bits₄ hcl
                    have hcls' := decodeCLSymbols_append _ _ [] bits₄ suffix _
                        codeLengths bits₅
                        (allCodes_swapped_prefix_free clLengths 7 hvCL) hcls
                    simp [h5', h5d', h4', hcl_a, hvCL, hcls', hlen, hvLL, hvDL,
                          guard, pure, Pure.pure]
                  · simp [h5, h5d, h4, hcl', hvCL, hcls, hlen, hvLL, hvDL,
                          guard, pure, Pure.pure, failure, Alternative.failure] at h
                · simp [h5, h5d, h4, hcl', hvCL, hcls, hlen, hvLL,
                        guard, pure, Pure.pure, failure, Alternative.failure] at h
              · simp [h5, h5d, h4, hcl', hvCL, hcls, hlen,
                      guard, pure, Pure.pure, failure, Alternative.failure] at h
          · simp [h5, h5d, h4, hcl', hvCL,
                  guard, pure, Pure.pure, failure, Alternative.failure] at h

/-- If `decodeDynamicTables` succeeds, both returned length lists are valid. -/
private theorem decodeDynamicTables_valid_both (bits : List Bool)
    (litLens distLens : List Nat) (rest : List Bool)
    (h : decodeDynamicTables bits = some (litLens, distLens, rest)) :
    Huffman.Spec.ValidLengths litLens 15 ∧ Huffman.Spec.ValidLengths distLens 15 := by
  unfold decodeDynamicTables at h
  cases h5 : readBitsLSB 5 bits with
  | none => simp [h5] at h
  | some p₁ =>
    obtain ⟨hlit, bits₁⟩ := p₁
    cases h5d : readBitsLSB 5 bits₁ with
    | none => simp [h5, h5d] at h
    | some p₂ =>
      obtain ⟨hdist, bits₂⟩ := p₂
      cases h4 : readBitsLSB 4 bits₂ with
      | none => simp [h5, h5d, h4] at h
      | some p₃ =>
        obtain ⟨hclen, bits₃⟩ := p₃
        cases hcl : Deflate.Spec.readCLLengths (hclen + 4) 0
            (List.replicate 19 0) bits₃ with
        | none =>
          rw [replicate_19_zero] at hcl
          simp [h5, h5d, h4, hcl] at h
        | some p₄ =>
          obtain ⟨clLengths, bits₄⟩ := p₄
          have hcl' := replicate_19_zero ▸ hcl
          by_cases hvCL : Huffman.Spec.ValidLengths clLengths 7
          · cases hcls : decodeDynamicTables.decodeCLSymbols
                ((Huffman.Spec.allCodes clLengths 7).map fun (sym, cw) => (cw, sym))
                (hlit + 257 + (hdist + 1)) [] bits₄
                (hlit + 257 + (hdist + 1) + 1) with
            | none =>
              simp [h5, h5d, h4, hcl', hvCL, hcls, guard, pure, Pure.pure] at h
            | some p₅ =>
              obtain ⟨codeLengths, bits₅⟩ := p₅
              by_cases hlen : codeLengths.length = hlit + 257 + (hdist + 1)
              · by_cases hvLL : Huffman.Spec.ValidLengths
                    (codeLengths.take (hlit + 257)) 15
                · by_cases hvDL : Huffman.Spec.ValidLengths
                      (codeLengths.drop (hlit + 257)) 15
                  · simp [h5, h5d, h4, hcl', hvCL, hcls, hlen, hvLL, hvDL,
                          guard, pure, Pure.pure] at h
                    exact ⟨h.1 ▸ hvLL, h.2.1 ▸ hvDL⟩
                  · simp [h5, h5d, h4, hcl', hvCL, hcls, hlen, hvLL, hvDL,
                          guard, pure, Pure.pure, failure, Alternative.failure] at h
                · simp [h5, h5d, h4, hcl', hvCL, hcls, hlen, hvLL,
                        guard, pure, Pure.pure, failure, Alternative.failure] at h
              · simp [h5, h5d, h4, hcl', hvCL, hcls, hlen,
                      guard, pure, Pure.pure, failure, Alternative.failure] at h
          · simp [h5, h5d, h4, hcl', hvCL,
                  guard, pure, Pure.pure, failure, Alternative.failure] at h

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

set_option maxRecDepth 4096 in
/-- `decode.go` is suffix-invariant: appending bits after a valid stream
    yields the same decoded result with the extra bits ignored.
    Requires `suffix.length % 8 = 0` for stored blocks (btype = 0). -/
theorem decode_go_suffix
    (bits suffix : List Bool) (acc : List UInt8) (fuel : Nat) (result : List UInt8)
    (hsuf : suffix.length % 8 = 0)
    (h : decode.go bits acc fuel = some result) :
    decode.go (bits ++ suffix) acc fuel = some result := by
  induction fuel generalizing bits acc result with
  | zero => simp [decode.go] at h
  | succ n ih =>
    unfold decode.go at h ⊢
    cases hbf : readBitsLSB 1 bits with
    | none => simp [hbf] at h
    | some p =>
      obtain ⟨bfinal, bits₁⟩ := p
      rw [hbf] at h; dsimp only [bind, Option.bind] at h ⊢
      rw [readBitsLSB_append 1 bits suffix bfinal bits₁ hbf]
      dsimp only [bind, Option.bind]
      cases hbt : readBitsLSB 2 bits₁ with
      | none => simp [hbt] at h
      | some q =>
        obtain ⟨btype, bits₂⟩ := q
        rw [hbt] at h; dsimp only [bind, Option.bind] at h
        rw [readBitsLSB_append 2 bits₁ suffix btype bits₂ hbt]
        dsimp only [bind, Option.bind]
        match hm : btype with
        | 0 => -- Stored block
          cases hds : decodeStored bits₂ with
          | none => simp [hds] at h
          | some r =>
            obtain ⟨bytes, bits₃⟩ := r
            rw [hds] at h; dsimp only [bind, Option.bind] at h
            rw [decodeStored_append bits₂ suffix bytes bits₃ hsuf hds]
            dsimp only [bind, Option.bind]
            by_cases hbf1 : (bfinal == 1) = true
            · rw [if_pos hbf1] at h ⊢; exact h
            · rw [if_neg hbf1] at h ⊢; exact ih _ _ _ h
        | 1 => -- Fixed Huffman
          cases hsyms : decodeSymbols fixedLitLengths fixedDistLengths bits₂ with
          | none => simp [hsyms] at h
          | some r =>
            obtain ⟨syms, bits₃⟩ := r
            rw [hsyms] at h; dsimp only [bind, Option.bind] at h
            rw [decodeSymbols_append fixedLitLengths fixedDistLengths bits₂ suffix _
                syms bits₃ fixedLitLengths_valid fixedDistLengths_valid hsyms]
            dsimp only [bind, Option.bind]
            cases hres : resolveLZ77 syms acc with
            | none => simp [hres] at h
            | some acc' =>
              rw [hres] at h; dsimp only [bind, Option.bind] at h ⊢
              by_cases hbf1 : (bfinal == 1) = true
              · rw [if_pos hbf1] at h ⊢; exact h
              · rw [if_neg hbf1] at h ⊢; exact ih _ _ _ h
        | 2 => -- Dynamic Huffman
          cases hdt : decodeDynamicTables bits₂ with
          | none => simp [hdt] at h
          | some r =>
            obtain ⟨litLens, distLens, bits₃⟩ := r
            rw [hdt] at h; dsimp only [bind, Option.bind] at h
            rw [decodeDynamicTables_append bits₂ suffix litLens distLens bits₃ hdt]
            dsimp only [bind, Option.bind]
            cases hsyms : decodeSymbols litLens distLens bits₃ with
            | none => simp [hsyms] at h
            | some s =>
              obtain ⟨syms, bits₄⟩ := s
              rw [hsyms] at h; dsimp only [bind, Option.bind] at h
              rw [decodeSymbols_append litLens distLens bits₃ suffix _
                  syms bits₄
                  (decodeDynamicTables_valid_lit bits₂ litLens distLens bits₃ hdt)
                  (decodeDynamicTables_valid_dist bits₂ litLens distLens bits₃ hdt) hsyms]
              dsimp only [bind, Option.bind]
              cases hres : resolveLZ77 syms acc with
              | none => simp [hres] at h
              | some acc' =>
                rw [hres] at h; dsimp only [bind, Option.bind] at h ⊢
                by_cases hbf1 : (bfinal == 1) = true
                · rw [if_pos hbf1] at h ⊢; exact h
                · rw [if_neg hbf1] at h ⊢; exact ih _ _ _ h
        | _ + 3 => simp at h

/-! ## decode.go with remaining bits

`decode.goR` is a variant of `decode.go` that also returns the remaining
(unprocessed) bits after decoding. This allows tracking how many bits
the decoder consumed, which is needed for endPos exactness proofs. -/

/-- Like `decode.go` but returns both the decoded result and the remaining bits. -/
def decode.goR (bits : List Bool) (acc : List UInt8) :
    Nat → Option (List UInt8 × List Bool)
  | 0 => none
  | fuel + 1 => do
    let (bfinal, bits) ← readBitsLSB 1 bits
    let (btype, bits) ← readBitsLSB 2 bits
    match btype with
    | 0 =>
      let (bytes, bits) ← decodeStored bits
      let acc := acc ++ bytes
      if bfinal == 1 then return (acc, bits) else decode.goR bits acc fuel
    | 1 =>
      let (syms, bits) ← decodeSymbols fixedLitLengths fixedDistLengths bits
      let acc ← resolveLZ77 syms acc
      if bfinal == 1 then return (acc, bits) else decode.goR bits acc fuel
    | 2 =>
      let (litLens, distLens, bits) ← decodeDynamicTables bits
      let (syms, bits) ← decodeSymbols litLens distLens bits
      let acc ← resolveLZ77 syms acc
      if bfinal == 1 then return (acc, bits) else decode.goR bits acc fuel
    | _ => none

set_option maxRecDepth 2048 in
/-- `decode.goR` agrees with `decode.go` on the result: if `decode.goR` returns
    `(result, rest)`, then `decode.go` returns `result`. -/
theorem decode_goR_fst (bits : List Bool) (acc : List UInt8) (fuel : Nat)
    (result : List UInt8) (rest : List Bool)
    (h : decode.goR bits acc fuel = some (result, rest)) :
    decode.go bits acc fuel = some result := by
  induction fuel generalizing bits acc result rest with
  | zero => simp [decode.goR] at h
  | succ n ih =>
    unfold decode.goR at h; unfold decode.go
    cases hbf : readBitsLSB 1 bits with
    | none => simp [hbf] at h
    | some p =>
      obtain ⟨bfinal, bits₁⟩ := p
      rw [hbf] at h; dsimp only [bind, Option.bind] at h ⊢
      cases hbt : readBitsLSB 2 bits₁ with
      | none => simp [hbt] at h
      | some q =>
        obtain ⟨btype, bits₂⟩ := q
        rw [hbt] at h; dsimp only [bind, Option.bind] at h ⊢
        match hm : btype with
        | 0 =>
          cases hds : decodeStored bits₂ with
          | none => simp [hds] at h
          | some r =>
            obtain ⟨bytes, bits₃⟩ := r
            rw [hds] at h; dsimp only [bind, Option.bind] at h ⊢
            by_cases hbf1 : (bfinal == 1) = true
            · rw [if_pos hbf1] at h ⊢
              simp [pure, Pure.pure] at h ⊢; exact h.1
            · rw [if_neg hbf1] at h ⊢; exact ih _ _ _ _ h
        | 1 =>
          cases hsyms : decodeSymbols fixedLitLengths fixedDistLengths bits₂ with
          | none => simp [hsyms] at h
          | some r =>
            obtain ⟨syms, bits₃⟩ := r
            rw [hsyms] at h; dsimp only [bind, Option.bind] at h ⊢
            cases hres : resolveLZ77 syms acc with
            | none => simp [hres] at h
            | some acc' =>
              rw [hres] at h; dsimp only [bind, Option.bind] at h ⊢
              by_cases hbf1 : (bfinal == 1) = true
              · rw [if_pos hbf1] at h ⊢
                simp [pure, Pure.pure] at h ⊢; exact h.1
              · rw [if_neg hbf1] at h ⊢; exact ih _ _ _ _ h
        | 2 =>
          cases hdt : decodeDynamicTables bits₂ with
          | none => simp [hdt] at h
          | some r =>
            obtain ⟨litLens, distLens, bits₃⟩ := r
            rw [hdt] at h; dsimp only [bind, Option.bind] at h ⊢
            cases hsyms : decodeSymbols litLens distLens bits₃ with
            | none => simp [hsyms] at h
            | some s =>
              obtain ⟨syms, bits₄⟩ := s
              rw [hsyms] at h; dsimp only [bind, Option.bind] at h ⊢
              cases hres : resolveLZ77 syms acc with
              | none => simp [hres] at h
              | some acc' =>
                rw [hres] at h; dsimp only [bind, Option.bind] at h ⊢
                by_cases hbf1 : (bfinal == 1) = true
                · rw [if_pos hbf1] at h ⊢
                  simp [pure, Pure.pure] at h ⊢; exact h.1
                · rw [if_neg hbf1] at h ⊢; exact ih _ _ _ _ h
        | _ + 3 => simp at h

set_option maxRecDepth 2048 in
/-- If `decode.go` succeeds, `decode.goR` also succeeds with some remaining bits. -/
theorem decode_goR_exists (bits : List Bool) (acc : List UInt8) (fuel : Nat)
    (result : List UInt8) (h : decode.go bits acc fuel = some result) :
    ∃ rest, decode.goR bits acc fuel = some (result, rest) := by
  induction fuel generalizing bits acc result with
  | zero => simp [decode.go] at h
  | succ n ih =>
    unfold decode.go at h; unfold decode.goR
    cases hbf : readBitsLSB 1 bits with
    | none => simp [hbf] at h
    | some p =>
      obtain ⟨bfinal, bits₁⟩ := p
      rw [hbf] at h; dsimp only [bind, Option.bind] at h ⊢
      cases hbt : readBitsLSB 2 bits₁ with
      | none => simp [hbt] at h
      | some q =>
        obtain ⟨btype, bits₂⟩ := q
        rw [hbt] at h; dsimp only [bind, Option.bind] at h ⊢
        match hm : btype with
        | 0 =>
          cases hds : decodeStored bits₂ with
          | none => simp [hds] at h
          | some r =>
            obtain ⟨bytes, bits₃⟩ := r
            rw [hds] at h; dsimp only [bind, Option.bind] at h ⊢
            by_cases hbf1 : (bfinal == 1) = true
            · rw [if_pos hbf1] at h ⊢
              have heq := (Option.some.inj h.symm).symm; subst heq
              exact ⟨bits₃, rfl⟩
            · rw [if_neg hbf1] at h ⊢; exact ih _ _ _ h
        | 1 =>
          cases hsyms : decodeSymbols fixedLitLengths fixedDistLengths bits₂ with
          | none => simp [hsyms] at h
          | some r =>
            obtain ⟨syms, bits₃⟩ := r
            rw [hsyms] at h; dsimp only [bind, Option.bind] at h ⊢
            cases hres : resolveLZ77 syms acc with
            | none => simp [hres] at h
            | some acc' =>
              rw [hres] at h; dsimp only [bind, Option.bind] at h ⊢
              by_cases hbf1 : (bfinal == 1) = true
              · rw [if_pos hbf1] at h ⊢
                have heq := (Option.some.inj h.symm).symm; subst heq
                exact ⟨bits₃, rfl⟩
              · rw [if_neg hbf1] at h ⊢; exact ih _ _ _ h
        | 2 =>
          cases hdt : decodeDynamicTables bits₂ with
          | none => simp [hdt] at h
          | some r =>
            obtain ⟨litLens, distLens, bits₃⟩ := r
            rw [hdt] at h; dsimp only [bind, Option.bind] at h ⊢
            cases hsyms : decodeSymbols litLens distLens bits₃ with
            | none => simp [hsyms] at h
            | some s =>
              obtain ⟨syms, bits₄⟩ := s
              rw [hsyms] at h; dsimp only [bind, Option.bind] at h ⊢
              cases hres : resolveLZ77 syms acc with
              | none => simp [hres] at h
              | some acc' =>
                rw [hres] at h; dsimp only [bind, Option.bind] at h ⊢
                by_cases hbf1 : (bfinal == 1) = true
                · rw [if_pos hbf1] at h ⊢
                  have heq := (Option.some.inj h.symm).symm; subst heq
                  exact ⟨bits₄, rfl⟩
                · rw [if_neg hbf1] at h ⊢; exact ih _ _ _ h
        | _ + 3 => simp at h

end Deflate.Spec
