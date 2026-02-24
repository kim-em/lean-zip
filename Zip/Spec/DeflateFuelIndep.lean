import Zip.Spec.Deflate

/-!
# DEFLATE Fuel Independence and Accumulator Prefix Theorems

These theorems establish that the fuel-based spec decoders are
fuel-independent (extra fuel doesn't change the result) and that
`decode.go` always extends its accumulator.

Split from `Deflate.lean` for file size management.
-/

namespace Deflate.Spec

/-! ## Fuel independence -/

/-- `decodeSymbols` is fuel-independent: if it succeeds with some fuel,
    it returns the same result with any additional fuel. -/
theorem decodeSymbols_fuel_independent
    (litLengths distLengths : List Nat) (bits : List Bool)
    (fuel : Nat) (result : List LZ77Symbol × List Bool) :
    decodeSymbols litLengths distLengths bits fuel = some result →
    ∀ k, decodeSymbols litLengths distLengths bits (fuel + k) = some result := by
  intro h k
  induction fuel generalizing bits result with
  | zero => simp [decodeSymbols] at h
  | succ n ih =>
    -- Rewrite fuel arithmetic: (n + 1) + k = (n + k) + 1
    conv => lhs; rw [show n + 1 + k = (n + k) + 1 from by omega]
    unfold decodeSymbols at h ⊢
    cases hlit : decodeLitLen litLengths distLengths bits with
    | none => simp [hlit] at h
    | some p =>
      obtain ⟨sym, bits'⟩ := p
      simp only [hlit, bind, Option.bind] at h ⊢
      match sym with
      | .endOfBlock => exact h
      | .literal _ | .reference .. =>
        cases hrec : decodeSymbols litLengths distLengths bits' n with
        | none => simp [hrec] at h
        | some q =>
          obtain ⟨rest, bits''⟩ := q
          simp only [hrec] at h
          simp only [ih bits' (rest, bits'') hrec]
          exact h

/-- `decodeCLSymbols` is fuel-independent: if it succeeds with some fuel,
    it returns the same result with any additional fuel. -/
theorem decodeCLSymbols_fuel_independent
    (clTable : List (Huffman.Spec.Codeword × Nat))
    (totalCodes : Nat) (acc : List Nat) (bits : List Bool)
    (fuel : Nat) (result : List Nat × List Bool) :
    decodeDynamicTables.decodeCLSymbols clTable totalCodes acc bits fuel = some result →
    ∀ k, decodeDynamicTables.decodeCLSymbols clTable totalCodes acc bits (fuel + k) = some result := by
  intro h k
  induction fuel generalizing acc bits result with
  | zero => simp [decodeDynamicTables.decodeCLSymbols] at h
  | succ n ih =>
    conv => lhs; rw [show n + 1 + k = (n + k) + 1 from by omega]
    unfold decodeDynamicTables.decodeCLSymbols at h ⊢
    split
    · next hge =>
      -- h : if hge then some (acc, bits) else ... = some result
      rw [if_pos hge] at h
      exact h
    · next hlt =>
      rw [if_neg hlt] at h
      cases hdec : Huffman.Spec.decode clTable bits with
      | none => simp [hdec] at h
      | some p =>
        obtain ⟨sym, bits'⟩ := p
        simp only [hdec, bind, Option.bind] at h ⊢
        split
        · next hsym =>
          rw [if_pos hsym] at h
          exact ih _ _ _ h
        · next hsym =>
          rw [if_neg hsym] at h
          split
          · next hsym16 =>
            rw [if_pos hsym16] at h
            -- guard (acc.length > 0), readBitsLSB 2, guard (acc'.length ≤ totalCodes), rec
            by_cases hg : (0 : Nat) < acc.length
            · simp only [guard, hg, ↓reduceIte] at h ⊢
              cases hrb : readBitsLSB 2 bits' with
              | none => simp [hrb] at h
              | some q =>
                obtain ⟨rep, bits''⟩ := q
                simp only [hrb] at h ⊢
                by_cases hg2 : (acc ++ List.replicate (rep + 3) acc.getLast!).length ≤ totalCodes
                · simp only [hg2, ↓reduceIte] at h ⊢
                  exact ih _ _ _ h
                · simp only [hg2, ↓reduceIte] at h; simp at h
            · simp only [guard, hg, ↓reduceIte] at h; simp at h
          · next hsym16 =>
            rw [if_neg hsym16] at h
            split
            · next hsym17 =>
              rw [if_pos hsym17] at h
              -- readBitsLSB 3, guard (acc'.length ≤ totalCodes), rec
              cases hrb : readBitsLSB 3 bits' with
              | none => simp [hrb] at h
              | some q =>
                obtain ⟨rep, bits''⟩ := q
                simp only [hrb] at h ⊢
                by_cases hg : (acc ++ List.replicate (rep + 3) 0).length ≤ totalCodes
                · simp only [guard, hg, ↓reduceIte] at h ⊢
                  exact ih _ _ _ h
                · simp only [guard, hg, ↓reduceIte] at h; simp at h
            · next hsym17 =>
              rw [if_neg hsym17] at h
              split
              · next hsym18 =>
                rw [if_pos hsym18] at h
                -- readBitsLSB 7, guard (acc'.length ≤ totalCodes), rec
                cases hrb : readBitsLSB 7 bits' with
                | none => simp [hrb] at h
                | some q =>
                  obtain ⟨rep, bits''⟩ := q
                  simp only [hrb] at h ⊢
                  by_cases hg : (acc ++ List.replicate (rep + 11) 0).length ≤ totalCodes
                  · simp only [guard, hg, ↓reduceIte] at h ⊢
                    exact ih _ _ _ h
                  · simp only [guard, hg, ↓reduceIte] at h; simp at h
              · next hsym18 =>
                rw [if_neg hsym18] at h
                simp at h

set_option maxRecDepth 4096 in
/-- `decode` is fuel-independent: if it succeeds with some fuel,
    it returns the same result with any additional fuel. -/
private theorem decode_go_fuel_independent
    (bits : List Bool) (acc : List UInt8) (fuel : Nat) (result : List UInt8) :
    decode.go bits acc fuel = some result →
    ∀ k, decode.go bits acc (fuel + k) = some result := by
  intro h k
  induction fuel generalizing bits acc result with
  | zero => simp [decode.go] at h
  | succ n ih =>
    conv => lhs; rw [show n + 1 + k = (n + k) + 1 from by omega]
    unfold decode.go at h ⊢
    cases hbf : readBitsLSB 1 bits with
    | none => simp [hbf] at h
    | some p =>
      obtain ⟨bfinal, bits₁⟩ := p
      simp only [hbf, bind, Option.bind] at h ⊢
      cases hbt : readBitsLSB 2 bits₁ with
      | none => simp [hbt] at h
      | some q =>
        obtain ⟨btype, bits₂⟩ := q
        simp only [hbt] at h ⊢
        match hm : btype with
        | 0 =>
          cases hds : decodeStored bits₂ with
          | none => simp [hds] at h
          | some r =>
            obtain ⟨bytes, bits₃⟩ := r
            simp only [hds] at h ⊢
            split
            · next hbf1 => rw [if_pos hbf1] at h; exact h
            · next hbf1 => rw [if_neg hbf1] at h; exact ih _ _ _ h
        | 1 =>
          cases hsyms : decodeSymbols fixedLitLengths fixedDistLengths bits₂ with
          | none => simp [hsyms] at h
          | some r =>
            obtain ⟨syms, bits₃⟩ := r
            simp only [hsyms] at h ⊢
            cases hres : resolveLZ77 syms acc with
            | none => simp [hres] at h
            | some acc' =>
              simp only [hres] at h ⊢
              split
              · next hbf1 => rw [if_pos hbf1] at h; exact h
              · next hbf1 => rw [if_neg hbf1] at h; exact ih _ _ _ h
        | 2 =>
          cases hdt : decodeDynamicTables bits₂ with
          | none => simp [hdt] at h
          | some r =>
            obtain ⟨litLens, distLens, bits₃⟩ := r
            simp only [hdt] at h ⊢
            cases hsyms : decodeSymbols litLens distLens bits₃ with
            | none => simp [hsyms] at h
            | some s =>
              obtain ⟨syms, bits₄⟩ := s
              simp only [hsyms] at h ⊢
              cases hres : resolveLZ77 syms acc with
              | none => simp [hres] at h
              | some acc' =>
                simp only [hres] at h ⊢
                split
                · next hbf1 => rw [if_pos hbf1] at h; exact h
                · next hbf1 => rw [if_neg hbf1] at h; exact ih _ _ _ h
        | _ + 3 => simp at h

set_option maxRecDepth 4096 in
/-- `decode.go` always extends the accumulator: if it succeeds, the
    result is an extension of the initial accumulator. -/
theorem decode_go_acc_prefix
    (bits : List Bool) (acc : List UInt8) (fuel : Nat) (result : List UInt8)
    (h : decode.go bits acc fuel = some result) :
    acc <+: result := by
  induction fuel generalizing bits acc result with
  | zero => simp [decode.go] at h
  | succ n ih =>
    unfold decode.go at h
    cases hbf : readBitsLSB 1 bits with
    | none => simp [hbf] at h
    | some p =>
      obtain ⟨bfinal, bits₁⟩ := p
      simp only [hbf, bind, Option.bind] at h
      cases hbt : readBitsLSB 2 bits₁ with
      | none => simp [hbt] at h
      | some q =>
        obtain ⟨btype, bits₂⟩ := q
        simp only [hbt] at h
        match hm : btype with
        | 0 =>
          cases hds : decodeStored bits₂ with
          | none => simp [hds] at h
          | some r =>
            obtain ⟨bytes, bits₃⟩ := r
            simp only [hds] at h
            split at h
            · simp [pure, Pure.pure] at h; exact h ▸ List.prefix_append _ _
            · exact List.IsPrefix.trans (List.prefix_append _ _) (ih _ _ _ h)
        | 1 =>
          cases hsyms : decodeSymbols fixedLitLengths fixedDistLengths bits₂ with
          | none => simp [hsyms] at h
          | some r =>
            obtain ⟨syms, bits₃⟩ := r
            simp only [hsyms] at h
            cases hres : resolveLZ77 syms acc with
            | none => simp [hres] at h
            | some acc' =>
              simp only [hres] at h
              have hacc' := resolveLZ77_extends syms acc acc' hres
              split at h
              · simp [pure, Pure.pure] at h; exact h ▸ hacc'
              · exact List.IsPrefix.trans hacc' (ih _ _ _ h)
        | 2 =>
          cases hdt : decodeDynamicTables bits₂ with
          | none => simp [hdt] at h
          | some r =>
            obtain ⟨litLens, distLens, bits₃⟩ := r
            simp only [hdt] at h
            cases hsyms : decodeSymbols litLens distLens bits₃ with
            | none => simp [hsyms] at h
            | some s =>
              obtain ⟨syms, bits₄⟩ := s
              simp only [hsyms] at h
              cases hres : resolveLZ77 syms acc with
              | none => simp [hres] at h
              | some acc' =>
                simp only [hres] at h
                have hacc' := resolveLZ77_extends syms acc acc' hres
                split at h
                · simp [pure, Pure.pure] at h; exact h ▸ hacc'
                · exact List.IsPrefix.trans hacc' (ih _ _ _ h)
        | _ + 3 => simp at h

theorem decode_fuel_independent
    (bits : List Bool) (fuel : Nat) (result : List UInt8) :
    decode bits fuel = some result →
    ∀ k, decode bits (fuel + k) = some result := by
  intro h k
  exact decode_go_fuel_independent bits [] fuel result h k

end Deflate.Spec
