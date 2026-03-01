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

set_option maxRecDepth 2048 in
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

set_option maxRecDepth 2048 in
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
