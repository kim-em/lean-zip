import Zip.Spec.DeflateEncodeDynamic
import Zip.Spec.DeflateEncodeProps

/-!
# Dynamic Block Header Correspondence Proofs (RFC 1951 §3.2.7)

Proofs connecting the dynamic block header encoder (`encodeDynamicTrees`)
to the decoder (`decodeDynamicTables`):
- `readCLLengths_writeCLLengths`: CL length write/read roundtrip
- `encodeCLEntries_decodeCLSymbols_go`: CL entry encode/decode roundtrip
- `readCLLengths_recovers_clLens`: foldl-set recovery of original CL lengths
- `encodeDynamicTrees_decodeDynamicTables`: full header roundtrip theorem
-/

namespace Deflate.Spec

/-! ## Helper lemmas for the dynamic tree header roundtrip -/

protected theorem clPermutation_length : Deflate.Spec.clPermutation.length = 19 := by decide

/-- `codeLengthOrder.toList` is the same list as `clPermutation`. -/
private theorem codeLengthOrder_toList_eq_clPermutation :
    codeLengthOrder.toList = Deflate.Spec.clPermutation := by rfl

theorem computeHCLEN_ge_four (clLens : List Nat) : computeHCLEN clLens ≥ 4 := by
  simp [computeHCLEN]; omega

theorem computeHCLEN_le_nineteen (clLens : List Nat) : computeHCLEN clLens ≤ 19 := by
  simp only [computeHCLEN]
  have : (Deflate.Spec.clPermutation.map fun pos => clLens.getD pos 0).length = 19 := by
    simp [Deflate.Spec.clPermutation_length]
  omega

/-! ## readCLLengths / writeCLLengths roundtrip -/

/-- Reading back CL lengths written by `writeCLLengths` recovers the values
    in the correct permuted positions.

    The result accumulator has `clLens.getD pos 0` at each position `pos`
    that is `codeLengthOrder[j]` for some `j < numCodeLen`, and retains
    the original `acc` values elsewhere. -/
private theorem readCLLengths_writeCLLengths_go
    (clLens : List Nat) (n idx : Nat) (acc : List Nat) (rest : List Bool)
    (hacc : acc.length = 19) (hidx : idx + n ≤ 19)
    (hvals : ∀ i, clLens.getD i 0 < 8) :
    Deflate.Spec.readCLLengths n idx acc
      ((Deflate.Spec.clPermutation.drop idx |>.take n).flatMap
        (fun pos => writeBitsLSB 3 (clLens.getD pos 0)) ++ rest) =
    some ((Deflate.Spec.clPermutation.drop idx |>.take n).foldl
      (fun a pos => a.set pos (clLens.getD pos 0))
      acc, rest) := by
  induction n generalizing idx acc with
  | zero =>
    simp [Deflate.Spec.readCLLengths]
  | succ k ih =>
    have hidx_lt : idx < 19 := by omega
    have hperm_len := Deflate.Spec.clPermutation_length
    -- Unfold the drop/take to expose the head element
    have hdrop_cons : Deflate.Spec.clPermutation.drop idx =
        Deflate.Spec.clPermutation[idx] :: Deflate.Spec.clPermutation.drop (idx + 1) :=
      (List.getElem_cons_drop (h := by omega)).symm
    simp only [hdrop_cons, List.take_succ_cons, List.flatMap_cons, List.foldl_cons]
    rw [List.append_assoc]
    -- readCLLengths unfolds one step
    rw [Deflate.Spec.readCLLengths]
    -- Bridge: codeLengthOrder[idx]! = clPermutation[idx]
    have hCOsize : codeLengthOrder.size = 19 := by
      have := congrArg List.length codeLengthOrder_toList_eq_clPermutation
      simp only [Array.length_toList] at this; omega
    have hpos : codeLengthOrder[idx]! = Deflate.Spec.clPermutation[idx] := by
      rw [getElem!_pos codeLengthOrder idx (by omega)]
      rw [show codeLengthOrder[idx] =
          codeLengthOrder.toList[idx]'(by
            rw [codeLengthOrder_toList_eq_clPermutation]; omega) from
        (Array.getElem_toList (h := by omega)).symm]
      exact List.getElem_of_eq codeLengthOrder_toList_eq_clPermutation _
    -- readBitsLSB 3 recovers the value
    have hval : clLens.getD Deflate.Spec.clPermutation[idx] 0 < 2 ^ 3 := by
      have := hvals Deflate.Spec.clPermutation[idx]; omega
    rw [Deflate.Correctness.readBitsLSB_writeBitsLSB 3 _ _ hval]
    simp only [bind, Option.bind]
    -- The position written by readCLLengths matches clPermutation[idx]
    rw [hpos]
    -- Apply IH with updated accumulator
    have hacc' : (acc.set Deflate.Spec.clPermutation[idx]
        (clLens.getD Deflate.Spec.clPermutation[idx] 0)).length = 19 := by
      simp [hacc]
    exact ih (idx + 1) _ hacc' (by omega)

/-- `writeCLLengths` unfolds to a flatMap over the clPermutation. -/
private theorem writeCLLengths_eq_flatMap (clLens : List Nat) (numCodeLen : Nat) :
    writeCLLengths clLens numCodeLen =
    (Deflate.Spec.clPermutation.take numCodeLen).flatMap
      (fun pos => writeBitsLSB 3 (clLens.getD pos 0)) := by
  simp [writeCLLengths]

/-- Full roundtrip: `readCLLengths` on `writeCLLengths` output produces
    the expected accumulator. -/
theorem readCLLengths_writeCLLengths
    (clLens : List Nat) (numCodeLen : Nat) (rest : List Bool)
    (hnum : numCodeLen ≤ 19)
    (hvals : ∀ i, clLens.getD i 0 < 8) :
    Deflate.Spec.readCLLengths numCodeLen 0 (List.replicate 19 0)
      (writeCLLengths clLens numCodeLen ++ rest) =
    some ((Deflate.Spec.clPermutation.take numCodeLen).foldl
      (fun a pos => a.set pos (clLens.getD pos 0))
      (List.replicate 19 0), rest) := by
  rw [writeCLLengths_eq_flatMap]
  have := readCLLengths_writeCLLengths_go clLens numCodeLen 0 (List.replicate 19 0) rest
    (by simp) (by omega) hvals
  simp only [List.drop_zero] at this
  exact this

/-! ## CL entry encoding/decoding roundtrip -/

/-- The CL Huffman table constructed by `encodeDynamicTrees` is prefix-free,
    enabling single-symbol encode/decode roundtrip via `encodeSymbol_decode`. -/
private theorem clTable_prefix_free
    (clLens : List Nat) (maxBits : Nat)
    (hv : Huffman.Spec.ValidLengths clLens maxBits) :
    let clTable := (Huffman.Spec.allCodes clLens maxBits).map fun (sym, cw) => (cw, sym)
    ∀ cw₁ s₁ cw₂ s₂, (cw₁, s₁) ∈ clTable → (cw₂, s₂) ∈ clTable →
      (cw₁, s₁) ≠ (cw₂, s₂) → ¬cw₁.IsPrefix cw₂ :=
  flipped_allCodes_prefix_free clLens maxBits hv

/-- Code values outside {0..15, 16, 17, 18} make `rlDecodeLengths.go` return `none`. -/
private theorem rlDecodeLengths_go_invalid_code
    (code : Nat) (extra : Nat) (rest : List CLEntry) (acc : List Nat)
    (hle : ¬(code ≤ 15)) (h16 : code ≠ 16) (h17 : code ≠ 17) (h18 : code ≠ 18) :
    rlDecodeLengths.go ((code, extra) :: rest) acc = none := by
  simp only [rlDecodeLengths.go]
  split; · omega
  split; · exact absurd (beq_iff_eq.mp ‹_›) h16
  split; · exact absurd (beq_iff_eq.mp ‹_›) h17
  split; · exact absurd (beq_iff_eq.mp ‹_›) h18
  simp

/-- `rlDecodeLengths.go` only appends to the accumulator, so the result
    is at least as long as the input accumulator. -/
private theorem rlDecodeLengths_go_mono (entries : List CLEntry) (acc result : List Nat)
    (h : rlDecodeLengths.go entries acc = some result) :
    acc.length ≤ result.length := by
  induction entries generalizing acc with
  | nil => simp [rlDecodeLengths.go] at h; subst h; omega
  | cons entry rest ih =>
    obtain ⟨code, extra⟩ := entry
    by_cases hle : code ≤ 15
    · rw [Deflate.Spec.rlDecode_go_literal code extra rest acc hle] at h
      have := ih _ h; simp at this; omega
    · by_cases h16 : code = 16
      · subst h16
        by_cases hg : 0 < acc.length
        · rw [Deflate.Spec.rlDecode_go_code16 extra rest acc hg] at h
          have := ih _ h; simp at this; omega
        · exfalso; simp [rlDecodeLengths.go, hg, guard, bind, failure] at h
      · by_cases h17 : code = 17
        · subst h17; rw [Deflate.Spec.rlDecode_go_code17 extra rest acc] at h
          have := ih _ h; simp at this; omega
        · by_cases h18 : code = 18
          · subst h18; rw [Deflate.Spec.rlDecode_go_code18 extra rest acc] at h
            have := ih _ h; simp at this; omega
          · exact absurd h (rlDecodeLengths_go_invalid_code code extra rest acc hle h16 h17 h18 ▸ nofun)

/-- When `rlDecodeLengths.go` succeeds on a non-empty list, the result is
    strictly longer than the input accumulator. -/
private theorem rlDecodeLengths_go_strict_mono
    (entry : CLEntry) (rest : List CLEntry) (acc result : List Nat)
    (h : rlDecodeLengths.go (entry :: rest) acc = some result) :
    acc.length < result.length := by
  obtain ⟨code, extra⟩ := entry
  by_cases hle : code ≤ 15
  · rw [Deflate.Spec.rlDecode_go_literal code extra rest acc hle] at h
    have := rlDecodeLengths_go_mono rest _ _ h; simp at this; omega
  · by_cases h16 : code = 16
    · subst h16
      by_cases hg : 0 < acc.length
      · rw [Deflate.Spec.rlDecode_go_code16 extra rest acc hg] at h
        have := rlDecodeLengths_go_mono rest _ _ h; simp at this; omega
      · exfalso; simp [rlDecodeLengths.go, hg, guard, bind, failure] at h
    · by_cases h17 : code = 17
      · subst h17; rw [Deflate.Spec.rlDecode_go_code17 extra rest acc] at h
        have := rlDecodeLengths_go_mono rest _ _ h; simp at this; omega
      · by_cases h18 : code = 18
        · subst h18; rw [Deflate.Spec.rlDecode_go_code18 extra rest acc] at h
          have := rlDecodeLengths_go_mono rest _ _ h; simp at this; omega
        · exact absurd h (rlDecodeLengths_go_invalid_code code extra rest acc hle h16 h17 h18 ▸ nofun)

/-- Encoding CL entries then decoding with `decodeCLSymbols` recovers
    the original code lengths (via RLE decode).

    Uses `rlDecodeLengths.go` with a general accumulator for induction.
    The fuel parameter must be ≥ entries.length + 1 (one per entry plus
    one for the final base-case check). -/
private theorem encodeCLEntries_decodeCLSymbols_go
    (clLens : List Nat)
    (clTable : List (Huffman.Spec.Codeword × Nat))
    (entries : List CLEntry)
    (symbolBits : List Bool)
    (rest : List Bool)
    (totalCodes : Nat)
    (acc : List Nat)
    (fuel : Nat)
    (hv : Huffman.Spec.ValidLengths clLens 7)
    (htable : clTable = (Huffman.Spec.allCodes clLens 7).map fun (sym, cw) => (cw, sym))
    (henc : encodeCLEntries clTable entries = some symbolBits)
    (hvalid : ∀ entry ∈ entries, (entry.1 ≤ 15 ∧ entry.2 = 0) ∨
      (entry.1 = 16 ∧ entry.2 ≤ 3) ∨
      (entry.1 = 17 ∧ entry.2 ≤ 7) ∨
      (entry.1 = 18 ∧ entry.2 ≤ 127))
    (hdec : rlDecodeLengths.go entries acc = some result)
    (hlen : result.length = totalCodes)
    (hacc_le : acc.length ≤ totalCodes)
    (hfuel : fuel ≥ entries.length + 1) :
    decodeDynamicTables.decodeCLSymbols clTable totalCodes acc
      (symbolBits ++ rest) fuel =
    some (result, rest) := by
  induction entries generalizing acc symbolBits fuel with
  | nil =>
    -- Base case: no entries, result = acc, fuel ≥ 1
    simp [encodeCLEntries] at henc; subst henc
    simp [rlDecodeLengths.go] at hdec; subst hdec
    simp only [List.nil_append]
    match fuel, hfuel with
    | fuel' + 1, _ =>
      simp [decodeDynamicTables.decodeCLSymbols, show acc.length ≥ totalCodes from by omega]
  | cons entry restEntries ih =>
    obtain ⟨code, extra⟩ := entry
    -- Decompose encodeCLEntries
    simp only [encodeCLEntries] at henc
    cases hcw : encodeSymbol clTable code with
    | none => simp [hcw, bind, Option.bind] at henc
    | some cw =>
      cases hrestBits : encodeCLEntries clTable restEntries with
      | none => simp [hcw, hrestBits, bind, Option.bind] at henc
      | some restBits =>
        simp only [hcw, hrestBits, bind, Option.bind, pure, Pure.pure] at henc
        simp only [Option.some.injEq] at henc; subst henc
        -- Key facts
        have hacc_lt : acc.length < totalCodes :=
          hlen ▸ rlDecodeLengths_go_strict_mono (code, extra) restEntries acc result hdec
        have hvalid_rest : ∀ entry ∈ restEntries,
            (entry.1 ≤ 15 ∧ entry.2 = 0) ∨ (entry.1 = 16 ∧ entry.2 ≤ 3) ∨
            (entry.1 = 17 ∧ entry.2 ≤ 7) ∨ (entry.1 = 18 ∧ entry.2 ≤ 127) :=
          fun e he => hvalid e (List.mem_cons_of_mem _ he)
        have hpf : ∀ cw₁ s₁ cw₂ s₂, (cw₁, s₁) ∈ clTable → (cw₂, s₂) ∈ clTable →
            (cw₁, s₁) ≠ (cw₂, s₂) → ¬cw₁.IsPrefix cw₂ := by
          rw [htable]; exact flipped_allCodes_prefix_free clLens 7 hv
        have hentry := hvalid (code, extra) (.head ..)
        -- Decompose fuel
        match fuel, hfuel with
        | fuel' + 1, hfuel' =>
          -- Unfold decodeCLSymbols, enter decode branch
          simp only [decodeDynamicTables.decodeCLSymbols,
            show ¬(acc.length ≥ totalCodes) from by omega, ↓reduceIte]
          -- Reassociate bits for Huffman decode
          rw [show (cw ++ encodeCLExtra code extra ++ restBits) ++ rest =
              cw ++ (encodeCLExtra code extra ++ restBits ++ rest) from by
            simp [List.append_assoc]]
          rw [encodeSymbol_decode _ _ _ _ hcw hpf]
          simp only [bind, Option.bind]
          -- Case split on the code type
          by_cases hle : code ≤ 15
          · -- Literal code (0-15): no extra bits
            rw [if_pos (show code < 16 from by omega)]
            -- encodeCLExtra for code ≤ 15 is []
            have h16f : (code == 16) = false := by
              cases h : code == 16 <;> simp_all [beq_iff_eq] <;> omega
            have h17f : (code == 17) = false := by
              cases h : code == 17 <;> simp_all [beq_iff_eq] <;> omega
            have h18f : (code == 18) = false := by
              cases h : code == 18 <;> simp_all [beq_iff_eq] <;> omega
            simp only [encodeCLExtra, h16f, h17f, h18f,
              Bool.false_eq_true, ↓reduceIte, List.nil_append]
            -- rlDecodeLengths.go step for literal
            rw [Deflate.Spec.rlDecode_go_literal code extra restEntries acc hle] at hdec
            -- Apply IH
            exact ih restBits (acc ++ [code]) fuel' hrestBits hvalid_rest hdec
              (by simp; omega) (by simp at hfuel' ⊢; omega)
          · -- Repeat codes (16, 17, 18)
            rw [if_neg (show ¬(code < 16) from by omega)]
            -- From hentry and ¬(code ≤ 15), code must be 16, 17, or 18
            cases hentry with
            | inl h => exact absurd h.1 (by omega)
            | inr h => cases h with
              | inl h16 =>
                -- Code 16: repeat previous code
                have h16eq := h16.1; have hextra := h16.2; subst h16eq
                have haccpos : acc.length > 0 := by
                  by_cases hpos : acc.length > 0
                  · exact hpos
                  · exfalso; simp [rlDecodeLengths.go, show acc.length = 0 from by omega,
                      guard, failure, bind, Option.bind] at hdec
                rw [Deflate.Spec.rlDecode_go_code16 extra restEntries acc haccpos] at hdec
                have hacc' := hlen ▸ rlDecodeLengths_go_mono restEntries _ _ hdec
                have hrb := Deflate.Correctness.readBitsLSB_writeBitsLSB 2 extra
                  (restBits ++ rest) (by omega)
                simp [encodeCLExtra, guard, haccpos, hrb, List.append_assoc]
                simp only [show acc.length + (extra + 3) ≤ totalCodes from by
                  have := hacc'; simp at this; exact this, ↓reduceIte]
                rw [show acc.getLast?.getD 0 = acc.getLast! from
                  List.getLast?_getD_eq_getLast! acc haccpos]
                exact ih restBits _ fuel' hrestBits hvalid_rest hdec hacc'
                  (by simp only [List.length_cons] at hfuel'; omega)
              | inr h => cases h with
                | inl h17 =>
                  -- Code 17: repeat 0, 3-10 times
                  have h17eq := h17.1; have hextra := h17.2; subst h17eq
                  rw [Deflate.Spec.rlDecode_go_code17 extra restEntries acc] at hdec
                  have hacc' := hlen ▸ rlDecodeLengths_go_mono restEntries _ _ hdec
                  have hrb := Deflate.Correctness.readBitsLSB_writeBitsLSB 3 extra
                    (restBits ++ rest) (by omega)
                  simp [encodeCLExtra, guard, hrb, List.append_assoc]
                  simp [show acc.length + (extra + 3) ≤ totalCodes from by
                    have := hacc'; simp at this; exact this]
                  exact ih restBits _ fuel' hrestBits hvalid_rest hdec hacc'
                    (by simp only [List.length_cons] at hfuel'; omega)
                | inr h18 =>
                  -- Code 18: repeat 0, 11-138 times
                  have h18eq := h18.1; have hextra := h18.2; subst h18eq
                  rw [Deflate.Spec.rlDecode_go_code18 extra restEntries acc] at hdec
                  have hacc' := hlen ▸ rlDecodeLengths_go_mono restEntries _ _ hdec
                  have hrb := Deflate.Correctness.readBitsLSB_writeBitsLSB 7 extra
                    (restBits ++ rest) (by omega)
                  simp [encodeCLExtra, guard, hrb, List.append_assoc]
                  simp [show acc.length + (extra + 11) ≤ totalCodes from by
                    have := hacc'; simp at this; exact this]
                  exact ih restBits _ fuel' hrestBits hvalid_rest hdec hacc'
                    (by simp only [List.length_cons] at hfuel'; omega)

/-! ## CL lengths recovery -/

/-- `clPermutation` contains no duplicates. -/
private theorem clPermutation_nodup : Deflate.Spec.clPermutation.Nodup := by decide

/-- Every position in `clPermutation` is less than 19. -/
private theorem clPermutation_lt_nineteen :
    ∀ p ∈ Deflate.Spec.clPermutation, p < 19 := by decide

/-- Every `p < 19` appears in `clPermutation`. -/
private theorem clPermutation_contains_all (p : Nat) (hp : p < 19) :
    p ∈ Deflate.Spec.clPermutation := by
  have : Deflate.Spec.clPermutation = [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15] := rfl
  simp only [this, List.mem_cons]; omega

/-- After `computeHCLEN`, the trailing positions in permuted order have value 0. -/
private theorem computeHCLEN_trailing_zero (clLens : List Nat) (j : Nat)
    (hj : j ≥ computeHCLEN clLens) (hjlt : j < 19) :
    clLens.getD (Deflate.Spec.clPermutation.getD j 0) 0 = 0 := by
  simp only [computeHCLEN] at hj
  have hperm_len := Deflate.Spec.clPermutation_length
  -- Work with the permuted lens list
  let pl := Deflate.Spec.clPermutation.map fun pos => clLens.getD pos 0
  have hpl_len : pl.length = 19 := by simp [pl, hperm_len]
  -- The trailing zeros in reverse
  let tw := pl.reverse.takeWhile (· == 0)
  -- tw is a prefix of pl.reverse
  have htw_prefix : tw <+: pl.reverse := List.takeWhile_prefix (· == 0)
  have htw_le : tw.length ≤ 19 := by
    have := htw_prefix.length_le; simp [hpl_len] at this; exact this
  -- j ≥ lastNonZero = 19 - tw.length, so 18 - j < tw.length
  -- Rewrite hj to use pl.length and tw.length
  change j ≥ max 4 (pl.length - tw.length) at hj
  rw [hpl_len] at hj
  have hidx : 18 - j < tw.length := by omega
  have htw_eq := List.prefix_iff_eq_take.mp htw_prefix
  -- tw[18-j] = pl.reverse[18-j] = pl[j]
  have helem : tw[18 - j] = pl[j]'(by rw [hpl_len]; exact hjlt) := by
    rw [htw_prefix.getElem hidx, List.getElem_reverse]
    exact getElem_congr_idx (by rw [hpl_len]; omega)
  -- All elements of tw satisfy (· == 0)
  have hall := List.all_takeWhile (l := pl.reverse) (p := (· == 0))
  rw [List.all_eq_true] at hall
  have hpred := hall _ (List.getElem_mem (n := 18 - j) hidx)
  simp only [beq_iff_eq] at hpred
  -- pl[j] = 0
  have hzero : pl[j]'(by rw [hpl_len]; exact hjlt) = 0 := by rw [← helem]; exact hpred
  -- Bridge: pl[j] = clLens.getD (clPermutation.getD j 0) 0
  -- pl[j] = (clPermutation.map f)[j] = f(clPermutation[j]) = clLens.getD clPermutation[j] 0
  have hmap : pl[j]'(by rw [hpl_len]; exact hjlt) =
      clLens.getD (Deflate.Spec.clPermutation[j]'(by rw [hperm_len]; exact hjlt)) 0 := by
    exact List.getElem_map ..
  rw [hmap] at hzero
  -- hzero: clLens.getD clPermutation[j] 0 = 0
  -- Goal: clLens.getD (clPermutation.getD j 0) 0 = 0
  rwa [show Deflate.Spec.clPermutation.getD j 0 =
      Deflate.Spec.clPermutation[j]'(by rw [hperm_len]; exact hjlt) from
    (List.getElem_eq_getD 0).symm]

/-- The foldl-set over clPermutation.take n on replicate 19 0 recovers
    the original list when trailing positions have value 0. -/
private theorem readCLLengths_recovers_clLens
    (clLens : List Nat) (numCodeLen : Nat)
    (hlen : clLens.length = 19) (hnum : numCodeLen ≤ 19)
    (htrailing : ∀ j, j ≥ numCodeLen → j < 19 →
      clLens.getD (Deflate.Spec.clPermutation.getD j 0) 0 = 0) :
    (Deflate.Spec.clPermutation.take numCodeLen).foldl
      (fun a pos => a.set pos (clLens.getD pos 0))
      (List.replicate 19 0) = clLens := by
  have hperm_len := Deflate.Spec.clPermutation_length
  let positions := Deflate.Spec.clPermutation.take numCodeLen
  have hpos_nodup : positions.Nodup :=
    List.Nodup.sublist (List.take_sublist _ _) clPermutation_nodup
  have hpos_bounds : ∀ q ∈ positions, q < 19 := by
    intro q hq; exact clPermutation_lt_nineteen q (List.take_subset _ _ hq)
  -- Prove by extensionality
  apply List.ext_getElem
  · -- Length
    rw [List.foldl_set_length, List.length_replicate]; exact hlen.symm
  · intro p h1 h2
    have hp19 : p < 19 := by rw [List.foldl_set_length, List.length_replicate] at h1; exact h1
    by_cases hmem : p ∈ positions
    · -- p was set by the foldl
      rw [List.foldl_set_getElem_mem positions _ _ p hmem hpos_nodup
          (by simp; omega)
          (fun q hq => by simp; exact hpos_bounds q hq)]
      -- Goal: clLens.getD p 0 = clLens[p]
      exact (List.getElem_eq_getD 0).symm
    · -- p was NOT set; value is 0 from replicate
      rw [List.foldl_set_getElem_not_mem positions _ _ p hmem
          (by simp; omega)]
      simp only [List.getElem_replicate]
      -- Need: clLens[p] = 0
      -- p ∉ positions = clPermutation.take numCodeLen
      -- But p < 19 and clPermutation is a permutation of [0..18]
      -- So p ∈ clPermutation, hence p ∈ clPermutation.drop numCodeLen
      have hp_in_perm : p ∈ Deflate.Spec.clPermutation :=
        clPermutation_contains_all p hp19
      have hp_in_drop : p ∈ Deflate.Spec.clPermutation.drop numCodeLen := by
        have htad := List.take_append_drop numCodeLen Deflate.Spec.clPermutation
        rw [← htad] at hp_in_perm
        simp only [List.mem_append] at hp_in_perm
        exact hp_in_perm.resolve_left hmem
      -- Get the index k in the dropped list where drop[k] = p
      rw [List.mem_iff_getElem] at hp_in_drop
      obtain ⟨k, hk_lt, hk_eq⟩ := hp_in_drop
      have hj_lt : numCodeLen + k < 19 := by
        rw [List.length_drop, hperm_len] at hk_lt; omega
      -- clPermutation[numCodeLen + k] = (clPermutation.drop numCodeLen)[k] = p
      have hperm_eq : Deflate.Spec.clPermutation.getD (numCodeLen + k) 0 = p := by
        rw [List.getD_eq_getElem?_getD,
            List.getElem?_eq_getElem (h := by rw [hperm_len]; omega),
            Option.getD_some]
        rw [← List.getElem_drop (h := hk_lt)]
        exact hk_eq
      have htr := htrailing (numCodeLen + k) (by omega) hj_lt
      rw [hperm_eq] at htr
      -- htr: clLens.getD p 0 = 0
      rw [List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (h := h2),
          Option.getD_some] at htr
      exact htr.symm

/-- The number of RLE entries is at most the decoded length. -/
private theorem rlDecodeLengths_go_entries_le_result
    (entries : List CLEntry) (acc result : List Nat)
    (h : rlDecodeLengths.go entries acc = some result) :
    entries.length + acc.length ≤ result.length := by
  induction entries generalizing acc with
  | nil => simp [rlDecodeLengths.go] at h; subst h; simp
  | cons entry rest ih =>
    obtain ⟨code, extra⟩ := entry
    by_cases hle : code ≤ 15
    · rw [Deflate.Spec.rlDecode_go_literal code extra rest acc hle] at h
      have := ih (acc ++ [code]) h
      simp only [List.length_append, List.length_cons] at this ⊢; omega
    · by_cases h16 : code = 16
      · subst h16
        by_cases hg : 0 < acc.length
        · rw [Deflate.Spec.rlDecode_go_code16 extra rest acc hg] at h
          have := ih _ h
          simp only [List.length_append, List.length_replicate, List.length_cons] at this ⊢; omega
        · exfalso; simp [rlDecodeLengths.go, hg, guard, failure, bind] at h
      · by_cases h17 : code = 17
        · subst h17; rw [Deflate.Spec.rlDecode_go_code17 extra rest acc] at h
          have := ih _ h
          simp only [List.length_append, List.length_replicate, List.length_cons] at this ⊢; omega
        · by_cases h18 : code = 18
          · subst h18; rw [Deflate.Spec.rlDecode_go_code18 extra rest acc] at h
            have := ih _ h
            simp only [List.length_append, List.length_replicate, List.length_cons] at this ⊢; omega
          · exact absurd h (rlDecodeLengths_go_invalid_code code extra rest acc hle h16 h17 h18 ▸ nofun)

/-! ## Dynamic tree header roundtrip -/

/-- The dynamic tree header roundtrip: encoding then decoding recovers
    the original code lengths. -/
theorem encodeDynamicTrees_decodeDynamicTables
    (litLens distLens : List Nat)
    (headerBits rest : List Bool)
    (hlit : ∀ x ∈ litLens, x ≤ 15) (hdist : ∀ x ∈ distLens, x ≤ 15)
    (hlitLen : litLens.length ≥ 257 ∧ litLens.length ≤ 288)
    (hdistLen : distLens.length ≥ 1 ∧ distLens.length ≤ 32)
    (hlit_valid : Huffman.Spec.ValidLengths litLens 15)
    (hdist_valid : Huffman.Spec.ValidLengths distLens 15)
    (henc : encodeDynamicTrees litLens distLens = some headerBits) :
    decodeDynamicTables (headerBits ++ rest) = some (litLens, distLens, rest) := by
  -- Set up abbreviations for key intermediate values
  have hallLens : ∀ x ∈ litLens ++ distLens, x ≤ 15 := by
    intro x hx; simp only [List.mem_append] at hx; cases hx with
    | inl h => exact hlit x h | inr h => exact hdist x h
  let allLens := litLens ++ distLens
  let clEntries := rlEncodeLengths allLens
  let clFreqs := clSymbolFreqs clEntries
  let clFreqPairs := (List.range clFreqs.length).map fun i => (i, clFreqs.getD i 0)
  let clLens := Huffman.Spec.computeCodeLengths clFreqPairs 19 7
  let clCodes := Huffman.Spec.allCodes clLens 7
  let clTable := clCodes.map fun (sym, cw) => (cw, sym)
  let numCodeLen := computeHCLEN clLens
  let hlit_val := litLens.length - 257
  let hdist_val := distLens.length - 1
  let hclen_val := numCodeLen - 4
  -- Extract symbolBits from encoder
  have henc_unfold : encodeDynamicTrees litLens distLens = do
    guard (litLens.length ≥ 257 ∧ litLens.length ≤ 288)
    guard (distLens.length ≥ 1 ∧ distLens.length ≤ 32)
    let symbolBits ← encodeCLEntries clTable clEntries
    return writeBitsLSB 5 hlit_val ++ writeBitsLSB 5 hdist_val ++
      writeBitsLSB 4 hclen_val ++ writeCLLengths clLens numCodeLen ++ symbolBits
    := by rfl
  rw [henc_unfold] at henc; clear henc_unfold
  simp only [hlitLen.1, hlitLen.2, hdistLen.1, hdistLen.2, guard, and_self,
    ↓reduceIte, pure, Pure.pure, bind, Option.bind] at henc
  cases hsymEnc : encodeCLEntries clTable clEntries with
  | none => simp [hsymEnc] at henc
  | some symbolBits =>
    simp only [hsymEnc, Option.some.injEq] at henc
    subst henc
    -- Now goal: decodeDynamicTables ((...) ++ rest) = some (litLens, distLens, rest)
    -- Prove key bounds
    have hhlit_bound : hlit_val < 2 ^ 5 := by omega
    have hhdist_bound : hdist_val < 2 ^ 5 := by omega
    have hhclen_bound : hclen_val < 2 ^ 4 := by
      have := computeHCLEN_le_nineteen clLens; omega
    -- Reassociate the header bits for sequential readBitsLSB
    have hbits_assoc : (writeBitsLSB 5 hlit_val ++ writeBitsLSB 5 hdist_val ++
        writeBitsLSB 4 hclen_val ++ writeCLLengths clLens numCodeLen ++
        symbolBits) ++ rest =
      writeBitsLSB 5 hlit_val ++ (writeBitsLSB 5 hdist_val ++
        (writeBitsLSB 4 hclen_val ++
          (writeCLLengths clLens numCodeLen ++ (symbolBits ++ rest)))) := by
      simp [List.append_assoc]
    -- Unfold decodeDynamicTables as a sequence of bind operations
    unfold decodeDynamicTables
    rw [hbits_assoc]
    -- Step 1: readBitsLSB 5 recovers hlit_val
    simp only [bind, Option.bind,
      Deflate.Correctness.readBitsLSB_writeBitsLSB 5 hlit_val _ hhlit_bound,
      Deflate.Correctness.readBitsLSB_writeBitsLSB 5 hdist_val _ hhdist_bound,
      Deflate.Correctness.readBitsLSB_writeBitsLSB 4 hclen_val _ hhclen_bound]
    -- hlit_val + 257 = litLens.length, hdist_val + 1 = distLens.length
    have hhlit_eq : hlit_val + 257 = litLens.length := by omega
    have hhdist_eq : hdist_val + 1 = distLens.length := by omega
    have hhclen_eq : hclen_val + 4 = numCodeLen := by
      have := computeHCLEN_ge_four clLens; omega
    rw [hhlit_eq, hhdist_eq, hhclen_eq]
    -- Step 4: readCLLengths recovers clLens
    have hclLens_len : clLens.length = 19 :=
      Huffman.Spec.computeCodeLengths_length clFreqPairs 19 7
    have hclLens_bounded : ∀ l ∈ clLens, l ≤ 7 :=
      Huffman.Spec.computeCodeLengths_bounded clFreqPairs 19 7 (by omega)
    have hvals : ∀ i, clLens.getD i 0 < 8 := by
      intro i
      by_cases hi : i < clLens.length
      · have := hclLens_bounded (clLens[i]) (List.getElem_mem ..)
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]; omega
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; simp
    have hnum_le : numCodeLen ≤ 19 := computeHCLEN_le_nineteen clLens
    have htrailing : ∀ j, j ≥ numCodeLen → j < 19 →
        clLens.getD (Deflate.Spec.clPermutation.getD j 0) 0 = 0 :=
      computeHCLEN_trailing_zero clLens
    -- readCLLengths produces the foldl result, which equals clLens
    have hreadCL := readCLLengths_writeCLLengths clLens numCodeLen (symbolBits ++ rest)
      hnum_le hvals
    have hfoldl_eq := readCLLengths_recovers_clLens clLens numCodeLen hclLens_len hnum_le htrailing
    rw [hfoldl_eq] at hreadCL
    -- Now hreadCL : readCLLengths numCodeLen 0 (...) (writeCLLengths ... ++ ...) = some (clLens, symbolBits ++ rest)
    simp only [hreadCL]
    -- Step 5: decodeCLSymbols recovers litLens ++ distLens
    -- Need ValidLengths for clLens
    have hv : Huffman.Spec.ValidLengths clLens 7 :=
      Huffman.Spec.computeCodeLengths_valid clFreqPairs 19 7 (by omega) (by omega)
    -- Discharge the CL ValidLengths guard
    simp only [guard, hv, ↓reduceIte, pure, Pure.pure]
    -- The table matches
    have htable : clTable = (Huffman.Spec.allCodes clLens 7).map fun (sym, cw) => (cw, sym) := by rfl
    -- RLE roundtrip
    have hrle : rlDecodeLengths.go clEntries [] = some allLens := by
      have := rlDecodeLengths_go_rlEncodeLengths_go allLens [] hallLens
      simp at this
      exact this
    -- Entry validity
    have hvalid_entries : ∀ entry ∈ clEntries,
        (entry.1 ≤ 15 ∧ entry.2 = 0) ∨
        (entry.1 = 16 ∧ entry.2 ≤ 3) ∨
        (entry.1 = 17 ∧ entry.2 ≤ 7) ∨
        (entry.1 = 18 ∧ entry.2 ≤ 127) :=
      rlEncodeLengths_valid allLens hallLens
    -- Total codes
    let totalCodes := litLens.length + distLens.length
    have htotalLen : allLens.length = totalCodes := by simp [allLens, totalCodes]
    -- Fuel bound: clEntries.length ≤ totalCodes
    have hfuel : totalCodes + 1 ≥ clEntries.length + 1 := by
      have := rlDecodeLengths_go_entries_le_result clEntries [] allLens hrle
      simp only [List.length_nil, Nat.add_zero] at this; omega
    -- Apply the main roundtrip theorem
    have hdecCL := encodeCLEntries_decodeCLSymbols_go clLens clTable clEntries
      symbolBits rest totalCodes [] (totalCodes + 1)
      hv htable hsymEnc hvalid_entries hrle htotalLen (by simp) hfuel
    -- Rewrite the goal to use hdecCL
    rw [show (List.map (fun x => (x.snd, x.fst)) (Huffman.Spec.allCodes clLens 7)) = clTable from rfl]
    rw [hdecCL]
    -- Guard and take/drop
    have hlen_eq : allLens.length = litLens.length + distLens.length := htotalLen
    simp only [hlen_eq, beq_self_eq_true, ite_true]
    -- Discharge lit/dist ValidLengths guards
    have hlit_take : (litLens ++ distLens).take litLens.length = litLens := List.take_left
    have hdist_drop : (litLens ++ distLens).drop litLens.length = distLens := List.drop_left
    rw [hlit_take, hdist_drop]
    simp only [hlit_valid, hdist_valid, ↓reduceIte]

/-! ## encodeCLEntries success -/

private abbrev clFreqFoldl := fun (acc : List Nat) (p : CLEntry) =>
  if p.1 < acc.length then acc.set p.1 (acc.getD p.1 0 + 1) else acc

/-- The foldl preserves `acc.length`. -/
private theorem clFreqFoldl_length (entries : List CLEntry)
    (acc : List Nat) (hacc : acc.length = n) :
    (entries.foldl clFreqFoldl acc).length = n := by
  induction entries generalizing acc with
  | nil => exact hacc
  | cons entry rest ih =>
    simp only [List.foldl_cons, clFreqFoldl]
    split
    · exact ih _ (by rw [List.length_set]; exact hacc)
    · exact ih _ hacc

/-- The foldl monotonically increases each entry: if `acc.getD code 0 > 0`,
    the result also has `getD code 0 > 0`. -/
private theorem clFreqFoldl_mono (entries : List CLEntry) (code : Nat)
    (acc : List Nat) (hacc : acc.length = 19) (hpos : acc.getD code 0 > 0) :
    (entries.foldl clFreqFoldl acc).getD code 0 > 0 := by
  induction entries generalizing acc with
  | nil => exact hpos
  | cons entry rest ih =>
    simp only [List.foldl_cons, clFreqFoldl]
    obtain ⟨c', _⟩ := entry
    by_cases hc'lt : c' < acc.length
    · rw [if_pos hc'lt]
      apply ih
      · rw [List.length_set]; exact hacc
      · rw [List.getD_eq_getElem?_getD, List.getElem?_set]
        by_cases hc'code : c' = code
        · subst hc'code
          rw [if_pos rfl, if_pos hc'lt]; simp only [Option.getD_some]; omega
        · rw [if_neg hc'code, ← List.getD_eq_getElem?_getD]; exact hpos
    · rw [if_neg hc'lt]; exact ih acc hacc hpos

/-- The foldl produces a positive entry at `code` if `(code, _)` appears
    in the entries and `code < acc.length`. Generalized over accumulator. -/
private theorem clFreqFoldl_pos (entries : List CLEntry) (code extra : Nat)
    (acc : List Nat) (hacc : acc.length = 19) (hcode : code < 19)
    (hmem : (code, extra) ∈ entries) :
    (entries.foldl clFreqFoldl acc).getD code 0 > 0 := by
  induction entries generalizing acc with
  | nil => simp at hmem
  | cons entry rest ih =>
    simp only [List.foldl_cons, clFreqFoldl]
    obtain ⟨c, e⟩ := entry
    simp only [List.mem_cons, Prod.mk.injEq] at hmem
    cases hmem with
    | inl heq =>
      have hc_eq : c = code := heq.1.symm
      have hclt_acc : c < acc.length := by omega
      rw [if_pos hclt_acc]; subst hc_eq
      apply clFreqFoldl_mono
      · rw [List.length_set]; exact hacc
      · rw [List.getD_eq_getElem?_getD, List.getElem?_set]
        rw [if_pos rfl, if_pos hclt_acc]; simp only [Option.getD_some]; omega
    | inr hmem_rest =>
      by_cases hclt : c < acc.length
      · rw [if_pos hclt]
        exact ih _ (by rw [List.length_set]; exact hacc) hmem_rest
      · rw [if_neg hclt]
        exact ih acc hacc hmem_rest

/-- `clSymbolFreqs` always returns a list of length 19. -/
theorem clSymbolFreqs_length (entries : List CLEntry) :
    (clSymbolFreqs entries).length = 19 :=
  clFreqFoldl_length entries _ (List.length_replicate ..)

/-- If `(code, _)` appears in `entries` and `code < 19`, then
    `(clSymbolFreqs entries).getD code 0 > 0`. -/
theorem clSymbolFreqs_pos (entries : List CLEntry) (code extra : Nat)
    (hmem : (code, extra) ∈ entries) (hcode : code < 19) :
    (clSymbolFreqs entries).getD code 0 > 0 :=
  clFreqFoldl_pos entries code extra _ (List.length_replicate ..) hcode hmem

/-- `encodeCLEntries` succeeds when all entry codes have nonzero CL code lengths. -/
theorem encodeCLEntries_isSome (clLens : List Nat) (maxBits : Nat)
    (entries : List CLEntry)
    (hall : ∀ p ∈ entries, p.1 < clLens.length ∧ clLens[p.1]! ≠ 0 ∧ clLens[p.1]! ≤ maxBits) :
    (encodeCLEntries ((Huffman.Spec.allCodes clLens maxBits).map
      fun p => (p.2, p.1)) entries).isSome = true := by
  induction entries with
  | nil => simp [encodeCLEntries]
  | cons entry rest ih =>
    obtain ⟨code, extra⟩ := entry
    simp only [encodeCLEntries]
    have ⟨hlt, hne, hle⟩ := hall (code, extra) (List.mem_cons_self ..)
    have hsym := encodeSymbol_fixed_isSome clLens maxBits code hlt hne hle
    cases hes : encodeSymbol ((Huffman.Spec.allCodes clLens maxBits).map
        fun p => (p.2, p.1)) code with
    | none => simp [hes] at hsym
    | some cwBits =>
      simp only [bind, Option.bind]
      have hrest := ih (fun p hp => hall p (List.mem_cons_of_mem _ hp))
      cases her : encodeCLEntries ((Huffman.Spec.allCodes clLens maxBits).map
          fun p => (p.2, p.1)) rest with
      | none => simp [her] at hrest
      | some restBits => simp [pure, Pure.pure]

end Deflate.Spec
