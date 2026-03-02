import Zip.Spec.InflateCorrect
import Zip.Spec.DynamicTreesComplete

/-!
# DEFLATE Stream-Level Completeness

Proves completeness: if the formal bitstream specification (`Deflate.Spec.decode`)
succeeds, then the native pure-Lean DEFLATE decompressor also succeeds and
produces the same output.

This is the reverse direction of `InflateCorrect`. The main theorem is
`inflateLoop_complete`.
-/

namespace Deflate.Correctness

/-! ## Helpers -/

/-- UInt8→Nat→UInt8 roundtrip: `Nat.toUInt8 ∘ UInt8.toNat = id` pointwise. -/
private theorem uint8_nat_roundtrip (l : List UInt8) :
    l.map (Nat.toUInt8 ∘ UInt8.toNat) = l := by
  rw [List.map_congr_left (fun u _ => by
    show Nat.toUInt8 (UInt8.toNat u) = u
    unfold Nat.toUInt8 UInt8.ofNat UInt8.toNat
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq])]
  simp

/-- Nat→UInt8→Nat roundtrip for lists with elements bounded by `maxBits ≤ 15`. -/
theorem validLengths_toUInt8_roundtrip (lens : List Nat)
    (hv : Huffman.Spec.ValidLengths lens maxBits) (hmb : maxBits ≤ 15) :
    (lens.map Nat.toUInt8).toArray.toList.map UInt8.toNat = lens := by
  simp only [List.map_map]
  rw [List.map_congr_left (fun n hn => by
    show (Nat.toUInt8 n).toNat = n
    simp only [Nat.toUInt8, UInt8.toNat, UInt8.ofNat, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by have := hv.1 n hn; omega))]
  simp

/-! ## Fuel monotonicity -/

/-- Fuel monotonicity: if `inflateLoop` succeeds with fuel `n`, it succeeds
    with any `m ≥ n` and produces the same result. -/
theorem inflateLoop_fuel_le
    (br : Zip.Native.BitReader) (output : ByteArray)
    (fixedLit fixedDist : Zip.Native.HuffTree) (maxOut n m : Nat)
    (x : ByteArray × Nat)
    (h : Zip.Native.Inflate.inflateLoop br output fixedLit fixedDist maxOut n = .ok x)
    (hle : n ≤ m) :
    Zip.Native.Inflate.inflateLoop br output fixedLit fixedDist maxOut m = .ok x := by
  induction n generalizing br output m with
  | zero => simp [Zip.Native.Inflate.inflateLoop] at h
  | succ n ih =>
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp only [Zip.Native.Inflate.inflateLoop, bind, Except.bind] at h ⊢
    -- readBits 1
    cases hbf : br.readBits 1 with
    | error e => simp [hbf] at h
    | ok p₁ =>
      obtain ⟨bfinal, br₁⟩ := p₁; simp only [hbf] at h ⊢
      -- readBits 2
      cases hbt : br₁.readBits 2 with
      | error e => simp [hbt] at h
      | ok p₂ =>
        obtain ⟨btype, br₂⟩ := p₂; simp only [hbt] at h ⊢
        -- Both h and ⊢ match on btype; only fuel differs (n vs m')
        -- split at h resolves the shared discriminant in both h and ⊢
        split at h
        · -- btype = 0: stored
          split at h
          · exact h -- error case
          · -- ok case: bfinal check
            split at h <;> split
            · exact h
            · rename_i h1 h2; exact absurd h1 h2
            · rename_i h1 h2; exact absurd h2 h1
            · exact ih _ _ _ h (by omega)
        · -- btype = 1: fixed Huffman
          split at h
          · exact h
          · split at h <;> split
            · exact h
            · rename_i h1 h2; exact absurd h1 h2
            · rename_i h1 h2; exact absurd h2 h1
            · exact ih _ _ _ h (by omega)
        · -- btype = 2: dynamic Huffman
          split at h
          · exact h -- decodeDynamicTrees error
          · split at h
            · exact h -- decodeHuffman error
            · split at h <;> split
              · exact h
              · rename_i h1 h2; exact absurd h1 h2
              · rename_i h1 h2; exact absurd h2 h1
              · exact ih _ _ _ h (by omega)
        · exact h -- btype ≥ 3: reserved error

/-! ## Block loop completeness -/

set_option maxRecDepth 2048 in
/-- **Completeness for block loop**: if the spec `decode.go` succeeds,
    the native `inflateLoop` also succeeds with the same result.

    Note: `fuel` is existentially quantified because `inflateLoop 0` always
    errors. The fuel bound allows transferring to any concrete fuel value
    via `inflateLoop_fuel_le`.

    This is the reverse of `inflateLoop_correct`. -/
theorem inflateLoop_complete (br : Zip.Native.BitReader)
    (output : ByteArray)
    (fixedLit fixedDist : Zip.Native.HuffTree)
    (maxOutputSize : Nat)
    (result : List UInt8)
    (hwf : br.bitOff < 8)
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (hple : br.pos ≤ br.data.size)
    (hflit : Zip.Native.HuffTree.fromLengths
      Zip.Native.Inflate.fixedLitLengths = .ok fixedLit)
    (hfdist : Zip.Native.HuffTree.fromLengths
      Zip.Native.Inflate.fixedDistLengths = .ok fixedDist)
    (hmax : result.length ≤ maxOutputSize)
    (hspec : Deflate.Spec.decode.go br.toBits output.data.toList =
        some result) :
    ∃ fuel endPos,
      fuel ≤ br.toBits.length + 1 ∧
      Zip.Native.Inflate.inflateLoop br output fixedLit fixedDist
        maxOutputSize fuel = .ok (⟨⟨result⟩⟩, endPos) := by
  -- Strong induction on bit stream length
  suffices ∀ len (br : Zip.Native.BitReader) (output : ByteArray)
      (result : List UInt8),
      br.toBits.length = len →
      br.bitOff < 8 →
      (br.bitOff = 0 ∨ br.pos < br.data.size) →
      br.pos ≤ br.data.size →
      result.length ≤ maxOutputSize →
      Deflate.Spec.decode.go br.toBits output.data.toList = some result →
      ∃ fuel endPos,
        fuel ≤ len + 1 ∧
        Zip.Native.Inflate.inflateLoop br output fixedLit fixedDist
          maxOutputSize fuel = .ok (⟨⟨result⟩⟩, endPos) from
    this _ br output result rfl hwf hpos hple hmax hspec
  intro len
  induction len using Nat.strongRecOn with
  | _ len ih =>
    intro br output result hlen hwf hpos hple hmaxout hspec
    -- Unfold spec one step
    unfold Deflate.Spec.decode.go at hspec
    -- Extract readBitsLSB 1 (bfinal)
    cases hspec_bf : Deflate.Spec.readBitsLSB 1 br.toBits with
    | none => simp [hspec_bf] at hspec
    | some p₁ =>
      obtain ⟨bfinal_val, bits₁⟩ := p₁
      simp only [hspec_bf, bind, Option.bind] at hspec
      have hval_bf := Deflate.Spec.readBitsLSB_bound hspec_bf
      have ⟨br₁, hrb_bf, hrest₁, hwf₁, hpos₁⟩ :=
        readBits_complete br 1 bfinal_val bits₁ hwf hpos (by omega) hval_bf hspec_bf
      have ⟨_, _, hple₁⟩ :=
        Zip.Native.readBits_inv br br₁ 1 bfinal_val.toUInt32 hrb_bf hpos hple
      -- Extract readBitsLSB 2 (btype)
      cases hspec_bt : Deflate.Spec.readBitsLSB 2 bits₁ with
      | none => simp [hspec_bt] at hspec
      | some p₂ =>
        obtain ⟨btype_val, bits₂⟩ := p₂
        simp only [hspec_bt] at hspec
        have hval_bt := Deflate.Spec.readBitsLSB_bound hspec_bt
        have ⟨br₂, hrb_bt, hrest₂, hwf₂, hpos₂⟩ :=
          readBits_complete br₁ 2 btype_val bits₂ hwf₁ hpos₁ (by omega) hval_bt
            (by rw [hrest₁]; exact hspec_bt)
        have ⟨_, _, hple₂⟩ :=
          Zip.Native.readBits_inv br₁ br₂ 2 btype_val.toUInt32 hrb_bt hpos₁ hple₁
        -- Dispatch on btype_val in spec
        split at hspec
        · -- btype_val = 0: stored
          -- Extract decodeStored from spec
          cases hspec_ds : Deflate.Spec.decodeStored bits₂ with
          | none => simp [hspec_ds] at hspec
          | some p₃ =>
            obtain ⟨storedBytes, rest⟩ := p₃
            simp only [hspec_ds] at hspec
            -- Use decodeStored_complete for native
            have hspec_ds' : Deflate.Spec.decodeStored br₂.toBits =
                some (storedBytes, rest) := by rw [hrest₂]; exact hspec_ds
            -- Split on bfinal
            split at hspec
            · -- bfinal_val == 1: final block
              rename_i hbf1
              simp only [pure] at hspec
              have hresult : result = output.data.toList ++ storedBytes := by
                cases hspec; rfl
              have hmax_s : output.size + storedBytes.length ≤ maxOutputSize := by
                rw [hresult, List.length_append] at hmaxout
                simp only [ByteArray.size, Array.length_toList] at *; omega
              obtain ⟨br', hds_nat, _, _, _⟩ := decodeStored_complete br₂ output
                maxOutputSize storedBytes rest hwf₂ hpos₂ hmax_s hspec_ds'
              refine ⟨1, br'.alignToByte.pos, by omega, ?_⟩
              simp only [Zip.Native.Inflate.inflateLoop, bind, Except.bind,
                hrb_bf, hrb_bt, hds_nat,
                show Nat.toUInt32 0 = (0 : UInt32) from rfl]
              -- bfinal check
              have hbf_u32 : (bfinal_val.toUInt32 == 1) = true := by
                rw [beq_iff_eq] at hbf1 ⊢; subst hbf1; rfl
              simp only [hbf_u32, ↓reduceIte, pure, Except.pure]
              -- Goal: .ok (output ++ ⟨⟨storedBytes⟩⟩, br'.alignToByte.pos) =
              --       .ok (⟨⟨result⟩⟩, br'.alignToByte.pos)
              rw [hresult]; rfl
            · -- bfinal_val ≠ 1: recursive case
              rename_i hbf_ne1
              -- Split the dite guard (rest.length < br.toBits.length)
              split at hspec
              · rename_i hrest_lt
                -- hspec : decode.go rest (output.data.toList ++ storedBytes) = some result
                -- Derive hmax_s for decodeStored_complete
                have hpre := Deflate.Spec.decode_go_acc_prefix _ _ _ hspec
                have hmax_s : output.size + storedBytes.length ≤ maxOutputSize := by
                  have := hpre.length_le
                  simp only [List.length_append, ByteArray.size, Array.length_toList] at this ⊢
                  omega
                -- Get native decodeStored result
                obtain ⟨br', hds_nat, hrest_br, hbo_0, hpos_br⟩ :=
                  decodeStored_complete br₂ output maxOutputSize storedBytes rest
                    hwf₂ hpos₂ hmax_s hspec_ds'
                have ⟨_, _, hple_br⟩ :=
                  Zip.Native.decodeStored_inv br₂ br' output _ maxOutputSize hds_nat
                -- Apply IH (rest.length < len)
                have hrest_lt' : rest.length < len := by rw [← hlen]; exact hrest_lt
                have hspec_br : Deflate.Spec.decode.go br'.toBits
                    (output ++ ⟨⟨storedBytes⟩⟩).data.toList = some result := by
                  rw [hrest_br]; exact hspec
                obtain ⟨fuel', endPos, hfuel_le, hloop⟩ :=
                  ih rest.length hrest_lt' br' (output ++ ⟨⟨storedBytes⟩⟩) result
                    (by rw [hrest_br])
                    (by rw [hbo_0]; omega) hpos_br hple_br hmaxout hspec_br
                -- Construct fuel = fuel' + 1
                refine ⟨fuel' + 1, endPos, by omega, ?_⟩
                simp only [Zip.Native.Inflate.inflateLoop, bind, Except.bind,
                  hrb_bf, hrb_bt, hds_nat,
                  show Nat.toUInt32 0 = (0 : UInt32) from rfl]
                have hbf_u32 : (bfinal_val.toUInt32 == 1) = false := by
                  have : bfinal_val = 0 := by simp only [beq_iff_eq] at hbf_ne1; omega
                  subst this; rfl
                simp only [hbf_u32, Bool.false_eq_true, ↓reduceIte]
                exact hloop
              · -- ¬(rest.length < br.toBits.length): spec returns none
                simp at hspec

        · -- btype_val = 1: fixed Huffman
          -- Extract decodeSymbols from spec
          cases hspec_ds : Deflate.Spec.decodeSymbols Deflate.Spec.fixedLitLengths
              Deflate.Spec.fixedDistLengths bits₂ with
          | none => simp [hspec_ds] at hspec
          | some p₃ =>
            obtain ⟨syms, rest⟩ := p₃
            simp only [hspec_ds] at hspec
            -- Extract resolveLZ77 from spec
            cases hspec_lz : Deflate.Spec.resolveLZ77 syms output.data.toList with
            | none => simp [hspec_lz] at hspec
            | some blockResult =>
              simp only [hspec_lz] at hspec
              -- Bridge decodeSymbols to native table names
              have hds_bridge : Deflate.Spec.decodeSymbols
                  (Zip.Native.Inflate.fixedLitLengths.toList.map UInt8.toNat)
                  (Zip.Native.Inflate.fixedDistLengths.toList.map UInt8.toNat)
                  br₂.toBits = some (syms, rest) := by
                rw [Deflate.Correctness.fixedLitLengths_eq,
                    Deflate.Correctness.fixedDistLengths_eq, hrest₂]
                exact hspec_ds
              -- Split on bfinal
              split at hspec
              · -- bfinal_val == 1: final block
                rename_i hbf1
                cases hspec -- substitutes blockResult := result
                obtain ⟨br', hdh, hrest_br, hwf_br, hpos_br⟩ :=
                  decodeHuffman_complete
                    Zip.Native.Inflate.fixedLitLengths Zip.Native.Inflate.fixedDistLengths
                    fixedLit fixedDist maxOutputSize br₂ output syms rest result
                    hwf₂ hpos₂ hflit hfdist
                    (by rw [Deflate.Correctness.fixedLitLengths_eq]
                        exact Deflate.Spec.fixedLitLengths_valid)
                    (by rw [Deflate.Correctness.fixedDistLengths_eq]
                        exact Deflate.Spec.fixedDistLengths_valid)
                    Deflate.Correctness.fixedLitLengths_size
                    Deflate.Correctness.fixedDistLengths_size
                    hmaxout br₂.data.size hple₂ (by omega)
                    hds_bridge hspec_lz
                have hdh_native : Zip.Native.Inflate.decodeHuffman br₂ output
                    fixedLit fixedDist maxOutputSize =
                    .ok (⟨⟨result⟩⟩, br') := by
                  unfold Zip.Native.Inflate.decodeHuffman; exact hdh
                refine ⟨1, br'.alignToByte.pos, by omega, ?_⟩
                simp only [Zip.Native.Inflate.inflateLoop, bind, Except.bind,
                  hrb_bf, hrb_bt, hdh_native,
                  show Nat.toUInt32 1 = (1 : UInt32) from rfl]
                have hbf_u32 : (bfinal_val.toUInt32 == 1) = true := by
                  rw [beq_iff_eq] at hbf1 ⊢; subst hbf1; rfl
                simp only [hbf_u32, ↓reduceIte, pure, Except.pure]
              · -- bfinal_val ≠ 1: recursive case
                rename_i hbf_ne1
                split at hspec
                · rename_i hrest_lt
                  -- Derive hmax for decodeHuffman_complete
                  have hmax_block : blockResult.length ≤ maxOutputSize := by
                    have := (Deflate.Spec.decode_go_acc_prefix _ _ _ hspec).length_le; omega
                  obtain ⟨br', hdh, hrest_br, hwf_br, hpos_br⟩ :=
                    decodeHuffman_complete
                      Zip.Native.Inflate.fixedLitLengths Zip.Native.Inflate.fixedDistLengths
                      fixedLit fixedDist maxOutputSize br₂ output syms rest blockResult
                      hwf₂ hpos₂ hflit hfdist
                      (by rw [Deflate.Correctness.fixedLitLengths_eq]
                          exact Deflate.Spec.fixedLitLengths_valid)
                      (by rw [Deflate.Correctness.fixedDistLengths_eq]
                          exact Deflate.Spec.fixedDistLengths_valid)
                      Deflate.Correctness.fixedLitLengths_size
                      Deflate.Correctness.fixedDistLengths_size
                      hmax_block br₂.data.size hple₂ (by omega)
                      hds_bridge hspec_lz
                  have hdh_native : Zip.Native.Inflate.decodeHuffman br₂ output
                      fixedLit fixedDist maxOutputSize =
                      .ok (⟨⟨blockResult⟩⟩, br') := by
                    unfold Zip.Native.Inflate.decodeHuffman; exact hdh
                  have ⟨_, _, hple_br⟩ :=
                    Zip.Native.decodeHuffman_inv fixedLit fixedDist br₂ br' output
                      ⟨⟨blockResult⟩⟩ maxOutputSize hdh_native hpos₂ hple₂
                  -- Apply IH
                  have hrest_lt' : rest.length < len := by rw [← hlen]; exact hrest_lt
                  have hspec_br : Deflate.Spec.decode.go br'.toBits
                      (⟨⟨blockResult⟩⟩ : ByteArray).data.toList = some result := by
                    rw [hrest_br]; exact hspec
                  obtain ⟨fuel', endPos, hfuel_le, hloop⟩ :=
                    ih rest.length hrest_lt' br' ⟨⟨blockResult⟩⟩ result
                      (by rw [hrest_br]) hwf_br hpos_br hple_br hmaxout hspec_br
                  refine ⟨fuel' + 1, endPos, by omega, ?_⟩
                  simp only [Zip.Native.Inflate.inflateLoop, bind, Except.bind,
                    hrb_bf, hrb_bt, hdh_native,
                    show Nat.toUInt32 1 = (1 : UInt32) from rfl]
                  have hbf_u32 : (bfinal_val.toUInt32 == 1) = false := by
                    have : bfinal_val = 0 := by simp only [beq_iff_eq] at hbf_ne1; omega
                    subst this; rfl
                  simp only [hbf_u32, Bool.false_eq_true, ↓reduceIte]
                  exact hloop
                · simp at hspec
        · -- btype_val = 2: dynamic Huffman
          -- Extract decodeDynamicTables from spec
          cases hspec_dt : Deflate.Spec.decodeDynamicTables bits₂ with
          | none => simp [hspec_dt] at hspec
          | some p₃ =>
            obtain ⟨litLens, distLens, bits₃⟩ := p₃
            simp only [hspec_dt] at hspec
            -- Extract decodeSymbols from spec
            cases hspec_ds : Deflate.Spec.decodeSymbols litLens distLens bits₃ with
            | none => simp [hspec_ds] at hspec
            | some p₄ =>
              obtain ⟨syms, rest⟩ := p₄
              simp only [hspec_ds] at hspec
              -- Extract resolveLZ77 from spec
              cases hspec_lz : Deflate.Spec.resolveLZ77 syms output.data.toList with
              | none => simp [hspec_lz] at hspec
              | some blockResult =>
                simp only [hspec_lz] at hspec
                -- Use decodeDynamicTrees_complete
                have hspec_dt' : Deflate.Spec.decodeDynamicTables br₂.toBits =
                    some (litLens, distLens, bits₃) := by rw [hrest₂]; exact hspec_dt
                obtain ⟨litTree, distTree, br₃, hdt_nat, hrest₃, hwf₃, hpos₃,
                    hvlit, hvdist,
                    litLengths, distLengths, hflit_d, hfdist_d,
                    hlit_map, hdist_map, hlen_lit, hlen_dist⟩ :=
                  Deflate.Correctness.decodeDynamicTrees_complete br₂ litLens distLens bits₃
                    hwf₂ hpos₂ hspec_dt'
                have ⟨hdata₃, _, hple₃⟩ :=
                  Zip.Native.decodeDynamicTrees_inv br₂ br₃ litTree distTree
                    hdt_nat hpos₂ hple₂
                -- Bridge decodeSymbols to native table names
                have hds_bridge : Deflate.Spec.decodeSymbols
                    (litLengths.toList.map UInt8.toNat)
                    (distLengths.toList.map UInt8.toNat)
                    br₃.toBits = some (syms, rest) := by
                  rw [hlit_map, hdist_map, hrest₃]
                  exact hspec_ds
                -- Split on bfinal
                split at hspec
                · -- bfinal_val == 1: final block
                  rename_i hbf1
                  cases hspec -- substitutes blockResult := result
                  obtain ⟨br', hdh, hrest_br, hwf_br, hpos_br⟩ :=
                    decodeHuffman_complete
                      litLengths distLengths
                      litTree distTree maxOutputSize br₃ output syms rest result
                      hwf₃ hpos₃ hflit_d hfdist_d
                      (by rw [hlit_map]; exact hvlit)
                      (by rw [hdist_map]; exact hvdist)
                      hlen_lit hlen_dist
                      hmaxout br₃.data.size hple₃ (by omega)
                      hds_bridge hspec_lz
                  have hdh_native : Zip.Native.Inflate.decodeHuffman br₃ output
                      litTree distTree maxOutputSize =
                      .ok (⟨⟨result⟩⟩, br') := by
                    unfold Zip.Native.Inflate.decodeHuffman; exact hdh
                  refine ⟨1, br'.alignToByte.pos, by omega, ?_⟩
                  simp only [Zip.Native.Inflate.inflateLoop, bind, Except.bind,
                    hrb_bf, hrb_bt, hdt_nat, hdh_native,
                    show Nat.toUInt32 2 = (2 : UInt32) from rfl]
                  have hbf_u32 : (bfinal_val.toUInt32 == 1) = true := by
                    rw [beq_iff_eq] at hbf1 ⊢; subst hbf1; rfl
                  simp only [hbf_u32, ↓reduceIte, pure, Except.pure]
                · -- bfinal_val ≠ 1: recursive case
                  rename_i hbf_ne1
                  split at hspec
                  · rename_i hrest_lt
                    have hmax_block : blockResult.length ≤ maxOutputSize := by
                      have := (Deflate.Spec.decode_go_acc_prefix _ _ _ hspec).length_le
                      omega
                    obtain ⟨br', hdh, hrest_br, hwf_br, hpos_br⟩ :=
                      decodeHuffman_complete
                        litLengths distLengths
                        litTree distTree maxOutputSize br₃ output syms rest blockResult
                        hwf₃ hpos₃ hflit_d hfdist_d
                        (by rw [hlit_map]; exact hvlit)
                        (by rw [hdist_map]; exact hvdist)
                        hlen_lit hlen_dist
                        hmax_block br₃.data.size hple₃ (by omega)
                        hds_bridge hspec_lz
                    have hdh_native : Zip.Native.Inflate.decodeHuffman br₃ output
                        litTree distTree maxOutputSize =
                        .ok (⟨⟨blockResult⟩⟩, br') := by
                      unfold Zip.Native.Inflate.decodeHuffman; exact hdh
                    have ⟨_, _, hple_br⟩ :=
                      Zip.Native.decodeHuffman_inv litTree distTree br₃ br' output
                        ⟨⟨blockResult⟩⟩ maxOutputSize hdh_native hpos₃ hple₃
                    -- Apply IH
                    have hrest_lt' : rest.length < len := by rw [← hlen]; exact hrest_lt
                    have hspec_br : Deflate.Spec.decode.go br'.toBits
                        (⟨⟨blockResult⟩⟩ : ByteArray).data.toList = some result := by
                      rw [hrest_br]; exact hspec
                    obtain ⟨fuel', endPos, hfuel_le, hloop⟩ :=
                      ih rest.length hrest_lt' br' ⟨⟨blockResult⟩⟩ result
                        (by rw [hrest_br]) hwf_br hpos_br hple_br hmaxout hspec_br
                    refine ⟨fuel' + 1, endPos, by omega, ?_⟩
                    simp only [Zip.Native.Inflate.inflateLoop, bind, Except.bind,
                      hrb_bf, hrb_bt, hdt_nat, hdh_native,
                      show Nat.toUInt32 2 = (2 : UInt32) from rfl]
                    have hbf_u32 : (bfinal_val.toUInt32 == 1) = false := by
                      have : bfinal_val = 0 := by simp only [beq_iff_eq] at hbf_ne1; omega
                      subst this; rfl
                    simp only [hbf_u32, Bool.false_eq_true, ↓reduceIte]
                    exact hloop
                  · simp at hspec
        · -- btype_val ≥ 3: reserved
          simp at hspec

end Deflate.Correctness
