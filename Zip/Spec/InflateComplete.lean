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
  exact List.map_id _

/-- Nat→UInt8→Nat roundtrip for lists with elements bounded by `maxBits ≤ 15`. -/
theorem validLengths_toUInt8_roundtrip (lens : List Nat)
    (hv : Huffman.Spec.ValidLengths lens maxBits) (hmb : maxBits ≤ 15) :
    (lens.map Nat.toUInt8).toArray.toList.map UInt8.toNat = lens := by
  simp only [List.map_map]
  rw [List.map_congr_left (fun n hn => by
    show (Nat.toUInt8 n).toNat = n
    simp only [Nat.toUInt8, UInt8.toNat, UInt8.ofNat, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by have := hv.1 n hn; omega))]
  exact List.map_id _

/-! ## WF guard helpers -/

/-- If `br'` has fewer remaining bits than `br` (same underlying data),
    then `br'` is strictly ahead: `br'.bitPos > br.bitPos`. -/
private theorem wf_progress_of_toBits_lt {br br' : ZipCommon.BitReader}
    (hple : br.pos ≤ br.data.size)
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (_hple' : br'.pos ≤ br'.data.size)
    (hpos' : br'.bitOff = 0 ∨ br'.pos < br'.data.size)
    (hdata : br'.data = br.data)
    (hlt : br'.toBits.length < br.toBits.length) :
    ¬(br'.bitPos ≤ br.bitPos) := by
  have htl := Deflate.Correctness.toBits_length br
  have htl' := Deflate.Correctness.toBits_length br'
  rw [hdata] at htl'
  simp only [ZipCommon.BitReader.bitPos] at *
  rcases hpos with h | h <;> rcases hpos' with h' | h' <;> omega

/-- If `br.data.size ≤ dataSize` and `br` is within bounds,
    then `br.bitPos ≤ dataSize * 8`. -/
private theorem wf_range_of_data_le {br : ZipCommon.BitReader} {dataSize : Nat}
    (hwf : br.bitOff < 8)
    (hple : br.pos ≤ br.data.size)
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (hds : br.data.size ≤ dataSize) :
    ¬(dataSize * 8 < br.bitPos) := by
  simp only [ZipCommon.BitReader.bitPos]
  rcases hpos with h | h <;> omega

/-! ## DataSize monotonicity -/

-- Shared tail tactic for `inflateLoop_fuel_le`. After the block-decode
-- `split at h`, handles the bfinal check and WF guards. Captures `h`
-- and `ih` from the enclosing proof context.
set_option hygiene false in
local macro "inflateLoop_fuel_le_ok_case" : tactic => `(tactic| (
  split at h <;> split
  next => exact h
  next h1 h2 => exact absurd h1 h2
  next h1 h2 => exact absurd h2 h1
  next =>
    split at h
    next => exact nomatch h
    next h_progress =>
      split at h
      next => exact nomatch h
      next h_range_n =>
        split
        next h_prog_m => exact absurd h_prog_m h_progress
        next =>
          split
          next h_range_m => exfalso; omega
          next => exact ih _ (by omega) _ _ _ Nat.le.refl h))

/-- DataSize monotonicity: if `inflateLoop` succeeds with dataSize `n`,
    it succeeds with any `m ≥ n` and produces the same result.
    (The only effect of a larger dataSize is a more permissive range guard.) -/
theorem inflateLoop_fuel_le
    (br : ZipCommon.BitReader) (output : ByteArray)
    (fixedLit fixedDist : Zip.Native.HuffTree) (maxOut n m : Nat)
    (x : ByteArray × Nat)
    (h : Zip.Native.Inflate.inflateLoop br output fixedLit fixedDist maxOut n = .ok x)
    (hle : n ≤ m) :
    Zip.Native.Inflate.inflateLoop br output fixedLit fixedDist maxOut m = .ok x := by
  -- Strong induction on WF measure: n * 8 - br.bitPos
  suffices ∀ k (br : ZipCommon.BitReader) (output : ByteArray) (x : ByteArray × Nat),
      n * 8 - br.bitPos ≤ k →
      Zip.Native.Inflate.inflateLoop br output fixedLit fixedDist maxOut n = .ok x →
      Zip.Native.Inflate.inflateLoop br output fixedLit fixedDist maxOut m = .ok x from
    this (n * 8 - br.bitPos) br output x (Nat.le.refl) h
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro br output x hk h
    rw [Zip.Native.Inflate.inflateLoop.eq_1] at h
    rw [Zip.Native.Inflate.inflateLoop.eq_1]
    simp only [bind, Except.bind] at h ⊢
    -- readBits 1
    cases hbf : br.readBits 1 with
    | error e => exact nomatch (hbf ▸ h)
    | ok p₁ =>
      obtain ⟨bfinal, br₁⟩ := p₁; simp only [hbf] at h ⊢
      -- readBits 2
      cases hbt : br₁.readBits 2 with
      | error e => exact nomatch (hbt ▸ h)
      | ok p₂ =>
        obtain ⟨btype, br₂⟩ := p₂; simp only [hbt] at h ⊢
        -- Both h and ⊢ match on btype; only dataSize differs (n vs m)
        split at h
        · -- btype = 0: stored
          split at h
          · exact h -- error case
          · inflateLoop_fuel_le_ok_case
        · -- btype = 1: fixed Huffman
          split at h
          · exact h
          · inflateLoop_fuel_le_ok_case
        · -- btype = 2: dynamic Huffman
          split at h
          · exact h -- decodeDynamicTrees error
          · split at h
            · exact h -- decodeHuffman error
            · inflateLoop_fuel_le_ok_case
        · exact h -- btype ≥ 3: reserved error

/-! ## Block loop completeness -/

set_option maxRecDepth 2048 in
/-- **Completeness for block loop**: if the spec `decode.go` succeeds,
    the native `inflateLoop` also succeeds with the same result.

    The `dataSize` parameter must be at least `br.data.size`. The caller
    can use `inflateLoop_fuel_le` to lift to any larger dataSize.

    This is the reverse of `inflateLoop_correct`. -/
theorem inflateLoop_complete (br : ZipCommon.BitReader)
    (output : ByteArray)
    (fixedLit fixedDist : Zip.Native.HuffTree)
    (maxOutputSize dataSize : Nat)
    (result : List UInt8)
    (hwf : br.bitOff < 8)
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (hple : br.pos ≤ br.data.size)
    (hds : br.data.size ≤ dataSize)
    (hflit : Zip.Native.HuffTree.fromLengths
      Zip.Native.Inflate.fixedLitLengths = .ok fixedLit)
    (hfdist : Zip.Native.HuffTree.fromLengths
      Zip.Native.Inflate.fixedDistLengths = .ok fixedDist)
    (hmax : result.length ≤ maxOutputSize)
    (hspec : Deflate.Spec.decode.go br.toBits output.data.toList =
        some result) :
    ∃ endPos,
      Zip.Native.Inflate.inflateLoop br output fixedLit fixedDist
        maxOutputSize dataSize = .ok (⟨⟨result⟩⟩, endPos) := by
  -- Strong induction on bit stream length
  suffices ∀ len (br : ZipCommon.BitReader) (output : ByteArray)
      (result : List UInt8),
      br.toBits.length = len →
      br.bitOff < 8 →
      (br.bitOff = 0 ∨ br.pos < br.data.size) →
      br.pos ≤ br.data.size →
      br.data.size ≤ dataSize →
      result.length ≤ maxOutputSize →
      Deflate.Spec.decode.go br.toBits output.data.toList = some result →
      ∃ endPos,
        Zip.Native.Inflate.inflateLoop br output fixedLit fixedDist
          maxOutputSize dataSize = .ok (⟨⟨result⟩⟩, endPos) from
    this _ br output result rfl hwf hpos hple hds hmax hspec
  intro len
  induction len using Nat.strongRecOn with
  | _ len ih =>
    intro br output result hlen hwf hpos hple hds hmaxout hspec
    -- Unfold spec one step
    unfold Deflate.Spec.decode.go at hspec
    -- Extract readBitsLSB 1 (bfinal)
    cases hspec_bf : Deflate.Spec.readBitsLSB 1 br.toBits with
    | none => exact nomatch (hspec_bf ▸ hspec)
    | some p₁ =>
      obtain ⟨bfinal_val, bits₁⟩ := p₁
      simp only [hspec_bf, bind, Option.bind] at hspec
      have hval_bf := Deflate.Spec.readBitsLSB_bound hspec_bf
      have ⟨br₁, hrb_bf, hrest₁, hwf₁, hpos₁⟩ :=
        readBits_complete br 1 bfinal_val bits₁ hwf hpos (by omega) hval_bf hspec_bf
      have ⟨hdata₁, _, hple₁⟩ :=
        ZipCommon.readBits_inv br br₁ 1 bfinal_val.toUInt32 hrb_bf hpos hple
      -- Extract readBitsLSB 2 (btype)
      cases hspec_bt : Deflate.Spec.readBitsLSB 2 bits₁ with
      | none => exact nomatch (hspec_bt ▸ hspec)
      | some p₂ =>
        obtain ⟨btype_val, bits₂⟩ := p₂
        simp only [hspec_bt] at hspec
        have hval_bt := Deflate.Spec.readBitsLSB_bound hspec_bt
        have ⟨br₂, hrb_bt, hrest₂, hwf₂, hpos₂⟩ :=
          readBits_complete br₁ 2 btype_val bits₂ hwf₁ hpos₁ (by omega) hval_bt
            (by rw [hrest₁]; exact hspec_bt)
        have ⟨hdata₂, _, hple₂⟩ :=
          ZipCommon.readBits_inv br₁ br₂ 2 btype_val.toUInt32 hrb_bt hpos₁ hple₁
        -- Dispatch on btype_val in spec
        split at hspec
        · -- btype_val = 0: stored
          -- Extract decodeStored from spec
          cases hspec_ds : Deflate.Spec.decodeStored bits₂ with
          | none => exact nomatch (hspec_ds ▸ hspec)
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
              refine ⟨br'.alignToByte.pos, ?_⟩
              rw [Zip.Native.Inflate.inflateLoop.eq_1]
              simp only [bind, Except.bind,
                hrb_bf, hrb_bt, hds_nat,
                show Nat.toUInt32 0 = (0 : UInt32) from rfl]
              -- bfinal check
              have hbf_u32 := Deflate.Correctness.nat_beq_to_uint32_true bfinal_val hval_bf hbf1
              simp only [hbf_u32, ↓reduceIte, pure, Except.pure]
              rw [hresult]; rfl
            · -- bfinal_val ≠ 1: recursive case
              rename_i hbf_ne1
              -- Split the dite guard (rest.length < br.toBits.length)
              split at hspec
              · rename_i hrest_lt
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
                have ⟨hdata_ds, _, hple_br⟩ :=
                  Zip.Native.decodeStored_inv br₂ br' output _ maxOutputSize hds_nat
                -- Data preservation chain
                have hdata_chain : br'.data = br.data :=
                  hdata_ds.trans (hdata₂.trans hdata₁)
                have hds_br : br'.data.size ≤ dataSize := by
                  rw [hdata_chain]; exact hds
                -- Apply IH (rest.length < len)
                have hrest_lt' : rest.length < len := by rw [← hlen]; exact hrest_lt
                have hspec_br : Deflate.Spec.decode.go br'.toBits
                    (output ++ ⟨⟨storedBytes⟩⟩).data.toList = some result := by
                  rw [hrest_br]; exact hspec
                obtain ⟨endPos, hloop⟩ :=
                  ih rest.length hrest_lt' br' (output ++ ⟨⟨storedBytes⟩⟩) result
                    (by rw [hrest_br])
                    (by rw [hbo_0]; omega) hpos_br hple_br hds_br hmaxout hspec_br
                -- Construct native result
                refine ⟨endPos, ?_⟩
                rw [Zip.Native.Inflate.inflateLoop.eq_1]
                simp only [bind, Except.bind,
                  hrb_bf, hrb_bt, hds_nat,
                  show Nat.toUInt32 0 = (0 : UInt32) from rfl]
                have hbf_u32 := Deflate.Correctness.nat_beq_to_uint32_eq_false
                  bfinal_val hval_bf hbf_ne1
                simp only [hbf_u32, Bool.false_eq_true, ↓reduceIte]
                -- Discharge WF guards
                split
                · rename_i h_prog
                  exact absurd h_prog (wf_progress_of_toBits_lt hple hpos hple_br hpos_br
                    hdata_chain (by rw [hrest_br]; exact hrest_lt))
                · split
                  · rename_i h_rng
                    exact absurd h_rng (wf_range_of_data_le (by rw [hbo_0]; omega) hple_br hpos_br hds_br)
                  · exact hloop
              · -- ¬(rest.length < br.toBits.length): spec returns none
                exact nomatch hspec

        · -- btype_val = 1: fixed Huffman
          -- Extract decodeSymbols from spec
          cases hspec_ds : Deflate.Spec.decodeSymbols Deflate.Spec.fixedLitLengths
              Deflate.Spec.fixedDistLengths bits₂ with
          | none => exact nomatch (hspec_ds ▸ hspec)
          | some p₃ =>
            obtain ⟨syms, rest⟩ := p₃
            simp only [hspec_ds] at hspec
            -- Extract resolveLZ77 from spec
            cases hspec_lz : Deflate.Spec.resolveLZ77 syms output.data.toList with
            | none => exact nomatch (hspec_lz ▸ hspec)
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
                refine ⟨br'.alignToByte.pos, ?_⟩
                rw [Zip.Native.Inflate.inflateLoop.eq_1]
                simp only [bind, Except.bind,
                  hrb_bf, hrb_bt, hdh_native,
                  show Nat.toUInt32 1 = (1 : UInt32) from rfl]
                have hbf_u32 := Deflate.Correctness.nat_beq_to_uint32_true bfinal_val hval_bf hbf1
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
                  have ⟨hdata_dh, _, hple_br⟩ :=
                    Zip.Native.decodeHuffman_inv fixedLit fixedDist br₂ br' output
                      ⟨⟨blockResult⟩⟩ maxOutputSize hdh_native hpos₂ hple₂
                  -- Data preservation chain
                  have hdata_chain : br'.data = br.data :=
                    hdata_dh.trans (hdata₂.trans hdata₁)
                  have hds_br : br'.data.size ≤ dataSize := by
                    rw [hdata_chain]; exact hds
                  -- Apply IH
                  have hrest_lt' : rest.length < len := by rw [← hlen]; exact hrest_lt
                  have hspec_br : Deflate.Spec.decode.go br'.toBits
                      (⟨⟨blockResult⟩⟩ : ByteArray).data.toList = some result := by
                    rw [hrest_br]; exact hspec
                  obtain ⟨endPos, hloop⟩ :=
                    ih rest.length hrest_lt' br' ⟨⟨blockResult⟩⟩ result
                      (by rw [hrest_br]) hwf_br hpos_br hple_br hds_br hmaxout hspec_br
                  refine ⟨endPos, ?_⟩
                  rw [Zip.Native.Inflate.inflateLoop.eq_1]
                  simp only [bind, Except.bind,
                    hrb_bf, hrb_bt, hdh_native,
                    show Nat.toUInt32 1 = (1 : UInt32) from rfl]
                  have hbf_u32 := Deflate.Correctness.nat_beq_to_uint32_eq_false
                    bfinal_val hval_bf hbf_ne1
                  simp only [hbf_u32, Bool.false_eq_true, ↓reduceIte]
                  -- Discharge WF guards
                  split
                  · rename_i h_prog
                    exact absurd h_prog (wf_progress_of_toBits_lt hple hpos hple_br hpos_br
                      hdata_chain (by rw [hrest_br]; exact hrest_lt))
                  · split
                    · rename_i h_rng
                      exact absurd h_rng (wf_range_of_data_le hwf_br hple_br hpos_br hds_br)
                    · exact hloop
                · exact nomatch hspec
        · -- btype_val = 2: dynamic Huffman
          -- Extract decodeDynamicTables from spec
          cases hspec_dt : Deflate.Spec.decodeDynamicTables bits₂ with
          | none => exact nomatch (hspec_dt ▸ hspec)
          | some p₃ =>
            obtain ⟨litLens, distLens, bits₃⟩ := p₃
            simp only [hspec_dt] at hspec
            -- Extract decodeSymbols from spec
            cases hspec_ds : Deflate.Spec.decodeSymbols litLens distLens bits₃ with
            | none => exact nomatch (hspec_ds ▸ hspec)
            | some p₄ =>
              obtain ⟨syms, rest⟩ := p₄
              simp only [hspec_ds] at hspec
              -- Extract resolveLZ77 from spec
              cases hspec_lz : Deflate.Spec.resolveLZ77 syms output.data.toList with
              | none => exact nomatch (hspec_lz ▸ hspec)
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
                  refine ⟨br'.alignToByte.pos, ?_⟩
                  rw [Zip.Native.Inflate.inflateLoop.eq_1]
                  simp only [bind, Except.bind,
                    hrb_bf, hrb_bt, hdt_nat, hdh_native,
                    show Nat.toUInt32 2 = (2 : UInt32) from rfl]
                  have hbf_u32 := Deflate.Correctness.nat_beq_to_uint32_true bfinal_val hval_bf hbf1
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
                    have ⟨hdata_dh, _, hple_br⟩ :=
                      Zip.Native.decodeHuffman_inv litTree distTree br₃ br' output
                        ⟨⟨blockResult⟩⟩ maxOutputSize hdh_native hpos₃ hple₃
                    -- Data preservation chain
                    have hdata_chain : br'.data = br.data :=
                      hdata_dh.trans (hdata₃.trans (hdata₂.trans hdata₁))
                    have hds_br : br'.data.size ≤ dataSize := by
                      rw [hdata_chain]; exact hds
                    -- Apply IH
                    have hrest_lt' : rest.length < len := by rw [← hlen]; exact hrest_lt
                    have hspec_br : Deflate.Spec.decode.go br'.toBits
                        (⟨⟨blockResult⟩⟩ : ByteArray).data.toList = some result := by
                      rw [hrest_br]; exact hspec
                    obtain ⟨endPos, hloop⟩ :=
                      ih rest.length hrest_lt' br' ⟨⟨blockResult⟩⟩ result
                        (by rw [hrest_br]) hwf_br hpos_br hple_br hds_br hmaxout hspec_br
                    refine ⟨endPos, ?_⟩
                    rw [Zip.Native.Inflate.inflateLoop.eq_1]
                    simp only [bind, Except.bind,
                      hrb_bf, hrb_bt, hdt_nat, hdh_native,
                      show Nat.toUInt32 2 = (2 : UInt32) from rfl]
                    have hbf_u32 := Deflate.Correctness.nat_beq_to_uint32_eq_false
                      bfinal_val hval_bf hbf_ne1
                    simp only [hbf_u32, Bool.false_eq_true, ↓reduceIte]
                    -- Discharge WF guards
                    split
                    · rename_i h_prog
                      exact absurd h_prog (wf_progress_of_toBits_lt hple hpos hple_br hpos_br
                        hdata_chain (by rw [hrest_br]; exact hrest_lt))
                    · split
                      · rename_i h_rng
                        exact absurd h_rng (wf_range_of_data_le hwf_br hple_br hpos_br hds_br)
                      · exact hloop
                  · exact nomatch hspec
        · -- btype_val ≥ 3: reserved
          exact nomatch hspec

end Deflate.Correctness
