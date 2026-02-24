import Zip.Spec.DynamicTreesComplete

/-!
# DEFLATE Stream-Level Correctness

Proves the main correctness theorem: the native pure-Lean DEFLATE
decompressor (`Zip.Native.Inflate.inflateRaw`) agrees with the formal
bitstream specification (`Deflate.Spec.decode`).

This file handles the block loop (`inflateLoop_correct`) and the
top-level `inflate_correct` / `inflate_correct'` wrappers. Block-level
decode proofs (stored, Huffman) are in `DecodeCorrect`; dynamic tree
proofs are in `DynamicTreesCorrect`.
-/

namespace Deflate.Correctness

/-! ## Block loop helpers -/

/-- `decodeStored` preserves `bitOff < 8` and the position invariant. -/
private theorem decodeStored_invariants (br : Zip.Native.BitReader) (output : ByteArray)
    (maxOutputSize : Nat) (output' : ByteArray) (br' : Zip.Native.BitReader)
    (h : Zip.Native.Inflate.decodeStored br output maxOutputSize = .ok (output', br')) :
    br'.bitOff < 8 ∧ (br'.bitOff = 0 ∨ br'.pos < br'.data.size) := by
  simp only [Zip.Native.Inflate.decodeStored, bind, Except.bind] at h
  cases h₁ : br.readUInt16LE with
  | error e => simp [h₁] at h
  | ok p₁ =>
    obtain ⟨len, br₁⟩ := p₁; simp only [h₁] at h
    cases h₂ : br₁.readUInt16LE with
    | error e => simp [h₂] at h
    | ok p₂ =>
      obtain ⟨nlen, br₂⟩ := p₂; simp only [h₂] at h
      split at h
      · simp at h
      · simp only [pure, Except.pure] at h
        split at h
        · simp at h
        · cases h₃ : br₂.readBytes len.toNat with
          | error e => simp [h₃] at h
          | ok p₃ =>
            obtain ⟨bytes, br₃⟩ := p₃
            simp only [h₃, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨_, rfl⟩ := h
            have hwf := readBytes_wf br₂ len.toNat bytes br₃ h₃
            exact ⟨by omega, Or.inl hwf⟩

/-! ## Fixed code length correspondence -/

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem fixedLitLengths_eq :
    (Zip.Native.Inflate.fixedLitLengths).toList.map UInt8.toNat =
    Deflate.Spec.fixedLitLengths := by rfl

set_option maxRecDepth 2048 in
private theorem fixedDistLengths_eq :
    (Zip.Native.Inflate.fixedDistLengths).toList.map UInt8.toNat =
    Deflate.Spec.fixedDistLengths := by decide

set_option maxRecDepth 4096 in
private theorem fixedLitLengths_size :
    Zip.Native.Inflate.fixedLitLengths.size ≤ UInt16.size := by
  show 288 ≤ 65536; omega

private theorem fixedDistLengths_size :
    Zip.Native.Inflate.fixedDistLengths.size ≤ UInt16.size := by decide

/-! ## Main correctness theorem -/

/-- Bridge: `(bfinal == 1) = true` (UInt32) implies `(bfinal.toNat == 1) = true` (Nat). -/
private theorem bfinal_beq_nat_true (bfinal : UInt32) (h : (bfinal == 1) = true) :
    (bfinal.toNat == 1) = true := by
  rw [beq_iff_eq] at h ⊢; exact congrArg UInt32.toNat h

/-- Bridge: `¬((bfinal == 1) = true)` (UInt32) implies `(bfinal.toNat == 1) = false`. -/
private theorem bfinal_beq_nat_false (bfinal : UInt32) (h : ¬((bfinal == 1) = true)) :
    (bfinal.toNat == 1) = false := by
  cases heq : bfinal.toNat == 1 <;> simp_all [← UInt32.toNat_inj]

set_option maxRecDepth 4096 in
/-- Block loop correspondence: the native `inflateLoop` agrees with
    the spec's `decode.go` on a block-by-block basis. -/
theorem inflateLoop_correct (br : Zip.Native.BitReader)
    (output : ByteArray)
    (fixedLit fixedDist : Zip.Native.HuffTree)
    (maxOutputSize fuel : Nat)
    (result : ByteArray) (endPos : Nat)
    (hwf : br.bitOff < 8)
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (hflit : Zip.Native.HuffTree.fromLengths
      Zip.Native.Inflate.fixedLitLengths = .ok fixedLit)
    (hfdist : Zip.Native.HuffTree.fromLengths
      Zip.Native.Inflate.fixedDistLengths = .ok fixedDist)
    (h : Zip.Native.Inflate.inflateLoop br output fixedLit fixedDist
      maxOutputSize fuel = .ok (result, endPos)) :
    ∃ specFuel,
      Deflate.Spec.decode.go br.toBits output.data.toList specFuel =
        some result.data.toList := by
  induction fuel generalizing br output with
  | zero =>
    unfold Zip.Native.Inflate.inflateLoop at h; simp at h
  | succ n ih =>
    unfold Zip.Native.Inflate.inflateLoop at h
    simp only [bind, Except.bind] at h
    -- readBits 1 (bfinal)
    cases hbf : br.readBits 1 with
    | error e => simp [hbf] at h
    | ok p =>
      obtain ⟨bfinal, br₁⟩ := p
      simp only [hbf] at h
      -- readBits 2 (btype)
      cases hbt : br₁.readBits 2 with
      | error e => simp [hbt] at h
      | ok p =>
        obtain ⟨btype, br₂⟩ := p
        simp only [hbt] at h
        -- Well-formedness chain
        have hwf₁ := readBits_wf br 1 bfinal br₁ hwf hbf
        have hwf₂ := readBits_wf br₁ 2 btype br₂ hwf₁ hbt
        have hpos₁ := readBits_pos_inv br 1 bfinal br₁ hwf hpos hbf
        have hpos₂ := readBits_pos_inv br₁ 2 btype br₂ hwf₁ hpos₁ hbt
        -- Spec-level readBitsLSB
        obtain ⟨rest₁, hspec_bf, hrest₁⟩ :=
          readBits_toBits br 1 bfinal br₁ hwf (by omega) hbf
        obtain ⟨rest₂, hspec_bt, hrest₂⟩ :=
          readBits_toBits br₁ 2 btype br₂ hwf₁ (by omega) hbt
        -- Case split on btype (0, 1, 2, or invalid).
        -- We use `by_cases + subst` so that btype is substituted everywhere,
        -- making (n : UInt32).toNat reduce definitionally on the spec side.
        by_cases hbt0 : btype = 0
        · -- btype = 0: stored block
          subst hbt0
          have hspec_bt' : Spec.readBitsLSB 2 br₁.toBits = some (0, rest₂) := hspec_bt
          cases hst : Zip.Native.Inflate.decodeStored br₂ output maxOutputSize with
          | error e => simp [hst] at h
          | ok p =>
            obtain ⟨output', br'⟩ := p
            simp only [hst] at h
            obtain ⟨storedBytes, rest₃, hspec_st, hout_eq, hrest₃⟩ :=
              decodeStored_correct br₂ output maxOutputSize output' br'
                hwf₂ hpos₂ hst
            obtain ⟨hwf', hpos'⟩ := decodeStored_invariants br₂ output maxOutputSize output' br' hst
            split at h
            · -- bfinal == 1: final block
              rename_i hbf1
              obtain ⟨rfl, _⟩ := Except.ok.inj h
              refine ⟨1, ?_⟩
              simp only [Deflate.Spec.decode.go, bind, Option.bind,
                hspec_bf, hspec_bt', ← hrest₁, ← hrest₂,
                hspec_st, hout_eq, pure, bfinal_beq_nat_true bfinal hbf1, ↓reduceIte]
            · -- bfinal ≠ 1: continue
              rename_i hbf1
              obtain ⟨sf, hgo⟩ := ih br' output' hwf' hpos' h
              refine ⟨sf + 1, ?_⟩
              simp only [Deflate.Spec.decode.go, bind, Option.bind,
                hspec_bf, hspec_bt', ← hrest₁, ← hrest₂,
                hspec_st, ← hout_eq, pure,
                bfinal_beq_nat_false bfinal hbf1]
              rw [← hrest₃]
              exact hgo
        · by_cases hbt1 : btype = 1
          · -- btype = 1: fixed Huffman
            subst hbt1
            have hspec_bt' : Spec.readBitsLSB 2 br₁.toBits = some (1, rest₂) := hspec_bt
            cases hhf : Zip.Native.Inflate.decodeHuffman br₂ output fixedLit
                fixedDist maxOutputSize with
            | error e => simp [hhf] at h
            | ok p =>
              obtain ⟨output', br'⟩ := p
              simp only [hhf] at h
              have hhf_go : Zip.Native.Inflate.decodeHuffman.go fixedLit fixedDist
                  maxOutputSize br₂ output 10000000 = .ok (output', br') := by
                simp only [Zip.Native.Inflate.decodeHuffman] at hhf; exact hhf
              obtain ⟨syms, rest_h, hds, hlz, hbr'_eq, hwf', hpos'⟩ :=
                decodeHuffman_correct
                  Zip.Native.Inflate.fixedLitLengths
                  Zip.Native.Inflate.fixedDistLengths
                  fixedLit fixedDist maxOutputSize 10000000
                  br₂ output output' br' hwf₂ hpos₂
                  hflit hfdist
                  (fixedLitLengths_eq ▸ Deflate.Spec.fixedLitLengths_valid)
                  (fixedDistLengths_eq ▸ Deflate.Spec.fixedDistLengths_valid)
                  fixedLitLengths_size fixedDistLengths_size
                  hhf_go
              split at h
              · -- bfinal == 1: final block
                rename_i hbf1
                obtain ⟨rfl, _⟩ := Except.ok.inj h
                refine ⟨1, ?_⟩
                simp only [Deflate.Spec.decode.go, bind, Option.bind,
                  hspec_bf, hspec_bt', ← hrest₁, ← hrest₂,
                  ← fixedLitLengths_eq, ← fixedDistLengths_eq,
                  hds, hlz, pure, bfinal_beq_nat_true bfinal hbf1, ↓reduceIte]
              · -- bfinal ≠ 1: continue
                rename_i hbf1
                obtain ⟨sf, hgo⟩ := ih br' output' hwf' hpos' h
                refine ⟨sf + 1, ?_⟩
                simp only [Deflate.Spec.decode.go, bind, Option.bind,
                  hspec_bf, hspec_bt', ← hrest₁, ← hrest₂,
                  ← fixedLitLengths_eq, ← fixedDistLengths_eq,
                  hds, hlz, pure, bfinal_beq_nat_false bfinal hbf1]
                rw [← hbr'_eq]
                exact hgo
          · by_cases hbt2 : btype = 2
            · -- btype = 2: dynamic Huffman
              subst hbt2
              have hspec_bt' : Spec.readBitsLSB 2 br₁.toBits = some (2, rest₂) := hspec_bt
              cases hdt : Zip.Native.Inflate.decodeDynamicTrees br₂ with
              | error e => simp [hdt] at h
              | ok p =>
                obtain ⟨litTree, distTree, br₃⟩ := p
                simp only [hdt] at h
                obtain ⟨litLens, distLens, rest_dt, hspec_dt, hrest_dt, hwf₃,
                  hpos₃, hflit_dyn, hfdist_dyn, hvlit_dyn, hvdist_dyn,
                  hsize_lit, hsize_dist⟩ :=
                  Correctness.decodeDynamicTrees_correct br₂ litTree distTree br₃ hwf₂ hpos₂ hdt
                cases hhf : Zip.Native.Inflate.decodeHuffman br₃ output litTree
                    distTree maxOutputSize with
                | error e => simp [hhf] at h
                | ok p =>
                  obtain ⟨output', br'⟩ := p
                  simp only [hhf] at h
                  have hhf_go : Zip.Native.Inflate.decodeHuffman.go litTree distTree
                      maxOutputSize br₃ output 10000000 = .ok (output', br') := by
                    simp only [Zip.Native.Inflate.decodeHuffman] at hhf; exact hhf
                  obtain ⟨syms, rest_h, hds, hlz, hbr'_eq, hwf', hpos'⟩ :=
                    decodeHuffman_correct litLens distLens litTree distTree
                      maxOutputSize 10000000 br₃ output output' br' hwf₃ hpos₃
                      hflit_dyn hfdist_dyn hvlit_dyn hvdist_dyn
                      hsize_lit hsize_dist hhf_go
                  split at h
                  · -- bfinal == 1: final block
                    rename_i hbf1
                    obtain ⟨rfl, _⟩ := Except.ok.inj h
                    refine ⟨1, ?_⟩
                    simp only [Deflate.Spec.decode.go, bind, Option.bind,
                      hspec_bf, hspec_bt', ← hrest₁, ← hrest₂,
                      hspec_dt, ← hrest_dt, hds, hlz, pure,
                      bfinal_beq_nat_true bfinal hbf1, ↓reduceIte]
                  · -- bfinal ≠ 1: continue
                    rename_i hbf1
                    obtain ⟨sf, hgo⟩ := ih br' output' hwf' hpos' h
                    refine ⟨sf + 1, ?_⟩
                    simp only [Deflate.Spec.decode.go, bind, Option.bind,
                      hspec_bf, hspec_bt', ← hrest₁, ← hrest₂,
                      hspec_dt, ← hrest_dt, hds, hlz, pure,
                      bfinal_beq_nat_false bfinal hbf1]
                    rw [← hbr'_eq]
                    exact hgo
            · -- btype ≥ 3: reserved (native throws error)
              exfalso
              split at h <;> first | contradiction | simp at h

/-- **Main theorem**: If the native DEFLATE decompressor succeeds, then
    the formal specification also succeeds and produces the same output. -/
theorem inflate_correct (data : ByteArray) (startPos maxOutputSize : Nat)
    (result : ByteArray) (endPos : Nat)
    (h : Zip.Native.Inflate.inflateRaw data startPos maxOutputSize =
      .ok (result, endPos)) :
    ∃ fuel,
      Deflate.Spec.decode
        ((Deflate.Spec.bytesToBits data).drop (startPos * 8)) fuel =
        some result.data.toList := by
  -- Unfold inflateRaw
  simp only [Zip.Native.Inflate.inflateRaw, bind, Except.bind] at h
  -- Build fixed trees
  cases hflit : Zip.Native.HuffTree.fromLengths
      Zip.Native.Inflate.fixedLitLengths with
  | error e => simp [hflit] at h
  | ok fixedLit =>
    simp only [hflit] at h
    cases hfdist : Zip.Native.HuffTree.fromLengths
        Zip.Native.Inflate.fixedDistLengths with
    | error e => simp [hfdist] at h
    | ok fixedDist =>
      simp only [hfdist] at h
      -- Now h : inflateLoop ... = .ok (result, endPos)
      have hbr_wf : (Zip.Native.BitReader.mk data startPos 0).bitOff < 8 := by simp
      have hbr_pos : (Zip.Native.BitReader.mk data startPos 0).bitOff = 0 ∨
          (Zip.Native.BitReader.mk data startPos 0).pos <
          (Zip.Native.BitReader.mk data startPos 0).data.size := by simp
      obtain ⟨specFuel, hgo⟩ := inflateLoop_correct
        ⟨data, startPos, 0⟩ .empty fixedLit fixedDist
        maxOutputSize 10001 result endPos
        hbr_wf hbr_pos hflit hfdist h
      -- decode = go bits [] fuel
      exact ⟨specFuel, by
        simp only [Deflate.Spec.decode]; exact hgo⟩

/-- Corollary: `inflate` (which starts at position 0) agrees with
    the spec `decode` applied to the full bitstream. -/
theorem inflate_correct' (data : ByteArray) (maxOutputSize : Nat)
    (result : ByteArray)
    (h : Zip.Native.Inflate.inflate data maxOutputSize = .ok result) :
    ∃ fuel,
      Deflate.Spec.decode (Deflate.Spec.bytesToBits data) fuel =
        some result.data.toList := by
  -- Unfold inflate: it calls inflateRaw data 0 maxOutputSize and discards endPos
  simp only [Zip.Native.Inflate.inflate, bind, Except.bind] at h
  cases hinf : Zip.Native.Inflate.inflateRaw data 0 maxOutputSize with
  | error e => simp [hinf] at h
  | ok p =>
    simp [hinf, pure, Except.pure] at h
    have := inflate_correct data 0 maxOutputSize p.1 p.2 (by rw [hinf])
    simp at this
    rw [← h]; exact this

/-! ## Completeness (reverse direction): spec success → native success -/

/-- **Completeness for dynamic tree decode**: if the spec `decodeDynamicTables`
    succeeds on the bit list, the native `decodeDynamicTrees` also succeeds.

    This is the reverse of `decodeDynamicTrees_correct`. -/
theorem decodeDynamicTrees_complete (br : Zip.Native.BitReader)
    (litLens distLens : List Nat) (rest : List Bool)
    (hwf : br.bitOff < 8)
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (hspec : Deflate.Spec.decodeDynamicTables br.toBits =
        some (litLens, distLens, rest)) :
    ∃ litTree distTree br',
      Zip.Native.Inflate.decodeDynamicTrees br = .ok (litTree, distTree, br') ∧
      br'.toBits = rest ∧
      br'.bitOff < 8 ∧
      (br'.bitOff = 0 ∨ br'.pos < br'.data.size) ∧
      Zip.Native.HuffTree.fromLengths (litLens.map Nat.toUInt8).toArray = .ok litTree ∧
      Zip.Native.HuffTree.fromLengths (distLens.map Nat.toUInt8).toArray = .ok distTree ∧
      Huffman.Spec.ValidLengths litLens 15 ∧
      Huffman.Spec.ValidLengths distLens 15 ∧
      litLens.length ≤ UInt16.size ∧
      distLens.length ≤ UInt16.size := by
  -- Unfold the spec do-block
  unfold Deflate.Spec.decodeDynamicTables at hspec
  -- readBitsLSB 5 (hlit)
  cases hspec1 : Deflate.Spec.readBitsLSB 5 br.toBits with
  | none => simp [hspec1] at hspec
  | some p1 =>
    obtain ⟨hlit_v, bits₁⟩ := p1
    simp [hspec1] at hspec
    have hval1 := Deflate.Spec.readBitsLSB_bound hspec1
    have ⟨br₁, hrb1, hrest₁, hwf₁, hpos₁⟩ :=
      readBits_complete br 5 hlit_v bits₁ hwf hpos (by omega) hval1 hspec1
    -- readBitsLSB 5 (hdist)
    cases hspec2 : Deflate.Spec.readBitsLSB 5 bits₁ with
    | none => simp [hspec2] at hspec
    | some p2 =>
      obtain ⟨hdist_v, bits₂⟩ := p2
      simp [hspec2] at hspec
      have hval2 := Deflate.Spec.readBitsLSB_bound hspec2
      have ⟨br₂, hrb2, hrest₂, hwf₂, hpos₂⟩ :=
        readBits_complete br₁ 5 hdist_v bits₂ hwf₁ hpos₁ (by omega) hval2
          (by rw [hrest₁]; exact hspec2)
      -- readBitsLSB 4 (hclen)
      cases hspec3 : Deflate.Spec.readBitsLSB 4 bits₂ with
      | none => simp [hspec3] at hspec
      | some p3 =>
        obtain ⟨hclen_v, bits₃⟩ := p3
        set_option linter.unusedSimpArgs false in
        simp only [hspec3, letFun] at hspec
        set_option linter.unusedSimpArgs false in
        simp only [bind, Option.bind] at hspec
        have hval3 := Deflate.Spec.readBitsLSB_bound hspec3
        have ⟨br₃, hrb3, hrest₃, hwf₃, hpos₃⟩ :=
          readBits_complete br₂ 4 hclen_v bits₃ hwf₂ hpos₂ (by omega) hval3
            (by rw [hrest₂]; exact hspec3)
        -- readCLLengths
        cases hspec_rcl : Deflate.Spec.readCLLengths (hclen_v + 4) 0
            (List.replicate 19 0) bits₃ with
        | none =>
          rw [show (List.replicate 19 0 : List Nat) =
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] from rfl] at hspec_rcl
          simp [hspec_rcl] at hspec
        | some p4 =>
          obtain ⟨clLengths, bits₄⟩ := p4
          rw [show (List.replicate 19 0 : List Nat) =
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] from rfl] at hspec_rcl
          simp [hspec_rcl] at hspec
          -- Extract ValidLengths clLengths 7 from the guard
          -- If guard fails, the match evaluates to none ≠ some
          have hcl_valid : Huffman.Spec.ValidLengths clLengths 7 := by
            by_cases h : Huffman.Spec.ValidLengths clLengths 7
            · exact h
            · simp [guard, h] at hspec
          simp [guard, hcl_valid] at hspec
          -- decodeCLSymbols
          cases hspec_dcl : Deflate.Spec.decodeDynamicTables.decodeCLSymbols
              ((Huffman.Spec.allCodes clLengths 7).map fun (sym, cw) => (cw, sym))
              (hlit_v + 257 + (hdist_v + 1)) [] bits₄
              (hlit_v + 257 + (hdist_v + 1) + 1) with
          | none => simp [hspec_dcl] at hspec
          | some p5 =>
            obtain ⟨codeLengths, bits₅⟩ := p5
            simp [hspec_dcl] at hspec
            -- Extract length guard
            have hlen : codeLengths.length = hlit_v + 257 + (hdist_v + 1) := by
              by_cases h : codeLengths.length = hlit_v + 257 + (hdist_v + 1)
              · exact h
              · simp [h] at hspec
            -- Extract lit ValidLengths guard
            have hlit_valid : Huffman.Spec.ValidLengths
                (codeLengths.take (hlit_v + 257)) 15 := by
              by_cases h : Huffman.Spec.ValidLengths (codeLengths.take (hlit_v + 257)) 15
              · exact h
              · simp [hlen, h] at hspec
            -- Extract dist ValidLengths guard
            have hdist_valid : Huffman.Spec.ValidLengths
                (codeLengths.drop (hlit_v + 257)) 15 := by
              by_cases h : Huffman.Spec.ValidLengths (codeLengths.drop (hlit_v + 257)) 15
              · exact h
              · simp [hlen, hlit_valid, h] at hspec
            -- Now reduce hspec fully
            simp [hlen, hlit_valid, hdist_valid] at hspec
            obtain ⟨hlit_eq, hdist_eq, hrest_eq⟩ := hspec
            -- Now build the native side
            -- Native readCLCodeLengths
            have ⟨br₄, clArr, hrcl_nat, hcl_map, hrest₄, hwf₄, hpos₄⟩ :=
              Deflate.Correctness.readCLCodeLengths_complete br₃
                (.replicate 19 0) 0 (hclen_v + 4) clLengths bits₄ hwf₃ hpos₃
                (by simp)
                (by rw [hrest₃]
                    have : List.map UInt8.toNat (Array.replicate 19 (0 : UInt8)).toList =
                        List.replicate 19 0 := by simp [Array.toList_replicate]
                    rw [this]
                    exact hspec_rcl)
            -- Derive clArr.size = 19 and clLengths.length = 19
            have hcl_sz : clArr.size = 19 := by
              have := Correctness.readCLCodeLengths_size br₃ _ 0 _ clArr br₄ hrcl_nat
              simpa using this
            have hcl_len : clLengths.length = 19 := by
              rw [← hcl_map]; simp [Array.length_toList, hcl_sz]
            -- Native fromLengths for CL tree
            have hcl_vl : Huffman.Spec.ValidLengths
                (clArr.toList.map UInt8.toNat) 7 := by
              rw [hcl_map]; exact hcl_valid
            have ⟨clTree, hft⟩ := fromLengths_complete clArr 7 hcl_vl
            -- Bridge hlit_v/hdist_v/hclen_v.toUInt32.toNat = hlit_v/hdist_v/hclen_v
            have hlit_conv : hlit_v.toUInt32.toNat = hlit_v :=
              Nat.mod_eq_of_lt (by omega)
            have hdist_conv : hdist_v.toUInt32.toNat = hdist_v :=
              Nat.mod_eq_of_lt (by omega)
            have hclen_conv : hclen_v.toUInt32.toNat = hclen_v :=
              Nat.mod_eq_of_lt (by omega)
            -- Native decodeCLSymbols
            -- The spec gives codeLengths and we need the native to produce codeLengths'
            -- such that (codeLengths'.extract 0 totalCodes).toList.map UInt8.toNat = codeLengths
            have hcl_sz_u16 : clArr.size ≤ UInt16.size := by
              rw [hcl_sz]; simp [UInt16.size]
            -- Bridge spec decodeCLSymbols call to native via decodeCLSymbols_complete
            -- The spec uses: allCodes clLengths 7, but complete needs allCodes (clArr.toList.map UInt8.toNat) 7
            -- These are equal by hcl_map
            have hspec_dcl_bridge : Deflate.Spec.decodeDynamicTables.decodeCLSymbols
                ((Huffman.Spec.allCodes (clArr.toList.map UInt8.toNat) 7).map
                  fun (sym, cw) => (cw, sym))
                (hlit_v + 257 + (hdist_v + 1))
                [] bits₄ (hlit_v + 257 + (hdist_v + 1) + 1) =
                some (codeLengths, bits₅) := by
              rw [hcl_map]; exact hspec_dcl
            -- Convert bits₄ to br₄.toBits
            have hspec_dcl_native :
                Deflate.Spec.decodeDynamicTables.decodeCLSymbols
                ((Huffman.Spec.allCodes (clArr.toList.map UInt8.toNat) 7).map
                  fun (sym, cw) => (cw, sym))
                (hlit_v + 257 + (hdist_v + 1))
                (((Array.replicate (hlit_v + 257 + (hdist_v + 1)) (0 : UInt8)).extract 0 0).toList.map
                  UInt8.toNat)
                br₄.toBits (hlit_v + 257 + (hdist_v + 1) + 1) =
                some (codeLengths, bits₅) := by
              simp; rw [hrest₄]; exact hspec_dcl_bridge
            have ⟨codeLengths', br₅, hdcl_nat, hcl_res_map, hrest₅, hwf₅, hpos₅⟩ :=
              Deflate.Correctness.decodeCLSymbols_complete clTree clArr br₄
                (.replicate (hlit_v + 257 + (hdist_v + 1)) 0) 0
                (hlit_v + 257 + (hdist_v + 1))
                (hlit_v + 257 + (hdist_v + 1) + 1)
                codeLengths bits₅ hwf₄ hpos₄ hft hcl_sz_u16
                (by omega) (by simp) hspec_dcl_native
            -- From hcl_res_map:
            -- (codeLengths'.extract 0 (hlit_v + 257 + (hdist_v + 1))).toList.map UInt8.toNat = codeLengths
            -- codeLengths.take (hlit_v + 257) = litLens (from hlit_eq)
            -- codeLengths.drop (hlit_v + 257) = distLens (from hdist_eq)
            -- Bridge native extract to spec take/drop
            have hcl_res_sz : codeLengths'.size =
                hlit_v + 257 + (hdist_v + 1) := by
              have := Correctness.decodeCLSymbols_size clTree br₄ _ 0 _
                _ codeLengths' br₅ hdcl_nat
              simpa using this
            -- Bridge native extracts to spec take/drop
            -- litLenLengths = codeLengths'.extract 0 (hlit_v + 257)
            -- distLengths = codeLengths'.extract (hlit_v + 257) (hlit_v + 257 + (hdist_v + 1))
            -- We need: (codeLengths'.extract 0 numLitLen).toList.map UInt8.toNat = litLens
            -- and: (codeLengths'.extract numLitLen totalCodes).toList.map UInt8.toNat = distLens
            have hlit_bridge :
                (codeLengths'.extract 0 (hlit_v + 257)).toList.map UInt8.toNat = litLens := by
              rw [← hlit_eq, ← hcl_res_map]
              simp only [Array.toList_extract, List.extract, Nat.sub_zero,
                List.drop_zero, List.map_take, List.take_take,
                Nat.min_eq_left (by omega : hlit_v + 257 ≤
                  hlit_v + 257 + (hdist_v + 1))]
            have hdist_bridge :
                (codeLengths'.extract (hlit_v + 257)
                  (hlit_v + 257 + (hdist_v + 1))).toList.map UInt8.toNat = distLens := by
              rw [← hdist_eq, ← hcl_res_map]
              simp only [Array.toList_extract, List.extract,
                Nat.sub_zero, List.drop_zero]
              rw [← List.map_drop, List.drop_take]
            -- ValidLengths for lit/dist through bridge
            have hlit_vl : Huffman.Spec.ValidLengths
                ((codeLengths'.extract 0 (hlit_v + 257)).toList.map UInt8.toNat) 15 := by
              rw [hlit_bridge, ← hlit_eq]; exact hlit_valid
            have hdist_vl : Huffman.Spec.ValidLengths
                ((codeLengths'.extract (hlit_v + 257)
                  (hlit_v + 257 + (hdist_v + 1))).toList.map UInt8.toNat) 15 := by
              rw [hdist_bridge, ← hdist_eq]; exact hdist_valid
            -- fromLengths_complete for lit and dist
            have ⟨litTree, hflit⟩ := fromLengths_complete
              (codeLengths'.extract 0 (hlit_v + 257)) 15 hlit_vl
            have ⟨distTree, hfdist⟩ := fromLengths_complete
              (codeLengths'.extract (hlit_v + 257)
                (hlit_v + 257 + (hdist_v + 1))) 15 hdist_vl
            -- Bridge rest: br₅.toBits = rest
            have hrest_final : br₅.toBits = rest := by rw [hrest₅, hrest_eq]
            -- Bridge: (l.map UInt8.toNat).map Nat.toUInt8).toArray = l.toArray
            -- for any list of UInt8 (since Nat.toUInt8 ∘ UInt8.toNat = id)
            have uint8_roundtrip : ∀ (l : List UInt8),
                l.map (Nat.toUInt8 ∘ UInt8.toNat) = l := by
              intro l
              rw [List.map_congr_left (fun u _ => by
                show Nat.toUInt8 (UInt8.toNat u) = u
                unfold Nat.toUInt8 UInt8.ofNat UInt8.toNat
                rw [BitVec.ofNat_toNat, BitVec.setWidth_eq])]
              simp
            -- litLens/distLens back to native arrays
            have hlit_arr : (litLens.map Nat.toUInt8).toArray =
                codeLengths'.extract 0 (hlit_v + 257) := by
              rw [← hlit_bridge, List.map_map, uint8_roundtrip, Array.toArray_toList]
            have hdist_arr : (distLens.map Nat.toUInt8).toArray =
                codeLengths'.extract (hlit_v + 257)
                  (hlit_v + 257 + (hdist_v + 1)) := by
              rw [← hdist_bridge, List.map_map, uint8_roundtrip, Array.toArray_toList]
            -- Assemble the native decodeDynamicTrees
            refine ⟨litTree, distTree, br₅, ?_, hrest_final, hwf₅, hpos₅,
              ?_, ?_, ?_, ?_, ?_, ?_⟩
            · -- decodeDynamicTrees br = .ok (litTree, distTree, br₅)
              simp only [Zip.Native.Inflate.decodeDynamicTrees, bind, Except.bind,
                hrb1, hrb2, hrb3, hlit_conv, hdist_conv, hclen_conv,
                hrcl_nat, hft, hdcl_nat, hflit, hfdist, pure, Except.pure]
            · -- fromLengths (litLens.map Nat.toUInt8).toArray = .ok litTree
              rw [hlit_arr]; exact hflit
            · -- fromLengths (distLens.map Nat.toUInt8).toArray = .ok distTree
              rw [hdist_arr]; exact hfdist
            · -- ValidLengths litLens 15
              rw [← hlit_eq]; exact hlit_valid
            · -- ValidLengths distLens 15
              rw [← hdist_eq]; exact hdist_valid
            · -- litLens.length ≤ UInt16.size
              rw [← hlit_eq]
              simp [List.length_take, hlen, UInt16.size]
              omega
            · -- distLens.length ≤ UInt16.size
              rw [← hdist_eq]
              simp [List.length_drop, hlen, UInt16.size]
              omega

/-- **Completeness for block loop**: if the spec `decode.go` succeeds,
    the native `inflateLoop` also succeeds with the same result.

    This is the reverse of `inflateLoop_correct`. -/
theorem inflateLoop_complete (br : Zip.Native.BitReader)
    (output : ByteArray)
    (fixedLit fixedDist : Zip.Native.HuffTree)
    (maxOutputSize : Nat)
    (result : List UInt8)
    (hwf : br.bitOff < 8)
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (hflit : Zip.Native.HuffTree.fromLengths
      Zip.Native.Inflate.fixedLitLengths = .ok fixedLit)
    (hfdist : Zip.Native.HuffTree.fromLengths
      Zip.Native.Inflate.fixedDistLengths = .ok fixedDist)
    (hmax : result.length ≤ maxOutputSize)
    (specFuel : Nat)
    (hspec : Deflate.Spec.decode.go br.toBits output.data.toList specFuel =
        some result) :
    ∃ endPos,
      Zip.Native.Inflate.inflateLoop br output fixedLit fixedDist
        maxOutputSize specFuel = .ok (⟨⟨result⟩⟩, endPos) := by
  sorry

end Deflate.Correctness
