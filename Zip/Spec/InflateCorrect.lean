import Zip.Spec.DynamicTreesCorrect

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
  sorry

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
        maxOutputSize (specFuel + 1) = .ok (⟨⟨result⟩⟩, endPos) := by
  sorry

end Deflate.Correctness
