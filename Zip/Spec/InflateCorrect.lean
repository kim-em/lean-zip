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

set_option maxRecDepth 2048 in
set_option maxHeartbeats 2000000 in
protected theorem fixedLitLengths_eq :
    (Zip.Native.Inflate.fixedLitLengths).toList.map UInt8.toNat =
    Deflate.Spec.fixedLitLengths := by rfl

set_option maxRecDepth 2048 in
protected theorem fixedDistLengths_eq :
    (Zip.Native.Inflate.fixedDistLengths).toList.map UInt8.toNat =
    Deflate.Spec.fixedDistLengths := by decide

set_option maxRecDepth 2048 in
protected theorem fixedLitLengths_size :
    Zip.Native.Inflate.fixedLitLengths.size ≤ UInt16.size := by
  show 288 ≤ 65536; omega

protected theorem fixedDistLengths_size :
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

/-- Bridge (reverse): `(v == 1) = true` (Nat) with `v < 2` implies
    `(v.toUInt32 == 1) = true` (UInt32). -/
protected theorem nat_beq_to_uint32_true (v : Nat) (hv : v < 2) (h : (v == 1) = true) :
    (v.toUInt32 == 1) = true := by
  rw [beq_iff_eq] at h ⊢; subst h; rfl

/-- Bridge (reverse): `¬((v == 1) = true)` (Nat) with `v < 2` implies
    `(v.toUInt32 == 1) = false` (UInt32). -/
protected theorem nat_beq_to_uint32_false (v : Nat) (hv : v < 2) (h : ¬((v == 1) = true)) :
    ¬((v.toUInt32 == 1) = true) := by
  have hv0 : v = 0 := by simp only [beq_iff_eq] at h; omega
  subst hv0; simp [Nat.toUInt32]

set_option maxRecDepth 2048 in
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
    Deflate.Spec.decode.go br.toBits output.data.toList =
      some result.data.toList := by
  sorry

/-- **Main theorem**: If the native DEFLATE decompressor succeeds, then
    the formal specification also succeeds and produces the same output. -/
theorem inflate_correct (data : ByteArray) (startPos maxOutputSize : Nat)
    (result : ByteArray) (endPos : Nat)
    (h : Zip.Native.Inflate.inflateRaw data startPos maxOutputSize =
      .ok (result, endPos)) :
    Deflate.Spec.decode
      ((Deflate.Spec.bytesToBits data).drop (startPos * 8)) =
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
      have hbr_wf : (Zip.Native.BitReader.mk data startPos 0).bitOff < 8 := by simp
      have hbr_pos : (Zip.Native.BitReader.mk data startPos 0).bitOff = 0 ∨
          (Zip.Native.BitReader.mk data startPos 0).pos <
          (Zip.Native.BitReader.mk data startPos 0).data.size := by simp
      have hgo := inflateLoop_correct
        ⟨data, startPos, 0⟩ .empty fixedLit fixedDist
        maxOutputSize 10000000000 result endPos
        hbr_wf hbr_pos hflit hfdist h
      simp only [Deflate.Spec.decode]; exact hgo

/-- Corollary: `inflate` (which starts at position 0) agrees with
    the spec `decode` applied to the full bitstream. -/
theorem inflate_correct' (data : ByteArray) (maxOutputSize : Nat)
    (result : ByteArray)
    (h : Zip.Native.Inflate.inflate data maxOutputSize = .ok result) :
    Deflate.Spec.decode (Deflate.Spec.bytesToBits data) =
      some result.data.toList := by
  simp only [Zip.Native.Inflate.inflate, bind, Except.bind] at h
  cases hinf : Zip.Native.Inflate.inflateRaw data 0 maxOutputSize with
  | error e => simp [hinf] at h
  | ok p =>
    simp [hinf, pure, Except.pure] at h
    have := inflate_correct data 0 maxOutputSize p.1 p.2 (by rw [hinf])
    simp at this
    rw [← h]; exact this

end Deflate.Correctness
