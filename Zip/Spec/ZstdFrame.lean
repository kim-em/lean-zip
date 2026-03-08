import Zip.Native.ZstdFrame
import Zip.Spec.Zstd

/-!
# Zstandard Top-Level Decompressor Specification

Formal specifications for `decompressZstdWF`, the well-founded recursive
entry point that processes concatenated Zstd frames (RFC 8878 §3.1).

The key properties proved here:
1. **Base case**: when the position is past the end of data, the accumulated
   output is returned unchanged.
2. **Single standard frame**: when the input contains exactly one Zstd frame
   starting at `pos`, the result is the accumulated output appended with
   the decompressed frame content.
3. **Single skippable frame**: when a skippable frame is at `pos` and the
   position after skipping is past the end of data, the output is returned
   unchanged (skippable frames contribute no content).
4. **Skippable then standard**: when a skippable frame is followed by a
   standard Zstd frame, only the standard frame contributes content.
5. **Output monotonicity**: when `decompressZstdWF` succeeds, the result is
   at least as large as the input accumulator (decompressing only adds data).
6. **Content preservation**: every byte in the initial accumulator is preserved
   at the same index in the result (append-only property).
7. **API-level single frame**: when the input contains exactly one standard
   frame at position 0, the public `decompressZstd` returns the content.
8. **Empty input**: decompressing an empty ByteArray returns an empty ByteArray.
-/

namespace Zip.Spec.ZstdFrame

/-- When `pos ≥ data.size`, `decompressZstdWF` returns the accumulated output
    unchanged.  This is the recursion base case: no more data to process. -/
theorem decompressZstdWF_base (data : ByteArray) (pos : Nat) (output : ByteArray)
    (h : pos ≥ data.size) :
    Zip.Native.decompressZstdWF data pos output = .ok output := by
  unfold Zip.Native.decompressZstdWF
  simp only [ge_iff_le, h, ↓reduceDIte, pure, Except.pure]

/-- When the input contains exactly one standard Zstd frame at `pos`,
    `decompressZstdWF` returns the accumulated output appended with the
    decompressed frame content.  The recursive call resolves via
    `decompressZstdWF_base` since `pos'` is past the end of data. -/
theorem decompressZstdWF_single_standard_frame (data : ByteArray) (pos : Nat)
    (output content : ByteArray) (pos' : Nat)
    (hsize : data.size ≥ pos + 4)
    (hmagic : Binary.readUInt32LE data pos = Zip.Native.zstdMagic)
    (hframe : Zip.Native.decompressFrame data pos = .ok (content, pos'))
    (hadv : pos' > pos)
    (hdone : pos' ≥ data.size) :
    Zip.Native.decompressZstdWF data pos output = .ok (output ++ content) := by
  unfold Zip.Native.decompressZstdWF
  simp only [show ¬ (pos ≥ data.size) from by omega, ↓reduceDIte,
    show ¬ (data.size < pos + 4) from by omega, ↓reduceIte,
    pure, Pure.pure, bind, Bind.bind, Except.bind, Except.pure]
  rw [hmagic, show Zip.Native.zstdMagic = (4247762216 : UInt32) from rfl]
  simp (config := { decide := true }) only [hframe, ite_true,
    show ¬ (pos' ≤ pos) from by omega, ↓reduceDIte]
  exact decompressZstdWF_base data pos' (output ++ content) hdone

/-- When a skippable frame is at `pos` and the position after skipping
    is past the end of data, `decompressZstdWF` returns the accumulated
    output unchanged — skippable frames contribute no decompressed content. -/
theorem decompressZstdWF_single_skippable_frame (data : ByteArray)
    (pos : Nat) (output : ByteArray) (pos' : Nat)
    (hsize : data.size ≥ pos + 4)
    (hmagic_lo : Binary.readUInt32LE data pos ≥ 0x184D2A50)
    (hmagic_hi : Binary.readUInt32LE data pos ≤ 0x184D2A5F)
    (hskip : Zip.Native.skipSkippableFrame data pos = .ok pos')
    (hadv : pos' > pos)
    (hdone : pos' ≥ data.size) :
    Zip.Native.decompressZstdWF data pos output = .ok output := by
  unfold Zip.Native.decompressZstdWF
  simp only [show ¬ (pos ≥ data.size) from by omega, ↓reduceDIte,
    show ¬ (data.size < pos + 4) from by omega, ↓reduceIte,
    pure, Pure.pure, bind, Bind.bind, Except.bind, Except.pure]
  simp only [decide_eq_true hmagic_lo, decide_eq_true hmagic_hi,
    Bool.true_and, ↓reduceIte, hskip,
    show ¬ (pos' ≤ pos) from by omega, ↓reduceDIte]
  exact decompressZstdWF_base data pos' output hdone

/-- When a skippable frame at `pos` is followed by a standard Zstd frame,
    the result is `output ++ content` — only the standard frame contributes
    decompressed content.  Composes the skippable frame spec with
    `decompressZstdWF_single_standard_frame`. -/
theorem decompressZstdWF_skip_then_standard (data : ByteArray)
    (pos : Nat) (output content : ByteArray) (skipPos framePos : Nat)
    (hsize : data.size ≥ pos + 4)
    (hmagic_lo : Binary.readUInt32LE data pos ≥ 0x184D2A50)
    (hmagic_hi : Binary.readUInt32LE data pos ≤ 0x184D2A5F)
    (hskip : Zip.Native.skipSkippableFrame data pos = .ok skipPos)
    (hskip_adv : skipPos > pos)
    (hsize2 : data.size ≥ skipPos + 4)
    (hmagic2 : Binary.readUInt32LE data skipPos = Zip.Native.zstdMagic)
    (hframe : Zip.Native.decompressFrame data skipPos = .ok (content, framePos))
    (hframe_adv : framePos > skipPos)
    (hdone : framePos ≥ data.size) :
    Zip.Native.decompressZstdWF data pos output = .ok (output ++ content) := by
  unfold Zip.Native.decompressZstdWF
  simp only [show ¬ (pos ≥ data.size) from by omega, ↓reduceDIte,
    show ¬ (data.size < pos + 4) from by omega, ↓reduceIte,
    pure, Pure.pure, bind, Bind.bind, Except.bind, Except.pure]
  simp only [decide_eq_true hmagic_lo, decide_eq_true hmagic_hi,
    Bool.true_and, ↓reduceIte, hskip,
    show ¬ (skipPos ≤ pos) from by omega, ↓reduceDIte]
  exact decompressZstdWF_single_standard_frame data skipPos output content framePos
    hsize2 hmagic2 hframe hframe_adv hdone

/-- When `decompressZstdWF` succeeds, the result is at least as large as the
    input accumulator — decompressing frames only adds data, never removes it. -/
theorem decompressZstdWF_output_size_ge (data : ByteArray) (pos : Nat)
    (output result : ByteArray)
    (h : Zip.Native.decompressZstdWF data pos output = .ok result) :
    result.size ≥ output.size := by
  induction pos, output using Zip.Native.decompressZstdWF.induct (data := data) generalizing result with
  | case1 pos output hpos =>
    -- Base case: pos ≥ data.size, function returns output unchanged
    rw [decompressZstdWF_base data pos output hpos] at h
    cases h; omega
  | case2 pos output hpos hshort ih_skip ih_std =>
    -- Error case: data.size < pos + 4, function throws — contradiction with .ok
    unfold Zip.Native.decompressZstdWF at h
    simp only [show ¬ (pos ≥ data.size) from hpos, ↓reduceDIte,
      show (data.size < pos + 4) from hshort, ↓reduceIte,
      bind, Bind.bind, Except.bind] at h
    exact absurd h nofun
  | case3 pos output hpos hlong ih_skip ih_std =>
    -- Main case: enough data for magic number, dispatch on frame type
    unfold Zip.Native.decompressZstdWF at h
    simp only [show ¬ (pos ≥ data.size) from hpos, ↓reduceDIte,
      show ¬ (data.size < pos + 4) from hlong, ↓reduceIte,
      pure, Pure.pure, bind, Bind.bind, Except.bind, Except.pure] at h
    -- Case split on magic number: skippable, standard, or invalid
    split at h
    · -- Skippable frame branch
      split at h
      · exact absurd h nofun  -- skipSkippableFrame errored
      · split at h
        · exact absurd h nofun  -- frame did not advance
        · exact ih_skip _ ‹_› _ h  -- recursive call with same output
    · -- Non-skippable: standard or invalid
      split at h
      · -- Standard frame branch
        split at h
        · exact absurd h nofun  -- decompressFrame errored
        · split at h
          · exact absurd h nofun  -- frame did not advance
          · -- Recursive call with output ++ content
            have := ih_std _ _ ‹_› _ h
            simp only [ByteArray.size_append] at this ⊢
            omega
      · exact absurd h nofun  -- invalid magic number

/-- When `decompressZstdWF` succeeds, every byte that was in the `output` buffer
    before the call is present at the same index in the result.  This is the
    content-level counterpart to `decompressZstdWF_output_size_ge`.  Together they
    establish that frame-loop decompression is append-only: it only adds data. -/
theorem decompressZstdWF_prefix (data : ByteArray) (pos : Nat)
    (output result : ByteArray)
    (h : Zip.Native.decompressZstdWF data pos output = .ok result)
    (i : Nat) (hi : i < output.size) :
    result[i]'(by have := decompressZstdWF_output_size_ge _ _ _ _ h; omega)
      = output[i] := by
  induction pos, output using Zip.Native.decompressZstdWF.induct (data := data) generalizing result with
  | case1 pos output hpos =>
    -- Base case: pos ≥ data.size, function returns output unchanged
    rw [decompressZstdWF_base data pos output hpos] at h
    cases h; rfl
  | case2 pos output hpos hshort ih_skip ih_std =>
    -- Error case: data.size < pos + 4, function throws — contradiction with .ok
    unfold Zip.Native.decompressZstdWF at h
    simp only [show ¬ (pos ≥ data.size) from hpos, ↓reduceDIte,
      show (data.size < pos + 4) from hshort, ↓reduceIte,
      bind, Bind.bind, Except.bind] at h
    exact absurd h nofun
  | case3 pos output hpos hlong ih_skip ih_std =>
    -- Main case: enough data for magic number, dispatch on frame type
    unfold Zip.Native.decompressZstdWF at h
    simp only [show ¬ (pos ≥ data.size) from hpos, ↓reduceDIte,
      show ¬ (data.size < pos + 4) from hlong, ↓reduceIte,
      pure, Pure.pure, bind, Bind.bind, Except.bind, Except.pure] at h
    -- Case split on magic number: skippable, standard, or invalid
    split at h
    · -- Skippable frame branch
      split at h
      · exact absurd h nofun  -- skipSkippableFrame errored
      · split at h
        · exact absurd h nofun  -- frame did not advance
        · exact ih_skip _ ‹_› _ h hi  -- recursive call with same output
    · -- Non-skippable: standard or invalid
      split at h
      · -- Standard frame branch
        split at h
        · exact absurd h nofun  -- decompressFrame errored
        · split at h
          · exact absurd h nofun  -- frame did not advance
          · -- Recursive call with output ++ content
            have := ih_std _ _ ‹_› _ h
              (by simp only [ByteArray.size_append]; omega)
            rw [this, ByteArray.getElem_append_left hi]
      · exact absurd h nofun  -- invalid magic number

/-- When the input contains exactly one standard Zstd frame starting at position 0,
    `decompressZstd` returns the decompressed content.  This is the first API-level
    theorem — it characterizes the public entry point rather than the internal
    `decompressZstdWF`. -/
theorem decompressZstd_single_frame (data : ByteArray)
    (content : ByteArray) (pos' : Nat)
    (hframe : Zip.Native.decompressFrame data 0 = .ok (content, pos'))
    (hend : pos' ≥ data.size) :
    Zip.Native.decompressZstd data = .ok content := by
  -- Extract parseFrameHeader success from decompressFrame success
  have ⟨hdr, afterHdr, hph⟩ : ∃ hdr afterHdr,
      Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr) := by
    unfold Zip.Native.decompressFrame at hframe
    cases hc : Zip.Native.parseFrameHeader data 0 with
    | error e => simp only [hc, bind, Except.bind] at hframe; exact nomatch hframe
    | ok val => exact ⟨val.1, val.2, rfl⟩
  -- Derive required conditions
  have hmagic : Binary.readUInt32LE data 0 = Zip.Native.zstdMagic :=
    Zstd.Spec.parseFrameHeader_magic data 0 hdr afterHdr hph
  have hsize : data.size ≥ 0 + 4 := by
    unfold Zip.Native.parseFrameHeader at hph
    dsimp only [Bind.bind, Except.bind] at hph
    by_cases hlt : data.size < 0 + 4
    · rw [if_pos hlt] at hph; exact nomatch hph
    · omega
  have hadv : pos' > 0 :=
    Zstd.Spec.decompressFrame_pos_gt data 0 content pos' hframe
  -- Apply single standard frame theorem and simplify ByteArray.empty ++ content
  unfold Zip.Native.decompressZstd
  rw [decompressZstdWF_single_standard_frame data 0 ByteArray.empty content pos'
    hsize hmagic hframe hadv hend, ByteArray.empty_append]

/-- Decompressing an empty ByteArray returns an empty ByteArray.
    This is a direct corollary of `decompressZstdWF_base`. -/
theorem decompressZstd_empty :
    Zip.Native.decompressZstd ⟨#[]⟩ = .ok ⟨#[]⟩ := by
  unfold Zip.Native.decompressZstd
  exact decompressZstdWF_base ⟨#[]⟩ 0 ByteArray.empty (by simp [ByteArray.size])

end Zip.Spec.ZstdFrame
