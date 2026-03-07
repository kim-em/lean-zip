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

end Zip.Spec.ZstdFrame
