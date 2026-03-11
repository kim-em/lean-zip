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
7. **Two consecutive standard frames**: when two standard frames fill the
   remaining data, `decompressZstdWF` produces the accumulator appended with
   both frames' content.
8. **API-level single frame**: when the input contains exactly one standard
   frame at position 0, the public `decompressZstd` returns the content.
9. **API-level two frames**: when the input contains exactly two standard
   frames starting at position 0, `decompressZstd` returns their concatenation.
10. **Empty input**: decompressing an empty ByteArray returns an empty ByteArray.
11. **API-level single skippable**: when the input contains a single skippable frame
    at position 0, `decompressZstd` returns empty output.
12. **API-level skip then standard**: when the input starts with a skippable frame
    followed by a standard frame, `decompressZstd` returns only the standard content.

## API-level content coverage matrix

Single-block (4/4):
- raw ✓ `decompressZstd_single_raw_block_content`
- rle ✓ `decompressZstd_single_rle_block_content`
- compLit ✓ `decompressZstd_single_compressed_literals`
- compSeq ✓ `decompressZstd_single_compressed_sequences`

Two-block (first non-last × second last, 12/16):
                  raw     rle     compLit compSeq
    raw      ✓       ✓       ✓       —
    rle      ✓       ✓       ✓       —
    compLit  ✓       ✓       —       ✓
    compSeq  ✓       ✓       ✓       —

Remaining gaps: raw+compSeq, rle+compSeq (issue #1082),
compLit+compLit, compSeq+compSeq (issue #1078).
-/

namespace Zip.Spec.ZstdFrame

/-- When `decompressFrame` succeeds, `parseFrameHeader` must also succeed at the
    same position — `decompressFrame` begins by calling `parseFrameHeader`. -/
private theorem decompressFrame_has_header (data : ByteArray) (pos : Nat)
    (content : ByteArray) (pos' : Nat)
    (hframe : Zip.Native.decompressFrame data pos = .ok (content, pos')) :
    ∃ hdr afterHdr, Zip.Native.parseFrameHeader data pos = .ok (hdr, afterHdr) := by
  unfold Zip.Native.decompressFrame at hframe
  cases hc : Zip.Native.parseFrameHeader data pos with
  | error e => simp only [hc, bind, Except.bind] at hframe; exact nomatch hframe
  | ok val => exact ⟨val.1, val.2, rfl⟩

/-- When `parseFrameHeader` succeeds, the data is at least `pos + 4` bytes long
    (enough for the magic number). -/
private theorem parseFrameHeader_data_size_ge (data : ByteArray) (pos : Nat)
    (hdr : Zip.Native.ZstdFrameHeader) (afterHdr : Nat)
    (h : Zip.Native.parseFrameHeader data pos = .ok (hdr, afterHdr)) :
    data.size ≥ pos + 4 := by
  have := Zstd.Spec.parseFrameHeader_pos_ge_five data pos hdr afterHdr h
  have := Zstd.Spec.parseFrameHeader_le_size data pos hdr afterHdr h
  omega

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
    exact nomatch h
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
      · exact nomatch h  -- skipSkippableFrame errored
      · split at h
        · exact nomatch h  -- frame did not advance
        · exact ih_skip _ ‹_› _ h  -- recursive call with same output
    · -- Non-skippable: standard or invalid
      split at h
      · -- Standard frame branch
        split at h
        · exact nomatch h  -- decompressFrame errored
        · split at h
          · exact nomatch h  -- frame did not advance
          · -- Recursive call with output ++ content
            have := ih_std _ _ ‹_› _ h
            simp only [ByteArray.size_append] at this ⊢
            omega
      · exact nomatch h  -- invalid magic number

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
    exact nomatch h
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
      · exact nomatch h  -- skipSkippableFrame errored
      · split at h
        · exact nomatch h  -- frame did not advance
        · exact ih_skip _ ‹_› _ h hi  -- recursive call with same output
    · -- Non-skippable: standard or invalid
      split at h
      · -- Standard frame branch
        split at h
        · exact nomatch h  -- decompressFrame errored
        · split at h
          · exact nomatch h  -- frame did not advance
          · -- Recursive call with output ++ content
            have := ih_std _ _ ‹_› _ h
              (by simp only [ByteArray.size_append]; omega)
            rw [this, ByteArray.getElem_append_left hi]
      · exact nomatch h  -- invalid magic number

/-- When the input contains exactly one standard Zstd frame starting at position 0,
    `decompressZstd` returns the decompressed content.  This is the first API-level
    theorem — it characterizes the public entry point rather than the internal
    `decompressZstdWF`. -/
theorem decompressZstd_single_frame (data : ByteArray)
    (content : ByteArray) (pos' : Nat)
    (hframe : Zip.Native.decompressFrame data 0 = .ok (content, pos'))
    (hend : pos' ≥ data.size) :
    Zip.Native.decompressZstd data = .ok content := by
  have ⟨hdr, afterHdr, hph⟩ := decompressFrame_has_header data 0 content pos' hframe
  have hmagic := Zstd.Spec.parseFrameHeader_magic data 0 hdr afterHdr hph
  have hsize := parseFrameHeader_data_size_ge data 0 hdr afterHdr hph
  have hadv := Zstd.Spec.decompressFrame_pos_gt data 0 content pos' hframe
  unfold Zip.Native.decompressZstd
  rw [decompressZstdWF_single_standard_frame data 0 ByteArray.empty content pos'
    hsize hmagic hframe hadv hend, ByteArray.empty_append]

/-- When two consecutive standard Zstd frames fill the remaining data,
    `decompressZstdWF` produces the accumulated output appended with both
    frames' content.  Unfolds one level for the first frame, then applies
    `decompressZstdWF_single_standard_frame` for the second. -/
theorem decompressZstdWF_standard_then_standard (data : ByteArray)
    (pos : Nat) (output content1 content2 : ByteArray)
    (pos1 pos2 : Nat)
    (hsize1 : data.size ≥ pos + 4)
    (hmagic1 : Binary.readUInt32LE data pos = Zip.Native.zstdMagic)
    (hframe1 : Zip.Native.decompressFrame data pos = .ok (content1, pos1))
    (hadv1 : pos1 > pos)
    (hsize2 : data.size ≥ pos1 + 4)
    (hmagic2 : Binary.readUInt32LE data pos1 = Zip.Native.zstdMagic)
    (hframe2 : Zip.Native.decompressFrame data pos1 = .ok (content2, pos2))
    (hadv2 : pos2 > pos1)
    (hdone : pos2 ≥ data.size) :
    Zip.Native.decompressZstdWF data pos output
      = .ok (output ++ content1 ++ content2) := by
  unfold Zip.Native.decompressZstdWF
  simp only [show ¬ (pos ≥ data.size) from by omega, ↓reduceDIte,
    show ¬ (data.size < pos + 4) from by omega, ↓reduceIte,
    pure, Pure.pure, bind, Bind.bind, Except.bind, Except.pure]
  rw [hmagic1, show Zip.Native.zstdMagic = (4247762216 : UInt32) from rfl]
  simp (config := { decide := true }) only [hframe1, ite_true,
    show ¬ (pos1 ≤ pos) from by omega, ↓reduceDIte]
  exact decompressZstdWF_single_standard_frame data pos1 (output ++ content1)
    content2 pos2 hsize2 hmagic2 hframe2 hadv2 hdone

/-- When the input contains exactly two standard Zstd frames starting at
    position 0, `decompressZstd` returns the concatenation of both frames'
    content.  This extends `decompressZstd_single_frame` to the two-frame
    case (RFC 8878 §3.1: concatenated frames are decompressed independently). -/
theorem decompressZstd_two_frames (data : ByteArray)
    (content1 content2 : ByteArray) (pos1 pos2 : Nat)
    (hframe1 : Zip.Native.decompressFrame data 0 = .ok (content1, pos1))
    (hframe2 : Zip.Native.decompressFrame data pos1 = .ok (content2, pos2))
    (hend : pos2 ≥ data.size) :
    Zip.Native.decompressZstd data = .ok (content1 ++ content2) := by
  have ⟨hdr1, afterHdr1, hph1⟩ := decompressFrame_has_header data 0 content1 pos1 hframe1
  have ⟨hdr2, afterHdr2, hph2⟩ := decompressFrame_has_header data pos1 content2 pos2 hframe2
  have hmagic1 := Zstd.Spec.parseFrameHeader_magic data 0 hdr1 afterHdr1 hph1
  have hsize1 := parseFrameHeader_data_size_ge data 0 hdr1 afterHdr1 hph1
  have hadv1 := Zstd.Spec.decompressFrame_pos_gt data 0 content1 pos1 hframe1
  have hmagic2 := Zstd.Spec.parseFrameHeader_magic data pos1 hdr2 afterHdr2 hph2
  have hsize2 := parseFrameHeader_data_size_ge data pos1 hdr2 afterHdr2 hph2
  have hadv2 := Zstd.Spec.decompressFrame_pos_gt data pos1 content2 pos2 hframe2
  unfold Zip.Native.decompressZstd
  rw [decompressZstdWF_standard_then_standard data 0 ByteArray.empty
    content1 content2 pos1 pos2 hsize1 hmagic1 hframe1 hadv1
    hsize2 hmagic2 hframe2 hadv2 hend, ByteArray.empty_append]

/-- Decompressing an empty ByteArray returns an empty ByteArray.
    This is a direct corollary of `decompressZstdWF_base`. -/
theorem decompressZstd_empty :
    Zip.Native.decompressZstd ⟨#[]⟩ = .ok ⟨#[]⟩ := by
  unfold Zip.Native.decompressZstd
  exact decompressZstdWF_base ⟨#[]⟩ 0 ByteArray.empty (by decide)

/-- When the input contains a single skippable frame starting at position 0 that
    fills all remaining data, `decompressZstd` returns empty output.  Skippable
    frames contribute no decompressed content (RFC 8878 §3.1.2). -/
theorem decompressZstd_single_skippable (data : ByteArray) (pos' : Nat)
    (hsize : data.size ≥ 4)
    (hmagic_lo : Binary.readUInt32LE data 0 ≥ 0x184D2A50)
    (hmagic_hi : Binary.readUInt32LE data 0 ≤ 0x184D2A5F)
    (hskip : Zip.Native.skipSkippableFrame data 0 = .ok pos')
    (hadv : pos' > 0)
    (hdone : pos' ≥ data.size) :
    Zip.Native.decompressZstd data = .ok ⟨#[]⟩ := by
  unfold Zip.Native.decompressZstd
  exact decompressZstdWF_single_skippable_frame data 0 ByteArray.empty pos'
    (by omega) hmagic_lo hmagic_hi hskip hadv hdone

/-- When the input starts with a skippable frame followed by a standard frame
    that fills all remaining data, `decompressZstd` returns only the standard
    frame's content.  The skippable frame is transparent to decompression. -/
theorem decompressZstd_skip_then_standard (data : ByteArray)
    (content : ByteArray) (skipPos framePos : Nat)
    (hsize : data.size ≥ 4)
    (hmagic_lo : Binary.readUInt32LE data 0 ≥ 0x184D2A50)
    (hmagic_hi : Binary.readUInt32LE data 0 ≤ 0x184D2A5F)
    (hskip : Zip.Native.skipSkippableFrame data 0 = .ok skipPos)
    (hskipAdv : skipPos > 0)
    (hsize2 : data.size ≥ skipPos + 4)
    (hmagic2 : Binary.readUInt32LE data skipPos = Zip.Native.zstdMagic)
    (hframe : Zip.Native.decompressFrame data skipPos = .ok (content, framePos))
    (hframeAdv : framePos > skipPos)
    (hdone : framePos ≥ data.size) :
    Zip.Native.decompressZstd data = .ok content := by
  unfold Zip.Native.decompressZstd
  rw [decompressZstdWF_skip_then_standard data 0 ByteArray.empty content skipPos framePos
    (by omega) hmagic_lo hmagic_hi hskip hskipAdv hsize2 hmagic2 hframe hframeAdv hdone,
    ByteArray.empty_append]

/-! ## API-level single-block content (raw/RLE) -/

/-- When the input contains exactly one standard Zstd frame at position 0 with a
    single last raw block, `decompressZstd` returns the raw block content.
    Composes `decompressFrame_single_raw_content` with `decompressZstd_single_frame`. -/
theorem decompressZstd_single_raw_block_content (data : ByteArray)
    (output : ByteArray) (pos' : Nat)
    (header : Zip.Native.ZstdFrameHeader) (afterHeader : Nat)
    (hdr : Zip.Native.ZstdBlockHeader) (afterHdr : Nat)
    (block : ByteArray) (afterBlock : Nat)
    (hframe : Zip.Native.decompressFrame data 0 = .ok (output, pos'))
    (hend : pos' ≥ data.size)
    (hh : Zip.Native.parseFrameHeader data 0 = .ok (header, afterHeader))
    (hparse : Zip.Native.parseBlockHeader data afterHeader = .ok (hdr, afterHdr))
    (hbs : ¬ hdr.blockSize > 131072)
    (hws : ¬ (header.windowSize > 0 && hdr.blockSize.toUInt64 > header.windowSize))
    (htype : hdr.blockType = .raw)
    (hraw : Zip.Native.decompressRawBlock data afterHdr hdr.blockSize = .ok (block, afterBlock))
    (hlast : hdr.lastBlock = true) :
    Zip.Native.decompressZstd data = .ok block := by
  have hcontent := Zstd.Spec.decompressFrame_single_raw_content data 0 output pos'
    header afterHeader hdr afterHdr block afterBlock
    hframe hh hparse hbs hws htype hraw hlast
  subst hcontent
  exact decompressZstd_single_frame data output pos' hframe hend

/-- When the input contains exactly one standard Zstd frame at position 0 with a
    single last RLE block, `decompressZstd` returns the RLE block content.
    Composes `decompressFrame_single_rle_content` with `decompressZstd_single_frame`. -/
theorem decompressZstd_single_rle_block_content (data : ByteArray)
    (output : ByteArray) (pos' : Nat)
    (header : Zip.Native.ZstdFrameHeader) (afterHeader : Nat)
    (hdr : Zip.Native.ZstdBlockHeader) (afterHdr : Nat)
    (block : ByteArray) (afterByte : Nat)
    (hframe : Zip.Native.decompressFrame data 0 = .ok (output, pos'))
    (hend : pos' ≥ data.size)
    (hh : Zip.Native.parseFrameHeader data 0 = .ok (header, afterHeader))
    (hparse : Zip.Native.parseBlockHeader data afterHeader = .ok (hdr, afterHdr))
    (hbs : ¬ hdr.blockSize > 131072)
    (hws : ¬ (header.windowSize > 0 && hdr.blockSize.toUInt64 > header.windowSize))
    (htype : hdr.blockType = .rle)
    (hrle : Zip.Native.decompressRLEBlock data afterHdr hdr.blockSize = .ok (block, afterByte))
    (hlast : hdr.lastBlock = true) :
    Zip.Native.decompressZstd data = .ok block := by
  have hcontent := Zstd.Spec.decompressFrame_single_rle_content data 0 output pos'
    header afterHeader hdr afterHdr block afterByte
    hframe hh hparse hbs hws htype hrle hlast
  subst hcontent
  exact decompressZstd_single_frame data output pos' hframe hend

/-! ## API-level two-block content (raw/RLE homogeneous) -/

/-- When the input contains exactly one standard Zstd frame at position 0 with two
    consecutive raw blocks (first non-last, second last), `decompressZstd` returns
    `block1 ++ block2`.  Composes `decompressFrame_two_raw_blocks_content` (which
    derives `output = block1 ++ block2`) with `decompressZstd_single_frame`. -/
theorem decompressZstd_two_raw_blocks_content (data : ByteArray)
    (output : ByteArray) (pos' : Nat)
    (header : Zip.Native.ZstdFrameHeader) (afterHeader : Nat)
    -- Block 1 (non-last raw)
    (hdr1 : Zip.Native.ZstdBlockHeader) (afterHdr1 : Nat)
    (block1 : ByteArray) (afterBlock1 : Nat)
    -- Block 2 (last raw)
    (hdr2 : Zip.Native.ZstdBlockHeader) (afterHdr2 : Nat)
    (block2 : ByteArray) (afterBlock2 : Nat)
    -- Frame hypotheses
    (hframe : Zip.Native.decompressFrame data 0 = .ok (output, pos'))
    (hh : Zip.Native.parseFrameHeader data 0 = .ok (header, afterHeader))
    -- Block 1 hypotheses
    (hparse1 : Zip.Native.parseBlockHeader data afterHeader = .ok (hdr1, afterHdr1))
    (hbs1 : ¬ hdr1.blockSize > 131072)
    (hws1 : ¬ (header.windowSize > 0 && hdr1.blockSize.toUInt64 > header.windowSize))
    (htype1 : hdr1.blockType = .raw)
    (hraw1 : Zip.Native.decompressRawBlock data afterHdr1 hdr1.blockSize
               = .ok (block1, afterBlock1))
    (hnotlast1 : hdr1.lastBlock = false)
    (hadv1 : ¬ afterBlock1 ≤ afterHeader)
    -- Block 2 hypotheses
    (hoff2 : ¬ data.size ≤ afterBlock1)
    (hparse2 : Zip.Native.parseBlockHeader data afterBlock1 = .ok (hdr2, afterHdr2))
    (hbs2 : ¬ hdr2.blockSize > 131072)
    (hws2 : ¬ (header.windowSize > 0 && hdr2.blockSize.toUInt64 > header.windowSize))
    (htype2 : hdr2.blockType = .raw)
    (hraw2 : Zip.Native.decompressRawBlock data afterHdr2 hdr2.blockSize
               = .ok (block2, afterBlock2))
    (hlast2 : hdr2.lastBlock = true)
    -- End of data
    (hend : pos' ≥ data.size) :
    Zip.Native.decompressZstd data = .ok (block1 ++ block2) := by
  have hcontent := Zstd.Spec.decompressFrame_two_raw_blocks_content data 0 output pos'
    header afterHeader hdr1 afterHdr1 block1 afterBlock1
    hdr2 afterHdr2 block2 afterBlock2
    hframe hh hparse1 hbs1 hws1 htype1 hraw1 hnotlast1 hadv1
    hoff2 hparse2 hbs2 hws2 htype2 hraw2 hlast2
  subst hcontent
  exact decompressZstd_single_frame data (block1 ++ block2) pos' hframe hend

/-- When the input contains exactly one standard Zstd frame at position 0 with two
    consecutive RLE blocks (first non-last, second last), `decompressZstd` returns
    `block1 ++ block2`.  Composes `decompressFrame_two_rle_blocks_content` (which
    derives `output = block1 ++ block2`) with `decompressZstd_single_frame`. -/
theorem decompressZstd_two_rle_blocks_content (data : ByteArray)
    (output : ByteArray) (pos' : Nat)
    (header : Zip.Native.ZstdFrameHeader) (afterHeader : Nat)
    -- Block 1 (non-last RLE)
    (hdr1 : Zip.Native.ZstdBlockHeader) (afterHdr1 : Nat)
    (block1 : ByteArray) (afterByte1 : Nat)
    -- Block 2 (last RLE)
    (hdr2 : Zip.Native.ZstdBlockHeader) (afterHdr2 : Nat)
    (block2 : ByteArray) (afterByte2 : Nat)
    -- Frame hypotheses
    (hframe : Zip.Native.decompressFrame data 0 = .ok (output, pos'))
    (hh : Zip.Native.parseFrameHeader data 0 = .ok (header, afterHeader))
    -- Block 1 hypotheses
    (hparse1 : Zip.Native.parseBlockHeader data afterHeader = .ok (hdr1, afterHdr1))
    (hbs1 : ¬ hdr1.blockSize > 131072)
    (hws1 : ¬ (header.windowSize > 0 && hdr1.blockSize.toUInt64 > header.windowSize))
    (htype1 : hdr1.blockType = .rle)
    (hrle1 : Zip.Native.decompressRLEBlock data afterHdr1 hdr1.blockSize
               = .ok (block1, afterByte1))
    (hnotlast1 : hdr1.lastBlock = false)
    (hadv1 : ¬ afterByte1 ≤ afterHeader)
    -- Block 2 hypotheses
    (hoff2 : ¬ data.size ≤ afterByte1)
    (hparse2 : Zip.Native.parseBlockHeader data afterByte1 = .ok (hdr2, afterHdr2))
    (hbs2 : ¬ hdr2.blockSize > 131072)
    (hws2 : ¬ (header.windowSize > 0 && hdr2.blockSize.toUInt64 > header.windowSize))
    (htype2 : hdr2.blockType = .rle)
    (hrle2 : Zip.Native.decompressRLEBlock data afterHdr2 hdr2.blockSize
               = .ok (block2, afterByte2))
    (hlast2 : hdr2.lastBlock = true)
    -- End of data
    (hend : pos' ≥ data.size) :
    Zip.Native.decompressZstd data = .ok (block1 ++ block2) := by
  have hcontent := Zstd.Spec.decompressFrame_two_rle_blocks_content data 0 output pos'
    header afterHeader hdr1 afterHdr1 block1 afterByte1
    hdr2 afterHdr2 block2 afterByte2
    hframe hh hparse1 hbs1 hws1 htype1 hrle1 hnotlast1 hadv1
    hoff2 hparse2 hbs2 hws2 htype2 hrle2 hlast2
  subst hcontent
  exact decompressZstd_single_frame data (block1 ++ block2) pos' hframe hend

/-- When the input contains exactly one standard Zstd frame at position 0 with two
    blocks (first non-last raw, second last RLE), `decompressZstd` returns
    `block1 ++ block2`.  Composes `decompressFrame_raw_then_rle_content` (which
    derives `output = block1 ++ block2`) with `decompressZstd_single_frame`. -/
theorem decompressZstd_raw_then_rle_content (data : ByteArray)
    (output : ByteArray) (pos' : Nat)
    (header : Zip.Native.ZstdFrameHeader) (afterHeader : Nat)
    -- Block 1 (non-last raw)
    (hdr1 : Zip.Native.ZstdBlockHeader) (afterHdr1 : Nat)
    (block1 : ByteArray) (afterBlock1 : Nat)
    -- Block 2 (last RLE)
    (hdr2 : Zip.Native.ZstdBlockHeader) (afterHdr2 : Nat)
    (block2 : ByteArray) (afterByte2 : Nat)
    -- Frame hypotheses
    (hframe : Zip.Native.decompressFrame data 0 = .ok (output, pos'))
    (hh : Zip.Native.parseFrameHeader data 0 = .ok (header, afterHeader))
    -- Block 1 hypotheses (raw, non-last)
    (hparse1 : Zip.Native.parseBlockHeader data afterHeader = .ok (hdr1, afterHdr1))
    (hbs1 : ¬ hdr1.blockSize > 131072)
    (hws1 : ¬ (header.windowSize > 0 && hdr1.blockSize.toUInt64 > header.windowSize))
    (htype1 : hdr1.blockType = .raw)
    (hraw1 : Zip.Native.decompressRawBlock data afterHdr1 hdr1.blockSize
               = .ok (block1, afterBlock1))
    (hnotlast1 : hdr1.lastBlock = false)
    (hadv1 : ¬ afterBlock1 ≤ afterHeader)
    -- Block 2 hypotheses (RLE, last)
    (hoff2 : ¬ data.size ≤ afterBlock1)
    (hparse2 : Zip.Native.parseBlockHeader data afterBlock1 = .ok (hdr2, afterHdr2))
    (hbs2 : ¬ hdr2.blockSize > 131072)
    (hws2 : ¬ (header.windowSize > 0 && hdr2.blockSize.toUInt64 > header.windowSize))
    (htype2 : hdr2.blockType = .rle)
    (hrle2 : Zip.Native.decompressRLEBlock data afterHdr2 hdr2.blockSize
               = .ok (block2, afterByte2))
    (hlast2 : hdr2.lastBlock = true)
    -- End of data
    (hend : pos' ≥ data.size) :
    Zip.Native.decompressZstd data = .ok (block1 ++ block2) := by
  have hcontent := Zstd.Spec.decompressFrame_raw_then_rle_content data 0 output pos'
    header afterHeader hdr1 afterHdr1 block1 afterBlock1
    hdr2 afterHdr2 block2 afterByte2
    hframe hh hparse1 hbs1 hws1 htype1 hraw1 hnotlast1 hadv1
    hoff2 hparse2 hbs2 hws2 htype2 hrle2 hlast2
  subst hcontent
  exact decompressZstd_single_frame data (block1 ++ block2) pos' hframe hend

/-- When the input contains exactly one standard Zstd frame at position 0 with two
    blocks (first non-last RLE, second last raw), `decompressZstd` returns
    `block1 ++ block2`.  Composes `decompressFrame_rle_then_raw_content` (which
    derives `output = block1 ++ block2`) with `decompressZstd_single_frame`. -/
theorem decompressZstd_rle_then_raw_content (data : ByteArray)
    (output : ByteArray) (pos' : Nat)
    (header : Zip.Native.ZstdFrameHeader) (afterHeader : Nat)
    -- Block 1 (non-last RLE)
    (hdr1 : Zip.Native.ZstdBlockHeader) (afterHdr1 : Nat)
    (block1 : ByteArray) (afterByte1 : Nat)
    -- Block 2 (last raw)
    (hdr2 : Zip.Native.ZstdBlockHeader) (afterHdr2 : Nat)
    (block2 : ByteArray) (afterBlock2 : Nat)
    -- Frame hypotheses
    (hframe : Zip.Native.decompressFrame data 0 = .ok (output, pos'))
    (hh : Zip.Native.parseFrameHeader data 0 = .ok (header, afterHeader))
    -- Block 1 hypotheses (RLE, non-last)
    (hparse1 : Zip.Native.parseBlockHeader data afterHeader = .ok (hdr1, afterHdr1))
    (hbs1 : ¬ hdr1.blockSize > 131072)
    (hws1 : ¬ (header.windowSize > 0 && hdr1.blockSize.toUInt64 > header.windowSize))
    (htype1 : hdr1.blockType = .rle)
    (hrle1 : Zip.Native.decompressRLEBlock data afterHdr1 hdr1.blockSize
               = .ok (block1, afterByte1))
    (hnotlast1 : hdr1.lastBlock = false)
    (hadv1 : ¬ afterByte1 ≤ afterHeader)
    -- Block 2 hypotheses (raw, last)
    (hoff2 : ¬ data.size ≤ afterByte1)
    (hparse2 : Zip.Native.parseBlockHeader data afterByte1 = .ok (hdr2, afterHdr2))
    (hbs2 : ¬ hdr2.blockSize > 131072)
    (hws2 : ¬ (header.windowSize > 0 && hdr2.blockSize.toUInt64 > header.windowSize))
    (htype2 : hdr2.blockType = .raw)
    (hraw2 : Zip.Native.decompressRawBlock data afterHdr2 hdr2.blockSize
               = .ok (block2, afterBlock2))
    (hlast2 : hdr2.lastBlock = true)
    -- End of data
    (hend : pos' ≥ data.size) :
    Zip.Native.decompressZstd data = .ok (block1 ++ block2) := by
  have hcontent := Zstd.Spec.decompressFrame_rle_then_raw_content data 0 output pos'
    header afterHeader hdr1 afterHdr1 block1 afterByte1
    hdr2 afterHdr2 block2 afterBlock2
    hframe hh hparse1 hbs1 hws1 htype1 hrle1 hnotlast1 hadv1
    hoff2 hparse2 hbs2 hws2 htype2 hraw2 hlast2
  subst hcontent
  exact decompressZstd_single_frame data (block1 ++ block2) pos' hframe hend

/-! ## API-level single-block content (compressed) -/

/-- When the input contains exactly one standard Zstd frame at position 0 with a
    single last compressed block having numSeq=0 (literals only), `decompressZstd`
    returns the literal section content.  Composes
    `decompressFrame_single_compressed_literals_content` with
    `decompressZstd_single_frame`. -/
theorem decompressZstd_single_compressed_literals (data : ByteArray)
    (output : ByteArray) (pos' : Nat)
    (header : Zip.Native.ZstdFrameHeader) (afterHeader : Nat)
    (hdr : Zip.Native.ZstdBlockHeader) (afterHdr : Nat)
    (literals : ByteArray) (afterLiterals : Nat)
    (huffTree : Option Zip.Native.ZstdHuffmanTable)
    (modes : Zip.Native.SequenceCompressionModes) (afterSeqHeader : Nat)
    (hframe : Zip.Native.decompressFrame data 0 = .ok (output, pos'))
    (hh : Zip.Native.parseFrameHeader data 0 = .ok (header, afterHeader))
    (hparse : Zip.Native.parseBlockHeader data afterHeader = .ok (hdr, afterHdr))
    (hbs : ¬ hdr.blockSize > 131072)
    (hws : ¬ (header.windowSize > 0 && hdr.blockSize.toUInt64 > header.windowSize))
    (htype : hdr.blockType = .compressed)
    (hblockEnd : ¬ data.size < afterHdr + hdr.blockSize.toNat)
    (hlit : Zip.Native.parseLiteralsSection data afterHdr none
              = .ok (literals, afterLiterals, huffTree))
    (hseq : Zip.Native.parseSequencesHeader data afterLiterals
              = .ok (0, modes, afterSeqHeader))
    (hlast : hdr.lastBlock = true)
    (hend : pos' ≥ data.size) :
    Zip.Native.decompressZstd data = .ok literals := by
  have hcontent := Zstd.Spec.decompressFrame_single_compressed_literals_content data 0
    output pos' header afterHeader hdr afterHdr literals afterLiterals huffTree
    modes afterSeqHeader hframe hh hparse hbs hws htype hblockEnd hlit hseq hlast
  subst hcontent
  exact decompressZstd_single_frame data output pos' hframe hend

/-- When the input contains exactly one standard Zstd frame at position 0 with a
    single last compressed block having sequences (numSeq > 0), `decompressZstd`
    returns the sequence execution result.  Composes
    `decompressFrame_single_compressed_sequences_content` with
    `decompressZstd_single_frame`. -/
theorem decompressZstd_single_compressed_sequences (data : ByteArray)
    (output : ByteArray) (pos' : Nat)
    (header : Zip.Native.ZstdFrameHeader) (afterHeader : Nat)
    (hdr : Zip.Native.ZstdBlockHeader) (afterHdr : Nat)
    (literals : ByteArray) (afterLiterals : Nat)
    (huffTree : Option Zip.Native.ZstdHuffmanTable)
    (numSeq : Nat) (modes : Zip.Native.SequenceCompressionModes) (afterSeqHeader : Nat)
    (llTable ofTable mlTable : Zip.Native.FseTable) (afterTables : Nat)
    (bbr : Zip.Native.BackwardBitReader)
    (sequences : Array Zip.Native.ZstdSequence)
    (blockOutput : ByteArray) (newHist : Array Nat)
    (hframe : Zip.Native.decompressFrame data 0 = .ok (output, pos'))
    (hh : Zip.Native.parseFrameHeader data 0 = .ok (header, afterHeader))
    (hparse : Zip.Native.parseBlockHeader data afterHeader = .ok (hdr, afterHdr))
    (hbs : ¬ hdr.blockSize > 131072)
    (hws : ¬ (header.windowSize > 0 && hdr.blockSize.toUInt64 > header.windowSize))
    (htype : hdr.blockType = .compressed)
    (hblockEnd : ¬ data.size < afterHdr + hdr.blockSize.toNat)
    (hlit : Zip.Native.parseLiteralsSection data afterHdr none
              = .ok (literals, afterLiterals, huffTree))
    (hseq : Zip.Native.parseSequencesHeader data afterLiterals
              = .ok (numSeq, modes, afterSeqHeader))
    (hNumSeq : ¬ numSeq == 0)
    (hfse : Zip.Native.resolveSequenceFseTables modes data afterSeqHeader {}
              = .ok (llTable, ofTable, mlTable, afterTables))
    (hbbr : Zip.Native.BackwardBitReader.init data afterTables
              (afterHdr + hdr.blockSize.toNat) = .ok bbr)
    (hdec : Zip.Native.decodeSequences llTable ofTable mlTable bbr numSeq
              = .ok sequences)
    (hexec : Zip.Native.executeSequences sequences literals ByteArray.empty
               #[1, 4, 8] header.windowSize.toNat
               = .ok (blockOutput, newHist))
    (hlast : hdr.lastBlock = true)
    (hend : pos' ≥ data.size) :
    Zip.Native.decompressZstd data = .ok blockOutput := by
  have hcontent := Zstd.Spec.decompressFrame_single_compressed_sequences_content data 0
    output pos' header afterHeader hdr afterHdr literals afterLiterals huffTree
    numSeq modes afterSeqHeader llTable ofTable mlTable afterTables bbr sequences
    blockOutput newHist hframe hh hparse hbs hws htype hblockEnd hlit hseq
    hNumSeq hfse hbbr hdec hexec hlast
  subst hcontent
  exact decompressZstd_single_frame data output pos' hframe hend

/-! ## API-level two-block content (mixed compressed) -/

/-- When the input contains exactly one standard Zstd frame at position 0 with two
    blocks (first non-last compressed with numSeq=0, second last raw), `decompressZstd`
    returns `literals1 ++ block2`.  Composes
    `decompressFrame_compressed_lit_then_raw_content` with
    `decompressZstd_single_frame`. -/
theorem decompressZstd_compressed_lit_then_raw_content (data : ByteArray)
    (output : ByteArray) (pos' : Nat)
    (header : Zip.Native.ZstdFrameHeader) (afterHeader : Nat)
    -- Block 1 (non-last compressed, numSeq=0)
    (hdr1 : Zip.Native.ZstdBlockHeader) (afterHdr1 : Nat)
    (literals1 : ByteArray) (afterLiterals1 : Nat)
    (huffTree1 : Option Zip.Native.ZstdHuffmanTable)
    (modes1 : Zip.Native.SequenceCompressionModes) (afterSeqHeader1 : Nat)
    -- Block 2 (last raw)
    (hdr2 : Zip.Native.ZstdBlockHeader) (afterHdr2 : Nat)
    (block2 : ByteArray) (afterBlock2 : Nat)
    -- Frame hypotheses
    (hframe : Zip.Native.decompressFrame data 0 = .ok (output, pos'))
    (hh : Zip.Native.parseFrameHeader data 0 = .ok (header, afterHeader))
    -- Block 1 hypotheses (compressed, non-last)
    (hparse1 : Zip.Native.parseBlockHeader data afterHeader = .ok (hdr1, afterHdr1))
    (hbs1 : ¬ hdr1.blockSize > 131072)
    (hws1 : ¬ (header.windowSize > 0 && hdr1.blockSize.toUInt64 > header.windowSize))
    (htype1 : hdr1.blockType = .compressed)
    (hblockEnd1 : ¬ data.size < afterHdr1 + hdr1.blockSize.toNat)
    (hlit1 : Zip.Native.parseLiteralsSection data afterHdr1 none
               = .ok (literals1, afterLiterals1, huffTree1))
    (hseq1 : Zip.Native.parseSequencesHeader data afterLiterals1
               = .ok (0, modes1, afterSeqHeader1))
    (hnotlast1 : hdr1.lastBlock = false)
    (hadv1 : ¬ afterHdr1 + hdr1.blockSize.toNat ≤ afterHeader)
    -- Block 2 hypotheses (raw, last)
    (hoff2 : ¬ data.size ≤ afterHdr1 + hdr1.blockSize.toNat)
    (hparse2 : Zip.Native.parseBlockHeader data (afterHdr1 + hdr1.blockSize.toNat)
                 = .ok (hdr2, afterHdr2))
    (hbs2 : ¬ hdr2.blockSize > 131072)
    (hws2 : ¬ (header.windowSize > 0 && hdr2.blockSize.toUInt64 > header.windowSize))
    (htype2 : hdr2.blockType = .raw)
    (hraw2 : Zip.Native.decompressRawBlock data afterHdr2 hdr2.blockSize
               = .ok (block2, afterBlock2))
    (hlast2 : hdr2.lastBlock = true)
    -- End of data
    (hend : pos' ≥ data.size) :
    Zip.Native.decompressZstd data = .ok (literals1 ++ block2) := by
  have hcontent := Zstd.Spec.decompressFrame_compressed_lit_then_raw_content data 0 output pos'
    header afterHeader hdr1 afterHdr1 literals1 afterLiterals1 huffTree1
    modes1 afterSeqHeader1 hdr2 afterHdr2 block2 afterBlock2
    hframe hh hparse1 hbs1 hws1 htype1 hblockEnd1 hlit1 hseq1 hnotlast1 hadv1
    hoff2 hparse2 hbs2 hws2 htype2 hraw2 hlast2
  subst hcontent
  exact decompressZstd_single_frame data (literals1 ++ block2) pos' hframe hend

/-- When the input contains exactly one standard Zstd frame at position 0 with two
    blocks (first non-last compressed with numSeq=0, second last RLE), `decompressZstd`
    returns `literals1 ++ block2`.  Composes
    `decompressFrame_compressed_lit_then_rle_content` with
    `decompressZstd_single_frame`. -/
theorem decompressZstd_compressed_lit_then_rle_content (data : ByteArray)
    (output : ByteArray) (pos' : Nat)
    (header : Zip.Native.ZstdFrameHeader) (afterHeader : Nat)
    -- Block 1 (non-last compressed, numSeq=0)
    (hdr1 : Zip.Native.ZstdBlockHeader) (afterHdr1 : Nat)
    (literals1 : ByteArray) (afterLiterals1 : Nat)
    (huffTree1 : Option Zip.Native.ZstdHuffmanTable)
    (modes1 : Zip.Native.SequenceCompressionModes) (afterSeqHeader1 : Nat)
    -- Block 2 (last RLE)
    (hdr2 : Zip.Native.ZstdBlockHeader) (afterHdr2 : Nat)
    (block2 : ByteArray) (afterByte2 : Nat)
    -- Frame hypotheses
    (hframe : Zip.Native.decompressFrame data 0 = .ok (output, pos'))
    (hh : Zip.Native.parseFrameHeader data 0 = .ok (header, afterHeader))
    -- Block 1 hypotheses (compressed, non-last)
    (hparse1 : Zip.Native.parseBlockHeader data afterHeader = .ok (hdr1, afterHdr1))
    (hbs1 : ¬ hdr1.blockSize > 131072)
    (hws1 : ¬ (header.windowSize > 0 && hdr1.blockSize.toUInt64 > header.windowSize))
    (htype1 : hdr1.blockType = .compressed)
    (hblockEnd1 : ¬ data.size < afterHdr1 + hdr1.blockSize.toNat)
    (hlit1 : Zip.Native.parseLiteralsSection data afterHdr1 none
               = .ok (literals1, afterLiterals1, huffTree1))
    (hseq1 : Zip.Native.parseSequencesHeader data afterLiterals1
               = .ok (0, modes1, afterSeqHeader1))
    (hnotlast1 : hdr1.lastBlock = false)
    (hadv1 : ¬ afterHdr1 + hdr1.blockSize.toNat ≤ afterHeader)
    -- Block 2 hypotheses (RLE, last)
    (hoff2 : ¬ data.size ≤ afterHdr1 + hdr1.blockSize.toNat)
    (hparse2 : Zip.Native.parseBlockHeader data (afterHdr1 + hdr1.blockSize.toNat)
                 = .ok (hdr2, afterHdr2))
    (hbs2 : ¬ hdr2.blockSize > 131072)
    (hws2 : ¬ (header.windowSize > 0 && hdr2.blockSize.toUInt64 > header.windowSize))
    (htype2 : hdr2.blockType = .rle)
    (hrle2 : Zip.Native.decompressRLEBlock data afterHdr2 hdr2.blockSize
               = .ok (block2, afterByte2))
    (hlast2 : hdr2.lastBlock = true)
    -- End of data
    (hend : pos' ≥ data.size) :
    Zip.Native.decompressZstd data = .ok (literals1 ++ block2) := by
  have hcontent := Zstd.Spec.decompressFrame_compressed_lit_then_rle_content data 0 output pos'
    header afterHeader hdr1 afterHdr1 literals1 afterLiterals1 huffTree1
    modes1 afterSeqHeader1 hdr2 afterHdr2 block2 afterByte2
    hframe hh hparse1 hbs1 hws1 htype1 hblockEnd1 hlit1 hseq1 hnotlast1 hadv1
    hoff2 hparse2 hbs2 hws2 htype2 hrle2 hlast2
  subst hcontent
  exact decompressZstd_single_frame data (literals1 ++ block2) pos' hframe hend

/-- When the input contains exactly one standard Zstd frame at position 0 with two
    blocks (first non-last compressed with numSeq>0, second last compressed with
    numSeq=0), `decompressZstd` returns `blockOutput1 ++ literals2`.  Composes
    `decompressFrame_compressed_seq_then_compressed_lit_content` with
    `decompressZstd_single_frame`. -/
theorem decompressZstd_compressed_seq_then_compressed_lit_content (data : ByteArray)
    (output : ByteArray) (pos' : Nat)
    (header : Zip.Native.ZstdFrameHeader) (afterHeader : Nat)
    -- Block 1 (non-last compressed, numSeq > 0)
    (hdr1 : Zip.Native.ZstdBlockHeader) (afterHdr1 : Nat)
    (literals1 : ByteArray) (afterLiterals1 : Nat)
    (huffTree1 : Option Zip.Native.ZstdHuffmanTable)
    (numSeq1 : Nat) (modes1 : Zip.Native.SequenceCompressionModes) (afterSeqHeader1 : Nat)
    (llTable1 ofTable1 mlTable1 : Zip.Native.FseTable) (afterTables1 : Nat)
    (bbr1 : Zip.Native.BackwardBitReader)
    (sequences1 : Array Zip.Native.ZstdSequence)
    (blockOutput1 : ByteArray) (newHist1 : Array Nat)
    -- Block 2 (last compressed, numSeq=0)
    (hdr2 : Zip.Native.ZstdBlockHeader) (afterHdr2 : Nat)
    (literals2 : ByteArray) (afterLiterals2 : Nat)
    (huffTree2 : Option Zip.Native.ZstdHuffmanTable)
    (modes2 : Zip.Native.SequenceCompressionModes) (afterSeqHeader2 : Nat)
    -- Frame hypotheses
    (hframe : Zip.Native.decompressFrame data 0 = .ok (output, pos'))
    (hh : Zip.Native.parseFrameHeader data 0 = .ok (header, afterHeader))
    -- Block 1 hypotheses (compressed, non-last, numSeq > 0)
    (hparse1 : Zip.Native.parseBlockHeader data afterHeader = .ok (hdr1, afterHdr1))
    (hbs1 : ¬ hdr1.blockSize > 131072)
    (hws1 : ¬ (header.windowSize > 0 && hdr1.blockSize.toUInt64 > header.windowSize))
    (htype1 : hdr1.blockType = .compressed)
    (hblockEnd1 : ¬ data.size < afterHdr1 + hdr1.blockSize.toNat)
    (hlit1 : Zip.Native.parseLiteralsSection data afterHdr1 none
               = .ok (literals1, afterLiterals1, huffTree1))
    (hseq1 : Zip.Native.parseSequencesHeader data afterLiterals1
               = .ok (numSeq1, modes1, afterSeqHeader1))
    (hNumSeq1 : ¬ numSeq1 == 0)
    (hfse1 : Zip.Native.resolveSequenceFseTables modes1 data afterSeqHeader1 {}
               = .ok (llTable1, ofTable1, mlTable1, afterTables1))
    (hbbr1 : Zip.Native.BackwardBitReader.init data afterTables1
               (afterHdr1 + hdr1.blockSize.toNat) = .ok bbr1)
    (hdec1 : Zip.Native.decodeSequences llTable1 ofTable1 mlTable1 bbr1 numSeq1
               = .ok sequences1)
    (hexec1 : Zip.Native.executeSequences sequences1 literals1 ByteArray.empty
                #[1, 4, 8] header.windowSize.toNat
                = .ok (blockOutput1, newHist1))
    (hnotlast1 : hdr1.lastBlock = false)
    (hadv1 : ¬ (afterHdr1 + hdr1.blockSize.toNat) ≤ afterHeader)
    -- Block 2 hypotheses (compressed, last, numSeq=0)
    (hoff2 : ¬ data.size ≤ afterHdr1 + hdr1.blockSize.toNat)
    (hparse2 : Zip.Native.parseBlockHeader data (afterHdr1 + hdr1.blockSize.toNat)
                 = .ok (hdr2, afterHdr2))
    (hbs2 : ¬ hdr2.blockSize > 131072)
    (hws2 : ¬ (header.windowSize > 0 && hdr2.blockSize.toUInt64 > header.windowSize))
    (htype2 : hdr2.blockType = .compressed)
    (hblockEnd2 : ¬ data.size < afterHdr2 + hdr2.blockSize.toNat)
    (hlit2 : Zip.Native.parseLiteralsSection data afterHdr2 huffTree1
               = .ok (literals2, afterLiterals2, huffTree2))
    (hseq2 : Zip.Native.parseSequencesHeader data afterLiterals2
               = .ok (0, modes2, afterSeqHeader2))
    (hlast2 : hdr2.lastBlock = true)
    -- End of data
    (hend : pos' ≥ data.size) :
    Zip.Native.decompressZstd data = .ok (blockOutput1 ++ literals2) := by
  have hcontent := Zstd.Spec.decompressFrame_compressed_seq_then_compressed_lit_content data 0
    output pos' header afterHeader hdr1 afterHdr1 literals1 afterLiterals1 huffTree1
    numSeq1 modes1 afterSeqHeader1 llTable1 ofTable1 mlTable1 afterTables1 bbr1 sequences1
    blockOutput1 newHist1 hdr2 afterHdr2 literals2 afterLiterals2 huffTree2 modes2
    afterSeqHeader2 hframe hh hparse1 hbs1 hws1 htype1 hblockEnd1 hlit1 hseq1
    hNumSeq1 hfse1 hbbr1 hdec1 hexec1 hnotlast1 hadv1 hoff2 hparse2 hbs2 hws2 htype2
    hblockEnd2 hlit2 hseq2 hlast2
  subst hcontent
  exact decompressZstd_single_frame data (blockOutput1 ++ literals2) pos' hframe hend

/-- When the input contains exactly one standard Zstd frame at position 0 with two
    blocks (first non-last compressed with numSeq=0, second last compressed with
    numSeq>0), `decompressZstd` returns `literals1 ++ blockOutput2`.  Composes
    `decompressFrame_compressed_lit_then_compressed_seq_content` with
    `decompressZstd_single_frame`. -/
theorem decompressZstd_compressed_lit_then_compressed_seq_content (data : ByteArray)
    (output : ByteArray) (pos' : Nat)
    (header : Zip.Native.ZstdFrameHeader) (afterHeader : Nat)
    -- Block 1 (non-last compressed, numSeq=0)
    (hdr1 : Zip.Native.ZstdBlockHeader) (afterHdr1 : Nat)
    (literals1 : ByteArray) (afterLiterals1 : Nat)
    (huffTree1 : Option Zip.Native.ZstdHuffmanTable)
    (modes1 : Zip.Native.SequenceCompressionModes) (afterSeqHeader1 : Nat)
    -- Block 2 (last compressed, numSeq > 0)
    (hdr2 : Zip.Native.ZstdBlockHeader) (afterHdr2 : Nat)
    (literals2 : ByteArray) (afterLiterals2 : Nat)
    (huffTree2 : Option Zip.Native.ZstdHuffmanTable)
    (numSeq2 : Nat) (modes2 : Zip.Native.SequenceCompressionModes) (afterSeqHeader2 : Nat)
    (llTable2 ofTable2 mlTable2 : Zip.Native.FseTable) (afterTables2 : Nat)
    (bbr2 : Zip.Native.BackwardBitReader)
    (sequences2 : Array Zip.Native.ZstdSequence)
    (blockOutput2 : ByteArray) (newHist2 : Array Nat)
    -- Frame hypotheses
    (hframe : Zip.Native.decompressFrame data 0 = .ok (output, pos'))
    (hh : Zip.Native.parseFrameHeader data 0 = .ok (header, afterHeader))
    -- Block 1 hypotheses (compressed, non-last, numSeq=0)
    (hparse1 : Zip.Native.parseBlockHeader data afterHeader = .ok (hdr1, afterHdr1))
    (hbs1 : ¬ hdr1.blockSize > 131072)
    (hws1 : ¬ (header.windowSize > 0 && hdr1.blockSize.toUInt64 > header.windowSize))
    (htype1 : hdr1.blockType = .compressed)
    (hblockEnd1 : ¬ data.size < afterHdr1 + hdr1.blockSize.toNat)
    (hlit1 : Zip.Native.parseLiteralsSection data afterHdr1 none
               = .ok (literals1, afterLiterals1, huffTree1))
    (hseq1 : Zip.Native.parseSequencesHeader data afterLiterals1
               = .ok (0, modes1, afterSeqHeader1))
    (hnotlast1 : hdr1.lastBlock = false)
    (hadv1 : ¬ afterHdr1 + hdr1.blockSize.toNat ≤ afterHeader)
    -- Block 2 hypotheses (compressed, last, numSeq > 0)
    (hoff2 : ¬ data.size ≤ afterHdr1 + hdr1.blockSize.toNat)
    (hparse2 : Zip.Native.parseBlockHeader data (afterHdr1 + hdr1.blockSize.toNat)
                 = .ok (hdr2, afterHdr2))
    (hbs2 : ¬ hdr2.blockSize > 131072)
    (hws2 : ¬ (header.windowSize > 0 && hdr2.blockSize.toUInt64 > header.windowSize))
    (htype2 : hdr2.blockType = .compressed)
    (hblockEnd2 : ¬ data.size < afterHdr2 + hdr2.blockSize.toNat)
    (hlit2 : Zip.Native.parseLiteralsSection data afterHdr2 huffTree1
               = .ok (literals2, afterLiterals2, huffTree2))
    (hseq2 : Zip.Native.parseSequencesHeader data afterLiterals2
               = .ok (numSeq2, modes2, afterSeqHeader2))
    (hNumSeq2 : ¬ numSeq2 == 0)
    (hfse2 : Zip.Native.resolveSequenceFseTables modes2 data afterSeqHeader2 {}
               = .ok (llTable2, ofTable2, mlTable2, afterTables2))
    (hbbr2 : Zip.Native.BackwardBitReader.init data afterTables2
               (afterHdr2 + hdr2.blockSize.toNat) = .ok bbr2)
    (hdec2 : Zip.Native.decodeSequences llTable2 ofTable2 mlTable2 bbr2 numSeq2
               = .ok sequences2)
    (hexec2 : Zip.Native.executeSequences sequences2 literals2
                (if header.windowSize > 0 && literals1.size > header.windowSize.toNat
                 then literals1.extract (literals1.size - header.windowSize.toNat)
                        literals1.size
                 else literals1)
                #[1, 4, 8] header.windowSize.toNat
                = .ok (blockOutput2, newHist2))
    (hlast2 : hdr2.lastBlock = true)
    -- End of data
    (hend : pos' ≥ data.size) :
    Zip.Native.decompressZstd data = .ok (literals1 ++ blockOutput2) := by
  have hcontent := Zstd.Spec.decompressFrame_compressed_lit_then_compressed_seq_content data 0
    output pos' header afterHeader hdr1 afterHdr1 literals1 afterLiterals1 huffTree1
    modes1 afterSeqHeader1 hdr2 afterHdr2 literals2 afterLiterals2 huffTree2
    numSeq2 modes2 afterSeqHeader2 llTable2 ofTable2 mlTable2 afterTables2 bbr2 sequences2
    blockOutput2 newHist2 hframe hh hparse1 hbs1 hws1 htype1 hblockEnd1 hlit1 hseq1
    hnotlast1 hadv1 hoff2 hparse2 hbs2 hws2 htype2 hblockEnd2 hlit2 hseq2 hNumSeq2
    hfse2 hbbr2 hdec2 hexec2 hlast2
  subst hcontent
  exact decompressZstd_single_frame data (literals1 ++ blockOutput2) pos' hframe hend

/-- When the input contains exactly one standard Zstd frame at position 0 with two
    compressed blocks both having numSeq=0 (literals-only), `decompressZstd` returns
    `literals1 ++ literals2`.  Composes
    `decompressFrame_two_compressed_literals_blocks_content` with
    `decompressZstd_single_frame`. -/
theorem decompressZstd_two_compressed_literals_blocks_content (data : ByteArray)
    (output : ByteArray) (pos' : Nat)
    (header : Zip.Native.ZstdFrameHeader) (afterHeader : Nat)
    -- Block 1 (non-last compressed, numSeq=0)
    (hdr1 : Zip.Native.ZstdBlockHeader) (afterHdr1 : Nat)
    (literals1 : ByteArray) (afterLiterals1 : Nat)
    (huffTree1 : Option Zip.Native.ZstdHuffmanTable)
    (modes1 : Zip.Native.SequenceCompressionModes) (afterSeqHeader1 : Nat)
    -- Block 2 (last compressed, numSeq=0)
    (hdr2 : Zip.Native.ZstdBlockHeader) (afterHdr2 : Nat)
    (literals2 : ByteArray) (afterLiterals2 : Nat)
    (huffTree2 : Option Zip.Native.ZstdHuffmanTable)
    (modes2 : Zip.Native.SequenceCompressionModes) (afterSeqHeader2 : Nat)
    -- Frame hypotheses
    (hframe : Zip.Native.decompressFrame data 0 = .ok (output, pos'))
    (hh : Zip.Native.parseFrameHeader data 0 = .ok (header, afterHeader))
    -- Block 1 hypotheses (compressed, non-last)
    (hparse1 : Zip.Native.parseBlockHeader data afterHeader = .ok (hdr1, afterHdr1))
    (hbs1 : ¬ hdr1.blockSize > 131072)
    (hws1 : ¬ (header.windowSize > 0 && hdr1.blockSize.toUInt64 > header.windowSize))
    (htype1 : hdr1.blockType = .compressed)
    (hblockEnd1 : ¬ data.size < afterHdr1 + hdr1.blockSize.toNat)
    (hlit1 : Zip.Native.parseLiteralsSection data afterHdr1 none
               = .ok (literals1, afterLiterals1, huffTree1))
    (hseq1 : Zip.Native.parseSequencesHeader data afterLiterals1
               = .ok (0, modes1, afterSeqHeader1))
    (hnotlast1 : hdr1.lastBlock = false)
    (hadv1 : ¬ afterHdr1 + hdr1.blockSize.toNat ≤ afterHeader)
    -- Block 2 hypotheses (compressed, last)
    (hoff2 : ¬ data.size ≤ afterHdr1 + hdr1.blockSize.toNat)
    (hparse2 : Zip.Native.parseBlockHeader data (afterHdr1 + hdr1.blockSize.toNat)
                 = .ok (hdr2, afterHdr2))
    (hbs2 : ¬ hdr2.blockSize > 131072)
    (hws2 : ¬ (header.windowSize > 0 && hdr2.blockSize.toUInt64 > header.windowSize))
    (htype2 : hdr2.blockType = .compressed)
    (hblockEnd2 : ¬ data.size < afterHdr2 + hdr2.blockSize.toNat)
    (hlit2 : Zip.Native.parseLiteralsSection data afterHdr2
               (if let some ht := huffTree1 then some ht else none)
               = .ok (literals2, afterLiterals2, huffTree2))
    (hseq2 : Zip.Native.parseSequencesHeader data afterLiterals2
               = .ok (0, modes2, afterSeqHeader2))
    (hlast2 : hdr2.lastBlock = true)
    -- End of data
    (hend : pos' ≥ data.size) :
    Zip.Native.decompressZstd data = .ok (literals1 ++ literals2) := by
  have hcontent := Zstd.Spec.decompressFrame_two_compressed_literals_blocks_content data 0
    output pos' header afterHeader hdr1 afterHdr1 literals1 afterLiterals1 huffTree1
    modes1 afterSeqHeader1 hdr2 afterHdr2 literals2 afterLiterals2 huffTree2 modes2
    afterSeqHeader2 hframe hh hparse1 hbs1 hws1 htype1 hblockEnd1 hlit1 hseq1
    hnotlast1 hadv1 hoff2 hparse2 hbs2 hws2 htype2 hblockEnd2 hlit2 hseq2 hlast2
  subst hcontent
  exact decompressZstd_single_frame data (literals1 ++ literals2) pos' hframe hend

/-- When the input contains exactly one standard Zstd frame at position 0 with two
    compressed blocks both having numSeq>0 (sequences), `decompressZstd` returns
    `blockOutput1 ++ blockOutput2`.  Composes
    `decompressFrame_two_compressed_sequences_blocks_content` with
    `decompressZstd_single_frame`. -/
theorem decompressZstd_two_compressed_sequences_blocks_content (data : ByteArray)
    (output : ByteArray) (pos' : Nat)
    (header : Zip.Native.ZstdFrameHeader) (afterHeader : Nat)
    -- Block 1 (non-last compressed, numSeq > 0)
    (hdr1 : Zip.Native.ZstdBlockHeader) (afterHdr1 : Nat)
    (literals1 : ByteArray) (afterLiterals1 : Nat)
    (huffTree1 : Option Zip.Native.ZstdHuffmanTable)
    (numSeq1 : Nat) (modes1 : Zip.Native.SequenceCompressionModes) (afterSeqHeader1 : Nat)
    (llTable1 ofTable1 mlTable1 : Zip.Native.FseTable) (afterTables1 : Nat)
    (bbr1 : Zip.Native.BackwardBitReader)
    (sequences1 : Array Zip.Native.ZstdSequence)
    (blockOutput1 : ByteArray) (newHist1 : Array Nat)
    -- Block 2 (last compressed, numSeq > 0)
    (hdr2 : Zip.Native.ZstdBlockHeader) (afterHdr2 : Nat)
    (literals2 : ByteArray) (afterLiterals2 : Nat)
    (huffTree2 : Option Zip.Native.ZstdHuffmanTable)
    (numSeq2 : Nat) (modes2 : Zip.Native.SequenceCompressionModes) (afterSeqHeader2 : Nat)
    (llTable2 ofTable2 mlTable2 : Zip.Native.FseTable) (afterTables2 : Nat)
    (bbr2 : Zip.Native.BackwardBitReader)
    (sequences2 : Array Zip.Native.ZstdSequence)
    (blockOutput2 : ByteArray) (newHist2 : Array Nat)
    -- Frame hypotheses
    (hframe : Zip.Native.decompressFrame data 0 = .ok (output, pos'))
    (hh : Zip.Native.parseFrameHeader data 0 = .ok (header, afterHeader))
    -- Block 1 hypotheses (compressed, non-last, numSeq > 0)
    (hparse1 : Zip.Native.parseBlockHeader data afterHeader = .ok (hdr1, afterHdr1))
    (hbs1 : ¬ hdr1.blockSize > 131072)
    (hws1 : ¬ (header.windowSize > 0 && hdr1.blockSize.toUInt64 > header.windowSize))
    (htype1 : hdr1.blockType = .compressed)
    (hblockEnd1 : ¬ data.size < afterHdr1 + hdr1.blockSize.toNat)
    (hlit1 : Zip.Native.parseLiteralsSection data afterHdr1 none
               = .ok (literals1, afterLiterals1, huffTree1))
    (hseq1 : Zip.Native.parseSequencesHeader data afterLiterals1
               = .ok (numSeq1, modes1, afterSeqHeader1))
    (hNumSeq1 : ¬ numSeq1 == 0)
    (hfse1 : Zip.Native.resolveSequenceFseTables modes1 data afterSeqHeader1 {}
               = .ok (llTable1, ofTable1, mlTable1, afterTables1))
    (hbbr1 : Zip.Native.BackwardBitReader.init data afterTables1
               (afterHdr1 + hdr1.blockSize.toNat) = .ok bbr1)
    (hdec1 : Zip.Native.decodeSequences llTable1 ofTable1 mlTable1 bbr1 numSeq1
               = .ok sequences1)
    (hexec1 : Zip.Native.executeSequences sequences1 literals1 ByteArray.empty
                #[1, 4, 8] header.windowSize.toNat
                = .ok (blockOutput1, newHist1))
    (hnotlast1 : hdr1.lastBlock = false)
    (hadv1 : ¬ (afterHdr1 + hdr1.blockSize.toNat) ≤ afterHeader)
    -- Block 2 hypotheses (compressed, last, numSeq > 0)
    (hoff2 : ¬ data.size ≤ afterHdr1 + hdr1.blockSize.toNat)
    (hparse2 : Zip.Native.parseBlockHeader data (afterHdr1 + hdr1.blockSize.toNat)
                 = .ok (hdr2, afterHdr2))
    (hbs2 : ¬ hdr2.blockSize > 131072)
    (hws2 : ¬ (header.windowSize > 0 && hdr2.blockSize.toUInt64 > header.windowSize))
    (htype2 : hdr2.blockType = .compressed)
    (hblockEnd2 : ¬ data.size < afterHdr2 + hdr2.blockSize.toNat)
    (hlit2 : Zip.Native.parseLiteralsSection data afterHdr2 huffTree1
               = .ok (literals2, afterLiterals2, huffTree2))
    (hseq2 : Zip.Native.parseSequencesHeader data afterLiterals2
               = .ok (numSeq2, modes2, afterSeqHeader2))
    (hNumSeq2 : ¬ numSeq2 == 0)
    (hfse2 : Zip.Native.resolveSequenceFseTables modes2 data afterSeqHeader2
               { litLen := some llTable1, offset := some ofTable1, matchLen := some mlTable1 }
               = .ok (llTable2, ofTable2, mlTable2, afterTables2))
    (hbbr2 : Zip.Native.BackwardBitReader.init data afterTables2
               (afterHdr2 + hdr2.blockSize.toNat) = .ok bbr2)
    (hdec2 : Zip.Native.decodeSequences llTable2 ofTable2 mlTable2 bbr2 numSeq2
               = .ok sequences2)
    (hexec2 : Zip.Native.executeSequences sequences2 literals2
                (if header.windowSize > 0 && blockOutput1.size > header.windowSize.toNat
                 then blockOutput1.extract (blockOutput1.size - header.windowSize.toNat)
                        blockOutput1.size
                 else blockOutput1)
                newHist1 header.windowSize.toNat
                = .ok (blockOutput2, newHist2))
    (hlast2 : hdr2.lastBlock = true)
    -- End of data
    (hend : pos' ≥ data.size) :
    Zip.Native.decompressZstd data = .ok (blockOutput1 ++ blockOutput2) := by
  have hcontent := Zstd.Spec.decompressFrame_two_compressed_sequences_blocks_content data 0
    output pos' header afterHeader hdr1 afterHdr1 literals1 afterLiterals1 huffTree1
    numSeq1 modes1 afterSeqHeader1 llTable1 ofTable1 mlTable1 afterTables1 bbr1 sequences1
    blockOutput1 newHist1 hdr2 afterHdr2 literals2 afterLiterals2 huffTree2
    numSeq2 modes2 afterSeqHeader2 llTable2 ofTable2 mlTable2 afterTables2 bbr2 sequences2
    blockOutput2 newHist2 hframe hh hparse1 hbs1 hws1 htype1 hblockEnd1 hlit1 hseq1
    hNumSeq1 hfse1 hbbr1 hdec1 hexec1 hnotlast1 hadv1 hoff2 hparse2 hbs2 hws2 htype2
    hblockEnd2 hlit2 hseq2 hNumSeq2 hfse2 hbbr2 hdec2 hexec2 hlast2
  subst hcontent
  exact decompressZstd_single_frame data (blockOutput1 ++ blockOutput2) pos' hframe hend

/-- When the input contains exactly one standard Zstd frame at position 0 with two
    blocks (first non-last raw, second last compressed with numSeq=0), `decompressZstd`
    returns `block1 ++ literals2`.  Composes
    `decompressFrame_raw_then_compressed_lit_content` with
    `decompressZstd_single_frame`. -/
theorem decompressZstd_raw_then_compressed_lit_content (data : ByteArray)
    (output : ByteArray) (pos' : Nat)
    (header : Zip.Native.ZstdFrameHeader) (afterHeader : Nat)
    -- Block 1 (non-last raw)
    (hdr1 : Zip.Native.ZstdBlockHeader) (afterHdr1 : Nat)
    (block1 : ByteArray) (afterBlock1 : Nat)
    -- Block 2 (last compressed, numSeq=0)
    (hdr2 : Zip.Native.ZstdBlockHeader) (afterHdr2 : Nat)
    (literals2 : ByteArray) (afterLiterals2 : Nat)
    (huffTree2 : Option Zip.Native.ZstdHuffmanTable)
    (modes2 : Zip.Native.SequenceCompressionModes) (afterSeqHeader2 : Nat)
    -- Frame hypotheses
    (hframe : Zip.Native.decompressFrame data 0 = .ok (output, pos'))
    (hh : Zip.Native.parseFrameHeader data 0 = .ok (header, afterHeader))
    -- Block 1 hypotheses (raw, non-last)
    (hparse1 : Zip.Native.parseBlockHeader data afterHeader = .ok (hdr1, afterHdr1))
    (hbs1 : ¬ hdr1.blockSize > 131072)
    (hws1 : ¬ (header.windowSize > 0 && hdr1.blockSize.toUInt64 > header.windowSize))
    (htype1 : hdr1.blockType = .raw)
    (hraw1 : Zip.Native.decompressRawBlock data afterHdr1 hdr1.blockSize
               = .ok (block1, afterBlock1))
    (hnotlast1 : hdr1.lastBlock = false)
    (hadv1 : ¬ afterBlock1 ≤ afterHeader)
    -- Block 2 hypotheses (compressed, last, numSeq=0)
    (hoff2 : ¬ data.size ≤ afterBlock1)
    (hparse2 : Zip.Native.parseBlockHeader data afterBlock1 = .ok (hdr2, afterHdr2))
    (hbs2 : ¬ hdr2.blockSize > 131072)
    (hws2 : ¬ (header.windowSize > 0 && hdr2.blockSize.toUInt64 > header.windowSize))
    (htype2 : hdr2.blockType = .compressed)
    (hblockEnd2 : ¬ data.size < afterHdr2 + hdr2.blockSize.toNat)
    (hlit2 : Zip.Native.parseLiteralsSection data afterHdr2 none
               = .ok (literals2, afterLiterals2, huffTree2))
    (hseq2 : Zip.Native.parseSequencesHeader data afterLiterals2
               = .ok (0, modes2, afterSeqHeader2))
    (hlast2 : hdr2.lastBlock = true)
    -- End of data
    (hend : pos' ≥ data.size) :
    Zip.Native.decompressZstd data = .ok (block1 ++ literals2) := by
  have hcontent := Zstd.Spec.decompressFrame_raw_then_compressed_lit_content data 0 output pos'
    header afterHeader hdr1 afterHdr1 block1 afterBlock1 hdr2 afterHdr2 literals2 afterLiterals2
    huffTree2 modes2 afterSeqHeader2
    hframe hh hparse1 hbs1 hws1 htype1 hraw1 hnotlast1 hadv1
    hoff2 hparse2 hbs2 hws2 htype2 hblockEnd2 hlit2 hseq2 hlast2
  subst hcontent
  exact decompressZstd_single_frame data (block1 ++ literals2) pos' hframe hend

/-- When the input contains exactly one standard Zstd frame at position 0 with two
    blocks (first non-last RLE, second last compressed with numSeq=0), `decompressZstd`
    returns `block1 ++ literals2`.  Composes
    `decompressFrame_rle_then_compressed_lit_content` with
    `decompressZstd_single_frame`. -/
theorem decompressZstd_rle_then_compressed_lit_content (data : ByteArray)
    (output : ByteArray) (pos' : Nat)
    (header : Zip.Native.ZstdFrameHeader) (afterHeader : Nat)
    -- Block 1 (non-last RLE)
    (hdr1 : Zip.Native.ZstdBlockHeader) (afterHdr1 : Nat)
    (block1 : ByteArray) (afterByte1 : Nat)
    -- Block 2 (last compressed, numSeq=0)
    (hdr2 : Zip.Native.ZstdBlockHeader) (afterHdr2 : Nat)
    (literals2 : ByteArray) (afterLiterals2 : Nat)
    (huffTree2 : Option Zip.Native.ZstdHuffmanTable)
    (modes2 : Zip.Native.SequenceCompressionModes) (afterSeqHeader2 : Nat)
    -- Frame hypotheses
    (hframe : Zip.Native.decompressFrame data 0 = .ok (output, pos'))
    (hh : Zip.Native.parseFrameHeader data 0 = .ok (header, afterHeader))
    -- Block 1 hypotheses (RLE, non-last)
    (hparse1 : Zip.Native.parseBlockHeader data afterHeader = .ok (hdr1, afterHdr1))
    (hbs1 : ¬ hdr1.blockSize > 131072)
    (hws1 : ¬ (header.windowSize > 0 && hdr1.blockSize.toUInt64 > header.windowSize))
    (htype1 : hdr1.blockType = .rle)
    (hrle1 : Zip.Native.decompressRLEBlock data afterHdr1 hdr1.blockSize
               = .ok (block1, afterByte1))
    (hnotlast1 : hdr1.lastBlock = false)
    (hadv1 : ¬ afterByte1 ≤ afterHeader)
    -- Block 2 hypotheses (compressed, last, numSeq=0)
    (hoff2 : ¬ data.size ≤ afterByte1)
    (hparse2 : Zip.Native.parseBlockHeader data afterByte1 = .ok (hdr2, afterHdr2))
    (hbs2 : ¬ hdr2.blockSize > 131072)
    (hws2 : ¬ (header.windowSize > 0 && hdr2.blockSize.toUInt64 > header.windowSize))
    (htype2 : hdr2.blockType = .compressed)
    (hblockEnd2 : ¬ data.size < afterHdr2 + hdr2.blockSize.toNat)
    (hlit2 : Zip.Native.parseLiteralsSection data afterHdr2 none
               = .ok (literals2, afterLiterals2, huffTree2))
    (hseq2 : Zip.Native.parseSequencesHeader data afterLiterals2
               = .ok (0, modes2, afterSeqHeader2))
    (hlast2 : hdr2.lastBlock = true)
    -- End of data
    (hend : pos' ≥ data.size) :
    Zip.Native.decompressZstd data = .ok (block1 ++ literals2) := by
  have hcontent := Zstd.Spec.decompressFrame_rle_then_compressed_lit_content data 0 output pos'
    header afterHeader hdr1 afterHdr1 block1 afterByte1 hdr2 afterHdr2 literals2 afterLiterals2
    huffTree2 modes2 afterSeqHeader2
    hframe hh hparse1 hbs1 hws1 htype1 hrle1 hnotlast1 hadv1
    hoff2 hparse2 hbs2 hws2 htype2 hblockEnd2 hlit2 hseq2 hlast2
  subst hcontent
  exact decompressZstd_single_frame data (block1 ++ literals2) pos' hframe hend

/-- When the input contains exactly one standard Zstd frame at position 0 with two
    blocks (first non-last compressed with numSeq>0, second last raw), `decompressZstd`
    returns `blockOutput1 ++ block2`.  Composes
    `decompressFrame_compressed_seq_then_raw_content` with
    `decompressZstd_single_frame`. -/
theorem decompressZstd_compressed_seq_then_raw_content (data : ByteArray)
    (output : ByteArray) (pos' : Nat)
    (header : Zip.Native.ZstdFrameHeader) (afterHeader : Nat)
    -- Block 1 (non-last compressed, numSeq > 0)
    (hdr1 : Zip.Native.ZstdBlockHeader) (afterHdr1 : Nat)
    (literals1 : ByteArray) (afterLiterals1 : Nat)
    (huffTree1 : Option Zip.Native.ZstdHuffmanTable)
    (numSeq1 : Nat) (modes1 : Zip.Native.SequenceCompressionModes) (afterSeqHeader1 : Nat)
    (llTable1 ofTable1 mlTable1 : Zip.Native.FseTable) (afterTables1 : Nat)
    (bbr1 : Zip.Native.BackwardBitReader)
    (sequences1 : Array Zip.Native.ZstdSequence)
    (blockOutput1 : ByteArray) (newHist1 : Array Nat)
    -- Block 2 (last raw)
    (hdr2 : Zip.Native.ZstdBlockHeader) (afterHdr2 : Nat)
    (block2 : ByteArray) (afterBlock2 : Nat)
    -- Frame hypotheses
    (hframe : Zip.Native.decompressFrame data 0 = .ok (output, pos'))
    (hh : Zip.Native.parseFrameHeader data 0 = .ok (header, afterHeader))
    -- Block 1 hypotheses (compressed, non-last, numSeq > 0)
    (hparse1 : Zip.Native.parseBlockHeader data afterHeader = .ok (hdr1, afterHdr1))
    (hbs1 : ¬ hdr1.blockSize > 131072)
    (hws1 : ¬ (header.windowSize > 0 && hdr1.blockSize.toUInt64 > header.windowSize))
    (htype1 : hdr1.blockType = .compressed)
    (hblockEnd1 : ¬ data.size < afterHdr1 + hdr1.blockSize.toNat)
    (hlit1 : Zip.Native.parseLiteralsSection data afterHdr1 none
               = .ok (literals1, afterLiterals1, huffTree1))
    (hseq1 : Zip.Native.parseSequencesHeader data afterLiterals1
               = .ok (numSeq1, modes1, afterSeqHeader1))
    (hNumSeq1 : ¬ numSeq1 == 0)
    (hfse1 : Zip.Native.resolveSequenceFseTables modes1 data afterSeqHeader1 {}
               = .ok (llTable1, ofTable1, mlTable1, afterTables1))
    (hbbr1 : Zip.Native.BackwardBitReader.init data afterTables1
               (afterHdr1 + hdr1.blockSize.toNat) = .ok bbr1)
    (hdec1 : Zip.Native.decodeSequences llTable1 ofTable1 mlTable1 bbr1 numSeq1
               = .ok sequences1)
    (hexec1 : Zip.Native.executeSequences sequences1 literals1 ByteArray.empty
                #[1, 4, 8] header.windowSize.toNat
                = .ok (blockOutput1, newHist1))
    (hnotlast1 : hdr1.lastBlock = false)
    (hadv1 : ¬ (afterHdr1 + hdr1.blockSize.toNat) ≤ afterHeader)
    -- Block 2 hypotheses (raw, last)
    (hoff2 : ¬ data.size ≤ afterHdr1 + hdr1.blockSize.toNat)
    (hparse2 : Zip.Native.parseBlockHeader data (afterHdr1 + hdr1.blockSize.toNat)
                 = .ok (hdr2, afterHdr2))
    (hbs2 : ¬ hdr2.blockSize > 131072)
    (hws2 : ¬ (header.windowSize > 0 && hdr2.blockSize.toUInt64 > header.windowSize))
    (htype2 : hdr2.blockType = .raw)
    (hraw2 : Zip.Native.decompressRawBlock data afterHdr2 hdr2.blockSize
               = .ok (block2, afterBlock2))
    (hlast2 : hdr2.lastBlock = true)
    -- End of data
    (hend : pos' ≥ data.size) :
    Zip.Native.decompressZstd data = .ok (blockOutput1 ++ block2) := by
  have hcontent := Zstd.Spec.decompressFrame_compressed_seq_then_raw_content data 0 output pos'
    header afterHeader hdr1 afterHdr1 literals1 afterLiterals1 huffTree1
    numSeq1 modes1 afterSeqHeader1 llTable1 ofTable1 mlTable1 afterTables1 bbr1 sequences1
    blockOutput1 newHist1 hdr2 afterHdr2 block2 afterBlock2
    hframe hh hparse1 hbs1 hws1 htype1 hblockEnd1 hlit1 hseq1
    hNumSeq1 hfse1 hbbr1 hdec1 hexec1 hnotlast1 hadv1
    hoff2 hparse2 hbs2 hws2 htype2 hraw2 hlast2
  subst hcontent
  exact decompressZstd_single_frame data (blockOutput1 ++ block2) pos' hframe hend

/-- When the input contains exactly one standard Zstd frame at position 0 with two
    blocks (first non-last compressed with numSeq>0, second last RLE), `decompressZstd`
    returns `blockOutput1 ++ block2`.  Composes
    `decompressFrame_compressed_seq_then_rle_content` with
    `decompressZstd_single_frame`. -/
theorem decompressZstd_compressed_seq_then_rle_content (data : ByteArray)
    (output : ByteArray) (pos' : Nat)
    (header : Zip.Native.ZstdFrameHeader) (afterHeader : Nat)
    -- Block 1 (non-last compressed, numSeq > 0)
    (hdr1 : Zip.Native.ZstdBlockHeader) (afterHdr1 : Nat)
    (literals1 : ByteArray) (afterLiterals1 : Nat)
    (huffTree1 : Option Zip.Native.ZstdHuffmanTable)
    (numSeq1 : Nat) (modes1 : Zip.Native.SequenceCompressionModes) (afterSeqHeader1 : Nat)
    (llTable1 ofTable1 mlTable1 : Zip.Native.FseTable) (afterTables1 : Nat)
    (bbr1 : Zip.Native.BackwardBitReader)
    (sequences1 : Array Zip.Native.ZstdSequence)
    (blockOutput1 : ByteArray) (newHist1 : Array Nat)
    -- Block 2 (last RLE)
    (hdr2 : Zip.Native.ZstdBlockHeader) (afterHdr2 : Nat)
    (block2 : ByteArray) (afterByte2 : Nat)
    -- Frame hypotheses
    (hframe : Zip.Native.decompressFrame data 0 = .ok (output, pos'))
    (hh : Zip.Native.parseFrameHeader data 0 = .ok (header, afterHeader))
    -- Block 1 hypotheses (compressed, non-last, numSeq > 0)
    (hparse1 : Zip.Native.parseBlockHeader data afterHeader = .ok (hdr1, afterHdr1))
    (hbs1 : ¬ hdr1.blockSize > 131072)
    (hws1 : ¬ (header.windowSize > 0 && hdr1.blockSize.toUInt64 > header.windowSize))
    (htype1 : hdr1.blockType = .compressed)
    (hblockEnd1 : ¬ data.size < afterHdr1 + hdr1.blockSize.toNat)
    (hlit1 : Zip.Native.parseLiteralsSection data afterHdr1 none
               = .ok (literals1, afterLiterals1, huffTree1))
    (hseq1 : Zip.Native.parseSequencesHeader data afterLiterals1
               = .ok (numSeq1, modes1, afterSeqHeader1))
    (hNumSeq1 : ¬ numSeq1 == 0)
    (hfse1 : Zip.Native.resolveSequenceFseTables modes1 data afterSeqHeader1 {}
               = .ok (llTable1, ofTable1, mlTable1, afterTables1))
    (hbbr1 : Zip.Native.BackwardBitReader.init data afterTables1
               (afterHdr1 + hdr1.blockSize.toNat) = .ok bbr1)
    (hdec1 : Zip.Native.decodeSequences llTable1 ofTable1 mlTable1 bbr1 numSeq1
               = .ok sequences1)
    (hexec1 : Zip.Native.executeSequences sequences1 literals1 ByteArray.empty
                #[1, 4, 8] header.windowSize.toNat
                = .ok (blockOutput1, newHist1))
    (hnotlast1 : hdr1.lastBlock = false)
    (hadv1 : ¬ (afterHdr1 + hdr1.blockSize.toNat) ≤ afterHeader)
    -- Block 2 hypotheses (RLE, last)
    (hoff2 : ¬ data.size ≤ afterHdr1 + hdr1.blockSize.toNat)
    (hparse2 : Zip.Native.parseBlockHeader data (afterHdr1 + hdr1.blockSize.toNat)
                 = .ok (hdr2, afterHdr2))
    (hbs2 : ¬ hdr2.blockSize > 131072)
    (hws2 : ¬ (header.windowSize > 0 && hdr2.blockSize.toUInt64 > header.windowSize))
    (htype2 : hdr2.blockType = .rle)
    (hrle2 : Zip.Native.decompressRLEBlock data afterHdr2 hdr2.blockSize
               = .ok (block2, afterByte2))
    (hlast2 : hdr2.lastBlock = true)
    -- End of data
    (hend : pos' ≥ data.size) :
    Zip.Native.decompressZstd data = .ok (blockOutput1 ++ block2) := by
  have hcontent := Zstd.Spec.decompressFrame_compressed_seq_then_rle_content data 0 output pos'
    header afterHeader hdr1 afterHdr1 literals1 afterLiterals1 huffTree1
    numSeq1 modes1 afterSeqHeader1 llTable1 ofTable1 mlTable1 afterTables1 bbr1 sequences1
    blockOutput1 newHist1 hdr2 afterHdr2 block2 afterByte2
    hframe hh hparse1 hbs1 hws1 htype1 hblockEnd1 hlit1 hseq1
    hNumSeq1 hfse1 hbbr1 hdec1 hexec1 hnotlast1 hadv1
    hoff2 hparse2 hbs2 hws2 htype2 hrle2 hlast2
  subst hcontent
  exact decompressZstd_single_frame data (blockOutput1 ++ block2) pos' hframe hend

/-- When the input contains exactly one standard Zstd frame at position 0 with two
    blocks (first non-last raw, second last compressed with numSeq>0), `decompressZstd`
    returns `block1 ++ blockOutput2`.  Composes
    `decompressFrame_raw_then_compressed_seq_content` with
    `decompressZstd_single_frame`. -/
theorem decompressZstd_raw_then_compressed_seq_content (data : ByteArray)
    (output : ByteArray) (pos' : Nat)
    (header : Zip.Native.ZstdFrameHeader) (afterHeader : Nat)
    -- Block 1 (non-last raw)
    (hdr1 : Zip.Native.ZstdBlockHeader) (afterHdr1 : Nat)
    (block1 : ByteArray) (afterBlock1 : Nat)
    -- Block 2 (last compressed, numSeq > 0)
    (hdr2 : Zip.Native.ZstdBlockHeader) (afterHdr2 : Nat)
    (literals2 : ByteArray) (afterLiterals2 : Nat)
    (huffTree2 : Option Zip.Native.ZstdHuffmanTable)
    (numSeq2 : Nat) (modes2 : Zip.Native.SequenceCompressionModes) (afterSeqHeader2 : Nat)
    (llTable2 ofTable2 mlTable2 : Zip.Native.FseTable) (afterTables2 : Nat)
    (bbr2 : Zip.Native.BackwardBitReader)
    (sequences2 : Array Zip.Native.ZstdSequence)
    (blockOutput2 : ByteArray) (newHist2 : Array Nat)
    -- Frame hypotheses
    (hframe : Zip.Native.decompressFrame data 0 = .ok (output, pos'))
    (hh : Zip.Native.parseFrameHeader data 0 = .ok (header, afterHeader))
    -- Block 1 hypotheses (raw, non-last)
    (hparse1 : Zip.Native.parseBlockHeader data afterHeader = .ok (hdr1, afterHdr1))
    (hbs1 : ¬ hdr1.blockSize > 131072)
    (hws1 : ¬ (header.windowSize > 0 && hdr1.blockSize.toUInt64 > header.windowSize))
    (htype1 : hdr1.blockType = .raw)
    (hraw1 : Zip.Native.decompressRawBlock data afterHdr1 hdr1.blockSize
               = .ok (block1, afterBlock1))
    (hnotlast1 : hdr1.lastBlock = false)
    (hadv1 : ¬ afterBlock1 ≤ afterHeader)
    -- Block 2 hypotheses (compressed, last, numSeq > 0)
    (hoff2 : ¬ data.size ≤ afterBlock1)
    (hparse2 : Zip.Native.parseBlockHeader data afterBlock1 = .ok (hdr2, afterHdr2))
    (hbs2 : ¬ hdr2.blockSize > 131072)
    (hws2 : ¬ (header.windowSize > 0 && hdr2.blockSize.toUInt64 > header.windowSize))
    (htype2 : hdr2.blockType = .compressed)
    (hblockEnd2 : ¬ data.size < afterHdr2 + hdr2.blockSize.toNat)
    (hlit2 : Zip.Native.parseLiteralsSection data afterHdr2 none
               = .ok (literals2, afterLiterals2, huffTree2))
    (hseq2 : Zip.Native.parseSequencesHeader data afterLiterals2
               = .ok (numSeq2, modes2, afterSeqHeader2))
    (hNumSeq2 : ¬ numSeq2 == 0)
    (hfse2 : Zip.Native.resolveSequenceFseTables modes2 data afterSeqHeader2 {}
               = .ok (llTable2, ofTable2, mlTable2, afterTables2))
    (hbbr2 : Zip.Native.BackwardBitReader.init data afterTables2
               (afterHdr2 + hdr2.blockSize.toNat) = .ok bbr2)
    (hdec2 : Zip.Native.decodeSequences llTable2 ofTable2 mlTable2 bbr2 numSeq2
               = .ok sequences2)
    (hexec2 : Zip.Native.executeSequences sequences2 literals2
                (if header.windowSize > 0 && block1.size > header.windowSize.toNat
                 then block1.extract (block1.size - header.windowSize.toNat) block1.size
                 else block1)
                #[1, 4, 8] header.windowSize.toNat
                = .ok (blockOutput2, newHist2))
    (hlast2 : hdr2.lastBlock = true)
    -- End of data
    (hend : pos' ≥ data.size) :
    Zip.Native.decompressZstd data = .ok (block1 ++ blockOutput2) := by
  have hcontent := Zstd.Spec.decompressFrame_raw_then_compressed_seq_content data 0 output pos'
    header afterHeader hdr1 afterHdr1 block1 afterBlock1
    hdr2 afterHdr2 literals2 afterLiterals2 huffTree2
    numSeq2 modes2 afterSeqHeader2 llTable2 ofTable2 mlTable2 afterTables2 bbr2 sequences2
    blockOutput2 newHist2
    hframe hh hparse1 hbs1 hws1 htype1 hraw1 hnotlast1 hadv1
    hoff2 hparse2 hbs2 hws2 htype2 hblockEnd2 hlit2 hseq2 hNumSeq2
    hfse2 hbbr2 hdec2 hexec2 hlast2
  subst hcontent
  exact decompressZstd_single_frame data (block1 ++ blockOutput2) pos' hframe hend

/-- When the input contains exactly one standard Zstd frame at position 0 with two
    blocks (first non-last RLE, second last compressed with numSeq>0), `decompressZstd`
    returns `block1 ++ blockOutput2`.  Composes
    `decompressFrame_rle_then_compressed_seq_content` with
    `decompressZstd_single_frame`. -/
theorem decompressZstd_rle_then_compressed_seq_content (data : ByteArray)
    (output : ByteArray) (pos' : Nat)
    (header : Zip.Native.ZstdFrameHeader) (afterHeader : Nat)
    -- Block 1 (non-last RLE)
    (hdr1 : Zip.Native.ZstdBlockHeader) (afterHdr1 : Nat)
    (block1 : ByteArray) (afterByte1 : Nat)
    -- Block 2 (last compressed, numSeq > 0)
    (hdr2 : Zip.Native.ZstdBlockHeader) (afterHdr2 : Nat)
    (literals2 : ByteArray) (afterLiterals2 : Nat)
    (huffTree2 : Option Zip.Native.ZstdHuffmanTable)
    (numSeq2 : Nat) (modes2 : Zip.Native.SequenceCompressionModes) (afterSeqHeader2 : Nat)
    (llTable2 ofTable2 mlTable2 : Zip.Native.FseTable) (afterTables2 : Nat)
    (bbr2 : Zip.Native.BackwardBitReader)
    (sequences2 : Array Zip.Native.ZstdSequence)
    (blockOutput2 : ByteArray) (newHist2 : Array Nat)
    -- Frame hypotheses
    (hframe : Zip.Native.decompressFrame data 0 = .ok (output, pos'))
    (hh : Zip.Native.parseFrameHeader data 0 = .ok (header, afterHeader))
    -- Block 1 hypotheses (RLE, non-last)
    (hparse1 : Zip.Native.parseBlockHeader data afterHeader = .ok (hdr1, afterHdr1))
    (hbs1 : ¬ hdr1.blockSize > 131072)
    (hws1 : ¬ (header.windowSize > 0 && hdr1.blockSize.toUInt64 > header.windowSize))
    (htype1 : hdr1.blockType = .rle)
    (hrle1 : Zip.Native.decompressRLEBlock data afterHdr1 hdr1.blockSize
               = .ok (block1, afterByte1))
    (hnotlast1 : hdr1.lastBlock = false)
    (hadv1 : ¬ afterByte1 ≤ afterHeader)
    -- Block 2 hypotheses (compressed, last, numSeq > 0)
    (hoff2 : ¬ data.size ≤ afterByte1)
    (hparse2 : Zip.Native.parseBlockHeader data afterByte1 = .ok (hdr2, afterHdr2))
    (hbs2 : ¬ hdr2.blockSize > 131072)
    (hws2 : ¬ (header.windowSize > 0 && hdr2.blockSize.toUInt64 > header.windowSize))
    (htype2 : hdr2.blockType = .compressed)
    (hblockEnd2 : ¬ data.size < afterHdr2 + hdr2.blockSize.toNat)
    (hlit2 : Zip.Native.parseLiteralsSection data afterHdr2 none
               = .ok (literals2, afterLiterals2, huffTree2))
    (hseq2 : Zip.Native.parseSequencesHeader data afterLiterals2
               = .ok (numSeq2, modes2, afterSeqHeader2))
    (hNumSeq2 : ¬ numSeq2 == 0)
    (hfse2 : Zip.Native.resolveSequenceFseTables modes2 data afterSeqHeader2 {}
               = .ok (llTable2, ofTable2, mlTable2, afterTables2))
    (hbbr2 : Zip.Native.BackwardBitReader.init data afterTables2
               (afterHdr2 + hdr2.blockSize.toNat) = .ok bbr2)
    (hdec2 : Zip.Native.decodeSequences llTable2 ofTable2 mlTable2 bbr2 numSeq2
               = .ok sequences2)
    (hexec2 : Zip.Native.executeSequences sequences2 literals2
                (if header.windowSize > 0 && block1.size > header.windowSize.toNat
                 then block1.extract (block1.size - header.windowSize.toNat) block1.size
                 else block1)
                #[1, 4, 8] header.windowSize.toNat
                = .ok (blockOutput2, newHist2))
    (hlast2 : hdr2.lastBlock = true)
    -- End of data
    (hend : pos' ≥ data.size) :
    Zip.Native.decompressZstd data = .ok (block1 ++ blockOutput2) := by
  have hcontent := Zstd.Spec.decompressFrame_rle_then_compressed_seq_content data 0 output pos'
    header afterHeader hdr1 afterHdr1 block1 afterByte1
    hdr2 afterHdr2 literals2 afterLiterals2 huffTree2
    numSeq2 modes2 afterSeqHeader2 llTable2 ofTable2 mlTable2 afterTables2 bbr2 sequences2
    blockOutput2 newHist2
    hframe hh hparse1 hbs1 hws1 htype1 hrle1 hnotlast1 hadv1
    hoff2 hparse2 hbs2 hws2 htype2 hblockEnd2 hlit2 hseq2 hNumSeq2
    hfse2 hbbr2 hdec2 hexec2 hlast2
  subst hcontent
  exact decompressZstd_single_frame data (block1 ++ blockOutput2) pos' hframe hend

/-! ## decompressZstd frame metadata characterizing properties -/

/-- When `decompressZstd` succeeds on a single-frame input whose frame header
    declares `contentSize = some n`, the output has exactly `n` bytes.
    Composes `decompressZstd_single_frame` with `decompressFrame_contentSize_eq`. -/
theorem decompressZstd_single_frame_contentSize (data : ByteArray)
    (content : ByteArray) (pos' : Nat)
    (hframe : Zip.Native.decompressFrame data 0 = .ok (content, pos'))
    (hend : pos' ≥ data.size)
    (header : Zip.Native.ZstdFrameHeader) (headerPos : Nat)
    (hh : Zip.Native.parseFrameHeader data 0 = .ok (header, headerPos))
    (n : UInt64) (hn : header.contentSize = some n) :
    Zip.Native.decompressZstd data = .ok content ∧ content.size.toUInt64 = n :=
  ⟨decompressZstd_single_frame data content pos' hframe hend,
   Zstd.Spec.decompressFrame_contentSize_eq data 0 content pos' hframe header headerPos hh n hn⟩

/-- When `decompressZstd` succeeds on a single-frame input whose frame header
    has `contentChecksum = true`, the output's XXH64 upper 32 bits match the
    checksum stored in the 4 bytes before `pos'` in the input.
    Composes `decompressZstd_single_frame` with `decompressFrame_checksum_valid`. -/
theorem decompressZstd_single_frame_checksum (data : ByteArray)
    (content : ByteArray) (pos' : Nat)
    (hframe : Zip.Native.decompressFrame data 0 = .ok (content, pos'))
    (hend : pos' ≥ data.size)
    (header : Zip.Native.ZstdFrameHeader) (headerPos : Nat)
    (hh : Zip.Native.parseFrameHeader data 0 = .ok (header, headerPos))
    (hc : header.contentChecksum = true) :
    Zip.Native.decompressZstd data = .ok content ∧
      XxHash64.xxHash64Upper32 content = Binary.readUInt32LE data (pos' - 4) :=
  ⟨decompressZstd_single_frame data content pos' hframe hend,
   Zstd.Spec.decompressFrame_checksum_valid data 0 content pos' hframe header headerPos hh hc⟩

end Zip.Spec.ZstdFrame
