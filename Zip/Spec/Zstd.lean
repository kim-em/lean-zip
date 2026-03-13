import Zip.Spec.ZstdFrameSuccess
import Zip.Spec.ZstdContent

/-!
# Zstandard Frame Specification (RFC 8878) — Unified Completeness

This file contains the unified frame-level completeness meta-theorem
`decompressFrame_succeeds_of_well_formed`.

Frame success theorems are in `Zip/Spec/ZstdFrameSuccess.lean`.
Content characterization theorems are in `Zip/Spec/ZstdContent.lean`.
Step theorems, induction predicates, and block-level two-block completeness
are in `Zip/Spec/ZstdTwoBlock.lean` (L3).
Base definitions and predicates are in `Zip/Spec/ZstdBase.lean` (L1).
Block-loop structural lemmas are in `Zip/Spec/ZstdBlockLoop.lean` (L2).
-/

namespace Zstd.Spec

/-! ## Unified frame-level completeness via WellFormedBlocks -/

/-- When a frame header parses successfully and the block sequence is well-formed
    (according to `WellFormedBlocks`), `decompressFrame` succeeds.  This subsumes
    all specific `decompressFrame_succeeds_*` theorems for the no-dictionary,
    no-checksum, no-content-size case. -/
theorem decompressFrame_succeeds_of_well_formed (data : ByteArray) (pos : Nat)
    (header : Zip.Native.ZstdFrameHeader) (afterHeader : Nat)
    (hparse : Zip.Native.parseFrameHeader data pos = .ok (header, afterHeader))
    (hnodict : header.dictionaryId = none)
    (hnocksum : header.contentChecksum = false)
    (hnosize : header.contentSize = none)
    (hwf : WellFormedBlocks data afterHeader header.windowSize
      ByteArray.empty none {} #[1, 4, 8]) :
    ∃ content pos',
      Zip.Native.decompressFrame data pos = .ok (content, pos') := by
  -- Step 1: Get block-level success from WellFormedBlocks
  obtain ⟨result, blockPos, hblocks⟩ :=
    decompressBlocksWF_succeeds_of_well_formed data afterHeader header.windowSize
      ByteArray.empty none {} #[1, 4, 8] hwf
  -- Step 2: Unfold decompressFrame and thread through
  unfold Zip.Native.decompressFrame
  simp only [bind, Except.bind, pure, Except.pure, hparse]
  -- Step 3: Dictionary check — header.dictionaryId = none
  simp only [hnodict]
  -- Step 4: Block decompression succeeds
  unfold Zip.Native.decompressBlocks
  rw [hblocks]
  -- Step 5: Checksum is false, content size is none
  simp only [hnocksum, hnosize, Bool.false_eq_true, ↓reduceIte]
  exact ⟨_, _, rfl⟩

end Zstd.Spec
