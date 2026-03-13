import Zip.Spec.ZstdContent

/-!
# Zstandard Frame Specification — Unified Completeness

The unified completeness theorem `decompressFrame_succeeds_of_well_formed`
that subsumes all specific `decompressFrame_succeeds_*` theorems via the
`WellFormedBlocks` predicate.

See `Zip/Spec/ZstdSucceeds.lean` for individual succeeds theorems.
See `Zip/Spec/ZstdContent.lean` for content characterization theorems.
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
