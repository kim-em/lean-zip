import Zip.Native.ZstdFrame
import Std.Tactic.BVDecide

/-!
# Zstandard Frame Specification (RFC 8878)

Formal specification of the Zstandard compressed data format at the frame
and block level.  This defines what constitutes a valid Zstd frame header
and block header, independently of any particular decompressor implementation.

The specification is structured in layers:
1. **Magic numbers**: Zstd frame magic and skippable frame magic range
2. **Frame header**: descriptor flags, window size bounds, content size
3. **Block header**: block type validity and block size bounds

The key correctness theorems prove that `parseFrameHeader` and
`parseBlockHeader` in `Zip.Native` only produce results that satisfy
these specification predicates.
-/

-- Unfold monadic `Except` bind/pure in hypothesis `h`.
-- This pattern appears throughout Zstd spec proofs that case-split on monadic
-- computations returning `Except`.
set_option hygiene false in
local macro "unfold_except" : tactic =>
  `(tactic| simp only [bind, Except.bind, pure, Except.pure] at h)

namespace Zstd.Spec

/-! ## Magic number predicates -/

/-- A valid Zstd frame magic number is exactly `0xFD2FB528` (RFC 8878 §3.1.1). -/
def validMagic (m : UInt32) : Prop := m = 0xFD2FB528

instance : Decidable (validMagic m) := inferInstanceAs (Decidable (_ = _))

/-- A skippable frame magic number is in the range `0x184D2A50`–`0x184D2A5F`
    (RFC 8878 §3.1.2). -/
def isSkippableMagic (m : UInt32) : Prop :=
  0x184D2A50 ≤ m ∧ m ≤ 0x184D2A5F

instance : Decidable (isSkippableMagic m) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ## Frame header predicates -/

/-- A valid frame header descriptor byte has its reserved bit (bit 3) equal to 0
    (RFC 8878 §3.1.1.1). -/
def validFrameHeaderDescriptor (desc : UInt8) : Prop :=
  (desc >>> 3) &&& 1 = 0

instance : Decidable (validFrameHeaderDescriptor desc) :=
  inferInstanceAs (Decidable (_ = _))

/-- A valid window size exponent is at most 41 (RFC 8878 §3.1.1.1.2).
    The exponent is the upper 5 bits of the window descriptor byte,
    giving a maximum window size of 2^(10+41) = 2^51 bytes. -/
def validWindowSizeExponent (exp : Nat) : Prop := exp ≤ 41

instance : Decidable (validWindowSizeExponent exp) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-! ## Block header predicates -/

/-- `ZstdBlockType` has decidable equality (needed for specification predicates). -/
instance : DecidableEq Zip.Native.ZstdBlockType := by
  intro a b
  cases a <;> cases b
  all_goals first
    | exact isTrue rfl
    | exact isFalse (by intro h; cases h)

/-- A valid block type is not reserved (not 3) per RFC 8878 §3.1.1.2. -/
def validBlockType (bt : Zip.Native.ZstdBlockType) : Prop :=
  bt ≠ .reserved

instance : Decidable (validBlockType bt) :=
  inferInstanceAs (Decidable (_ ≠ _))

/-- A valid block size is at most 128 KB (131072 bytes) per RFC 8878 §3.1.1.2.
    The Block_Size field is 21 bits, and the maximum allowed value is 128 KB. -/
def validBlockSize (sz : UInt32) : Prop := sz ≤ 131072

instance : Decidable (validBlockSize sz) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- A valid block header has a non-reserved type and a size within bounds. -/
def ValidBlockHeader (hdr : Zip.Native.ZstdBlockHeader) : Prop :=
  validBlockType hdr.blockType ∧ validBlockSize hdr.blockSize

instance : Decidable (ValidBlockHeader hdr) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ## Correctness theorems -/

/-- When `parseFrameHeader` succeeds, the parsed magic number is valid.
    This follows from the guard `magic != zstdMagic` in the implementation. -/
theorem parseFrameHeader_magic (data : ByteArray) (pos : Nat)
    (hdr : Zip.Native.ZstdFrameHeader) (pos' : Nat)
    (h : Zip.Native.parseFrameHeader data pos = .ok (hdr, pos')) :
    validMagic (Binary.readUInt32LE data pos) := by
  unfold Zip.Native.parseFrameHeader at h
  dsimp only [Bind.bind, Except.bind] at h
  -- Use by_cases + rw instead of split (split hits simp step limit on this large term)
  by_cases hsize : data.size < pos + 4
  · rw [if_pos hsize] at h; exact nomatch h
  · rw [if_neg hsize] at h
    simp only [pure, Pure.pure] at h
    by_cases hmagic : (Binary.readUInt32LE data pos != Zip.Native.zstdMagic) = true
    · rw [if_pos hmagic] at h; exact nomatch h
    · rw [if_neg hmagic] at h
      unfold validMagic
      have heq : (Binary.readUInt32LE data pos == Zip.Native.zstdMagic) = true := by
        cases hb : (Binary.readUInt32LE data pos == Zip.Native.zstdMagic)
        · exfalso; apply hmagic; show (!(Binary.readUInt32LE data pos == Zip.Native.zstdMagic)) = true
          rw [hb]; rfl
        · rfl
      exact eq_of_beq heq

/-- When `parseBlockHeader` succeeds, the block type is not reserved.
    This follows from the `throw "Zstd: reserved block type"` guard. -/
theorem parseBlockHeader_type_ne_reserved (data : ByteArray) (pos : Nat)
    (hdr : Zip.Native.ZstdBlockHeader) (pos' : Nat)
    (h : Zip.Native.parseBlockHeader data pos = .ok (hdr, pos')) :
    validBlockType hdr.blockType := by
  unfold Zip.Native.parseBlockHeader at h
  split at h
  · exact nomatch h
  · unfold_except
    split at h
    · -- typeVal = 0 → raw
      obtain ⟨rfl, rfl⟩ := h; exact fun h => nomatch h
    · -- typeVal = 1 → rle
      obtain ⟨rfl, rfl⟩ := h; exact fun h => nomatch h
    · -- typeVal = 2 → compressed
      obtain ⟨rfl, rfl⟩ := h; exact fun h => nomatch h
    · -- typeVal = _ → throw
      exact nomatch h

/-- The 21-bit Block_Size field (bits 3–23 of a 24-bit header) is always less than 2^21.
    This is the core bitwise arithmetic fact: right-shifting a 24-bit value by 3
    yields at most a 21-bit value. -/
private theorem raw24_shiftRight3_lt (b0 b1 b2 : UInt8) :
    ((b0.toUInt32 ||| b1.toUInt32 <<< 8 ||| b2.toUInt32 <<< 16) >>> 3).toNat < 2 ^ 21 := by
  show ((b0.toUInt32 ||| b1.toUInt32 <<< 8 ||| b2.toUInt32 <<< 16) >>> 3 : UInt32) < 2097152
  bv_decide

/-- When `parseBlockHeader` succeeds, the block size fits in 21 bits.
    The Block_Size field occupies bits 3–23 of the 24-bit block header
    (RFC 8878 §3.1.1.2), so the parsed value is always less than 2^21.
    Note: the stricter 128 KB limit (`validBlockSize`) is enforced by
    `decompressBlocks`, not by `parseBlockHeader`. -/
theorem parseBlockHeader_blockSize_lt (data : ByteArray) (pos : Nat)
    (hdr : Zip.Native.ZstdBlockHeader) (pos' : Nat)
    (h : Zip.Native.parseBlockHeader data pos = .ok (hdr, pos')) :
    hdr.blockSize.toNat < 2 ^ 21 := by
  unfold Zip.Native.parseBlockHeader at h
  split at h
  · exact nomatch h
  · unfold_except
    split at h
    · obtain ⟨rfl, rfl⟩ := h; exact raw24_shiftRight3_lt ..
    · obtain ⟨rfl, rfl⟩ := h; exact raw24_shiftRight3_lt ..
    · obtain ⟨rfl, rfl⟩ := h; exact raw24_shiftRight3_lt ..
    · exact nomatch h

/-- When `parseBlockHeader` succeeds, the returned position is exactly `pos + 3`.
    This follows from the structure of the 3-byte block header (RFC 8878 §3.1.1.2):
    on all success paths, the function returns `(_, pos + 3)`. -/
theorem parseBlockHeader_pos_eq (data : ByteArray) (pos : Nat)
    (header : Zip.Native.ZstdBlockHeader) (afterHdr : Nat)
    (h : Zip.Native.parseBlockHeader data pos = .ok (header, afterHdr)) :
    afterHdr = pos + 3 := by
  unfold Zip.Native.parseBlockHeader at h
  split at h
  · exact nomatch h
  · unfold_except
    split at h
    · obtain ⟨rfl, rfl⟩ := h; rfl
    · obtain ⟨rfl, rfl⟩ := h; rfl
    · obtain ⟨rfl, rfl⟩ := h; rfl
    · exact nomatch h

/-- When `parseBlockHeader` succeeds, the returned position is within data bounds.
    Follows from `parseBlockHeader_pos_eq` (pos' = pos + 3) and the bounds check
    ¬(data.size < pos + 3). -/
theorem parseBlockHeader_le_size (data : ByteArray) (pos : Nat)
    (header : Zip.Native.ZstdBlockHeader) (pos' : Nat)
    (h : Zip.Native.parseBlockHeader data pos = .ok (header, pos')) :
    pos' ≤ data.size := by
  have hpos := parseBlockHeader_pos_eq data pos header pos' h
  unfold Zip.Native.parseBlockHeader at h
  split at h
  · exact nomatch h
  · subst hpos; omega

/-! ## Block decompression correctness -/

/-- When `decompressRawBlock` succeeds, the output has exactly `blockSize` bytes. -/
theorem decompressRawBlock_size (data : ByteArray) (pos : Nat)
    (blockSize : UInt32) (result : ByteArray) (pos' : Nat)
    (h : Zip.Native.decompressRawBlock data pos blockSize = .ok (result, pos')) :
    result.size = blockSize.toNat := by
  unfold Zip.Native.decompressRawBlock at h
  unfold_except
  split at h
  · exact nomatch h
  · obtain ⟨rfl, rfl⟩ := h
    simp only [ByteArray.size_extract]
    omega

/-- When `decompressRLEBlock` succeeds, the output has exactly `blockSize` bytes. -/
theorem decompressRLEBlock_size (data : ByteArray) (pos : Nat)
    (blockSize : UInt32) (result : ByteArray) (pos' : Nat)
    (h : Zip.Native.decompressRLEBlock data pos blockSize = .ok (result, pos')) :
    result.size = blockSize.toNat := by
  unfold Zip.Native.decompressRLEBlock at h
  unfold_except
  split at h
  · exact nomatch h
  · obtain ⟨rfl, rfl⟩ := h
    exact Array.size_replicate ..

/-- When `decompressRLEBlock` succeeds, every byte in the output equals the
    source byte at position `pos` in the input. -/
theorem decompressRLEBlock_content (data : ByteArray) (pos : Nat)
    (blockSize : UInt32) (result : ByteArray) (pos' : Nat)
    (h : Zip.Native.decompressRLEBlock data pos blockSize = .ok (result, pos'))
    (i : Nat) (hi : i < result.size) :
    result[i] = data[pos]! := by
  unfold Zip.Native.decompressRLEBlock at h
  unfold_except
  split at h
  · exact nomatch h
  · obtain ⟨rfl, rfl⟩ := h
    rw [ByteArray.getElem_eq_getElem_data, Array.getElem_replicate]

/-- When `decompressRawBlock` succeeds, the returned position is `pos + blockSize.toNat`.
    The raw block consumes exactly `blockSize` bytes from the input. -/
theorem decompressRawBlock_pos_eq (data : ByteArray) (pos : Nat)
    (blockSize : UInt32) (result : ByteArray) (pos' : Nat)
    (h : Zip.Native.decompressRawBlock data pos blockSize = .ok (result, pos')) :
    pos' = pos + blockSize.toNat := by
  unfold Zip.Native.decompressRawBlock at h
  unfold_except
  split at h
  · exact nomatch h
  · obtain ⟨rfl, rfl⟩ := h; rfl

/-- When `decompressRawBlock` succeeds, the returned position is within data bounds. -/
theorem decompressRawBlock_le_size (data : ByteArray) (pos : Nat)
    (blockSize : UInt32) (output : ByteArray) (pos' : Nat)
    (h : Zip.Native.decompressRawBlock data pos blockSize = .ok (output, pos')) :
    pos' ≤ data.size := by
  unfold Zip.Native.decompressRawBlock at h
  unfold_except
  split at h
  · exact nomatch h
  · obtain ⟨rfl, rfl⟩ := h; omega

/-- When `decompressRLEBlock` succeeds, the returned position is `pos + 1`.
    The RLE block consumes exactly 1 byte from the input (the repeated byte). -/
theorem decompressRLEBlock_pos_eq (data : ByteArray) (pos : Nat)
    (blockSize : UInt32) (result : ByteArray) (pos' : Nat)
    (h : Zip.Native.decompressRLEBlock data pos blockSize = .ok (result, pos')) :
    pos' = pos + 1 := by
  unfold Zip.Native.decompressRLEBlock at h
  unfold_except
  split at h
  · exact nomatch h
  · obtain ⟨rfl, rfl⟩ := h; rfl

/-- When `decompressRLEBlock` succeeds, the returned position is within data bounds. -/
theorem decompressRLEBlock_le_size (data : ByteArray) (pos : Nat)
    (blockSize : UInt32) (output : ByteArray) (pos' : Nat)
    (h : Zip.Native.decompressRLEBlock data pos blockSize = .ok (output, pos')) :
    pos' ≤ data.size := by
  unfold Zip.Native.decompressRLEBlock at h
  unfold_except
  split at h
  · exact nomatch h
  · obtain ⟨rfl, rfl⟩ := h; omega

/-- When `decompressRawBlock` succeeds, each output byte equals the corresponding
    input byte at offset `pos + i`. Raw blocks copy input verbatim. -/
theorem decompressRawBlock_content (data : ByteArray) (pos : Nat)
    (blockSize : UInt32) (result : ByteArray) (pos' : Nat)
    (h : Zip.Native.decompressRawBlock data pos blockSize = .ok (result, pos'))
    (i : Nat) (hi : i < result.size) :
    result[i] = data[pos + i]'(by
      have := decompressRawBlock_size data pos blockSize result pos' h
      have := decompressRawBlock_pos_eq data pos blockSize result pos' h
      unfold Zip.Native.decompressRawBlock at h
      unfold_except
      split at h
      · exact nomatch h
      · obtain ⟨rfl, rfl⟩ := h; simp only [ByteArray.size_extract] at hi; omega) := by
  unfold Zip.Native.decompressRawBlock at h
  unfold_except
  split at h
  · exact nomatch h
  · obtain ⟨rfl, rfl⟩ := h
    simp only [ByteArray.getElem_extract]

/-! ## Frame-level output guarantees -/

/-- When `decompressFrame` succeeds and the frame header specifies a content size of `n`,
    the decompressed output has exactly `n` bytes. This follows from the content size
    validation guard at the end of `decompressFrame`. -/
theorem decompressFrame_contentSize_eq (data : ByteArray) (pos : Nat)
    (output : ByteArray) (pos' : Nat)
    (h : Zip.Native.decompressFrame data pos = .ok (output, pos'))
    (header : Zip.Native.ZstdFrameHeader) (headerPos : Nat)
    (hh : Zip.Native.parseFrameHeader data pos = .ok (header, headerPos))
    (n : UInt64) (hn : header.contentSize = some n) :
    output.size.toUInt64 = n := by
  unfold Zip.Native.decompressFrame at h
  dsimp only [Bind.bind, Except.bind] at h
  rw [hh] at h
  unfold_except
  -- Substitute contentSize = some n to resolve the contentSize match
  simp only [hn] at h
  -- grind handles the remaining deeply nested monadic case-splitting:
  -- dictionary check, decompressBlocks, checksum guard, content size guard.
  -- Manual `split at h` would require 4-6 nested blocks with no clarity benefit.
  grind

/-- When `decompressFrame` succeeds and the frame header has `contentChecksum = true`,
    the output's XXH64 upper 32 bits matches the checksum stored in the 4 bytes
    before `pos'` in the input. This follows from the checksum verification guard
    in `decompressFrame`. -/
theorem decompressFrame_checksum_valid (data : ByteArray) (pos : Nat)
    (output : ByteArray) (pos' : Nat)
    (h : Zip.Native.decompressFrame data pos = .ok (output, pos'))
    (header : Zip.Native.ZstdFrameHeader) (headerPos : Nat)
    (hh : Zip.Native.parseFrameHeader data pos = .ok (header, headerPos))
    (hc : header.contentChecksum = true) :
    XxHash64.xxHash64Upper32 output =
      Binary.readUInt32LE data (pos' - 4) := by
  unfold Zip.Native.decompressFrame at h
  dsimp only [Bind.bind, Except.bind] at h
  rw [hh] at h
  unfold_except
  -- Substitute contentChecksum = true to resolve the checksum conditionals
  simp only [hc] at h
  -- grind handles the remaining deeply nested monadic case-splitting:
  -- dictionary check, decompressBlocks, data size guard, checksum comparison,
  -- content size check. Manual `split at h` would require 4-6 nested blocks.
  grind

/-! ## Skippable frame specification -/

/-- When `skipSkippableFrame` succeeds, the returned position is exactly
    `pos + 8 + frameSize` where `frameSize` is the 4-byte little-endian value
    at `pos + 4` in the input data. -/
theorem skipSkippableFrame_pos_eq (data : ByteArray) (pos : Nat)
    (pos' : Nat)
    (h : Zip.Native.skipSkippableFrame data pos = .ok pos') :
    pos' = pos + 8 + (Binary.readUInt32LE data (pos + 4)).toNat := by
  unfold Zip.Native.skipSkippableFrame at h
  unfold_except
  split at h
  · exact nomatch h
  · split at h
    · exact nomatch h
    · split at h
      · exact nomatch h
      · exact (Except.ok.inj h).symm

/-- When `skipSkippableFrame` succeeds, the returned position is strictly greater than
    the input position. The skippable frame header is 8 bytes, so the result is at least
    `pos + 8`. -/
theorem skipSkippableFrame_pos_gt (data : ByteArray) (pos : Nat)
    (pos' : Nat)
    (h : Zip.Native.skipSkippableFrame data pos = .ok pos') :
    pos' > pos := by
  have := skipSkippableFrame_pos_eq data pos pos' h
  omega

/-- When `skipSkippableFrame` succeeds, the returned position is within data bounds. -/
theorem skipSkippableFrame_le_size (data : ByteArray) (pos pos' : Nat)
    (h : Zip.Native.skipSkippableFrame data pos = .ok pos') :
    pos' ≤ data.size := by
  unfold Zip.Native.skipSkippableFrame at h
  unfold_except
  split at h
  · exact nomatch h
  · split at h
    · exact nomatch h
    · split at h
      · exact nomatch h
      · have := Except.ok.inj h; omega

/-! ## Block loop structural lemmas -/

/-- When `decompressBlocksWF` succeeds, the output ByteArray is at least as large as
    the input `output` parameter. Blocks only append data, never shrink the output. -/
theorem decompressBlocksWF_output_size_ge (data : ByteArray) (off : Nat)
    (windowSize : UInt64) (output : ByteArray) (prevHuff : Option Zip.Native.ZstdHuffmanTable)
    (prevFse : Zip.Native.PrevFseTables) (history : Array Nat)
    (result : ByteArray) (pos' : Nat)
    (h : Zip.Native.decompressBlocksWF data off windowSize output prevHuff prevFse history
      = .ok (result, pos')) :
    result.size ≥ output.size := by
  unfold Zip.Native.decompressBlocksWF at h
  unfold_except
  -- Peel off error cases: off guard, parseBlockHeader, blockSize, windowSize
  split at h; next => exact nomatch h
  split at h; next => exact nomatch h
  split at h; next => exact nomatch h
  split at h; next => exact nomatch h
  split at h  -- blockType: raw | rle | compressed | reserved
  · -- raw
    split at h; next => exact nomatch h
    split at h  -- lastBlock
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
      simp only [ByteArray.size_append]; omega
    · split at h; next => exact nomatch h  -- position guard
      have ih := decompressBlocksWF_output_size_ge _ _ _ _ _ _ _ _ _ h
      simp only [ByteArray.size_append] at ih; omega
  · -- rle
    split at h; next => exact nomatch h
    split at h  -- lastBlock
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
      simp only [ByteArray.size_append]; omega
    · split at h; next => exact nomatch h  -- position guard
      have ih := decompressBlocksWF_output_size_ge _ _ _ _ _ _ _ _ _ h
      simp only [ByteArray.size_append] at ih; omega
  · -- compressed
    split at h; next => exact nomatch h  -- blockEnd guard
    split at h; next => exact nomatch h  -- parseLiteralsSection
    split at h; next => exact nomatch h  -- parseSequencesHeader
    split at h  -- numSeq == 0
    · split at h  -- lastBlock
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
        simp only [ByteArray.size_append]; omega
      · split at h; next => exact nomatch h  -- position guard
        have ih := decompressBlocksWF_output_size_ge _ _ _ _ _ _ _ _ _ h
        simp only [ByteArray.size_append] at ih; omega
    · -- numSeq > 0
      split at h; next => exact nomatch h  -- resolveSequenceFseTables
      split at h; next => exact nomatch h  -- BackwardBitReader.init
      split at h; next => exact nomatch h  -- decodeSequences
      split at h; next => exact nomatch h  -- executeSequences
      split at h  -- lastBlock
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
        simp only [ByteArray.size_append]; omega
      · split at h; next => exact nomatch h  -- position guard
        have ih := decompressBlocksWF_output_size_ge _ _ _ _ _ _ _ _ _ h
        simp only [ByteArray.size_append] at ih; omega
  · exact nomatch h  -- reserved

private theorem getElem!_ba_append_left (a b : ByteArray) (i : Nat) (h : i < a.size) :
    (a ++ b)[i]! = a[i]! := by
  rw [getElem!_pos (a ++ b) i (by simp only [ByteArray.size_append]; omega),
      getElem!_pos a i h]
  exact ByteArray.getElem_append_left h

/-- When `decompressBlocksWF` succeeds, every byte that was in the `output` buffer
    before the call is present at the same index in the result. This is the
    content-level counterpart to `decompressBlocksWF_output_size_ge`. Together
    they establish that block decompression is append-only. -/
theorem decompressBlocksWF_prefix (data : ByteArray) (off : Nat)
    (windowSize : UInt64) (output : ByteArray) (prevHuff : Option Zip.Native.ZstdHuffmanTable)
    (prevFse : Zip.Native.PrevFseTables) (history : Array Nat)
    (result : ByteArray) (pos' : Nat)
    (h : Zip.Native.decompressBlocksWF data off windowSize output prevHuff prevFse history
      = .ok (result, pos'))
    (i : Nat) (hi : i < output.size) :
    result[i]! = output[i]! := by
  unfold Zip.Native.decompressBlocksWF at h
  unfold_except
  -- Peel off error cases: off guard, parseBlockHeader, blockSize, windowSize
  split at h; next => exact nomatch h
  split at h; next => exact nomatch h
  split at h; next => exact nomatch h
  split at h; next => exact nomatch h
  split at h  -- blockType: raw | rle | compressed | reserved
  · -- raw
    split at h; next => exact nomatch h
    split at h  -- lastBlock
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
      exact getElem!_ba_append_left _ _ _ hi
    · split at h; next => exact nomatch h  -- position guard
      have ih := decompressBlocksWF_prefix _ _ _ _ _ _ _ _ _ h i
        (by simp only [ByteArray.size_append]; omega)
      rw [ih, getElem!_ba_append_left _ _ _ hi]
  · -- rle
    split at h; next => exact nomatch h
    split at h  -- lastBlock
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
      exact getElem!_ba_append_left _ _ _ hi
    · split at h; next => exact nomatch h  -- position guard
      have ih := decompressBlocksWF_prefix _ _ _ _ _ _ _ _ _ h i
        (by simp only [ByteArray.size_append]; omega)
      rw [ih, getElem!_ba_append_left _ _ _ hi]
  · -- compressed
    split at h; next => exact nomatch h  -- blockEnd guard
    split at h; next => exact nomatch h  -- parseLiteralsSection
    split at h; next => exact nomatch h  -- parseSequencesHeader
    split at h  -- numSeq == 0
    · split at h  -- lastBlock
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
        exact getElem!_ba_append_left _ _ _ hi
      · split at h; next => exact nomatch h  -- position guard
        have ih := decompressBlocksWF_prefix _ _ _ _ _ _ _ _ _ h i
          (by simp only [ByteArray.size_append]; omega)
        rw [ih, getElem!_ba_append_left _ _ _ hi]
    · -- numSeq > 0
      split at h; next => exact nomatch h  -- resolveSequenceFseTables
      split at h; next => exact nomatch h  -- BackwardBitReader.init
      split at h; next => exact nomatch h  -- decodeSequences
      split at h; next => exact nomatch h  -- executeSequences
      split at h  -- lastBlock
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
        exact getElem!_ba_append_left _ _ _ hi
      · split at h; next => exact nomatch h  -- position guard
        have ih := decompressBlocksWF_prefix _ _ _ _ _ _ _ _ _ h i
          (by simp only [ByteArray.size_append]; omega)
        rw [ih, getElem!_ba_append_left _ _ _ hi]
  · exact nomatch h  -- reserved

/-- When `decompressBlocksWF` succeeds, the returned position is strictly greater
    than the input offset. Each block header is at least 3 bytes. -/
theorem decompressBlocksWF_pos_gt (data : ByteArray) (off : Nat)
    (windowSize : UInt64) (output : ByteArray) (prevHuff : Option Zip.Native.ZstdHuffmanTable)
    (prevFse : Zip.Native.PrevFseTables) (history : Array Nat)
    (result : ByteArray) (pos' : Nat)
    (h : Zip.Native.decompressBlocksWF data off windowSize output prevHuff prevFse history
      = .ok (result, pos')) :
    pos' > off := by
  unfold Zip.Native.decompressBlocksWF at h
  unfold_except
  -- Peel off error cases: off guard, parseBlockHeader, blockSize, windowSize
  split at h; next => exact nomatch h
  split at h; next => exact nomatch h
  split at h; next => exact nomatch h
  split at h; next => exact nomatch h
  split at h  -- blockType: raw | rle | compressed | reserved
  · -- raw
    split at h; next => exact nomatch h
    split at h  -- lastBlock
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
      have h1 := parseBlockHeader_pos_eq _ _ _ _ (by assumption)
      have h2 := decompressRawBlock_pos_eq _ _ _ _ _ (by assumption)
      omega
    · split at h; next => exact nomatch h  -- position guard
      have ih := decompressBlocksWF_pos_gt _ _ _ _ _ _ _ _ _ h
      omega
  · -- rle
    split at h; next => exact nomatch h
    split at h  -- lastBlock
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
      have h1 := parseBlockHeader_pos_eq _ _ _ _ (by assumption)
      have h2 := decompressRLEBlock_pos_eq _ _ _ _ _ (by assumption)
      omega
    · split at h; next => exact nomatch h  -- position guard
      have ih := decompressBlocksWF_pos_gt _ _ _ _ _ _ _ _ _ h
      omega
  · -- compressed
    split at h; next => exact nomatch h  -- blockEnd guard
    split at h; next => exact nomatch h  -- parseLiteralsSection
    split at h; next => exact nomatch h  -- parseSequencesHeader
    split at h  -- numSeq == 0
    · split at h  -- lastBlock
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
        have h1 := parseBlockHeader_pos_eq _ _ _ _ (by assumption)
        omega
      · split at h; next => exact nomatch h  -- position guard
        have ih := decompressBlocksWF_pos_gt _ _ _ _ _ _ _ _ _ h
        omega
    · -- numSeq > 0
      split at h; next => exact nomatch h  -- resolveSequenceFseTables
      split at h; next => exact nomatch h  -- BackwardBitReader.init
      split at h; next => exact nomatch h  -- decodeSequences
      split at h; next => exact nomatch h  -- executeSequences
      split at h  -- lastBlock
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
        have h1 := parseBlockHeader_pos_eq _ _ _ _ (by assumption)
        omega
      · split at h; next => exact nomatch h  -- position guard
        have ih := decompressBlocksWF_pos_gt _ _ _ _ _ _ _ _ _ h
        omega
  · exact nomatch h  -- reserved

/-- When `decompressBlocksWF` succeeds, the returned position is within the
    data bounds. This is the block-loop level of the le_size campaign. -/
theorem decompressBlocksWF_le_size (data : ByteArray) (off : Nat)
    (windowSize : UInt64) (output : ByteArray) (prevHuff : Option Zip.Native.ZstdHuffmanTable)
    (prevFse : Zip.Native.PrevFseTables) (history : Array Nat)
    (result : ByteArray) (pos' : Nat)
    (h : Zip.Native.decompressBlocksWF data off windowSize output prevHuff prevFse history
      = .ok (result, pos')) :
    pos' ≤ data.size := by
  unfold Zip.Native.decompressBlocksWF at h
  unfold_except
  split at h; next => exact nomatch h
  split at h; next => exact nomatch h
  split at h; next => exact nomatch h
  split at h; next => exact nomatch h
  split at h  -- blockType: raw | rle | compressed | reserved
  · -- raw
    split at h; next => exact nomatch h
    split at h  -- lastBlock
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
      exact decompressRawBlock_le_size _ _ _ _ _ (by assumption)
    · split at h; next => exact nomatch h
      exact decompressBlocksWF_le_size _ _ _ _ _ _ _ _ _ h
  · -- rle
    split at h; next => exact nomatch h
    split at h  -- lastBlock
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
      exact decompressRLEBlock_le_size _ _ _ _ _ (by assumption)
    · split at h; next => exact nomatch h
      exact decompressBlocksWF_le_size _ _ _ _ _ _ _ _ _ h
  · -- compressed
    split at h; next => exact nomatch h  -- blockEnd guard
    rename_i hbe
    split at h; next => exact nomatch h  -- parseLiteralsSection
    split at h; next => exact nomatch h  -- parseSequencesHeader
    split at h  -- numSeq == 0
    · split at h  -- lastBlock
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
        omega
      · split at h; next => exact nomatch h
        exact decompressBlocksWF_le_size _ _ _ _ _ _ _ _ _ h
    · -- numSeq > 0
      split at h; next => exact nomatch h  -- resolveSequenceFseTables
      split at h; next => exact nomatch h  -- BackwardBitReader.init
      split at h; next => exact nomatch h  -- decodeSequences
      split at h; next => exact nomatch h  -- executeSequences
      split at h  -- lastBlock
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
        omega
      · split at h; next => exact nomatch h
        exact decompressBlocksWF_le_size _ _ _ _ _ _ _ _ _ h
  · exact nomatch h  -- reserved

/-! ## decompressBlocksWF content properties -/

/-- When `decompressBlocksWF` encounters a single raw last block, the result is
    the accumulated output extended by the raw block content, and the position
    after the raw data. -/
theorem decompressBlocksWF_single_raw (data : ByteArray) (off : Nat)
    (windowSize : UInt64) (output : ByteArray) (prevHuff : Option Zip.Native.ZstdHuffmanTable)
    (prevFse : Zip.Native.PrevFseTables) (history : Array Nat)
    (hdr : Zip.Native.ZstdBlockHeader) (afterHdr : Nat)
    (block : ByteArray) (afterBlock : Nat)
    (hoff : ¬ data.size ≤ off)
    (hparse : Zip.Native.parseBlockHeader data off = .ok (hdr, afterHdr))
    (hbs : ¬ hdr.blockSize > 131072)
    (hws : ¬ (windowSize > 0 && hdr.blockSize.toUInt64 > windowSize))
    (htype : hdr.blockType = .raw)
    (hraw : Zip.Native.decompressRawBlock data afterHdr hdr.blockSize = .ok (block, afterBlock))
    (hlast : hdr.lastBlock = true) :
    Zip.Native.decompressBlocksWF data off windowSize output prevHuff prevFse history
      = .ok (output ++ block, afterBlock) := by
  unfold Zip.Native.decompressBlocksWF
  simp only [hoff, ↓reduceDIte, hparse, hbs, hws, bind, Except.bind, pure, Except.pure,
    ↓reduceIte, htype, hraw, hlast, Bool.false_eq_true]

/-- When `decompressBlocksWF` encounters a single RLE last block, the result is
    the accumulated output extended by the RLE block content, and the position
    after the RLE byte. -/
theorem decompressBlocksWF_single_rle (data : ByteArray) (off : Nat)
    (windowSize : UInt64) (output : ByteArray) (prevHuff : Option Zip.Native.ZstdHuffmanTable)
    (prevFse : Zip.Native.PrevFseTables) (history : Array Nat)
    (hdr : Zip.Native.ZstdBlockHeader) (afterHdr : Nat)
    (block : ByteArray) (afterByte : Nat)
    (hoff : ¬ data.size ≤ off)
    (hparse : Zip.Native.parseBlockHeader data off = .ok (hdr, afterHdr))
    (hbs : ¬ hdr.blockSize > 131072)
    (hws : ¬ (windowSize > 0 && hdr.blockSize.toUInt64 > windowSize))
    (htype : hdr.blockType = .rle)
    (hrle : Zip.Native.decompressRLEBlock data afterHdr hdr.blockSize = .ok (block, afterByte))
    (hlast : hdr.lastBlock = true) :
    Zip.Native.decompressBlocksWF data off windowSize output prevHuff prevFse history
      = .ok (output ++ block, afterByte) := by
  unfold Zip.Native.decompressBlocksWF
  simp only [hoff, ↓reduceDIte, hparse, hbs, hws, bind, Except.bind, pure, Except.pure,
    ↓reduceIte, htype, hrle, hlast, Bool.false_eq_true]

/-! ## decompressBlocksWF step theorems -/

/-- When `decompressBlocksWF` encounters a non-last raw block, it recurses with
    `output ++ block` and position `afterBlock`. The Huffman table, FSE tables,
    and offset history are unchanged (raw blocks don't update them). -/
theorem decompressBlocksWF_raw_step (data : ByteArray) (off : Nat)
    (windowSize : UInt64) (output : ByteArray) (prevHuff : Option Zip.Native.ZstdHuffmanTable)
    (prevFse : Zip.Native.PrevFseTables) (history : Array Nat)
    (hdr : Zip.Native.ZstdBlockHeader) (afterHdr : Nat)
    (block : ByteArray) (afterBlock : Nat)
    (hoff : ¬ data.size ≤ off)
    (hparse : Zip.Native.parseBlockHeader data off = .ok (hdr, afterHdr))
    (hbs : ¬ hdr.blockSize > 131072)
    (hws : ¬ (windowSize > 0 && hdr.blockSize.toUInt64 > windowSize))
    (htype : hdr.blockType = .raw)
    (hraw : Zip.Native.decompressRawBlock data afterHdr hdr.blockSize = .ok (block, afterBlock))
    (hnotlast : hdr.lastBlock = false)
    (hadv : ¬ afterBlock ≤ off) :
    Zip.Native.decompressBlocksWF data off windowSize output prevHuff prevFse history
      = Zip.Native.decompressBlocksWF data afterBlock windowSize (output ++ block)
          prevHuff prevFse history := by
  generalize heq : Zip.Native.decompressBlocksWF data afterBlock windowSize
    (output ++ block) prevHuff prevFse history = rhs
  unfold Zip.Native.decompressBlocksWF
  simp only [hoff, ↓reduceDIte, hparse, hbs, hws, htype, hraw, hnotlast, hadv,
    bind, Except.bind, pure, Except.pure, ↓reduceIte, Bool.false_eq_true]
  exact heq

/-- When `decompressBlocksWF` encounters a non-last RLE block, it recurses with
    `output ++ block` and position `afterByte`. The Huffman table, FSE tables,
    and offset history are unchanged (RLE blocks don't update them). -/
theorem decompressBlocksWF_rle_step (data : ByteArray) (off : Nat)
    (windowSize : UInt64) (output : ByteArray) (prevHuff : Option Zip.Native.ZstdHuffmanTable)
    (prevFse : Zip.Native.PrevFseTables) (history : Array Nat)
    (hdr : Zip.Native.ZstdBlockHeader) (afterHdr : Nat)
    (block : ByteArray) (afterByte : Nat)
    (hoff : ¬ data.size ≤ off)
    (hparse : Zip.Native.parseBlockHeader data off = .ok (hdr, afterHdr))
    (hbs : ¬ hdr.blockSize > 131072)
    (hws : ¬ (windowSize > 0 && hdr.blockSize.toUInt64 > windowSize))
    (htype : hdr.blockType = .rle)
    (hrle : Zip.Native.decompressRLEBlock data afterHdr hdr.blockSize = .ok (block, afterByte))
    (hnotlast : hdr.lastBlock = false)
    (hadv : ¬ afterByte ≤ off) :
    Zip.Native.decompressBlocksWF data off windowSize output prevHuff prevFse history
      = Zip.Native.decompressBlocksWF data afterByte windowSize (output ++ block)
          prevHuff prevFse history := by
  generalize heq : Zip.Native.decompressBlocksWF data afterByte windowSize
    (output ++ block) prevHuff prevFse history = rhs
  unfold Zip.Native.decompressBlocksWF
  simp only [hoff, ↓reduceDIte, hparse, hbs, hws, htype, hrle, hnotlast, hadv,
    bind, Except.bind, pure, Except.pure, ↓reduceIte, Bool.false_eq_true]
  exact heq

/-! ## decompressBlocksWF two-block composition theorems -/

/-- When `decompressBlocksWF` encounters two consecutive raw blocks (first non-last,
    second last), the output is `output ++ block1 ++ block2` at the position after
    the second block. Composes `decompressBlocksWF_raw_step` and
    `decompressBlocksWF_single_raw`. -/
theorem decompressBlocksWF_two_raw_blocks (data : ByteArray) (off : Nat)
    (windowSize : UInt64) (output : ByteArray)
    (prevHuff : Option Zip.Native.ZstdHuffmanTable)
    (prevFse : Zip.Native.PrevFseTables) (history : Array Nat)
    -- Block 1 (non-last raw)
    (hdr1 : Zip.Native.ZstdBlockHeader) (afterHdr1 : Nat)
    (block1 : ByteArray) (afterBlock1 : Nat)
    -- Block 2 (last raw)
    (hdr2 : Zip.Native.ZstdBlockHeader) (afterHdr2 : Nat)
    (block2 : ByteArray) (afterBlock2 : Nat)
    -- Block 1 hypotheses
    (hoff1 : ¬ data.size ≤ off)
    (hparse1 : Zip.Native.parseBlockHeader data off = .ok (hdr1, afterHdr1))
    (hbs1 : ¬ hdr1.blockSize > 131072)
    (hws1 : ¬ (windowSize > 0 && hdr1.blockSize.toUInt64 > windowSize))
    (htype1 : hdr1.blockType = .raw)
    (hraw1 : Zip.Native.decompressRawBlock data afterHdr1 hdr1.blockSize
               = .ok (block1, afterBlock1))
    (hnotlast1 : hdr1.lastBlock = false)
    (hadv1 : ¬ afterBlock1 ≤ off)
    -- Block 2 hypotheses
    (hoff2 : ¬ data.size ≤ afterBlock1)
    (hparse2 : Zip.Native.parseBlockHeader data afterBlock1 = .ok (hdr2, afterHdr2))
    (hbs2 : ¬ hdr2.blockSize > 131072)
    (hws2 : ¬ (windowSize > 0 && hdr2.blockSize.toUInt64 > windowSize))
    (htype2 : hdr2.blockType = .raw)
    (hraw2 : Zip.Native.decompressRawBlock data afterHdr2 hdr2.blockSize
               = .ok (block2, afterBlock2))
    (hlast2 : hdr2.lastBlock = true) :
    Zip.Native.decompressBlocksWF data off windowSize output prevHuff prevFse history
      = .ok (output ++ block1 ++ block2, afterBlock2) := by
  rw [decompressBlocksWF_raw_step data off windowSize output prevHuff prevFse history
    hdr1 afterHdr1 block1 afterBlock1 hoff1 hparse1 hbs1 hws1 htype1 hraw1 hnotlast1 hadv1]
  rw [decompressBlocksWF_single_raw data afterBlock1 windowSize (output ++ block1) prevHuff
    prevFse history hdr2 afterHdr2 block2 afterBlock2 hoff2 hparse2 hbs2 hws2 htype2 hraw2
    hlast2]

/-- When `decompressBlocksWF` encounters two consecutive RLE blocks (first non-last,
    second last), the output is `output ++ block1 ++ block2` at the position after
    the second block's byte. Composes `decompressBlocksWF_rle_step` and
    `decompressBlocksWF_single_rle`. -/
theorem decompressBlocksWF_two_rle_blocks (data : ByteArray) (off : Nat)
    (windowSize : UInt64) (output : ByteArray)
    (prevHuff : Option Zip.Native.ZstdHuffmanTable)
    (prevFse : Zip.Native.PrevFseTables) (history : Array Nat)
    -- Block 1 (non-last RLE)
    (hdr1 : Zip.Native.ZstdBlockHeader) (afterHdr1 : Nat)
    (block1 : ByteArray) (afterByte1 : Nat)
    -- Block 2 (last RLE)
    (hdr2 : Zip.Native.ZstdBlockHeader) (afterHdr2 : Nat)
    (block2 : ByteArray) (afterByte2 : Nat)
    -- Block 1 hypotheses
    (hoff1 : ¬ data.size ≤ off)
    (hparse1 : Zip.Native.parseBlockHeader data off = .ok (hdr1, afterHdr1))
    (hbs1 : ¬ hdr1.blockSize > 131072)
    (hws1 : ¬ (windowSize > 0 && hdr1.blockSize.toUInt64 > windowSize))
    (htype1 : hdr1.blockType = .rle)
    (hrle1 : Zip.Native.decompressRLEBlock data afterHdr1 hdr1.blockSize
               = .ok (block1, afterByte1))
    (hnotlast1 : hdr1.lastBlock = false)
    (hadv1 : ¬ afterByte1 ≤ off)
    -- Block 2 hypotheses
    (hoff2 : ¬ data.size ≤ afterByte1)
    (hparse2 : Zip.Native.parseBlockHeader data afterByte1 = .ok (hdr2, afterHdr2))
    (hbs2 : ¬ hdr2.blockSize > 131072)
    (hws2 : ¬ (windowSize > 0 && hdr2.blockSize.toUInt64 > windowSize))
    (htype2 : hdr2.blockType = .rle)
    (hrle2 : Zip.Native.decompressRLEBlock data afterHdr2 hdr2.blockSize
               = .ok (block2, afterByte2))
    (hlast2 : hdr2.lastBlock = true) :
    Zip.Native.decompressBlocksWF data off windowSize output prevHuff prevFse history
      = .ok (output ++ block1 ++ block2, afterByte2) := by
  rw [decompressBlocksWF_rle_step data off windowSize output prevHuff prevFse history
    hdr1 afterHdr1 block1 afterByte1 hoff1 hparse1 hbs1 hws1 htype1 hrle1 hnotlast1 hadv1]
  rw [decompressBlocksWF_single_rle data afterByte1 windowSize (output ++ block1) prevHuff
    prevFse history hdr2 afterHdr2 block2 afterByte2 hoff2 hparse2 hbs2 hws2 htype2 hrle2
    hlast2]

/-- When `decompressBlocksWF` encounters a single last compressed block with
    numSeq == 0 (literals only, no sequence commands), the result is the
    accumulated output extended by the literal data at position blockEnd. -/
theorem decompressBlocksWF_single_compressed_literals_only (data : ByteArray)
    (off : Nat) (windowSize : UInt64) (output : ByteArray)
    (prevHuffTree : Option Zip.Native.ZstdHuffmanTable)
    (prevFseTables : Zip.Native.PrevFseTables)
    (offsetHistory : Array Nat)
    (hdr : Zip.Native.ZstdBlockHeader) (afterHdr : Nat)
    (literals : ByteArray) (afterLiterals : Nat)
    (huffTree : Option Zip.Native.ZstdHuffmanTable)
    (modes : Zip.Native.SequenceCompressionModes) (afterSeqHeader : Nat)
    (hoff : ¬ data.size ≤ off)
    (hparse : Zip.Native.parseBlockHeader data off = .ok (hdr, afterHdr))
    (hbs : ¬ hdr.blockSize > 131072)
    (hws : ¬ (windowSize > 0 && hdr.blockSize.toUInt64 > windowSize))
    (htype : hdr.blockType = .compressed)
    (hblockEnd : ¬ data.size < afterHdr + hdr.blockSize.toNat)
    (hlit : Zip.Native.parseLiteralsSection data afterHdr prevHuffTree
      = .ok (literals, afterLiterals, huffTree))
    (hseq : Zip.Native.parseSequencesHeader data afterLiterals
      = .ok (0, modes, afterSeqHeader))
    (hlast : hdr.lastBlock = true) :
    Zip.Native.decompressBlocksWF data off windowSize output prevHuffTree prevFseTables
        offsetHistory
      = .ok (output ++ literals, afterHdr + hdr.blockSize.toNat) := by
  unfold Zip.Native.decompressBlocksWF
  simp only [hoff, ↓reduceDIte, hparse, hbs, hws, bind, Except.bind, pure, Except.pure,
    ↓reduceIte, htype, hblockEnd, hlit, Except.mapError.eq_2, hseq, beq_self_eq_true,
    hlast, Bool.false_eq_true]

/-- When `decompressBlocksWF` encounters a non-last compressed block with
    numSeq == 0 (literals only), it recurses with `output ++ literals`,
    updated Huffman table (keeping new tree if present, otherwise preserving
    previous), unchanged FSE tables and offset history, and position at blockEnd. -/
theorem decompressBlocksWF_compressed_literals_only_step (data : ByteArray)
    (off : Nat) (windowSize : UInt64) (output : ByteArray)
    (prevHuffTree : Option Zip.Native.ZstdHuffmanTable)
    (prevFseTables : Zip.Native.PrevFseTables)
    (offsetHistory : Array Nat)
    (hdr : Zip.Native.ZstdBlockHeader) (afterHdr : Nat)
    (literals : ByteArray) (afterLiterals : Nat)
    (huffTree : Option Zip.Native.ZstdHuffmanTable)
    (modes : Zip.Native.SequenceCompressionModes) (afterSeqHeader : Nat)
    (hoff : ¬ data.size ≤ off)
    (hparse : Zip.Native.parseBlockHeader data off = .ok (hdr, afterHdr))
    (hbs : ¬ hdr.blockSize > 131072)
    (hws : ¬ (windowSize > 0 && hdr.blockSize.toUInt64 > windowSize))
    (htype : hdr.blockType = .compressed)
    (hblockEnd : ¬ data.size < afterHdr + hdr.blockSize.toNat)
    (hlit : Zip.Native.parseLiteralsSection data afterHdr prevHuffTree
      = .ok (literals, afterLiterals, huffTree))
    (hseq : Zip.Native.parseSequencesHeader data afterLiterals
      = .ok (0, modes, afterSeqHeader))
    (hnotlast : hdr.lastBlock = false)
    (hadv : ¬ afterHdr + hdr.blockSize.toNat ≤ off) :
    Zip.Native.decompressBlocksWF data off windowSize output prevHuffTree prevFseTables
        offsetHistory
      = Zip.Native.decompressBlocksWF data (afterHdr + hdr.blockSize.toNat) windowSize
          (output ++ literals)
          (if let some ht := huffTree then some ht else prevHuffTree)
          prevFseTables offsetHistory := by
  rw [show Zip.Native.decompressBlocksWF data off windowSize output prevHuffTree
    prevFseTables offsetHistory = _ from by unfold Zip.Native.decompressBlocksWF; rfl]
  simp only [hoff, ↓reduceDIte, hparse, hbs, hws, bind, Except.bind, pure, Except.pure,
    ↓reduceIte, htype, hblockEnd, hlit, Except.mapError.eq_2, hseq, beq_self_eq_true,
    hnotlast, Bool.false_eq_true, hadv]
  congr 1
  cases huffTree <;> rfl

/-! ## Frame header position advancement -/

/-- When `parseFrameHeader` succeeds, the returned position advances by at
    least 5 (4 magic bytes + 1 descriptor byte). In practice the minimum
    is 6 bytes (singleSegment frames have at least 1 byte of content size). -/
theorem parseFrameHeader_pos_ge_five (data : ByteArray) (pos : Nat)
    (header : Zip.Native.ZstdFrameHeader) (pos' : Nat)
    (h : Zip.Native.parseFrameHeader data pos = .ok (header, pos')) :
    pos' ≥ pos + 5 := by
  unfold Zip.Native.parseFrameHeader at h
  dsimp only [Bind.bind, Except.bind] at h
  by_cases h1 : data.size < pos + 4
  · rw [if_pos h1] at h; exact nomatch h
  · rw [if_neg h1] at h
    simp only [pure, Pure.pure] at h
    by_cases h2 : (Binary.readUInt32LE data pos != Zip.Native.zstdMagic) = true
    · rw [if_pos h2] at h; exact nomatch h
    · rw [if_neg h2] at h
      by_cases h3 : data.size < pos + 4 + 1
      · rw [if_pos h3] at h; exact nomatch h
      · rw [if_neg h3] at h
        split at h
        · exact nomatch h
        · simp only [Except.pure] at h
          repeat split at h
          iterate 5 (all_goals (try (first | contradiction | (split at h))))
          all_goals first
            | contradiction
            | (simp only [Except.ok.injEq, Prod.mk.injEq] at h
               obtain ⟨-, rfl⟩ := h; omega)

/-- When `parseFrameHeader` succeeds, the returned position is strictly greater
    than the input position. The header is at least 6 bytes (4 magic + 1
    descriptor + at least 1 byte for window descriptor or content size). -/
theorem parseFrameHeader_pos_gt (data : ByteArray) (pos : Nat)
    (header : Zip.Native.ZstdFrameHeader) (pos' : Nat)
    (h : Zip.Native.parseFrameHeader data pos = .ok (header, pos')) :
    pos' > pos := by
  have := parseFrameHeader_pos_ge_five data pos header pos' h; omega

/-- When `parseFrameHeader` succeeds, the returned position is within data bounds.
    Each stage of the header has a bounds check (`data.size < off + N → throw`),
    so on the success path, `off + N ≤ data.size` holds at every stage. The final
    returned position is the last `off`, bounded by the last check. -/
theorem parseFrameHeader_le_size (data : ByteArray) (pos : Nat)
    (header : Zip.Native.ZstdFrameHeader) (pos' : Nat)
    (h : Zip.Native.parseFrameHeader data pos = .ok (header, pos')) :
    pos' ≤ data.size := by
  unfold Zip.Native.parseFrameHeader at h
  dsimp only [Bind.bind, Except.bind] at h
  by_cases h1 : data.size < pos + 4
  · rw [if_pos h1] at h; exact nomatch h
  · rw [if_neg h1] at h
    simp only [pure, Pure.pure] at h
    by_cases h2 : (Binary.readUInt32LE data pos != Zip.Native.zstdMagic) = true
    · rw [if_pos h2] at h; exact nomatch h
    · rw [if_neg h2] at h
      by_cases h3 : data.size < pos + 4 + 1
      · rw [if_pos h3] at h; exact nomatch h
      · rw [if_neg h3] at h
        split at h
        · exact nomatch h
        · simp only [Except.pure] at h
          repeat split at h
          iterate 5 (all_goals (try (first | contradiction | (split at h))))
          all_goals first
            | contradiction
            | (simp only [Except.ok.injEq, Prod.mk.injEq] at h
               obtain ⟨-, rfl⟩ := h; omega)

/-! ## Window size characterizing properties -/

set_option maxRecDepth 1024 in
/-- The minimum window size is 1KB (RFC 8878 §3.1.1.1.2: windowLog ≥ 10,
    so windowBase ≥ 2^10 = 1024 and windowAdd ≥ 0). -/
theorem windowSizeFromDescriptor_ge_1024 (d : UInt8) :
    Zip.Native.windowSizeFromDescriptor d ≥ 1024 := by
  have h : ∀ i : Fin 256, Zip.Native.windowSizeFromDescriptor ⟨⟨i⟩⟩ ≥ 1024 := by decide
  exact h d.toBitVec.toFin

/-- The window size is always positive (follows from `windowSizeFromDescriptor_ge_1024`). -/
theorem windowSizeFromDescriptor_pos (d : UInt8) :
    Zip.Native.windowSizeFromDescriptor d > 0 := by
  exact Nat.lt_of_lt_of_le (by decide : (0 : UInt64) < 1024) (windowSizeFromDescriptor_ge_1024 d)

/-! ## Frame-level position advancement -/

/-- When `decompressFrame` succeeds, the returned position is strictly greater
    than the input position. This follows from `parseFrameHeader_pos_gt`
    (header ≥ 6 bytes) and `decompressBlocksWF_pos_gt` (blocks ≥ 3 bytes),
    plus an optional 4-byte checksum. -/
theorem decompressFrame_pos_gt (data : ByteArray) (pos : Nat)
    (output : ByteArray) (pos' : Nat)
    (h : Zip.Native.decompressFrame data pos = .ok (output, pos')) :
    pos' > pos := by
  unfold Zip.Native.decompressFrame at h
  cases hph : Zip.Native.parseFrameHeader data pos with
  | error e => simp only [hph, bind, Except.bind] at h; exact nomatch h
  | ok val =>
    obtain ⟨header, afterHeader⟩ := val
    have hgt1 := parseFrameHeader_pos_gt _ _ _ _ hph
    simp only [hph, bind, Except.bind, pure, Except.pure] at h
    -- Dictionary check then decompressBlocks
    split at h  -- dictionaryId
    · -- some dictId
      split at h  -- dictId != 0
      · exact nomatch h
      · unfold Zip.Native.decompressBlocks at h
        cases hdb : Zip.Native.decompressBlocksWF data afterHeader header.windowSize
            ByteArray.empty none {} #[1, 4, 8] with
        | error e => simp only [hdb] at h; exact nomatch h
        | ok val2 =>
          obtain ⟨content, afterBlocks⟩ := val2
          have hgt2 := decompressBlocksWF_pos_gt _ _ _ _ _ _ _ _ _ hdb
          simp only [hdb] at h
          -- grind handles nested checksum/contentSize case-splitting and
          -- propagates pos' > pos from hgt1 and hgt2 through all branches.
          grind
    · -- none
      unfold Zip.Native.decompressBlocks at h
      cases hdb : Zip.Native.decompressBlocksWF data afterHeader header.windowSize
          ByteArray.empty none {} #[1, 4, 8] with
      | error e => simp only [hdb] at h; exact nomatch h
      | ok val2 =>
        obtain ⟨content, afterBlocks⟩ := val2
        have hgt2 := decompressBlocksWF_pos_gt _ _ _ _ _ _ _ _ _ hdb
        simp only [hdb] at h
        -- grind handles nested checksum/contentSize case-splitting and
        -- propagates pos' > pos from hgt1 and hgt2 through all branches.
        grind

/-- When `decompressFrame` succeeds, the returned position is within data bounds.
    This is the frame-level capstone of the le_size campaign: it composes
    `decompressBlocksWF_le_size` with the checksum bounds guard. -/
theorem decompressFrame_le_size (data : ByteArray) (pos : Nat)
    (output : ByteArray) (pos' : Nat)
    (h : Zip.Native.decompressFrame data pos = .ok (output, pos')) :
    pos' ≤ data.size := by
  unfold Zip.Native.decompressFrame at h
  cases hph : Zip.Native.parseFrameHeader data pos with
  | error e => simp only [hph, bind, Except.bind] at h; exact nomatch h
  | ok val =>
    obtain ⟨header, afterHeader⟩ := val
    simp only [hph, bind, Except.bind, pure, Except.pure] at h
    split at h  -- dictionaryId
    · -- some dictId
      split at h  -- dictId != 0
      · exact nomatch h
      · unfold Zip.Native.decompressBlocks at h
        cases hdb : Zip.Native.decompressBlocksWF data afterHeader header.windowSize
            ByteArray.empty none {} #[1, 4, 8] with
        | error e => simp only [hdb] at h; exact nomatch h
        | ok val2 =>
          obtain ⟨content, afterBlocks⟩ := val2
          have hle := decompressBlocksWF_le_size _ _ _ _ _ _ _ _ _ hdb
          simp only [hdb] at h
          grind
    · -- none
      unfold Zip.Native.decompressBlocks at h
      cases hdb : Zip.Native.decompressBlocksWF data afterHeader header.windowSize
          ByteArray.empty none {} #[1, 4, 8] with
      | error e => simp only [hdb] at h; exact nomatch h
      | ok val2 =>
        obtain ⟨content, afterBlocks⟩ := val2
        have hle := decompressBlocksWF_le_size _ _ _ _ _ _ _ _ _ hdb
        simp only [hdb] at h
        grind

/-! ## Frame-level content characterization -/

/-- When `decompressFrame` succeeds and the frame contains a single raw last block,
    the output equals the raw block content. Composes `decompressBlocksWF_single_raw`
    with the frame-level dictionary check, checksum, and content size validation. -/
theorem decompressFrame_single_raw_content (data : ByteArray) (pos : Nat)
    (output : ByteArray) (pos' : Nat)
    (header : Zip.Native.ZstdFrameHeader) (afterHeader : Nat)
    (hdr : Zip.Native.ZstdBlockHeader) (afterHdr : Nat)
    (block : ByteArray) (afterBlock : Nat)
    (hframe : Zip.Native.decompressFrame data pos = .ok (output, pos'))
    (hh : Zip.Native.parseFrameHeader data pos = .ok (header, afterHeader))
    (_hdict : header.dictionaryId = none ∨ header.dictionaryId = some 0)
    (hparse : Zip.Native.parseBlockHeader data afterHeader = .ok (hdr, afterHdr))
    (hbs : ¬ hdr.blockSize > 131072)
    (hws : ¬ (header.windowSize > 0 && hdr.blockSize.toUInt64 > header.windowSize))
    (htype : hdr.blockType = .raw)
    (hraw : Zip.Native.decompressRawBlock data afterHdr hdr.blockSize = .ok (block, afterBlock))
    (hlast : hdr.lastBlock = true) :
    output = block := by
  -- Derive that the block loop offset is within bounds
  have hoff : ¬ data.size ≤ afterHeader := by
    have := parseBlockHeader_le_size data afterHeader hdr afterHdr hparse
    have := parseBlockHeader_pos_eq data afterHeader hdr afterHdr hparse
    omega
  -- Compute the exact block loop result
  have hblocks := decompressBlocksWF_single_raw data afterHeader header.windowSize
    ByteArray.empty none {} #[1, 4, 8] hdr afterHdr block afterBlock
    hoff hparse hbs hws htype hraw hlast
  -- Unfold decompressFrame and substitute the frame header result
  unfold Zip.Native.decompressFrame at hframe
  dsimp only [Bind.bind, Except.bind] at hframe
  rw [hh] at hframe
  simp only [pure, Except.pure] at hframe
  -- Handle dictionary check, then substitute known block result
  split at hframe
  · -- dictionaryId = some dictId
    split at hframe
    · exact nomatch hframe  -- dictId != 0 throws
    · unfold Zip.Native.decompressBlocks at hframe
      rw [hblocks] at hframe
      simp only [ByteArray.empty_append] at hframe
      grind
  · -- dictionaryId = none
    unfold Zip.Native.decompressBlocks at hframe
    rw [hblocks] at hframe
    simp only [ByteArray.empty_append] at hframe
    grind

/-- When `decompressFrame` succeeds and the frame contains a single RLE last block,
    the output equals the RLE block content. Composes `decompressBlocksWF_single_rle`
    with the frame-level dictionary check, checksum, and content size validation. -/
theorem decompressFrame_single_rle_content (data : ByteArray) (pos : Nat)
    (output : ByteArray) (pos' : Nat)
    (header : Zip.Native.ZstdFrameHeader) (afterHeader : Nat)
    (hdr : Zip.Native.ZstdBlockHeader) (afterHdr : Nat)
    (block : ByteArray) (afterByte : Nat)
    (hframe : Zip.Native.decompressFrame data pos = .ok (output, pos'))
    (hh : Zip.Native.parseFrameHeader data pos = .ok (header, afterHeader))
    (_hdict : header.dictionaryId = none ∨ header.dictionaryId = some 0)
    (hparse : Zip.Native.parseBlockHeader data afterHeader = .ok (hdr, afterHdr))
    (hbs : ¬ hdr.blockSize > 131072)
    (hws : ¬ (header.windowSize > 0 && hdr.blockSize.toUInt64 > header.windowSize))
    (htype : hdr.blockType = .rle)
    (hrle : Zip.Native.decompressRLEBlock data afterHdr hdr.blockSize = .ok (block, afterByte))
    (hlast : hdr.lastBlock = true) :
    output = block := by
  -- Derive that the block loop offset is within bounds
  have hoff : ¬ data.size ≤ afterHeader := by
    have := parseBlockHeader_le_size data afterHeader hdr afterHdr hparse
    have := parseBlockHeader_pos_eq data afterHeader hdr afterHdr hparse
    omega
  -- Compute the exact block loop result
  have hblocks := decompressBlocksWF_single_rle data afterHeader header.windowSize
    ByteArray.empty none {} #[1, 4, 8] hdr afterHdr block afterByte
    hoff hparse hbs hws htype hrle hlast
  -- Unfold decompressFrame and substitute the frame header result
  unfold Zip.Native.decompressFrame at hframe
  dsimp only [Bind.bind, Except.bind] at hframe
  rw [hh] at hframe
  simp only [pure, Except.pure] at hframe
  -- Handle dictionary check, then substitute known block result
  split at hframe
  · -- dictionaryId = some dictId
    split at hframe
    · exact nomatch hframe  -- dictId != 0 throws
    · unfold Zip.Native.decompressBlocks at hframe
      rw [hblocks] at hframe
      simp only [ByteArray.empty_append] at hframe
      grind
  · -- dictionaryId = none
    unfold Zip.Native.decompressBlocks at hframe
    rw [hblocks] at hframe
    simp only [ByteArray.empty_append] at hframe
    grind

/-! ## decompressBlocksWF compressed sequences content -/

/-- When `decompressBlocksWF` encounters a single last compressed block with
    sequences (numSeq > 0), the result is the accumulated output extended by
    the sequence execution output, at position `afterHdr + blockSize`. -/
theorem decompressBlocksWF_single_compressed_sequences (data : ByteArray)
    (off : Nat) (windowSize : UInt64) (output : ByteArray)
    (prevHuffTree : Option Zip.Native.ZstdHuffmanTable)
    (prevFseTables : Zip.Native.PrevFseTables)
    (offsetHistory : Array Nat)
    (hdr : Zip.Native.ZstdBlockHeader) (afterHdr : Nat)
    (literals : ByteArray) (afterLiterals : Nat)
    (huffTree : Option Zip.Native.ZstdHuffmanTable)
    (numSeq : Nat) (modes : Zip.Native.SequenceCompressionModes) (afterSeqHeader : Nat)
    (llTable ofTable mlTable : Zip.Native.FseTable) (afterTables : Nat)
    (bbr : Zip.Native.BackwardBitReader)
    (sequences : Array Zip.Native.ZstdSequence)
    (blockOutput : ByteArray) (newHist : Array Nat)
    (hoff : ¬ data.size ≤ off)
    (hparse : Zip.Native.parseBlockHeader data off = .ok (hdr, afterHdr))
    (hbs : ¬ hdr.blockSize > 131072)
    (hws : ¬ (windowSize > 0 && hdr.blockSize.toUInt64 > windowSize))
    (htype : hdr.blockType = .compressed)
    (hblockEnd : ¬ data.size < afterHdr + hdr.blockSize.toNat)
    (hlit : Zip.Native.parseLiteralsSection data afterHdr prevHuffTree
              = .ok (literals, afterLiterals, huffTree))
    (hseq : Zip.Native.parseSequencesHeader data afterLiterals
              = .ok (numSeq, modes, afterSeqHeader))
    (hNumSeq : ¬ numSeq == 0)
    (hfse : Zip.Native.resolveSequenceFseTables modes data afterSeqHeader prevFseTables
              = .ok (llTable, ofTable, mlTable, afterTables))
    (hbbr : Zip.Native.BackwardBitReader.init data afterTables (afterHdr + hdr.blockSize.toNat)
              = .ok bbr)
    (hdec : Zip.Native.decodeSequences llTable ofTable mlTable bbr numSeq
              = .ok sequences)
    (hexec : Zip.Native.executeSequences sequences literals
               (if windowSize > 0 && output.size > windowSize.toNat
                then output.extract (output.size - windowSize.toNat) output.size
                else output)
               offsetHistory windowSize.toNat
               = .ok (blockOutput, newHist))
    (hlast : hdr.lastBlock = true) :
    Zip.Native.decompressBlocksWF data off windowSize output prevHuffTree prevFseTables
      offsetHistory
      = .ok (output ++ blockOutput, afterHdr + hdr.blockSize.toNat) := by
  unfold Zip.Native.decompressBlocksWF
  simp only [hoff, ↓reduceDIte, hparse, hbs, hws, bind, Except.bind, pure, Except.pure,
    ↓reduceIte, htype, hblockEnd, hlit, Except.mapError, hseq, hNumSeq, hfse, hbbr,
    hdec, hexec, hlast, Bool.false_eq_true]

/-- When `decompressBlocksWF` encounters a non-last compressed block with
    sequences (numSeq > 0), the result is a recursive call with updated
    output, Huffman table, FSE tables, and offset history. -/
theorem decompressBlocksWF_compressed_sequences_step (data : ByteArray)
    (off : Nat) (windowSize : UInt64) (output : ByteArray)
    (prevHuffTree : Option Zip.Native.ZstdHuffmanTable)
    (prevFseTables : Zip.Native.PrevFseTables)
    (offsetHistory : Array Nat)
    (hdr : Zip.Native.ZstdBlockHeader) (afterHdr : Nat)
    (literals : ByteArray) (afterLiterals : Nat)
    (huffTree : Option Zip.Native.ZstdHuffmanTable)
    (numSeq : Nat) (modes : Zip.Native.SequenceCompressionModes) (afterSeqHeader : Nat)
    (llTable ofTable mlTable : Zip.Native.FseTable) (afterTables : Nat)
    (bbr : Zip.Native.BackwardBitReader)
    (sequences : Array Zip.Native.ZstdSequence)
    (blockOutput : ByteArray) (newHist : Array Nat)
    (hoff : ¬ data.size ≤ off)
    (hparse : Zip.Native.parseBlockHeader data off = .ok (hdr, afterHdr))
    (hbs : ¬ hdr.blockSize > 131072)
    (hws : ¬ (windowSize > 0 && hdr.blockSize.toUInt64 > windowSize))
    (htype : hdr.blockType = .compressed)
    (hblockEnd : ¬ data.size < afterHdr + hdr.blockSize.toNat)
    (hlit : Zip.Native.parseLiteralsSection data afterHdr prevHuffTree
              = .ok (literals, afterLiterals, huffTree))
    (hseq : Zip.Native.parseSequencesHeader data afterLiterals
              = .ok (numSeq, modes, afterSeqHeader))
    (hNumSeq : ¬ numSeq == 0)
    (hfse : Zip.Native.resolveSequenceFseTables modes data afterSeqHeader prevFseTables
              = .ok (llTable, ofTable, mlTable, afterTables))
    (hbbr : Zip.Native.BackwardBitReader.init data afterTables (afterHdr + hdr.blockSize.toNat)
              = .ok bbr)
    (hdec : Zip.Native.decodeSequences llTable ofTable mlTable bbr numSeq
              = .ok sequences)
    (hexec : Zip.Native.executeSequences sequences literals
               (if windowSize > 0 && output.size > windowSize.toNat
                then output.extract (output.size - windowSize.toNat) output.size
                else output)
               offsetHistory windowSize.toNat
               = .ok (blockOutput, newHist))
    (hnotlast : hdr.lastBlock = false)
    (hadv : ¬ (afterHdr + hdr.blockSize.toNat) ≤ off) :
    Zip.Native.decompressBlocksWF data off windowSize output prevHuffTree prevFseTables
      offsetHistory
      = Zip.Native.decompressBlocksWF data (afterHdr + hdr.blockSize.toNat) windowSize
          (output ++ blockOutput)
          (if let some ht := huffTree then some ht else prevHuffTree)
          { litLen := some llTable, offset := some ofTable, matchLen := some mlTable }
          newHist := by
  rw [show Zip.Native.decompressBlocksWF data off windowSize output prevHuffTree
    prevFseTables offsetHistory = _ from by unfold Zip.Native.decompressBlocksWF; rfl]
  simp only [hoff, ↓reduceDIte, hparse, hbs, hws, bind, Except.bind, pure, Except.pure,
    ↓reduceIte, htype, hblockEnd, hlit, Except.mapError, hseq, hNumSeq, hfse, hbbr,
    hdec, hexec, hnotlast, Bool.false_eq_true, hadv]
  congr 1; cases huffTree <;> rfl

end Zstd.Spec
