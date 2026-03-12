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

-- Unfold `decompressFrame`, substitute `hh` (parseFrameHeader result) and `hblocks`
-- (block-loop result), then handle the dictionary check and close both branches with grind.
-- This 19-line pattern is identical across all ~20 frame-level content theorems.
set_option hygiene false in
local macro "frame_from_blocks" : tactic =>
  `(tactic| (
    unfold Zip.Native.decompressFrame at hframe
    dsimp only [Bind.bind, Except.bind] at hframe
    rw [hh] at hframe
    simp only [pure, Except.pure] at hframe
    split at hframe
    · split at hframe
      · exact nomatch hframe
      · unfold Zip.Native.decompressBlocks at hframe
        rw [hblocks] at hframe
        simp only [ByteArray.empty_append] at hframe
        grind
    · unfold Zip.Native.decompressBlocks at hframe
      rw [hblocks] at hframe
      simp only [ByteArray.empty_append] at hframe
      grind))

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

/-- When `parseBlockHeader` succeeds, the data extends past `pos`. Combines
    `parseBlockHeader_le_size` and `parseBlockHeader_pos_eq` to derive that
    `pos` is within data bounds. Used pervasively in frame-level content proofs
    to establish the block loop's offset guard. -/
theorem parseBlockHeader_data_not_le (data : ByteArray) (pos : Nat)
    (hdr : Zip.Native.ZstdBlockHeader) (afterHdr : Nat)
    (hparse : Zip.Native.parseBlockHeader data pos = .ok (hdr, afterHdr)) :
    ¬ data.size ≤ pos := by
  have := parseBlockHeader_le_size data pos hdr afterHdr hparse
  have := parseBlockHeader_pos_eq data pos hdr afterHdr hparse
  omega

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

/-! ## Parsing completeness -/

/-- When the data has at least 3 bytes from `pos` and the 2-bit block type field
    is not the reserved value (3), `parseBlockHeader` succeeds. -/
theorem parseBlockHeader_succeeds (data : ByteArray) (pos : Nat)
    (hsize : data.size ≥ pos + 3)
    (htypeVal : ((data[pos]!.toUInt32 ||| (data[pos + 1]!.toUInt32 <<< 8)
        ||| (data[pos + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 ≠ 3) :
    ∃ hdr afterHdr, Zip.Native.parseBlockHeader data pos = .ok (hdr, afterHdr) := by
  unfold Zip.Native.parseBlockHeader
  simp only [show ¬(data.size < pos + 3) from by omega, ↓reduceIte,
    bind, Except.bind, pure, Except.pure]
  -- The match on typeVal has branches for 0, 1, 2, and the catch-all (reserved).
  -- htypeVal eliminates the catch-all, so one of the first three branches applies.
  split
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩
  · -- Catch-all: typeVal ∉ {0,1,2} from split, and ≠ 3 from htypeVal.
    -- But typeVal = expr &&& 3 can only be 0-3, contradiction.
    exfalso; rename_i _ h0 h1 h2; bv_decide

/-- When the data has at least `blockSize.toNat` bytes from `pos`,
    `decompressRawBlock` succeeds. -/
theorem decompressRawBlock_succeeds (data : ByteArray) (pos : Nat) (blockSize : UInt32)
    (hsize : data.size ≥ pos + blockSize.toNat) :
    ∃ block afterBlock, Zip.Native.decompressRawBlock data pos blockSize
        = .ok (block, afterBlock) := by
  unfold Zip.Native.decompressRawBlock
  simp only [show ¬(data.size < pos + blockSize.toNat) from by omega, ↓reduceIte]
  exact ⟨_, _, rfl⟩

/-- When the data has at least 1 byte from `pos`, `decompressRLEBlock` succeeds. -/
theorem decompressRLEBlock_succeeds (data : ByteArray) (pos : Nat) (blockSize : UInt32)
    (hsize : data.size ≥ pos + 1) :
    ∃ block afterBlock, Zip.Native.decompressRLEBlock data pos blockSize
        = .ok (block, afterBlock) := by
  unfold Zip.Native.decompressRLEBlock
  simp only [show ¬(data.size < pos + 1) from by omega, ↓reduceIte]
  exact ⟨_, _, rfl⟩

/-! ### parseBlockHeader field characterization -/

/-- When `parseBlockHeader` succeeds, `hdr.lastBlock` equals whether bit 0 of the
    3-byte little-endian header word is set. -/
theorem parseBlockHeader_lastBlock_eq (data : ByteArray) (pos : Nat)
    (hdr : Zip.Native.ZstdBlockHeader) (afterHdr : Nat)
    (h : Zip.Native.parseBlockHeader data pos = .ok (hdr, afterHdr)) :
    hdr.lastBlock = ((data[pos]!.toUInt32 ||| (data[pos + 1]!.toUInt32 <<< 8)
      ||| (data[pos + 2]!.toUInt32 <<< 16)) &&& 1 == 1) := by
  unfold Zip.Native.parseBlockHeader at h
  unfold_except
  split at h
  · exact nomatch h
  · split at h
    · obtain ⟨rfl, rfl⟩ := h; rfl
    · obtain ⟨rfl, rfl⟩ := h; rfl
    · obtain ⟨rfl, rfl⟩ := h; rfl
    · exact nomatch h

/-- When `parseBlockHeader` succeeds, `hdr.blockType` is determined by bits 1-2 of
    the 3-byte little-endian header word: 0→raw, 1→rle, 2→compressed. -/
theorem parseBlockHeader_blockType_eq (data : ByteArray) (pos : Nat)
    (hdr : Zip.Native.ZstdBlockHeader) (afterHdr : Nat)
    (h : Zip.Native.parseBlockHeader data pos = .ok (hdr, afterHdr)) :
    (let raw24 := data[pos]!.toUInt32 ||| (data[pos + 1]!.toUInt32 <<< 8)
      ||| (data[pos + 2]!.toUInt32 <<< 16)
     let typeVal := (raw24 >>> 1) &&& 3
     (typeVal = 0 → hdr.blockType = .raw) ∧
     (typeVal = 1 → hdr.blockType = .rle) ∧
     (typeVal = 2 → hdr.blockType = .compressed)) := by
  unfold Zip.Native.parseBlockHeader at h
  unfold_except
  split at h
  · exact nomatch h
  · split at h
    · obtain ⟨rfl, rfl⟩ := h; simp_all
    · obtain ⟨rfl, rfl⟩ := h; simp_all
    · obtain ⟨rfl, rfl⟩ := h; simp_all
    · exact nomatch h

/-- When `parseBlockHeader` succeeds, `hdr.blockSize` equals bits 3-23 of the
    3-byte little-endian header word. -/
theorem parseBlockHeader_blockSize_eq (data : ByteArray) (pos : Nat)
    (hdr : Zip.Native.ZstdBlockHeader) (afterHdr : Nat)
    (h : Zip.Native.parseBlockHeader data pos = .ok (hdr, afterHdr)) :
    hdr.blockSize = (data[pos]!.toUInt32 ||| (data[pos + 1]!.toUInt32 <<< 8)
      ||| (data[pos + 2]!.toUInt32 <<< 16)) >>> 3 := by
  unfold Zip.Native.parseBlockHeader at h
  unfold_except
  split at h
  · exact nomatch h
  · split at h
    · obtain ⟨rfl, rfl⟩ := h; rfl
    · obtain ⟨rfl, rfl⟩ := h; rfl
    · obtain ⟨rfl, rfl⟩ := h; rfl
    · exact nomatch h

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

/-- When the data has at least 8 bytes for the header plus `frameSize` bytes for the
    payload, and the magic number is in the skippable range, `skipSkippableFrame` succeeds. -/
theorem skipSkippableFrame_succeeds (data : ByteArray) (pos : Nat)
    (hsize : data.size ≥ pos + 8)
    (hmagic_lo : Binary.readUInt32LE data pos ≥ 0x184D2A50)
    (hmagic_hi : Binary.readUInt32LE data pos ≤ 0x184D2A5F)
    (hpayload : data.size ≥ pos + 8 + (Binary.readUInt32LE data (pos + 4)).toNat) :
    ∃ pos', Zip.Native.skipSkippableFrame data pos = .ok pos' := by
  unfold Zip.Native.skipSkippableFrame
  simp only [show ¬(data.size < pos + 8) from by omega, ↓reduceIte,
    bind, Except.bind, pure, Except.pure]
  have h1 : ¬(Binary.readUInt32LE data pos < 0x184D2A50) := Nat.not_lt.mpr hmagic_lo
  have h2 : ¬(Binary.readUInt32LE data pos > 0x184D2A5F) := Nat.not_lt.mpr hmagic_hi
  have h3 : ¬(data.size < pos + 8 + (Binary.readUInt32LE data (pos + 4)).toNat) :=
    Nat.not_lt.mpr hpayload
  simp only [decide_eq_false h1, decide_eq_false h2, Bool.false_or, if_neg h3]
  exact ⟨_, rfl⟩

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

/-! ## decompressBlocksWF composed completeness -/

/-- When a single raw last block is encoded at offset `off`, with sufficient
    data for header + payload, `decompressBlocksWF` succeeds. This chains
    `parseBlockHeader_succeeds` → field characterization → `decompressRawBlock_succeeds`
    → `decompressBlocksWF_single_raw` into a single theorem with only raw-byte-level
    preconditions. -/
theorem decompressBlocksWF_succeeds_single_raw (data : ByteArray)
    (off : Nat) (windowSize : UInt64) (output : ByteArray)
    (prevHuff : Option Zip.Native.ZstdHuffmanTable)
    (prevFse : Zip.Native.PrevFseTables) (history : Array Nat)
    (hsize : data.size ≥ off + 3)
    (htypeVal : ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
        ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 0)
    (hlastBit : (data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
        ||| (data[off + 2]!.toUInt32 <<< 16)) &&& 1 = 1)
    (hblockSize : ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
        ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow : ¬ (windowSize > 0 &&
        ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
          ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > windowSize))
    (hpayload : data.size ≥ off + 3 +
        (((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
          ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3).toNat)) :
    ∃ result pos',
      Zip.Native.decompressBlocksWF data off windowSize output prevHuff prevFse history
        = .ok (result, pos') := by
  -- Step 1: parseBlockHeader succeeds (typeVal=0 ≠ 3)
  have htypeNe3 : ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
      ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 ≠ 3 := by
    rw [htypeVal]; decide
  obtain ⟨hdr, afterHdr, hparse⟩ := parseBlockHeader_succeeds data off hsize htypeNe3
  -- Step 2: Extract field values from the existential result
  have htype := (parseBlockHeader_blockType_eq data off hdr afterHdr hparse).1 htypeVal
  have hlast_eq := parseBlockHeader_lastBlock_eq data off hdr afterHdr hparse
  have hbs_eq := parseBlockHeader_blockSize_eq data off hdr afterHdr hparse
  have hpos_eq := parseBlockHeader_pos_eq data off hdr afterHdr hparse
  -- Step 3: Derive lastBlock = true from hlastBit
  have hlast : hdr.lastBlock = true := by rw [hlast_eq, hlastBit]; decide
  -- Step 4: Derive blockSize and window size constraints
  have hbs : ¬ hdr.blockSize > 131072 := by rw [hbs_eq]; exact Nat.not_lt.mpr hblockSize
  have hws : ¬ (windowSize > 0 && hdr.blockSize.toUInt64 > windowSize) := by
    rw [hbs_eq]; exact hwindow
  -- Step 5: decompressRawBlock succeeds (afterHdr = off + 3, sufficient payload)
  have hpayload' : data.size ≥ afterHdr + hdr.blockSize.toNat := by
    rw [hpos_eq, hbs_eq]; omega
  obtain ⟨block, afterBlock, hraw⟩ := decompressRawBlock_succeeds data afterHdr
    hdr.blockSize hpayload'
  -- Step 6: Compose via decompressBlocksWF_single_raw
  have hoff : ¬ data.size ≤ off := by omega
  exact ⟨_, _, decompressBlocksWF_single_raw data off windowSize output prevHuff prevFse
    history hdr afterHdr block afterBlock hoff hparse hbs hws htype hraw hlast⟩

/-- When a single RLE last block is encoded at offset `off`, with sufficient
    data for header + 1 byte payload, `decompressBlocksWF` succeeds. This chains
    `parseBlockHeader_succeeds` → field characterization → `decompressRLEBlock_succeeds`
    → `decompressBlocksWF_single_rle` into a single theorem with only raw-byte-level
    preconditions. -/
theorem decompressBlocksWF_succeeds_single_rle (data : ByteArray)
    (off : Nat) (windowSize : UInt64) (output : ByteArray)
    (prevHuff : Option Zip.Native.ZstdHuffmanTable)
    (prevFse : Zip.Native.PrevFseTables) (history : Array Nat)
    (hsize : data.size ≥ off + 3)
    (htypeVal : ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
        ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 1)
    (hlastBit : (data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
        ||| (data[off + 2]!.toUInt32 <<< 16)) &&& 1 = 1)
    (hblockSize : ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
        ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow : ¬ (windowSize > 0 &&
        ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
          ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > windowSize))
    (hpayload : data.size ≥ off + 4) :
    ∃ result pos',
      Zip.Native.decompressBlocksWF data off windowSize output prevHuff prevFse history
        = .ok (result, pos') := by
  -- Step 1: parseBlockHeader succeeds (typeVal=1 ≠ 3)
  have htypeNe3 : ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
      ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 ≠ 3 := by
    rw [htypeVal]; decide
  obtain ⟨hdr, afterHdr, hparse⟩ := parseBlockHeader_succeeds data off hsize htypeNe3
  -- Step 2: Extract field values from the existential result
  have htype := (parseBlockHeader_blockType_eq data off hdr afterHdr hparse).2.1 htypeVal
  have hlast_eq := parseBlockHeader_lastBlock_eq data off hdr afterHdr hparse
  have hbs_eq := parseBlockHeader_blockSize_eq data off hdr afterHdr hparse
  have hpos_eq := parseBlockHeader_pos_eq data off hdr afterHdr hparse
  -- Step 3: Derive lastBlock = true from hlastBit
  have hlast : hdr.lastBlock = true := by rw [hlast_eq, hlastBit]; decide
  -- Step 4: Derive blockSize and window size constraints
  have hbs : ¬ hdr.blockSize > 131072 := by rw [hbs_eq]; exact Nat.not_lt.mpr hblockSize
  have hws : ¬ (windowSize > 0 && hdr.blockSize.toUInt64 > windowSize) := by
    rw [hbs_eq]; exact hwindow
  -- Step 5: decompressRLEBlock succeeds (afterHdr = off + 3, need 1 byte)
  have hpayload' : data.size ≥ afterHdr + 1 := by rw [hpos_eq]; omega
  obtain ⟨block, afterByte, hrle⟩ := decompressRLEBlock_succeeds data afterHdr
    hdr.blockSize hpayload'
  -- Step 6: Compose via decompressBlocksWF_single_rle
  have hoff : ¬ data.size ≤ off := by omega
  exact ⟨_, _, decompressBlocksWF_single_rle data off windowSize output prevHuff prevFse
    history hdr afterHdr block afterByte hoff hparse hbs hws htype hrle hlast⟩

/-! ## decompressFrame composed completeness -/

/-- When a frame contains a single raw last block, with no dictionary, no content
    checksum, and no declared content size, `decompressFrame` succeeds. This composes
    `parseFrameHeader` success with `decompressBlocksWF_succeeds_single_raw` and
    threads through the frame-level dictionary/checksum/size guards. -/
theorem decompressFrame_succeeds_single_raw (data : ByteArray) (pos : Nat)
    (header : Zip.Native.ZstdFrameHeader) (afterHeader : Nat)
    (hparse : Zip.Native.parseFrameHeader data pos = .ok (header, afterHeader))
    (hnodict : header.dictionaryId = none)
    (hnocksum : header.contentChecksum = false)
    (hnosize : header.contentSize = none)
    (hsize : data.size ≥ afterHeader + 3)
    (htypeVal : ((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
        ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 0)
    (hlastBit : (data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
        ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) &&& 1 = 1)
    (hblockSize : ((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
        ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow : ¬ (header.windowSize > 0 &&
        ((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
          ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > header.windowSize))
    (hpayload : data.size ≥ afterHeader + 3 +
        (((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
          ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3).toNat)) :
    ∃ content pos',
      Zip.Native.decompressFrame data pos = .ok (content, pos') := by
  -- Step 1: Get block-level success from byte-level conditions
  obtain ⟨result, blockPos, hblocks⟩ := decompressBlocksWF_succeeds_single_raw
    data afterHeader header.windowSize ByteArray.empty none {} #[1, 4, 8]
    hsize htypeVal hlastBit hblockSize hwindow hpayload
  -- Step 2: Unfold decompressFrame and thread through
  unfold Zip.Native.decompressFrame
  simp only [bind, Except.bind, pure, Except.pure, hparse]
  -- Step 3: Dictionary check — header.dictionaryId = none, so if-let doesn't match
  simp only [hnodict]
  -- Step 4: Block decompression succeeds
  unfold Zip.Native.decompressBlocks
  rw [hblocks]
  -- Step 5: Checksum is false, content size is none — both guards are trivial
  simp only [hnocksum, hnosize, Bool.false_eq_true, ↓reduceIte]
  exact ⟨_, _, rfl⟩

/-- When a frame contains a single RLE last block, with no dictionary, no content
    checksum, and no declared content size, `decompressFrame` succeeds. This composes
    `parseFrameHeader` success with `decompressBlocksWF_succeeds_single_rle` and
    threads through the frame-level dictionary/checksum/size guards. -/
theorem decompressFrame_succeeds_single_rle (data : ByteArray) (pos : Nat)
    (header : Zip.Native.ZstdFrameHeader) (afterHeader : Nat)
    (hparse : Zip.Native.parseFrameHeader data pos = .ok (header, afterHeader))
    (hnodict : header.dictionaryId = none)
    (hnocksum : header.contentChecksum = false)
    (hnosize : header.contentSize = none)
    (hsize : data.size ≥ afterHeader + 3)
    (htypeVal : ((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
        ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 1)
    (hlastBit : (data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
        ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) &&& 1 = 1)
    (hblockSize : ((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
        ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow : ¬ (header.windowSize > 0 &&
        ((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
          ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > header.windowSize))
    (hpayload : data.size ≥ afterHeader + 4) :
    ∃ content pos',
      Zip.Native.decompressFrame data pos = .ok (content, pos') := by
  -- Step 1: Get block-level success from byte-level conditions
  obtain ⟨result, blockPos, hblocks⟩ := decompressBlocksWF_succeeds_single_rle
    data afterHeader header.windowSize ByteArray.empty none {} #[1, 4, 8]
    hsize htypeVal hlastBit hblockSize hwindow hpayload
  -- Step 2: Unfold decompressFrame and thread through
  unfold Zip.Native.decompressFrame
  simp only [bind, Except.bind, pure, Except.pure, hparse]
  -- Step 3: Dictionary check — header.dictionaryId = none, so if-let doesn't match
  simp only [hnodict]
  -- Step 4: Block decompression succeeds
  unfold Zip.Native.decompressBlocks
  rw [hblocks]
  -- Step 5: Checksum is false, content size is none — both guards are trivial
  simp only [hnocksum, hnosize, Bool.false_eq_true, ↓reduceIte]
  exact ⟨_, _, rfl⟩

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

/-! ## decompressBlocksWF two-block composed completeness (homogeneous) -/

/-- When two consecutive raw blocks are encoded at byte level (first non-last at `off`,
    second last at `off2`), `decompressBlocksWF` succeeds. Composes
    `parseBlockHeader_succeeds` + field characterization + `decompressRawBlock_succeeds`
    for block 1, then `decompressBlocksWF_raw_step` to advance, and
    `decompressBlocksWF_succeeds_single_raw` for block 2. -/
theorem decompressBlocksWF_succeeds_two_raw_blocks (data : ByteArray)
    (off off2 : Nat) (windowSize : UInt64) (output : ByteArray)
    (prevHuff : Option Zip.Native.ZstdHuffmanTable)
    (prevFse : Zip.Native.PrevFseTables) (history : Array Nat)
    -- Block 1 byte-level conditions (non-last raw at off)
    (hsize1 : data.size ≥ off + 3)
    (htypeVal1 : ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
        ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 0)
    (hlastBit1 : (data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
        ||| (data[off + 2]!.toUInt32 <<< 16)) &&& 1 = 0)
    (hblockSize1 : ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
        ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow1 : ¬ (windowSize > 0 &&
        ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
          ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > windowSize))
    (hpayload1 : data.size ≥ off + 3 +
        (((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
          ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    -- Position: off2 is after block 1 (3-byte header + blockSize payload)
    (hoff2 : off2 = off + 3 +
        (((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
          ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    -- Block 2 byte-level conditions (last raw at off2)
    (hsize2 : data.size ≥ off2 + 3)
    (htypeVal2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 0)
    (hlastBit2 : (data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) &&& 1 = 1)
    (hblockSize2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow2 : ¬ (windowSize > 0 &&
        ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
          ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > windowSize))
    (hpayload2 : data.size ≥ off2 + 3 +
        (((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
          ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toNat)) :
    ∃ result pos',
      Zip.Native.decompressBlocksWF data off windowSize output prevHuff prevFse history
        = .ok (result, pos') := by
  -- Block 1: parseBlockHeader succeeds (typeVal=0 ≠ 3)
  have htypeNe3_1 : ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
      ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 ≠ 3 := by
    rw [htypeVal1]; decide
  obtain ⟨hdr1, afterHdr1, hparse1⟩ := parseBlockHeader_succeeds data off hsize1 htypeNe3_1
  -- Block 1: field characterization
  have htype1 := (parseBlockHeader_blockType_eq data off hdr1 afterHdr1 hparse1).1 htypeVal1
  have hbs1_eq := parseBlockHeader_blockSize_eq data off hdr1 afterHdr1 hparse1
  have hpos1_eq := parseBlockHeader_pos_eq data off hdr1 afterHdr1 hparse1
  have hnotlast1 : hdr1.lastBlock = false := by
    rw [parseBlockHeader_lastBlock_eq data off hdr1 afterHdr1 hparse1, hlastBit1]; decide
  have hbs1 : ¬ hdr1.blockSize > 131072 := by rw [hbs1_eq]; exact Nat.not_lt.mpr hblockSize1
  have hws1 : ¬ (windowSize > 0 && hdr1.blockSize.toUInt64 > windowSize) := by
    rw [hbs1_eq]; exact hwindow1
  -- Block 1: decompressRawBlock succeeds
  have hpayload1' : data.size ≥ afterHdr1 + hdr1.blockSize.toNat := by
    rw [hpos1_eq, hbs1_eq]; omega
  obtain ⟨block1, afterBlock1, hraw1⟩ := decompressRawBlock_succeeds data afterHdr1
    hdr1.blockSize hpayload1'
  -- Position threading: afterBlock1 = off2
  have hAfterBlock1 : afterBlock1 = off2 := by
    rw [decompressRawBlock_pos_eq data afterHdr1 hdr1.blockSize block1 afterBlock1 hraw1,
      hpos1_eq, hbs1_eq]; exact hoff2.symm
  -- Apply raw step for block 1, rewrite position to off2
  have hoff1 : ¬ data.size ≤ off := by omega
  have hadv1 : ¬ afterBlock1 ≤ off := by rw [hAfterBlock1, hoff2]; omega
  rw [decompressBlocksWF_raw_step data off windowSize output prevHuff prevFse history
    hdr1 afterHdr1 block1 afterBlock1 hoff1 hparse1 hbs1 hws1 htype1 hraw1 hnotlast1 hadv1,
    hAfterBlock1]
  -- Apply single raw succeeds for block 2
  exact decompressBlocksWF_succeeds_single_raw data off2 windowSize (output ++ block1)
    prevHuff prevFse history hsize2 htypeVal2 hlastBit2 hblockSize2 hwindow2 hpayload2

/-- When two consecutive RLE blocks are encoded at byte level (first non-last at `off`,
    second last at `off2`), `decompressBlocksWF` succeeds. Composes
    `parseBlockHeader_succeeds` + field characterization + `decompressRLEBlock_succeeds`
    for block 1, then `decompressBlocksWF_rle_step` to advance, and
    `decompressBlocksWF_succeeds_single_rle` for block 2. -/
theorem decompressBlocksWF_succeeds_two_rle_blocks (data : ByteArray)
    (off off2 : Nat) (windowSize : UInt64) (output : ByteArray)
    (prevHuff : Option Zip.Native.ZstdHuffmanTable)
    (prevFse : Zip.Native.PrevFseTables) (history : Array Nat)
    -- Block 1 byte-level conditions (non-last RLE at off)
    (hsize1 : data.size ≥ off + 3)
    (htypeVal1 : ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
        ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 1)
    (hlastBit1 : (data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
        ||| (data[off + 2]!.toUInt32 <<< 16)) &&& 1 = 0)
    (hblockSize1 : ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
        ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow1 : ¬ (windowSize > 0 &&
        ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
          ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > windowSize))
    (hpayload1 : data.size ≥ off + 4)
    -- Position: off2 is after block 1 (3-byte header + 1-byte RLE payload)
    (hoff2 : off2 = off + 4)
    -- Block 2 byte-level conditions (last RLE at off2)
    (hsize2 : data.size ≥ off2 + 3)
    (htypeVal2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 1)
    (hlastBit2 : (data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) &&& 1 = 1)
    (hblockSize2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow2 : ¬ (windowSize > 0 &&
        ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
          ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > windowSize))
    (hpayload2 : data.size ≥ off2 + 4) :
    ∃ result pos',
      Zip.Native.decompressBlocksWF data off windowSize output prevHuff prevFse history
        = .ok (result, pos') := by
  -- Block 1: parseBlockHeader succeeds (typeVal=1 ≠ 3)
  have htypeNe3_1 : ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
      ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 ≠ 3 := by
    rw [htypeVal1]; decide
  obtain ⟨hdr1, afterHdr1, hparse1⟩ := parseBlockHeader_succeeds data off hsize1 htypeNe3_1
  -- Block 1: field characterization
  have htype1 := (parseBlockHeader_blockType_eq data off hdr1 afterHdr1 hparse1).2.1 htypeVal1
  have hbs1_eq := parseBlockHeader_blockSize_eq data off hdr1 afterHdr1 hparse1
  have hpos1_eq := parseBlockHeader_pos_eq data off hdr1 afterHdr1 hparse1
  have hnotlast1 : hdr1.lastBlock = false := by
    rw [parseBlockHeader_lastBlock_eq data off hdr1 afterHdr1 hparse1, hlastBit1]; decide
  have hbs1 : ¬ hdr1.blockSize > 131072 := by rw [hbs1_eq]; exact Nat.not_lt.mpr hblockSize1
  have hws1 : ¬ (windowSize > 0 && hdr1.blockSize.toUInt64 > windowSize) := by
    rw [hbs1_eq]; exact hwindow1
  -- Block 1: decompressRLEBlock succeeds (afterHdr = off + 3, need 1 byte)
  have hpayload1' : data.size ≥ afterHdr1 + 1 := by rw [hpos1_eq]; omega
  obtain ⟨block1, afterByte1, hrle1⟩ := decompressRLEBlock_succeeds data afterHdr1
    hdr1.blockSize hpayload1'
  -- Position threading: afterByte1 = off2
  have hAfterByte1 : afterByte1 = off2 := by
    rw [decompressRLEBlock_pos_eq data afterHdr1 hdr1.blockSize block1 afterByte1 hrle1,
      hpos1_eq]; omega
  -- Apply RLE step for block 1, rewrite position to off2
  have hoff1 : ¬ data.size ≤ off := by omega
  have hadv1 : ¬ afterByte1 ≤ off := by rw [hAfterByte1, hoff2]; omega
  rw [decompressBlocksWF_rle_step data off windowSize output prevHuff prevFse history
    hdr1 afterHdr1 block1 afterByte1 hoff1 hparse1 hbs1 hws1 htype1 hrle1 hnotlast1 hadv1,
    hAfterByte1]
  -- Apply single RLE succeeds for block 2
  exact decompressBlocksWF_succeeds_single_rle data off2 windowSize (output ++ block1)
    prevHuff prevFse history hsize2 htypeVal2 hlastBit2 hblockSize2 hwindow2 hpayload2

/-! ## decompressFrame two-block composed completeness (homogeneous) -/

/-- When a frame contains two consecutive raw blocks (first non-last, second last),
    with no dictionary, no content checksum, and no declared content size,
    `decompressFrame` succeeds. Composes `parseFrameHeader` success with
    `decompressBlocksWF_succeeds_two_raw_blocks` and threads through the
    frame-level dictionary/checksum/size guards. -/
theorem decompressFrame_succeeds_two_raw_blocks (data : ByteArray) (pos : Nat)
    (header : Zip.Native.ZstdFrameHeader) (afterHeader : Nat)
    (hparse : Zip.Native.parseFrameHeader data pos = .ok (header, afterHeader))
    (hnodict : header.dictionaryId = none)
    (hnocksum : header.contentChecksum = false)
    (hnosize : header.contentSize = none)
    -- Block 1 byte-level conditions (non-last raw at afterHeader)
    (hsize1 : data.size ≥ afterHeader + 3)
    (htypeVal1 : ((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
        ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 0)
    (hlastBit1 : (data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
        ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) &&& 1 = 0)
    (hblockSize1 : ((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
        ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow1 : ¬ (header.windowSize > 0 &&
        ((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
          ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > header.windowSize))
    (hpayload1 : data.size ≥ afterHeader + 3 +
        (((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
          ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    -- Block 2 position and byte-level conditions (last raw)
    {off2 : Nat}
    (hoff2 : off2 = afterHeader + 3 +
        (((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
          ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    (hsize2 : data.size ≥ off2 + 3)
    (htypeVal2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 0)
    (hlastBit2 : (data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) &&& 1 = 1)
    (hblockSize2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow2 : ¬ (header.windowSize > 0 &&
        ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
          ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > header.windowSize))
    (hpayload2 : data.size ≥ off2 + 3 +
        (((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
          ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toNat)) :
    ∃ content pos',
      Zip.Native.decompressFrame data pos = .ok (content, pos') := by
  -- Step 1: Get block-level success from byte-level conditions
  obtain ⟨result, blockPos, hblocks⟩ := decompressBlocksWF_succeeds_two_raw_blocks
    data afterHeader off2 header.windowSize ByteArray.empty none {} #[1, 4, 8]
    hsize1 htypeVal1 hlastBit1 hblockSize1 hwindow1 hpayload1 hoff2
    hsize2 htypeVal2 hlastBit2 hblockSize2 hwindow2 hpayload2
  -- Step 2: Unfold decompressFrame and thread through
  unfold Zip.Native.decompressFrame
  simp only [bind, Except.bind, pure, Except.pure, hparse]
  -- Step 3: Dictionary check — header.dictionaryId = none, so if-let doesn't match
  simp only [hnodict]
  -- Step 4: Block decompression succeeds
  unfold Zip.Native.decompressBlocks
  rw [hblocks]
  -- Step 5: Checksum is false, content size is none — both guards are trivial
  simp only [hnocksum, hnosize, Bool.false_eq_true, ↓reduceIte]
  exact ⟨_, _, rfl⟩

/-- When a frame contains two consecutive RLE blocks (first non-last, second last),
    with no dictionary, no content checksum, and no declared content size,
    `decompressFrame` succeeds. Composes `parseFrameHeader` success with
    `decompressBlocksWF_succeeds_two_rle_blocks` and threads through the
    frame-level dictionary/checksum/size guards. -/
theorem decompressFrame_succeeds_two_rle_blocks (data : ByteArray) (pos : Nat)
    (header : Zip.Native.ZstdFrameHeader) (afterHeader : Nat)
    (hparse : Zip.Native.parseFrameHeader data pos = .ok (header, afterHeader))
    (hnodict : header.dictionaryId = none)
    (hnocksum : header.contentChecksum = false)
    (hnosize : header.contentSize = none)
    -- Block 1 byte-level conditions (non-last RLE at afterHeader)
    (hsize1 : data.size ≥ afterHeader + 3)
    (htypeVal1 : ((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
        ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 1)
    (hlastBit1 : (data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
        ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) &&& 1 = 0)
    (hblockSize1 : ((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
        ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow1 : ¬ (header.windowSize > 0 &&
        ((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
          ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > header.windowSize))
    (hpayload1 : data.size ≥ afterHeader + 4)
    -- Block 2 position and byte-level conditions (last RLE)
    {off2 : Nat}
    (hoff2 : off2 = afterHeader + 4)
    (hsize2 : data.size ≥ off2 + 3)
    (htypeVal2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 1)
    (hlastBit2 : (data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) &&& 1 = 1)
    (hblockSize2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow2 : ¬ (header.windowSize > 0 &&
        ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
          ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > header.windowSize))
    (hpayload2 : data.size ≥ off2 + 4) :
    ∃ content pos',
      Zip.Native.decompressFrame data pos = .ok (content, pos') := by
  -- Step 1: Get block-level success from byte-level conditions
  obtain ⟨result, blockPos, hblocks⟩ := decompressBlocksWF_succeeds_two_rle_blocks
    data afterHeader off2 header.windowSize ByteArray.empty none {} #[1, 4, 8]
    hsize1 htypeVal1 hlastBit1 hblockSize1 hwindow1 hpayload1 hoff2
    hsize2 htypeVal2 hlastBit2 hblockSize2 hwindow2 hpayload2
  -- Step 2: Unfold decompressFrame and thread through
  unfold Zip.Native.decompressFrame
  simp only [bind, Except.bind, pure, Except.pure, hparse]
  -- Step 3: Dictionary check — header.dictionaryId = none, so if-let doesn't match
  simp only [hnodict]
  -- Step 4: Block decompression succeeds
  unfold Zip.Native.decompressBlocks
  rw [hblocks]
  -- Step 5: Checksum is false, content size is none — both guards are trivial
  simp only [hnocksum, hnosize, Bool.false_eq_true, ↓reduceIte]
  exact ⟨_, _, rfl⟩

/-- When `decompressBlocksWF` encounters a non-last raw block followed by a last
    RLE block, the output is `output ++ block1 ++ block2` at the position after
    the RLE byte. Composes `decompressBlocksWF_raw_step` and
    `decompressBlocksWF_single_rle`. -/
theorem decompressBlocksWF_raw_then_rle (data : ByteArray) (off : Nat)
    (windowSize : UInt64) (output : ByteArray)
    (prevHuff : Option Zip.Native.ZstdHuffmanTable)
    (prevFse : Zip.Native.PrevFseTables) (history : Array Nat)
    -- Block 1 (non-last raw)
    (hdr1 : Zip.Native.ZstdBlockHeader) (afterHdr1 : Nat)
    (block1 : ByteArray) (afterBlock1 : Nat)
    -- Block 2 (last RLE)
    (hdr2 : Zip.Native.ZstdBlockHeader) (afterHdr2 : Nat)
    (block2 : ByteArray) (afterByte2 : Nat)
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
    (htype2 : hdr2.blockType = .rle)
    (hrle2 : Zip.Native.decompressRLEBlock data afterHdr2 hdr2.blockSize
               = .ok (block2, afterByte2))
    (hlast2 : hdr2.lastBlock = true) :
    Zip.Native.decompressBlocksWF data off windowSize output prevHuff prevFse history
      = .ok (output ++ block1 ++ block2, afterByte2) := by
  rw [decompressBlocksWF_raw_step data off windowSize output prevHuff prevFse history
    hdr1 afterHdr1 block1 afterBlock1 hoff1 hparse1 hbs1 hws1 htype1 hraw1 hnotlast1 hadv1]
  rw [decompressBlocksWF_single_rle data afterBlock1 windowSize (output ++ block1) prevHuff
    prevFse history hdr2 afterHdr2 block2 afterByte2 hoff2 hparse2 hbs2 hws2 htype2 hrle2
    hlast2]

/-- When `decompressBlocksWF` encounters a non-last RLE block followed by a last
    raw block, the output is `output ++ block1 ++ block2` at the position after
    the second block. Composes `decompressBlocksWF_rle_step` and
    `decompressBlocksWF_single_raw`. -/
theorem decompressBlocksWF_rle_then_raw (data : ByteArray) (off : Nat)
    (windowSize : UInt64) (output : ByteArray)
    (prevHuff : Option Zip.Native.ZstdHuffmanTable)
    (prevFse : Zip.Native.PrevFseTables) (history : Array Nat)
    -- Block 1 (non-last RLE)
    (hdr1 : Zip.Native.ZstdBlockHeader) (afterHdr1 : Nat)
    (block1 : ByteArray) (afterByte1 : Nat)
    -- Block 2 (last raw)
    (hdr2 : Zip.Native.ZstdBlockHeader) (afterHdr2 : Nat)
    (block2 : ByteArray) (afterBlock2 : Nat)
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
    (htype2 : hdr2.blockType = .raw)
    (hraw2 : Zip.Native.decompressRawBlock data afterHdr2 hdr2.blockSize
               = .ok (block2, afterBlock2))
    (hlast2 : hdr2.lastBlock = true) :
    Zip.Native.decompressBlocksWF data off windowSize output prevHuff prevFse history
      = .ok (output ++ block1 ++ block2, afterBlock2) := by
  rw [decompressBlocksWF_rle_step data off windowSize output prevHuff prevFse history
    hdr1 afterHdr1 block1 afterByte1 hoff1 hparse1 hbs1 hws1 htype1 hrle1 hnotlast1 hadv1]
  rw [decompressBlocksWF_single_raw data afterByte1 windowSize (output ++ block1) prevHuff
    prevFse history hdr2 afterHdr2 block2 afterBlock2 hoff2 hparse2 hbs2 hws2 htype2 hraw2
    hlast2]

/-! ## decompressBlocksWF two-block composed completeness (heterogeneous raw/RLE) -/

/-- When a non-last raw block at `off` is followed by a last RLE block at `off2`,
    `decompressBlocksWF` succeeds. Composes `decompressBlocksWF_raw_step` with
    `decompressBlocksWF_succeeds_single_rle` using only byte-level preconditions. -/
theorem decompressBlocksWF_succeeds_raw_then_rle (data : ByteArray)
    (off off2 : Nat) (windowSize : UInt64) (output : ByteArray)
    (prevHuff : Option Zip.Native.ZstdHuffmanTable)
    (prevFse : Zip.Native.PrevFseTables) (history : Array Nat)
    -- Block 1 (non-last raw) byte-level conditions at off
    (hsize1 : data.size ≥ off + 3)
    (htypeVal1 : ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
        ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 0)
    (hlastBit1 : (data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
        ||| (data[off + 2]!.toUInt32 <<< 16)) &&& 1 = 0)
    (hblockSize1 : ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
        ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow1 : ¬ (windowSize > 0 &&
        ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
          ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > windowSize))
    (hpayload1 : data.size ≥ off + 3 +
        (((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
          ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    -- off2 = position after block 1's raw payload
    (hoff2 : off2 = off + 3 + (((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
          ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    -- Block 2 (last RLE) byte-level conditions at off2
    (hsize2 : data.size ≥ off2 + 3)
    (htypeVal2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 1)
    (hlastBit2 : (data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) &&& 1 = 1)
    (hblockSize2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow2 : ¬ (windowSize > 0 &&
        ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
          ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > windowSize))
    (hpayload2 : data.size ≥ off2 + 4) :
    ∃ result pos',
      Zip.Native.decompressBlocksWF data off windowSize output prevHuff prevFse history
        = .ok (result, pos') := by
  -- Block 1: parseBlockHeader succeeds (typeVal=0 ≠ 3)
  have htypeNe3 : ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
      ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 ≠ 3 := by
    rw [htypeVal1]; decide
  obtain ⟨hdr1, afterHdr1, hparse1⟩ := parseBlockHeader_succeeds data off hsize1 htypeNe3
  have htype1 := (parseBlockHeader_blockType_eq data off hdr1 afterHdr1 hparse1).1 htypeVal1
  have hbs_eq1 := parseBlockHeader_blockSize_eq data off hdr1 afterHdr1 hparse1
  have hpos_eq1 := parseBlockHeader_pos_eq data off hdr1 afterHdr1 hparse1
  have hnotlast1 : hdr1.lastBlock = false := by
    rw [parseBlockHeader_lastBlock_eq data off hdr1 afterHdr1 hparse1, hlastBit1]; decide
  have hbs1 : ¬ hdr1.blockSize > 131072 := by rw [hbs_eq1]; exact Nat.not_lt.mpr hblockSize1
  have hws1 : ¬ (windowSize > 0 && hdr1.blockSize.toUInt64 > windowSize) := by
    rw [hbs_eq1]; exact hwindow1
  -- Block 1: decompressRawBlock succeeds
  have hpayload1' : data.size ≥ afterHdr1 + hdr1.blockSize.toNat := by
    rw [hpos_eq1, hbs_eq1]; omega
  obtain ⟨block1, afterBlock1, hraw1⟩ := decompressRawBlock_succeeds data afterHdr1
    hdr1.blockSize hpayload1'
  have hoff1 : ¬ data.size ≤ off := by omega
  have hRawPos := decompressRawBlock_pos_eq data afterHdr1 hdr1.blockSize block1
    afterBlock1 hraw1
  have hadv1 : ¬ afterBlock1 ≤ off := by rw [hRawPos, hpos_eq1]; omega
  -- afterBlock1 = off2, substitute
  have : off2 = afterBlock1 := by rw [hoff2, hRawPos, hpos_eq1, hbs_eq1]
  subst this
  -- Step through block 1, then apply succeeds_single_rle for block 2
  rw [decompressBlocksWF_raw_step data off windowSize output prevHuff prevFse history
    hdr1 afterHdr1 block1 off2 hoff1 hparse1 hbs1 hws1 htype1 hraw1 hnotlast1 hadv1]
  exact decompressBlocksWF_succeeds_single_rle data off2 windowSize (output ++ block1)
    prevHuff prevFse history hsize2 htypeVal2 hlastBit2 hblockSize2 hwindow2 hpayload2

/-- When a non-last RLE block at `off` is followed by a last raw block at `off2`,
    `decompressBlocksWF` succeeds. Composes `decompressBlocksWF_rle_step` with
    `decompressBlocksWF_succeeds_single_raw` using only byte-level preconditions. -/
theorem decompressBlocksWF_succeeds_rle_then_raw (data : ByteArray)
    (off off2 : Nat) (windowSize : UInt64) (output : ByteArray)
    (prevHuff : Option Zip.Native.ZstdHuffmanTable)
    (prevFse : Zip.Native.PrevFseTables) (history : Array Nat)
    -- Block 1 (non-last RLE) byte-level conditions at off
    (hsize1 : data.size ≥ off + 3)
    (htypeVal1 : ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
        ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 1)
    (hlastBit1 : (data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
        ||| (data[off + 2]!.toUInt32 <<< 16)) &&& 1 = 0)
    (hblockSize1 : ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
        ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow1 : ¬ (windowSize > 0 &&
        ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
          ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > windowSize))
    (hpayload1 : data.size ≥ off + 4)
    -- off2 = position after block 1's RLE byte
    (hoff2 : off2 = off + 4)
    -- Block 2 (last raw) byte-level conditions at off2
    (hsize2 : data.size ≥ off2 + 3)
    (htypeVal2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 0)
    (hlastBit2 : (data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) &&& 1 = 1)
    (hblockSize2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow2 : ¬ (windowSize > 0 &&
        ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
          ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > windowSize))
    (hpayload2 : data.size ≥ off2 + 3 +
        (((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
          ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toNat)) :
    ∃ result pos',
      Zip.Native.decompressBlocksWF data off windowSize output prevHuff prevFse history
        = .ok (result, pos') := by
  -- Block 1: parseBlockHeader succeeds (typeVal=1 ≠ 3)
  have htypeNe3 : ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
      ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 ≠ 3 := by
    rw [htypeVal1]; decide
  obtain ⟨hdr1, afterHdr1, hparse1⟩ := parseBlockHeader_succeeds data off hsize1 htypeNe3
  have htype1 := (parseBlockHeader_blockType_eq data off hdr1 afterHdr1 hparse1).2.1 htypeVal1
  have hbs_eq1 := parseBlockHeader_blockSize_eq data off hdr1 afterHdr1 hparse1
  have hpos_eq1 := parseBlockHeader_pos_eq data off hdr1 afterHdr1 hparse1
  have hnotlast1 : hdr1.lastBlock = false := by
    rw [parseBlockHeader_lastBlock_eq data off hdr1 afterHdr1 hparse1, hlastBit1]; decide
  have hbs1 : ¬ hdr1.blockSize > 131072 := by rw [hbs_eq1]; exact Nat.not_lt.mpr hblockSize1
  have hws1 : ¬ (windowSize > 0 && hdr1.blockSize.toUInt64 > windowSize) := by
    rw [hbs_eq1]; exact hwindow1
  -- Block 1: decompressRLEBlock succeeds
  have hpayload1' : data.size ≥ afterHdr1 + 1 := by rw [hpos_eq1]; omega
  obtain ⟨block1, afterByte1, hrle1⟩ := decompressRLEBlock_succeeds data afterHdr1
    hdr1.blockSize hpayload1'
  have hoff1 : ¬ data.size ≤ off := by omega
  have hRlePos := decompressRLEBlock_pos_eq data afterHdr1 hdr1.blockSize block1
    afterByte1 hrle1
  have hadv1 : ¬ afterByte1 ≤ off := by rw [hRlePos, hpos_eq1]; omega
  -- afterByte1 = off2, substitute
  have : off2 = afterByte1 := by rw [hoff2, hRlePos, hpos_eq1]
  subst this
  -- Step through block 1, then apply succeeds_single_raw for block 2
  rw [decompressBlocksWF_rle_step data off windowSize output prevHuff prevFse history
    hdr1 afterHdr1 block1 off2 hoff1 hparse1 hbs1 hws1 htype1 hrle1 hnotlast1 hadv1]
  exact decompressBlocksWF_succeeds_single_raw data off2 windowSize (output ++ block1)
    prevHuff prevFse history hsize2 htypeVal2 hlastBit2 hblockSize2 hwindow2 hpayload2

/-! ## decompressFrame two-block composed completeness (heterogeneous) -/

/-- When a frame contains a non-last raw block followed by a last RLE block,
    with no dictionary, no content checksum, and no declared content size,
    `decompressFrame` succeeds. This composes `parseFrameHeader` success with
    `decompressBlocksWF_succeeds_raw_then_rle` and threads through the
    frame-level dictionary/checksum/size guards. -/
theorem decompressFrame_succeeds_raw_then_rle (data : ByteArray) (pos : Nat)
    (header : Zip.Native.ZstdFrameHeader) (afterHeader : Nat)
    (hparse : Zip.Native.parseFrameHeader data pos = .ok (header, afterHeader))
    (hnodict : header.dictionaryId = none)
    (hnocksum : header.contentChecksum = false)
    (hnosize : header.contentSize = none)
    -- Block 1 (non-last raw) at afterHeader
    (hsize1 : data.size ≥ afterHeader + 3)
    (htypeVal1 : ((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
        ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 0)
    (hlastBit1 : (data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
        ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) &&& 1 = 0)
    (hblockSize1 : ((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
        ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow1 : ¬ (header.windowSize > 0 &&
        ((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
          ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > header.windowSize))
    (hpayload1 : data.size ≥ afterHeader + 3 +
        (((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
          ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    -- Block 2 (last RLE) at off2
    (off2 : Nat)
    (hoff2 : off2 = afterHeader + 3 + (((data[afterHeader]!.toUInt32
          ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
          ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    (hsize2 : data.size ≥ off2 + 3)
    (htypeVal2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 1)
    (hlastBit2 : (data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) &&& 1 = 1)
    (hblockSize2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow2 : ¬ (header.windowSize > 0 &&
        ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
          ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > header.windowSize))
    (hpayload2 : data.size ≥ off2 + 4) :
    ∃ content pos',
      Zip.Native.decompressFrame data pos = .ok (content, pos') := by
  -- Step 1: Get block-level success from byte-level conditions
  obtain ⟨result, blockPos, hblocks⟩ := decompressBlocksWF_succeeds_raw_then_rle
    data afterHeader off2 header.windowSize ByteArray.empty none {} #[1, 4, 8]
    hsize1 htypeVal1 hlastBit1 hblockSize1 hwindow1 hpayload1 hoff2
    hsize2 htypeVal2 hlastBit2 hblockSize2 hwindow2 hpayload2
  -- Step 2: Unfold decompressFrame and thread through
  unfold Zip.Native.decompressFrame
  simp only [bind, Except.bind, pure, Except.pure, hparse]
  -- Step 3: Dictionary check — header.dictionaryId = none, so if-let doesn't match
  simp only [hnodict]
  -- Step 4: Block decompression succeeds
  unfold Zip.Native.decompressBlocks
  rw [hblocks]
  -- Step 5: Checksum is false, content size is none — both guards are trivial
  simp only [hnocksum, hnosize, Bool.false_eq_true, ↓reduceIte]
  exact ⟨_, _, rfl⟩

/-- When a frame contains a non-last RLE block followed by a last raw block,
    with no dictionary, no content checksum, and no declared content size,
    `decompressFrame` succeeds. This composes `parseFrameHeader` success with
    `decompressBlocksWF_succeeds_rle_then_raw` and threads through the
    frame-level dictionary/checksum/size guards. -/
theorem decompressFrame_succeeds_rle_then_raw (data : ByteArray) (pos : Nat)
    (header : Zip.Native.ZstdFrameHeader) (afterHeader : Nat)
    (hparse : Zip.Native.parseFrameHeader data pos = .ok (header, afterHeader))
    (hnodict : header.dictionaryId = none)
    (hnocksum : header.contentChecksum = false)
    (hnosize : header.contentSize = none)
    -- Block 1 (non-last RLE) at afterHeader
    (hsize1 : data.size ≥ afterHeader + 3)
    (htypeVal1 : ((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
        ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 1)
    (hlastBit1 : (data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
        ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) &&& 1 = 0)
    (hblockSize1 : ((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
        ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow1 : ¬ (header.windowSize > 0 &&
        ((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
          ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > header.windowSize))
    (hpayload1 : data.size ≥ afterHeader + 4)
    -- Block 2 (last raw) at off2
    (off2 : Nat)
    (hoff2 : off2 = afterHeader + 4)
    (hsize2 : data.size ≥ off2 + 3)
    (htypeVal2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 0)
    (hlastBit2 : (data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) &&& 1 = 1)
    (hblockSize2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow2 : ¬ (header.windowSize > 0 &&
        ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
          ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > header.windowSize))
    (hpayload2 : data.size ≥ off2 + 3 +
        (((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
          ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toNat)) :
    ∃ content pos',
      Zip.Native.decompressFrame data pos = .ok (content, pos') := by
  -- Step 1: Get block-level success from byte-level conditions
  obtain ⟨result, blockPos, hblocks⟩ := decompressBlocksWF_succeeds_rle_then_raw
    data afterHeader off2 header.windowSize ByteArray.empty none {} #[1, 4, 8]
    hsize1 htypeVal1 hlastBit1 hblockSize1 hwindow1 hpayload1 hoff2
    hsize2 htypeVal2 hlastBit2 hblockSize2 hwindow2 hpayload2
  -- Step 2: Unfold decompressFrame and thread through
  unfold Zip.Native.decompressFrame
  simp only [bind, Except.bind, pure, Except.pure, hparse]
  -- Step 3: Dictionary check — header.dictionaryId = none, so if-let doesn't match
  simp only [hnodict]
  -- Step 4: Block decompression succeeds
  unfold Zip.Native.decompressBlocks
  rw [hblocks]
  -- Step 5: Checksum is false, content size is none — both guards are trivial
  simp only [hnocksum, hnosize, Bool.false_eq_true, ↓reduceIte]
  exact ⟨_, _, rfl⟩

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

/-- When `decompressBlocksWF` encounters two consecutive compressed blocks with
    numSeq == 0 (literals only, no sequence commands), where the first is non-last
    and the second is last, the output is `output ++ literals1 ++ literals2` at
    the position after the second block. Block 2's literal parsing uses the
    updated Huffman tree from block 1.

    Composes `decompressBlocksWF_compressed_literals_only_step` and
    `decompressBlocksWF_single_compressed_literals_only`. The two-block output
    is the concatenation of both blocks' literal sections — combined with
    `decompressRawBlock_content` and `decompressRLEBlock_content`, this gives
    a complete characterization for two-block frames across all block types
    (when numSeq=0 for compressed blocks). -/
theorem decompressBlocksWF_two_compressed_literals_blocks (data : ByteArray)
    (off : Nat) (windowSize : UInt64) (output : ByteArray)
    (prevHuff : Option Zip.Native.ZstdHuffmanTable)
    (prevFse : Zip.Native.PrevFseTables) (history : Array Nat)
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
    -- Block 1 hypotheses
    (hoff1 : ¬ data.size ≤ off)
    (hparse1 : Zip.Native.parseBlockHeader data off = .ok (hdr1, afterHdr1))
    (hbs1 : ¬ hdr1.blockSize > 131072)
    (hws1 : ¬ (windowSize > 0 && hdr1.blockSize.toUInt64 > windowSize))
    (htype1 : hdr1.blockType = .compressed)
    (hblockEnd1 : ¬ data.size < afterHdr1 + hdr1.blockSize.toNat)
    (hlit1 : Zip.Native.parseLiteralsSection data afterHdr1 prevHuff
               = .ok (literals1, afterLiterals1, huffTree1))
    (hseq1 : Zip.Native.parseSequencesHeader data afterLiterals1
               = .ok (0, modes1, afterSeqHeader1))
    (hnotlast1 : hdr1.lastBlock = false)
    (hadv1 : ¬ afterHdr1 + hdr1.blockSize.toNat ≤ off)
    -- Block 2 hypotheses
    (hoff2 : ¬ data.size ≤ afterHdr1 + hdr1.blockSize.toNat)
    (hparse2 : Zip.Native.parseBlockHeader data (afterHdr1 + hdr1.blockSize.toNat)
                 = .ok (hdr2, afterHdr2))
    (hbs2 : ¬ hdr2.blockSize > 131072)
    (hws2 : ¬ (windowSize > 0 && hdr2.blockSize.toUInt64 > windowSize))
    (htype2 : hdr2.blockType = .compressed)
    (hblockEnd2 : ¬ data.size < afterHdr2 + hdr2.blockSize.toNat)
    (hlit2 : Zip.Native.parseLiteralsSection data afterHdr2
               (if let some ht := huffTree1 then some ht else prevHuff)
               = .ok (literals2, afterLiterals2, huffTree2))
    (hseq2 : Zip.Native.parseSequencesHeader data afterLiterals2
               = .ok (0, modes2, afterSeqHeader2))
    (hlast2 : hdr2.lastBlock = true) :
    Zip.Native.decompressBlocksWF data off windowSize output prevHuff prevFse history
      = .ok (output ++ literals1 ++ literals2,
             afterHdr2 + hdr2.blockSize.toNat) := by
  rw [decompressBlocksWF_compressed_literals_only_step data off windowSize output prevHuff
    prevFse history hdr1 afterHdr1 literals1 afterLiterals1 huffTree1 modes1 afterSeqHeader1
    hoff1 hparse1 hbs1 hws1 htype1 hblockEnd1 hlit1 hseq1 hnotlast1 hadv1]
  exact decompressBlocksWF_single_compressed_literals_only data
    (afterHdr1 + hdr1.blockSize.toNat) windowSize (output ++ literals1)
    _ prevFse history
    hdr2 afterHdr2 literals2 afterLiterals2 huffTree2 modes2 afterSeqHeader2
    hoff2 hparse2 hbs2 hws2 htype2 hblockEnd2 hlit2 hseq2 hlast2

/-- When `decompressBlocksWF` encounters a non-last compressed block with
    numSeq == 0 (literals only) followed by a last raw block, the output is
    `output ++ literals1 ++ block2` at the position after the raw data.
    Composes `decompressBlocksWF_compressed_literals_only_step` and
    `decompressBlocksWF_single_raw`. Raw blocks don't use Huffman/FSE state,
    so the state threading from block 1 is irrelevant for block 2. -/
theorem decompressBlocksWF_compressed_literals_then_raw (data : ByteArray)
    (off : Nat) (windowSize : UInt64) (output : ByteArray)
    (prevHuff : Option Zip.Native.ZstdHuffmanTable)
    (prevFse : Zip.Native.PrevFseTables) (history : Array Nat)
    -- Block 1 (non-last compressed, numSeq=0)
    (hdr1 : Zip.Native.ZstdBlockHeader) (afterHdr1 : Nat)
    (literals1 : ByteArray) (afterLiterals1 : Nat)
    (huffTree1 : Option Zip.Native.ZstdHuffmanTable)
    (modes1 : Zip.Native.SequenceCompressionModes) (afterSeqHeader1 : Nat)
    -- Block 2 (last raw)
    (hdr2 : Zip.Native.ZstdBlockHeader) (afterHdr2 : Nat)
    (block2 : ByteArray) (afterBlock2 : Nat)
    -- Block 1 hypotheses
    (hoff1 : ¬ data.size ≤ off)
    (hparse1 : Zip.Native.parseBlockHeader data off = .ok (hdr1, afterHdr1))
    (hbs1 : ¬ hdr1.blockSize > 131072)
    (hws1 : ¬ (windowSize > 0 && hdr1.blockSize.toUInt64 > windowSize))
    (htype1 : hdr1.blockType = .compressed)
    (hblockEnd1 : ¬ data.size < afterHdr1 + hdr1.blockSize.toNat)
    (hlit1 : Zip.Native.parseLiteralsSection data afterHdr1 prevHuff
               = .ok (literals1, afterLiterals1, huffTree1))
    (hseq1 : Zip.Native.parseSequencesHeader data afterLiterals1
               = .ok (0, modes1, afterSeqHeader1))
    (hnotlast1 : hdr1.lastBlock = false)
    (hadv1 : ¬ afterHdr1 + hdr1.blockSize.toNat ≤ off)
    -- Block 2 hypotheses
    (hoff2 : ¬ data.size ≤ afterHdr1 + hdr1.blockSize.toNat)
    (hparse2 : Zip.Native.parseBlockHeader data (afterHdr1 + hdr1.blockSize.toNat)
                 = .ok (hdr2, afterHdr2))
    (hbs2 : ¬ hdr2.blockSize > 131072)
    (hws2 : ¬ (windowSize > 0 && hdr2.blockSize.toUInt64 > windowSize))
    (htype2 : hdr2.blockType = .raw)
    (hraw2 : Zip.Native.decompressRawBlock data afterHdr2 hdr2.blockSize
               = .ok (block2, afterBlock2))
    (hlast2 : hdr2.lastBlock = true) :
    Zip.Native.decompressBlocksWF data off windowSize output prevHuff prevFse history
      = .ok (output ++ literals1 ++ block2, afterBlock2) := by
  rw [decompressBlocksWF_compressed_literals_only_step data off windowSize output prevHuff
    prevFse history hdr1 afterHdr1 literals1 afterLiterals1 huffTree1 modes1 afterSeqHeader1
    hoff1 hparse1 hbs1 hws1 htype1 hblockEnd1 hlit1 hseq1 hnotlast1 hadv1]
  exact decompressBlocksWF_single_raw data (afterHdr1 + hdr1.blockSize.toNat) windowSize
    (output ++ literals1) _ prevFse history hdr2 afterHdr2 block2 afterBlock2
    hoff2 hparse2 hbs2 hws2 htype2 hraw2 hlast2

/-- When `decompressBlocksWF` encounters a non-last compressed block with
    numSeq == 0 (literals only) followed by a last RLE block, the output is
    `output ++ literals1 ++ block2` at the position after the RLE byte.
    Composes `decompressBlocksWF_compressed_literals_only_step` and
    `decompressBlocksWF_single_rle`. RLE blocks don't use Huffman/FSE state,
    so the state threading from block 1 is irrelevant for block 2. -/
theorem decompressBlocksWF_compressed_literals_then_rle (data : ByteArray)
    (off : Nat) (windowSize : UInt64) (output : ByteArray)
    (prevHuff : Option Zip.Native.ZstdHuffmanTable)
    (prevFse : Zip.Native.PrevFseTables) (history : Array Nat)
    -- Block 1 (non-last compressed, numSeq=0)
    (hdr1 : Zip.Native.ZstdBlockHeader) (afterHdr1 : Nat)
    (literals1 : ByteArray) (afterLiterals1 : Nat)
    (huffTree1 : Option Zip.Native.ZstdHuffmanTable)
    (modes1 : Zip.Native.SequenceCompressionModes) (afterSeqHeader1 : Nat)
    -- Block 2 (last RLE)
    (hdr2 : Zip.Native.ZstdBlockHeader) (afterHdr2 : Nat)
    (block2 : ByteArray) (afterByte2 : Nat)
    -- Block 1 hypotheses
    (hoff1 : ¬ data.size ≤ off)
    (hparse1 : Zip.Native.parseBlockHeader data off = .ok (hdr1, afterHdr1))
    (hbs1 : ¬ hdr1.blockSize > 131072)
    (hws1 : ¬ (windowSize > 0 && hdr1.blockSize.toUInt64 > windowSize))
    (htype1 : hdr1.blockType = .compressed)
    (hblockEnd1 : ¬ data.size < afterHdr1 + hdr1.blockSize.toNat)
    (hlit1 : Zip.Native.parseLiteralsSection data afterHdr1 prevHuff
               = .ok (literals1, afterLiterals1, huffTree1))
    (hseq1 : Zip.Native.parseSequencesHeader data afterLiterals1
               = .ok (0, modes1, afterSeqHeader1))
    (hnotlast1 : hdr1.lastBlock = false)
    (hadv1 : ¬ afterHdr1 + hdr1.blockSize.toNat ≤ off)
    -- Block 2 hypotheses
    (hoff2 : ¬ data.size ≤ afterHdr1 + hdr1.blockSize.toNat)
    (hparse2 : Zip.Native.parseBlockHeader data (afterHdr1 + hdr1.blockSize.toNat)
                 = .ok (hdr2, afterHdr2))
    (hbs2 : ¬ hdr2.blockSize > 131072)
    (hws2 : ¬ (windowSize > 0 && hdr2.blockSize.toUInt64 > windowSize))
    (htype2 : hdr2.blockType = .rle)
    (hrle2 : Zip.Native.decompressRLEBlock data afterHdr2 hdr2.blockSize
               = .ok (block2, afterByte2))
    (hlast2 : hdr2.lastBlock = true) :
    Zip.Native.decompressBlocksWF data off windowSize output prevHuff prevFse history
      = .ok (output ++ literals1 ++ block2, afterByte2) := by
  rw [decompressBlocksWF_compressed_literals_only_step data off windowSize output prevHuff
    prevFse history hdr1 afterHdr1 literals1 afterLiterals1 huffTree1 modes1 afterSeqHeader1
    hoff1 hparse1 hbs1 hws1 htype1 hblockEnd1 hlit1 hseq1 hnotlast1 hadv1]
  exact decompressBlocksWF_single_rle data (afterHdr1 + hdr1.blockSize.toNat) windowSize
    (output ++ literals1) _ prevFse history hdr2 afterHdr2 block2 afterByte2
    hoff2 hparse2 hbs2 hws2 htype2 hrle2 hlast2

/-- When `decompressBlocksWF` encounters a non-last raw block followed by a last
    compressed block with numSeq == 0 (literals only), the output is
    `output ++ block1 ++ literals2` at the position `afterHdr2 + hdr2.blockSize`.
    Composes `decompressBlocksWF_raw_step` and
    `decompressBlocksWF_single_compressed_literals_only`. Since raw blocks don't
    modify Huffman/FSE state, block 2's `parseLiteralsSection` receives the
    original `prevHuff`. -/
theorem decompressBlocksWF_raw_then_compressed_literals (data : ByteArray)
    (off : Nat) (windowSize : UInt64) (output : ByteArray)
    (prevHuff : Option Zip.Native.ZstdHuffmanTable)
    (prevFse : Zip.Native.PrevFseTables) (history : Array Nat)
    -- Block 1 (non-last raw)
    (hdr1 : Zip.Native.ZstdBlockHeader) (afterHdr1 : Nat)
    (block1 : ByteArray) (afterBlock1 : Nat)
    -- Block 2 (last compressed, numSeq=0)
    (hdr2 : Zip.Native.ZstdBlockHeader) (afterHdr2 : Nat)
    (literals2 : ByteArray) (afterLiterals2 : Nat)
    (huffTree2 : Option Zip.Native.ZstdHuffmanTable)
    (modes2 : Zip.Native.SequenceCompressionModes) (afterSeqHeader2 : Nat)
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
    (htype2 : hdr2.blockType = .compressed)
    (hblockEnd2 : ¬ data.size < afterHdr2 + hdr2.blockSize.toNat)
    (hlit2 : Zip.Native.parseLiteralsSection data afterHdr2 prevHuff
               = .ok (literals2, afterLiterals2, huffTree2))
    (hseq2 : Zip.Native.parseSequencesHeader data afterLiterals2
               = .ok (0, modes2, afterSeqHeader2))
    (hlast2 : hdr2.lastBlock = true) :
    Zip.Native.decompressBlocksWF data off windowSize output prevHuff prevFse history
      = .ok (output ++ block1 ++ literals2, afterHdr2 + hdr2.blockSize.toNat) := by
  rw [decompressBlocksWF_raw_step data off windowSize output prevHuff prevFse history
    hdr1 afterHdr1 block1 afterBlock1 hoff1 hparse1 hbs1 hws1 htype1 hraw1 hnotlast1 hadv1]
  exact decompressBlocksWF_single_compressed_literals_only data afterBlock1 windowSize
    (output ++ block1) prevHuff prevFse history hdr2 afterHdr2 literals2 afterLiterals2
    huffTree2 modes2 afterSeqHeader2 hoff2 hparse2 hbs2 hws2 htype2 hblockEnd2 hlit2 hseq2
    hlast2

/-- When `decompressBlocksWF` encounters a non-last RLE block followed by a last
    compressed block with numSeq == 0 (literals only), the output is
    `output ++ block1 ++ literals2` at the position `afterHdr2 + hdr2.blockSize`.
    Composes `decompressBlocksWF_rle_step` and
    `decompressBlocksWF_single_compressed_literals_only`. Since RLE blocks don't
    modify Huffman/FSE state, block 2's `parseLiteralsSection` receives the
    original `prevHuff`. -/
theorem decompressBlocksWF_rle_then_compressed_literals (data : ByteArray)
    (off : Nat) (windowSize : UInt64) (output : ByteArray)
    (prevHuff : Option Zip.Native.ZstdHuffmanTable)
    (prevFse : Zip.Native.PrevFseTables) (history : Array Nat)
    -- Block 1 (non-last RLE)
    (hdr1 : Zip.Native.ZstdBlockHeader) (afterHdr1 : Nat)
    (block1 : ByteArray) (afterByte1 : Nat)
    -- Block 2 (last compressed, numSeq=0)
    (hdr2 : Zip.Native.ZstdBlockHeader) (afterHdr2 : Nat)
    (literals2 : ByteArray) (afterLiterals2 : Nat)
    (huffTree2 : Option Zip.Native.ZstdHuffmanTable)
    (modes2 : Zip.Native.SequenceCompressionModes) (afterSeqHeader2 : Nat)
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
    (htype2 : hdr2.blockType = .compressed)
    (hblockEnd2 : ¬ data.size < afterHdr2 + hdr2.blockSize.toNat)
    (hlit2 : Zip.Native.parseLiteralsSection data afterHdr2 prevHuff
               = .ok (literals2, afterLiterals2, huffTree2))
    (hseq2 : Zip.Native.parseSequencesHeader data afterLiterals2
               = .ok (0, modes2, afterSeqHeader2))
    (hlast2 : hdr2.lastBlock = true) :
    Zip.Native.decompressBlocksWF data off windowSize output prevHuff prevFse history
      = .ok (output ++ block1 ++ literals2, afterHdr2 + hdr2.blockSize.toNat) := by
  rw [decompressBlocksWF_rle_step data off windowSize output prevHuff prevFse history
    hdr1 afterHdr1 block1 afterByte1 hoff1 hparse1 hbs1 hws1 htype1 hrle1 hnotlast1 hadv1]
  exact decompressBlocksWF_single_compressed_literals_only data afterByte1 windowSize
    (output ++ block1) prevHuff prevFse history hdr2 afterHdr2 literals2 afterLiterals2
    huffTree2 modes2 afterSeqHeader2 hoff2 hparse2 hbs2 hws2 htype2 hblockEnd2 hlit2 hseq2
    hlast2

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

/-! ## Parsing completeness -/

/-- Minimum data size required for `parseFrameHeader` to succeed, given
    the frame header descriptor byte. The descriptor byte (at `pos + 4`)
    determines the sizes of optional header fields:
    - Window descriptor: 0 or 1 byte (absent if `singleSegment` flag set)
    - Dictionary ID: 0, 1, 2, or 4 bytes (from `didFlag` bits 1-0)
    - Frame content size: 0, 1, 2, 4, or 8 bytes (from `fcsFlag` bits 7-6) -/
def frameHeaderMinSize (desc : UInt8) : Nat :=
  let fcsFlag := (desc >>> 6).toNat
  let singleSegment := (desc >>> 5) &&& 1 == 1
  let didFlag := (desc &&& 3).toNat
  let windowDescSize := if singleSegment then 0 else 1
  let didSize := match didFlag with | 1 => 1 | 2 => 2 | 3 => 4 | _ => 0
  let fcsSize := match fcsFlag with
    | 0 => if singleSegment then 1 else 0
    | 1 => 2 | 2 => 4 | _ => 8
  4 + 1 + windowDescSize + didSize + fcsSize

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
set_option linter.unusedSimpArgs false in
/-- When the data has the correct Zstd magic number and enough bytes for the
    full header (as determined by the descriptor byte at `pos + 4`),
    `parseFrameHeader` succeeds. -/
theorem parseFrameHeader_succeeds (data : ByteArray) (pos : Nat)
    (hmagic : Binary.readUInt32LE data pos = Zip.Native.zstdMagic)
    (hsize : data.size ≥ pos + frameHeaderMinSize data[pos + 4]!) :
    ∃ hdr afterHdr, Zip.Native.parseFrameHeader data pos = .ok (hdr, afterHdr) := by
  have hmin : frameHeaderMinSize data[pos + 4]! ≥ 6 := by
    have h : ∀ i : Fin 256, frameHeaderMinSize ⟨⟨i⟩⟩ ≥ 6 := by decide
    exact h data[pos + 4]!.toBitVec.toFin
  -- Backward approach: case-split on the result
  cases hres : Zip.Native.parseFrameHeader data pos with
  | ok val => obtain ⟨hdr, pos'⟩ := val; exact ⟨hdr, pos', rfl⟩
  | error e =>
    exfalso
    -- Single-pass simp to reduce all monadic constructs
    simp only [Zip.Native.parseFrameHeader, Bind.bind, Except.bind,
      Pure.pure, Except.pure] at hres
    unfold frameHeaderMinSize at hsize
    dsimp only [] at hsize
    -- Guard 1: magic size
    rw [if_neg (show ¬(data.size < pos + 4) from by omega)] at hres
    -- Guard 2: magic value
    rw [hmagic] at hres
    simp only [Zip.Native.zstdMagic, bne_self_eq_false, Bool.false_eq_true, ite_false] at hres
    -- Guard 3: descriptor size
    rw [if_neg (show ¬(data.size < pos + 4 + 1) from by omega)] at hres
    -- Remaining guards depend on descriptor byte fields. Generalize them
    -- so case analysis gives consistent values in hsize.
    generalize hss : (data[pos + 4]! >>> 5 &&& 1 == 1) = ss at hres hsize
    generalize hdf : (data[pos + 4]! &&& 3).toNat = df at hres hsize
    generalize hff : (data[pos + 4]! >>> 6).toNat = ff at hres hsize
    -- Case-split on singleSegment; simp resolves both hres and hsize
    by_cases hss_val : ss = true
    · -- singleSegment = true: no window descriptor
      simp only [hss_val, Bool.not_true, Bool.false_eq_true, ite_false, ite_true] at hres hsize
      -- Walk through didFlag + fcsSize guards via split.
      -- contradiction closes ok branches (.ok _ = .error _)
      -- omega closes error branches (guard contradicts hsize)
      repeat (first | contradiction | (simp only [Bool.false_eq_true, ite_false, ite_true] at hsize; omega) | (split at hres))
    · -- singleSegment = false: window descriptor present
      have hss_false : ss = false := by cases ss <;> simp_all
      simp only [hss_false, Bool.not_false, ite_true, ite_false,
        Bool.false_eq_true] at hres hsize
      -- Window descriptor guard
      rw [if_neg (show ¬(data.size < pos + 4 + 1 + 1) from by omega)] at hres
      -- Walk through remaining guards
      repeat (first | contradiction | (simp only [Bool.false_eq_true, ite_false, ite_true] at hsize; omega) | (split at hres))

/-! ## parseFrameHeader field characterization -/

/-- When `parseFrameHeader` succeeds, the `contentChecksum` field equals
    bit 2 of the descriptor byte at `pos + 4`. -/
theorem parseFrameHeader_contentChecksum_eq (data : ByteArray) (pos : Nat)
    (hdr : Zip.Native.ZstdFrameHeader) (pos' : Nat)
    (h : Zip.Native.parseFrameHeader data pos = .ok (hdr, pos')) :
    hdr.contentChecksum = ((data[pos + 4]! >>> 2) &&& 1 == 1) := by
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
               obtain ⟨rfl, rfl⟩ := h; rfl)

/-- When `parseFrameHeader` succeeds, the `singleSegment` field equals
    bit 5 of the descriptor byte at `pos + 4`. -/
theorem parseFrameHeader_singleSegment_eq (data : ByteArray) (pos : Nat)
    (hdr : Zip.Native.ZstdFrameHeader) (pos' : Nat)
    (h : Zip.Native.parseFrameHeader data pos = .ok (hdr, pos')) :
    hdr.singleSegment = ((data[pos + 4]! >>> 5) &&& 1 == 1) := by
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
               obtain ⟨rfl, rfl⟩ := h; rfl)

set_option maxHeartbeats 800000 in
/-- When `parseFrameHeader` succeeds, the `dictionaryId` field is determined
    by bits 0-1 of the descriptor byte (DID_Field_Size) and the subsequent
    0/1/2/4 bytes. The DID offset depends on the singleSegment flag:
    `pos + 5` if singleSegment (no window descriptor), `pos + 6` otherwise. -/
theorem parseFrameHeader_dictionaryId_eq (data : ByteArray) (pos : Nat)
    (hdr : Zip.Native.ZstdFrameHeader) (pos' : Nat)
    (h : Zip.Native.parseFrameHeader data pos = .ok (hdr, pos')) :
    let desc := data[pos + 4]!
    let didFlag := (desc &&& 3).toNat
    let didOff := if (desc >>> 5) &&& 1 == 1 then pos + 5 else pos + 6
    (didFlag = 0 → hdr.dictionaryId = none) ∧
    (didFlag = 1 → hdr.dictionaryId = some data[didOff]!.toUInt32) ∧
    (didFlag = 2 → hdr.dictionaryId = some (Binary.readUInt16LE data didOff).toUInt32) ∧
    (didFlag = 3 → hdr.dictionaryId = some (Binary.readUInt32LE data didOff)) := by
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
               obtain ⟨rfl, rfl⟩ := h; simp_all)

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
    (hparse : Zip.Native.parseBlockHeader data afterHeader = .ok (hdr, afterHdr))
    (hbs : ¬ hdr.blockSize > 131072)
    (hws : ¬ (header.windowSize > 0 && hdr.blockSize.toUInt64 > header.windowSize))
    (htype : hdr.blockType = .raw)
    (hraw : Zip.Native.decompressRawBlock data afterHdr hdr.blockSize = .ok (block, afterBlock))
    (hlast : hdr.lastBlock = true) :
    output = block := by
  have hoff := parseBlockHeader_data_not_le data afterHeader hdr afterHdr hparse
  -- Compute the exact block loop result
  have hblocks := decompressBlocksWF_single_raw data afterHeader header.windowSize
    ByteArray.empty none {} #[1, 4, 8] hdr afterHdr block afterBlock
    hoff hparse hbs hws htype hraw hlast
  frame_from_blocks

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
    (hparse : Zip.Native.parseBlockHeader data afterHeader = .ok (hdr, afterHdr))
    (hbs : ¬ hdr.blockSize > 131072)
    (hws : ¬ (header.windowSize > 0 && hdr.blockSize.toUInt64 > header.windowSize))
    (htype : hdr.blockType = .rle)
    (hrle : Zip.Native.decompressRLEBlock data afterHdr hdr.blockSize = .ok (block, afterByte))
    (hlast : hdr.lastBlock = true) :
    output = block := by
  have hoff := parseBlockHeader_data_not_le data afterHeader hdr afterHdr hparse
  -- Compute the exact block loop result
  have hblocks := decompressBlocksWF_single_rle data afterHeader header.windowSize
    ByteArray.empty none {} #[1, 4, 8] hdr afterHdr block afterByte
    hoff hparse hbs hws htype hrle hlast
  frame_from_blocks

/-- When `decompressFrame` succeeds and the frame contains two consecutive raw blocks
    (first non-last, second last), the output equals `block1 ++ block2`.
    Composes `decompressBlocksWF_two_raw_blocks` with the frame-level dictionary check,
    checksum, and content size validation. -/
theorem decompressFrame_two_raw_blocks_content (data : ByteArray)
    (pos : Nat) (output : ByteArray) (pos' : Nat)
    (header : Zip.Native.ZstdFrameHeader) (afterHeader : Nat)
    -- Block 1 (non-last raw)
    (hdr1 : Zip.Native.ZstdBlockHeader) (afterHdr1 : Nat)
    (block1 : ByteArray) (afterBlock1 : Nat)
    -- Block 2 (last raw)
    (hdr2 : Zip.Native.ZstdBlockHeader) (afterHdr2 : Nat)
    (block2 : ByteArray) (afterBlock2 : Nat)
    -- Frame hypotheses
    (hframe : Zip.Native.decompressFrame data pos = .ok (output, pos'))
    (hh : Zip.Native.parseFrameHeader data pos = .ok (header, afterHeader))
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
    (hlast2 : hdr2.lastBlock = true) :
    output = block1 ++ block2 := by
  have hoff := parseBlockHeader_data_not_le data afterHeader hdr1 afterHdr1 hparse1
  -- Compute the exact block loop result
  have hblocks := decompressBlocksWF_two_raw_blocks data afterHeader header.windowSize
    ByteArray.empty none {} #[1, 4, 8] hdr1 afterHdr1 block1 afterBlock1
    hdr2 afterHdr2 block2 afterBlock2
    hoff hparse1 hbs1 hws1 htype1 hraw1 hnotlast1 hadv1
    hoff2 hparse2 hbs2 hws2 htype2 hraw2 hlast2
  frame_from_blocks

/-- When `decompressFrame` succeeds and the frame contains two consecutive RLE blocks
    (first non-last, second last), the output equals `block1 ++ block2`.
    Composes `decompressBlocksWF_two_rle_blocks` with the frame-level dictionary check,
    checksum, and content size validation. -/
theorem decompressFrame_two_rle_blocks_content (data : ByteArray)
    (pos : Nat) (output : ByteArray) (pos' : Nat)
    (header : Zip.Native.ZstdFrameHeader) (afterHeader : Nat)
    -- Block 1 (non-last RLE)
    (hdr1 : Zip.Native.ZstdBlockHeader) (afterHdr1 : Nat)
    (block1 : ByteArray) (afterByte1 : Nat)
    -- Block 2 (last RLE)
    (hdr2 : Zip.Native.ZstdBlockHeader) (afterHdr2 : Nat)
    (block2 : ByteArray) (afterByte2 : Nat)
    -- Frame hypotheses
    (hframe : Zip.Native.decompressFrame data pos = .ok (output, pos'))
    (hh : Zip.Native.parseFrameHeader data pos = .ok (header, afterHeader))
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
    (hlast2 : hdr2.lastBlock = true) :
    output = block1 ++ block2 := by
  have hoff := parseBlockHeader_data_not_le data afterHeader hdr1 afterHdr1 hparse1
  -- Compute the exact block loop result
  have hblocks := decompressBlocksWF_two_rle_blocks data afterHeader header.windowSize
    ByteArray.empty none {} #[1, 4, 8] hdr1 afterHdr1 block1 afterByte1
    hdr2 afterHdr2 block2 afterByte2
    hoff hparse1 hbs1 hws1 htype1 hrle1 hnotlast1 hadv1
    hoff2 hparse2 hbs2 hws2 htype2 hrle2 hlast2
  frame_from_blocks

/-- When `decompressFrame` succeeds and the frame contains a non-last raw block
    followed by a last RLE block, the output equals `block1 ++ block2`.
    Composes `decompressBlocksWF_raw_then_rle` with the frame-level dictionary check,
    checksum, and content size validation. -/
theorem decompressFrame_raw_then_rle_content (data : ByteArray)
    (pos : Nat) (output : ByteArray) (pos' : Nat)
    (header : Zip.Native.ZstdFrameHeader) (afterHeader : Nat)
    -- Block 1 (non-last raw)
    (hdr1 : Zip.Native.ZstdBlockHeader) (afterHdr1 : Nat)
    (block1 : ByteArray) (afterBlock1 : Nat)
    -- Block 2 (last RLE)
    (hdr2 : Zip.Native.ZstdBlockHeader) (afterHdr2 : Nat)
    (block2 : ByteArray) (afterByte2 : Nat)
    -- Frame hypotheses
    (hframe : Zip.Native.decompressFrame data pos = .ok (output, pos'))
    (hh : Zip.Native.parseFrameHeader data pos = .ok (header, afterHeader))
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
    (hlast2 : hdr2.lastBlock = true) :
    output = block1 ++ block2 := by
  have hoff := parseBlockHeader_data_not_le data afterHeader hdr1 afterHdr1 hparse1
  -- Compute the exact block loop result
  have hblocks := decompressBlocksWF_raw_then_rle data afterHeader header.windowSize
    ByteArray.empty none {} #[1, 4, 8] hdr1 afterHdr1 block1 afterBlock1
    hdr2 afterHdr2 block2 afterByte2
    hoff hparse1 hbs1 hws1 htype1 hraw1 hnotlast1 hadv1
    hoff2 hparse2 hbs2 hws2 htype2 hrle2 hlast2
  frame_from_blocks

/-- When `decompressFrame` succeeds and the frame contains a non-last RLE block
    followed by a last raw block, the output equals `block1 ++ block2`.
    Composes `decompressBlocksWF_rle_then_raw` with the frame-level dictionary check,
    checksum, and content size validation. -/
theorem decompressFrame_rle_then_raw_content (data : ByteArray)
    (pos : Nat) (output : ByteArray) (pos' : Nat)
    (header : Zip.Native.ZstdFrameHeader) (afterHeader : Nat)
    -- Block 1 (non-last RLE)
    (hdr1 : Zip.Native.ZstdBlockHeader) (afterHdr1 : Nat)
    (block1 : ByteArray) (afterByte1 : Nat)
    -- Block 2 (last raw)
    (hdr2 : Zip.Native.ZstdBlockHeader) (afterHdr2 : Nat)
    (block2 : ByteArray) (afterBlock2 : Nat)
    -- Frame hypotheses
    (hframe : Zip.Native.decompressFrame data pos = .ok (output, pos'))
    (hh : Zip.Native.parseFrameHeader data pos = .ok (header, afterHeader))
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
    (hlast2 : hdr2.lastBlock = true) :
    output = block1 ++ block2 := by
  have hoff := parseBlockHeader_data_not_le data afterHeader hdr1 afterHdr1 hparse1
  -- Compute the exact block loop result
  have hblocks := decompressBlocksWF_rle_then_raw data afterHeader header.windowSize
    ByteArray.empty none {} #[1, 4, 8] hdr1 afterHdr1 block1 afterByte1
    hdr2 afterHdr2 block2 afterBlock2
    hoff hparse1 hbs1 hws1 htype1 hrle1 hnotlast1 hadv1
    hoff2 hparse2 hbs2 hws2 htype2 hraw2 hlast2
  frame_from_blocks

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

/-! ## decompressBlocksWF composed completeness for compressed blocks -/

/-- When a single compressed last block with numSeq=0 is encoded at offset `off`,
    with sufficient data for header + payload, and `parseLiteralsSection` and
    `parseSequencesHeader` succeed, `decompressBlocksWF` succeeds. This chains
    `parseBlockHeader_succeeds` → field characterization →
    `decompressBlocksWF_single_compressed_literals_only` into a single theorem
    with raw-byte-level header preconditions. -/
theorem decompressBlocksWF_succeeds_single_compressed_zero_seq (data : ByteArray)
    (off : Nat) (windowSize : UInt64) (output : ByteArray)
    (prevHuff : Option Zip.Native.ZstdHuffmanTable)
    (prevFse : Zip.Native.PrevFseTables) (history : Array Nat)
    (literals : ByteArray) (afterLiterals : Nat)
    (huffTree : Option Zip.Native.ZstdHuffmanTable)
    (modes : Zip.Native.SequenceCompressionModes) (afterSeqHeader : Nat)
    (hsize : data.size ≥ off + 3)
    (htypeVal : ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
        ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 2)
    (hlastBit : (data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
        ||| (data[off + 2]!.toUInt32 <<< 16)) &&& 1 = 1)
    (hblockSize : ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
        ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow : ¬ (windowSize > 0 &&
        ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
          ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > windowSize))
    (hblockEnd : data.size ≥ off + 3 +
        (((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
          ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    (hlit : Zip.Native.parseLiteralsSection data (off + 3) prevHuff
              = .ok (literals, afterLiterals, huffTree))
    (hseq : Zip.Native.parseSequencesHeader data afterLiterals
              = .ok (0, modes, afterSeqHeader)) :
    ∃ result pos',
      Zip.Native.decompressBlocksWF data off windowSize output prevHuff prevFse history
        = .ok (result, pos') := by
  -- Step 1: parseBlockHeader succeeds (typeVal=2 ≠ 3)
  have htypeNe3 : ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
      ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 ≠ 3 := by
    rw [htypeVal]; decide
  obtain ⟨hdr, afterHdr, hparse⟩ := parseBlockHeader_succeeds data off hsize htypeNe3
  -- Step 2: Extract field values from the existential result
  have htype := (parseBlockHeader_blockType_eq data off hdr afterHdr hparse).2.2 htypeVal
  have hlast_eq := parseBlockHeader_lastBlock_eq data off hdr afterHdr hparse
  have hbs_eq := parseBlockHeader_blockSize_eq data off hdr afterHdr hparse
  have hpos_eq := parseBlockHeader_pos_eq data off hdr afterHdr hparse
  -- Step 3: Derive lastBlock = true from hlastBit
  have hlast : hdr.lastBlock = true := by rw [hlast_eq, hlastBit]; decide
  -- Step 4: Derive blockSize and window size constraints
  have hbs : ¬ hdr.blockSize > 131072 := by rw [hbs_eq]; exact Nat.not_lt.mpr hblockSize
  have hws : ¬ (windowSize > 0 && hdr.blockSize.toUInt64 > windowSize) := by
    rw [hbs_eq]; exact hwindow
  -- Step 5: Derive blockEnd and rewrite parseLiteralsSection hypothesis
  have hblockEnd' : ¬ data.size < afterHdr + hdr.blockSize.toNat := by
    rw [hpos_eq, hbs_eq]; omega
  have hlit' : Zip.Native.parseLiteralsSection data afterHdr prevHuff
      = .ok (literals, afterLiterals, huffTree) := by
    rw [← hpos_eq] at hlit; exact hlit
  -- Step 6: Compose via decompressBlocksWF_single_compressed_literals_only
  have hoff : ¬ data.size ≤ off := by omega
  exact ⟨_, _, decompressBlocksWF_single_compressed_literals_only data off windowSize output
    prevHuff prevFse history hdr afterHdr literals afterLiterals huffTree modes afterSeqHeader
    hoff hparse hbs hws htype hblockEnd' hlit' hseq hlast⟩

/-! ## decompressBlocksWF two-block composed completeness (raw/RLE + compressed zero-seq) -/

/-- When a non-last raw block at `off` is followed by a last compressed block with
    numSeq == 0 (literals only) at `off2`, `decompressBlocksWF` succeeds. Composes
    `decompressBlocksWF_raw_step` with
    `decompressBlocksWF_succeeds_single_compressed_zero_seq` using only byte-level
    preconditions. -/
theorem decompressBlocksWF_succeeds_raw_then_compressed_zero_seq (data : ByteArray)
    (off off2 : Nat) (windowSize : UInt64) (output : ByteArray)
    (prevHuff : Option Zip.Native.ZstdHuffmanTable)
    (prevFse : Zip.Native.PrevFseTables) (history : Array Nat)
    (literals : ByteArray) (afterLiterals : Nat)
    (huffTree : Option Zip.Native.ZstdHuffmanTable)
    (modes : Zip.Native.SequenceCompressionModes) (afterSeqHeader : Nat)
    -- Block 1 (non-last raw) byte-level conditions at off
    (hsize1 : data.size ≥ off + 3)
    (htypeVal1 : ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
        ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 0)
    (hlastBit1 : (data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
        ||| (data[off + 2]!.toUInt32 <<< 16)) &&& 1 = 0)
    (hblockSize1 : ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
        ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow1 : ¬ (windowSize > 0 &&
        ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
          ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > windowSize))
    (hpayload1 : data.size ≥ off + 3 +
        (((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
          ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    -- off2 = position after block 1's raw payload
    (hoff2 : off2 = off + 3 + (((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
          ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    -- Block 2 (last compressed, zero sequences) byte-level conditions at off2
    (hsize2 : data.size ≥ off2 + 3)
    (htypeVal2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 2)
    (hlastBit2 : (data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) &&& 1 = 1)
    (hblockSize2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow2 : ¬ (windowSize > 0 &&
        ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
          ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > windowSize))
    (hblockEnd2 : data.size ≥ off2 + 3 +
        (((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
          ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    (hlit2 : Zip.Native.parseLiteralsSection data (off2 + 3) prevHuff
              = .ok (literals, afterLiterals, huffTree))
    (hseq2 : Zip.Native.parseSequencesHeader data afterLiterals
              = .ok (0, modes, afterSeqHeader)) :
    ∃ result pos',
      Zip.Native.decompressBlocksWF data off windowSize output prevHuff prevFse history
        = .ok (result, pos') := by
  -- Block 1: parseBlockHeader succeeds (typeVal=0 ≠ 3)
  have htypeNe3 : ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
      ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 ≠ 3 := by
    rw [htypeVal1]; decide
  obtain ⟨hdr1, afterHdr1, hparse1⟩ := parseBlockHeader_succeeds data off hsize1 htypeNe3
  have htype1 := (parseBlockHeader_blockType_eq data off hdr1 afterHdr1 hparse1).1 htypeVal1
  have hbs_eq1 := parseBlockHeader_blockSize_eq data off hdr1 afterHdr1 hparse1
  have hpos_eq1 := parseBlockHeader_pos_eq data off hdr1 afterHdr1 hparse1
  have hnotlast1 : hdr1.lastBlock = false := by
    rw [parseBlockHeader_lastBlock_eq data off hdr1 afterHdr1 hparse1, hlastBit1]; decide
  have hbs1 : ¬ hdr1.blockSize > 131072 := by rw [hbs_eq1]; exact Nat.not_lt.mpr hblockSize1
  have hws1 : ¬ (windowSize > 0 && hdr1.blockSize.toUInt64 > windowSize) := by
    rw [hbs_eq1]; exact hwindow1
  -- Block 1: decompressRawBlock succeeds
  have hpayload1' : data.size ≥ afterHdr1 + hdr1.blockSize.toNat := by
    rw [hpos_eq1, hbs_eq1]; omega
  obtain ⟨block1, afterBlock1, hraw1⟩ := decompressRawBlock_succeeds data afterHdr1
    hdr1.blockSize hpayload1'
  have hoff1 : ¬ data.size ≤ off := by omega
  have hRawPos := decompressRawBlock_pos_eq data afterHdr1 hdr1.blockSize block1
    afterBlock1 hraw1
  have hadv1 : ¬ afterBlock1 ≤ off := by rw [hRawPos, hpos_eq1]; omega
  -- afterBlock1 = off2, substitute
  have : off2 = afterBlock1 := by rw [hoff2, hRawPos, hpos_eq1, hbs_eq1]
  subst this
  -- Step through block 1, then apply succeeds_single_compressed_zero_seq for block 2
  rw [decompressBlocksWF_raw_step data off windowSize output prevHuff prevFse history
    hdr1 afterHdr1 block1 off2 hoff1 hparse1 hbs1 hws1 htype1 hraw1 hnotlast1 hadv1]
  exact decompressBlocksWF_succeeds_single_compressed_zero_seq data off2 windowSize
    (output ++ block1) prevHuff prevFse history literals afterLiterals huffTree modes
    afterSeqHeader hsize2 htypeVal2 hlastBit2 hblockSize2 hwindow2 hblockEnd2 hlit2 hseq2

/-- When a non-last RLE block at `off` is followed by a last compressed block with
    numSeq == 0 (literals only) at `off2`, `decompressBlocksWF` succeeds. Composes
    `decompressBlocksWF_rle_step` with
    `decompressBlocksWF_succeeds_single_compressed_zero_seq` using only byte-level
    preconditions. -/
theorem decompressBlocksWF_succeeds_rle_then_compressed_zero_seq (data : ByteArray)
    (off off2 : Nat) (windowSize : UInt64) (output : ByteArray)
    (prevHuff : Option Zip.Native.ZstdHuffmanTable)
    (prevFse : Zip.Native.PrevFseTables) (history : Array Nat)
    (literals : ByteArray) (afterLiterals : Nat)
    (huffTree : Option Zip.Native.ZstdHuffmanTable)
    (modes : Zip.Native.SequenceCompressionModes) (afterSeqHeader : Nat)
    -- Block 1 (non-last RLE) byte-level conditions at off
    (hsize1 : data.size ≥ off + 3)
    (htypeVal1 : ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
        ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 1)
    (hlastBit1 : (data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
        ||| (data[off + 2]!.toUInt32 <<< 16)) &&& 1 = 0)
    (hblockSize1 : ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
        ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow1 : ¬ (windowSize > 0 &&
        ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
          ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > windowSize))
    (hpayload1 : data.size ≥ off + 4)
    -- off2 = position after block 1's RLE byte
    (hoff2 : off2 = off + 4)
    -- Block 2 (last compressed, zero sequences) byte-level conditions at off2
    (hsize2 : data.size ≥ off2 + 3)
    (htypeVal2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 2)
    (hlastBit2 : (data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) &&& 1 = 1)
    (hblockSize2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow2 : ¬ (windowSize > 0 &&
        ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
          ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > windowSize))
    (hblockEnd2 : data.size ≥ off2 + 3 +
        (((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
          ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    (hlit2 : Zip.Native.parseLiteralsSection data (off2 + 3) prevHuff
              = .ok (literals, afterLiterals, huffTree))
    (hseq2 : Zip.Native.parseSequencesHeader data afterLiterals
              = .ok (0, modes, afterSeqHeader)) :
    ∃ result pos',
      Zip.Native.decompressBlocksWF data off windowSize output prevHuff prevFse history
        = .ok (result, pos') := by
  -- Block 1: parseBlockHeader succeeds (typeVal=1 ≠ 3)
  have htypeNe3 : ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
      ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 ≠ 3 := by
    rw [htypeVal1]; decide
  obtain ⟨hdr1, afterHdr1, hparse1⟩ := parseBlockHeader_succeeds data off hsize1 htypeNe3
  have htype1 := (parseBlockHeader_blockType_eq data off hdr1 afterHdr1 hparse1).2.1 htypeVal1
  have hbs_eq1 := parseBlockHeader_blockSize_eq data off hdr1 afterHdr1 hparse1
  have hpos_eq1 := parseBlockHeader_pos_eq data off hdr1 afterHdr1 hparse1
  have hnotlast1 : hdr1.lastBlock = false := by
    rw [parseBlockHeader_lastBlock_eq data off hdr1 afterHdr1 hparse1, hlastBit1]; decide
  have hbs1 : ¬ hdr1.blockSize > 131072 := by rw [hbs_eq1]; exact Nat.not_lt.mpr hblockSize1
  have hws1 : ¬ (windowSize > 0 && hdr1.blockSize.toUInt64 > windowSize) := by
    rw [hbs_eq1]; exact hwindow1
  -- Block 1: decompressRLEBlock succeeds
  have hpayload1' : data.size ≥ afterHdr1 + 1 := by rw [hpos_eq1]; omega
  obtain ⟨block1, afterByte1, hrle1⟩ := decompressRLEBlock_succeeds data afterHdr1
    hdr1.blockSize hpayload1'
  have hoff1 : ¬ data.size ≤ off := by omega
  have hRlePos := decompressRLEBlock_pos_eq data afterHdr1 hdr1.blockSize block1
    afterByte1 hrle1
  have hadv1 : ¬ afterByte1 ≤ off := by rw [hRlePos, hpos_eq1]; omega
  -- afterByte1 = off2, substitute
  have : off2 = afterByte1 := by rw [hoff2, hRlePos, hpos_eq1]
  subst this
  -- Step through block 1, then apply succeeds_single_compressed_zero_seq for block 2
  rw [decompressBlocksWF_rle_step data off windowSize output prevHuff prevFse history
    hdr1 afterHdr1 block1 off2 hoff1 hparse1 hbs1 hws1 htype1 hrle1 hnotlast1 hadv1]
  exact decompressBlocksWF_succeeds_single_compressed_zero_seq data off2 windowSize
    (output ++ block1) prevHuff prevFse history literals afterLiterals huffTree modes
    afterSeqHeader hsize2 htypeVal2 hlastBit2 hblockSize2 hwindow2 hblockEnd2 hlit2 hseq2

/-! ## decompressBlocksWF two-block composed completeness (compressed zero-seq + raw/RLE) -/

/-- When a non-last compressed block with numSeq == 0 at `off` is followed by a last raw
    block at `off2`, `decompressBlocksWF` succeeds. Composes
    `decompressBlocksWF_compressed_literals_only_step` with
    `decompressBlocksWF_succeeds_single_raw` using only byte-level preconditions. -/
theorem decompressBlocksWF_succeeds_compressed_zero_seq_then_raw (data : ByteArray)
    (off off2 : Nat) (windowSize : UInt64) (output : ByteArray)
    (prevHuff : Option Zip.Native.ZstdHuffmanTable)
    (prevFse : Zip.Native.PrevFseTables) (history : Array Nat)
    (literals1 : ByteArray) (afterLiterals1 : Nat)
    (huffTree1 : Option Zip.Native.ZstdHuffmanTable)
    (modes1 : Zip.Native.SequenceCompressionModes) (afterSeqHeader1 : Nat)
    -- Block 1 (non-last compressed, zero sequences) byte-level conditions at off
    (hsize1 : data.size ≥ off + 3)
    (htypeVal1 : ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
        ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 2)
    (hlastBit1 : (data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
        ||| (data[off + 2]!.toUInt32 <<< 16)) &&& 1 = 0)
    (hblockSize1 : ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
        ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow1 : ¬ (windowSize > 0 &&
        ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
          ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > windowSize))
    (hblockEnd1 : data.size ≥ off + 3 +
        (((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
          ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    (hlit1 : Zip.Native.parseLiteralsSection data (off + 3) prevHuff
              = .ok (literals1, afterLiterals1, huffTree1))
    (hseq1 : Zip.Native.parseSequencesHeader data afterLiterals1
              = .ok (0, modes1, afterSeqHeader1))
    -- off2 = position after block 1's payload
    (hoff2 : off2 = off + 3 + (((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
          ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    -- Block 2 (last raw) byte-level conditions at off2
    (hsize2 : data.size ≥ off2 + 3)
    (htypeVal2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 0)
    (hlastBit2 : (data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) &&& 1 = 1)
    (hblockSize2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow2 : ¬ (windowSize > 0 &&
        ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
          ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > windowSize))
    (hpayload2 : data.size ≥ off2 + 3 +
        (((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
          ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toNat)) :
    ∃ result pos',
      Zip.Native.decompressBlocksWF data off windowSize output prevHuff prevFse history
        = .ok (result, pos') := by
  -- Block 1: parseBlockHeader succeeds (typeVal=2 ≠ 3)
  have htypeNe3 : ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
      ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 ≠ 3 := by
    rw [htypeVal1]; decide
  obtain ⟨hdr1, afterHdr1, hparse1⟩ := parseBlockHeader_succeeds data off hsize1 htypeNe3
  have htype1 := (parseBlockHeader_blockType_eq data off hdr1 afterHdr1 hparse1).2.2 htypeVal1
  have hbs_eq1 := parseBlockHeader_blockSize_eq data off hdr1 afterHdr1 hparse1
  have hpos_eq1 := parseBlockHeader_pos_eq data off hdr1 afterHdr1 hparse1
  have hnotlast1 : hdr1.lastBlock = false := by
    rw [parseBlockHeader_lastBlock_eq data off hdr1 afterHdr1 hparse1, hlastBit1]; decide
  have hbs1 : ¬ hdr1.blockSize > 131072 := by rw [hbs_eq1]; exact Nat.not_lt.mpr hblockSize1
  have hws1 : ¬ (windowSize > 0 && hdr1.blockSize.toUInt64 > windowSize) := by
    rw [hbs_eq1]; exact hwindow1
  -- Block 1: derive compressed block hypotheses
  have hblockEnd1' : ¬ data.size < afterHdr1 + hdr1.blockSize.toNat := by
    rw [hpos_eq1, hbs_eq1]; exact Nat.not_lt.mpr hblockEnd1
  have hlit1' : Zip.Native.parseLiteralsSection data afterHdr1 prevHuff
      = .ok (literals1, afterLiterals1, huffTree1) := by
    rw [← hpos_eq1] at hlit1; exact hlit1
  have hoff1 : ¬ data.size ≤ off := by omega
  have hadv1 : ¬ afterHdr1 + hdr1.blockSize.toNat ≤ off := by rw [hpos_eq1]; omega
  -- off2 = afterHdr1 + blockSize1, substitute
  have : off2 = afterHdr1 + hdr1.blockSize.toNat := by rw [hoff2, hpos_eq1, hbs_eq1]
  subst this
  -- Step through block 1, then apply succeeds_single_raw for block 2
  rw [decompressBlocksWF_compressed_literals_only_step data off windowSize output prevHuff
    prevFse history hdr1 afterHdr1 literals1 afterLiterals1 huffTree1 modes1 afterSeqHeader1
    hoff1 hparse1 hbs1 hws1 htype1 hblockEnd1' hlit1' hseq1 hnotlast1 hadv1]
  exact decompressBlocksWF_succeeds_single_raw data _ windowSize (output ++ literals1)
    _ prevFse history hsize2 htypeVal2 hlastBit2 hblockSize2 hwindow2 hpayload2

/-- When a non-last compressed block with numSeq == 0 at `off` is followed by a last RLE
    block at `off2`, `decompressBlocksWF` succeeds. Composes
    `decompressBlocksWF_compressed_literals_only_step` with
    `decompressBlocksWF_succeeds_single_rle` using only byte-level preconditions. -/
theorem decompressBlocksWF_succeeds_compressed_zero_seq_then_rle (data : ByteArray)
    (off off2 : Nat) (windowSize : UInt64) (output : ByteArray)
    (prevHuff : Option Zip.Native.ZstdHuffmanTable)
    (prevFse : Zip.Native.PrevFseTables) (history : Array Nat)
    (literals1 : ByteArray) (afterLiterals1 : Nat)
    (huffTree1 : Option Zip.Native.ZstdHuffmanTable)
    (modes1 : Zip.Native.SequenceCompressionModes) (afterSeqHeader1 : Nat)
    -- Block 1 (non-last compressed, zero sequences) byte-level conditions at off
    (hsize1 : data.size ≥ off + 3)
    (htypeVal1 : ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
        ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 2)
    (hlastBit1 : (data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
        ||| (data[off + 2]!.toUInt32 <<< 16)) &&& 1 = 0)
    (hblockSize1 : ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
        ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow1 : ¬ (windowSize > 0 &&
        ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
          ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > windowSize))
    (hblockEnd1 : data.size ≥ off + 3 +
        (((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
          ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    (hlit1 : Zip.Native.parseLiteralsSection data (off + 3) prevHuff
              = .ok (literals1, afterLiterals1, huffTree1))
    (hseq1 : Zip.Native.parseSequencesHeader data afterLiterals1
              = .ok (0, modes1, afterSeqHeader1))
    -- off2 = position after block 1's payload
    (hoff2 : off2 = off + 3 + (((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
          ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    -- Block 2 (last RLE) byte-level conditions at off2
    (hsize2 : data.size ≥ off2 + 3)
    (htypeVal2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 1)
    (hlastBit2 : (data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) &&& 1 = 1)
    (hblockSize2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow2 : ¬ (windowSize > 0 &&
        ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
          ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > windowSize))
    (hpayload2 : data.size ≥ off2 + 4) :
    ∃ result pos',
      Zip.Native.decompressBlocksWF data off windowSize output prevHuff prevFse history
        = .ok (result, pos') := by
  -- Block 1: parseBlockHeader succeeds (typeVal=2 ≠ 3)
  have htypeNe3 : ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
      ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 ≠ 3 := by
    rw [htypeVal1]; decide
  obtain ⟨hdr1, afterHdr1, hparse1⟩ := parseBlockHeader_succeeds data off hsize1 htypeNe3
  have htype1 := (parseBlockHeader_blockType_eq data off hdr1 afterHdr1 hparse1).2.2 htypeVal1
  have hbs_eq1 := parseBlockHeader_blockSize_eq data off hdr1 afterHdr1 hparse1
  have hpos_eq1 := parseBlockHeader_pos_eq data off hdr1 afterHdr1 hparse1
  have hnotlast1 : hdr1.lastBlock = false := by
    rw [parseBlockHeader_lastBlock_eq data off hdr1 afterHdr1 hparse1, hlastBit1]; decide
  have hbs1 : ¬ hdr1.blockSize > 131072 := by rw [hbs_eq1]; exact Nat.not_lt.mpr hblockSize1
  have hws1 : ¬ (windowSize > 0 && hdr1.blockSize.toUInt64 > windowSize) := by
    rw [hbs_eq1]; exact hwindow1
  -- Block 1: derive compressed block hypotheses
  have hblockEnd1' : ¬ data.size < afterHdr1 + hdr1.blockSize.toNat := by
    rw [hpos_eq1, hbs_eq1]; exact Nat.not_lt.mpr hblockEnd1
  have hlit1' : Zip.Native.parseLiteralsSection data afterHdr1 prevHuff
      = .ok (literals1, afterLiterals1, huffTree1) := by
    rw [← hpos_eq1] at hlit1; exact hlit1
  have hoff1 : ¬ data.size ≤ off := by omega
  have hadv1 : ¬ afterHdr1 + hdr1.blockSize.toNat ≤ off := by rw [hpos_eq1]; omega
  -- off2 = afterHdr1 + blockSize1, substitute
  have : off2 = afterHdr1 + hdr1.blockSize.toNat := by rw [hoff2, hpos_eq1, hbs_eq1]
  subst this
  -- Step through block 1, then apply succeeds_single_rle for block 2
  rw [decompressBlocksWF_compressed_literals_only_step data off windowSize output prevHuff
    prevFse history hdr1 afterHdr1 literals1 afterLiterals1 huffTree1 modes1 afterSeqHeader1
    hoff1 hparse1 hbs1 hws1 htype1 hblockEnd1' hlit1' hseq1 hnotlast1 hadv1]
  exact decompressBlocksWF_succeeds_single_rle data _ windowSize (output ++ literals1)
    _ prevFse history hsize2 htypeVal2 hlastBit2 hblockSize2 hwindow2 hpayload2

/-! ## decompressBlocksWF two-block composed completeness (compressed sequences + raw/RLE) -/

/-- When a non-last compressed block with numSeq > 0 at `off` is followed by a last raw
    block at `off2`, `decompressBlocksWF` succeeds. Composes
    `decompressBlocksWF_compressed_sequences_step` with
    `decompressBlocksWF_succeeds_single_raw` using only byte-level preconditions. -/
theorem decompressBlocksWF_succeeds_compressed_sequences_then_raw (data : ByteArray)
    (off off2 : Nat) (windowSize : UInt64) (output : ByteArray)
    (prevHuff : Option Zip.Native.ZstdHuffmanTable)
    (prevFse : Zip.Native.PrevFseTables) (history : Array Nat)
    (literals1 : ByteArray) (afterLiterals1 : Nat)
    (huffTree1 : Option Zip.Native.ZstdHuffmanTable)
    (numSeq1 : Nat) (modes1 : Zip.Native.SequenceCompressionModes) (afterSeqHeader1 : Nat)
    (llTable1 ofTable1 mlTable1 : Zip.Native.FseTable) (afterTables1 : Nat)
    (bbr1 : Zip.Native.BackwardBitReader)
    (sequences1 : Array Zip.Native.ZstdSequence)
    (blockOutput1 : ByteArray) (newHist1 : Array Nat)
    -- Block 1 (non-last compressed, numSeq > 0) byte-level conditions at off
    (hsize1 : data.size ≥ off + 3)
    (htypeVal1 : ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
        ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 2)
    (hlastBit1 : (data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
        ||| (data[off + 2]!.toUInt32 <<< 16)) &&& 1 = 0)
    (hblockSize1 : ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
        ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow1 : ¬ (windowSize > 0 &&
        ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
          ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > windowSize))
    (hblockEnd1 : data.size ≥ off + 3 +
        (((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
          ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    (hlit1 : Zip.Native.parseLiteralsSection data (off + 3) prevHuff
              = .ok (literals1, afterLiterals1, huffTree1))
    (hseq1 : Zip.Native.parseSequencesHeader data afterLiterals1
              = .ok (numSeq1, modes1, afterSeqHeader1))
    (hNumSeq1 : ¬ numSeq1 == 0)
    (hfse1 : Zip.Native.resolveSequenceFseTables modes1 data afterSeqHeader1 prevFse
              = .ok (llTable1, ofTable1, mlTable1, afterTables1))
    (hbbr1 : Zip.Native.BackwardBitReader.init data afterTables1
              (off + 3 + (((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
                ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
              = .ok bbr1)
    (hdec1 : Zip.Native.decodeSequences llTable1 ofTable1 mlTable1 bbr1 numSeq1
              = .ok sequences1)
    (hexec1 : Zip.Native.executeSequences sequences1 literals1
               (if windowSize > 0 && output.size > windowSize.toNat
                then output.extract (output.size - windowSize.toNat) output.size
                else output)
               history windowSize.toNat
               = .ok (blockOutput1, newHist1))
    -- off2 = position after block 1's payload
    (hoff2 : off2 = off + 3 + (((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
          ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    -- Block 2 (last raw) byte-level conditions at off2
    (hsize2 : data.size ≥ off2 + 3)
    (htypeVal2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 0)
    (hlastBit2 : (data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) &&& 1 = 1)
    (hblockSize2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow2 : ¬ (windowSize > 0 &&
        ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
          ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > windowSize))
    (hpayload2 : data.size ≥ off2 + 3 +
        (((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
          ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toNat)) :
    ∃ result pos',
      Zip.Native.decompressBlocksWF data off windowSize output prevHuff prevFse history
        = .ok (result, pos') := by
  -- Block 1: parseBlockHeader succeeds (typeVal=2 ≠ 3)
  have htypeNe3 : ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
      ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 ≠ 3 := by
    rw [htypeVal1]; decide
  obtain ⟨hdr1, afterHdr1, hparse1⟩ := parseBlockHeader_succeeds data off hsize1 htypeNe3
  have htype1 := (parseBlockHeader_blockType_eq data off hdr1 afterHdr1 hparse1).2.2 htypeVal1
  have hbs_eq1 := parseBlockHeader_blockSize_eq data off hdr1 afterHdr1 hparse1
  have hpos_eq1 := parseBlockHeader_pos_eq data off hdr1 afterHdr1 hparse1
  have hnotlast1 : hdr1.lastBlock = false := by
    rw [parseBlockHeader_lastBlock_eq data off hdr1 afterHdr1 hparse1, hlastBit1]; decide
  have hbs1 : ¬ hdr1.blockSize > 131072 := by rw [hbs_eq1]; exact Nat.not_lt.mpr hblockSize1
  have hws1 : ¬ (windowSize > 0 && hdr1.blockSize.toUInt64 > windowSize) := by
    rw [hbs_eq1]; exact hwindow1
  -- Block 1: derive compressed block hypotheses
  have hblockEnd1' : ¬ data.size < afterHdr1 + hdr1.blockSize.toNat := by
    rw [hpos_eq1, hbs_eq1]; exact Nat.not_lt.mpr hblockEnd1
  have hlit1' : Zip.Native.parseLiteralsSection data afterHdr1 prevHuff
      = .ok (literals1, afterLiterals1, huffTree1) := by
    rw [← hpos_eq1] at hlit1; exact hlit1
  have hbbr1' : Zip.Native.BackwardBitReader.init data afterTables1
      (afterHdr1 + hdr1.blockSize.toNat) = .ok bbr1 := by
    rw [← hpos_eq1, ← hbs_eq1] at hbbr1; exact hbbr1
  have hoff1 : ¬ data.size ≤ off := by omega
  have hadv1 : ¬ afterHdr1 + hdr1.blockSize.toNat ≤ off := by rw [hpos_eq1]; omega
  -- off2 = afterHdr1 + blockSize1, substitute
  have : off2 = afterHdr1 + hdr1.blockSize.toNat := by rw [hoff2, hpos_eq1, hbs_eq1]
  subst this
  -- Step through block 1, then apply succeeds_single_raw for block 2
  rw [decompressBlocksWF_compressed_sequences_step data off windowSize output prevHuff
    prevFse history hdr1 afterHdr1 literals1 afterLiterals1 huffTree1 numSeq1 modes1
    afterSeqHeader1 llTable1 ofTable1 mlTable1 afterTables1 bbr1 sequences1 blockOutput1
    newHist1 hoff1 hparse1 hbs1 hws1 htype1 hblockEnd1' hlit1' hseq1 hNumSeq1 hfse1 hbbr1'
    hdec1 hexec1 hnotlast1 hadv1]
  exact decompressBlocksWF_succeeds_single_raw data _ windowSize (output ++ blockOutput1)
    _ { litLen := some llTable1, offset := some ofTable1, matchLen := some mlTable1 }
    newHist1 hsize2 htypeVal2 hlastBit2 hblockSize2 hwindow2 hpayload2

/-- When a non-last compressed block with numSeq > 0 at `off` is followed by a last RLE
    block at `off2`, `decompressBlocksWF` succeeds. Composes
    `decompressBlocksWF_compressed_sequences_step` with
    `decompressBlocksWF_succeeds_single_rle` using only byte-level preconditions. -/
theorem decompressBlocksWF_succeeds_compressed_sequences_then_rle (data : ByteArray)
    (off off2 : Nat) (windowSize : UInt64) (output : ByteArray)
    (prevHuff : Option Zip.Native.ZstdHuffmanTable)
    (prevFse : Zip.Native.PrevFseTables) (history : Array Nat)
    (literals1 : ByteArray) (afterLiterals1 : Nat)
    (huffTree1 : Option Zip.Native.ZstdHuffmanTable)
    (numSeq1 : Nat) (modes1 : Zip.Native.SequenceCompressionModes) (afterSeqHeader1 : Nat)
    (llTable1 ofTable1 mlTable1 : Zip.Native.FseTable) (afterTables1 : Nat)
    (bbr1 : Zip.Native.BackwardBitReader)
    (sequences1 : Array Zip.Native.ZstdSequence)
    (blockOutput1 : ByteArray) (newHist1 : Array Nat)
    -- Block 1 (non-last compressed, numSeq > 0) byte-level conditions at off
    (hsize1 : data.size ≥ off + 3)
    (htypeVal1 : ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
        ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 2)
    (hlastBit1 : (data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
        ||| (data[off + 2]!.toUInt32 <<< 16)) &&& 1 = 0)
    (hblockSize1 : ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
        ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow1 : ¬ (windowSize > 0 &&
        ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
          ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > windowSize))
    (hblockEnd1 : data.size ≥ off + 3 +
        (((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
          ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    (hlit1 : Zip.Native.parseLiteralsSection data (off + 3) prevHuff
              = .ok (literals1, afterLiterals1, huffTree1))
    (hseq1 : Zip.Native.parseSequencesHeader data afterLiterals1
              = .ok (numSeq1, modes1, afterSeqHeader1))
    (hNumSeq1 : ¬ numSeq1 == 0)
    (hfse1 : Zip.Native.resolveSequenceFseTables modes1 data afterSeqHeader1 prevFse
              = .ok (llTable1, ofTable1, mlTable1, afterTables1))
    (hbbr1 : Zip.Native.BackwardBitReader.init data afterTables1
              (off + 3 + (((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
                ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
              = .ok bbr1)
    (hdec1 : Zip.Native.decodeSequences llTable1 ofTable1 mlTable1 bbr1 numSeq1
              = .ok sequences1)
    (hexec1 : Zip.Native.executeSequences sequences1 literals1
               (if windowSize > 0 && output.size > windowSize.toNat
                then output.extract (output.size - windowSize.toNat) output.size
                else output)
               history windowSize.toNat
               = .ok (blockOutput1, newHist1))
    -- off2 = position after block 1's payload
    (hoff2 : off2 = off + 3 + (((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
          ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    -- Block 2 (last RLE) byte-level conditions at off2
    (hsize2 : data.size ≥ off2 + 3)
    (htypeVal2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 1)
    (hlastBit2 : (data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) &&& 1 = 1)
    (hblockSize2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow2 : ¬ (windowSize > 0 &&
        ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
          ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > windowSize))
    (hpayload2 : data.size ≥ off2 + 4) :
    ∃ result pos',
      Zip.Native.decompressBlocksWF data off windowSize output prevHuff prevFse history
        = .ok (result, pos') := by
  -- Block 1: parseBlockHeader succeeds (typeVal=2 ≠ 3)
  have htypeNe3 : ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
      ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 ≠ 3 := by
    rw [htypeVal1]; decide
  obtain ⟨hdr1, afterHdr1, hparse1⟩ := parseBlockHeader_succeeds data off hsize1 htypeNe3
  have htype1 := (parseBlockHeader_blockType_eq data off hdr1 afterHdr1 hparse1).2.2 htypeVal1
  have hbs_eq1 := parseBlockHeader_blockSize_eq data off hdr1 afterHdr1 hparse1
  have hpos_eq1 := parseBlockHeader_pos_eq data off hdr1 afterHdr1 hparse1
  have hnotlast1 : hdr1.lastBlock = false := by
    rw [parseBlockHeader_lastBlock_eq data off hdr1 afterHdr1 hparse1, hlastBit1]; decide
  have hbs1 : ¬ hdr1.blockSize > 131072 := by rw [hbs_eq1]; exact Nat.not_lt.mpr hblockSize1
  have hws1 : ¬ (windowSize > 0 && hdr1.blockSize.toUInt64 > windowSize) := by
    rw [hbs_eq1]; exact hwindow1
  -- Block 1: derive compressed block hypotheses
  have hblockEnd1' : ¬ data.size < afterHdr1 + hdr1.blockSize.toNat := by
    rw [hpos_eq1, hbs_eq1]; exact Nat.not_lt.mpr hblockEnd1
  have hlit1' : Zip.Native.parseLiteralsSection data afterHdr1 prevHuff
      = .ok (literals1, afterLiterals1, huffTree1) := by
    rw [← hpos_eq1] at hlit1; exact hlit1
  have hbbr1' : Zip.Native.BackwardBitReader.init data afterTables1
      (afterHdr1 + hdr1.blockSize.toNat) = .ok bbr1 := by
    rw [← hpos_eq1, ← hbs_eq1] at hbbr1; exact hbbr1
  have hoff1 : ¬ data.size ≤ off := by omega
  have hadv1 : ¬ afterHdr1 + hdr1.blockSize.toNat ≤ off := by rw [hpos_eq1]; omega
  -- off2 = afterHdr1 + blockSize1, substitute
  have : off2 = afterHdr1 + hdr1.blockSize.toNat := by rw [hoff2, hpos_eq1, hbs_eq1]
  subst this
  -- Step through block 1, then apply succeeds_single_rle for block 2
  rw [decompressBlocksWF_compressed_sequences_step data off windowSize output prevHuff
    prevFse history hdr1 afterHdr1 literals1 afterLiterals1 huffTree1 numSeq1 modes1
    afterSeqHeader1 llTable1 ofTable1 mlTable1 afterTables1 bbr1 sequences1 blockOutput1
    newHist1 hoff1 hparse1 hbs1 hws1 htype1 hblockEnd1' hlit1' hseq1 hNumSeq1 hfse1 hbbr1'
    hdec1 hexec1 hnotlast1 hadv1]
  exact decompressBlocksWF_succeeds_single_rle data _ windowSize (output ++ blockOutput1)
    _ { litLen := some llTable1, offset := some ofTable1, matchLen := some mlTable1 }
    newHist1 hsize2 htypeVal2 hlastBit2 hblockSize2 hwindow2 hpayload2

/-- When a single compressed last block with numSeq > 0 is encoded at offset `off`,
    with sufficient data for header + payload, and all sub-functions succeed,
    `decompressBlocksWF` succeeds. This chains `parseBlockHeader_succeeds` → field
    characterization → `decompressBlocksWF_single_compressed_sequences` into a
    single theorem with raw-byte-level header preconditions. -/
theorem decompressBlocksWF_succeeds_single_compressed_sequences (data : ByteArray)
    (off : Nat) (windowSize : UInt64) (output : ByteArray)
    (prevHuff : Option Zip.Native.ZstdHuffmanTable)
    (prevFse : Zip.Native.PrevFseTables) (history : Array Nat)
    (literals : ByteArray) (afterLiterals : Nat)
    (huffTree : Option Zip.Native.ZstdHuffmanTable)
    (numSeq : Nat) (modes : Zip.Native.SequenceCompressionModes) (afterSeqHeader : Nat)
    (llTable ofTable mlTable : Zip.Native.FseTable) (afterTables : Nat)
    (bbr : Zip.Native.BackwardBitReader)
    (sequences : Array Zip.Native.ZstdSequence)
    (blockOutput : ByteArray) (newHist : Array Nat)
    (hsize : data.size ≥ off + 3)
    (htypeVal : ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
        ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 2)
    (hlastBit : (data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
        ||| (data[off + 2]!.toUInt32 <<< 16)) &&& 1 = 1)
    (hblockSize : ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
        ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow : ¬ (windowSize > 0 &&
        ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
          ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > windowSize))
    (hblockEnd : data.size ≥ off + 3 +
        (((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
          ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    (hlit : Zip.Native.parseLiteralsSection data (off + 3) prevHuff
              = .ok (literals, afterLiterals, huffTree))
    (hseq : Zip.Native.parseSequencesHeader data afterLiterals
              = .ok (numSeq, modes, afterSeqHeader))
    (hNumSeq : ¬ numSeq == 0)
    (hfse : Zip.Native.resolveSequenceFseTables modes data afterSeqHeader prevFse
              = .ok (llTable, ofTable, mlTable, afterTables))
    (hbbr : Zip.Native.BackwardBitReader.init data afterTables
              (off + 3 + (((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
                ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
              = .ok bbr)
    (hdec : Zip.Native.decodeSequences llTable ofTable mlTable bbr numSeq
              = .ok sequences)
    (hexec : Zip.Native.executeSequences sequences literals
               (if windowSize > 0 && output.size > windowSize.toNat
                then output.extract (output.size - windowSize.toNat) output.size
                else output)
               history windowSize.toNat
               = .ok (blockOutput, newHist)) :
    ∃ result pos',
      Zip.Native.decompressBlocksWF data off windowSize output prevHuff prevFse history
        = .ok (result, pos') := by
  -- Step 1: parseBlockHeader succeeds (typeVal=2 ≠ 3)
  have htypeNe3 : ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
      ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 ≠ 3 := by
    rw [htypeVal]; decide
  obtain ⟨hdr, afterHdr, hparse⟩ := parseBlockHeader_succeeds data off hsize htypeNe3
  -- Step 2: Extract field values from the existential result
  have htype := (parseBlockHeader_blockType_eq data off hdr afterHdr hparse).2.2 htypeVal
  have hlast_eq := parseBlockHeader_lastBlock_eq data off hdr afterHdr hparse
  have hbs_eq := parseBlockHeader_blockSize_eq data off hdr afterHdr hparse
  have hpos_eq := parseBlockHeader_pos_eq data off hdr afterHdr hparse
  -- Step 3: Derive lastBlock = true from hlastBit
  have hlast : hdr.lastBlock = true := by rw [hlast_eq, hlastBit]; decide
  -- Step 4: Derive blockSize and window size constraints
  have hbs : ¬ hdr.blockSize > 131072 := by rw [hbs_eq]; exact Nat.not_lt.mpr hblockSize
  have hws : ¬ (windowSize > 0 && hdr.blockSize.toUInt64 > windowSize) := by
    rw [hbs_eq]; exact hwindow
  -- Step 5: Derive blockEnd and rewrite hypotheses
  have hblockEnd' : ¬ data.size < afterHdr + hdr.blockSize.toNat := by
    rw [hpos_eq, hbs_eq]; omega
  have hlit' : Zip.Native.parseLiteralsSection data afterHdr prevHuff
      = .ok (literals, afterLiterals, huffTree) := by
    rw [← hpos_eq] at hlit; exact hlit
  have hbbr' : Zip.Native.BackwardBitReader.init data afterTables
      (afterHdr + hdr.blockSize.toNat) = .ok bbr := by
    rw [← hpos_eq, ← hbs_eq] at hbbr; exact hbbr
  -- Step 6: Compose via decompressBlocksWF_single_compressed_sequences
  have hoff : ¬ data.size ≤ off := by omega
  exact ⟨_, _, decompressBlocksWF_single_compressed_sequences data off windowSize output
    prevHuff prevFse history hdr afterHdr literals afterLiterals huffTree numSeq modes
    afterSeqHeader llTable ofTable mlTable afterTables bbr sequences blockOutput newHist
    hoff hparse hbs hws htype hblockEnd' hlit' hseq hNumSeq hfse hbbr' hdec hexec hlast⟩

/-! ## decompressBlocksWF two-block composed completeness (compressed zero-seq + compressed) -/

/-- When a non-last compressed block with numSeq == 0 at `off` is followed by a last compressed
    block with numSeq == 0 at `off2`, `decompressBlocksWF` succeeds. Composes
    `decompressBlocksWF_compressed_literals_only_step` with
    `decompressBlocksWF_succeeds_single_compressed_zero_seq` using only byte-level preconditions.
    Unlike the raw/RLE variants, we subst `afterHdr1` early to avoid a dependent-match
    mismatch between `hlit1` and `hlit2`'s Huffman table argument. -/
theorem decompressBlocksWF_succeeds_compressed_zero_seq_then_compressed_zero_seq
    (data : ByteArray)
    (off off2 : Nat) (windowSize : UInt64) (output : ByteArray)
    (prevHuff : Option Zip.Native.ZstdHuffmanTable)
    (prevFse : Zip.Native.PrevFseTables) (history : Array Nat)
    (literals1 : ByteArray) (afterLiterals1 : Nat)
    (huffTree1 : Option Zip.Native.ZstdHuffmanTable)
    (modes1 : Zip.Native.SequenceCompressionModes) (afterSeqHeader1 : Nat)
    (literals2 : ByteArray) (afterLiterals2 : Nat)
    (huffTree2 : Option Zip.Native.ZstdHuffmanTable)
    (modes2 : Zip.Native.SequenceCompressionModes) (afterSeqHeader2 : Nat)
    -- Block 1 (non-last compressed, zero sequences) byte-level conditions at off
    (hsize1 : data.size ≥ off + 3)
    (htypeVal1 : ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
        ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 2)
    (hlastBit1 : (data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
        ||| (data[off + 2]!.toUInt32 <<< 16)) &&& 1 = 0)
    (hblockSize1 : ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
        ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow1 : ¬ (windowSize > 0 &&
        ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
          ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > windowSize))
    (hblockEnd1 : data.size ≥ off + 3 +
        (((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
          ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    (hlit1 : Zip.Native.parseLiteralsSection data (off + 3) prevHuff
              = .ok (literals1, afterLiterals1, huffTree1))
    (hseq1 : Zip.Native.parseSequencesHeader data afterLiterals1
              = .ok (0, modes1, afterSeqHeader1))
    -- off2 = position after block 1's payload
    (hoff2 : off2 = off + 3 + (((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
          ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    -- Block 2 (last compressed, zero sequences) byte-level conditions at off2
    (hsize2 : data.size ≥ off2 + 3)
    (htypeVal2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 2)
    (hlastBit2 : (data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) &&& 1 = 1)
    (hblockSize2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow2 : ¬ (windowSize > 0 &&
        ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
          ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > windowSize))
    (hblockEnd2 : data.size ≥ off2 + 3 +
        (((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
          ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    (hlit2 : Zip.Native.parseLiteralsSection data (off2 + 3)
              (if let some ht := huffTree1 then some ht else prevHuff)
              = .ok (literals2, afterLiterals2, huffTree2))
    (hseq2 : Zip.Native.parseSequencesHeader data afterLiterals2
              = .ok (0, modes2, afterSeqHeader2)) :
    ∃ result pos',
      Zip.Native.decompressBlocksWF data off windowSize output prevHuff prevFse history
        = .ok (result, pos') := by
  -- Block 1: parseBlockHeader succeeds (typeVal=2 ≠ 3)
  have htypeNe3 : ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
      ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 ≠ 3 := by
    rw [htypeVal1]; decide
  obtain ⟨hdr1, afterHdr1, hparse1⟩ := parseBlockHeader_succeeds data off hsize1 htypeNe3
  -- Subst afterHdr1 = off + 3 early to preserve hlit1 identity in dependent matches
  have hpos_eq1 := parseBlockHeader_pos_eq data off hdr1 afterHdr1 hparse1
  subst hpos_eq1
  have htype1 := (parseBlockHeader_blockType_eq data off hdr1 (off + 3) hparse1).2.2 htypeVal1
  have hbs_eq1 := parseBlockHeader_blockSize_eq data off hdr1 (off + 3) hparse1
  have hnotlast1 : hdr1.lastBlock = false := by
    rw [parseBlockHeader_lastBlock_eq data off hdr1 (off + 3) hparse1, hlastBit1]; decide
  have hbs1 : ¬ hdr1.blockSize > 131072 := by rw [hbs_eq1]; exact Nat.not_lt.mpr hblockSize1
  have hws1 : ¬ (windowSize > 0 && hdr1.blockSize.toUInt64 > windowSize) := by
    rw [hbs_eq1]; exact hwindow1
  have hblockEnd1' : ¬ data.size < (off + 3) + hdr1.blockSize.toNat := by
    rw [hbs_eq1]; exact Nat.not_lt.mpr hblockEnd1
  have hoff1 : ¬ data.size ≤ off := by omega
  have hadv1 : ¬ (off + 3) + hdr1.blockSize.toNat ≤ off := by omega
  -- off2 = (off + 3) + blockSize1, substitute
  have : off2 = (off + 3) + hdr1.blockSize.toNat := by rw [hoff2, hbs_eq1]
  subst this
  -- Step through block 1, then apply succeeds_single_compressed_zero_seq for block 2
  rw [decompressBlocksWF_compressed_literals_only_step data off windowSize output prevHuff
    prevFse history hdr1 (off + 3) literals1 afterLiterals1 huffTree1 modes1 afterSeqHeader1
    hoff1 hparse1 hbs1 hws1 htype1 hblockEnd1' hlit1 hseq1 hnotlast1 hadv1]
  -- Case-split huffTree1 to reduce the if-let match and avoid alpha-equivalence mismatch
  cases huffTree1 <;>
    exact decompressBlocksWF_succeeds_single_compressed_zero_seq data _ windowSize
      (output ++ literals1) _ prevFse history literals2 afterLiterals2 huffTree2 modes2
      afterSeqHeader2 hsize2 htypeVal2 hlastBit2 hblockSize2 hwindow2 hblockEnd2 hlit2 hseq2

/-- When a non-last compressed block with numSeq == 0 at `off` is followed by a last compressed
    block with numSeq > 0 at `off2`, `decompressBlocksWF` succeeds. Composes
    `decompressBlocksWF_compressed_literals_only_step` with
    `decompressBlocksWF_succeeds_single_compressed_sequences` using only byte-level
    preconditions. -/
theorem decompressBlocksWF_succeeds_compressed_zero_seq_then_compressed_sequences
    (data : ByteArray)
    (off off2 : Nat) (windowSize : UInt64) (output : ByteArray)
    (prevHuff : Option Zip.Native.ZstdHuffmanTable)
    (prevFse : Zip.Native.PrevFseTables) (history : Array Nat)
    (literals1 : ByteArray) (afterLiterals1 : Nat)
    (huffTree1 : Option Zip.Native.ZstdHuffmanTable)
    (modes1 : Zip.Native.SequenceCompressionModes) (afterSeqHeader1 : Nat)
    (literals2 : ByteArray) (afterLiterals2 : Nat)
    (huffTree2 : Option Zip.Native.ZstdHuffmanTable)
    (numSeq2 : Nat) (modes2 : Zip.Native.SequenceCompressionModes) (afterSeqHeader2 : Nat)
    (llTable2 ofTable2 mlTable2 : Zip.Native.FseTable) (afterTables2 : Nat)
    (bbr2 : Zip.Native.BackwardBitReader)
    (sequences2 : Array Zip.Native.ZstdSequence)
    (blockOutput2 : ByteArray) (newHist2 : Array Nat)
    -- Block 1 (non-last compressed, zero sequences) byte-level conditions at off
    (hsize1 : data.size ≥ off + 3)
    (htypeVal1 : ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
        ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 2)
    (hlastBit1 : (data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
        ||| (data[off + 2]!.toUInt32 <<< 16)) &&& 1 = 0)
    (hblockSize1 : ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
        ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow1 : ¬ (windowSize > 0 &&
        ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
          ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > windowSize))
    (hblockEnd1 : data.size ≥ off + 3 +
        (((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
          ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    (hlit1 : Zip.Native.parseLiteralsSection data (off + 3) prevHuff
              = .ok (literals1, afterLiterals1, huffTree1))
    (hseq1 : Zip.Native.parseSequencesHeader data afterLiterals1
              = .ok (0, modes1, afterSeqHeader1))
    -- off2 = position after block 1's payload
    (hoff2 : off2 = off + 3 + (((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
          ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    -- Block 2 (last compressed, with sequences) byte-level conditions at off2
    (hsize2 : data.size ≥ off2 + 3)
    (htypeVal2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 2)
    (hlastBit2 : (data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) &&& 1 = 1)
    (hblockSize2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow2 : ¬ (windowSize > 0 &&
        ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
          ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > windowSize))
    (hblockEnd2 : data.size ≥ off2 + 3 +
        (((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
          ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    (hlit2 : Zip.Native.parseLiteralsSection data (off2 + 3)
              (if let some ht := huffTree1 then some ht else prevHuff)
              = .ok (literals2, afterLiterals2, huffTree2))
    (hseq2 : Zip.Native.parseSequencesHeader data afterLiterals2
              = .ok (numSeq2, modes2, afterSeqHeader2))
    (hNumSeq2 : ¬ numSeq2 == 0)
    (hfse2 : Zip.Native.resolveSequenceFseTables modes2 data afterSeqHeader2 prevFse
              = .ok (llTable2, ofTable2, mlTable2, afterTables2))
    (hbbr2 : Zip.Native.BackwardBitReader.init data afterTables2
              (off2 + 3 + (((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
                ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
              = .ok bbr2)
    (hdec2 : Zip.Native.decodeSequences llTable2 ofTable2 mlTable2 bbr2 numSeq2
              = .ok sequences2)
    (hexec2 : Zip.Native.executeSequences sequences2 literals2
               (if windowSize > 0 && (output ++ literals1).size > windowSize.toNat
                then (output ++ literals1).extract
                  ((output ++ literals1).size - windowSize.toNat) (output ++ literals1).size
                else (output ++ literals1))
               history windowSize.toNat
               = .ok (blockOutput2, newHist2)) :
    ∃ result pos',
      Zip.Native.decompressBlocksWF data off windowSize output prevHuff prevFse history
        = .ok (result, pos') := by
  -- Block 1: parseBlockHeader succeeds (typeVal=2 ≠ 3)
  have htypeNe3 : ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
      ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 ≠ 3 := by
    rw [htypeVal1]; decide
  obtain ⟨hdr1, afterHdr1, hparse1⟩ := parseBlockHeader_succeeds data off hsize1 htypeNe3
  -- Subst afterHdr1 = off + 3 early to preserve hlit1 identity in dependent matches
  have hpos_eq1 := parseBlockHeader_pos_eq data off hdr1 afterHdr1 hparse1
  subst hpos_eq1
  have htype1 := (parseBlockHeader_blockType_eq data off hdr1 (off + 3) hparse1).2.2 htypeVal1
  have hbs_eq1 := parseBlockHeader_blockSize_eq data off hdr1 (off + 3) hparse1
  have hnotlast1 : hdr1.lastBlock = false := by
    rw [parseBlockHeader_lastBlock_eq data off hdr1 (off + 3) hparse1, hlastBit1]; decide
  have hbs1 : ¬ hdr1.blockSize > 131072 := by rw [hbs_eq1]; exact Nat.not_lt.mpr hblockSize1
  have hws1 : ¬ (windowSize > 0 && hdr1.blockSize.toUInt64 > windowSize) := by
    rw [hbs_eq1]; exact hwindow1
  have hblockEnd1' : ¬ data.size < (off + 3) + hdr1.blockSize.toNat := by
    rw [hbs_eq1]; exact Nat.not_lt.mpr hblockEnd1
  have hoff1 : ¬ data.size ≤ off := by omega
  have hadv1 : ¬ (off + 3) + hdr1.blockSize.toNat ≤ off := by omega
  -- off2 = (off + 3) + blockSize1, substitute
  have : off2 = (off + 3) + hdr1.blockSize.toNat := by rw [hoff2, hbs_eq1]
  subst this
  -- Step through block 1, then apply succeeds_single_compressed_sequences for block 2
  rw [decompressBlocksWF_compressed_literals_only_step data off windowSize output prevHuff
    prevFse history hdr1 (off + 3) literals1 afterLiterals1 huffTree1 modes1 afterSeqHeader1
    hoff1 hparse1 hbs1 hws1 htype1 hblockEnd1' hlit1 hseq1 hnotlast1 hadv1]
  -- Case-split huffTree1 to reduce the if-let match and avoid alpha-equivalence mismatch
  cases huffTree1 <;>
    exact decompressBlocksWF_succeeds_single_compressed_sequences data _ windowSize
      (output ++ literals1) _ prevFse history literals2 afterLiterals2 huffTree2 numSeq2 modes2
      afterSeqHeader2 llTable2 ofTable2 mlTable2 afterTables2 bbr2 sequences2 blockOutput2
      newHist2 hsize2 htypeVal2 hlastBit2 hblockSize2 hwindow2 hblockEnd2 hlit2 hseq2 hNumSeq2
      hfse2 hbbr2 hdec2 hexec2

/-! ## decompressBlocksWF two-block composed completeness (compressed sequences + compressed) -/

/-- When a non-last compressed block with numSeq > 0 at `off` is followed by a last
    compressed block with numSeq == 0 at `off2`, `decompressBlocksWF` succeeds. Composes
    `decompressBlocksWF_compressed_sequences_step` with
    `decompressBlocksWF_succeeds_single_compressed_zero_seq` using only byte-level
    header preconditions. Block 2 uses the updated Huffman table from block 1. -/
theorem decompressBlocksWF_succeeds_compressed_sequences_then_compressed_zero_seq
    (data : ByteArray)
    (off off2 : Nat) (windowSize : UInt64) (output : ByteArray)
    (prevHuff : Option Zip.Native.ZstdHuffmanTable)
    (prevFse : Zip.Native.PrevFseTables) (history : Array Nat)
    -- Block 1 (non-last compressed, numSeq > 0) parsed results
    (literals1 : ByteArray) (afterLiterals1 : Nat)
    (huffTree1 : Option Zip.Native.ZstdHuffmanTable)
    (numSeq1 : Nat) (modes1 : Zip.Native.SequenceCompressionModes) (afterSeqHeader1 : Nat)
    (llTable1 ofTable1 mlTable1 : Zip.Native.FseTable) (afterTables1 : Nat)
    (bbr1 : Zip.Native.BackwardBitReader)
    (sequences1 : Array Zip.Native.ZstdSequence)
    (blockOutput1 : ByteArray) (newHist1 : Array Nat)
    -- Block 2 (last compressed, numSeq=0) parsed results
    (literals2 : ByteArray) (afterLiterals2 : Nat)
    (huffTree2 : Option Zip.Native.ZstdHuffmanTable)
    (modes2 : Zip.Native.SequenceCompressionModes) (afterSeqHeader2 : Nat)
    -- Block 1 byte-level header conditions at off
    (hsize1 : data.size ≥ off + 3)
    (htypeVal1 : ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
        ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 2)
    (hlastBit1 : (data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
        ||| (data[off + 2]!.toUInt32 <<< 16)) &&& 1 = 0)
    (hblockSize1 : ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
        ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow1 : ¬ (windowSize > 0 &&
        ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
          ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > windowSize))
    (hblockEnd1 : data.size ≥ off + 3 +
        (((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
          ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    -- Block 1 pipeline hypotheses
    (hlit1 : Zip.Native.parseLiteralsSection data (off + 3) prevHuff
              = .ok (literals1, afterLiterals1, huffTree1))
    (hseq1 : Zip.Native.parseSequencesHeader data afterLiterals1
              = .ok (numSeq1, modes1, afterSeqHeader1))
    (hNumSeq1 : ¬ numSeq1 == 0)
    (hfse1 : Zip.Native.resolveSequenceFseTables modes1 data afterSeqHeader1 prevFse
              = .ok (llTable1, ofTable1, mlTable1, afterTables1))
    (hbbr1 : Zip.Native.BackwardBitReader.init data afterTables1
              (off + 3 + (((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
                ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
              = .ok bbr1)
    (hdec1 : Zip.Native.decodeSequences llTable1 ofTable1 mlTable1 bbr1 numSeq1
              = .ok sequences1)
    (hexec1 : Zip.Native.executeSequences sequences1 literals1
               (if windowSize > 0 && output.size > windowSize.toNat
                then output.extract (output.size - windowSize.toNat) output.size
                else output)
               history windowSize.toNat
               = .ok (blockOutput1, newHist1))
    -- off2 = position after block 1's payload
    (hoff2 : off2 = off + 3 + (((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
          ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    -- Block 2 byte-level header conditions at off2
    (hsize2 : data.size ≥ off2 + 3)
    (htypeVal2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 2)
    (hlastBit2 : (data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) &&& 1 = 1)
    (hblockSize2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow2 : ¬ (windowSize > 0 &&
        ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
          ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > windowSize))
    (hblockEnd2 : data.size ≥ off2 + 3 +
        (((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
          ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    -- Block 2 pipeline hypotheses
    (hlit2 : Zip.Native.parseLiteralsSection data (off2 + 3)
              (if let some ht := huffTree1 then some ht else prevHuff)
              = .ok (literals2, afterLiterals2, huffTree2))
    (hseq2 : Zip.Native.parseSequencesHeader data afterLiterals2
              = .ok (0, modes2, afterSeqHeader2)) :
    ∃ result pos',
      Zip.Native.decompressBlocksWF data off windowSize output prevHuff prevFse history
        = .ok (result, pos') := by
  -- Block 1: parseBlockHeader succeeds (typeVal=2 ≠ 3)
  have htypeNe3 : ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
      ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 ≠ 3 := by
    rw [htypeVal1]; decide
  obtain ⟨hdr1, afterHdr1, hparse1⟩ := parseBlockHeader_succeeds data off hsize1 htypeNe3
  have htype1 := (parseBlockHeader_blockType_eq data off hdr1 afterHdr1 hparse1).2.2 htypeVal1
  have hbs_eq1 := parseBlockHeader_blockSize_eq data off hdr1 afterHdr1 hparse1
  have hpos_eq1 := parseBlockHeader_pos_eq data off hdr1 afterHdr1 hparse1
  have hnotlast1 : hdr1.lastBlock = false := by
    rw [parseBlockHeader_lastBlock_eq data off hdr1 afterHdr1 hparse1, hlastBit1]; decide
  have hbs1 : ¬ hdr1.blockSize > 131072 := by rw [hbs_eq1]; exact Nat.not_lt.mpr hblockSize1
  have hws1 : ¬ (windowSize > 0 && hdr1.blockSize.toUInt64 > windowSize) := by
    rw [hbs_eq1]; exact hwindow1
  -- Block 1: derive compressed block hypotheses
  have hblockEnd1' : ¬ data.size < afterHdr1 + hdr1.blockSize.toNat := by
    rw [hpos_eq1, hbs_eq1]; exact Nat.not_lt.mpr hblockEnd1
  rw [← hpos_eq1] at hlit1
  rw [← hpos_eq1, ← hbs_eq1] at hbbr1
  have hoff1 : ¬ data.size ≤ off := by omega
  have hadv1 : ¬ afterHdr1 + hdr1.blockSize.toNat ≤ off := by rw [hpos_eq1]; omega
  -- off2 = afterHdr1 + blockSize1, substitute
  have : off2 = afterHdr1 + hdr1.blockSize.toNat := by rw [hoff2, hpos_eq1, hbs_eq1]
  subst this
  -- Step through block 1
  rw [decompressBlocksWF_compressed_sequences_step data off windowSize output prevHuff
    prevFse history hdr1 afterHdr1 literals1 afterLiterals1 huffTree1 numSeq1 modes1
    afterSeqHeader1 llTable1 ofTable1 mlTable1 afterTables1 bbr1 sequences1 blockOutput1
    newHist1 hoff1 hparse1 hbs1 hws1 htype1 hblockEnd1' hlit1 hseq1 hNumSeq1 hfse1 hbbr1
    hdec1 hexec1 hnotlast1 hadv1]
  -- rw introduces dependent match huffTree1, hlit1; case split to reduce both it
  -- and the if-let in hlit2 to the same concrete form
  cases huffTree1 <;> exact decompressBlocksWF_succeeds_single_compressed_zero_seq data _
    windowSize (output ++ blockOutput1) _ _ newHist1 literals2 afterLiterals2 huffTree2 modes2
    afterSeqHeader2 hsize2 htypeVal2 hlastBit2 hblockSize2 hwindow2 hblockEnd2 hlit2 hseq2

/-- When a non-last compressed block with numSeq > 0 at `off` is followed by a last
    compressed block with numSeq > 0 at `off2`, `decompressBlocksWF` succeeds. Composes
    `decompressBlocksWF_compressed_sequences_step` with
    `decompressBlocksWF_succeeds_single_compressed_sequences` using only byte-level
    header preconditions. Block 2 uses the updated Huffman table, replaced FSE tables,
    and updated offset history from block 1. This is the most complex two-block
    combination: both blocks require the full sequence pipeline. -/
theorem decompressBlocksWF_succeeds_compressed_sequences_then_compressed_sequences
    (data : ByteArray)
    (off off2 : Nat) (windowSize : UInt64) (output : ByteArray)
    (prevHuff : Option Zip.Native.ZstdHuffmanTable)
    (prevFse : Zip.Native.PrevFseTables) (history : Array Nat)
    -- Block 1 (non-last compressed, numSeq > 0) parsed results
    (literals1 : ByteArray) (afterLiterals1 : Nat)
    (huffTree1 : Option Zip.Native.ZstdHuffmanTable)
    (numSeq1 : Nat) (modes1 : Zip.Native.SequenceCompressionModes) (afterSeqHeader1 : Nat)
    (llTable1 ofTable1 mlTable1 : Zip.Native.FseTable) (afterTables1 : Nat)
    (bbr1 : Zip.Native.BackwardBitReader)
    (sequences1 : Array Zip.Native.ZstdSequence)
    (blockOutput1 : ByteArray) (newHist1 : Array Nat)
    -- Block 2 (last compressed, numSeq > 0) parsed results
    (literals2 : ByteArray) (afterLiterals2 : Nat)
    (huffTree2 : Option Zip.Native.ZstdHuffmanTable)
    (numSeq2 : Nat) (modes2 : Zip.Native.SequenceCompressionModes) (afterSeqHeader2 : Nat)
    (llTable2 ofTable2 mlTable2 : Zip.Native.FseTable) (afterTables2 : Nat)
    (bbr2 : Zip.Native.BackwardBitReader)
    (sequences2 : Array Zip.Native.ZstdSequence)
    (blockOutput2 : ByteArray) (newHist2 : Array Nat)
    -- Block 1 byte-level header conditions at off
    (hsize1 : data.size ≥ off + 3)
    (htypeVal1 : ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
        ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 2)
    (hlastBit1 : (data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
        ||| (data[off + 2]!.toUInt32 <<< 16)) &&& 1 = 0)
    (hblockSize1 : ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
        ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow1 : ¬ (windowSize > 0 &&
        ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
          ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > windowSize))
    (hblockEnd1 : data.size ≥ off + 3 +
        (((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
          ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    -- Block 1 pipeline hypotheses
    (hlit1 : Zip.Native.parseLiteralsSection data (off + 3) prevHuff
              = .ok (literals1, afterLiterals1, huffTree1))
    (hseq1 : Zip.Native.parseSequencesHeader data afterLiterals1
              = .ok (numSeq1, modes1, afterSeqHeader1))
    (hNumSeq1 : ¬ numSeq1 == 0)
    (hfse1 : Zip.Native.resolveSequenceFseTables modes1 data afterSeqHeader1 prevFse
              = .ok (llTable1, ofTable1, mlTable1, afterTables1))
    (hbbr1 : Zip.Native.BackwardBitReader.init data afterTables1
              (off + 3 + (((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
                ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
              = .ok bbr1)
    (hdec1 : Zip.Native.decodeSequences llTable1 ofTable1 mlTable1 bbr1 numSeq1
              = .ok sequences1)
    (hexec1 : Zip.Native.executeSequences sequences1 literals1
               (if windowSize > 0 && output.size > windowSize.toNat
                then output.extract (output.size - windowSize.toNat) output.size
                else output)
               history windowSize.toNat
               = .ok (blockOutput1, newHist1))
    -- off2 = position after block 1's payload
    (hoff2 : off2 = off + 3 + (((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
          ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    -- Block 2 byte-level header conditions at off2
    (hsize2 : data.size ≥ off2 + 3)
    (htypeVal2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 2)
    (hlastBit2 : (data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) &&& 1 = 1)
    (hblockSize2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow2 : ¬ (windowSize > 0 &&
        ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
          ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > windowSize))
    (hblockEnd2 : data.size ≥ off2 + 3 +
        (((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
          ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    -- Block 2 pipeline hypotheses
    (hlit2 : Zip.Native.parseLiteralsSection data (off2 + 3)
              (if let some ht := huffTree1 then some ht else prevHuff)
              = .ok (literals2, afterLiterals2, huffTree2))
    (hseq2 : Zip.Native.parseSequencesHeader data afterLiterals2
              = .ok (numSeq2, modes2, afterSeqHeader2))
    (hNumSeq2 : ¬ numSeq2 == 0)
    (hfse2 : Zip.Native.resolveSequenceFseTables modes2 data afterSeqHeader2
              { litLen := some llTable1, offset := some ofTable1, matchLen := some mlTable1 }
              = .ok (llTable2, ofTable2, mlTable2, afterTables2))
    (hbbr2 : Zip.Native.BackwardBitReader.init data afterTables2
              (off2 + 3 + (((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
                ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
              = .ok bbr2)
    (hdec2 : Zip.Native.decodeSequences llTable2 ofTable2 mlTable2 bbr2 numSeq2
              = .ok sequences2)
    (hexec2 : Zip.Native.executeSequences sequences2 literals2
               (if windowSize > 0 && (output ++ blockOutput1).size > windowSize.toNat
                then (output ++ blockOutput1).extract
                  ((output ++ blockOutput1).size - windowSize.toNat)
                  (output ++ blockOutput1).size
                else output ++ blockOutput1)
               newHist1 windowSize.toNat
               = .ok (blockOutput2, newHist2)) :
    ∃ result pos',
      Zip.Native.decompressBlocksWF data off windowSize output prevHuff prevFse history
        = .ok (result, pos') := by
  -- Block 1: parseBlockHeader succeeds (typeVal=2 ≠ 3)
  have htypeNe3 : ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
      ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 ≠ 3 := by
    rw [htypeVal1]; decide
  obtain ⟨hdr1, afterHdr1, hparse1⟩ := parseBlockHeader_succeeds data off hsize1 htypeNe3
  have htype1 := (parseBlockHeader_blockType_eq data off hdr1 afterHdr1 hparse1).2.2 htypeVal1
  have hbs_eq1 := parseBlockHeader_blockSize_eq data off hdr1 afterHdr1 hparse1
  have hpos_eq1 := parseBlockHeader_pos_eq data off hdr1 afterHdr1 hparse1
  have hnotlast1 : hdr1.lastBlock = false := by
    rw [parseBlockHeader_lastBlock_eq data off hdr1 afterHdr1 hparse1, hlastBit1]; decide
  have hbs1 : ¬ hdr1.blockSize > 131072 := by rw [hbs_eq1]; exact Nat.not_lt.mpr hblockSize1
  have hws1 : ¬ (windowSize > 0 && hdr1.blockSize.toUInt64 > windowSize) := by
    rw [hbs_eq1]; exact hwindow1
  -- Block 1: derive compressed block hypotheses
  have hblockEnd1' : ¬ data.size < afterHdr1 + hdr1.blockSize.toNat := by
    rw [hpos_eq1, hbs_eq1]; exact Nat.not_lt.mpr hblockEnd1
  rw [← hpos_eq1] at hlit1
  rw [← hpos_eq1, ← hbs_eq1] at hbbr1
  have hoff1 : ¬ data.size ≤ off := by omega
  have hadv1 : ¬ afterHdr1 + hdr1.blockSize.toNat ≤ off := by rw [hpos_eq1]; omega
  -- off2 = afterHdr1 + blockSize1, substitute
  have : off2 = afterHdr1 + hdr1.blockSize.toNat := by rw [hoff2, hpos_eq1, hbs_eq1]
  subst this
  -- Step through block 1
  rw [decompressBlocksWF_compressed_sequences_step data off windowSize output prevHuff
    prevFse history hdr1 afterHdr1 literals1 afterLiterals1 huffTree1 numSeq1 modes1
    afterSeqHeader1 llTable1 ofTable1 mlTable1 afterTables1 bbr1 sequences1 blockOutput1
    newHist1 hoff1 hparse1 hbs1 hws1 htype1 hblockEnd1' hlit1 hseq1 hNumSeq1 hfse1 hbbr1
    hdec1 hexec1 hnotlast1 hadv1]
  -- Normalize: rw introduces dependent match huffTree1, hlit1 which is propositionally
  -- rw introduces dependent match huffTree1, hlit1; case split to reduce both it
  -- and the if-let in hlit2 to the same concrete form
  cases huffTree1 <;> exact decompressBlocksWF_succeeds_single_compressed_sequences data _
    windowSize (output ++ blockOutput1) _ _ newHist1 literals2 afterLiterals2 huffTree2 numSeq2
    modes2 afterSeqHeader2 llTable2 ofTable2 mlTable2 afterTables2 bbr2 sequences2 blockOutput2
    newHist2 hsize2 htypeVal2 hlastBit2 hblockSize2 hwindow2 hblockEnd2 hlit2 hseq2 hNumSeq2
    hfse2 hbbr2 hdec2 hexec2

/-! ## decompressFrame composed completeness for compressed blocks -/

/-- When a frame contains a single compressed last block with zero sequences
    (literals only), with no dictionary, no content checksum, and no declared
    content size, `decompressFrame` succeeds. This composes
    `decompressBlocksWF_succeeds_single_compressed_zero_seq` with the frame-level
    dictionary/checksum/size guards. -/
theorem decompressFrame_succeeds_single_compressed_zero_seq (data : ByteArray) (pos : Nat)
    (header : Zip.Native.ZstdFrameHeader) (afterHeader : Nat)
    (literals : ByteArray) (afterLiterals : Nat)
    (huffTree : Option Zip.Native.ZstdHuffmanTable)
    (modes : Zip.Native.SequenceCompressionModes) (afterSeqHeader : Nat)
    (hparse : Zip.Native.parseFrameHeader data pos = .ok (header, afterHeader))
    (hnodict : header.dictionaryId = none)
    (hnocksum : header.contentChecksum = false)
    (hnosize : header.contentSize = none)
    (hsize : data.size ≥ afterHeader + 3)
    (htypeVal : ((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
        ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 2)
    (hlastBit : (data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
        ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) &&& 1 = 1)
    (hblockSize : ((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
        ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow : ¬ (header.windowSize > 0 &&
        ((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
          ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > header.windowSize))
    (hblockEnd : data.size ≥ afterHeader + 3 +
        (((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
          ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    (hlit : Zip.Native.parseLiteralsSection data (afterHeader + 3) none
              = .ok (literals, afterLiterals, huffTree))
    (hseq : Zip.Native.parseSequencesHeader data afterLiterals
              = .ok (0, modes, afterSeqHeader)) :
    ∃ content pos',
      Zip.Native.decompressFrame data pos = .ok (content, pos') := by
  -- Step 1: Get block-level success from byte-level conditions
  obtain ⟨result, blockPos, hblocks⟩ := decompressBlocksWF_succeeds_single_compressed_zero_seq
    data afterHeader header.windowSize ByteArray.empty none {} #[1, 4, 8]
    literals afterLiterals huffTree modes afterSeqHeader
    hsize htypeVal hlastBit hblockSize hwindow hblockEnd hlit hseq
  -- Step 2: Unfold decompressFrame and thread through
  unfold Zip.Native.decompressFrame
  simp only [bind, Except.bind, pure, Except.pure, hparse]
  -- Step 3: Dictionary check — header.dictionaryId = none, so if-let doesn't match
  simp only [hnodict]
  -- Step 4: Block decompression succeeds
  unfold Zip.Native.decompressBlocks
  rw [hblocks]
  -- Step 5: Checksum is false, content size is none — both guards are trivial
  simp only [hnocksum, hnosize, Bool.false_eq_true, ↓reduceIte]
  exact ⟨_, _, rfl⟩

/-- When a frame contains a single compressed last block with sequences
    (numSeq > 0), with no dictionary, no content checksum, and no declared
    content size, `decompressFrame` succeeds. This composes
    `decompressBlocksWF_succeeds_single_compressed_sequences` with the frame-level
    dictionary/checksum/size guards. -/
theorem decompressFrame_succeeds_single_compressed_sequences (data : ByteArray) (pos : Nat)
    (header : Zip.Native.ZstdFrameHeader) (afterHeader : Nat)
    (literals : ByteArray) (afterLiterals : Nat)
    (huffTree : Option Zip.Native.ZstdHuffmanTable)
    (numSeq : Nat) (modes : Zip.Native.SequenceCompressionModes) (afterSeqHeader : Nat)
    (llTable ofTable mlTable : Zip.Native.FseTable) (afterTables : Nat)
    (bbr : Zip.Native.BackwardBitReader)
    (sequences : Array Zip.Native.ZstdSequence)
    (blockOutput : ByteArray) (newHist : Array Nat)
    (hparse : Zip.Native.parseFrameHeader data pos = .ok (header, afterHeader))
    (hnodict : header.dictionaryId = none)
    (hnocksum : header.contentChecksum = false)
    (hnosize : header.contentSize = none)
    (hsize : data.size ≥ afterHeader + 3)
    (htypeVal : ((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
        ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 2)
    (hlastBit : (data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
        ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) &&& 1 = 1)
    (hblockSize : ((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
        ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow : ¬ (header.windowSize > 0 &&
        ((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
          ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > header.windowSize))
    (hblockEnd : data.size ≥ afterHeader + 3 +
        (((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
          ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    (hlit : Zip.Native.parseLiteralsSection data (afterHeader + 3) none
              = .ok (literals, afterLiterals, huffTree))
    (hseq : Zip.Native.parseSequencesHeader data afterLiterals
              = .ok (numSeq, modes, afterSeqHeader))
    (hNumSeq : ¬ numSeq == 0)
    (hfse : Zip.Native.resolveSequenceFseTables modes data afterSeqHeader {}
              = .ok (llTable, ofTable, mlTable, afterTables))
    (hbbr : Zip.Native.BackwardBitReader.init data afterTables
              (afterHeader + 3 + (((data[afterHeader]!.toUInt32
                ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
                ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
              = .ok bbr)
    (hdec : Zip.Native.decodeSequences llTable ofTable mlTable bbr numSeq
              = .ok sequences)
    (hexec : Zip.Native.executeSequences sequences literals ByteArray.empty #[1, 4, 8]
               header.windowSize.toNat
               = .ok (blockOutput, newHist)) :
    ∃ content pos',
      Zip.Native.decompressFrame data pos = .ok (content, pos') := by
  -- Step 0: Convert hexec to match block-level form (if-guard simplifies for empty output)
  have hexec' : Zip.Native.executeSequences sequences literals
      (if header.windowSize > 0 && ByteArray.empty.size > header.windowSize.toNat
       then ByteArray.empty.extract (ByteArray.empty.size - header.windowSize.toNat)
         ByteArray.empty.size
       else ByteArray.empty)
      #[1, 4, 8] header.windowSize.toNat = .ok (blockOutput, newHist) := by
    simp only [ByteArray.size_empty, Nat.not_lt_zero, decide_false, Bool.and_false,
      Bool.false_eq_true, ↓reduceIte]; exact hexec
  -- Step 1: Get block-level success from byte-level conditions
  obtain ⟨result, blockPos, hblocks⟩ := decompressBlocksWF_succeeds_single_compressed_sequences
    data afterHeader header.windowSize ByteArray.empty none {} #[1, 4, 8]
    literals afterLiterals huffTree numSeq modes afterSeqHeader
    llTable ofTable mlTable afterTables bbr sequences blockOutput newHist
    hsize htypeVal hlastBit hblockSize hwindow hblockEnd hlit hseq hNumSeq hfse hbbr hdec hexec'
  -- Step 2: Unfold decompressFrame and thread through
  unfold Zip.Native.decompressFrame
  simp only [bind, Except.bind, pure, Except.pure, hparse]
  -- Step 3: Dictionary check — header.dictionaryId = none, so if-let doesn't match
  simp only [hnodict]
  -- Step 4: Block decompression succeeds
  unfold Zip.Native.decompressBlocks
  rw [hblocks]
  -- Step 5: Checksum is false, content size is none — both guards are trivial
  simp only [hnocksum, hnosize, Bool.false_eq_true, ↓reduceIte]
  exact ⟨_, _, rfl⟩

/-! ## decompressFrame two-block "succeeds" (raw/RLE + compressed zero-seq) -/

/-- When a frame contains a non-last raw block followed by a last compressed block
    with numSeq=0 (literals only), with no dictionary, no content checksum, and no
    declared content size, `decompressFrame` succeeds. Composes `parseFrameHeader`
    success with `decompressBlocksWF_succeeds_raw_then_compressed_zero_seq` and
    threads through the frame-level dictionary/checksum/size guards. -/
theorem decompressFrame_succeeds_raw_then_compressed_zero_seq (data : ByteArray) (pos : Nat)
    (header : Zip.Native.ZstdFrameHeader) (afterHeader : Nat)
    (literals : ByteArray) (afterLiterals : Nat)
    (huffTree : Option Zip.Native.ZstdHuffmanTable)
    (modes : Zip.Native.SequenceCompressionModes) (afterSeqHeader : Nat)
    (hparse : Zip.Native.parseFrameHeader data pos = .ok (header, afterHeader))
    (hnodict : header.dictionaryId = none)
    (hnocksum : header.contentChecksum = false)
    (hnosize : header.contentSize = none)
    -- Block 1 (non-last raw) at afterHeader
    (hsize1 : data.size ≥ afterHeader + 3)
    (htypeVal1 : ((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
        ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 0)
    (hlastBit1 : (data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
        ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) &&& 1 = 0)
    (hblockSize1 : ((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
        ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow1 : ¬ (header.windowSize > 0 &&
        ((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
          ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > header.windowSize))
    (hpayload1 : data.size ≥ afterHeader + 3 +
        (((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
          ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    -- Block 2 (last compressed, zero sequences) at off2
    (off2 : Nat)
    (hoff2 : off2 = afterHeader + 3 + (((data[afterHeader]!.toUInt32
          ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
          ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    (hsize2 : data.size ≥ off2 + 3)
    (htypeVal2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 2)
    (hlastBit2 : (data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) &&& 1 = 1)
    (hblockSize2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow2 : ¬ (header.windowSize > 0 &&
        ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
          ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > header.windowSize))
    (hblockEnd2 : data.size ≥ off2 + 3 +
        (((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
          ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    (hlit2 : Zip.Native.parseLiteralsSection data (off2 + 3) none
              = .ok (literals, afterLiterals, huffTree))
    (hseq2 : Zip.Native.parseSequencesHeader data afterLiterals
              = .ok (0, modes, afterSeqHeader)) :
    ∃ content pos',
      Zip.Native.decompressFrame data pos = .ok (content, pos') := by
  -- Step 1: Get block-level success from byte-level conditions
  obtain ⟨result, blockPos, hblocks⟩ := decompressBlocksWF_succeeds_raw_then_compressed_zero_seq
    data afterHeader off2 header.windowSize ByteArray.empty none {} #[1, 4, 8]
    literals afterLiterals huffTree modes afterSeqHeader
    hsize1 htypeVal1 hlastBit1 hblockSize1 hwindow1 hpayload1 hoff2
    hsize2 htypeVal2 hlastBit2 hblockSize2 hwindow2 hblockEnd2 hlit2 hseq2
  -- Step 2: Unfold decompressFrame and thread through
  unfold Zip.Native.decompressFrame
  simp only [bind, Except.bind, pure, Except.pure, hparse]
  -- Step 3: Dictionary check — header.dictionaryId = none, so if-let doesn't match
  simp only [hnodict]
  -- Step 4: Block decompression succeeds
  unfold Zip.Native.decompressBlocks
  rw [hblocks]
  -- Step 5: Checksum is false, content size is none — both guards are trivial
  simp only [hnocksum, hnosize, Bool.false_eq_true, ↓reduceIte]
  exact ⟨_, _, rfl⟩

/-- When a frame contains a non-last RLE block followed by a last compressed block
    with numSeq=0 (literals only), with no dictionary, no content checksum, and no
    declared content size, `decompressFrame` succeeds. Composes `parseFrameHeader`
    success with `decompressBlocksWF_succeeds_rle_then_compressed_zero_seq` and
    threads through the frame-level dictionary/checksum/size guards. -/
theorem decompressFrame_succeeds_rle_then_compressed_zero_seq (data : ByteArray) (pos : Nat)
    (header : Zip.Native.ZstdFrameHeader) (afterHeader : Nat)
    (literals : ByteArray) (afterLiterals : Nat)
    (huffTree : Option Zip.Native.ZstdHuffmanTable)
    (modes : Zip.Native.SequenceCompressionModes) (afterSeqHeader : Nat)
    (hparse : Zip.Native.parseFrameHeader data pos = .ok (header, afterHeader))
    (hnodict : header.dictionaryId = none)
    (hnocksum : header.contentChecksum = false)
    (hnosize : header.contentSize = none)
    -- Block 1 (non-last RLE) at afterHeader
    (hsize1 : data.size ≥ afterHeader + 3)
    (htypeVal1 : ((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
        ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 1)
    (hlastBit1 : (data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
        ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) &&& 1 = 0)
    (hblockSize1 : ((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
        ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow1 : ¬ (header.windowSize > 0 &&
        ((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
          ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > header.windowSize))
    (hpayload1 : data.size ≥ afterHeader + 4)
    -- Block 2 (last compressed, zero sequences) at off2
    (off2 : Nat)
    (hoff2 : off2 = afterHeader + 4)
    (hsize2 : data.size ≥ off2 + 3)
    (htypeVal2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 2)
    (hlastBit2 : (data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) &&& 1 = 1)
    (hblockSize2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow2 : ¬ (header.windowSize > 0 &&
        ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
          ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > header.windowSize))
    (hblockEnd2 : data.size ≥ off2 + 3 +
        (((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
          ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    (hlit2 : Zip.Native.parseLiteralsSection data (off2 + 3) none
              = .ok (literals, afterLiterals, huffTree))
    (hseq2 : Zip.Native.parseSequencesHeader data afterLiterals
              = .ok (0, modes, afterSeqHeader)) :
    ∃ content pos',
      Zip.Native.decompressFrame data pos = .ok (content, pos') := by
  -- Step 1: Get block-level success from byte-level conditions
  obtain ⟨result, blockPos, hblocks⟩ := decompressBlocksWF_succeeds_rle_then_compressed_zero_seq
    data afterHeader off2 header.windowSize ByteArray.empty none {} #[1, 4, 8]
    literals afterLiterals huffTree modes afterSeqHeader
    hsize1 htypeVal1 hlastBit1 hblockSize1 hwindow1 hpayload1 hoff2
    hsize2 htypeVal2 hlastBit2 hblockSize2 hwindow2 hblockEnd2 hlit2 hseq2
  -- Step 2: Unfold decompressFrame and thread through
  unfold Zip.Native.decompressFrame
  simp only [bind, Except.bind, pure, Except.pure, hparse]
  -- Step 3: Dictionary check — header.dictionaryId = none, so if-let doesn't match
  simp only [hnodict]
  -- Step 4: Block decompression succeeds
  unfold Zip.Native.decompressBlocks
  rw [hblocks]
  -- Step 5: Checksum is false, content size is none — both guards are trivial
  simp only [hnocksum, hnosize, Bool.false_eq_true, ↓reduceIte]
  exact ⟨_, _, rfl⟩

/-! ## decompressFrame two-block "succeeds" (compressed zero-seq + raw/RLE) -/

/-- When a frame contains a non-last compressed block with numSeq=0 (literals only)
    followed by a last raw block, with no dictionary, no content checksum, and no
    declared content size, `decompressFrame` succeeds. Composes `parseFrameHeader`
    success with `decompressBlocksWF_succeeds_compressed_zero_seq_then_raw` and
    threads through the frame-level dictionary/checksum/size guards. -/
theorem decompressFrame_succeeds_compressed_zero_seq_then_raw (data : ByteArray) (pos : Nat)
    (header : Zip.Native.ZstdFrameHeader) (afterHeader : Nat)
    (literals : ByteArray) (afterLiterals : Nat)
    (huffTree : Option Zip.Native.ZstdHuffmanTable)
    (modes : Zip.Native.SequenceCompressionModes) (afterSeqHeader : Nat)
    (hparse : Zip.Native.parseFrameHeader data pos = .ok (header, afterHeader))
    (hnodict : header.dictionaryId = none)
    (hnocksum : header.contentChecksum = false)
    (hnosize : header.contentSize = none)
    -- Block 1 (non-last compressed, zero sequences) at afterHeader
    (hsize1 : data.size ≥ afterHeader + 3)
    (htypeVal1 : ((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
        ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 2)
    (hlastBit1 : (data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
        ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) &&& 1 = 0)
    (hblockSize1 : ((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
        ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow1 : ¬ (header.windowSize > 0 &&
        ((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
          ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > header.windowSize))
    (hblockEnd1 : data.size ≥ afterHeader + 3 +
        (((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
          ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    (hlit1 : Zip.Native.parseLiteralsSection data (afterHeader + 3) none
              = .ok (literals, afterLiterals, huffTree))
    (hseq1 : Zip.Native.parseSequencesHeader data afterLiterals
              = .ok (0, modes, afterSeqHeader))
    -- Block 2 (last raw) at off2
    (off2 : Nat)
    (hoff2 : off2 = afterHeader + 3 + (((data[afterHeader]!.toUInt32
          ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
          ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    (hsize2 : data.size ≥ off2 + 3)
    (htypeVal2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 0)
    (hlastBit2 : (data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) &&& 1 = 1)
    (hblockSize2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow2 : ¬ (header.windowSize > 0 &&
        ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
          ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > header.windowSize))
    (hpayload2 : data.size ≥ off2 + 3 +
        (((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
          ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toNat)) :
    ∃ content pos',
      Zip.Native.decompressFrame data pos = .ok (content, pos') := by
  -- Step 1: Get block-level success from byte-level conditions
  obtain ⟨result, blockPos, hblocks⟩ := decompressBlocksWF_succeeds_compressed_zero_seq_then_raw
    data afterHeader off2 header.windowSize ByteArray.empty none {} #[1, 4, 8]
    literals afterLiterals huffTree modes afterSeqHeader
    hsize1 htypeVal1 hlastBit1 hblockSize1 hwindow1 hblockEnd1 hlit1 hseq1 hoff2
    hsize2 htypeVal2 hlastBit2 hblockSize2 hwindow2 hpayload2
  -- Step 2: Unfold decompressFrame and thread through
  unfold Zip.Native.decompressFrame
  simp only [bind, Except.bind, pure, Except.pure, hparse]
  -- Step 3: Dictionary check — header.dictionaryId = none, so if-let doesn't match
  simp only [hnodict]
  -- Step 4: Block decompression succeeds
  unfold Zip.Native.decompressBlocks
  rw [hblocks]
  -- Step 5: Checksum is false, content size is none — both guards are trivial
  simp only [hnocksum, hnosize, Bool.false_eq_true, ↓reduceIte]
  exact ⟨_, _, rfl⟩

/-- When a frame contains a non-last compressed block with numSeq=0 (literals only)
    followed by a last RLE block, with no dictionary, no content checksum, and no
    declared content size, `decompressFrame` succeeds. Composes `parseFrameHeader`
    success with `decompressBlocksWF_succeeds_compressed_zero_seq_then_rle` and
    threads through the frame-level dictionary/checksum/size guards. -/
theorem decompressFrame_succeeds_compressed_zero_seq_then_rle (data : ByteArray) (pos : Nat)
    (header : Zip.Native.ZstdFrameHeader) (afterHeader : Nat)
    (literals : ByteArray) (afterLiterals : Nat)
    (huffTree : Option Zip.Native.ZstdHuffmanTable)
    (modes : Zip.Native.SequenceCompressionModes) (afterSeqHeader : Nat)
    (hparse : Zip.Native.parseFrameHeader data pos = .ok (header, afterHeader))
    (hnodict : header.dictionaryId = none)
    (hnocksum : header.contentChecksum = false)
    (hnosize : header.contentSize = none)
    -- Block 1 (non-last compressed, zero sequences) at afterHeader
    (hsize1 : data.size ≥ afterHeader + 3)
    (htypeVal1 : ((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
        ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 2)
    (hlastBit1 : (data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
        ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) &&& 1 = 0)
    (hblockSize1 : ((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
        ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow1 : ¬ (header.windowSize > 0 &&
        ((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
          ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > header.windowSize))
    (hblockEnd1 : data.size ≥ afterHeader + 3 +
        (((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
          ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    (hlit1 : Zip.Native.parseLiteralsSection data (afterHeader + 3) none
              = .ok (literals, afterLiterals, huffTree))
    (hseq1 : Zip.Native.parseSequencesHeader data afterLiterals
              = .ok (0, modes, afterSeqHeader))
    -- Block 2 (last RLE) at off2
    (off2 : Nat)
    (hoff2 : off2 = afterHeader + 3 + (((data[afterHeader]!.toUInt32
          ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
          ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    (hsize2 : data.size ≥ off2 + 3)
    (htypeVal2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 1)
    (hlastBit2 : (data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) &&& 1 = 1)
    (hblockSize2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow2 : ¬ (header.windowSize > 0 &&
        ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
          ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > header.windowSize))
    (hpayload2 : data.size ≥ off2 + 4) :
    ∃ content pos',
      Zip.Native.decompressFrame data pos = .ok (content, pos') := by
  -- Step 1: Get block-level success from byte-level conditions
  obtain ⟨result, blockPos, hblocks⟩ := decompressBlocksWF_succeeds_compressed_zero_seq_then_rle
    data afterHeader off2 header.windowSize ByteArray.empty none {} #[1, 4, 8]
    literals afterLiterals huffTree modes afterSeqHeader
    hsize1 htypeVal1 hlastBit1 hblockSize1 hwindow1 hblockEnd1 hlit1 hseq1 hoff2
    hsize2 htypeVal2 hlastBit2 hblockSize2 hwindow2 hpayload2
  -- Step 2: Unfold decompressFrame and thread through
  unfold Zip.Native.decompressFrame
  simp only [bind, Except.bind, pure, Except.pure, hparse]
  -- Step 3: Dictionary check — header.dictionaryId = none, so if-let doesn't match
  simp only [hnodict]
  -- Step 4: Block decompression succeeds
  unfold Zip.Native.decompressBlocks
  rw [hblocks]
  -- Step 5: Checksum is false, content size is none — both guards are trivial
  simp only [hnocksum, hnosize, Bool.false_eq_true, ↓reduceIte]
  exact ⟨_, _, rfl⟩

/-! ## decompressFrame two-block "succeeds" (compressed sequences + raw/RLE) -/

/-- When a frame contains a non-last compressed block with numSeq > 0 (full sequence
    pipeline) followed by a last raw block, with no dictionary, no content checksum,
    and no declared content size, `decompressFrame` succeeds. Composes
    `parseFrameHeader` success with
    `decompressBlocksWF_succeeds_compressed_sequences_then_raw` and threads through
    the frame-level dictionary/checksum/size guards. -/
theorem decompressFrame_succeeds_compressed_sequences_then_raw (data : ByteArray) (pos : Nat)
    (header : Zip.Native.ZstdFrameHeader) (afterHeader : Nat)
    (literals : ByteArray) (afterLiterals : Nat)
    (huffTree : Option Zip.Native.ZstdHuffmanTable)
    (numSeq : Nat) (modes : Zip.Native.SequenceCompressionModes) (afterSeqHeader : Nat)
    (llTable ofTable mlTable : Zip.Native.FseTable) (afterTables : Nat)
    (bbr : Zip.Native.BackwardBitReader)
    (sequences : Array Zip.Native.ZstdSequence)
    (blockOutput1 : ByteArray) (newHist1 : Array Nat)
    (hparse : Zip.Native.parseFrameHeader data pos = .ok (header, afterHeader))
    (hnodict : header.dictionaryId = none)
    (hnocksum : header.contentChecksum = false)
    (hnosize : header.contentSize = none)
    -- Block 1 (non-last compressed, numSeq > 0) at afterHeader
    (hsize1 : data.size ≥ afterHeader + 3)
    (htypeVal1 : ((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
        ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 2)
    (hlastBit1 : (data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
        ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) &&& 1 = 0)
    (hblockSize1 : ((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
        ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow1 : ¬ (header.windowSize > 0 &&
        ((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
          ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > header.windowSize))
    (hblockEnd1 : data.size ≥ afterHeader + 3 +
        (((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
          ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    (hlit1 : Zip.Native.parseLiteralsSection data (afterHeader + 3) none
              = .ok (literals, afterLiterals, huffTree))
    (hseq1 : Zip.Native.parseSequencesHeader data afterLiterals
              = .ok (numSeq, modes, afterSeqHeader))
    (hNumSeq1 : ¬ numSeq == 0)
    (hfse1 : Zip.Native.resolveSequenceFseTables modes data afterSeqHeader {}
              = .ok (llTable, ofTable, mlTable, afterTables))
    (hbbr1 : Zip.Native.BackwardBitReader.init data afterTables
              (afterHeader + 3 + (((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
                ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
              = .ok bbr)
    (hdec1 : Zip.Native.decodeSequences llTable ofTable mlTable bbr numSeq
              = .ok sequences)
    (hexec1 : Zip.Native.executeSequences sequences literals
               (if header.windowSize > 0 && ByteArray.empty.size > header.windowSize.toNat
                then ByteArray.empty.extract (ByteArray.empty.size - header.windowSize.toNat) ByteArray.empty.size
                else ByteArray.empty)
               #[1, 4, 8] header.windowSize.toNat
               = .ok (blockOutput1, newHist1))
    -- Block 2 (last raw) at off2
    (off2 : Nat)
    (hoff2 : off2 = afterHeader + 3 + (((data[afterHeader]!.toUInt32
          ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
          ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    (hsize2 : data.size ≥ off2 + 3)
    (htypeVal2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 0)
    (hlastBit2 : (data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) &&& 1 = 1)
    (hblockSize2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow2 : ¬ (header.windowSize > 0 &&
        ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
          ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > header.windowSize))
    (hpayload2 : data.size ≥ off2 + 3 +
        (((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
          ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toNat)) :
    ∃ content pos',
      Zip.Native.decompressFrame data pos = .ok (content, pos') := by
  -- Step 1: Get block-level success from byte-level conditions
  obtain ⟨result, blockPos, hblocks⟩ := decompressBlocksWF_succeeds_compressed_sequences_then_raw
    data afterHeader off2 header.windowSize ByteArray.empty none {} #[1, 4, 8]
    literals afterLiterals huffTree numSeq modes afterSeqHeader
    llTable ofTable mlTable afterTables bbr sequences blockOutput1 newHist1
    hsize1 htypeVal1 hlastBit1 hblockSize1 hwindow1 hblockEnd1 hlit1 hseq1 hNumSeq1
    hfse1 hbbr1 hdec1 hexec1 hoff2
    hsize2 htypeVal2 hlastBit2 hblockSize2 hwindow2 hpayload2
  -- Step 2: Unfold decompressFrame and thread through
  unfold Zip.Native.decompressFrame
  simp only [bind, Except.bind, pure, Except.pure, hparse]
  -- Step 3: Dictionary check — header.dictionaryId = none, so if-let doesn't match
  simp only [hnodict]
  -- Step 4: Block decompression succeeds
  unfold Zip.Native.decompressBlocks
  rw [hblocks]
  -- Step 5: Checksum is false, content size is none — both guards are trivial
  simp only [hnocksum, hnosize, Bool.false_eq_true, ↓reduceIte]
  exact ⟨_, _, rfl⟩

/-- When a frame contains a non-last compressed block with numSeq > 0 (full sequence
    pipeline) followed by a last RLE block, with no dictionary, no content checksum,
    and no declared content size, `decompressFrame` succeeds. Composes
    `parseFrameHeader` success with
    `decompressBlocksWF_succeeds_compressed_sequences_then_rle` and threads through
    the frame-level dictionary/checksum/size guards. -/
theorem decompressFrame_succeeds_compressed_sequences_then_rle (data : ByteArray) (pos : Nat)
    (header : Zip.Native.ZstdFrameHeader) (afterHeader : Nat)
    (literals : ByteArray) (afterLiterals : Nat)
    (huffTree : Option Zip.Native.ZstdHuffmanTable)
    (numSeq : Nat) (modes : Zip.Native.SequenceCompressionModes) (afterSeqHeader : Nat)
    (llTable ofTable mlTable : Zip.Native.FseTable) (afterTables : Nat)
    (bbr : Zip.Native.BackwardBitReader)
    (sequences : Array Zip.Native.ZstdSequence)
    (blockOutput1 : ByteArray) (newHist1 : Array Nat)
    (hparse : Zip.Native.parseFrameHeader data pos = .ok (header, afterHeader))
    (hnodict : header.dictionaryId = none)
    (hnocksum : header.contentChecksum = false)
    (hnosize : header.contentSize = none)
    -- Block 1 (non-last compressed, numSeq > 0) at afterHeader
    (hsize1 : data.size ≥ afterHeader + 3)
    (htypeVal1 : ((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
        ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 2)
    (hlastBit1 : (data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
        ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) &&& 1 = 0)
    (hblockSize1 : ((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
        ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow1 : ¬ (header.windowSize > 0 &&
        ((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
          ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > header.windowSize))
    (hblockEnd1 : data.size ≥ afterHeader + 3 +
        (((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
          ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    (hlit1 : Zip.Native.parseLiteralsSection data (afterHeader + 3) none
              = .ok (literals, afterLiterals, huffTree))
    (hseq1 : Zip.Native.parseSequencesHeader data afterLiterals
              = .ok (numSeq, modes, afterSeqHeader))
    (hNumSeq1 : ¬ numSeq == 0)
    (hfse1 : Zip.Native.resolveSequenceFseTables modes data afterSeqHeader {}
              = .ok (llTable, ofTable, mlTable, afterTables))
    (hbbr1 : Zip.Native.BackwardBitReader.init data afterTables
              (afterHeader + 3 + (((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
                ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
              = .ok bbr)
    (hdec1 : Zip.Native.decodeSequences llTable ofTable mlTable bbr numSeq
              = .ok sequences)
    (hexec1 : Zip.Native.executeSequences sequences literals
               (if header.windowSize > 0 && ByteArray.empty.size > header.windowSize.toNat
                then ByteArray.empty.extract (ByteArray.empty.size - header.windowSize.toNat) ByteArray.empty.size
                else ByteArray.empty)
               #[1, 4, 8] header.windowSize.toNat
               = .ok (blockOutput1, newHist1))
    -- Block 2 (last RLE) at off2
    (off2 : Nat)
    (hoff2 : off2 = afterHeader + 3 + (((data[afterHeader]!.toUInt32
          ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
          ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    (hsize2 : data.size ≥ off2 + 3)
    (htypeVal2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 1)
    (hlastBit2 : (data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) &&& 1 = 1)
    (hblockSize2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow2 : ¬ (header.windowSize > 0 &&
        ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
          ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > header.windowSize))
    (hpayload2 : data.size ≥ off2 + 4) :
    ∃ content pos',
      Zip.Native.decompressFrame data pos = .ok (content, pos') := by
  -- Step 1: Get block-level success from byte-level conditions
  obtain ⟨result, blockPos, hblocks⟩ := decompressBlocksWF_succeeds_compressed_sequences_then_rle
    data afterHeader off2 header.windowSize ByteArray.empty none {} #[1, 4, 8]
    literals afterLiterals huffTree numSeq modes afterSeqHeader
    llTable ofTable mlTable afterTables bbr sequences blockOutput1 newHist1
    hsize1 htypeVal1 hlastBit1 hblockSize1 hwindow1 hblockEnd1 hlit1 hseq1 hNumSeq1
    hfse1 hbbr1 hdec1 hexec1 hoff2
    hsize2 htypeVal2 hlastBit2 hblockSize2 hwindow2 hpayload2
  -- Step 2: Unfold decompressFrame and thread through
  unfold Zip.Native.decompressFrame
  simp only [bind, Except.bind, pure, Except.pure, hparse]
  -- Step 3: Dictionary check — header.dictionaryId = none, so if-let doesn't match
  simp only [hnodict]
  -- Step 4: Block decompression succeeds
  unfold Zip.Native.decompressBlocks
  rw [hblocks]
  -- Step 5: Checksum is false, content size is none — both guards are trivial
  simp only [hnocksum, hnosize, Bool.false_eq_true, ↓reduceIte]
  exact ⟨_, _, rfl⟩

/-! ## decompressFrame two-block "succeeds" (compressed zero-seq + compressed) -/

/-- When a frame contains a non-last compressed block with numSeq=0 (literals only)
    followed by a last compressed block with numSeq=0 (literals only), with no dictionary,
    no content checksum, and no declared content size, `decompressFrame` succeeds.
    Composes `parseFrameHeader` success with
    `decompressBlocksWF_succeeds_compressed_zero_seq_then_compressed_zero_seq` and
    threads through the frame-level dictionary/checksum/size guards. -/
theorem decompressFrame_succeeds_compressed_zero_seq_then_compressed_zero_seq
    (data : ByteArray) (pos : Nat)
    (header : Zip.Native.ZstdFrameHeader) (afterHeader : Nat)
    (literals1 : ByteArray) (afterLiterals1 : Nat)
    (huffTree1 : Option Zip.Native.ZstdHuffmanTable)
    (modes1 : Zip.Native.SequenceCompressionModes) (afterSeqHeader1 : Nat)
    (literals2 : ByteArray) (afterLiterals2 : Nat)
    (huffTree2 : Option Zip.Native.ZstdHuffmanTable)
    (modes2 : Zip.Native.SequenceCompressionModes) (afterSeqHeader2 : Nat)
    (hparse : Zip.Native.parseFrameHeader data pos = .ok (header, afterHeader))
    (hnodict : header.dictionaryId = none)
    (hnocksum : header.contentChecksum = false)
    (hnosize : header.contentSize = none)
    -- Block 1 (non-last compressed, zero sequences) at afterHeader
    (hsize1 : data.size ≥ afterHeader + 3)
    (htypeVal1 : ((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
        ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 2)
    (hlastBit1 : (data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
        ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) &&& 1 = 0)
    (hblockSize1 : ((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
        ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow1 : ¬ (header.windowSize > 0 &&
        ((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
          ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > header.windowSize))
    (hblockEnd1 : data.size ≥ afterHeader + 3 +
        (((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
          ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    (hlit1 : Zip.Native.parseLiteralsSection data (afterHeader + 3) none
              = .ok (literals1, afterLiterals1, huffTree1))
    (hseq1 : Zip.Native.parseSequencesHeader data afterLiterals1
              = .ok (0, modes1, afterSeqHeader1))
    -- Block 2 (last compressed, zero sequences) at off2
    (off2 : Nat)
    (hoff2 : off2 = afterHeader + 3 + (((data[afterHeader]!.toUInt32
          ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
          ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    (hsize2 : data.size ≥ off2 + 3)
    (htypeVal2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 2)
    (hlastBit2 : (data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) &&& 1 = 1)
    (hblockSize2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow2 : ¬ (header.windowSize > 0 &&
        ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
          ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > header.windowSize))
    (hblockEnd2 : data.size ≥ off2 + 3 +
        (((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
          ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    (hlit2 : Zip.Native.parseLiteralsSection data (off2 + 3)
              (if let some ht := huffTree1 then some ht else none)
              = .ok (literals2, afterLiterals2, huffTree2))
    (hseq2 : Zip.Native.parseSequencesHeader data afterLiterals2
              = .ok (0, modes2, afterSeqHeader2)) :
    ∃ content pos',
      Zip.Native.decompressFrame data pos = .ok (content, pos') := by
  -- Case-split huffTree1 to reduce the if-let match in hlit2 and avoid dependent type mismatch
  cases huffTree1 <;> (
  obtain ⟨result, blockPos, hblocks⟩ :=
    decompressBlocksWF_succeeds_compressed_zero_seq_then_compressed_zero_seq
    data afterHeader off2 header.windowSize ByteArray.empty none {} #[1, 4, 8]
    literals1 afterLiterals1 _ modes1 afterSeqHeader1
    literals2 afterLiterals2 huffTree2 modes2 afterSeqHeader2
    hsize1 htypeVal1 hlastBit1 hblockSize1 hwindow1 hblockEnd1 hlit1 hseq1 hoff2
    hsize2 htypeVal2 hlastBit2 hblockSize2 hwindow2 hblockEnd2 hlit2 hseq2
  unfold Zip.Native.decompressFrame
  simp only [bind, Except.bind, pure, Except.pure, hparse, hnodict]
  unfold Zip.Native.decompressBlocks
  rw [hblocks]
  simp only [hnocksum, hnosize, Bool.false_eq_true, ↓reduceIte]
  exact ⟨_, _, rfl⟩)

/-- When a frame contains a non-last compressed block with numSeq=0 (literals only)
    followed by a last compressed block with numSeq > 0 (full sequence pipeline), with
    no dictionary, no content checksum, and no declared content size, `decompressFrame`
    succeeds. Composes `parseFrameHeader` success with
    `decompressBlocksWF_succeeds_compressed_zero_seq_then_compressed_sequences` and
    threads through the frame-level dictionary/checksum/size guards. -/
theorem decompressFrame_succeeds_compressed_zero_seq_then_compressed_sequences
    (data : ByteArray) (pos : Nat)
    (header : Zip.Native.ZstdFrameHeader) (afterHeader : Nat)
    (literals1 : ByteArray) (afterLiterals1 : Nat)
    (huffTree1 : Option Zip.Native.ZstdHuffmanTable)
    (modes1 : Zip.Native.SequenceCompressionModes) (afterSeqHeader1 : Nat)
    (literals2 : ByteArray) (afterLiterals2 : Nat)
    (huffTree2 : Option Zip.Native.ZstdHuffmanTable)
    (numSeq2 : Nat) (modes2 : Zip.Native.SequenceCompressionModes) (afterSeqHeader2 : Nat)
    (llTable2 ofTable2 mlTable2 : Zip.Native.FseTable) (afterTables2 : Nat)
    (bbr2 : Zip.Native.BackwardBitReader)
    (sequences2 : Array Zip.Native.ZstdSequence)
    (blockOutput2 : ByteArray) (newHist2 : Array Nat)
    (hparse : Zip.Native.parseFrameHeader data pos = .ok (header, afterHeader))
    (hnodict : header.dictionaryId = none)
    (hnocksum : header.contentChecksum = false)
    (hnosize : header.contentSize = none)
    -- Block 1 (non-last compressed, zero sequences) at afterHeader
    (hsize1 : data.size ≥ afterHeader + 3)
    (htypeVal1 : ((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
        ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 2)
    (hlastBit1 : (data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
        ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) &&& 1 = 0)
    (hblockSize1 : ((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
        ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow1 : ¬ (header.windowSize > 0 &&
        ((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
          ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > header.windowSize))
    (hblockEnd1 : data.size ≥ afterHeader + 3 +
        (((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
          ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    (hlit1 : Zip.Native.parseLiteralsSection data (afterHeader + 3) none
              = .ok (literals1, afterLiterals1, huffTree1))
    (hseq1 : Zip.Native.parseSequencesHeader data afterLiterals1
              = .ok (0, modes1, afterSeqHeader1))
    -- Block 2 (last compressed, with sequences) at off2
    (off2 : Nat)
    (hoff2 : off2 = afterHeader + 3 + (((data[afterHeader]!.toUInt32
          ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
          ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    (hsize2 : data.size ≥ off2 + 3)
    (htypeVal2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 2)
    (hlastBit2 : (data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) &&& 1 = 1)
    (hblockSize2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow2 : ¬ (header.windowSize > 0 &&
        ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
          ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > header.windowSize))
    (hblockEnd2 : data.size ≥ off2 + 3 +
        (((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
          ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    (hlit2 : Zip.Native.parseLiteralsSection data (off2 + 3)
              (if let some ht := huffTree1 then some ht else none)
              = .ok (literals2, afterLiterals2, huffTree2))
    (hseq2 : Zip.Native.parseSequencesHeader data afterLiterals2
              = .ok (numSeq2, modes2, afterSeqHeader2))
    (hNumSeq2 : ¬ numSeq2 == 0)
    (hfse2 : Zip.Native.resolveSequenceFseTables modes2 data afterSeqHeader2 {}
              = .ok (llTable2, ofTable2, mlTable2, afterTables2))
    (hbbr2 : Zip.Native.BackwardBitReader.init data afterTables2
              (off2 + 3 + (((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
                ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
              = .ok bbr2)
    (hdec2 : Zip.Native.decodeSequences llTable2 ofTable2 mlTable2 bbr2 numSeq2
              = .ok sequences2)
    (hexec2 : Zip.Native.executeSequences sequences2 literals2
               (if header.windowSize > 0 &&
                    (ByteArray.empty ++ literals1).size > header.windowSize.toNat
                then (ByteArray.empty ++ literals1).extract
                  ((ByteArray.empty ++ literals1).size - header.windowSize.toNat)
                  (ByteArray.empty ++ literals1).size
                else (ByteArray.empty ++ literals1))
               #[1, 4, 8] header.windowSize.toNat
               = .ok (blockOutput2, newHist2)) :
    ∃ content pos',
      Zip.Native.decompressFrame data pos = .ok (content, pos') := by
  -- Case-split huffTree1 to reduce the if-let match in hlit2 and avoid dependent type mismatch
  cases huffTree1 <;> (
  obtain ⟨result, blockPos, hblocks⟩ :=
    decompressBlocksWF_succeeds_compressed_zero_seq_then_compressed_sequences
    data afterHeader off2 header.windowSize ByteArray.empty none {} #[1, 4, 8]
    literals1 afterLiterals1 _ modes1 afterSeqHeader1
    literals2 afterLiterals2 huffTree2 numSeq2 modes2 afterSeqHeader2
    llTable2 ofTable2 mlTable2 afterTables2 bbr2 sequences2 blockOutput2 newHist2
    hsize1 htypeVal1 hlastBit1 hblockSize1 hwindow1 hblockEnd1 hlit1 hseq1 hoff2
    hsize2 htypeVal2 hlastBit2 hblockSize2 hwindow2 hblockEnd2 hlit2 hseq2 hNumSeq2
    hfse2 hbbr2 hdec2 hexec2
  unfold Zip.Native.decompressFrame
  simp only [bind, Except.bind, pure, Except.pure, hparse, hnodict]
  unfold Zip.Native.decompressBlocks
  rw [hblocks]
  simp only [hnocksum, hnosize, Bool.false_eq_true, ↓reduceIte]
  exact ⟨_, _, rfl⟩)

/-- When `decompressBlocksWF` encounters two consecutive compressed blocks with
    sequences (numSeq > 0), where the first is non-last and the second is last,
    the output is `output ++ blockOutput1 ++ blockOutput2` at the position after
    the second block. Block 2 receives the updated Huffman table, replaced FSE
    tables, updated offset history, and extended output from block 1.

    Composes `decompressBlocksWF_compressed_sequences_step` and
    `decompressBlocksWF_single_compressed_sequences`. -/
theorem decompressBlocksWF_two_compressed_sequences_blocks (data : ByteArray)
    (off : Nat) (windowSize : UInt64) (output : ByteArray)
    (prevHuff : Option Zip.Native.ZstdHuffmanTable)
    (prevFse : Zip.Native.PrevFseTables) (history : Array Nat)
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
    -- Block 1 hypotheses
    (hoff1 : ¬ data.size ≤ off)
    (hparse1 : Zip.Native.parseBlockHeader data off = .ok (hdr1, afterHdr1))
    (hbs1 : ¬ hdr1.blockSize > 131072)
    (hws1 : ¬ (windowSize > 0 && hdr1.blockSize.toUInt64 > windowSize))
    (htype1 : hdr1.blockType = .compressed)
    (hblockEnd1 : ¬ data.size < afterHdr1 + hdr1.blockSize.toNat)
    (hlit1 : Zip.Native.parseLiteralsSection data afterHdr1 prevHuff
               = .ok (literals1, afterLiterals1, huffTree1))
    (hseq1 : Zip.Native.parseSequencesHeader data afterLiterals1
               = .ok (numSeq1, modes1, afterSeqHeader1))
    (hNumSeq1 : ¬ numSeq1 == 0)
    (hfse1 : Zip.Native.resolveSequenceFseTables modes1 data afterSeqHeader1 prevFse
               = .ok (llTable1, ofTable1, mlTable1, afterTables1))
    (hbbr1 : Zip.Native.BackwardBitReader.init data afterTables1
               (afterHdr1 + hdr1.blockSize.toNat) = .ok bbr1)
    (hdec1 : Zip.Native.decodeSequences llTable1 ofTable1 mlTable1 bbr1 numSeq1
               = .ok sequences1)
    (hexec1 : Zip.Native.executeSequences sequences1 literals1
                (if windowSize > 0 && output.size > windowSize.toNat
                 then output.extract (output.size - windowSize.toNat) output.size
                 else output)
                history windowSize.toNat
                = .ok (blockOutput1, newHist1))
    (hnotlast1 : hdr1.lastBlock = false)
    (hadv1 : ¬ (afterHdr1 + hdr1.blockSize.toNat) ≤ off)
    -- Block 2 hypotheses
    (hoff2 : ¬ data.size ≤ afterHdr1 + hdr1.blockSize.toNat)
    (hparse2 : Zip.Native.parseBlockHeader data (afterHdr1 + hdr1.blockSize.toNat)
                 = .ok (hdr2, afterHdr2))
    (hbs2 : ¬ hdr2.blockSize > 131072)
    (hws2 : ¬ (windowSize > 0 && hdr2.blockSize.toUInt64 > windowSize))
    (htype2 : hdr2.blockType = .compressed)
    (hblockEnd2 : ¬ data.size < afterHdr2 + hdr2.blockSize.toNat)
    (hlit2 : Zip.Native.parseLiteralsSection data afterHdr2
               (if let some ht := huffTree1 then some ht else prevHuff)
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
                (if windowSize > 0 && (output ++ blockOutput1).size > windowSize.toNat
                 then (output ++ blockOutput1).extract
                   ((output ++ blockOutput1).size - windowSize.toNat)
                   (output ++ blockOutput1).size
                 else output ++ blockOutput1)
                newHist1 windowSize.toNat
                = .ok (blockOutput2, newHist2))
    (hlast2 : hdr2.lastBlock = true) :
    Zip.Native.decompressBlocksWF data off windowSize output prevHuff prevFse history
      = .ok (output ++ blockOutput1 ++ blockOutput2,
             afterHdr2 + hdr2.blockSize.toNat) := by
  rw [decompressBlocksWF_compressed_sequences_step data off windowSize output prevHuff
    prevFse history hdr1 afterHdr1 literals1 afterLiterals1 huffTree1 numSeq1 modes1
    afterSeqHeader1 llTable1 ofTable1 mlTable1 afterTables1 bbr1 sequences1 blockOutput1
    newHist1 hoff1 hparse1 hbs1 hws1 htype1 hblockEnd1 hlit1 hseq1 hNumSeq1 hfse1 hbbr1
    hdec1 hexec1 hnotlast1 hadv1]
  exact decompressBlocksWF_single_compressed_sequences data
    (afterHdr1 + hdr1.blockSize.toNat) windowSize (output ++ blockOutput1) _
    { litLen := some llTable1, offset := some ofTable1, matchLen := some mlTable1 }
    newHist1
    hdr2 afterHdr2 literals2 afterLiterals2 huffTree2 numSeq2 modes2 afterSeqHeader2
    llTable2 ofTable2 mlTable2 afterTables2 bbr2 sequences2 blockOutput2 newHist2
    hoff2 hparse2 hbs2 hws2 htype2 hblockEnd2 hlit2 hseq2 hNumSeq2 hfse2 hbbr2
    hdec2 hexec2 hlast2

/-- When `decompressBlocksWF` encounters a non-last compressed block with
    sequences (numSeq > 0) followed by a last raw block, the output is
    `output ++ blockOutput1 ++ block2` at the position after the raw block.
    The raw block doesn't use Huffman/FSE/history state — it just appends
    raw bytes.

    Composes `decompressBlocksWF_compressed_sequences_step` and
    `decompressBlocksWF_single_raw`. -/
theorem decompressBlocksWF_compressed_seq_then_raw (data : ByteArray)
    (off : Nat) (windowSize : UInt64) (output : ByteArray)
    (prevHuff : Option Zip.Native.ZstdHuffmanTable)
    (prevFse : Zip.Native.PrevFseTables) (history : Array Nat)
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
    -- Block 1 hypotheses
    (hoff1 : ¬ data.size ≤ off)
    (hparse1 : Zip.Native.parseBlockHeader data off = .ok (hdr1, afterHdr1))
    (hbs1 : ¬ hdr1.blockSize > 131072)
    (hws1 : ¬ (windowSize > 0 && hdr1.blockSize.toUInt64 > windowSize))
    (htype1 : hdr1.blockType = .compressed)
    (hblockEnd1 : ¬ data.size < afterHdr1 + hdr1.blockSize.toNat)
    (hlit1 : Zip.Native.parseLiteralsSection data afterHdr1 prevHuff
               = .ok (literals1, afterLiterals1, huffTree1))
    (hseq1 : Zip.Native.parseSequencesHeader data afterLiterals1
               = .ok (numSeq1, modes1, afterSeqHeader1))
    (hNumSeq1 : ¬ numSeq1 == 0)
    (hfse1 : Zip.Native.resolveSequenceFseTables modes1 data afterSeqHeader1 prevFse
               = .ok (llTable1, ofTable1, mlTable1, afterTables1))
    (hbbr1 : Zip.Native.BackwardBitReader.init data afterTables1
               (afterHdr1 + hdr1.blockSize.toNat) = .ok bbr1)
    (hdec1 : Zip.Native.decodeSequences llTable1 ofTable1 mlTable1 bbr1 numSeq1
               = .ok sequences1)
    (hexec1 : Zip.Native.executeSequences sequences1 literals1
                (if windowSize > 0 && output.size > windowSize.toNat
                 then output.extract (output.size - windowSize.toNat) output.size
                 else output)
                history windowSize.toNat
                = .ok (blockOutput1, newHist1))
    (hnotlast1 : hdr1.lastBlock = false)
    (hadv1 : ¬ (afterHdr1 + hdr1.blockSize.toNat) ≤ off)
    -- Block 2 hypotheses
    (hoff2 : ¬ data.size ≤ afterHdr1 + hdr1.blockSize.toNat)
    (hparse2 : Zip.Native.parseBlockHeader data (afterHdr1 + hdr1.blockSize.toNat)
                 = .ok (hdr2, afterHdr2))
    (hbs2 : ¬ hdr2.blockSize > 131072)
    (hws2 : ¬ (windowSize > 0 && hdr2.blockSize.toUInt64 > windowSize))
    (htype2 : hdr2.blockType = .raw)
    (hraw2 : Zip.Native.decompressRawBlock data afterHdr2 hdr2.blockSize
               = .ok (block2, afterBlock2))
    (hlast2 : hdr2.lastBlock = true) :
    Zip.Native.decompressBlocksWF data off windowSize output prevHuff prevFse history
      = .ok (output ++ blockOutput1 ++ block2, afterBlock2) := by
  rw [decompressBlocksWF_compressed_sequences_step data off windowSize output prevHuff
    prevFse history hdr1 afterHdr1 literals1 afterLiterals1 huffTree1 numSeq1 modes1
    afterSeqHeader1 llTable1 ofTable1 mlTable1 afterTables1 bbr1 sequences1 blockOutput1
    newHist1 hoff1 hparse1 hbs1 hws1 htype1 hblockEnd1 hlit1 hseq1 hNumSeq1 hfse1 hbbr1
    hdec1 hexec1 hnotlast1 hadv1]
  exact decompressBlocksWF_single_raw data
    (afterHdr1 + hdr1.blockSize.toNat) windowSize (output ++ blockOutput1)
    _ { litLen := some llTable1, offset := some ofTable1, matchLen := some mlTable1 }
    newHist1
    hdr2 afterHdr2 block2 afterBlock2
    hoff2 hparse2 hbs2 hws2 htype2 hraw2 hlast2

/-- When `decompressBlocksWF` encounters a non-last compressed block with
    sequences (numSeq > 0) followed by a last compressed block with numSeq == 0
    (literals only), the output is `output ++ blockOutput1 ++ literals2` at the
    position after block 2. Block 1 produces updated Huffman tree, replaced FSE
    tables, and updated offset history. Block 2 (compLit) uses the updated
    Huffman tree for `parseLiteralsSection`; FSE tables and history are irrelevant
    for compLit blocks (numSeq=0).

    Composes `decompressBlocksWF_compressed_sequences_step` and
    `decompressBlocksWF_single_compressed_literals_only`. -/
theorem decompressBlocksWF_compressed_seq_then_compressed_lit (data : ByteArray)
    (off : Nat) (windowSize : UInt64) (output : ByteArray)
    (prevHuff : Option Zip.Native.ZstdHuffmanTable)
    (prevFse : Zip.Native.PrevFseTables) (history : Array Nat)
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
    -- Block 1 hypotheses
    (hoff1 : ¬ data.size ≤ off)
    (hparse1 : Zip.Native.parseBlockHeader data off = .ok (hdr1, afterHdr1))
    (hbs1 : ¬ hdr1.blockSize > 131072)
    (hws1 : ¬ (windowSize > 0 && hdr1.blockSize.toUInt64 > windowSize))
    (htype1 : hdr1.blockType = .compressed)
    (hblockEnd1 : ¬ data.size < afterHdr1 + hdr1.blockSize.toNat)
    (hlit1 : Zip.Native.parseLiteralsSection data afterHdr1 prevHuff
               = .ok (literals1, afterLiterals1, huffTree1))
    (hseq1 : Zip.Native.parseSequencesHeader data afterLiterals1
               = .ok (numSeq1, modes1, afterSeqHeader1))
    (hNumSeq1 : ¬ numSeq1 == 0)
    (hfse1 : Zip.Native.resolveSequenceFseTables modes1 data afterSeqHeader1 prevFse
               = .ok (llTable1, ofTable1, mlTable1, afterTables1))
    (hbbr1 : Zip.Native.BackwardBitReader.init data afterTables1
               (afterHdr1 + hdr1.blockSize.toNat) = .ok bbr1)
    (hdec1 : Zip.Native.decodeSequences llTable1 ofTable1 mlTable1 bbr1 numSeq1
               = .ok sequences1)
    (hexec1 : Zip.Native.executeSequences sequences1 literals1
                (if windowSize > 0 && output.size > windowSize.toNat
                 then output.extract (output.size - windowSize.toNat) output.size
                 else output)
                history windowSize.toNat
                = .ok (blockOutput1, newHist1))
    (hnotlast1 : hdr1.lastBlock = false)
    (hadv1 : ¬ (afterHdr1 + hdr1.blockSize.toNat) ≤ off)
    -- Block 2 hypotheses
    (hoff2 : ¬ data.size ≤ afterHdr1 + hdr1.blockSize.toNat)
    (hparse2 : Zip.Native.parseBlockHeader data (afterHdr1 + hdr1.blockSize.toNat)
                 = .ok (hdr2, afterHdr2))
    (hbs2 : ¬ hdr2.blockSize > 131072)
    (hws2 : ¬ (windowSize > 0 && hdr2.blockSize.toUInt64 > windowSize))
    (htype2 : hdr2.blockType = .compressed)
    (hblockEnd2 : ¬ data.size < afterHdr2 + hdr2.blockSize.toNat)
    (hlit2 : Zip.Native.parseLiteralsSection data afterHdr2
               (if let some ht := huffTree1 then some ht else prevHuff)
               = .ok (literals2, afterLiterals2, huffTree2))
    (hseq2 : Zip.Native.parseSequencesHeader data afterLiterals2
               = .ok (0, modes2, afterSeqHeader2))
    (hlast2 : hdr2.lastBlock = true) :
    Zip.Native.decompressBlocksWF data off windowSize output prevHuff prevFse history
      = .ok (output ++ blockOutput1 ++ literals2,
             afterHdr2 + hdr2.blockSize.toNat) := by
  rw [decompressBlocksWF_compressed_sequences_step data off windowSize output prevHuff
    prevFse history hdr1 afterHdr1 literals1 afterLiterals1 huffTree1 numSeq1 modes1
    afterSeqHeader1 llTable1 ofTable1 mlTable1 afterTables1 bbr1 sequences1 blockOutput1
    newHist1 hoff1 hparse1 hbs1 hws1 htype1 hblockEnd1 hlit1 hseq1 hNumSeq1 hfse1 hbbr1
    hdec1 hexec1 hnotlast1 hadv1]
  exact decompressBlocksWF_single_compressed_literals_only data
    (afterHdr1 + hdr1.blockSize.toNat) windowSize (output ++ blockOutput1) _
    { litLen := some llTable1, offset := some ofTable1, matchLen := some mlTable1 }
    newHist1
    hdr2 afterHdr2 literals2 afterLiterals2 huffTree2 modes2 afterSeqHeader2
    hoff2 hparse2 hbs2 hws2 htype2 hblockEnd2 hlit2 hseq2 hlast2

/-- When `decompressBlocksWF` encounters a non-last compressed block with
    numSeq == 0 (literals only) followed by a last compressed block with
    sequences (numSeq > 0), the output is `output ++ literals1 ++ blockOutput2`
    at the position after block 2. Block 1 produces updated Huffman tree;
    FSE tables and offset history are unchanged (numSeq=0). Block 2 (compSeq)
    uses the updated Huffman tree for `parseLiteralsSection`, the original FSE
    tables for `resolveSequenceFseTables`, and the original offset history for
    `executeSequences`.

    Composes `decompressBlocksWF_compressed_literals_only_step` and
    `decompressBlocksWF_single_compressed_sequences`. -/
theorem decompressBlocksWF_compressed_lit_then_compressed_seq (data : ByteArray)
    (off : Nat) (windowSize : UInt64) (output : ByteArray)
    (prevHuff : Option Zip.Native.ZstdHuffmanTable)
    (prevFse : Zip.Native.PrevFseTables) (history : Array Nat)
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
    -- Block 1 hypotheses
    (hoff1 : ¬ data.size ≤ off)
    (hparse1 : Zip.Native.parseBlockHeader data off = .ok (hdr1, afterHdr1))
    (hbs1 : ¬ hdr1.blockSize > 131072)
    (hws1 : ¬ (windowSize > 0 && hdr1.blockSize.toUInt64 > windowSize))
    (htype1 : hdr1.blockType = .compressed)
    (hblockEnd1 : ¬ data.size < afterHdr1 + hdr1.blockSize.toNat)
    (hlit1 : Zip.Native.parseLiteralsSection data afterHdr1 prevHuff
               = .ok (literals1, afterLiterals1, huffTree1))
    (hseq1 : Zip.Native.parseSequencesHeader data afterLiterals1
               = .ok (0, modes1, afterSeqHeader1))
    (hnotlast1 : hdr1.lastBlock = false)
    (hadv1 : ¬ afterHdr1 + hdr1.blockSize.toNat ≤ off)
    -- Block 2 hypotheses
    (hoff2 : ¬ data.size ≤ afterHdr1 + hdr1.blockSize.toNat)
    (hparse2 : Zip.Native.parseBlockHeader data (afterHdr1 + hdr1.blockSize.toNat)
                 = .ok (hdr2, afterHdr2))
    (hbs2 : ¬ hdr2.blockSize > 131072)
    (hws2 : ¬ (windowSize > 0 && hdr2.blockSize.toUInt64 > windowSize))
    (htype2 : hdr2.blockType = .compressed)
    (hblockEnd2 : ¬ data.size < afterHdr2 + hdr2.blockSize.toNat)
    (hlit2 : Zip.Native.parseLiteralsSection data afterHdr2
               (if let some ht := huffTree1 then some ht else prevHuff)
               = .ok (literals2, afterLiterals2, huffTree2))
    (hseq2 : Zip.Native.parseSequencesHeader data afterLiterals2
               = .ok (numSeq2, modes2, afterSeqHeader2))
    (hNumSeq2 : ¬ numSeq2 == 0)
    (hfse2 : Zip.Native.resolveSequenceFseTables modes2 data afterSeqHeader2 prevFse
               = .ok (llTable2, ofTable2, mlTable2, afterTables2))
    (hbbr2 : Zip.Native.BackwardBitReader.init data afterTables2
               (afterHdr2 + hdr2.blockSize.toNat) = .ok bbr2)
    (hdec2 : Zip.Native.decodeSequences llTable2 ofTable2 mlTable2 bbr2 numSeq2
               = .ok sequences2)
    (hexec2 : Zip.Native.executeSequences sequences2 literals2
                (if windowSize > 0 && (output ++ literals1).size > windowSize.toNat
                 then (output ++ literals1).extract
                   ((output ++ literals1).size - windowSize.toNat)
                   (output ++ literals1).size
                 else output ++ literals1)
                history windowSize.toNat
                = .ok (blockOutput2, newHist2))
    (hlast2 : hdr2.lastBlock = true) :
    Zip.Native.decompressBlocksWF data off windowSize output prevHuff prevFse history
      = .ok (output ++ literals1 ++ blockOutput2,
             afterHdr2 + hdr2.blockSize.toNat) := by
  rw [decompressBlocksWF_compressed_literals_only_step data off windowSize output prevHuff
    prevFse history hdr1 afterHdr1 literals1 afterLiterals1 huffTree1 modes1 afterSeqHeader1
    hoff1 hparse1 hbs1 hws1 htype1 hblockEnd1 hlit1 hseq1 hnotlast1 hadv1]
  exact decompressBlocksWF_single_compressed_sequences data
    (afterHdr1 + hdr1.blockSize.toNat) windowSize (output ++ literals1) _ prevFse history
    hdr2 afterHdr2 literals2 afterLiterals2 huffTree2 numSeq2 modes2 afterSeqHeader2
    llTable2 ofTable2 mlTable2 afterTables2 bbr2 sequences2 blockOutput2 newHist2
    hoff2 hparse2 hbs2 hws2 htype2 hblockEnd2 hlit2 hseq2 hNumSeq2 hfse2 hbbr2
    hdec2 hexec2 hlast2

/-- When `decompressFrame` succeeds and the frame contains a single last
    compressed block with numSeq=0 (literals only), the output equals the
    literal section content. -/
theorem decompressFrame_single_compressed_literals_content (data : ByteArray)
    (pos : Nat) (output : ByteArray) (pos' : Nat)
    (header : Zip.Native.ZstdFrameHeader) (afterHeader : Nat)
    (hdr : Zip.Native.ZstdBlockHeader) (afterHdr : Nat)
    (literals : ByteArray) (afterLiterals : Nat)
    (huffTree : Option Zip.Native.ZstdHuffmanTable)
    (modes : Zip.Native.SequenceCompressionModes) (afterSeqHeader : Nat)
    (hframe : Zip.Native.decompressFrame data pos = .ok (output, pos'))
    (hh : Zip.Native.parseFrameHeader data pos = .ok (header, afterHeader))
    (hparse : Zip.Native.parseBlockHeader data afterHeader = .ok (hdr, afterHdr))
    (hbs : ¬ hdr.blockSize > 131072)
    (hws : ¬ (header.windowSize > 0 && hdr.blockSize.toUInt64 > header.windowSize))
    (htype : hdr.blockType = .compressed)
    (hblockEnd : ¬ data.size < afterHdr + hdr.blockSize.toNat)
    (hlit : Zip.Native.parseLiteralsSection data afterHdr none
              = .ok (literals, afterLiterals, huffTree))
    (hseq : Zip.Native.parseSequencesHeader data afterLiterals
              = .ok (0, modes, afterSeqHeader))
    (hlast : hdr.lastBlock = true) :
    output = literals := by
  have hoff := parseBlockHeader_data_not_le data afterHeader hdr afterHdr hparse
  -- Compute the exact block loop result
  have hblocks := decompressBlocksWF_single_compressed_literals_only data afterHeader
    header.windowSize ByteArray.empty none {} #[1, 4, 8] hdr afterHdr
    literals afterLiterals huffTree modes afterSeqHeader
    hoff hparse hbs hws htype hblockEnd hlit hseq hlast
  frame_from_blocks

/-- When `decompressFrame` succeeds and the frame contains a single last
    compressed block with sequences (numSeq > 0), the output equals the
    sequence execution result. -/
theorem decompressFrame_single_compressed_sequences_content (data : ByteArray)
    (pos : Nat) (output : ByteArray) (pos' : Nat)
    (header : Zip.Native.ZstdFrameHeader) (afterHeader : Nat)
    (hdr : Zip.Native.ZstdBlockHeader) (afterHdr : Nat)
    (literals : ByteArray) (afterLiterals : Nat)
    (huffTree : Option Zip.Native.ZstdHuffmanTable)
    (numSeq : Nat) (modes : Zip.Native.SequenceCompressionModes) (afterSeqHeader : Nat)
    (llTable ofTable mlTable : Zip.Native.FseTable) (afterTables : Nat)
    (bbr : Zip.Native.BackwardBitReader)
    (sequences : Array Zip.Native.ZstdSequence)
    (blockOutput : ByteArray) (newHist : Array Nat)
    (hframe : Zip.Native.decompressFrame data pos = .ok (output, pos'))
    (hh : Zip.Native.parseFrameHeader data pos = .ok (header, afterHeader))
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
    (hlast : hdr.lastBlock = true) :
    output = blockOutput := by
  have hoff := parseBlockHeader_data_not_le data afterHeader hdr afterHdr hparse
  -- The block-loop theorem needs the executeSequences with window-checked output.
  -- Since decompressBlocks passes ByteArray.empty as initial output, and
  -- ByteArray.empty.size = 0 is never > windowSize.toNat, the window check
  -- simplifies to ByteArray.empty.
  have hexec' : Zip.Native.executeSequences sequences literals
      (if header.windowSize > 0 && ByteArray.empty.size > header.windowSize.toNat
       then ByteArray.empty.extract (ByteArray.empty.size - header.windowSize.toNat)
              ByteArray.empty.size
       else ByteArray.empty)
      #[1, 4, 8] header.windowSize.toNat
      = .ok (blockOutput, newHist) := by
    simp only [ByteArray.size_empty, Nat.not_lt_zero, decide_false, Bool.and_false]
    exact hexec
  -- Compute the exact block loop result
  have hblocks := decompressBlocksWF_single_compressed_sequences data afterHeader
    header.windowSize ByteArray.empty none {} #[1, 4, 8] hdr afterHdr
    literals afterLiterals huffTree numSeq modes afterSeqHeader
    llTable ofTable mlTable afterTables bbr sequences blockOutput newHist
    hoff hparse hbs hws htype hblockEnd hlit hseq hNumSeq hfse hbbr hdec hexec' hlast
  frame_from_blocks

/-- When `decompressFrame` succeeds and the frame contains a non-last compressed
    block with numSeq=0 (literals only) followed by a last raw block, the output
    equals `literals1 ++ block2`. Compressed-literals blocks don't modify FSE
    tables or offset history, and raw blocks don't use Huffman/FSE state, so no
    state threading complexity arises. -/
theorem decompressFrame_compressed_lit_then_raw_content (data : ByteArray)
    (pos : Nat) (output : ByteArray) (pos' : Nat)
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
    (hframe : Zip.Native.decompressFrame data pos = .ok (output, pos'))
    (hh : Zip.Native.parseFrameHeader data pos = .ok (header, afterHeader))
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
    (hlast2 : hdr2.lastBlock = true) :
    output = literals1 ++ block2 := by
  have hoff := parseBlockHeader_data_not_le data afterHeader hdr1 afterHdr1 hparse1
  -- Compute the exact block loop result
  have hblocks := decompressBlocksWF_compressed_literals_then_raw data afterHeader
    header.windowSize ByteArray.empty none {} #[1, 4, 8] hdr1 afterHdr1
    literals1 afterLiterals1 huffTree1 modes1 afterSeqHeader1
    hdr2 afterHdr2 block2 afterBlock2
    hoff hparse1 hbs1 hws1 htype1 hblockEnd1 hlit1 hseq1 hnotlast1 hadv1
    hoff2 hparse2 hbs2 hws2 htype2 hraw2 hlast2
  frame_from_blocks

/-- When `decompressFrame` succeeds and the frame contains a non-last compressed
    block with numSeq=0 (literals only) followed by a last RLE block, the output
    equals `literals1 ++ block2`. Compressed-literals blocks don't modify FSE
    tables or offset history, and RLE blocks don't use Huffman/FSE state, so no
    state threading complexity arises. -/
theorem decompressFrame_compressed_lit_then_rle_content (data : ByteArray)
    (pos : Nat) (output : ByteArray) (pos' : Nat)
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
    (hframe : Zip.Native.decompressFrame data pos = .ok (output, pos'))
    (hh : Zip.Native.parseFrameHeader data pos = .ok (header, afterHeader))
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
    (hlast2 : hdr2.lastBlock = true) :
    output = literals1 ++ block2 := by
  have hoff := parseBlockHeader_data_not_le data afterHeader hdr1 afterHdr1 hparse1
  -- Compute the exact block loop result
  have hblocks := decompressBlocksWF_compressed_literals_then_rle data afterHeader
    header.windowSize ByteArray.empty none {} #[1, 4, 8] hdr1 afterHdr1
    literals1 afterLiterals1 huffTree1 modes1 afterSeqHeader1
    hdr2 afterHdr2 block2 afterByte2
    hoff hparse1 hbs1 hws1 htype1 hblockEnd1 hlit1 hseq1 hnotlast1 hadv1
    hoff2 hparse2 hbs2 hws2 htype2 hrle2 hlast2
  frame_from_blocks

/-- When `decompressFrame` succeeds and the frame contains a non-last compressed
    block with numSeq>0 (sequences) followed by a last raw block, the output
    equals `blockOutput1 ++ block2`. The compressed-sequences block produces
    `blockOutput1` via sequence execution; the raw block contributes `block2`
    directly. Raw blocks ignore all Huffman/FSE/offset state from block 1. -/
theorem decompressFrame_compressed_seq_then_raw_content (data : ByteArray)
    (pos : Nat) (output : ByteArray) (pos' : Nat)
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
    (hframe : Zip.Native.decompressFrame data pos = .ok (output, pos'))
    (hh : Zip.Native.parseFrameHeader data pos = .ok (header, afterHeader))
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
    (hlast2 : hdr2.lastBlock = true) :
    output = blockOutput1 ++ block2 := by
  have hoff := parseBlockHeader_data_not_le data afterHeader hdr1 afterHdr1 hparse1
  -- Bridge executeSequences: frame starts with empty output, so window check is trivial
  have hexec1' : Zip.Native.executeSequences sequences1 literals1
      (if header.windowSize > 0 && ByteArray.empty.size > header.windowSize.toNat
       then ByteArray.empty.extract (ByteArray.empty.size - header.windowSize.toNat)
              ByteArray.empty.size
       else ByteArray.empty)
      #[1, 4, 8] header.windowSize.toNat
      = .ok (blockOutput1, newHist1) := by
    simp only [ByteArray.size_empty, Nat.not_lt_zero, decide_false, Bool.and_false]
    exact hexec1
  -- Compute the exact block loop result
  have hblocks := decompressBlocksWF_compressed_seq_then_raw data afterHeader
    header.windowSize ByteArray.empty none {} #[1, 4, 8] hdr1 afterHdr1
    literals1 afterLiterals1 huffTree1 numSeq1 modes1 afterSeqHeader1
    llTable1 ofTable1 mlTable1 afterTables1 bbr1 sequences1 blockOutput1 newHist1
    hdr2 afterHdr2 block2 afterBlock2
    hoff hparse1 hbs1 hws1 htype1 hblockEnd1 hlit1 hseq1 hNumSeq1 hfse1 hbbr1
    hdec1 hexec1' hnotlast1 hadv1
    hoff2 hparse2 hbs2 hws2 htype2 hraw2 hlast2
  frame_from_blocks

/-- When `decompressFrame` succeeds and the frame contains a non-last compressed
    block with numSeq>0 (sequences) followed by a last compressed block with
    numSeq=0 (literals only), the output equals `blockOutput1 ++ literals2`.
    Block 1 produces updated Huffman tree and FSE tables; block 2's
    `parseLiteralsSection` uses the potentially updated tree from block 1.

    Inlines `decompressBlocksWF_compressed_sequences_step` +
    `decompressBlocksWF_single_compressed_literals_only` at the frame level. -/
theorem decompressFrame_compressed_seq_then_compressed_lit_content (data : ByteArray)
    (pos : Nat) (output : ByteArray) (pos' : Nat)
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
    (hframe : Zip.Native.decompressFrame data pos = .ok (output, pos'))
    (hh : Zip.Native.parseFrameHeader data pos = .ok (header, afterHeader))
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
    (hlast2 : hdr2.lastBlock = true) :
    output = blockOutput1 ++ literals2 := by
  have hoff := parseBlockHeader_data_not_le data afterHeader hdr1 afterHdr1 hparse1
  -- The block-loop theorem needs the executeSequences with window-checked output.
  -- Since decompressBlocks passes ByteArray.empty as initial output, and
  -- ByteArray.empty.size = 0 is never > windowSize.toNat, the window check
  -- simplifies to ByteArray.empty.
  have hexec1' : Zip.Native.executeSequences sequences1 literals1
      (if header.windowSize > 0 && ByteArray.empty.size > header.windowSize.toNat
       then ByteArray.empty.extract (ByteArray.empty.size - header.windowSize.toNat)
              ByteArray.empty.size
       else ByteArray.empty)
      #[1, 4, 8] header.windowSize.toNat
      = .ok (blockOutput1, newHist1) := by
    simp only [ByteArray.size_empty, Nat.not_lt_zero, decide_false, Bool.and_false]
    exact hexec1
  -- Reduce block 1 (compSeq step) then apply block 2 (single compLit).
  -- We inline the two-step proof to avoid dependent-type mismatch with the
  -- composition theorem's elaboration of `if let` in hlit2.
  have hblocks : Zip.Native.decompressBlocksWF data afterHeader header.windowSize
      ByteArray.empty none {} #[1, 4, 8]
      = .ok (ByteArray.empty ++ blockOutput1 ++ literals2,
             afterHdr2 + hdr2.blockSize.toNat) := by
    rw [decompressBlocksWF_compressed_sequences_step data afterHeader header.windowSize
      ByteArray.empty none {} #[1, 4, 8] hdr1 afterHdr1
      literals1 afterLiterals1 huffTree1 numSeq1 modes1 afterSeqHeader1
      llTable1 ofTable1 mlTable1 afterTables1 bbr1 sequences1 blockOutput1 newHist1
      hoff hparse1 hbs1 hws1 htype1 hblockEnd1 hlit1 hseq1 hNumSeq1 hfse1 hbbr1
      hdec1 hexec1' hnotlast1 hadv1]
    exact decompressBlocksWF_single_compressed_literals_only data
      (afterHdr1 + hdr1.blockSize.toNat) header.windowSize (ByteArray.empty ++ blockOutput1)
      _ { litLen := some llTable1, offset := some ofTable1, matchLen := some mlTable1 }
      newHist1
      hdr2 afterHdr2 literals2 afterLiterals2 huffTree2 modes2 afterSeqHeader2
      hoff2 hparse2 hbs2 hws2 htype2 hblockEnd2
      (by cases huffTree1 <;> exact hlit2) hseq2 hlast2
  frame_from_blocks

/-- When `decompressFrame` succeeds and the frame contains a non-last compressed
    block with numSeq=0 (literals only) followed by a last compressed block with
    numSeq>0 (sequences), the output equals `literals1 ++ blockOutput2`.
    Block 1 produces updated Huffman tree; FSE tables and offset history are
    unchanged (numSeq=0). Block 2 uses the updated Huffman tree for
    `parseLiteralsSection`, the original FSE tables (`{}`) for
    `resolveSequenceFseTables`, and the original offset history.

    Inlines `decompressBlocksWF_compressed_literals_only_step` +
    `decompressBlocksWF_single_compressed_sequences` at the frame level. -/
theorem decompressFrame_compressed_lit_then_compressed_seq_content (data : ByteArray)
    (pos : Nat) (output : ByteArray) (pos' : Nat)
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
    (hframe : Zip.Native.decompressFrame data pos = .ok (output, pos'))
    (hh : Zip.Native.parseFrameHeader data pos = .ok (header, afterHeader))
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
    (hlast2 : hdr2.lastBlock = true) :
    output = literals1 ++ blockOutput2 := by
  have hoff := parseBlockHeader_data_not_le data afterHeader hdr1 afterHdr1 hparse1
  -- The block-loop theorem needs executeSequences with (output ++ literals1) as the
  -- window reference, where output = ByteArray.empty. Convert to use literals1 directly.
  have hexec2' : Zip.Native.executeSequences sequences2 literals2
      (if header.windowSize > 0 &&
           (ByteArray.empty ++ literals1).size > header.windowSize.toNat
       then (ByteArray.empty ++ literals1).extract
              ((ByteArray.empty ++ literals1).size - header.windowSize.toNat)
              (ByteArray.empty ++ literals1).size
       else ByteArray.empty ++ literals1)
      #[1, 4, 8] header.windowSize.toNat
      = .ok (blockOutput2, newHist2) := by
    simp only [ByteArray.empty_append]
    exact hexec2
  -- Reduce block 1 (compLit step) then apply block 2 (single compSeq).
  -- We inline the two-step proof to avoid dependent-type mismatch with the
  -- composition theorem's elaboration of `if let` in hlit2.
  have hblocks : Zip.Native.decompressBlocksWF data afterHeader header.windowSize
      ByteArray.empty none {} #[1, 4, 8]
      = .ok (ByteArray.empty ++ literals1 ++ blockOutput2,
             afterHdr2 + hdr2.blockSize.toNat) := by
    rw [decompressBlocksWF_compressed_literals_only_step data afterHeader header.windowSize
      ByteArray.empty none {} #[1, 4, 8] hdr1 afterHdr1
      literals1 afterLiterals1 huffTree1 modes1 afterSeqHeader1
      hoff hparse1 hbs1 hws1 htype1 hblockEnd1 hlit1 hseq1 hnotlast1 hadv1]
    exact decompressBlocksWF_single_compressed_sequences data
      (afterHdr1 + hdr1.blockSize.toNat) header.windowSize (ByteArray.empty ++ literals1)
      _ {} #[1, 4, 8]
      hdr2 afterHdr2 literals2 afterLiterals2 huffTree2 numSeq2 modes2 afterSeqHeader2
      llTable2 ofTable2 mlTable2 afterTables2 bbr2 sequences2 blockOutput2 newHist2
      hoff2 hparse2 hbs2 hws2 htype2 hblockEnd2
      (by cases huffTree1 <;> exact hlit2) hseq2 hNumSeq2 hfse2 hbbr2
      hdec2 hexec2' hlast2
  frame_from_blocks

/-- When `decompressFrame` succeeds and the frame contains a non-last raw block
    followed by a last compressed block with numSeq=0 (literals only), the output
    equals `block1 ++ literals2`. Raw blocks don't modify Huffman/FSE state, so
    block 2's `parseLiteralsSection` receives `none` for prevHuff. -/
theorem decompressFrame_raw_then_compressed_lit_content (data : ByteArray)
    (pos : Nat) (output : ByteArray) (pos' : Nat)
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
    (hframe : Zip.Native.decompressFrame data pos = .ok (output, pos'))
    (hh : Zip.Native.parseFrameHeader data pos = .ok (header, afterHeader))
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
    (hlast2 : hdr2.lastBlock = true) :
    output = block1 ++ literals2 := by
  have hoff := parseBlockHeader_data_not_le data afterHeader hdr1 afterHdr1 hparse1
  -- Compute the exact block loop result
  have hblocks := decompressBlocksWF_raw_then_compressed_literals data afterHeader
    header.windowSize ByteArray.empty none {} #[1, 4, 8] hdr1 afterHdr1
    block1 afterBlock1 hdr2 afterHdr2 literals2 afterLiterals2
    huffTree2 modes2 afterSeqHeader2
    hoff hparse1 hbs1 hws1 htype1 hraw1 hnotlast1 hadv1
    hoff2 hparse2 hbs2 hws2 htype2 hblockEnd2 hlit2 hseq2 hlast2
  frame_from_blocks

/-- When `decompressFrame` succeeds and the frame contains a non-last RLE block
    followed by a last compressed block with numSeq=0 (literals only), the output
    equals `block1 ++ literals2`. RLE blocks don't modify Huffman/FSE state, so
    block 2's `parseLiteralsSection` receives `none` for prevHuff. -/
theorem decompressFrame_rle_then_compressed_lit_content (data : ByteArray)
    (pos : Nat) (output : ByteArray) (pos' : Nat)
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
    (hframe : Zip.Native.decompressFrame data pos = .ok (output, pos'))
    (hh : Zip.Native.parseFrameHeader data pos = .ok (header, afterHeader))
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
    (hlast2 : hdr2.lastBlock = true) :
    output = block1 ++ literals2 := by
  have hoff := parseBlockHeader_data_not_le data afterHeader hdr1 afterHdr1 hparse1
  -- Compute the exact block loop result
  have hblocks := decompressBlocksWF_rle_then_compressed_literals data afterHeader
    header.windowSize ByteArray.empty none {} #[1, 4, 8] hdr1 afterHdr1
    block1 afterByte1 hdr2 afterHdr2 literals2 afterLiterals2
    huffTree2 modes2 afterSeqHeader2
    hoff hparse1 hbs1 hws1 htype1 hrle1 hnotlast1 hadv1
    hoff2 hparse2 hbs2 hws2 htype2 hblockEnd2 hlit2 hseq2 hlast2
  frame_from_blocks

/-- When `decompressBlocksWF` encounters a non-last raw block followed by a
    last compressed block with sequences (numSeq > 0), the output is
    `output ++ block1 ++ blockOutput2` at the position after the compressed block.
    Raw blocks don't modify Huffman/FSE state or offset history, so block 2
    receives the original `prevHuff`, `prevFse`, and `history`.

    Composes `decompressBlocksWF_raw_step` and
    `decompressBlocksWF_single_compressed_sequences`. -/
theorem decompressBlocksWF_raw_then_compressed_sequences (data : ByteArray)
    (off : Nat) (windowSize : UInt64) (output : ByteArray)
    (prevHuff : Option Zip.Native.ZstdHuffmanTable)
    (prevFse : Zip.Native.PrevFseTables) (history : Array Nat)
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
    (htype2 : hdr2.blockType = .compressed)
    (hblockEnd2 : ¬ data.size < afterHdr2 + hdr2.blockSize.toNat)
    (hlit2 : Zip.Native.parseLiteralsSection data afterHdr2 prevHuff
               = .ok (literals2, afterLiterals2, huffTree2))
    (hseq2 : Zip.Native.parseSequencesHeader data afterLiterals2
               = .ok (numSeq2, modes2, afterSeqHeader2))
    (hNumSeq2 : ¬ numSeq2 == 0)
    (hfse2 : Zip.Native.resolveSequenceFseTables modes2 data afterSeqHeader2 prevFse
               = .ok (llTable2, ofTable2, mlTable2, afterTables2))
    (hbbr2 : Zip.Native.BackwardBitReader.init data afterTables2
               (afterHdr2 + hdr2.blockSize.toNat) = .ok bbr2)
    (hdec2 : Zip.Native.decodeSequences llTable2 ofTable2 mlTable2 bbr2 numSeq2
               = .ok sequences2)
    (hexec2 : Zip.Native.executeSequences sequences2 literals2
                (if windowSize > 0 && (output ++ block1).size > windowSize.toNat
                 then (output ++ block1).extract
                   ((output ++ block1).size - windowSize.toNat)
                   (output ++ block1).size
                 else output ++ block1)
                history windowSize.toNat
                = .ok (blockOutput2, newHist2))
    (hlast2 : hdr2.lastBlock = true) :
    Zip.Native.decompressBlocksWF data off windowSize output prevHuff prevFse history
      = .ok (output ++ block1 ++ blockOutput2,
             afterHdr2 + hdr2.blockSize.toNat) := by
  rw [decompressBlocksWF_raw_step data off windowSize output prevHuff prevFse history
    hdr1 afterHdr1 block1 afterBlock1 hoff1 hparse1 hbs1 hws1 htype1 hraw1 hnotlast1 hadv1]
  exact decompressBlocksWF_single_compressed_sequences data
    afterBlock1 windowSize (output ++ block1) prevHuff prevFse history
    hdr2 afterHdr2 literals2 afterLiterals2 huffTree2 numSeq2 modes2 afterSeqHeader2
    llTable2 ofTable2 mlTable2 afterTables2 bbr2 sequences2 blockOutput2 newHist2
    hoff2 hparse2 hbs2 hws2 htype2 hblockEnd2 hlit2 hseq2 hNumSeq2 hfse2 hbbr2
    hdec2 hexec2 hlast2

/-- When `decompressBlocksWF` encounters a non-last RLE block followed by a
    last compressed block with sequences (numSeq > 0), the output is
    `output ++ block1 ++ blockOutput2` at the position after the compressed block.
    RLE blocks don't modify Huffman/FSE state or offset history, so block 2
    receives the original `prevHuff`, `prevFse`, and `history`.

    Composes `decompressBlocksWF_rle_step` and
    `decompressBlocksWF_single_compressed_sequences`. -/
theorem decompressBlocksWF_rle_then_compressed_sequences (data : ByteArray)
    (off : Nat) (windowSize : UInt64) (output : ByteArray)
    (prevHuff : Option Zip.Native.ZstdHuffmanTable)
    (prevFse : Zip.Native.PrevFseTables) (history : Array Nat)
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
    (htype2 : hdr2.blockType = .compressed)
    (hblockEnd2 : ¬ data.size < afterHdr2 + hdr2.blockSize.toNat)
    (hlit2 : Zip.Native.parseLiteralsSection data afterHdr2 prevHuff
               = .ok (literals2, afterLiterals2, huffTree2))
    (hseq2 : Zip.Native.parseSequencesHeader data afterLiterals2
               = .ok (numSeq2, modes2, afterSeqHeader2))
    (hNumSeq2 : ¬ numSeq2 == 0)
    (hfse2 : Zip.Native.resolveSequenceFseTables modes2 data afterSeqHeader2 prevFse
               = .ok (llTable2, ofTable2, mlTable2, afterTables2))
    (hbbr2 : Zip.Native.BackwardBitReader.init data afterTables2
               (afterHdr2 + hdr2.blockSize.toNat) = .ok bbr2)
    (hdec2 : Zip.Native.decodeSequences llTable2 ofTable2 mlTable2 bbr2 numSeq2
               = .ok sequences2)
    (hexec2 : Zip.Native.executeSequences sequences2 literals2
                (if windowSize > 0 && (output ++ block1).size > windowSize.toNat
                 then (output ++ block1).extract
                   ((output ++ block1).size - windowSize.toNat)
                   (output ++ block1).size
                 else output ++ block1)
                history windowSize.toNat
                = .ok (blockOutput2, newHist2))
    (hlast2 : hdr2.lastBlock = true) :
    Zip.Native.decompressBlocksWF data off windowSize output prevHuff prevFse history
      = .ok (output ++ block1 ++ blockOutput2,
             afterHdr2 + hdr2.blockSize.toNat) := by
  rw [decompressBlocksWF_rle_step data off windowSize output prevHuff prevFse history
    hdr1 afterHdr1 block1 afterByte1 hoff1 hparse1 hbs1 hws1 htype1 hrle1 hnotlast1 hadv1]
  exact decompressBlocksWF_single_compressed_sequences data
    afterByte1 windowSize (output ++ block1) prevHuff prevFse history
    hdr2 afterHdr2 literals2 afterLiterals2 huffTree2 numSeq2 modes2 afterSeqHeader2
    llTable2 ofTable2 mlTable2 afterTables2 bbr2 sequences2 blockOutput2 newHist2
    hoff2 hparse2 hbs2 hws2 htype2 hblockEnd2 hlit2 hseq2 hNumSeq2 hfse2 hbbr2
    hdec2 hexec2 hlast2

/-- When `decompressBlocksWF` encounters a non-last compressed block with
    sequences (numSeq > 0) followed by a last RLE block, the output is
    `output ++ blockOutput1 ++ block2` at the position after the RLE byte.
    The RLE block doesn't use Huffman/FSE/history state — it just replicates
    a single byte.

    Composes `decompressBlocksWF_compressed_sequences_step` and
    `decompressBlocksWF_single_rle`. -/
theorem decompressBlocksWF_compressed_seq_then_rle (data : ByteArray)
    (off : Nat) (windowSize : UInt64) (output : ByteArray)
    (prevHuff : Option Zip.Native.ZstdHuffmanTable)
    (prevFse : Zip.Native.PrevFseTables) (history : Array Nat)
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
    -- Block 1 hypotheses
    (hoff1 : ¬ data.size ≤ off)
    (hparse1 : Zip.Native.parseBlockHeader data off = .ok (hdr1, afterHdr1))
    (hbs1 : ¬ hdr1.blockSize > 131072)
    (hws1 : ¬ (windowSize > 0 && hdr1.blockSize.toUInt64 > windowSize))
    (htype1 : hdr1.blockType = .compressed)
    (hblockEnd1 : ¬ data.size < afterHdr1 + hdr1.blockSize.toNat)
    (hlit1 : Zip.Native.parseLiteralsSection data afterHdr1 prevHuff
               = .ok (literals1, afterLiterals1, huffTree1))
    (hseq1 : Zip.Native.parseSequencesHeader data afterLiterals1
               = .ok (numSeq1, modes1, afterSeqHeader1))
    (hNumSeq1 : ¬ numSeq1 == 0)
    (hfse1 : Zip.Native.resolveSequenceFseTables modes1 data afterSeqHeader1 prevFse
               = .ok (llTable1, ofTable1, mlTable1, afterTables1))
    (hbbr1 : Zip.Native.BackwardBitReader.init data afterTables1
               (afterHdr1 + hdr1.blockSize.toNat) = .ok bbr1)
    (hdec1 : Zip.Native.decodeSequences llTable1 ofTable1 mlTable1 bbr1 numSeq1
               = .ok sequences1)
    (hexec1 : Zip.Native.executeSequences sequences1 literals1
                (if windowSize > 0 && output.size > windowSize.toNat
                 then output.extract (output.size - windowSize.toNat) output.size
                 else output)
                history windowSize.toNat
                = .ok (blockOutput1, newHist1))
    (hnotlast1 : hdr1.lastBlock = false)
    (hadv1 : ¬ (afterHdr1 + hdr1.blockSize.toNat) ≤ off)
    -- Block 2 hypotheses
    (hoff2 : ¬ data.size ≤ afterHdr1 + hdr1.blockSize.toNat)
    (hparse2 : Zip.Native.parseBlockHeader data (afterHdr1 + hdr1.blockSize.toNat)
                 = .ok (hdr2, afterHdr2))
    (hbs2 : ¬ hdr2.blockSize > 131072)
    (hws2 : ¬ (windowSize > 0 && hdr2.blockSize.toUInt64 > windowSize))
    (htype2 : hdr2.blockType = .rle)
    (hrle2 : Zip.Native.decompressRLEBlock data afterHdr2 hdr2.blockSize
               = .ok (block2, afterByte2))
    (hlast2 : hdr2.lastBlock = true) :
    Zip.Native.decompressBlocksWF data off windowSize output prevHuff prevFse history
      = .ok (output ++ blockOutput1 ++ block2, afterByte2) := by
  rw [decompressBlocksWF_compressed_sequences_step data off windowSize output prevHuff
    prevFse history hdr1 afterHdr1 literals1 afterLiterals1 huffTree1 numSeq1 modes1
    afterSeqHeader1 llTable1 ofTable1 mlTable1 afterTables1 bbr1 sequences1 blockOutput1
    newHist1 hoff1 hparse1 hbs1 hws1 htype1 hblockEnd1 hlit1 hseq1 hNumSeq1 hfse1 hbbr1
    hdec1 hexec1 hnotlast1 hadv1]
  exact decompressBlocksWF_single_rle data
    (afterHdr1 + hdr1.blockSize.toNat) windowSize (output ++ blockOutput1)
    _ { litLen := some llTable1, offset := some ofTable1, matchLen := some mlTable1 }
    newHist1
    hdr2 afterHdr2 block2 afterByte2
    hoff2 hparse2 hbs2 hws2 htype2 hrle2 hlast2

/-- When `decompressFrame` succeeds and the frame contains a non-last compressed
    block with numSeq>0 (sequences) followed by a last RLE block, the output
    equals `blockOutput1 ++ block2`. The compressed-sequences block produces
    `blockOutput1` via sequence execution; the RLE block contributes `block2`
    directly. RLE blocks ignore all Huffman/FSE/offset state from block 1. -/
theorem decompressFrame_compressed_seq_then_rle_content (data : ByteArray)
    (pos : Nat) (output : ByteArray) (pos' : Nat)
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
    (hframe : Zip.Native.decompressFrame data pos = .ok (output, pos'))
    (hh : Zip.Native.parseFrameHeader data pos = .ok (header, afterHeader))
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
    (hlast2 : hdr2.lastBlock = true) :
    output = blockOutput1 ++ block2 := by
  have hoff := parseBlockHeader_data_not_le data afterHeader hdr1 afterHdr1 hparse1
  -- Bridge executeSequences: frame starts with empty output, so window check is trivial
  have hexec1' : Zip.Native.executeSequences sequences1 literals1
      (if header.windowSize > 0 && ByteArray.empty.size > header.windowSize.toNat
       then ByteArray.empty.extract (ByteArray.empty.size - header.windowSize.toNat)
              ByteArray.empty.size
       else ByteArray.empty)
      #[1, 4, 8] header.windowSize.toNat
      = .ok (blockOutput1, newHist1) := by
    simp only [ByteArray.size_empty, Nat.not_lt_zero, decide_false, Bool.and_false]
    exact hexec1
  -- Compute the exact block loop result
  have hblocks := decompressBlocksWF_compressed_seq_then_rle data afterHeader
    header.windowSize ByteArray.empty none {} #[1, 4, 8] hdr1 afterHdr1
    literals1 afterLiterals1 huffTree1 numSeq1 modes1 afterSeqHeader1
    llTable1 ofTable1 mlTable1 afterTables1 bbr1 sequences1 blockOutput1 newHist1
    hdr2 afterHdr2 block2 afterByte2
    hoff hparse1 hbs1 hws1 htype1 hblockEnd1 hlit1 hseq1 hNumSeq1 hfse1 hbbr1
    hdec1 hexec1' hnotlast1 hadv1
    hoff2 hparse2 hbs2 hws2 htype2 hrle2 hlast2
  frame_from_blocks

/-! ## decompressFrame compressed two-block content -/

/-- When `decompressFrame` succeeds on a frame containing two compressed blocks
    (both with numSeq=0, i.e. literals only), the output equals `literals1 ++ literals2`.
    Lifts `decompressBlocksWF_two_compressed_literals_blocks` to frame level. -/
theorem decompressFrame_two_compressed_literals_blocks_content (data : ByteArray)
    (pos : Nat) (output : ByteArray) (pos' : Nat)
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
    (hframe : Zip.Native.decompressFrame data pos = .ok (output, pos'))
    (hh : Zip.Native.parseFrameHeader data pos = .ok (header, afterHeader))
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
    (hlast2 : hdr2.lastBlock = true) :
    output = literals1 ++ literals2 := by
  have hoff := parseBlockHeader_data_not_le data afterHeader hdr1 afterHdr1 hparse1
  -- Compute the exact block loop result using step + single-block theorems
  have hblocks : Zip.Native.decompressBlocksWF data afterHeader header.windowSize
      ByteArray.empty none {} #[1, 4, 8]
      = .ok (ByteArray.empty ++ literals1 ++ literals2,
             afterHdr2 + hdr2.blockSize.toNat) := by
    rw [decompressBlocksWF_compressed_literals_only_step data afterHeader header.windowSize
      ByteArray.empty none {} #[1, 4, 8] hdr1 afterHdr1 literals1 afterLiterals1 huffTree1
      modes1 afterSeqHeader1 hoff hparse1 hbs1 hws1 htype1 hblockEnd1 hlit1 hseq1
      hnotlast1 hadv1]
    cases huffTree1 with
    | none =>
      exact decompressBlocksWF_single_compressed_literals_only data
        (afterHdr1 + hdr1.blockSize.toNat) header.windowSize (ByteArray.empty ++ literals1)
        none {} #[1, 4, 8]
        hdr2 afterHdr2 literals2 afterLiterals2 huffTree2 modes2 afterSeqHeader2
        hoff2 hparse2 hbs2 hws2 htype2 hblockEnd2 hlit2 hseq2 hlast2
    | some ht =>
      exact decompressBlocksWF_single_compressed_literals_only data
        (afterHdr1 + hdr1.blockSize.toNat) header.windowSize (ByteArray.empty ++ literals1)
        (some ht) {} #[1, 4, 8]
        hdr2 afterHdr2 literals2 afterLiterals2 huffTree2 modes2 afterSeqHeader2
        hoff2 hparse2 hbs2 hws2 htype2 hblockEnd2 hlit2 hseq2 hlast2
  frame_from_blocks

/-- When `decompressFrame` succeeds on a frame containing two compressed blocks
    (both with numSeq > 0, i.e. using sequences), the output equals
    `blockOutput1 ++ blockOutput2`. Block 2 receives the updated Huffman table,
    replaced FSE tables, updated offset history, and extended output from block 1.
    Lifts `decompressBlocksWF_two_compressed_sequences_blocks` to frame level.

    Inlines `decompressBlocksWF_compressed_sequences_step` +
    `decompressBlocksWF_single_compressed_sequences` at the frame level to avoid
    dependent-type mismatch with the composition theorem's Huffman threading. -/
theorem decompressFrame_two_compressed_sequences_blocks_content (data : ByteArray)
    (pos : Nat) (output : ByteArray) (pos' : Nat)
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
    (hframe : Zip.Native.decompressFrame data pos = .ok (output, pos'))
    (hh : Zip.Native.parseFrameHeader data pos = .ok (header, afterHeader))
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
    (hlast2 : hdr2.lastBlock = true) :
    output = blockOutput1 ++ blockOutput2 := by
  have hoff := parseBlockHeader_data_not_le data afterHeader hdr1 afterHdr1 hparse1
  -- Bridge executeSequences for block 1: frame starts with empty output,
  -- so window check is trivial
  have hexec1' : Zip.Native.executeSequences sequences1 literals1
      (if header.windowSize > 0 && ByteArray.empty.size > header.windowSize.toNat
       then ByteArray.empty.extract (ByteArray.empty.size - header.windowSize.toNat)
              ByteArray.empty.size
       else ByteArray.empty)
      #[1, 4, 8] header.windowSize.toNat
      = .ok (blockOutput1, newHist1) := by
    simp only [ByteArray.size_empty, Nat.not_lt_zero, decide_false, Bool.and_false]
    exact hexec1
  -- Bridge executeSequences for block 2: block-loop uses (ByteArray.empty ++ blockOutput1)
  -- as the window reference, convert to blockOutput1 directly
  have hexec2' : Zip.Native.executeSequences sequences2 literals2
      (if header.windowSize > 0 &&
           (ByteArray.empty ++ blockOutput1).size > header.windowSize.toNat
       then (ByteArray.empty ++ blockOutput1).extract
              ((ByteArray.empty ++ blockOutput1).size - header.windowSize.toNat)
              (ByteArray.empty ++ blockOutput1).size
       else ByteArray.empty ++ blockOutput1)
      newHist1 header.windowSize.toNat
      = .ok (blockOutput2, newHist2) := by
    simp only [ByteArray.empty_append]
    exact hexec2
  -- Reduce block 1 (compSeq step) then apply block 2 (single compSeq).
  -- We inline the two-step proof to avoid dependent-type mismatch with the
  -- composition theorem's elaboration of `if let` in hlit2.
  have hblocks : Zip.Native.decompressBlocksWF data afterHeader header.windowSize
      ByteArray.empty none {} #[1, 4, 8]
      = .ok (ByteArray.empty ++ blockOutput1 ++ blockOutput2,
             afterHdr2 + hdr2.blockSize.toNat) := by
    rw [decompressBlocksWF_compressed_sequences_step data afterHeader header.windowSize
      ByteArray.empty none {} #[1, 4, 8] hdr1 afterHdr1
      literals1 afterLiterals1 huffTree1 numSeq1 modes1 afterSeqHeader1
      llTable1 ofTable1 mlTable1 afterTables1 bbr1 sequences1 blockOutput1 newHist1
      hoff hparse1 hbs1 hws1 htype1 hblockEnd1 hlit1 hseq1 hNumSeq1 hfse1 hbbr1
      hdec1 hexec1' hnotlast1 hadv1]
    exact decompressBlocksWF_single_compressed_sequences data
      (afterHdr1 + hdr1.blockSize.toNat) header.windowSize (ByteArray.empty ++ blockOutput1)
      _ { litLen := some llTable1, offset := some ofTable1, matchLen := some mlTable1 }
      newHist1
      hdr2 afterHdr2 literals2 afterLiterals2 huffTree2 numSeq2 modes2 afterSeqHeader2
      llTable2 ofTable2 mlTable2 afterTables2 bbr2 sequences2 blockOutput2 newHist2
      hoff2 hparse2 hbs2 hws2 htype2 hblockEnd2
      (by cases huffTree1 <;> exact hlit2) hseq2 hNumSeq2 hfse2 hbbr2
      hdec2 hexec2' hlast2
  frame_from_blocks

/-! ## decompressFrame raw/RLE + compressed-sequences two-block content -/

/-- When `decompressFrame` succeeds and the frame contains a non-last raw block
    followed by a last compressed block with numSeq>0 (sequences), the output
    equals `block1 ++ blockOutput2`. The raw block contributes `block1` directly;
    the compressed-sequences block produces `blockOutput2` via sequence execution.
    Raw blocks don't modify Huffman/FSE state, so block 2 receives the initial
    `none`/`{}` state. -/
theorem decompressFrame_raw_then_compressed_seq_content (data : ByteArray)
    (pos : Nat) (output : ByteArray) (pos' : Nat)
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
    (hframe : Zip.Native.decompressFrame data pos = .ok (output, pos'))
    (hh : Zip.Native.parseFrameHeader data pos = .ok (header, afterHeader))
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
    (hlast2 : hdr2.lastBlock = true) :
    output = block1 ++ blockOutput2 := by
  have hoff := parseBlockHeader_data_not_le data afterHeader hdr1 afterHdr1 hparse1
  -- Bridge executeSequences: frame starts with empty output, so window uses block1 directly
  have hexec2' : Zip.Native.executeSequences sequences2 literals2
      (if header.windowSize > 0 && (ByteArray.empty ++ block1).size > header.windowSize.toNat
       then (ByteArray.empty ++ block1).extract
         ((ByteArray.empty ++ block1).size - header.windowSize.toNat)
         (ByteArray.empty ++ block1).size
       else ByteArray.empty ++ block1)
      #[1, 4, 8] header.windowSize.toNat
      = .ok (blockOutput2, newHist2) := by
    simp only [ByteArray.empty_append]
    exact hexec2
  -- Compute the exact block loop result
  have hblocks := decompressBlocksWF_raw_then_compressed_sequences data afterHeader
    header.windowSize ByteArray.empty none {} #[1, 4, 8] hdr1 afterHdr1
    block1 afterBlock1
    hdr2 afterHdr2 literals2 afterLiterals2 huffTree2 numSeq2 modes2 afterSeqHeader2
    llTable2 ofTable2 mlTable2 afterTables2 bbr2 sequences2 blockOutput2 newHist2
    hoff hparse1 hbs1 hws1 htype1 hraw1 hnotlast1 hadv1
    hoff2 hparse2 hbs2 hws2 htype2 hblockEnd2 hlit2 hseq2 hNumSeq2 hfse2 hbbr2
    hdec2 hexec2' hlast2
  frame_from_blocks

/-- When `decompressFrame` succeeds and the frame contains a non-last RLE block
    followed by a last compressed block with numSeq>0 (sequences), the output
    equals `block1 ++ blockOutput2`. The RLE block contributes `block1` directly;
    the compressed-sequences block produces `blockOutput2` via sequence execution.
    RLE blocks don't modify Huffman/FSE state, so block 2 receives the initial
    `none`/`{}` state. -/
theorem decompressFrame_rle_then_compressed_seq_content (data : ByteArray)
    (pos : Nat) (output : ByteArray) (pos' : Nat)
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
    (hframe : Zip.Native.decompressFrame data pos = .ok (output, pos'))
    (hh : Zip.Native.parseFrameHeader data pos = .ok (header, afterHeader))
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
    (hlast2 : hdr2.lastBlock = true) :
    output = block1 ++ blockOutput2 := by
  have hoff := parseBlockHeader_data_not_le data afterHeader hdr1 afterHdr1 hparse1
  -- Bridge executeSequences: frame starts with empty output, so window uses block1 directly
  have hexec2' : Zip.Native.executeSequences sequences2 literals2
      (if header.windowSize > 0 && (ByteArray.empty ++ block1).size > header.windowSize.toNat
       then (ByteArray.empty ++ block1).extract
         ((ByteArray.empty ++ block1).size - header.windowSize.toNat)
         (ByteArray.empty ++ block1).size
       else ByteArray.empty ++ block1)
      #[1, 4, 8] header.windowSize.toNat
      = .ok (blockOutput2, newHist2) := by
    simp only [ByteArray.empty_append]
    exact hexec2
  -- Compute the exact block loop result
  have hblocks := decompressBlocksWF_rle_then_compressed_sequences data afterHeader
    header.windowSize ByteArray.empty none {} #[1, 4, 8] hdr1 afterHdr1
    block1 afterByte1
    hdr2 afterHdr2 literals2 afterLiterals2 huffTree2 numSeq2 modes2 afterSeqHeader2
    llTable2 ofTable2 mlTable2 afterTables2 bbr2 sequences2 blockOutput2 newHist2
    hoff hparse1 hbs1 hws1 htype1 hrle1 hnotlast1 hadv1
    hoff2 hparse2 hbs2 hws2 htype2 hblockEnd2 hlit2 hseq2 hNumSeq2 hfse2 hbbr2
    hdec2 hexec2' hlast2
  frame_from_blocks

end Zstd.Spec
