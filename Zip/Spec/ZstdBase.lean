import Zip.Native.ZstdFrame
import Std.Tactic.BVDecide

/-!
# Zstandard Frame Specification — Base Definitions (RFC 8878)

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

Split from `Zip/Spec/Zstd.lean` for file-size management.  This file
contains predicates, instances, and basic correctness theorems (L1).
Block-loop structural lemmas live in `Zip/Spec/ZstdBlockLoop.lean` (L2).
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
    -- typeVal cases: 0→raw, 1→rle, 2→compressed share the same proof; catch-all is absurd
    <;> first
      | (obtain ⟨rfl, rfl⟩ := h; exact fun h => nomatch h)
      | exact nomatch h

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
    split at h <;> first
      | (obtain ⟨rfl, rfl⟩ := h; exact raw24_shiftRight3_lt ..)
      | exact nomatch h

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
    split at h <;> first | (obtain ⟨rfl, rfl⟩ := h; rfl) | exact nomatch h

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
  · simp only [getElem!_pos data pos (by omega)]
    obtain ⟨rfl, rfl⟩ := h
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
  simp only [dif_neg (show ¬(data.size < pos + 3) from by omega),
    bind, Except.bind, pure, Except.pure]
  -- The match on typeVal has branches for 0, 1, 2, and the catch-all (reserved).
  -- htypeVal eliminates the catch-all, so one of the first three branches applies.
  -- Normalize data[pos]! to data[pos] so bv_decide sees consistent terms.
  rw [getElem!_pos data pos (by omega), getElem!_pos data (pos + 1) (by omega),
    getElem!_pos data (pos + 2) (by omega)] at htypeVal
  split
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩
  · -- Catch-all: typeVal ∉ {0,1,2} from split, and ≠ 3 from htypeVal.
    -- But typeVal = expr &&& 3 can only be 0-3, contradiction.
    exfalso; rename_i _ h0 h1 h2
    generalize data[pos] = b0 at *
    generalize data[pos + 1] = b1 at *
    generalize data[pos + 2] = b2 at *
    bv_decide

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
  simp only [dif_neg (show ¬(data.size < pos + 1) from by omega)]
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
  · simp only [getElem!_pos data pos (by omega), getElem!_pos data (pos + 1) (by omega),
      getElem!_pos data (pos + 2) (by omega)]
    split at h <;> first | (obtain ⟨rfl, rfl⟩ := h; rfl) | exact nomatch h

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
  · simp only [getElem!_pos data pos (by omega), getElem!_pos data (pos + 1) (by omega),
      getElem!_pos data (pos + 2) (by omega)]
    split at h <;> first
      | (obtain ⟨rfl, rfl⟩ := h; grind)
      | exact nomatch h

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
  · simp only [getElem!_pos data pos (by omega), getElem!_pos data (pos + 1) (by omega),
      getElem!_pos data (pos + 2) (by omega)]
    split at h <;> first | (obtain ⟨rfl, rfl⟩ := h; rfl) | exact nomatch h

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

end Zstd.Spec
