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
  · simp only [bind, Except.bind, pure, Except.pure] at h
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
  · simp only [bind, Except.bind, pure, Except.pure] at h
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
  · simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    · obtain ⟨rfl, rfl⟩ := h; rfl
    · obtain ⟨rfl, rfl⟩ := h; rfl
    · obtain ⟨rfl, rfl⟩ := h; rfl
    · exact nomatch h

/-! ## Block decompression correctness -/

/-- When `decompressRawBlock` succeeds, the output has exactly `blockSize` bytes. -/
theorem decompressRawBlock_size (data : ByteArray) (pos : Nat)
    (blockSize : UInt32) (result : ByteArray) (pos' : Nat)
    (h : Zip.Native.decompressRawBlock data pos blockSize = .ok (result, pos')) :
    result.size = blockSize.toNat := by
  unfold Zip.Native.decompressRawBlock at h
  simp only [bind, Except.bind, pure, Except.pure] at h
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
  simp only [bind, Except.bind, pure, Except.pure] at h
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
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · exact nomatch h
  · obtain ⟨rfl, rfl⟩ := h
    rw [ByteArray.getElem_eq_getElem_data, Array.getElem_replicate]

end Zstd.Spec
