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

/-- When `decompressRawBlock` succeeds, the returned position is `pos + blockSize.toNat`.
    The raw block consumes exactly `blockSize` bytes from the input. -/
theorem decompressRawBlock_pos_eq (data : ByteArray) (pos : Nat)
    (blockSize : UInt32) (result : ByteArray) (pos' : Nat)
    (h : Zip.Native.decompressRawBlock data pos blockSize = .ok (result, pos')) :
    pos' = pos + blockSize.toNat := by
  unfold Zip.Native.decompressRawBlock at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · exact nomatch h
  · obtain ⟨rfl, rfl⟩ := h; rfl

/-- When `decompressRLEBlock` succeeds, the returned position is `pos + 1`.
    The RLE block consumes exactly 1 byte from the input (the repeated byte). -/
theorem decompressRLEBlock_pos_eq (data : ByteArray) (pos : Nat)
    (blockSize : UInt32) (result : ByteArray) (pos' : Nat)
    (h : Zip.Native.decompressRLEBlock data pos blockSize = .ok (result, pos')) :
    pos' = pos + 1 := by
  unfold Zip.Native.decompressRLEBlock at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · exact nomatch h
  · obtain ⟨rfl, rfl⟩ := h; rfl

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
      simp only [bind, Except.bind, pure, Except.pure] at h
      split at h
      · exact nomatch h
      · obtain ⟨rfl, rfl⟩ := h; simp [ByteArray.size_extract] at hi; omega) := by
  unfold Zip.Native.decompressRawBlock at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · exact nomatch h
  · obtain ⟨rfl, rfl⟩ := h
    simp [ByteArray.getElem_extract]

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
  dsimp only [Bind.bind, Except.bind, pure, Except.pure] at h
  -- Substitute contentSize = some n to resolve the contentSize match
  simp only [hn] at h
  -- Thread through all remaining guards (dictionary, decompressBlocks, checksum)
  -- All paths end with: if (v.fst.size.toUInt64 != n) then throw else .ok (v.fst, ...)
  -- Since h says the result is .ok, the content size guard passed
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
  dsimp only [Bind.bind, Except.bind, pure, Except.pure] at h
  -- Substitute contentChecksum = true to resolve the checksum conditionals
  simp only [hc] at h
  -- Thread through all remaining guards (dictionary, decompressBlocks, data size, checksum !=)
  -- Since h says the result is .ok, the checksum guard passed
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
  simp only [bind, Except.bind, pure, Except.pure] at h
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
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · exact nomatch h
  · rename_i hoff
    split at h
    · exact nomatch h  -- parseBlockHeader error
    · -- parseBlockHeader ok
      split at h
      · exact nomatch h  -- blockSize > 131072
      · split at h
        · exact nomatch h  -- windowSize guard
        · split at h  -- blockType match
          · -- raw
            split at h
            · exact nomatch h  -- decompressRawBlock error
            · split at h  -- lastBlock
              · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
                simp only [ByteArray.size_append]; omega
              · split at h  -- position guard
                · exact nomatch h
                · have ih := decompressBlocksWF_output_size_ge _ _ _ _ _ _ _ _ _ h
                  simp only [ByteArray.size_append] at ih; omega
          · -- rle
            split at h
            · exact nomatch h
            · split at h
              · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
                simp only [ByteArray.size_append]; omega
              · split at h
                · exact nomatch h
                · have ih := decompressBlocksWF_output_size_ge _ _ _ _ _ _ _ _ _ h
                  simp only [ByteArray.size_append] at ih; omega
          · -- compressed: many sub-operations (parseLiteralsSection, parseSequencesHeader, etc.)
            -- All paths produce output ++ something
            split at h  -- parseLiteralsSection
            · exact nomatch h
            · split at h  -- parseSequencesHeader
              · exact nomatch h
              · split at h  -- numSeq == 0 check
                · -- numSeq == 0: output ++ literals
                  split at h  -- lastBlock
                  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
                    simp only [ByteArray.size_append]; omega
                  · split at h
                    · exact nomatch h
                    · have ih := decompressBlocksWF_output_size_ge _ _ _ _ _ _ _ _ _ h
                      simp only [ByteArray.size_append] at ih; omega
                · -- numSeq > 0: resolveSequenceFseTables, decodeSequences, executeSequences
                  split at h  -- resolveSequenceFseTables
                  · exact nomatch h
                  · split at h  -- BackwardBitReader.init
                    · exact nomatch h
                    · split at h  -- decodeSequences
                      · exact nomatch h
                      · split at h  -- executeSequences
                        · exact nomatch h
                        · split at h  -- lastBlock
                          · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
                            simp only [ByteArray.size_append]; omega
                          · split at h
                            · exact nomatch h
                            · have ih := decompressBlocksWF_output_size_ge _ _ _ _ _ _ _ _ _ h
                              simp only [ByteArray.size_append] at ih; omega
          · exact nomatch h  -- reserved
  termination_by data.size - off
  decreasing_by all_goals omega

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
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · exact nomatch h
  · rename_i hoff
    split at h
    · exact nomatch h  -- parseBlockHeader error
    · -- parseBlockHeader ok
      split at h
      · exact nomatch h  -- blockSize > 131072
      · split at h
        · exact nomatch h  -- windowSize guard
        · split at h  -- blockType match
          · -- raw
            split at h
            · exact nomatch h
            · split at h  -- lastBlock
              · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
                have h1 := parseBlockHeader_pos_eq _ _ _ _ (by assumption)
                have h2 := decompressRawBlock_pos_eq _ _ _ _ _ (by assumption)
                omega
              · split at h
                · exact nomatch h
                · have ih := decompressBlocksWF_pos_gt _ _ _ _ _ _ _ _ _ h
                  omega
          · -- rle
            split at h
            · exact nomatch h
            · split at h
              · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
                have h1 := parseBlockHeader_pos_eq _ _ _ _ (by assumption)
                have h2 := decompressRLEBlock_pos_eq _ _ _ _ _ (by assumption)
                omega
              · split at h
                · exact nomatch h
                · have ih := decompressBlocksWF_pos_gt _ _ _ _ _ _ _ _ _ h
                  omega
          · -- compressed
            split at h
            · exact nomatch h
            · split at h
              · exact nomatch h
              · split at h
                · -- numSeq == 0
                  split at h
                  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
                    have h1 := parseBlockHeader_pos_eq _ _ _ _ (by assumption)
                    omega
                  · split at h
                    · exact nomatch h
                    · have ih := decompressBlocksWF_pos_gt _ _ _ _ _ _ _ _ _ h
                      omega
                · -- numSeq > 0
                  split at h
                  · exact nomatch h
                  · split at h
                    · exact nomatch h
                    · split at h
                      · exact nomatch h
                      · split at h
                        · exact nomatch h
                        · split at h
                          · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
                            have h1 := parseBlockHeader_pos_eq _ _ _ _ (by assumption)
                            omega
                          · split at h
                            · exact nomatch h
                            · have ih := decompressBlocksWF_pos_gt _ _ _ _ _ _ _ _ _ h
                              omega
          · exact nomatch h  -- reserved
  termination_by data.size - off
  decreasing_by all_goals omega

/-! ## Frame header position advancement -/

/-- When `parseFrameHeader` succeeds, the returned position is strictly greater
    than the input position. The header is at least 6 bytes (4 magic + 1
    descriptor + at least 1 byte for window descriptor or content size). -/
theorem parseFrameHeader_pos_gt (data : ByteArray) (pos : Nat)
    (header : Zip.Native.ZstdFrameHeader) (pos' : Nat)
    (h : Zip.Native.parseFrameHeader data pos = .ok (header, pos')) :
    pos' > pos := by
  unfold Zip.Native.parseFrameHeader at h
  dsimp only [Bind.bind, Except.bind] at h
  by_cases h1 : data.size < pos + 4
  · rw [if_pos h1] at h; exact nomatch h
  · rw [if_neg h1] at h
    simp only [pure, Pure.pure] at h
    by_cases h2 : (Binary.readUInt32LE data pos != Zip.Native.zstdMagic) = true
    · rw [if_pos h2] at h; exact nomatch h
    · rw [if_neg h2] at h
      -- Guard 3: descriptor size check
      by_cases h3 : data.size < pos + 4 + 1
      · rw [if_pos h3] at h; exact nomatch h
      · rw [if_neg h3] at h
        -- Branch: first top-level split
        split at h
        · exact nomatch h  -- error path
        · -- Reduce residual `match Except.ok v✝` patterns (unexpanded binds)
          simp only [Except.pure] at h
          repeat split at h
          -- Process remaining goals: close errors, split residual if/match
          iterate 5 (all_goals (try (first | contradiction | (split at h))))
          all_goals first
            | contradiction
            | (simp only [Except.ok.injEq, Prod.mk.injEq] at h
               obtain ⟨-, rfl⟩ := h; omega)

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
        grind

end Zstd.Spec
