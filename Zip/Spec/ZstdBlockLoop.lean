import Zip.Spec.ZstdBase

/-!
# Block loop structural lemmas

Structural properties of `decompressBlocksWF`: output growth, prefix
preservation, position advancement, bounds, single-block content, and
composed completeness for single raw/RLE blocks at both the block-loop
and frame level.

Split from `Zip/Spec/Zstd.lean` (L2 section) for file-size management.
-/

-- Unfold monadic `Except` bind/pure in hypothesis `h`.
-- Duplicated from ZstdBase.lean because `local macro` is file-scoped.
set_option hygiene false in
local macro "unfold_except" : tactic =>
  `(tactic| simp only [bind, Except.bind, pure, Except.pure] at h)

namespace Zstd.Spec

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

end Zstd.Spec
