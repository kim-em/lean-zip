import Zip.Spec.ZstdTwoBlock

/-!
# Zstandard Frame Success Theorems

Frame-level completeness theorems (`decompressFrame_succeeds_*`) for all
block-type combinations: single compressed, raw/RLE + compressed,
compressed + raw/RLE, and compressed + compressed pairs.

See `Zip/Spec/ZstdContent.lean` for content characterization theorems.
See `Zip/Spec/Zstd.lean` for the unified `decompressFrame_succeeds_of_well_formed`.
-/

-- Unfold monadic `Except` bind/pure in hypothesis `h`.
-- Duplicated from ZstdBase.lean because `local macro` is file-scoped.
set_option hygiene false in
local macro "unfold_except" : tactic =>
  `(tactic| simp only [bind, Except.bind, pure, Except.pure] at h)

-- Unfold `decompressFrame`, substitute `hh` (parseFrameHeader result) and `hblocks`
-- (block-loop result), then handle the dictionary check and close both branches with grind.
-- Duplicated from ZstdBase.lean because `local macro` is file-scoped.
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
  obtain ⟨result, blockPos, hblocks⟩ := decompressBlocksWF_succeeds_single_compressed_zero_seq
    data afterHeader header.windowSize ByteArray.empty none {} #[1, 4, 8]
    literals afterLiterals huffTree modes afterSeqHeader
    hsize htypeVal hlastBit hblockSize hwindow hblockEnd hlit hseq
  unfold Zip.Native.decompressFrame
  simp only [bind, Except.bind, pure, Except.pure, hparse, hnodict]
  unfold Zip.Native.decompressBlocks
  rw [hblocks]
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
  -- Convert hexec to match block-level form (if-guard simplifies for empty output)
  have hexec' : Zip.Native.executeSequences sequences literals
      (if header.windowSize > 0 && ByteArray.empty.size > header.windowSize.toNat
       then ByteArray.empty.extract (ByteArray.empty.size - header.windowSize.toNat)
         ByteArray.empty.size
       else ByteArray.empty)
      #[1, 4, 8] header.windowSize.toNat = .ok (blockOutput, newHist) := by
    simp only [ByteArray.size_empty, Nat.not_lt_zero, decide_false, Bool.and_false,
      Bool.false_eq_true, ↓reduceIte]; exact hexec
  obtain ⟨result, blockPos, hblocks⟩ := decompressBlocksWF_succeeds_single_compressed_sequences
    data afterHeader header.windowSize ByteArray.empty none {} #[1, 4, 8]
    literals afterLiterals huffTree numSeq modes afterSeqHeader
    llTable ofTable mlTable afterTables bbr sequences blockOutput newHist
    hsize htypeVal hlastBit hblockSize hwindow hblockEnd hlit hseq hNumSeq hfse hbbr hdec hexec'
  unfold Zip.Native.decompressFrame
  simp only [bind, Except.bind, pure, Except.pure, hparse, hnodict]
  unfold Zip.Native.decompressBlocks
  rw [hblocks]
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
  obtain ⟨result, blockPos, hblocks⟩ := decompressBlocksWF_succeeds_raw_then_compressed_zero_seq
    data afterHeader off2 header.windowSize ByteArray.empty none {} #[1, 4, 8]
    literals afterLiterals huffTree modes afterSeqHeader
    hsize1 htypeVal1 hlastBit1 hblockSize1 hwindow1 hpayload1 hoff2
    hsize2 htypeVal2 hlastBit2 hblockSize2 hwindow2 hblockEnd2 hlit2 hseq2
  unfold Zip.Native.decompressFrame
  simp only [bind, Except.bind, pure, Except.pure, hparse, hnodict]
  unfold Zip.Native.decompressBlocks
  rw [hblocks]
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
  obtain ⟨result, blockPos, hblocks⟩ := decompressBlocksWF_succeeds_rle_then_compressed_zero_seq
    data afterHeader off2 header.windowSize ByteArray.empty none {} #[1, 4, 8]
    literals afterLiterals huffTree modes afterSeqHeader
    hsize1 htypeVal1 hlastBit1 hblockSize1 hwindow1 hpayload1 hoff2
    hsize2 htypeVal2 hlastBit2 hblockSize2 hwindow2 hblockEnd2 hlit2 hseq2
  unfold Zip.Native.decompressFrame
  simp only [bind, Except.bind, pure, Except.pure, hparse, hnodict]
  unfold Zip.Native.decompressBlocks
  rw [hblocks]
  simp only [hnocksum, hnosize, Bool.false_eq_true, ↓reduceIte]
  exact ⟨_, _, rfl⟩

/-! ## decompressFrame two-block "succeeds" (raw/RLE + compressed sequences) -/

/-- When a frame contains a non-last raw block followed by a last compressed block
    with numSeq > 0 (full sequence pipeline), with no dictionary, no content checksum,
    and no declared content size, `decompressFrame` succeeds. Composes
    `parseFrameHeader` success with
    `decompressBlocksWF_succeeds_raw_then_compressed_sequences` and threads through
    the frame-level dictionary/checksum/size guards. -/
theorem decompressFrame_succeeds_raw_then_compressed_sequences (data : ByteArray) (pos : Nat)
    (header : Zip.Native.ZstdFrameHeader) (afterHeader : Nat)
    (block1 : ByteArray)
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
    (off2 : Nat)
    (hraw1 : Zip.Native.decompressRawBlock data (afterHeader + 3)
        ((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
          ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3)
        = .ok (block1, off2))
    -- Block 2 (last compressed, with sequences) at off2
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
               (if header.windowSize > 0 && (ByteArray.empty ++ block1).size > header.windowSize.toNat
                then (ByteArray.empty ++ block1).extract
                  ((ByteArray.empty ++ block1).size - header.windowSize.toNat)
                  (ByteArray.empty ++ block1).size
                else ByteArray.empty ++ block1)
               #[1, 4, 8] header.windowSize.toNat
               = .ok (blockOutput2, newHist2)) :
    ∃ content pos',
      Zip.Native.decompressFrame data pos = .ok (content, pos') := by
  -- Step 1: Get block-level success from byte-level conditions
  obtain ⟨result, blockPos, hblocks⟩ := decompressBlocksWF_succeeds_raw_then_compressed_sequences
    data afterHeader off2 header.windowSize ByteArray.empty none {} #[1, 4, 8]
    block1 literals2 afterLiterals2 huffTree2 numSeq2 modes2 afterSeqHeader2
    llTable2 ofTable2 mlTable2 afterTables2 bbr2 sequences2 blockOutput2 newHist2
    hsize1 htypeVal1 hlastBit1 hblockSize1 hwindow1 hraw1
    hsize2 htypeVal2 hlastBit2 hblockSize2 hwindow2 hblockEnd2 hlit2 hseq2 hNumSeq2
    hfse2 hbbr2 hdec2 hexec2
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
    with numSeq > 0 (full sequence pipeline), with no dictionary, no content checksum,
    and no declared content size, `decompressFrame` succeeds. Composes
    `parseFrameHeader` success with
    `decompressBlocksWF_succeeds_rle_then_compressed_sequences` and threads through
    the frame-level dictionary/checksum/size guards. -/
theorem decompressFrame_succeeds_rle_then_compressed_sequences (data : ByteArray) (pos : Nat)
    (header : Zip.Native.ZstdFrameHeader) (afterHeader : Nat)
    (block1 : ByteArray)
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
    (off2 : Nat)
    (hrle1 : Zip.Native.decompressRLEBlock data (afterHeader + 3)
        ((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
          ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3)
        = .ok (block1, off2))
    -- Block 2 (last compressed, with sequences) at off2
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
               (if header.windowSize > 0 && (ByteArray.empty ++ block1).size > header.windowSize.toNat
                then (ByteArray.empty ++ block1).extract
                  ((ByteArray.empty ++ block1).size - header.windowSize.toNat)
                  (ByteArray.empty ++ block1).size
                else ByteArray.empty ++ block1)
               #[1, 4, 8] header.windowSize.toNat
               = .ok (blockOutput2, newHist2)) :
    ∃ content pos',
      Zip.Native.decompressFrame data pos = .ok (content, pos') := by
  -- Step 1: Get block-level success from byte-level conditions
  obtain ⟨result, blockPos, hblocks⟩ := decompressBlocksWF_succeeds_rle_then_compressed_sequences
    data afterHeader off2 header.windowSize ByteArray.empty none {} #[1, 4, 8]
    block1 literals2 afterLiterals2 huffTree2 numSeq2 modes2 afterSeqHeader2
    llTable2 ofTable2 mlTable2 afterTables2 bbr2 sequences2 blockOutput2 newHist2
    hsize1 htypeVal1 hlastBit1 hblockSize1 hwindow1 hrle1
    hsize2 htypeVal2 hlastBit2 hblockSize2 hwindow2 hblockEnd2 hlit2 hseq2 hNumSeq2
    hfse2 hbbr2 hdec2 hexec2
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
  obtain ⟨result, blockPos, hblocks⟩ := decompressBlocksWF_succeeds_compressed_zero_seq_then_raw
    data afterHeader off2 header.windowSize ByteArray.empty none {} #[1, 4, 8]
    literals afterLiterals huffTree modes afterSeqHeader
    hsize1 htypeVal1 hlastBit1 hblockSize1 hwindow1 hblockEnd1 hlit1 hseq1 hoff2
    hsize2 htypeVal2 hlastBit2 hblockSize2 hwindow2 hpayload2
  unfold Zip.Native.decompressFrame
  simp only [bind, Except.bind, pure, Except.pure, hparse, hnodict]
  unfold Zip.Native.decompressBlocks
  rw [hblocks]
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
  obtain ⟨result, blockPos, hblocks⟩ := decompressBlocksWF_succeeds_compressed_zero_seq_then_rle
    data afterHeader off2 header.windowSize ByteArray.empty none {} #[1, 4, 8]
    literals afterLiterals huffTree modes afterSeqHeader
    hsize1 htypeVal1 hlastBit1 hblockSize1 hwindow1 hblockEnd1 hlit1 hseq1 hoff2
    hsize2 htypeVal2 hlastBit2 hblockSize2 hwindow2 hpayload2
  unfold Zip.Native.decompressFrame
  simp only [bind, Except.bind, pure, Except.pure, hparse, hnodict]
  unfold Zip.Native.decompressBlocks
  rw [hblocks]
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
  obtain ⟨result, blockPos, hblocks⟩ := decompressBlocksWF_succeeds_compressed_sequences_then_raw
    data afterHeader off2 header.windowSize ByteArray.empty none {} #[1, 4, 8]
    literals afterLiterals huffTree numSeq modes afterSeqHeader
    llTable ofTable mlTable afterTables bbr sequences blockOutput1 newHist1
    hsize1 htypeVal1 hlastBit1 hblockSize1 hwindow1 hblockEnd1 hlit1 hseq1 hNumSeq1
    hfse1 hbbr1 hdec1 hexec1 hoff2
    hsize2 htypeVal2 hlastBit2 hblockSize2 hwindow2 hpayload2
  unfold Zip.Native.decompressFrame
  simp only [bind, Except.bind, pure, Except.pure, hparse, hnodict]
  unfold Zip.Native.decompressBlocks
  rw [hblocks]
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
  obtain ⟨result, blockPos, hblocks⟩ := decompressBlocksWF_succeeds_compressed_sequences_then_rle
    data afterHeader off2 header.windowSize ByteArray.empty none {} #[1, 4, 8]
    literals afterLiterals huffTree numSeq modes afterSeqHeader
    llTable ofTable mlTable afterTables bbr sequences blockOutput1 newHist1
    hsize1 htypeVal1 hlastBit1 hblockSize1 hwindow1 hblockEnd1 hlit1 hseq1 hNumSeq1
    hfse1 hbbr1 hdec1 hexec1 hoff2
    hsize2 htypeVal2 hlastBit2 hblockSize2 hwindow2 hpayload2
  unfold Zip.Native.decompressFrame
  simp only [bind, Except.bind, pure, Except.pure, hparse, hnodict]
  unfold Zip.Native.decompressBlocks
  rw [hblocks]
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

end Zstd.Spec
