import Zip.Spec.ZstdTwoBlock

/-!
# Zstandard Frame Specification (RFC 8878) — Frame-Level Theorems

This file contains frame-level completeness and content characterization
theorems for Zstd decompression.

Step theorems, induction predicates, and block-level two-block completeness
are in `Zip/Spec/ZstdTwoBlock.lean` (L3).
Base definitions and predicates are in `Zip/Spec/ZstdBase.lean` (L1).
Block-loop structural lemmas are in `Zip/Spec/ZstdBlockLoop.lean` (L2).
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
