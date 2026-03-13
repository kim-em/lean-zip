import Zip.Spec.ZstdTwoBlockFrame

/-!
# Zstandard Two-Block Compressed Completeness

Compressed block content characterization, `WellFormedBlocks` induction predicate
for all block types, and all two-block completeness theorems involving compressed
blocks (compressed+raw/RLE, raw/RLE+compressed, compressed+compressed).

Frame-level theorems for simple blocks are in `Zip/Spec/ZstdTwoBlockFrame.lean`.
-/

namespace Zstd.Spec

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

/-! ## WellFormedBlocks induction predicate (all block types) -/

/-- An inductive predicate encoding a sequence of blocks of any type (raw, RLE,
    compressed zero-seq, compressed sequences), each satisfying the hypotheses of
    the existing step/base theorems. Unlike `WellFormedSimpleBlocks`, compressed
    block constructors thread updated Huffman table, FSE tables, and offset history
    through the recursive `rest`, enabling heterogeneous block sequences. -/
inductive WellFormedBlocks (data : ByteArray) :
    Nat → UInt64 → ByteArray →
    Option Zip.Native.ZstdHuffmanTable →
    Zip.Native.PrevFseTables → Array Nat → Prop where
  | last_raw (off windowSize output prevHuff prevFse history
      hdr afterHdr block afterBlock :_)
      (hoff : ¬ data.size ≤ off)
      (hparse : Zip.Native.parseBlockHeader data off = .ok (hdr, afterHdr))
      (hbs : ¬ hdr.blockSize > 131072)
      (hws : ¬ (windowSize > 0 && hdr.blockSize.toUInt64 > windowSize))
      (htype : hdr.blockType = .raw)
      (hraw : Zip.Native.decompressRawBlock data afterHdr hdr.blockSize = .ok (block, afterBlock))
      (hlast : hdr.lastBlock = true) :
      WellFormedBlocks data off windowSize output prevHuff prevFse history
  | last_rle (off windowSize output prevHuff prevFse history
      hdr afterHdr block afterByte :_)
      (hoff : ¬ data.size ≤ off)
      (hparse : Zip.Native.parseBlockHeader data off = .ok (hdr, afterHdr))
      (hbs : ¬ hdr.blockSize > 131072)
      (hws : ¬ (windowSize > 0 && hdr.blockSize.toUInt64 > windowSize))
      (htype : hdr.blockType = .rle)
      (hrle : Zip.Native.decompressRLEBlock data afterHdr hdr.blockSize = .ok (block, afterByte))
      (hlast : hdr.lastBlock = true) :
      WellFormedBlocks data off windowSize output prevHuff prevFse history
  | last_compressed_zero_seq (off windowSize output prevHuff prevFse history
      hdr afterHdr literals afterLiterals huffTree
      modes afterSeqHeader :_)
      (hoff : ¬ data.size ≤ off)
      (hparse : Zip.Native.parseBlockHeader data off = .ok (hdr, afterHdr))
      (hbs : ¬ hdr.blockSize > 131072)
      (hws : ¬ (windowSize > 0 && hdr.blockSize.toUInt64 > windowSize))
      (htype : hdr.blockType = .compressed)
      (hblockEnd : ¬ data.size < afterHdr + hdr.blockSize.toNat)
      (hlit : Zip.Native.parseLiteralsSection data afterHdr prevHuff
        = .ok (literals, afterLiterals, huffTree))
      (hseq : Zip.Native.parseSequencesHeader data afterLiterals
        = .ok (0, modes, afterSeqHeader))
      (hlast : hdr.lastBlock = true) :
      WellFormedBlocks data off windowSize output prevHuff prevFse history
  | last_compressed_sequences (off windowSize output prevHuff prevFse history
      hdr afterHdr literals afterLiterals huffTree
      numSeq modes afterSeqHeader
      llTable ofTable mlTable afterTables
      bbr sequences blockOutput newHist :_)
      (hoff : ¬ data.size ≤ off)
      (hparse : Zip.Native.parseBlockHeader data off = .ok (hdr, afterHdr))
      (hbs : ¬ hdr.blockSize > 131072)
      (hws : ¬ (windowSize > 0 && hdr.blockSize.toUInt64 > windowSize))
      (htype : hdr.blockType = .compressed)
      (hblockEnd : ¬ data.size < afterHdr + hdr.blockSize.toNat)
      (hlit : Zip.Native.parseLiteralsSection data afterHdr prevHuff
                = .ok (literals, afterLiterals, huffTree))
      (hseq : Zip.Native.parseSequencesHeader data afterLiterals
                = .ok (numSeq, modes, afterSeqHeader))
      (hNumSeq : ¬ numSeq == 0)
      (hfse : Zip.Native.resolveSequenceFseTables modes data afterSeqHeader prevFse
                = .ok (llTable, ofTable, mlTable, afterTables))
      (hbbr : Zip.Native.BackwardBitReader.init data afterTables (afterHdr + hdr.blockSize.toNat)
                = .ok bbr)
      (hdec : Zip.Native.decodeSequences llTable ofTable mlTable bbr numSeq
                = .ok sequences)
      (hexec : Zip.Native.executeSequences sequences literals
                 (if windowSize > 0 && output.size > windowSize.toNat
                  then output.extract (output.size - windowSize.toNat) output.size
                  else output)
                 history windowSize.toNat
                 = .ok (blockOutput, newHist))
      (hlast : hdr.lastBlock = true) :
      WellFormedBlocks data off windowSize output prevHuff prevFse history
  | step_raw (off windowSize output prevHuff prevFse history
      hdr afterHdr block afterBlock :_)
      (hoff : ¬ data.size ≤ off)
      (hparse : Zip.Native.parseBlockHeader data off = .ok (hdr, afterHdr))
      (hbs : ¬ hdr.blockSize > 131072)
      (hws : ¬ (windowSize > 0 && hdr.blockSize.toUInt64 > windowSize))
      (htype : hdr.blockType = .raw)
      (hraw : Zip.Native.decompressRawBlock data afterHdr hdr.blockSize = .ok (block, afterBlock))
      (hnotlast : hdr.lastBlock = false)
      (hadv : ¬ afterBlock ≤ off)
      (rest : WellFormedBlocks data afterBlock windowSize
        (output ++ block) prevHuff prevFse history) :
      WellFormedBlocks data off windowSize output prevHuff prevFse history
  | step_rle (off windowSize output prevHuff prevFse history
      hdr afterHdr block afterByte :_)
      (hoff : ¬ data.size ≤ off)
      (hparse : Zip.Native.parseBlockHeader data off = .ok (hdr, afterHdr))
      (hbs : ¬ hdr.blockSize > 131072)
      (hws : ¬ (windowSize > 0 && hdr.blockSize.toUInt64 > windowSize))
      (htype : hdr.blockType = .rle)
      (hrle : Zip.Native.decompressRLEBlock data afterHdr hdr.blockSize = .ok (block, afterByte))
      (hnotlast : hdr.lastBlock = false)
      (hadv : ¬ afterByte ≤ off)
      (rest : WellFormedBlocks data afterByte windowSize
        (output ++ block) prevHuff prevFse history) :
      WellFormedBlocks data off windowSize output prevHuff prevFse history
  | step_compressed_zero_seq (off windowSize output prevHuff prevFse history
      hdr afterHdr literals afterLiterals huffTree
      modes afterSeqHeader :_)
      (hoff : ¬ data.size ≤ off)
      (hparse : Zip.Native.parseBlockHeader data off = .ok (hdr, afterHdr))
      (hbs : ¬ hdr.blockSize > 131072)
      (hws : ¬ (windowSize > 0 && hdr.blockSize.toUInt64 > windowSize))
      (htype : hdr.blockType = .compressed)
      (hblockEnd : ¬ data.size < afterHdr + hdr.blockSize.toNat)
      (hlit : Zip.Native.parseLiteralsSection data afterHdr prevHuff
        = .ok (literals, afterLiterals, huffTree))
      (hseq : Zip.Native.parseSequencesHeader data afterLiterals
        = .ok (0, modes, afterSeqHeader))
      (hnotlast : hdr.lastBlock = false)
      (hadv : ¬ afterHdr + hdr.blockSize.toNat ≤ off)
      (rest : WellFormedBlocks data (afterHdr + hdr.blockSize.toNat) windowSize
        (output ++ literals)
        (if let some ht := huffTree then some ht else prevHuff)
        prevFse history) :
      WellFormedBlocks data off windowSize output prevHuff prevFse history
  | step_compressed_sequences (off windowSize output prevHuff prevFse history
      hdr afterHdr literals afterLiterals huffTree
      numSeq modes afterSeqHeader
      llTable ofTable mlTable afterTables
      bbr sequences blockOutput newHist :_)
      (hoff : ¬ data.size ≤ off)
      (hparse : Zip.Native.parseBlockHeader data off = .ok (hdr, afterHdr))
      (hbs : ¬ hdr.blockSize > 131072)
      (hws : ¬ (windowSize > 0 && hdr.blockSize.toUInt64 > windowSize))
      (htype : hdr.blockType = .compressed)
      (hblockEnd : ¬ data.size < afterHdr + hdr.blockSize.toNat)
      (hlit : Zip.Native.parseLiteralsSection data afterHdr prevHuff
                = .ok (literals, afterLiterals, huffTree))
      (hseq : Zip.Native.parseSequencesHeader data afterLiterals
                = .ok (numSeq, modes, afterSeqHeader))
      (hNumSeq : ¬ numSeq == 0)
      (hfse : Zip.Native.resolveSequenceFseTables modes data afterSeqHeader prevFse
                = .ok (llTable, ofTable, mlTable, afterTables))
      (hbbr : Zip.Native.BackwardBitReader.init data afterTables (afterHdr + hdr.blockSize.toNat)
                = .ok bbr)
      (hdec : Zip.Native.decodeSequences llTable ofTable mlTable bbr numSeq
                = .ok sequences)
      (hexec : Zip.Native.executeSequences sequences literals
                 (if windowSize > 0 && output.size > windowSize.toNat
                  then output.extract (output.size - windowSize.toNat) output.size
                  else output)
                 history windowSize.toNat
                 = .ok (blockOutput, newHist))
      (hnotlast : hdr.lastBlock = false)
      (hadv : ¬ (afterHdr + hdr.blockSize.toNat) ≤ off)
      (rest : WellFormedBlocks data (afterHdr + hdr.blockSize.toNat) windowSize
        (output ++ blockOutput)
        (if let some ht := huffTree then some ht else prevHuff)
        { litLen := some llTable, offset := some ofTable, matchLen := some mlTable }
        newHist) :
      WellFormedBlocks data off windowSize output prevHuff prevFse history

/-- `decompressBlocksWF` succeeds on any well-formed sequence of blocks (raw, RLE,
    compressed zero-seq, or compressed sequences). This subsumes all specific N-block
    completeness theorems across all block types. -/
theorem decompressBlocksWF_succeeds_of_well_formed
    (data : ByteArray) (off : Nat) (windowSize : UInt64)
    (output : ByteArray) (prevHuff : Option Zip.Native.ZstdHuffmanTable)
    (prevFse : Zip.Native.PrevFseTables) (history : Array Nat)
    (hwf : WellFormedBlocks data off windowSize output prevHuff prevFse history) :
    ∃ result pos',
      Zip.Native.decompressBlocksWF data off windowSize output prevHuff prevFse history
        = .ok (result, pos') := by
  induction hwf with
  | last_raw off windowSize output prevHuff prevFse history
      hdr afterHdr block afterBlock hoff hparse hbs hws htype hraw hlast =>
    exact ⟨_, _, decompressBlocksWF_single_raw data off windowSize output prevHuff prevFse
      history hdr afterHdr block afterBlock hoff hparse hbs hws htype hraw hlast⟩
  | last_rle off windowSize output prevHuff prevFse history
      hdr afterHdr block afterByte hoff hparse hbs hws htype hrle hlast =>
    exact ⟨_, _, decompressBlocksWF_single_rle data off windowSize output prevHuff prevFse
      history hdr afterHdr block afterByte hoff hparse hbs hws htype hrle hlast⟩
  | last_compressed_zero_seq off windowSize output prevHuff prevFse history
      hdr afterHdr literals afterLiterals huffTree modes afterSeqHeader
      hoff hparse hbs hws htype hblockEnd hlit hseq hlast =>
    exact ⟨_, _, decompressBlocksWF_single_compressed_literals_only data off windowSize output
      prevHuff prevFse history hdr afterHdr literals afterLiterals huffTree modes afterSeqHeader
      hoff hparse hbs hws htype hblockEnd hlit hseq hlast⟩
  | last_compressed_sequences off windowSize output prevHuff prevFse history
      hdr afterHdr literals afterLiterals huffTree numSeq modes afterSeqHeader
      llTable ofTable mlTable afterTables bbr sequences blockOutput newHist
      hoff hparse hbs hws htype hblockEnd hlit hseq hNumSeq hfse hbbr hdec hexec hlast =>
    exact ⟨_, _, decompressBlocksWF_single_compressed_sequences data off windowSize output
      prevHuff prevFse history hdr afterHdr literals afterLiterals huffTree numSeq modes
      afterSeqHeader llTable ofTable mlTable afterTables bbr sequences blockOutput newHist
      hoff hparse hbs hws htype hblockEnd hlit hseq hNumSeq hfse hbbr hdec hexec hlast⟩
  | step_raw off windowSize output prevHuff prevFse history
      hdr afterHdr block afterBlock hoff hparse hbs hws htype hraw hnotlast hadv _rest ih =>
    rw [decompressBlocksWF_raw_step data off windowSize output prevHuff prevFse history
      hdr afterHdr block afterBlock hoff hparse hbs hws htype hraw hnotlast hadv]
    exact ih
  | step_rle off windowSize output prevHuff prevFse history
      hdr afterHdr block afterByte hoff hparse hbs hws htype hrle hnotlast hadv _rest ih =>
    rw [decompressBlocksWF_rle_step data off windowSize output prevHuff prevFse history
      hdr afterHdr block afterByte hoff hparse hbs hws htype hrle hnotlast hadv]
    exact ih
  | step_compressed_zero_seq off windowSize output prevHuff prevFse history
      hdr afterHdr literals afterLiterals huffTree modes afterSeqHeader
      hoff hparse hbs hws htype hblockEnd hlit hseq hnotlast hadv _rest ih =>
    rw [decompressBlocksWF_compressed_literals_only_step data off windowSize output prevHuff
      prevFse history hdr afterHdr literals afterLiterals huffTree modes afterSeqHeader
      hoff hparse hbs hws htype hblockEnd hlit hseq hnotlast hadv]
    exact ih
  | step_compressed_sequences off windowSize output prevHuff prevFse history
      hdr afterHdr literals afterLiterals huffTree numSeq modes afterSeqHeader
      llTable ofTable mlTable afterTables bbr sequences blockOutput newHist
      hoff hparse hbs hws htype hblockEnd hlit hseq hNumSeq hfse hbbr hdec hexec
      hnotlast hadv _rest ih =>
    rw [decompressBlocksWF_compressed_sequences_step data off windowSize output prevHuff
      prevFse history hdr afterHdr literals afterLiterals huffTree numSeq modes afterSeqHeader
      llTable ofTable mlTable afterTables bbr sequences blockOutput newHist
      hoff hparse hbs hws htype hblockEnd hlit hseq hNumSeq hfse hbbr hdec hexec hnotlast hadv]
    exact ih

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

/-! ## decompressBlocksWF two-block composed completeness (raw/RLE + compressed sequences) -/

/-- When a non-last raw block at `off` is followed by a last compressed block with
    numSeq > 0 (full sequence pipeline) at `off2`, `decompressBlocksWF` succeeds.
    Composes `decompressBlocksWF_raw_step` with
    `decompressBlocksWF_succeeds_single_compressed_sequences` using byte-level
    preconditions for block 1 header. The `block1` parameter and `hraw1` hypothesis
    determine the raw block output, which appears in `hexec2`'s window context
    because `executeSequences` for block 2 depends on the accumulated output. -/
theorem decompressBlocksWF_succeeds_raw_then_compressed_sequences (data : ByteArray)
    (off off2 : Nat) (windowSize : UInt64) (output : ByteArray)
    (prevHuff : Option Zip.Native.ZstdHuffmanTable)
    (prevFse : Zip.Native.PrevFseTables) (history : Array Nat)
    (block1 : ByteArray)
    (literals2 : ByteArray) (afterLiterals2 : Nat)
    (huffTree2 : Option Zip.Native.ZstdHuffmanTable)
    (numSeq2 : Nat) (modes2 : Zip.Native.SequenceCompressionModes) (afterSeqHeader2 : Nat)
    (llTable2 ofTable2 mlTable2 : Zip.Native.FseTable) (afterTables2 : Nat)
    (bbr2 : Zip.Native.BackwardBitReader)
    (sequences2 : Array Zip.Native.ZstdSequence)
    (blockOutput2 : ByteArray) (newHist2 : Array Nat)
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
    (hraw1 : Zip.Native.decompressRawBlock data (off + 3)
        ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
          ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3)
        = .ok (block1, off2))
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
    (hlit2 : Zip.Native.parseLiteralsSection data (off2 + 3) prevHuff
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
               (if windowSize > 0 && (output ++ block1).size > windowSize.toNat
                then (output ++ block1).extract
                  ((output ++ block1).size - windowSize.toNat) (output ++ block1).size
                else output ++ block1)
               history windowSize.toNat
               = .ok (blockOutput2, newHist2)) :
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
  -- Block 1: rewrite hraw1 to use parsed blockSize and position
  have hraw1' : Zip.Native.decompressRawBlock data afterHdr1 hdr1.blockSize
      = .ok (block1, off2) := by
    rw [← hbs_eq1, ← hpos_eq1] at hraw1; exact hraw1
  have hoff1 : ¬ data.size ≤ off := by omega
  have hRawPos := decompressRawBlock_pos_eq data afterHdr1 hdr1.blockSize block1 off2 hraw1'
  have hadv1 : ¬ off2 ≤ off := by rw [hRawPos, hpos_eq1]; omega
  -- Step through block 1, then apply succeeds_single_compressed_sequences for block 2
  rw [decompressBlocksWF_raw_step data off windowSize output prevHuff prevFse history
    hdr1 afterHdr1 block1 off2 hoff1 hparse1 hbs1 hws1 htype1 hraw1' hnotlast1 hadv1]
  exact decompressBlocksWF_succeeds_single_compressed_sequences data off2 windowSize
    (output ++ block1) prevHuff prevFse history literals2 afterLiterals2 huffTree2 numSeq2 modes2
    afterSeqHeader2 llTable2 ofTable2 mlTable2 afterTables2 bbr2 sequences2 blockOutput2
    newHist2 hsize2 htypeVal2 hlastBit2 hblockSize2 hwindow2 hblockEnd2 hlit2 hseq2 hNumSeq2
    hfse2 hbbr2 hdec2 hexec2

/-- When a non-last RLE block at `off` is followed by a last compressed block with
    numSeq > 0 (full sequence pipeline) at `off2`, `decompressBlocksWF` succeeds.
    Composes `decompressBlocksWF_rle_step` with
    `decompressBlocksWF_succeeds_single_compressed_sequences` using byte-level
    preconditions for block 1 header. The `block1` parameter and `hrle1` hypothesis
    determine the RLE block output, which appears in `hexec2`'s window context
    because `executeSequences` for block 2 depends on the accumulated output. -/
theorem decompressBlocksWF_succeeds_rle_then_compressed_sequences (data : ByteArray)
    (off off2 : Nat) (windowSize : UInt64) (output : ByteArray)
    (prevHuff : Option Zip.Native.ZstdHuffmanTable)
    (prevFse : Zip.Native.PrevFseTables) (history : Array Nat)
    (block1 : ByteArray)
    (literals2 : ByteArray) (afterLiterals2 : Nat)
    (huffTree2 : Option Zip.Native.ZstdHuffmanTable)
    (numSeq2 : Nat) (modes2 : Zip.Native.SequenceCompressionModes) (afterSeqHeader2 : Nat)
    (llTable2 ofTable2 mlTable2 : Zip.Native.FseTable) (afterTables2 : Nat)
    (bbr2 : Zip.Native.BackwardBitReader)
    (sequences2 : Array Zip.Native.ZstdSequence)
    (blockOutput2 : ByteArray) (newHist2 : Array Nat)
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
    (hrle1 : Zip.Native.decompressRLEBlock data (off + 3)
        ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
          ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3)
        = .ok (block1, off2))
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
    (hlit2 : Zip.Native.parseLiteralsSection data (off2 + 3) prevHuff
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
               (if windowSize > 0 && (output ++ block1).size > windowSize.toNat
                then (output ++ block1).extract
                  ((output ++ block1).size - windowSize.toNat) (output ++ block1).size
                else output ++ block1)
               history windowSize.toNat
               = .ok (blockOutput2, newHist2)) :
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
  -- Block 1: rewrite hrle1 to use parsed blockSize and position
  have hrle1' : Zip.Native.decompressRLEBlock data afterHdr1 hdr1.blockSize
      = .ok (block1, off2) := by
    rw [← hbs_eq1, ← hpos_eq1] at hrle1; exact hrle1
  have hoff1 : ¬ data.size ≤ off := by omega
  have hRlePos := decompressRLEBlock_pos_eq data afterHdr1 hdr1.blockSize block1 off2 hrle1'
  have hadv1 : ¬ off2 ≤ off := by rw [hRlePos, hpos_eq1]; omega
  -- Step through block 1, then apply succeeds_single_compressed_sequences for block 2
  rw [decompressBlocksWF_rle_step data off windowSize output prevHuff prevFse history
    hdr1 afterHdr1 block1 off2 hoff1 hparse1 hbs1 hws1 htype1 hrle1' hnotlast1 hadv1]
  exact decompressBlocksWF_succeeds_single_compressed_sequences data off2 windowSize
    (output ++ block1) prevHuff prevFse history literals2 afterLiterals2 huffTree2 numSeq2 modes2
    afterSeqHeader2 llTable2 ofTable2 mlTable2 afterTables2 bbr2 sequences2 blockOutput2
    newHist2 hsize2 htypeVal2 hlastBit2 hblockSize2 hwindow2 hblockEnd2 hlit2 hseq2 hNumSeq2
    hfse2 hbbr2 hdec2 hexec2

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
  -- Case split huffTree1 to reduce the if-let match in hlit2
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
  -- Case split huffTree1 to reduce the if-let match in hlit2
  cases huffTree1 <;> exact decompressBlocksWF_succeeds_single_compressed_sequences data _
    windowSize (output ++ blockOutput1) _ _ newHist1 literals2 afterLiterals2 huffTree2 numSeq2
    modes2 afterSeqHeader2 llTable2 ofTable2 mlTable2 afterTables2 bbr2 sequences2 blockOutput2
    newHist2 hsize2 htypeVal2 hlastBit2 hblockSize2 hwindow2 hblockEnd2 hlit2 hseq2 hNumSeq2
    hfse2 hbbr2 hdec2 hexec2


end Zstd.Spec
