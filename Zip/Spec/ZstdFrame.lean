import Zip.Spec.ZstdFrameBase

/-!
# Zstandard Top-Level Decompressor — Composed Completeness

Composed completeness theorems for `decompressZstd`, building on the
foundations in `ZstdFrameBase`. Contains:
- Composed completeness for compressed blocks (zero-seq and with-sequences)
- Composed completeness for raw/RLE-first two-block frames
- Composed completeness for compressed-first two-block frames
- Unified completeness via `WellFormedSimpleBlocks` predicate
-/

namespace Zip.Spec.ZstdFrame

/-! ## decompressZstd composed completeness for compressed blocks -/

/-- End-to-end composed completeness for a single compressed-block frame with zero
    sequences (literals only): byte-level conditions on the frame header, block header,
    and parsing conditions imply `decompressZstd` succeeds.

    Composes the full chain:
    1. `parseFrameHeader_succeeds` (byte-level magic + size → frame header parsed)
    2. `decompressFrame_succeeds_single_compressed_zero_seq` (header + block → frame success)
    3. `decompressZstd_single_frame` (frame success + end-of-data → API success)

    Header field constraints and block conditions are universally quantified over
    `(hdr, afterHdr)` from `parseFrameHeader`, since the caller doesn't know these
    values without parsing. -/
theorem decompressZstd_succeeds_single_compressed_zero_seq_frame (data : ByteArray)
    -- Frame header conditions (from parseFrameHeader_succeeds)
    (hmagic : Binary.readUInt32LE data 0 = Zip.Native.zstdMagic)
    (hframeSize : data.size ≥ Zstd.Spec.frameHeaderMinSize data[4]!)
    -- Header field constraints (universally quantified over parseFrameHeader result)
    (hnodict : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.dictionaryId = none)
    (hnocksum : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.contentChecksum = false)
    (hnosize : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.contentSize = none)
    -- Block conditions at afterHdr (compressed block: type=2, lastBlock=1)
    (htypeVal : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 2)
    (hlastBit : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → (data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) &&& 1 = 1)
    (hblockSizeBound : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → ¬ (hdr.windowSize > 0 &&
            ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > hdr.windowSize))
    (hblockEnd : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    -- Literals section and sequences header succeed (quantified, with existentials)
    (hparsing : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ∃ literals afterLiterals huffTree modes afterSeqHeader,
            Zip.Native.parseLiteralsSection data (afterHdr + 3) none
              = .ok (literals, afterLiterals, huffTree) ∧
            Zip.Native.parseSequencesHeader data afterLiterals
              = .ok (0, modes, afterSeqHeader))
    -- Frame terminates the data
    (hterm : ∀ content pos', Zip.Native.decompressFrame data 0 = .ok (content, pos')
        → pos' ≥ data.size) :
    ∃ output, Zip.Native.decompressZstd data = .ok output := by
  -- Step 1: Obtain header from parseFrameHeader_succeeds
  obtain ⟨hdr, afterHdr, hparse⟩ :=
    Zstd.Spec.parseFrameHeader_succeeds data 0 hmagic (by simpa only [Nat.zero_add] using hframeSize)
  -- Step 2: Specialize universally quantified hypotheses
  have htypeVal' := htypeVal hdr afterHdr hparse
  have hlastBit' := hlastBit hdr afterHdr hparse
  have hblockSizeBound' := hblockSizeBound hdr afterHdr hparse
  have hwindow' := hwindow hdr afterHdr hparse
  have hblockEnd' := hblockEnd hdr afterHdr hparse
  -- Step 3: Obtain literals and sequences parsing from combined hypothesis
  obtain ⟨literals, afterLiterals, huffTree, modes, afterSeqHeader, hlit', hseq'⟩ :=
    hparsing hdr afterHdr hparse
  -- Step 4: Apply decompressFrame_succeeds_single_compressed_zero_seq
  obtain ⟨content, pos', hframe⟩ := Zstd.Spec.decompressFrame_succeeds_single_compressed_zero_seq
    data 0 hdr afterHdr literals afterLiterals huffTree modes afterSeqHeader
    hparse (hnodict hdr afterHdr hparse) (hnocksum hdr afterHdr hparse)
    (hnosize hdr afterHdr hparse) (by omega) htypeVal' hlastBit' hblockSizeBound'
    hwindow' hblockEnd' hlit' hseq'
  -- Step 5: Apply decompressZstd_single_frame
  exact ⟨content, decompressZstd_single_frame data content pos' hframe (hterm content pos' hframe)⟩

/-- End-to-end composed completeness for a single compressed-block frame with sequences
    (numSeq > 0): byte-level conditions on the frame header, block header, and full
    parsing/decoding/execution pipeline imply `decompressZstd` succeeds.

    Same structure as `decompressZstd_succeeds_single_compressed_zero_seq_frame` but
    with additional conditions for FSE table resolution, backward bitstream
    initialization, sequence decoding, and sequence execution.

    Composes the full chain:
    1. `parseFrameHeader_succeeds` (byte-level magic + size → frame header parsed)
    2. `decompressFrame_succeeds_single_compressed_sequences` (header + block + sequences → frame)
    3. `decompressZstd_single_frame` (frame success + end-of-data → API success) -/
theorem decompressZstd_succeeds_single_compressed_sequences_frame (data : ByteArray)
    -- Frame header conditions (from parseFrameHeader_succeeds)
    (hmagic : Binary.readUInt32LE data 0 = Zip.Native.zstdMagic)
    (hframeSize : data.size ≥ Zstd.Spec.frameHeaderMinSize data[4]!)
    -- Header field constraints (universally quantified over parseFrameHeader result)
    (hnodict : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.dictionaryId = none)
    (hnocksum : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.contentChecksum = false)
    (hnosize : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.contentSize = none)
    -- Block conditions at afterHdr (compressed block: type=2, lastBlock=1)
    (htypeVal : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 2)
    (hlastBit : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → (data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) &&& 1 = 1)
    (hblockSizeBound : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → ¬ (hdr.windowSize > 0 &&
            ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > hdr.windowSize))
    (hblockEnd : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    -- Full parsing/decoding/execution pipeline (quantified, with existentials)
    (hparsing : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → ∃ literals afterLiterals huffTree numSeq modes afterSeqHeader
            llTable ofTable mlTable afterTables bbr sequences blockOutput newHist,
            Zip.Native.parseLiteralsSection data (afterHdr + 3) none
              = .ok (literals, afterLiterals, huffTree) ∧
            Zip.Native.parseSequencesHeader data afterLiterals
              = .ok (numSeq, modes, afterSeqHeader) ∧
            ¬ (numSeq == 0) ∧
            Zip.Native.resolveSequenceFseTables modes data afterSeqHeader {}
              = .ok (llTable, ofTable, mlTable, afterTables) ∧
            Zip.Native.BackwardBitReader.init data afterTables
              (afterHdr + 3 + (((data[afterHdr]!.toUInt32
                ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
                ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
              = .ok bbr ∧
            Zip.Native.decodeSequences llTable ofTable mlTable bbr numSeq
              = .ok sequences ∧
            Zip.Native.executeSequences sequences literals ByteArray.empty #[1, 4, 8]
              hdr.windowSize.toNat = .ok (blockOutput, newHist))
    -- Frame terminates the data
    (hterm : ∀ content pos', Zip.Native.decompressFrame data 0 = .ok (content, pos')
        → pos' ≥ data.size) :
    ∃ output, Zip.Native.decompressZstd data = .ok output := by
  -- Step 1: Obtain header from parseFrameHeader_succeeds
  obtain ⟨hdr, afterHdr, hparse⟩ :=
    Zstd.Spec.parseFrameHeader_succeeds data 0 hmagic (by simpa only [Nat.zero_add] using hframeSize)
  -- Step 2: Specialize universally quantified hypotheses
  have htypeVal' := htypeVal hdr afterHdr hparse
  have hlastBit' := hlastBit hdr afterHdr hparse
  have hblockSizeBound' := hblockSizeBound hdr afterHdr hparse
  have hwindow' := hwindow hdr afterHdr hparse
  have hblockEnd' := hblockEnd hdr afterHdr hparse
  -- Step 3: Obtain full pipeline from combined hypothesis
  obtain ⟨literals, afterLiterals, huffTree, numSeq, modes, afterSeqHeader,
    llTable, ofTable, mlTable, afterTables, bbr, sequences, blockOutput, newHist,
    hlit', hseq', hNumSeq', hfse', hbbr', hdec', hexec'⟩ := hparsing hdr afterHdr hparse
  -- Step 4: Apply decompressFrame_succeeds_single_compressed_sequences
  obtain ⟨content, pos', hframe⟩ := Zstd.Spec.decompressFrame_succeeds_single_compressed_sequences
    data 0 hdr afterHdr literals afterLiterals huffTree numSeq modes afterSeqHeader
    llTable ofTable mlTable afterTables bbr sequences blockOutput newHist
    hparse (hnodict hdr afterHdr hparse) (hnocksum hdr afterHdr hparse)
    (hnosize hdr afterHdr hparse) (by omega) htypeVal' hlastBit' hblockSizeBound'
    hwindow' hblockEnd' hlit' hseq' hNumSeq' hfse' hbbr' hdec' hexec'
  -- Step 5: Apply decompressZstd_single_frame
  exact ⟨content, decompressZstd_single_frame data content pos' hframe (hterm content pos' hframe)⟩

/-! ## decompressZstd composed completeness for raw/RLE blocks -/

/-- End-to-end composed completeness for a single raw-block frame: byte-level conditions
    on the frame header and block header imply `decompressZstd` succeeds.

    Composes the full chain:
    1. `parseFrameHeader_succeeds` (byte-level magic + size → frame header parsed)
    2. `decompressFrame_succeeds_single_raw` (frame header + block conditions → frame success)
    3. `decompressZstd_single_frame` (frame success + end-of-data → API success)

    The header field constraints and block conditions are universally quantified over
    `(hdr, afterHdr)` from `parseFrameHeader`, since the caller doesn't know these values
    without parsing. The termination hypothesis `hterm` states that the frame fills all
    remaining data — this cannot be derived from byte-level conditions without a separate
    characterization of `decompressFrame`'s output position. -/
theorem decompressZstd_succeeds_single_raw_frame (data : ByteArray)
    -- Frame header conditions (from parseFrameHeader_succeeds)
    (hmagic : Binary.readUInt32LE data 0 = Zip.Native.zstdMagic)
    (hframeSize : data.size ≥ Zstd.Spec.frameHeaderMinSize data[4]!)
    -- Header field constraints (universally quantified over parseFrameHeader result)
    (hnodict : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.dictionaryId = none)
    (hnocksum : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.contentChecksum = false)
    (hnosize : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.contentSize = none)
    -- Block conditions at afterHdr (byte-level raw block: type=0, lastBlock=1)
    (htypeVal : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 0)
    (hlastBit : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → (data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) &&& 1 = 1)
    (hblockSizeBound : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → ¬ (hdr.windowSize > 0 &&
            ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > hdr.windowSize))
    (hpayload : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    -- Frame terminates the data (for decompressZstdWF recursion termination)
    (hterm : ∀ content pos', Zip.Native.decompressFrame data 0 = .ok (content, pos')
        → pos' ≥ data.size) :
    ∃ output, Zip.Native.decompressZstd data = .ok output := by
  -- Step 1: Obtain header from parseFrameHeader_succeeds
  obtain ⟨hdr, afterHdr, hparse⟩ :=
    Zstd.Spec.parseFrameHeader_succeeds data 0 hmagic (by simpa only [Nat.zero_add] using hframeSize)
  -- Step 2: Specialize universally quantified hypotheses
  have htypeVal' := htypeVal hdr afterHdr hparse
  have hlastBit' := hlastBit hdr afterHdr hparse
  have hblockSizeBound' := hblockSizeBound hdr afterHdr hparse
  have hwindow' := hwindow hdr afterHdr hparse
  have hpayload' := hpayload hdr afterHdr hparse
  -- Step 3: Apply decompressFrame_succeeds_single_raw
  obtain ⟨content, pos', hframe⟩ := Zstd.Spec.decompressFrame_succeeds_single_raw
    data 0 hdr afterHdr hparse (hnodict hdr afterHdr hparse) (hnocksum hdr afterHdr hparse)
    (hnosize hdr afterHdr hparse) (by omega) htypeVal' hlastBit' hblockSizeBound' hwindow' hpayload'
  -- Step 4: Apply decompressZstd_single_frame
  exact ⟨content, decompressZstd_single_frame data content pos' hframe (hterm content pos' hframe)⟩

/-- End-to-end composed completeness for a single RLE-block frame: byte-level conditions
    on the frame header and block header imply `decompressZstd` succeeds.

    Same structure as `decompressZstd_succeeds_single_raw_frame` but for RLE blocks
    (block type = 1). RLE blocks need only 1 byte of payload (the repeated byte),
    so `hpayload` requires `afterHdr + 4` instead of `afterHdr + 3 + blockSize`. -/
theorem decompressZstd_succeeds_single_rle_frame (data : ByteArray)
    -- Frame header conditions (from parseFrameHeader_succeeds)
    (hmagic : Binary.readUInt32LE data 0 = Zip.Native.zstdMagic)
    (hframeSize : data.size ≥ Zstd.Spec.frameHeaderMinSize data[4]!)
    -- Header field constraints (universally quantified over parseFrameHeader result)
    (hnodict : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.dictionaryId = none)
    (hnocksum : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.contentChecksum = false)
    (hnosize : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.contentSize = none)
    -- Block conditions at afterHdr (byte-level RLE block: type=1, lastBlock=1)
    (htypeVal : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 1)
    (hlastBit : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → (data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) &&& 1 = 1)
    (hblockSizeBound : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → ¬ (hdr.windowSize > 0 &&
            ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > hdr.windowSize))
    (hpayload : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ afterHdr + 4)
    -- Frame terminates the data (for decompressZstdWF recursion termination)
    (hterm : ∀ content pos', Zip.Native.decompressFrame data 0 = .ok (content, pos')
        → pos' ≥ data.size) :
    ∃ output, Zip.Native.decompressZstd data = .ok output := by
  -- Step 1: Obtain header from parseFrameHeader_succeeds
  obtain ⟨hdr, afterHdr, hparse⟩ :=
    Zstd.Spec.parseFrameHeader_succeeds data 0 hmagic (by simpa only [Nat.zero_add] using hframeSize)
  -- Step 2: Specialize universally quantified hypotheses
  have htypeVal' := htypeVal hdr afterHdr hparse
  have hlastBit' := hlastBit hdr afterHdr hparse
  have hblockSizeBound' := hblockSizeBound hdr afterHdr hparse
  have hwindow' := hwindow hdr afterHdr hparse
  have hpayload' := hpayload hdr afterHdr hparse
  -- Step 3: Apply decompressFrame_succeeds_single_rle
  obtain ⟨content, pos', hframe⟩ := Zstd.Spec.decompressFrame_succeeds_single_rle
    data 0 hdr afterHdr hparse (hnodict hdr afterHdr hparse) (hnocksum hdr afterHdr hparse)
    (hnosize hdr afterHdr hparse) (by omega) htypeVal' hlastBit' hblockSizeBound' hwindow' hpayload'
  -- Step 4: Apply decompressZstd_single_frame
  exact ⟨content, decompressZstd_single_frame data content pos' hframe (hterm content pos' hframe)⟩

/-! ## decompressZstd two-block composed completeness (rle first block) -/

/-- End-to-end composed completeness for a two-RLE-block frame: byte-level conditions
    on the frame header and both block headers imply `decompressZstd` succeeds.

    Composes the full chain:
    1. `parseFrameHeader_succeeds` (byte-level magic + size → frame header parsed)
    2. `decompressFrame_succeeds_two_rle_blocks` (header + two RLE blocks → frame)
    3. `decompressZstd_single_frame` (frame success + end-of-data → API success) -/
theorem decompressZstd_succeeds_two_rle_frame (data : ByteArray)
    -- Frame header conditions (from parseFrameHeader_succeeds)
    (hmagic : Binary.readUInt32LE data 0 = Zip.Native.zstdMagic)
    (hframeSize : data.size ≥ Zstd.Spec.frameHeaderMinSize data[4]!)
    -- Header field constraints (universally quantified over parseFrameHeader result)
    (hnodict : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.dictionaryId = none)
    (hnocksum : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.contentChecksum = false)
    (hnosize : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.contentSize = none)
    -- Block 1 (non-last RLE) at afterHdr
    (hsize1 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ afterHdr + 3)
    (htypeVal1 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 1)
    (hlastBit1 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → (data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) &&& 1 = 0)
    (hblockSize1 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow1 : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → ¬ (hdr.windowSize > 0 &&
            ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > hdr.windowSize))
    (hpayload1 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ afterHdr + 4)
    -- Block 2 (last RLE) at off2 = afterHdr + 4
    (hsize2 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ (afterHdr + 4) + 3)
    (htypeVal2 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr + 4]!.toUInt32 ||| (data[afterHdr + 4 + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 4 + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 1)
    (hlastBit2 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → (data[afterHdr + 4]!.toUInt32 ||| (data[afterHdr + 4 + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 4 + 2]!.toUInt32 <<< 16)) &&& 1 = 1)
    (hblockSize2 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr + 4]!.toUInt32 ||| (data[afterHdr + 4 + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 4 + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow2 : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → ¬ (hdr.windowSize > 0 &&
            ((data[afterHdr + 4]!.toUInt32 ||| (data[afterHdr + 4 + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 4 + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > hdr.windowSize))
    (hpayload2 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ (afterHdr + 4) + 4)
    -- Frame terminates the data
    (hterm : ∀ content pos', Zip.Native.decompressFrame data 0 = .ok (content, pos')
        → pos' ≥ data.size) :
    ∃ output, Zip.Native.decompressZstd data = .ok output := by
  -- Step 1: Obtain header from parseFrameHeader_succeeds
  obtain ⟨hdr, afterHdr, hparse⟩ :=
    Zstd.Spec.parseFrameHeader_succeeds data 0 hmagic (by simpa only [Nat.zero_add] using hframeSize)
  -- Step 2: Apply decompressFrame_succeeds_two_rle_blocks
  obtain ⟨content, pos', hframe⟩ := Zstd.Spec.decompressFrame_succeeds_two_rle_blocks
    data 0 hdr afterHdr hparse
    (hnodict hdr afterHdr hparse) (hnocksum hdr afterHdr hparse) (hnosize hdr afterHdr hparse)
    (hsize1 hdr afterHdr hparse) (htypeVal1 hdr afterHdr hparse) (hlastBit1 hdr afterHdr hparse)
    (hblockSize1 hdr afterHdr hparse) (hwindow1 hdr afterHdr hparse)
    (hpayload1 hdr afterHdr hparse) rfl
    (hsize2 hdr afterHdr hparse) (htypeVal2 hdr afterHdr hparse) (hlastBit2 hdr afterHdr hparse)
    (hblockSize2 hdr afterHdr hparse) (hwindow2 hdr afterHdr hparse)
    (hpayload2 hdr afterHdr hparse)
  -- Step 3: Apply decompressZstd_single_frame
  exact ⟨content, decompressZstd_single_frame data content pos' hframe (hterm content pos' hframe)⟩

/-- End-to-end composed completeness for a frame with a non-last RLE block followed
    by a last raw block: byte-level conditions on the frame header and both block
    headers imply `decompressZstd` succeeds.

    Composes the full chain:
    1. `parseFrameHeader_succeeds` (byte-level magic + size → frame header parsed)
    2. `decompressFrame_succeeds_rle_then_raw` (header + RLE + raw blocks → frame)
    3. `decompressZstd_single_frame` (frame success + end-of-data → API success) -/
theorem decompressZstd_succeeds_rle_then_raw_frame (data : ByteArray)
    -- Frame header conditions (from parseFrameHeader_succeeds)
    (hmagic : Binary.readUInt32LE data 0 = Zip.Native.zstdMagic)
    (hframeSize : data.size ≥ Zstd.Spec.frameHeaderMinSize data[4]!)
    -- Header field constraints (universally quantified over parseFrameHeader result)
    (hnodict : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.dictionaryId = none)
    (hnocksum : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.contentChecksum = false)
    (hnosize : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.contentSize = none)
    -- Block 1 (non-last RLE) at afterHdr
    (hsize1 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ afterHdr + 3)
    (htypeVal1 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 1)
    (hlastBit1 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → (data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) &&& 1 = 0)
    (hblockSize1 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow1 : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → ¬ (hdr.windowSize > 0 &&
            ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > hdr.windowSize))
    (hpayload1 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ afterHdr + 4)
    -- Block 2 (last raw) at off2 = afterHdr + 4
    (hsize2 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ (afterHdr + 4) + 3)
    (htypeVal2 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr + 4]!.toUInt32 ||| (data[afterHdr + 4 + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 4 + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 0)
    (hlastBit2 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → (data[afterHdr + 4]!.toUInt32 ||| (data[afterHdr + 4 + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 4 + 2]!.toUInt32 <<< 16)) &&& 1 = 1)
    (hblockSize2 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr + 4]!.toUInt32 ||| (data[afterHdr + 4 + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 4 + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow2 : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → ¬ (hdr.windowSize > 0 &&
            ((data[afterHdr + 4]!.toUInt32 ||| (data[afterHdr + 4 + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 4 + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > hdr.windowSize))
    (hpayload2 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ (afterHdr + 4) + 3 +
            (((data[afterHdr + 4]!.toUInt32 ||| (data[afterHdr + 4 + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 4 + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    -- Frame terminates the data
    (hterm : ∀ content pos', Zip.Native.decompressFrame data 0 = .ok (content, pos')
        → pos' ≥ data.size) :
    ∃ output, Zip.Native.decompressZstd data = .ok output := by
  -- Step 1: Obtain header from parseFrameHeader_succeeds
  obtain ⟨hdr, afterHdr, hparse⟩ :=
    Zstd.Spec.parseFrameHeader_succeeds data 0 hmagic (by simpa only [Nat.zero_add] using hframeSize)
  -- Step 2: Apply decompressFrame_succeeds_rle_then_raw
  obtain ⟨content, pos', hframe⟩ := Zstd.Spec.decompressFrame_succeeds_rle_then_raw
    data 0 hdr afterHdr hparse
    (hnodict hdr afterHdr hparse) (hnocksum hdr afterHdr hparse) (hnosize hdr afterHdr hparse)
    (hsize1 hdr afterHdr hparse) (htypeVal1 hdr afterHdr hparse) (hlastBit1 hdr afterHdr hparse)
    (hblockSize1 hdr afterHdr hparse) (hwindow1 hdr afterHdr hparse)
    (hpayload1 hdr afterHdr hparse) (afterHdr + 4) rfl
    (hsize2 hdr afterHdr hparse) (htypeVal2 hdr afterHdr hparse) (hlastBit2 hdr afterHdr hparse)
    (hblockSize2 hdr afterHdr hparse) (hwindow2 hdr afterHdr hparse)
    (hpayload2 hdr afterHdr hparse)
  -- Step 3: Apply decompressZstd_single_frame
  exact ⟨content, decompressZstd_single_frame data content pos' hframe (hterm content pos' hframe)⟩

/-- End-to-end composed completeness for a frame with a non-last RLE block followed
    by a last compressed block with zero sequences: byte-level conditions on the frame
    header, both block headers, and the compressed block's literals/sequences parsing
    imply `decompressZstd` succeeds.

    Composes the full chain:
    1. `parseFrameHeader_succeeds` (byte-level magic + size → frame header parsed)
    2. `decompressFrame_succeeds_rle_then_compressed_zero_seq` (header + RLE + compressed → frame)
    3. `decompressZstd_single_frame` (frame success + end-of-data → API success) -/
theorem decompressZstd_succeeds_rle_then_compressed_zero_seq_frame (data : ByteArray)
    -- Frame header conditions (from parseFrameHeader_succeeds)
    (hmagic : Binary.readUInt32LE data 0 = Zip.Native.zstdMagic)
    (hframeSize : data.size ≥ Zstd.Spec.frameHeaderMinSize data[4]!)
    -- Header field constraints (universally quantified over parseFrameHeader result)
    (hnodict : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.dictionaryId = none)
    (hnocksum : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.contentChecksum = false)
    (hnosize : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.contentSize = none)
    -- Block 1 (non-last RLE) at afterHdr
    (hsize1 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ afterHdr + 3)
    (htypeVal1 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 1)
    (hlastBit1 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → (data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) &&& 1 = 0)
    (hblockSize1 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow1 : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → ¬ (hdr.windowSize > 0 &&
            ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > hdr.windowSize))
    (hpayload1 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ afterHdr + 4)
    -- Block 2 (last compressed, zero sequences) at off2 = afterHdr + 4
    (hsize2 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ (afterHdr + 4) + 3)
    (htypeVal2 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr + 4]!.toUInt32 ||| (data[afterHdr + 4 + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 4 + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 2)
    (hlastBit2 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → (data[afterHdr + 4]!.toUInt32 ||| (data[afterHdr + 4 + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 4 + 2]!.toUInt32 <<< 16)) &&& 1 = 1)
    (hblockSize2 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr + 4]!.toUInt32 ||| (data[afterHdr + 4 + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 4 + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow2 : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → ¬ (hdr.windowSize > 0 &&
            ((data[afterHdr + 4]!.toUInt32 ||| (data[afterHdr + 4 + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 4 + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > hdr.windowSize))
    (hblockEnd2 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ (afterHdr + 4) + 3 +
            (((data[afterHdr + 4]!.toUInt32 ||| (data[afterHdr + 4 + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 4 + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    -- Literals section and sequences header succeed for block 2
    (hparsing2 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ∃ literals afterLiterals huffTree modes afterSeqHeader,
            Zip.Native.parseLiteralsSection data (afterHdr + 4 + 3) none
              = .ok (literals, afterLiterals, huffTree) ∧
            Zip.Native.parseSequencesHeader data afterLiterals
              = .ok (0, modes, afterSeqHeader))
    -- Frame terminates the data
    (hterm : ∀ content pos', Zip.Native.decompressFrame data 0 = .ok (content, pos')
        → pos' ≥ data.size) :
    ∃ output, Zip.Native.decompressZstd data = .ok output := by
  -- Step 1: Obtain header from parseFrameHeader_succeeds
  obtain ⟨hdr, afterHdr, hparse⟩ :=
    Zstd.Spec.parseFrameHeader_succeeds data 0 hmagic (by simpa only [Nat.zero_add] using hframeSize)
  -- Step 2: Obtain literals and sequences parsing from combined hypothesis
  obtain ⟨literals, afterLiterals, huffTree, modes, afterSeqHeader, hlit2', hseq2'⟩ :=
    hparsing2 hdr afterHdr hparse
  -- Step 3: Apply decompressFrame_succeeds_rle_then_compressed_zero_seq
  obtain ⟨content, pos', hframe⟩ := Zstd.Spec.decompressFrame_succeeds_rle_then_compressed_zero_seq
    data 0 hdr afterHdr literals afterLiterals huffTree modes afterSeqHeader hparse
    (hnodict hdr afterHdr hparse) (hnocksum hdr afterHdr hparse) (hnosize hdr afterHdr hparse)
    (hsize1 hdr afterHdr hparse) (htypeVal1 hdr afterHdr hparse) (hlastBit1 hdr afterHdr hparse)
    (hblockSize1 hdr afterHdr hparse) (hwindow1 hdr afterHdr hparse)
    (hpayload1 hdr afterHdr hparse) (afterHdr + 4) rfl
    (hsize2 hdr afterHdr hparse) (htypeVal2 hdr afterHdr hparse) (hlastBit2 hdr afterHdr hparse)
    (hblockSize2 hdr afterHdr hparse) (hwindow2 hdr afterHdr hparse)
    (hblockEnd2 hdr afterHdr hparse) hlit2' hseq2'
  -- Step 4: Apply decompressZstd_single_frame
  exact ⟨content, decompressZstd_single_frame data content pos' hframe (hterm content pos' hframe)⟩

/-! ## decompressZstd two-block composed completeness (raw first block) -/

/-- End-to-end composed completeness for a frame with two raw blocks:
    byte-level conditions on the frame header and both block headers imply
    `decompressZstd` succeeds.

    Composes the full chain:
    1. `parseFrameHeader_succeeds` (byte-level magic + size → frame header parsed)
    2. `decompressFrame_succeeds_two_raw_blocks` (header + two raw blocks → frame success)
    3. `decompressZstd_single_frame` (frame success + end-of-data → API success) -/
theorem decompressZstd_succeeds_two_raw_frame (data : ByteArray)
    -- Frame header conditions (from parseFrameHeader_succeeds)
    (hmagic : Binary.readUInt32LE data 0 = Zip.Native.zstdMagic)
    (hframeSize : data.size ≥ Zstd.Spec.frameHeaderMinSize data[4]!)
    -- Header field constraints (universally quantified over parseFrameHeader result)
    (hnodict : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.dictionaryId = none)
    (hnocksum : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.contentChecksum = false)
    (hnosize : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.contentSize = none)
    -- Block 1 (non-last raw) at afterHdr
    (hsize1 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ afterHdr + 3)
    (htypeVal1 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 0)
    (hlastBit1 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → (data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) &&& 1 = 0)
    (hblockSize1 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow1 : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → ¬ (hdr.windowSize > 0 &&
            ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > hdr.windowSize))
    (hpayload1 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    -- Block 2 (last raw) at off2 = afterHdr + 3 + block1Size
    (hsize2 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr) →
        let off2 := afterHdr + 3 + (((data[afterHdr]!.toUInt32
              ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)
        data.size ≥ off2 + 3)
    (htypeVal2 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr) →
        let off2 := afterHdr + 3 + (((data[afterHdr]!.toUInt32
              ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)
        ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
            ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 0)
    (hlastBit2 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr) →
        let off2 := afterHdr + 3 + (((data[afterHdr]!.toUInt32
              ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)
        (data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
            ||| (data[off2 + 2]!.toUInt32 <<< 16)) &&& 1 = 1)
    (hblockSize2 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr) →
        let off2 := afterHdr + 3 + (((data[afterHdr]!.toUInt32
              ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)
        ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
            ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow2 : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr) →
        let off2 := afterHdr + 3 + (((data[afterHdr]!.toUInt32
              ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)
        ¬ (hdr.windowSize > 0 &&
            ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
              ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > hdr.windowSize))
    (hpayload2 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr) →
        let off2 := afterHdr + 3 + (((data[afterHdr]!.toUInt32
              ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)
        data.size ≥ off2 + 3 +
            (((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
              ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    -- Frame terminates the data
    (hterm : ∀ content pos', Zip.Native.decompressFrame data 0 = .ok (content, pos')
        → pos' ≥ data.size) :
    ∃ output, Zip.Native.decompressZstd data = .ok output := by
  -- Step 1: Obtain header from parseFrameHeader_succeeds
  obtain ⟨hdr, afterHdr, hparse⟩ :=
    Zstd.Spec.parseFrameHeader_succeeds data 0 hmagic (by simpa only [Nat.zero_add] using hframeSize)
  -- Step 2: Apply decompressFrame_succeeds_two_raw_blocks
  obtain ⟨content, pos', hframe⟩ := Zstd.Spec.decompressFrame_succeeds_two_raw_blocks
    data 0 hdr afterHdr hparse
    (hnodict hdr afterHdr hparse) (hnocksum hdr afterHdr hparse) (hnosize hdr afterHdr hparse)
    (hsize1 hdr afterHdr hparse) (htypeVal1 hdr afterHdr hparse) (hlastBit1 hdr afterHdr hparse)
    (hblockSize1 hdr afterHdr hparse) (hwindow1 hdr afterHdr hparse) (hpayload1 hdr afterHdr hparse)
    rfl (hsize2 hdr afterHdr hparse) (htypeVal2 hdr afterHdr hparse) (hlastBit2 hdr afterHdr hparse)
    (hblockSize2 hdr afterHdr hparse) (hwindow2 hdr afterHdr hparse) (hpayload2 hdr afterHdr hparse)
  -- Step 3: Apply decompressZstd_single_frame
  exact ⟨content, decompressZstd_single_frame data content pos' hframe (hterm content pos' hframe)⟩

/-- End-to-end composed completeness for a frame with a raw first block and RLE
    second block: byte-level conditions on the frame header and both block headers
    imply `decompressZstd` succeeds.

    Composes the full chain:
    1. `parseFrameHeader_succeeds` (byte-level magic + size → frame header parsed)
    2. `decompressFrame_succeeds_raw_then_rle` (header + raw + RLE blocks → frame success)
    3. `decompressZstd_single_frame` (frame success + end-of-data → API success) -/
theorem decompressZstd_succeeds_raw_then_rle_frame (data : ByteArray)
    -- Frame header conditions (from parseFrameHeader_succeeds)
    (hmagic : Binary.readUInt32LE data 0 = Zip.Native.zstdMagic)
    (hframeSize : data.size ≥ Zstd.Spec.frameHeaderMinSize data[4]!)
    -- Header field constraints (universally quantified over parseFrameHeader result)
    (hnodict : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.dictionaryId = none)
    (hnocksum : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.contentChecksum = false)
    (hnosize : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.contentSize = none)
    -- Block 1 (non-last raw) at afterHdr
    (hsize1 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ afterHdr + 3)
    (htypeVal1 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 0)
    (hlastBit1 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → (data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) &&& 1 = 0)
    (hblockSize1 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow1 : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → ¬ (hdr.windowSize > 0 &&
            ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > hdr.windowSize))
    (hpayload1 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    -- Block 2 (last RLE) at off2 = afterHdr + 3 + block1Size
    (hsize2 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr) →
        let off2 := afterHdr + 3 + (((data[afterHdr]!.toUInt32
              ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)
        data.size ≥ off2 + 3)
    (htypeVal2 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr) →
        let off2 := afterHdr + 3 + (((data[afterHdr]!.toUInt32
              ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)
        ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
            ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 1)
    (hlastBit2 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr) →
        let off2 := afterHdr + 3 + (((data[afterHdr]!.toUInt32
              ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)
        (data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
            ||| (data[off2 + 2]!.toUInt32 <<< 16)) &&& 1 = 1)
    (hblockSize2 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr) →
        let off2 := afterHdr + 3 + (((data[afterHdr]!.toUInt32
              ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)
        ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
            ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow2 : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr) →
        let off2 := afterHdr + 3 + (((data[afterHdr]!.toUInt32
              ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)
        ¬ (hdr.windowSize > 0 &&
            ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
              ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > hdr.windowSize))
    (hpayload2 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr) →
        let off2 := afterHdr + 3 + (((data[afterHdr]!.toUInt32
              ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)
        data.size ≥ off2 + 4)
    -- Frame terminates the data
    (hterm : ∀ content pos', Zip.Native.decompressFrame data 0 = .ok (content, pos')
        → pos' ≥ data.size) :
    ∃ output, Zip.Native.decompressZstd data = .ok output := by
  -- Step 1: Obtain header from parseFrameHeader_succeeds
  obtain ⟨hdr, afterHdr, hparse⟩ :=
    Zstd.Spec.parseFrameHeader_succeeds data 0 hmagic (by simpa only [Nat.zero_add] using hframeSize)
  -- Step 2: Apply decompressFrame_succeeds_raw_then_rle
  obtain ⟨content, pos', hframe⟩ := Zstd.Spec.decompressFrame_succeeds_raw_then_rle
    data 0 hdr afterHdr hparse
    (hnodict hdr afterHdr hparse) (hnocksum hdr afterHdr hparse) (hnosize hdr afterHdr hparse)
    (hsize1 hdr afterHdr hparse) (htypeVal1 hdr afterHdr hparse) (hlastBit1 hdr afterHdr hparse)
    (hblockSize1 hdr afterHdr hparse) (hwindow1 hdr afterHdr hparse) (hpayload1 hdr afterHdr hparse)
    _ rfl (hsize2 hdr afterHdr hparse) (htypeVal2 hdr afterHdr hparse)
    (hlastBit2 hdr afterHdr hparse) (hblockSize2 hdr afterHdr hparse)
    (hwindow2 hdr afterHdr hparse) (hpayload2 hdr afterHdr hparse)
  -- Step 3: Apply decompressZstd_single_frame
  exact ⟨content, decompressZstd_single_frame data content pos' hframe (hterm content pos' hframe)⟩

/-- End-to-end composed completeness for a frame with a raw first block and
    compressed second block (zero sequences): byte-level conditions on the frame
    header, both block headers, and parsing conditions imply `decompressZstd` succeeds.

    Composes the full chain:
    1. `parseFrameHeader_succeeds` (byte-level magic + size → frame header parsed)
    2. `decompressFrame_succeeds_raw_then_compressed_zero_seq` (header + raw + compressed → frame)
    3. `decompressZstd_single_frame` (frame success + end-of-data → API success) -/
theorem decompressZstd_succeeds_raw_then_compressed_zero_seq_frame (data : ByteArray)
    -- Frame header conditions (from parseFrameHeader_succeeds)
    (hmagic : Binary.readUInt32LE data 0 = Zip.Native.zstdMagic)
    (hframeSize : data.size ≥ Zstd.Spec.frameHeaderMinSize data[4]!)
    -- Header field constraints (universally quantified over parseFrameHeader result)
    (hnodict : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.dictionaryId = none)
    (hnocksum : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.contentChecksum = false)
    (hnosize : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.contentSize = none)
    -- Block 1 (non-last raw) at afterHdr
    (hsize1 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ afterHdr + 3)
    (htypeVal1 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 0)
    (hlastBit1 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → (data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) &&& 1 = 0)
    (hblockSize1 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow1 : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → ¬ (hdr.windowSize > 0 &&
            ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > hdr.windowSize))
    (hpayload1 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    -- Block 2 (last compressed, zero sequences) at off2 = afterHdr + 3 + block1Size
    (hsize2 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr) →
        let off2 := afterHdr + 3 + (((data[afterHdr]!.toUInt32
              ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)
        data.size ≥ off2 + 3)
    (htypeVal2 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr) →
        let off2 := afterHdr + 3 + (((data[afterHdr]!.toUInt32
              ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)
        ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
            ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 2)
    (hlastBit2 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr) →
        let off2 := afterHdr + 3 + (((data[afterHdr]!.toUInt32
              ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)
        (data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
            ||| (data[off2 + 2]!.toUInt32 <<< 16)) &&& 1 = 1)
    (hblockSize2 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr) →
        let off2 := afterHdr + 3 + (((data[afterHdr]!.toUInt32
              ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)
        ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
            ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow2 : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr) →
        let off2 := afterHdr + 3 + (((data[afterHdr]!.toUInt32
              ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)
        ¬ (hdr.windowSize > 0 &&
            ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
              ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > hdr.windowSize))
    (hblockEnd2 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr) →
        let off2 := afterHdr + 3 + (((data[afterHdr]!.toUInt32
              ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)
        data.size ≥ off2 + 3 +
            (((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
              ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    -- Literals section and sequences header succeed at block 2 (quantified, with existentials)
    (hparsing2 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr) →
        let off2 := afterHdr + 3 + (((data[afterHdr]!.toUInt32
              ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)
        ∃ literals afterLiterals huffTree modes afterSeqHeader,
            Zip.Native.parseLiteralsSection data (off2 + 3) none
              = .ok (literals, afterLiterals, huffTree) ∧
            Zip.Native.parseSequencesHeader data afterLiterals
              = .ok (0, modes, afterSeqHeader))
    -- Frame terminates the data
    (hterm : ∀ content pos', Zip.Native.decompressFrame data 0 = .ok (content, pos')
        → pos' ≥ data.size) :
    ∃ output, Zip.Native.decompressZstd data = .ok output := by
  -- Step 1: Obtain header from parseFrameHeader_succeeds
  obtain ⟨hdr, afterHdr, hparse⟩ :=
    Zstd.Spec.parseFrameHeader_succeeds data 0 hmagic (by simpa only [Nat.zero_add] using hframeSize)
  -- Step 2: Obtain literals and sequences parsing from combined hypothesis
  obtain ⟨literals, afterLiterals, huffTree, modes, afterSeqHeader, hlit', hseq'⟩ :=
    hparsing2 hdr afterHdr hparse
  -- Step 3: Apply decompressFrame_succeeds_raw_then_compressed_zero_seq
  obtain ⟨content, pos', hframe⟩ :=
    Zstd.Spec.decompressFrame_succeeds_raw_then_compressed_zero_seq
    data 0 hdr afterHdr literals afterLiterals huffTree modes afterSeqHeader
    hparse (hnodict hdr afterHdr hparse) (hnocksum hdr afterHdr hparse)
    (hnosize hdr afterHdr hparse)
    (hsize1 hdr afterHdr hparse) (htypeVal1 hdr afterHdr hparse) (hlastBit1 hdr afterHdr hparse)
    (hblockSize1 hdr afterHdr hparse) (hwindow1 hdr afterHdr hparse) (hpayload1 hdr afterHdr hparse)
    _ rfl (hsize2 hdr afterHdr hparse) (htypeVal2 hdr afterHdr hparse)
    (hlastBit2 hdr afterHdr hparse) (hblockSize2 hdr afterHdr hparse)
    (hwindow2 hdr afterHdr hparse) (hblockEnd2 hdr afterHdr hparse) hlit' hseq'
  -- Step 4: Apply decompressZstd_single_frame
  exact ⟨content, decompressZstd_single_frame data content pos' hframe (hterm content pos' hframe)⟩

/-! ## decompressZstd two-block composed completeness (comp_zero_seq first block) -/

/-- End-to-end composed completeness for a frame with a non-last compressed block
    (numSeq=0) followed by a last raw block: byte-level conditions on the frame header,
    both block headers, and the compressed block's literals/sequences parsing
    imply `decompressZstd` succeeds.

    Composes the full chain:
    1. `parseFrameHeader_succeeds` (byte-level magic + size → frame header parsed)
    2. `decompressFrame_succeeds_compressed_zero_seq_then_raw` (header + compressed + raw → frame)
    3. `decompressZstd_single_frame` (frame success + end-of-data → API success) -/
theorem decompressZstd_succeeds_compressed_zero_seq_then_raw_frame (data : ByteArray)
    -- Frame header conditions (from parseFrameHeader_succeeds)
    (hmagic : Binary.readUInt32LE data 0 = Zip.Native.zstdMagic)
    (hframeSize : data.size ≥ Zstd.Spec.frameHeaderMinSize data[4]!)
    -- Header field constraints (universally quantified over parseFrameHeader result)
    (hnodict : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.dictionaryId = none)
    (hnocksum : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.contentChecksum = false)
    (hnosize : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.contentSize = none)
    -- Block 1 (non-last compressed, zero sequences) at afterHdr
    (hsize1 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ afterHdr + 3)
    (htypeVal1 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 2)
    (hlastBit1 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → (data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) &&& 1 = 0)
    (hblockSize1 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow1 : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → ¬ (hdr.windowSize > 0 &&
            ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > hdr.windowSize))
    (hblockEnd1 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    -- Literals section and sequences header succeed for block 1
    (hparsing1 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ∃ literals afterLiterals huffTree modes afterSeqHeader,
            Zip.Native.parseLiteralsSection data (afterHdr + 3) none
              = .ok (literals, afterLiterals, huffTree) ∧
            Zip.Native.parseSequencesHeader data afterLiterals
              = .ok (0, modes, afterSeqHeader))
    -- Block 2 (last raw) at off2 = afterHdr + 3 + blockSize1
    (hsize2 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ (afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)) + 3)
    (htypeVal2 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)]!.toUInt32
            ||| (data[afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat) + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat) + 2]!.toUInt32 <<< 16))
            >>> 1) &&& 3 = 0)
    (hlastBit2 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → (data[afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)]!.toUInt32
            ||| (data[afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat) + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat) + 2]!.toUInt32 <<< 16))
            &&& 1 = 1)
    (hblockSize2 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)]!.toUInt32
            ||| (data[afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat) + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat) + 2]!.toUInt32 <<< 16))
            >>> 3) ≤ 131072)
    (hwindow2 : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → ¬ (hdr.windowSize > 0 &&
            ((data[afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)]!.toUInt32
            ||| (data[afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat) + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat) + 2]!.toUInt32 <<< 16))
            >>> 3).toUInt64 > hdr.windowSize))
    (hpayload2 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ (afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)) + 3 +
            (((data[afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)]!.toUInt32
            ||| (data[afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat) + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat) + 2]!.toUInt32 <<< 16))
            >>> 3).toNat))
    -- Frame terminates the data
    (hterm : ∀ content pos', Zip.Native.decompressFrame data 0 = .ok (content, pos')
        → pos' ≥ data.size) :
    ∃ output, Zip.Native.decompressZstd data = .ok output := by
  -- Step 1: Obtain header from parseFrameHeader_succeeds
  obtain ⟨hdr, afterHdr, hparse⟩ :=
    Zstd.Spec.parseFrameHeader_succeeds data 0 hmagic (by simpa only [Nat.zero_add] using hframeSize)
  -- Step 2: Obtain literals and sequences parsing from combined hypothesis
  obtain ⟨literals, afterLiterals, huffTree, modes, afterSeqHeader, hlit1', hseq1'⟩ :=
    hparsing1 hdr afterHdr hparse
  -- Step 3: Apply decompressFrame_succeeds_compressed_zero_seq_then_raw
  obtain ⟨content, pos', hframe⟩ := Zstd.Spec.decompressFrame_succeeds_compressed_zero_seq_then_raw
    data 0 hdr afterHdr literals afterLiterals huffTree modes afterSeqHeader hparse
    (hnodict hdr afterHdr hparse) (hnocksum hdr afterHdr hparse) (hnosize hdr afterHdr hparse)
    (hsize1 hdr afterHdr hparse) (htypeVal1 hdr afterHdr hparse) (hlastBit1 hdr afterHdr hparse)
    (hblockSize1 hdr afterHdr hparse) (hwindow1 hdr afterHdr hparse)
    (hblockEnd1 hdr afterHdr hparse) hlit1' hseq1'
    _ rfl
    (hsize2 hdr afterHdr hparse) (htypeVal2 hdr afterHdr hparse) (hlastBit2 hdr afterHdr hparse)
    (hblockSize2 hdr afterHdr hparse) (hwindow2 hdr afterHdr hparse)
    (hpayload2 hdr afterHdr hparse)
  -- Step 4: Apply decompressZstd_single_frame
  exact ⟨content, decompressZstd_single_frame data content pos' hframe (hterm content pos' hframe)⟩

/-- End-to-end composed completeness for a frame with a non-last compressed block
    (numSeq=0) followed by a last RLE block: byte-level conditions on the frame header,
    both block headers, and the compressed block's literals/sequences parsing
    imply `decompressZstd` succeeds.

    Composes the full chain:
    1. `parseFrameHeader_succeeds` (byte-level magic + size → frame header parsed)
    2. `decompressFrame_succeeds_compressed_zero_seq_then_rle` (header + compressed + RLE → frame)
    3. `decompressZstd_single_frame` (frame success + end-of-data → API success) -/
theorem decompressZstd_succeeds_compressed_zero_seq_then_rle_frame (data : ByteArray)
    -- Frame header conditions (from parseFrameHeader_succeeds)
    (hmagic : Binary.readUInt32LE data 0 = Zip.Native.zstdMagic)
    (hframeSize : data.size ≥ Zstd.Spec.frameHeaderMinSize data[4]!)
    -- Header field constraints (universally quantified over parseFrameHeader result)
    (hnodict : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.dictionaryId = none)
    (hnocksum : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.contentChecksum = false)
    (hnosize : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.contentSize = none)
    -- Block 1 (non-last compressed, zero sequences) at afterHdr
    (hsize1 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ afterHdr + 3)
    (htypeVal1 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 2)
    (hlastBit1 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → (data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) &&& 1 = 0)
    (hblockSize1 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow1 : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → ¬ (hdr.windowSize > 0 &&
            ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > hdr.windowSize))
    (hblockEnd1 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    -- Literals section and sequences header succeed for block 1
    (hparsing1 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ∃ literals afterLiterals huffTree modes afterSeqHeader,
            Zip.Native.parseLiteralsSection data (afterHdr + 3) none
              = .ok (literals, afterLiterals, huffTree) ∧
            Zip.Native.parseSequencesHeader data afterLiterals
              = .ok (0, modes, afterSeqHeader))
    -- Block 2 (last RLE) at off2 = afterHdr + 3 + blockSize1
    (hsize2 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ (afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)) + 3)
    (htypeVal2 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)]!.toUInt32
            ||| (data[afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat) + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat) + 2]!.toUInt32 <<< 16))
            >>> 1) &&& 3 = 1)
    (hlastBit2 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → (data[afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)]!.toUInt32
            ||| (data[afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat) + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat) + 2]!.toUInt32 <<< 16))
            &&& 1 = 1)
    (hblockSize2 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)]!.toUInt32
            ||| (data[afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat) + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat) + 2]!.toUInt32 <<< 16))
            >>> 3) ≤ 131072)
    (hwindow2 : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → ¬ (hdr.windowSize > 0 &&
            ((data[afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)]!.toUInt32
            ||| (data[afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat) + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat) + 2]!.toUInt32 <<< 16))
            >>> 3).toUInt64 > hdr.windowSize))
    (hpayload2 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ (afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)) + 4)
    -- Frame terminates the data
    (hterm : ∀ content pos', Zip.Native.decompressFrame data 0 = .ok (content, pos')
        → pos' ≥ data.size) :
    ∃ output, Zip.Native.decompressZstd data = .ok output := by
  -- Step 1: Obtain header from parseFrameHeader_succeeds
  obtain ⟨hdr, afterHdr, hparse⟩ :=
    Zstd.Spec.parseFrameHeader_succeeds data 0 hmagic (by simpa only [Nat.zero_add] using hframeSize)
  -- Step 2: Obtain literals and sequences parsing from combined hypothesis
  obtain ⟨literals, afterLiterals, huffTree, modes, afterSeqHeader, hlit1', hseq1'⟩ :=
    hparsing1 hdr afterHdr hparse
  -- Step 3: Apply decompressFrame_succeeds_compressed_zero_seq_then_rle
  obtain ⟨content, pos', hframe⟩ := Zstd.Spec.decompressFrame_succeeds_compressed_zero_seq_then_rle
    data 0 hdr afterHdr literals afterLiterals huffTree modes afterSeqHeader hparse
    (hnodict hdr afterHdr hparse) (hnocksum hdr afterHdr hparse) (hnosize hdr afterHdr hparse)
    (hsize1 hdr afterHdr hparse) (htypeVal1 hdr afterHdr hparse) (hlastBit1 hdr afterHdr hparse)
    (hblockSize1 hdr afterHdr hparse) (hwindow1 hdr afterHdr hparse)
    (hblockEnd1 hdr afterHdr hparse) hlit1' hseq1'
    _ rfl
    (hsize2 hdr afterHdr hparse) (htypeVal2 hdr afterHdr hparse) (hlastBit2 hdr afterHdr hparse)
    (hblockSize2 hdr afterHdr hparse) (hwindow2 hdr afterHdr hparse)
    (hpayload2 hdr afterHdr hparse)
  -- Step 4: Apply decompressZstd_single_frame
  exact ⟨content, decompressZstd_single_frame data content pos' hframe (hterm content pos' hframe)⟩

/-! ## decompressZstd two-block composed completeness (comp_zero_seq first, compressed second) -/

/-- End-to-end composed completeness for a frame with a non-last compressed block
    (numSeq=0) followed by a last compressed block (numSeq=0): byte-level conditions
    on the frame header and both block headers, plus a combined parsing hypothesis
    for both blocks' literals/sequences, imply `decompressZstd` succeeds.

    Composes the full chain:
    1. `parseFrameHeader_succeeds` (byte-level magic + size → frame header parsed)
    2. `decompressFrame_succeeds_compressed_zero_seq_then_compressed_zero_seq` (header + two compressed → frame)
    3. `decompressZstd_single_frame` (frame success + end-of-data → API success) -/
theorem decompressZstd_succeeds_compressed_zero_seq_then_compressed_zero_seq_frame (data : ByteArray)
    -- Frame header conditions (from parseFrameHeader_succeeds)
    (hmagic : Binary.readUInt32LE data 0 = Zip.Native.zstdMagic)
    (hframeSize : data.size ≥ Zstd.Spec.frameHeaderMinSize data[4]!)
    -- Header field constraints (universally quantified over parseFrameHeader result)
    (hnodict : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.dictionaryId = none)
    (hnocksum : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.contentChecksum = false)
    (hnosize : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.contentSize = none)
    -- Block 1 (non-last compressed, zero sequences) at afterHdr
    (hsize1 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ afterHdr + 3)
    (htypeVal1 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 2)
    (hlastBit1 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → (data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) &&& 1 = 0)
    (hblockSize1 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow1 : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → ¬ (hdr.windowSize > 0 &&
            ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > hdr.windowSize))
    (hblockEnd1 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    -- Block 2 (last compressed, zero sequences) at off2
    (hsize2 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr) →
        let off2 := afterHdr + 3 + (((data[afterHdr]!.toUInt32
              ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)
        data.size ≥ off2 + 3)
    (htypeVal2 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr) →
        let off2 := afterHdr + 3 + (((data[afterHdr]!.toUInt32
              ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)
        ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
            ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 2)
    (hlastBit2 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr) →
        let off2 := afterHdr + 3 + (((data[afterHdr]!.toUInt32
              ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)
        (data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
            ||| (data[off2 + 2]!.toUInt32 <<< 16)) &&& 1 = 1)
    (hblockSize2 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr) →
        let off2 := afterHdr + 3 + (((data[afterHdr]!.toUInt32
              ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)
        ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
            ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow2 : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr) →
        let off2 := afterHdr + 3 + (((data[afterHdr]!.toUInt32
              ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)
        ¬ (hdr.windowSize > 0 &&
            ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
              ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > hdr.windowSize))
    (hblockEnd2 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr) →
        let off2 := afterHdr + 3 + (((data[afterHdr]!.toUInt32
              ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)
        data.size ≥ off2 + 3 +
            (((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
              ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    -- Combined parsing for both blocks (block 2 inherits Huffman table from block 1)
    (hparsing : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr) →
        let off2 := afterHdr + 3 + (((data[afterHdr]!.toUInt32
              ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)
        ∃ literals1 afterLiterals1 huffTree1 modes1 afterSeqHeader1
          literals2 afterLiterals2 huffTree2 modes2 afterSeqHeader2,
          Zip.Native.parseLiteralsSection data (afterHdr + 3) none
            = .ok (literals1, afterLiterals1, huffTree1) ∧
          Zip.Native.parseSequencesHeader data afterLiterals1
            = .ok (0, modes1, afterSeqHeader1) ∧
          Zip.Native.parseLiteralsSection data (off2 + 3)
            (if let some ht := huffTree1 then some ht else none)
            = .ok (literals2, afterLiterals2, huffTree2) ∧
          Zip.Native.parseSequencesHeader data afterLiterals2
            = .ok (0, modes2, afterSeqHeader2))
    -- Frame terminates the data
    (hterm : ∀ content pos', Zip.Native.decompressFrame data 0 = .ok (content, pos')
        → pos' ≥ data.size) :
    ∃ output, Zip.Native.decompressZstd data = .ok output := by
  -- Step 1: Obtain header from parseFrameHeader_succeeds
  obtain ⟨hdr, afterHdr, hparse⟩ :=
    Zstd.Spec.parseFrameHeader_succeeds data 0 hmagic (by simpa only [Nat.zero_add] using hframeSize)
  -- Step 2: Obtain literals and sequences parsing from combined hypothesis
  obtain ⟨literals1, afterLiterals1, huffTree1, modes1, afterSeqHeader1,
          literals2, afterLiterals2, huffTree2, modes2, afterSeqHeader2,
          hlit1', hseq1', hlit2', hseq2'⟩ :=
    hparsing hdr afterHdr hparse
  -- Step 3: Case-split on huffTree1 to resolve dependent match, then apply frame-level theorem
  cases huffTree1 <;> (
    obtain ⟨content, pos', hframe⟩ :=
      Zstd.Spec.decompressFrame_succeeds_compressed_zero_seq_then_compressed_zero_seq
      data 0 hdr afterHdr
      literals1 afterLiterals1 _ modes1 afterSeqHeader1
      literals2 afterLiterals2 huffTree2 modes2 afterSeqHeader2
      hparse (hnodict hdr afterHdr hparse) (hnocksum hdr afterHdr hparse)
      (hnosize hdr afterHdr hparse) (hsize1 hdr afterHdr hparse)
      (htypeVal1 hdr afterHdr hparse) (hlastBit1 hdr afterHdr hparse)
      (hblockSize1 hdr afterHdr hparse) (hwindow1 hdr afterHdr hparse)
      (hblockEnd1 hdr afterHdr hparse) hlit1' hseq1'
      _ rfl (hsize2 hdr afterHdr hparse) (htypeVal2 hdr afterHdr hparse)
      (hlastBit2 hdr afterHdr hparse) (hblockSize2 hdr afterHdr hparse)
      (hwindow2 hdr afterHdr hparse) (hblockEnd2 hdr afterHdr hparse) hlit2' hseq2'
    -- Step 4: Apply decompressZstd_single_frame
    exact ⟨content, decompressZstd_single_frame data content pos' hframe (hterm content pos' hframe)⟩)

/-- End-to-end composed completeness for a frame with a non-last compressed block
    (numSeq=0) followed by a last compressed block with sequences (numSeq > 0):
    byte-level conditions on the frame header and both block headers, plus a combined
    parsing/decoding/execution hypothesis for both blocks, imply `decompressZstd` succeeds.

    Composes the full chain:
    1. `parseFrameHeader_succeeds` (byte-level magic + size → frame header parsed)
    2. `decompressFrame_succeeds_compressed_zero_seq_then_compressed_sequences` (header + compressed + compressed → frame)
    3. `decompressZstd_single_frame` (frame success + end-of-data → API success) -/
theorem decompressZstd_succeeds_compressed_zero_seq_then_compressed_sequences_frame (data : ByteArray)
    -- Frame header conditions (from parseFrameHeader_succeeds)
    (hmagic : Binary.readUInt32LE data 0 = Zip.Native.zstdMagic)
    (hframeSize : data.size ≥ Zstd.Spec.frameHeaderMinSize data[4]!)
    -- Header field constraints (universally quantified over parseFrameHeader result)
    (hnodict : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.dictionaryId = none)
    (hnocksum : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.contentChecksum = false)
    (hnosize : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.contentSize = none)
    -- Block 1 (non-last compressed, zero sequences) at afterHdr
    (hsize1 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ afterHdr + 3)
    (htypeVal1 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 2)
    (hlastBit1 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → (data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) &&& 1 = 0)
    (hblockSize1 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow1 : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → ¬ (hdr.windowSize > 0 &&
            ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > hdr.windowSize))
    (hblockEnd1 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    -- Block 2 (last compressed, with sequences) at off2
    (hsize2 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr) →
        let off2 := afterHdr + 3 + (((data[afterHdr]!.toUInt32
              ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)
        data.size ≥ off2 + 3)
    (htypeVal2 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr) →
        let off2 := afterHdr + 3 + (((data[afterHdr]!.toUInt32
              ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)
        ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
            ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 2)
    (hlastBit2 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr) →
        let off2 := afterHdr + 3 + (((data[afterHdr]!.toUInt32
              ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)
        (data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
            ||| (data[off2 + 2]!.toUInt32 <<< 16)) &&& 1 = 1)
    (hblockSize2 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr) →
        let off2 := afterHdr + 3 + (((data[afterHdr]!.toUInt32
              ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)
        ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
            ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow2 : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr) →
        let off2 := afterHdr + 3 + (((data[afterHdr]!.toUInt32
              ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)
        ¬ (hdr.windowSize > 0 &&
            ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
              ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > hdr.windowSize))
    (hblockEnd2 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr) →
        let off2 := afterHdr + 3 + (((data[afterHdr]!.toUInt32
              ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)
        data.size ≥ off2 + 3 +
            (((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
              ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    -- Combined parsing for both blocks: block 1 (zero_seq) + block 2 (full sequence pipeline)
    (hparsing : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr) →
        let off2 := afterHdr + 3 + (((data[afterHdr]!.toUInt32
              ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)
        ∃ literals1 afterLiterals1 huffTree1 modes1 afterSeqHeader1
          literals2 afterLiterals2 huffTree2 numSeq2 modes2 afterSeqHeader2
          llTable2 ofTable2 mlTable2 afterTables2 bbr2 sequences2 blockOutput2 newHist2,
          Zip.Native.parseLiteralsSection data (afterHdr + 3) none
            = .ok (literals1, afterLiterals1, huffTree1) ∧
          Zip.Native.parseSequencesHeader data afterLiterals1
            = .ok (0, modes1, afterSeqHeader1) ∧
          Zip.Native.parseLiteralsSection data (off2 + 3)
            (if let some ht := huffTree1 then some ht else none)
            = .ok (literals2, afterLiterals2, huffTree2) ∧
          Zip.Native.parseSequencesHeader data afterLiterals2
            = .ok (numSeq2, modes2, afterSeqHeader2) ∧
          ¬ (numSeq2 == 0) ∧
          Zip.Native.resolveSequenceFseTables modes2 data afterSeqHeader2 {}
            = .ok (llTable2, ofTable2, mlTable2, afterTables2) ∧
          Zip.Native.BackwardBitReader.init data afterTables2
            (off2 + 3 + (((data[off2]!.toUInt32
              ||| (data[off2 + 1]!.toUInt32 <<< 8)
              ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
            = .ok bbr2 ∧
          Zip.Native.decodeSequences llTable2 ofTable2 mlTable2 bbr2 numSeq2
            = .ok sequences2 ∧
          Zip.Native.executeSequences sequences2 literals2
            (if hdr.windowSize > 0 &&
                  (ByteArray.empty ++ literals1).size > hdr.windowSize.toNat
              then (ByteArray.empty ++ literals1).extract
                ((ByteArray.empty ++ literals1).size - hdr.windowSize.toNat)
                (ByteArray.empty ++ literals1).size
              else (ByteArray.empty ++ literals1))
            #[1, 4, 8] hdr.windowSize.toNat
            = .ok (blockOutput2, newHist2))
    -- Frame terminates the data
    (hterm : ∀ content pos', Zip.Native.decompressFrame data 0 = .ok (content, pos')
        → pos' ≥ data.size) :
    ∃ output, Zip.Native.decompressZstd data = .ok output := by
  -- Step 1: Obtain header from parseFrameHeader_succeeds
  obtain ⟨hdr, afterHdr, hparse⟩ :=
    Zstd.Spec.parseFrameHeader_succeeds data 0 hmagic (by simpa only [Nat.zero_add] using hframeSize)
  -- Step 2: Obtain full pipeline from combined hypothesis
  obtain ⟨literals1, afterLiterals1, huffTree1, modes1, afterSeqHeader1,
          literals2, afterLiterals2, huffTree2, numSeq2, modes2, afterSeqHeader2,
          llTable2, ofTable2, mlTable2, afterTables2, bbr2, sequences2, blockOutput2, newHist2,
          hlit1', hseq1', hlit2', hseq2', hNumSeq2', hfse2', hbbr2', hdec2', hexec2'⟩ :=
    hparsing hdr afterHdr hparse
  -- Step 3: Case-split on huffTree1 to resolve dependent match, then apply frame-level theorem
  cases huffTree1 <;> (
    obtain ⟨content, pos', hframe⟩ :=
      Zstd.Spec.decompressFrame_succeeds_compressed_zero_seq_then_compressed_sequences
      data 0 hdr afterHdr
      literals1 afterLiterals1 _ modes1 afterSeqHeader1
      literals2 afterLiterals2 huffTree2 numSeq2 modes2 afterSeqHeader2
      llTable2 ofTable2 mlTable2 afterTables2 bbr2 sequences2 blockOutput2 newHist2
      hparse (hnodict hdr afterHdr hparse) (hnocksum hdr afterHdr hparse)
      (hnosize hdr afterHdr hparse) (hsize1 hdr afterHdr hparse)
      (htypeVal1 hdr afterHdr hparse) (hlastBit1 hdr afterHdr hparse)
      (hblockSize1 hdr afterHdr hparse) (hwindow1 hdr afterHdr hparse)
      (hblockEnd1 hdr afterHdr hparse) hlit1' hseq1'
      _ rfl (hsize2 hdr afterHdr hparse) (htypeVal2 hdr afterHdr hparse)
      (hlastBit2 hdr afterHdr hparse) (hblockSize2 hdr afterHdr hparse)
      (hwindow2 hdr afterHdr hparse) (hblockEnd2 hdr afterHdr hparse) hlit2' hseq2'
      hNumSeq2' hfse2' hbbr2' hdec2' hexec2'
    -- Step 4: Apply decompressZstd_single_frame
    exact ⟨content, decompressZstd_single_frame data content pos' hframe (hterm content pos' hframe)⟩)

/-! ## decompressZstd two-block composed completeness (comp_sequences first, raw/RLE second) -/

/-- End-to-end composed completeness for a frame with a non-last compressed block
    with sequences (numSeq > 0) followed by a last raw block: byte-level conditions
    on the frame header, block 1's full parsing/decoding/execution pipeline, and
    block 2's raw block conditions imply `decompressZstd` succeeds.

    Composes the full chain:
    1. `parseFrameHeader_succeeds` (byte-level magic + size → frame header parsed)
    2. `decompressFrame_succeeds_compressed_sequences_then_raw` (header + compressed + raw → frame)
    3. `decompressZstd_single_frame` (frame success + end-of-data → API success) -/
theorem decompressZstd_succeeds_compressed_sequences_then_raw_frame (data : ByteArray)
    -- Frame header conditions (from parseFrameHeader_succeeds)
    (hmagic : Binary.readUInt32LE data 0 = Zip.Native.zstdMagic)
    (hframeSize : data.size ≥ Zstd.Spec.frameHeaderMinSize data[4]!)
    -- Header field constraints (universally quantified over parseFrameHeader result)
    (hnodict : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.dictionaryId = none)
    (hnocksum : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.contentChecksum = false)
    (hnosize : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.contentSize = none)
    -- Block 1 (non-last compressed, numSeq > 0) at afterHdr
    (hsize1 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ afterHdr + 3)
    (htypeVal1 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 2)
    (hlastBit1 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → (data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) &&& 1 = 0)
    (hblockSize1 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow1 : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → ¬ (hdr.windowSize > 0 &&
            ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > hdr.windowSize))
    (hblockEnd1 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    -- Full parsing/decoding/execution pipeline for block 1 (quantified, with existentials)
    (hpipeline1 : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → ∃ literals afterLiterals huffTree numSeq modes afterSeqHeader
            llTable ofTable mlTable afterTables bbr sequences blockOutput newHist,
            Zip.Native.parseLiteralsSection data (afterHdr + 3) none
              = .ok (literals, afterLiterals, huffTree) ∧
            Zip.Native.parseSequencesHeader data afterLiterals
              = .ok (numSeq, modes, afterSeqHeader) ∧
            ¬ (numSeq == 0) ∧
            Zip.Native.resolveSequenceFseTables modes data afterSeqHeader {}
              = .ok (llTable, ofTable, mlTable, afterTables) ∧
            Zip.Native.BackwardBitReader.init data afterTables
              (afterHdr + 3 + (((data[afterHdr]!.toUInt32
                ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
                ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
              = .ok bbr ∧
            Zip.Native.decodeSequences llTable ofTable mlTable bbr numSeq
              = .ok sequences ∧
            Zip.Native.executeSequences sequences literals ByteArray.empty
              #[1, 4, 8] hdr.windowSize.toNat = .ok (blockOutput, newHist))
    -- Block 2 (last raw) at off2 = afterHdr + 3 + block1Size
    (hsize2 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr) →
        let off2 := afterHdr + 3 + (((data[afterHdr]!.toUInt32
              ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)
        data.size ≥ off2 + 3)
    (htypeVal2 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr) →
        let off2 := afterHdr + 3 + (((data[afterHdr]!.toUInt32
              ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)
        ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
            ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 0)
    (hlastBit2 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr) →
        let off2 := afterHdr + 3 + (((data[afterHdr]!.toUInt32
              ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)
        (data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
            ||| (data[off2 + 2]!.toUInt32 <<< 16)) &&& 1 = 1)
    (hblockSize2 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr) →
        let off2 := afterHdr + 3 + (((data[afterHdr]!.toUInt32
              ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)
        ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
            ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow2 : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr) →
        let off2 := afterHdr + 3 + (((data[afterHdr]!.toUInt32
              ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)
        ¬ (hdr.windowSize > 0 &&
            ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
              ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > hdr.windowSize))
    (hpayload2 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr) →
        let off2 := afterHdr + 3 + (((data[afterHdr]!.toUInt32
              ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)
        data.size ≥ off2 + 3 +
            (((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
              ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    -- Frame terminates the data
    (hterm : ∀ content pos', Zip.Native.decompressFrame data 0 = .ok (content, pos')
        → pos' ≥ data.size) :
    ∃ output, Zip.Native.decompressZstd data = .ok output := by
  -- Step 1: Obtain header from parseFrameHeader_succeeds
  obtain ⟨hdr, afterHdr, hparse⟩ :=
    Zstd.Spec.parseFrameHeader_succeeds data 0 hmagic (by simpa only [Nat.zero_add] using hframeSize)
  -- Step 2: Destructure pipeline existential for block 1
  obtain ⟨literals, afterLiterals, huffTree, numSeq, modes, afterSeqHeader,
    llTable, ofTable, mlTable, afterTables, bbr, sequences, blockOutput1, newHist1,
    hlit1', hseq1', hNumSeq1', hfse1', hbbr1', hdec1', hexec1'⟩ :=
    hpipeline1 hdr afterHdr hparse
  -- Step 3: Convert hexec1' to match block-level form (if-guard simplifies for empty output)
  have hexec1'' : Zip.Native.executeSequences sequences literals
      (if hdr.windowSize > 0 && ByteArray.empty.size > hdr.windowSize.toNat
       then ByteArray.empty.extract (ByteArray.empty.size - hdr.windowSize.toNat)
         ByteArray.empty.size
       else ByteArray.empty)
      #[1, 4, 8] hdr.windowSize.toNat = .ok (blockOutput1, newHist1) := by
    simp only [ByteArray.size_empty, Nat.not_lt_zero, decide_false, Bool.and_false,
      Bool.false_eq_true, ↓reduceIte]; exact hexec1'
  -- Step 4: Apply decompressFrame_succeeds_compressed_sequences_then_raw
  obtain ⟨content, pos', hframe⟩ :=
    Zstd.Spec.decompressFrame_succeeds_compressed_sequences_then_raw
    data 0 hdr afterHdr literals afterLiterals huffTree numSeq modes afterSeqHeader
    llTable ofTable mlTable afterTables bbr sequences blockOutput1 newHist1
    hparse (hnodict hdr afterHdr hparse) (hnocksum hdr afterHdr hparse)
    (hnosize hdr afterHdr hparse) (hsize1 hdr afterHdr hparse)
    (htypeVal1 hdr afterHdr hparse) (hlastBit1 hdr afterHdr hparse)
    (hblockSize1 hdr afterHdr hparse) (hwindow1 hdr afterHdr hparse)
    (hblockEnd1 hdr afterHdr hparse) hlit1' hseq1' hNumSeq1'
    hfse1' hbbr1' hdec1' hexec1''
    _ rfl (hsize2 hdr afterHdr hparse) (htypeVal2 hdr afterHdr hparse)
    (hlastBit2 hdr afterHdr hparse) (hblockSize2 hdr afterHdr hparse)
    (hwindow2 hdr afterHdr hparse) (hpayload2 hdr afterHdr hparse)
  -- Step 5: Apply decompressZstd_single_frame
  exact ⟨content, decompressZstd_single_frame data content pos' hframe (hterm content pos' hframe)⟩

/-- End-to-end composed completeness for a frame with a non-last compressed block
    with sequences (numSeq > 0) followed by a last RLE block: byte-level conditions
    on the frame header, block 1's full parsing/decoding/execution pipeline, and
    block 2's RLE block conditions imply `decompressZstd` succeeds.

    Composes the full chain:
    1. `parseFrameHeader_succeeds` (byte-level magic + size → frame header parsed)
    2. `decompressFrame_succeeds_compressed_sequences_then_rle` (header + compressed + RLE → frame)
    3. `decompressZstd_single_frame` (frame success + end-of-data → API success) -/
theorem decompressZstd_succeeds_compressed_sequences_then_rle_frame (data : ByteArray)
    -- Frame header conditions (from parseFrameHeader_succeeds)
    (hmagic : Binary.readUInt32LE data 0 = Zip.Native.zstdMagic)
    (hframeSize : data.size ≥ Zstd.Spec.frameHeaderMinSize data[4]!)
    -- Header field constraints (universally quantified over parseFrameHeader result)
    (hnodict : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.dictionaryId = none)
    (hnocksum : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.contentChecksum = false)
    (hnosize : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.contentSize = none)
    -- Block 1 (non-last compressed, numSeq > 0) at afterHdr
    (hsize1 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ afterHdr + 3)
    (htypeVal1 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 2)
    (hlastBit1 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → (data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) &&& 1 = 0)
    (hblockSize1 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow1 : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → ¬ (hdr.windowSize > 0 &&
            ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > hdr.windowSize))
    (hblockEnd1 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    -- Full parsing/decoding/execution pipeline for block 1 (quantified, with existentials)
    (hpipeline1 : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → ∃ literals afterLiterals huffTree numSeq modes afterSeqHeader
            llTable ofTable mlTable afterTables bbr sequences blockOutput newHist,
            Zip.Native.parseLiteralsSection data (afterHdr + 3) none
              = .ok (literals, afterLiterals, huffTree) ∧
            Zip.Native.parseSequencesHeader data afterLiterals
              = .ok (numSeq, modes, afterSeqHeader) ∧
            ¬ (numSeq == 0) ∧
            Zip.Native.resolveSequenceFseTables modes data afterSeqHeader {}
              = .ok (llTable, ofTable, mlTable, afterTables) ∧
            Zip.Native.BackwardBitReader.init data afterTables
              (afterHdr + 3 + (((data[afterHdr]!.toUInt32
                ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
                ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
              = .ok bbr ∧
            Zip.Native.decodeSequences llTable ofTable mlTable bbr numSeq
              = .ok sequences ∧
            Zip.Native.executeSequences sequences literals ByteArray.empty
              #[1, 4, 8] hdr.windowSize.toNat = .ok (blockOutput, newHist))
    -- Block 2 (last RLE) at off2 = afterHdr + 3 + block1Size
    (hsize2 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr) →
        let off2 := afterHdr + 3 + (((data[afterHdr]!.toUInt32
              ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)
        data.size ≥ off2 + 3)
    (htypeVal2 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr) →
        let off2 := afterHdr + 3 + (((data[afterHdr]!.toUInt32
              ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)
        ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
            ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 1)
    (hlastBit2 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr) →
        let off2 := afterHdr + 3 + (((data[afterHdr]!.toUInt32
              ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)
        (data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
            ||| (data[off2 + 2]!.toUInt32 <<< 16)) &&& 1 = 1)
    (hblockSize2 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr) →
        let off2 := afterHdr + 3 + (((data[afterHdr]!.toUInt32
              ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)
        ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
            ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow2 : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr) →
        let off2 := afterHdr + 3 + (((data[afterHdr]!.toUInt32
              ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)
        ¬ (hdr.windowSize > 0 &&
            ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
              ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > hdr.windowSize))
    (hpayload2 : ∀ _hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr) →
        let off2 := afterHdr + 3 + (((data[afterHdr]!.toUInt32
              ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)
        data.size ≥ off2 + 4)
    -- Frame terminates the data
    (hterm : ∀ content pos', Zip.Native.decompressFrame data 0 = .ok (content, pos')
        → pos' ≥ data.size) :
    ∃ output, Zip.Native.decompressZstd data = .ok output := by
  -- Step 1: Obtain header from parseFrameHeader_succeeds
  obtain ⟨hdr, afterHdr, hparse⟩ :=
    Zstd.Spec.parseFrameHeader_succeeds data 0 hmagic (by simpa only [Nat.zero_add] using hframeSize)
  -- Step 2: Destructure pipeline existential for block 1
  obtain ⟨literals, afterLiterals, huffTree, numSeq, modes, afterSeqHeader,
    llTable, ofTable, mlTable, afterTables, bbr, sequences, blockOutput1, newHist1,
    hlit1', hseq1', hNumSeq1', hfse1', hbbr1', hdec1', hexec1'⟩ :=
    hpipeline1 hdr afterHdr hparse
  -- Step 3: Convert hexec1' to match block-level form (if-guard simplifies for empty output)
  have hexec1'' : Zip.Native.executeSequences sequences literals
      (if hdr.windowSize > 0 && ByteArray.empty.size > hdr.windowSize.toNat
       then ByteArray.empty.extract (ByteArray.empty.size - hdr.windowSize.toNat)
         ByteArray.empty.size
       else ByteArray.empty)
      #[1, 4, 8] hdr.windowSize.toNat = .ok (blockOutput1, newHist1) := by
    simp only [ByteArray.size_empty, Nat.not_lt_zero, decide_false, Bool.and_false,
      Bool.false_eq_true, ↓reduceIte]; exact hexec1'
  -- Step 4: Apply decompressFrame_succeeds_compressed_sequences_then_rle
  obtain ⟨content, pos', hframe⟩ :=
    Zstd.Spec.decompressFrame_succeeds_compressed_sequences_then_rle
    data 0 hdr afterHdr literals afterLiterals huffTree numSeq modes afterSeqHeader
    llTable ofTable mlTable afterTables bbr sequences blockOutput1 newHist1
    hparse (hnodict hdr afterHdr hparse) (hnocksum hdr afterHdr hparse)
    (hnosize hdr afterHdr hparse) (hsize1 hdr afterHdr hparse)
    (htypeVal1 hdr afterHdr hparse) (hlastBit1 hdr afterHdr hparse)
    (hblockSize1 hdr afterHdr hparse) (hwindow1 hdr afterHdr hparse)
    (hblockEnd1 hdr afterHdr hparse) hlit1' hseq1' hNumSeq1'
    hfse1' hbbr1' hdec1' hexec1''
    _ rfl (hsize2 hdr afterHdr hparse) (htypeVal2 hdr afterHdr hparse)
    (hlastBit2 hdr afterHdr hparse) (hblockSize2 hdr afterHdr hparse)
    (hwindow2 hdr afterHdr hparse) (hpayload2 hdr afterHdr hparse)
  -- Step 5: Apply decompressZstd_single_frame
  exact ⟨content, decompressZstd_single_frame data content pos' hframe (hterm content pos' hframe)⟩

/-- When the input contains exactly one standard Zstd frame at position 0 with two
    blocks (first non-last compressed with numSeq>0, second last compressed with
    numSeq=0), `decompressZstd` succeeds.  Derived from
    `decompressZstd_compressed_seq_then_compressed_lit_content`. -/
theorem decompressZstd_succeeds_compressed_sequences_then_compressed_zero_seq_frame
    (data : ByteArray)
    (output : ByteArray) (pos' : Nat)
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
    (hframe : Zip.Native.decompressFrame data 0 = .ok (output, pos'))
    (hh : Zip.Native.parseFrameHeader data 0 = .ok (header, afterHeader))
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
    (hlast2 : hdr2.lastBlock = true)
    -- End of data
    (hend : pos' ≥ data.size) :
    ∃ out, Zip.Native.decompressZstd data = .ok out :=
  ⟨_, decompressZstd_compressed_seq_then_compressed_lit_content data output pos'
    header afterHeader hdr1 afterHdr1 literals1 afterLiterals1 huffTree1
    numSeq1 modes1 afterSeqHeader1 llTable1 ofTable1 mlTable1 afterTables1 bbr1 sequences1
    blockOutput1 newHist1 hdr2 afterHdr2 literals2 afterLiterals2 huffTree2 modes2
    afterSeqHeader2 hframe hh hparse1 hbs1 hws1 htype1 hblockEnd1 hlit1 hseq1
    hNumSeq1 hfse1 hbbr1 hdec1 hexec1 hnotlast1 hadv1 hoff2 hparse2 hbs2 hws2 htype2
    hblockEnd2 hlit2 hseq2 hlast2 hend⟩

/-- When the input contains exactly one standard Zstd frame at position 0 with two
    blocks (both compressed with numSeq>0), `decompressZstd` succeeds.  Derived from
    `decompressZstd_two_compressed_sequences_blocks_content`. -/
theorem decompressZstd_succeeds_two_compressed_sequences_frame (data : ByteArray)
    (output : ByteArray) (pos' : Nat)
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
    (hframe : Zip.Native.decompressFrame data 0 = .ok (output, pos'))
    (hh : Zip.Native.parseFrameHeader data 0 = .ok (header, afterHeader))
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
    (hlast2 : hdr2.lastBlock = true)
    -- End of data
    (hend : pos' ≥ data.size) :
    ∃ out, Zip.Native.decompressZstd data = .ok out :=
  ⟨_, decompressZstd_two_compressed_sequences_blocks_content data output pos'
    header afterHeader hdr1 afterHdr1 literals1 afterLiterals1 huffTree1
    numSeq1 modes1 afterSeqHeader1 llTable1 ofTable1 mlTable1 afterTables1 bbr1 sequences1
    blockOutput1 newHist1 hdr2 afterHdr2 literals2 afterLiterals2 huffTree2
    numSeq2 modes2 afterSeqHeader2 llTable2 ofTable2 mlTable2 afterTables2 bbr2 sequences2
    blockOutput2 newHist2 hframe hh hparse1 hbs1 hws1 htype1 hblockEnd1 hlit1 hseq1
    hNumSeq1 hfse1 hbbr1 hdec1 hexec1 hnotlast1 hadv1 hoff2 hparse2 hbs2 hws2 htype2
    hblockEnd2 hlit2 hseq2 hNumSeq2 hfse2 hbbr2 hdec2 hexec2 hlast2 hend⟩

/-- When the input contains exactly one standard Zstd frame at position 0 with two
    blocks (first non-last raw, second last compressed with numSeq>0), `decompressZstd`
    succeeds.  Derived from `decompressZstd_raw_then_compressed_seq_content`. -/
theorem decompressZstd_succeeds_raw_then_compressed_sequences_frame (data : ByteArray)
    (output : ByteArray) (pos' : Nat)
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
    (hframe : Zip.Native.decompressFrame data 0 = .ok (output, pos'))
    (hh : Zip.Native.parseFrameHeader data 0 = .ok (header, afterHeader))
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
    (hlast2 : hdr2.lastBlock = true)
    -- End of data
    (hend : pos' ≥ data.size) :
    ∃ out, Zip.Native.decompressZstd data = .ok out :=
  ⟨_, decompressZstd_raw_then_compressed_seq_content data output pos'
    header afterHeader hdr1 afterHdr1 block1 afterBlock1
    hdr2 afterHdr2 literals2 afterLiterals2 huffTree2
    numSeq2 modes2 afterSeqHeader2 llTable2 ofTable2 mlTable2 afterTables2 bbr2 sequences2
    blockOutput2 newHist2
    hframe hh hparse1 hbs1 hws1 htype1 hraw1 hnotlast1 hadv1
    hoff2 hparse2 hbs2 hws2 htype2 hblockEnd2 hlit2 hseq2 hNumSeq2
    hfse2 hbbr2 hdec2 hexec2 hlast2 hend⟩

/-- When the input contains exactly one standard Zstd frame at position 0 with two
    blocks (first non-last RLE, second last compressed with numSeq>0), `decompressZstd`
    succeeds.  Derived from `decompressZstd_rle_then_compressed_seq_content`. -/
theorem decompressZstd_succeeds_rle_then_compressed_sequences_frame (data : ByteArray)
    (output : ByteArray) (pos' : Nat)
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
    (hframe : Zip.Native.decompressFrame data 0 = .ok (output, pos'))
    (hh : Zip.Native.parseFrameHeader data 0 = .ok (header, afterHeader))
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
    (hlast2 : hdr2.lastBlock = true)
    -- End of data
    (hend : pos' ≥ data.size) :
    ∃ out, Zip.Native.decompressZstd data = .ok out :=
  ⟨_, decompressZstd_rle_then_compressed_seq_content data output pos'
    header afterHeader hdr1 afterHdr1 block1 afterByte1
    hdr2 afterHdr2 literals2 afterLiterals2 huffTree2
    numSeq2 modes2 afterSeqHeader2 llTable2 ofTable2 mlTable2 afterTables2 bbr2 sequences2
    blockOutput2 newHist2
    hframe hh hparse1 hbs1 hws1 htype1 hrle1 hnotlast1 hadv1
    hoff2 hparse2 hbs2 hws2 htype2 hblockEnd2 hlit2 hseq2 hNumSeq2
    hfse2 hbbr2 hdec2 hexec2 hlast2 hend⟩

/-! ## WellFormedSimpleBlocks frame-level and API-level lifting -/

/-- When a frame has no dictionary, no checksum, and no content size, and its block
    sequence satisfies `WellFormedSimpleBlocks`, `decompressFrame` succeeds.
    This subsumes all specific N-block raw/RLE frame-level succeeds theorems. -/
theorem decompressFrame_succeeds_of_well_formed_simple (data : ByteArray) (pos : Nat)
    (header : Zip.Native.ZstdFrameHeader) (afterHeader : Nat)
    (hparse : Zip.Native.parseFrameHeader data pos = .ok (header, afterHeader))
    (hnodict : header.dictionaryId = none)
    (hnocksum : header.contentChecksum = false)
    (hnosize : header.contentSize = none)
    (hwf : Zstd.Spec.WellFormedSimpleBlocks data afterHeader header.windowSize
      ByteArray.empty none {} #[1, 4, 8]) :
    ∃ content pos',
      Zip.Native.decompressFrame data pos = .ok (content, pos') := by
  -- Step 1: Get block-level success from WellFormedSimpleBlocks induction
  obtain ⟨result, blockPos, hblocks⟩ :=
    Zstd.Spec.decompressBlocksWF_succeeds_of_well_formed_simple
      data afterHeader header.windowSize ByteArray.empty none {} #[1, 4, 8] hwf
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

/-- Three-block raw/RLE/raw corollary at frame level. Demonstrates that
    `decompressFrame_succeeds_of_well_formed_simple` handles N-block mixed
    raw/RLE sequences: construct the `WellFormedSimpleBlocks` chain and apply. -/
theorem decompressFrame_succeeds_three_raw_rle_raw (data : ByteArray) (pos : Nat)
    (header : Zip.Native.ZstdFrameHeader) (afterHeader : Nat)
    (hparse : Zip.Native.parseFrameHeader data pos = .ok (header, afterHeader))
    (hnodict : header.dictionaryId = none)
    (hnocksum : header.contentChecksum = false)
    (hnosize : header.contentSize = none)
    -- Block 1 (non-last raw)
    (hdr1 : Zip.Native.ZstdBlockHeader) (afterHdr1 : Nat)
    (block1 : ByteArray) (afterBlock1 : Nat)
    (hoff1 : ¬ data.size ≤ afterHeader)
    (hparse1 : Zip.Native.parseBlockHeader data afterHeader = .ok (hdr1, afterHdr1))
    (hbs1 : ¬ hdr1.blockSize > 131072)
    (hws1 : ¬ (header.windowSize > 0 && hdr1.blockSize.toUInt64 > header.windowSize))
    (htype1 : hdr1.blockType = .raw)
    (hraw1 : Zip.Native.decompressRawBlock data afterHdr1 hdr1.blockSize
               = .ok (block1, afterBlock1))
    (hnotlast1 : hdr1.lastBlock = false)
    (hadv1 : ¬ afterBlock1 ≤ afterHeader)
    -- Block 2 (non-last RLE)
    (hdr2 : Zip.Native.ZstdBlockHeader) (afterHdr2 : Nat)
    (block2 : ByteArray) (afterByte2 : Nat)
    (hoff2 : ¬ data.size ≤ afterBlock1)
    (hparse2 : Zip.Native.parseBlockHeader data afterBlock1 = .ok (hdr2, afterHdr2))
    (hbs2 : ¬ hdr2.blockSize > 131072)
    (hws2 : ¬ (header.windowSize > 0 && hdr2.blockSize.toUInt64 > header.windowSize))
    (htype2 : hdr2.blockType = .rle)
    (hrle2 : Zip.Native.decompressRLEBlock data afterHdr2 hdr2.blockSize
               = .ok (block2, afterByte2))
    (hnotlast2 : hdr2.lastBlock = false)
    (hadv2 : ¬ afterByte2 ≤ afterBlock1)
    -- Block 3 (last raw)
    (hdr3 : Zip.Native.ZstdBlockHeader) (afterHdr3 : Nat)
    (block3 : ByteArray) (afterBlock3 : Nat)
    (hoff3 : ¬ data.size ≤ afterByte2)
    (hparse3 : Zip.Native.parseBlockHeader data afterByte2 = .ok (hdr3, afterHdr3))
    (hbs3 : ¬ hdr3.blockSize > 131072)
    (hws3 : ¬ (header.windowSize > 0 && hdr3.blockSize.toUInt64 > header.windowSize))
    (htype3 : hdr3.blockType = .raw)
    (hraw3 : Zip.Native.decompressRawBlock data afterHdr3 hdr3.blockSize
               = .ok (block3, afterBlock3))
    (hlast3 : hdr3.lastBlock = true) :
    ∃ content pos',
      Zip.Native.decompressFrame data pos = .ok (content, pos') :=
  decompressFrame_succeeds_of_well_formed_simple data pos header afterHeader
    hparse hnodict hnocksum hnosize
    (.step_raw afterHeader header.windowSize ByteArray.empty none {} #[1, 4, 8]
      hdr1 afterHdr1 block1 afterBlock1
      hoff1 hparse1 hbs1 hws1 htype1 hraw1 hnotlast1 hadv1
      (.step_rle afterBlock1 header.windowSize (ByteArray.empty ++ block1) none {} #[1, 4, 8]
        hdr2 afterHdr2 block2 afterByte2
        hoff2 hparse2 hbs2 hws2 htype2 hrle2 hnotlast2 hadv2
        (.last_raw afterByte2 header.windowSize (ByteArray.empty ++ block1 ++ block2) none {} #[1, 4, 8]
          hdr3 afterHdr3 block3 afterBlock3
          hoff3 hparse3 hbs3 hws3 htype3 hraw3 hlast3)))

/-- When the input contains exactly one standard Zstd frame at position 0 whose block
    sequence satisfies `WellFormedSimpleBlocks`, `decompressZstd` succeeds. This lifts
    `decompressFrame_succeeds_of_well_formed_simple` to the top-level API. -/
theorem decompressZstd_single_frame_succeeds_of_well_formed_simple (data : ByteArray)
    (header : Zip.Native.ZstdFrameHeader) (afterHeader : Nat)
    (hparse : Zip.Native.parseFrameHeader data 0 = .ok (header, afterHeader))
    (hnodict : header.dictionaryId = none)
    (hnocksum : header.contentChecksum = false)
    (hnosize : header.contentSize = none)
    (hwf : Zstd.Spec.WellFormedSimpleBlocks data afterHeader header.windowSize
      ByteArray.empty none {} #[1, 4, 8])
    (hterm : ∀ content pos', Zip.Native.decompressFrame data 0 = .ok (content, pos')
        → pos' ≥ data.size) :
    ∃ output, Zip.Native.decompressZstd data = .ok output := by
  obtain ⟨content, pos', hframe⟩ := decompressFrame_succeeds_of_well_formed_simple
    data 0 header afterHeader hparse hnodict hnocksum hnosize hwf
  exact ⟨content, decompressZstd_single_frame data content pos' hframe (hterm content pos' hframe)⟩

/-! ## Unified API-level completeness via WellFormedBlocks -/

/-- When the input contains a standard Zstd frame at position 0 with a well-formed
    block sequence (raw, RLE, compressed zero-seq, or compressed sequences in any
    combination and order), `decompressZstd` succeeds.  This subsumes all 16 specific
    `decompressZstd_succeeds_*` two-block theorems and generalizes to arbitrary N-block
    sequences.

    Proof chain:
    1. `parseFrameHeader_succeeds` (magic + size → header parsed)
    2. `decompressFrame_succeeds_of_well_formed` (header + WellFormedBlocks → frame success)
    3. `decompressZstd_single_frame` (frame success + end-of-data → API success) -/
theorem decompressZstd_succeeds_of_well_formed (data : ByteArray)
    -- Frame header conditions
    (hmagic : Binary.readUInt32LE data 0 = Zip.Native.zstdMagic)
    (hframeSize : data.size ≥ Zstd.Spec.frameHeaderMinSize data[4]!)
    -- Header field constraints (universally quantified over parseFrameHeader result)
    (hnodict : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.dictionaryId = none)
    (hnocksum : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.contentChecksum = false)
    (hnosize : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.contentSize = none)
    -- Block sequence is well-formed (universally quantified over parseFrameHeader result)
    (hwf : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → Zstd.Spec.WellFormedBlocks data afterHdr hdr.windowSize
            ByteArray.empty none {} #[1, 4, 8])
    -- Frame terminates the data
    (hterm : ∀ content pos', Zip.Native.decompressFrame data 0 = .ok (content, pos')
        → pos' ≥ data.size) :
    ∃ output, Zip.Native.decompressZstd data = .ok output := by
  -- Step 1: Obtain header from parseFrameHeader_succeeds
  obtain ⟨hdr, afterHdr, hparse⟩ :=
    Zstd.Spec.parseFrameHeader_succeeds data 0 hmagic
      (by simpa only [Nat.zero_add] using hframeSize)
  -- Step 2: Get frame-level success from WellFormedBlocks
  obtain ⟨content, pos', hframe⟩ :=
    Zstd.Spec.decompressFrame_succeeds_of_well_formed data 0 hdr afterHdr hparse
      (hnodict hdr afterHdr hparse) (hnocksum hdr afterHdr hparse)
      (hnosize hdr afterHdr hparse) (hwf hdr afterHdr hparse)
  -- Step 3: Lift to API level
  exact ⟨content, decompressZstd_single_frame data content pos' hframe
    (hterm content pos' hframe)⟩

/-- Three-block corollary: a raw block followed by a compressed-zero-seq block followed
    by an RLE block.  Demonstrates that `decompressZstd_succeeds_of_well_formed` handles
    arbitrary N-block mixed sequences at the API level.

    The proof constructs a `WellFormedBlocks` term from the three individual block
    hypotheses and applies `decompressZstd_succeeds_of_well_formed`. -/
theorem decompressZstd_succeeds_three_blocks_raw_czs_rle (data : ByteArray)
    (header : Zip.Native.ZstdFrameHeader) (afterHeader : Nat)
    -- Frame header
    (hparse : Zip.Native.parseFrameHeader data 0 = .ok (header, afterHeader))
    (hnodict : header.dictionaryId = none)
    (hnocksum : header.contentChecksum = false)
    (hnosize : header.contentSize = none)
    -- Block 1: raw (not last)
    (hdr1 : Zip.Native.ZstdBlockHeader) (afterHdr1 : Nat)
    (block1 : ByteArray) (afterBlock1 : Nat)
    (hoff1 : ¬ data.size ≤ afterHeader)
    (hparse1 : Zip.Native.parseBlockHeader data afterHeader = .ok (hdr1, afterHdr1))
    (hbs1 : ¬ hdr1.blockSize > 131072)
    (hws1 : ¬ (header.windowSize > 0 && hdr1.blockSize.toUInt64 > header.windowSize))
    (htype1 : hdr1.blockType = .raw)
    (hraw1 : Zip.Native.decompressRawBlock data afterHdr1 hdr1.blockSize
      = .ok (block1, afterBlock1))
    (hnotlast1 : hdr1.lastBlock = false)
    (hadv1 : ¬ afterBlock1 ≤ afterHeader)
    -- Block 2: compressed zero-seq (not last)
    (hdr2 : Zip.Native.ZstdBlockHeader) (afterHdr2 : Nat)
    (literals2 : ByteArray) (afterLiterals2 : Nat)
    (huffTree2 : Option Zip.Native.ZstdHuffmanTable)
    (modes2 : Zip.Native.SequenceCompressionModes) (afterSeqHeader2 : Nat)
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
    (hnotlast2 : hdr2.lastBlock = false)
    (hadv2 : ¬ afterHdr2 + hdr2.blockSize.toNat ≤ afterBlock1)
    -- Block 3: rle (last)
    (hdr3 : Zip.Native.ZstdBlockHeader) (afterHdr3 : Nat)
    (block3 : ByteArray) (afterByte3 : Nat)
    (hoff3 : ¬ data.size ≤ afterHdr2 + hdr2.blockSize.toNat)
    (hparse3 : Zip.Native.parseBlockHeader data (afterHdr2 + hdr2.blockSize.toNat)
      = .ok (hdr3, afterHdr3))
    (hbs3 : ¬ hdr3.blockSize > 131072)
    (hws3 : ¬ (header.windowSize > 0 && hdr3.blockSize.toUInt64 > header.windowSize))
    (htype3 : hdr3.blockType = .rle)
    (hrle3 : Zip.Native.decompressRLEBlock data afterHdr3 hdr3.blockSize
      = .ok (block3, afterByte3))
    (hlast3 : hdr3.lastBlock = true)
    -- Frame terminates the data
    (hterm : ∀ content pos', Zip.Native.decompressFrame data 0 = .ok (content, pos')
        → pos' ≥ data.size) :
    ∃ output, Zip.Native.decompressZstd data = .ok output := by
  -- Step 1: Construct the WellFormedBlocks term: step_raw → step_compressed_zero_seq → last_rle
  have hwf : Zstd.Spec.WellFormedBlocks data afterHeader header.windowSize
      ByteArray.empty none {} #[1, 4, 8] := by
    apply Zstd.Spec.WellFormedBlocks.step_raw
      (hoff := hoff1) (hparse := hparse1) (hbs := hbs1) (hws := hws1)
      (htype := htype1) (hraw := hraw1) (hnotlast := hnotlast1) (hadv := hadv1)
    apply Zstd.Spec.WellFormedBlocks.step_compressed_zero_seq
      (hoff := hoff2) (hparse := hparse2) (hbs := hbs2) (hws := hws2)
      (htype := htype2) (hblockEnd := hblockEnd2)
      (hlit := hlit2) (hseq := hseq2) (hnotlast := hnotlast2) (hadv := hadv2)
    exact Zstd.Spec.WellFormedBlocks.last_rle _ _ _ _ _ _
      hdr3 afterHdr3 block3 afterByte3
      hoff3 hparse3 hbs3 hws3 htype3 hrle3 hlast3
  -- Step 2: Get frame-level success from WellFormedBlocks
  obtain ⟨content, pos', hframe⟩ :=
    Zstd.Spec.decompressFrame_succeeds_of_well_formed data 0 header afterHeader hparse
      hnodict hnocksum hnosize hwf
  -- Step 3: Lift to API level
  exact ⟨content, decompressZstd_single_frame data content pos' hframe
    (hterm content pos' hframe)⟩

/-! ## Unified frame-level and API-level completeness via WellFormedSimpleBlocks -/

/-- When the input contains a standard Zstd frame at position 0 with a well-formed
    sequence of raw/RLE blocks (per `WellFormedSimpleBlocks`), `decompressZstd` succeeds.
    This subsumes all specific `decompressZstd_succeeds_*` two-block theorems for raw/RLE
    combinations and generalizes to arbitrary N-block raw/RLE sequences.

    Proof chain:
    1. `parseFrameHeader_succeeds` (magic + size → header parsed)
    2. `decompressFrame_succeeds_of_well_formed_simple` (header + WellFormedSimpleBlocks → frame)
    3. `decompressZstd_single_frame` (frame success + end-of-data → API success) -/
theorem decompressZstd_succeeds_of_well_formed_simple (data : ByteArray)
    -- Frame header conditions
    (hmagic : Binary.readUInt32LE data 0 = Zip.Native.zstdMagic)
    (hframeSize : data.size ≥ Zstd.Spec.frameHeaderMinSize data[4]!)
    -- Header field constraints (universally quantified over parseFrameHeader result)
    (hnodict : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.dictionaryId = none)
    (hnocksum : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.contentChecksum = false)
    (hnosize : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.contentSize = none)
    -- Block sequence is well-formed (universally quantified over parseFrameHeader result)
    (hwf : ∀ hdr afterHdr, Zip.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → Zstd.Spec.WellFormedSimpleBlocks data afterHdr hdr.windowSize
            ByteArray.empty none {} #[1, 4, 8])
    -- Frame terminates the data
    (hterm : ∀ content pos', Zip.Native.decompressFrame data 0 = .ok (content, pos')
        → pos' ≥ data.size) :
    ∃ output, Zip.Native.decompressZstd data = .ok output := by
  -- Step 1: Obtain header from parseFrameHeader_succeeds
  obtain ⟨hdr, afterHdr, hparse⟩ :=
    Zstd.Spec.parseFrameHeader_succeeds data 0 hmagic
      (by simpa only [Nat.zero_add] using hframeSize)
  -- Step 2: Get frame-level success from WellFormedSimpleBlocks
  obtain ⟨content, pos', hframe⟩ :=
    decompressFrame_succeeds_of_well_formed_simple data 0 hdr afterHdr hparse
      (hnodict hdr afterHdr hparse) (hnocksum hdr afterHdr hparse)
      (hnosize hdr afterHdr hparse) (hwf hdr afterHdr hparse)
  -- Step 3: Lift to API level
  exact ⟨content, decompressZstd_single_frame data content pos' hframe
    (hterm content pos' hframe)⟩

/-- Three-block corollary: a raw block followed by an RLE block followed by a raw block.
    Demonstrates that `decompressZstd_succeeds_of_well_formed_simple` handles
    arbitrary N-block raw/RLE sequences at the API level.

    The proof constructs a `WellFormedSimpleBlocks` term from the three individual block
    hypotheses and applies `decompressZstd_succeeds_of_well_formed_simple`. -/
theorem decompressZstd_succeeds_three_blocks_raw_rle_raw_simple (data : ByteArray)
    (header : Zip.Native.ZstdFrameHeader) (afterHeader : Nat)
    -- Frame header
    (hparse : Zip.Native.parseFrameHeader data 0 = .ok (header, afterHeader))
    (hnodict : header.dictionaryId = none)
    (hnocksum : header.contentChecksum = false)
    (hnosize : header.contentSize = none)
    -- Block 1: raw (not last)
    (hdr1 : Zip.Native.ZstdBlockHeader) (afterHdr1 : Nat)
    (block1 : ByteArray) (afterBlock1 : Nat)
    (hoff1 : ¬ data.size ≤ afterHeader)
    (hparse1 : Zip.Native.parseBlockHeader data afterHeader = .ok (hdr1, afterHdr1))
    (hbs1 : ¬ hdr1.blockSize > 131072)
    (hws1 : ¬ (header.windowSize > 0 && hdr1.blockSize.toUInt64 > header.windowSize))
    (htype1 : hdr1.blockType = .raw)
    (hraw1 : Zip.Native.decompressRawBlock data afterHdr1 hdr1.blockSize
      = .ok (block1, afterBlock1))
    (hnotlast1 : hdr1.lastBlock = false)
    (hadv1 : ¬ afterBlock1 ≤ afterHeader)
    -- Block 2: rle (not last)
    (hdr2 : Zip.Native.ZstdBlockHeader) (afterHdr2 : Nat)
    (block2 : ByteArray) (afterByte2 : Nat)
    (hoff2 : ¬ data.size ≤ afterBlock1)
    (hparse2 : Zip.Native.parseBlockHeader data afterBlock1 = .ok (hdr2, afterHdr2))
    (hbs2 : ¬ hdr2.blockSize > 131072)
    (hws2 : ¬ (header.windowSize > 0 && hdr2.blockSize.toUInt64 > header.windowSize))
    (htype2 : hdr2.blockType = .rle)
    (hrle2 : Zip.Native.decompressRLEBlock data afterHdr2 hdr2.blockSize
      = .ok (block2, afterByte2))
    (hnotlast2 : hdr2.lastBlock = false)
    (hadv2 : ¬ afterByte2 ≤ afterBlock1)
    -- Block 3: raw (last)
    (hdr3 : Zip.Native.ZstdBlockHeader) (afterHdr3 : Nat)
    (block3 : ByteArray) (afterBlock3 : Nat)
    (hoff3 : ¬ data.size ≤ afterByte2)
    (hparse3 : Zip.Native.parseBlockHeader data afterByte2 = .ok (hdr3, afterHdr3))
    (hbs3 : ¬ hdr3.blockSize > 131072)
    (hws3 : ¬ (header.windowSize > 0 && hdr3.blockSize.toUInt64 > header.windowSize))
    (htype3 : hdr3.blockType = .raw)
    (hraw3 : Zip.Native.decompressRawBlock data afterHdr3 hdr3.blockSize
      = .ok (block3, afterBlock3))
    (hlast3 : hdr3.lastBlock = true)
    -- Frame terminates the data
    (hterm : ∀ content pos', Zip.Native.decompressFrame data 0 = .ok (content, pos')
        → pos' ≥ data.size) :
    ∃ output, Zip.Native.decompressZstd data = .ok output := by
  -- Step 1: Construct WellFormedSimpleBlocks: step_raw → step_rle → last_raw
  have hwf : Zstd.Spec.WellFormedSimpleBlocks data afterHeader header.windowSize
      ByteArray.empty none {} #[1, 4, 8] := by
    apply Zstd.Spec.WellFormedSimpleBlocks.step_raw
      (hoff := hoff1) (hparse := hparse1) (hbs := hbs1) (hws := hws1)
      (htype := htype1) (hraw := hraw1) (hnotlast := hnotlast1) (hadv := hadv1)
    apply Zstd.Spec.WellFormedSimpleBlocks.step_rle
      (hoff := hoff2) (hparse := hparse2) (hbs := hbs2) (hws := hws2)
      (htype := htype2) (hrle := hrle2) (hnotlast := hnotlast2) (hadv := hadv2)
    exact Zstd.Spec.WellFormedSimpleBlocks.last_raw _ _ _ _ _ _
      hdr3 afterHdr3 block3 afterBlock3
      hoff3 hparse3 hbs3 hws3 htype3 hraw3 hlast3
  -- Step 2: Get frame-level success from WellFormedSimpleBlocks
  obtain ⟨content, pos', hframe⟩ :=
    decompressFrame_succeeds_of_well_formed_simple data 0 header afterHeader hparse
      hnodict hnocksum hnosize hwf
  -- Step 3: Lift to API level
  exact ⟨content, decompressZstd_single_frame data content pos' hframe
    (hterm content pos' hframe)⟩

end Zip.Spec.ZstdFrame
