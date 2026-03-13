import Zip.Spec.ZstdFrameBase

/-!
# Zstandard Composed Completeness — Simple Block Combinations

Composed completeness theorems for `decompressZstd` with simple block
combinations: single blocks (raw, RLE, compressed) and two-block frames
where the first block is raw or RLE.

Each theorem composes the full chain:
1. `parseFrameHeader_succeeds` (byte-level → frame header parsed)
2. `decompressFrame_succeeds_*` (header + blocks → frame success)
3. `decompressZstd_single_frame` (frame success + end-of-data → API success)

Also includes frame metadata characterization (content size and checksum).

See `ZstdFrameCompComplete` for compressed-first block combinations.
See `ZstdFrame` for unified completeness via `WellFormedSimpleBlocks`.
-/

namespace Zip.Spec.ZstdFrame

/-! ## decompressZstd frame metadata characterizing properties -/

/-- When `decompressZstd` succeeds on a single-frame input whose frame header
    declares `contentSize = some n`, the output has exactly `n` bytes.
    Composes `decompressZstd_single_frame` with `decompressFrame_contentSize_eq`. -/
theorem decompressZstd_single_frame_contentSize (data : ByteArray)
    (content : ByteArray) (pos' : Nat)
    (hframe : Zip.Native.decompressFrame data 0 = .ok (content, pos'))
    (hend : pos' ≥ data.size)
    (header : Zip.Native.ZstdFrameHeader) (headerPos : Nat)
    (hh : Zip.Native.parseFrameHeader data 0 = .ok (header, headerPos))
    (n : UInt64) (hn : header.contentSize = some n) :
    Zip.Native.decompressZstd data = .ok content ∧ content.size.toUInt64 = n :=
  ⟨decompressZstd_single_frame data content pos' hframe hend,
   Zstd.Spec.decompressFrame_contentSize_eq data 0 content pos' hframe header headerPos hh n hn⟩

/-- When `decompressZstd` succeeds on a single-frame input whose frame header
    has `contentChecksum = true`, the output's XXH64 upper 32 bits match the
    checksum stored in the 4 bytes before `pos'` in the input.
    Composes `decompressZstd_single_frame` with `decompressFrame_checksum_valid`. -/
theorem decompressZstd_single_frame_checksum (data : ByteArray)
    (content : ByteArray) (pos' : Nat)
    (hframe : Zip.Native.decompressFrame data 0 = .ok (content, pos'))
    (hend : pos' ≥ data.size)
    (header : Zip.Native.ZstdFrameHeader) (headerPos : Nat)
    (hh : Zip.Native.parseFrameHeader data 0 = .ok (header, headerPos))
    (hc : header.contentChecksum = true) :
    Zip.Native.decompressZstd data = .ok content ∧
      XxHash64.xxHash64Upper32 content = Binary.readUInt32LE data (pos' - 4) :=
  ⟨decompressZstd_single_frame data content pos' hframe hend,
   Zstd.Spec.decompressFrame_checksum_valid data 0 content pos' hframe header headerPos hh hc⟩

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


end Zip.Spec.ZstdFrame
