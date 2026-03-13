import Zip.Spec.ZstdFrameSimpleComplete

/-!
# Zstandard Composed Completeness — Compressed-First Block Combinations

Composed completeness theorems for `decompressZstd` with two-block frames
where the first block is a compressed block (either zero-sequence or
with sequences).

Each theorem composes the full chain:
1. `parseFrameHeader_succeeds` (byte-level → frame header parsed)
2. `decompressFrame_succeeds_*` (header + blocks → frame success)
3. `decompressZstd_single_frame` (frame success + end-of-data → API success)

Covers all combinations:
- compressed_zero_seq + {raw, RLE, compressed_zero_seq, compressed_sequences}
- compressed_sequences + {raw, RLE, compressed_zero_seq, compressed_sequences}
- {raw, RLE} + compressed_sequences

See `ZstdFrameSimpleComplete` for raw/RLE-first block combinations.
See `ZstdFrame` for unified completeness via `WellFormedSimpleBlocks`.
-/

namespace Zip.Spec.ZstdFrame

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


end Zip.Spec.ZstdFrame
