import Zip.Spec.ZstdFrameCompComplete

/-!
# Zstandard Top-Level Decompressor — Unified Completeness

Unified completeness theorems for `decompressZstd` via `WellFormedSimpleBlocks`
and `WellFormedBlocks` predicates (RFC 8878 §3.1).

These theorems subsume all specific N-block completeness theorems from
`ZstdFrameSimpleComplete` and `ZstdFrameCompComplete` by lifting the
block-level `WellFormedSimpleBlocks` / `WellFormedBlocks` predicates
to frame-level and API-level success.

See `ZstdFrameBase` for foundation theorems and content characterization.
See `ZstdFrameSimpleComplete` for raw/RLE-first block combinations.
See `ZstdFrameCompComplete` for compressed-first block combinations.
-/

namespace Zip.Spec.ZstdFrame

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
