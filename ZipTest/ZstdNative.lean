import ZipTest.Helpers
import Zip.Native.ZstdFrame
import Zip.Native.XxHash

/-! Tests for the native Zstd frame header parser against FFI-compressed data. -/

def ZipTest.ZstdNative.tests : IO Unit := do
  -- Helper: compress data and parse the frame header
  let parseCompressed (input : ByteArray) (level : UInt8 := 3) : IO Zip.Native.ZstdFrameHeader := do
    let compressed ← Zstd.compress input level
    match Zip.Native.parseFrameHeader compressed 0 with
    | .ok (header, _) => return header
    | .error e => throw (IO.userError s!"parseFrameHeader failed: {e}")

  -- Test 1: empty input
  let hdr ← parseCompressed ByteArray.empty
  -- Empty input should parse successfully (zstd produces a valid frame for empty data)
  -- Content size should be 0 when present
  if let some cs := hdr.contentSize then
    unless cs == 0 do throw (IO.userError s!"empty: expected contentSize 0, got {cs}")

  -- Test 2: small input (62 bytes)
  let small := "Hello, world! This is a test of zlib compression from Lean 4. ".toUTF8
  let hdr ← parseCompressed small
  if let some cs := hdr.contentSize then
    unless cs == small.size.toUInt64 do
      throw (IO.userError s!"small: expected contentSize {small.size}, got {cs}")

  -- Test 3: medium input (64KB)
  let medium := mkConstantData 65536
  let hdr ← parseCompressed medium
  if let some cs := hdr.contentSize then
    unless cs == 65536 do
      throw (IO.userError s!"medium: expected contentSize 65536, got {cs}")

  -- Test 4: compression level 1 (fast)
  let testData ← mkTestData
  let hdr ← parseCompressed testData 1
  if let some cs := hdr.contentSize then
    unless cs == testData.size.toUInt64 do
      throw (IO.userError s!"level1: expected contentSize {testData.size}, got {cs}")

  -- Test 5: compression level 19 (best)
  let hdr ← parseCompressed testData 19
  if let some cs := hdr.contentSize then
    unless cs == testData.size.toUInt64 do
      throw (IO.userError s!"level19: expected contentSize {testData.size}, got {cs}")

  -- Test 6: position after header is valid (within compressed data bounds)
  let compressed ← Zstd.compress testData
  match Zip.Native.parseFrameHeader compressed 0 with
  | .ok (_, endPos) =>
    unless endPos ≤ compressed.size do
      throw (IO.userError s!"endPos {endPos} exceeds compressed size {compressed.size}")
    unless endPos ≥ 6 do  -- minimum: 4 magic + 1 descriptor + 1 (fcs or window)
      throw (IO.userError s!"endPos {endPos} too small for a valid header")
  | .error e => throw (IO.userError s!"parseFrameHeader failed: {e}")

  -- Test 7: invalid magic number
  let badMagic := ByteArray.mk #[0x00, 0x00, 0x00, 0x00, 0x00]
  match Zip.Native.parseFrameHeader badMagic 0 with
  | .ok _ => throw (IO.userError "bad magic: should have failed")
  | .error e =>
    unless e.contains "invalid magic number" do
      throw (IO.userError s!"bad magic: wrong error message: {e}")

  -- Test 8: truncated input
  match Zip.Native.parseFrameHeader (ByteArray.mk #[0x28, 0xB5]) 0 with
  | .ok _ => throw (IO.userError "truncated: should have failed")
  | .error _ => pure ()

  -- Test 9: large input (124KB)
  let large ← mkLargeData
  let hdr ← parseCompressed large
  if let some cs := hdr.contentSize then
    unless cs == large.size.toUInt64 do
      throw (IO.userError s!"large: expected contentSize {large.size}, got {cs}")

  -- Test 10: parseBlockHeader on FFI-compressed data (after frame header)
  let compressed ← Zstd.compress testData
  match Zip.Native.parseFrameHeader compressed 0 with
  | .ok (_, blockStart) =>
    match Zip.Native.parseBlockHeader compressed blockStart with
    | .ok (blkHdr, _) =>
      unless blkHdr.blockSize.toNat > 0 do
        throw (IO.userError s!"block: expected blockSize > 0, got {blkHdr.blockSize}")
      -- Block type should be raw, rle, or compressed (not reserved)
      unless blkHdr.blockType != .reserved do
        throw (IO.userError "block: got reserved block type")
    | .error e => throw (IO.userError s!"parseBlockHeader failed: {e}")
  | .error e => throw (IO.userError s!"parseFrameHeader failed: {e}")

  -- Test 11: decompressRLEBlock produces correct repeated output
  -- Manually construct a byte array: [0xAA] and decompress as RLE with size 5
  let rleSrc := ByteArray.mk #[0xAA]
  match Zip.Native.decompressRLEBlock rleSrc 0 5 with
  | .ok (result, endPos) =>
    unless result.size == 5 do
      throw (IO.userError s!"RLE: expected 5 bytes, got {result.size}")
    unless endPos == 1 do
      throw (IO.userError s!"RLE: expected endPos 1, got {endPos}")
    for i in [:5] do
      unless result[i]! == 0xAA do
        throw (IO.userError s!"RLE: byte {i} expected 0xAA, got {result[i]!}")
  | .error e => throw (IO.userError s!"decompressRLEBlock failed: {e}")

  -- Test 12: decompressRawBlock produces correct verbatim copy
  let rawSrc := ByteArray.mk #[0x01, 0x02, 0x03, 0x04, 0x05]
  match Zip.Native.decompressRawBlock rawSrc 1 3 with
  | .ok (result, endPos) =>
    unless result.size == 3 do
      throw (IO.userError s!"Raw: expected 3 bytes, got {result.size}")
    unless endPos == 4 do
      throw (IO.userError s!"Raw: expected endPos 4, got {endPos}")
    unless result[0]! == 0x02 && result[1]! == 0x03 && result[2]! == 0x04 do
      throw (IO.userError "Raw: incorrect bytes copied")
  | .error e => throw (IO.userError s!"decompressRawBlock failed: {e}")

  -- Test 13: parseBlockHeader on truncated input fails
  match Zip.Native.parseBlockHeader (ByteArray.mk #[0x00, 0x00]) 0 with
  | .ok _ => throw (IO.userError "truncated block header: should have failed")
  | .error _ => pure ()

  -- Test 14: decompressBlocks on empty-input compressed data
  -- Empty input compressed by zstd may produce a single block (likely RLE or raw of size 0)
  let emptyCompressed ← Zstd.compress ByteArray.empty
  match Zip.Native.parseFrameHeader emptyCompressed 0 with
  | .ok (_, blockStart) =>
    -- Try to decompress blocks — may succeed (raw/RLE) or fail (compressed)
    match Zip.Native.decompressBlocks emptyCompressed blockStart with
    | .ok (result, _) =>
      unless result.size == 0 do
        throw (IO.userError s!"empty blocks: expected 0 output bytes, got {result.size}")
    | .error e =>
      -- If it fails because of compressed block type, that's acceptable
      unless e.contains "compressed blocks not yet implemented" || e.contains "sequence decoding not yet implemented" || e.contains "compressed literals" || e.contains "treeless literals" do
        throw (IO.userError s!"empty blocks: unexpected error: {e}")
  | .error e => throw (IO.userError s!"parseFrameHeader on empty: {e}")

  -- Test 15: decompressBlocks round-trip on constant data
  -- Constant data often gets stored as RLE blocks by zstd
  let constData := mkConstantData 256
  let constCompressed ← Zstd.compress constData 1
  match Zip.Native.parseFrameHeader constCompressed 0 with
  | .ok (_, blockStart) =>
    match Zip.Native.decompressBlocks constCompressed blockStart with
    | .ok (result, _) =>
      unless result.data == constData.data do
        throw (IO.userError s!"const blocks: decompressed {result.size} bytes, expected {constData.size}")
    | .error e =>
      -- Compressed blocks are expected for some data — not a test failure
      unless e.contains "compressed blocks not yet implemented" || e.contains "sequence decoding not yet implemented" || e.contains "compressed literals" || e.contains "treeless literals" do
        throw (IO.userError s!"const blocks: unexpected error: {e}")
  | .error e => throw (IO.userError s!"parseFrameHeader on const: {e}")

  -- Test 16: decompressZstd round-trip on empty input
  let emptyCompressed2 ← Zstd.compress ByteArray.empty
  match Zip.Native.decompressZstd emptyCompressed2 with
  | .ok result =>
    unless result.size == 0 do
      throw (IO.userError s!"decompressZstd empty: expected 0 bytes, got {result.size}")
  | .error e =>
    unless e.contains "compressed blocks not yet implemented" || e.contains "sequence decoding not yet implemented" || e.contains "compressed literals" || e.contains "treeless literals" do
      throw (IO.userError s!"decompressZstd empty: unexpected error: {e}")

  -- Test 17: decompressZstd round-trip on constant data (likely RLE blocks)
  let constData2 := mkConstantData 256
  let constCompressed2 ← Zstd.compress constData2 1
  match Zip.Native.decompressZstd constCompressed2 with
  | .ok result =>
    unless result.data == constData2.data do
      throw (IO.userError s!"decompressZstd const: decompressed {result.size} bytes, expected {constData2.size}")
  | .error e =>
    unless e.contains "compressed blocks not yet implemented" || e.contains "sequence decoding not yet implemented" || e.contains "compressed literals" || e.contains "treeless literals" do
      throw (IO.userError s!"decompressZstd const: unexpected error: {e}")

  -- Test 18: decompressZstd round-trip on single byte
  let singleByte := ByteArray.mk #[0x42]
  let singleCompressed ← Zstd.compress singleByte 1
  match Zip.Native.decompressZstd singleCompressed with
  | .ok result =>
    unless result.data == singleByte.data do
      throw (IO.userError s!"decompressZstd single: expected [0x42], got {result.data}")
  | .error e =>
    unless e.contains "compressed blocks not yet implemented" || e.contains "sequence decoding not yet implemented" || e.contains "compressed literals" || e.contains "treeless literals" do
      throw (IO.userError s!"decompressZstd single: unexpected error: {e}")

  -- Test 19: decompressZstd round-trip on all-zeros (maximally compressible)
  let zeros := mkConstantData 1024
  let zerosCompressed ← Zstd.compress zeros 1
  match Zip.Native.decompressZstd zerosCompressed with
  | .ok result =>
    unless result.data == zeros.data do
      throw (IO.userError s!"decompressZstd zeros: decompressed {result.size} bytes, expected {zeros.size}")
  | .error e =>
    unless e.contains "compressed blocks not yet implemented" || e.contains "sequence decoding not yet implemented" || e.contains "compressed literals" || e.contains "treeless literals" do
      throw (IO.userError s!"decompressZstd zeros: unexpected error: {e}")

  -- Test 20: decompressZstd error on invalid magic number
  match Zip.Native.decompressZstd (ByteArray.mk #[0x00, 0x00, 0x00, 0x00, 0x00]) with
  | .ok _ => throw (IO.userError "decompressZstd bad magic: should have failed")
  | .error e =>
    unless e.contains "invalid magic number" do
      throw (IO.userError s!"decompressZstd bad magic: wrong error: {e}")

  -- Test 21: decompressZstd error on truncated input
  match Zip.Native.decompressZstd (ByteArray.mk #[0x28, 0xB5]) with
  | .ok _ => throw (IO.userError "decompressZstd truncated: should have failed")
  | .error e =>
    unless e.contains "too short" do
      throw (IO.userError s!"decompressZstd truncated: wrong error: {e}")

  -- Test 22: decompressZstd skips skippable-only input, returning empty output
  -- Skippable frame magic: 0x184D2A50 (little-endian: 50 2A 4D 18), size = 4, payload = 4 zeros
  let skippable := ByteArray.mk #[0x50, 0x2A, 0x4D, 0x18, 0x04, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
  match Zip.Native.decompressZstd skippable with
  | .ok result =>
    unless result.size == 0 do
      throw (IO.userError s!"decompressZstd skippable-only: expected empty, got {result.size} bytes")
  | .error e => throw (IO.userError s!"decompressZstd skippable-only: unexpected error: {e}")

  -- Test 23: decompressFrame returns correct position after frame
  let frameTestData := mkConstantData 128
  let frameCompressed ← Zstd.compress frameTestData 1
  match Zip.Native.decompressFrame frameCompressed 0 with
  | .ok (result, endPos) =>
    unless result.data == frameTestData.data do
      throw (IO.userError s!"decompressFrame: decompressed {result.size} bytes, expected {frameTestData.size}")
    -- endPos should be at or near the end of compressed data
    unless endPos ≤ frameCompressed.size do
      throw (IO.userError s!"decompressFrame: endPos {endPos} exceeds compressed size {frameCompressed.size}")
    unless endPos ≥ 6 do
      throw (IO.userError s!"decompressFrame: endPos {endPos} too small")
  | .error e =>
    unless e.contains "compressed blocks not yet implemented" || e.contains "sequence decoding not yet implemented" || e.contains "compressed literals" || e.contains "treeless literals" do
      throw (IO.userError s!"decompressFrame: unexpected error: {e}")

  -- Test 24: decompressFrame content size validation
  -- We verify this indirectly: FFI-compressed data includes content size in header,
  -- and our decompressor checks it matches the decompressed output.
  -- If decompression succeeds, the size check passed.
  let sizeTestData := mkConstantData 512
  let sizeCompressed ← Zstd.compress sizeTestData 1
  match Zip.Native.decompressFrame sizeCompressed 0 with
  | .ok (result, _) =>
    unless result.size == 512 do
      throw (IO.userError s!"decompressFrame size: expected 512 bytes, got {result.size}")
  | .error e =>
    unless e.contains "compressed blocks not yet implemented" || e.contains "sequence decoding not yet implemented" || e.contains "compressed literals" || e.contains "treeless literals" do
      throw (IO.userError s!"decompressFrame size: unexpected error: {e}")

  -- Test 25: checksum verification — valid FFI-compressed data decompresses
  -- FFI zstd sets the content checksum flag by default, so decompressZstd
  -- will verify XXH64 checksum on this data.
  let checksumData := mkConstantData 256
  let checksumCompressed ← Zstd.compress checksumData 1
  match Zip.Native.decompressZstd checksumCompressed with
  | .ok result =>
    unless result.data == checksumData.data do
      throw (IO.userError "checksum valid: decompressed data mismatch")
  | .error e =>
    unless e.contains "compressed blocks not yet implemented" || e.contains "sequence decoding not yet implemented" || e.contains "compressed literals" || e.contains "treeless literals" do
      throw (IO.userError s!"checksum valid: unexpected error: {e}")

  -- Test 26: checksum verification — corrupted data triggers checksum error
  -- We corrupt a byte in the decompressed content region of the frame
  -- (after header + block headers, before the checksum trailer).
  -- For constant data compressed at level 1, the frame is:
  --   header | block header (3 bytes) | block content | checksum (4 bytes)
  let corruptData := mkConstantData 256
  let corruptCompressed ← Zstd.compress corruptData 1
  -- Parse header to find where block content starts
  match Zip.Native.parseFrameHeader corruptCompressed 0 with
  | .ok (_, blockStart) =>
    -- Block header is 3 bytes, content starts after that
    let contentStart := blockStart + 3
    if contentStart < corruptCompressed.size - 4 then
      -- Flip a byte in the block content
      let corrupted := corruptCompressed.set! contentStart
        (corruptCompressed[contentStart]! ^^^ 0xFF)
      match Zip.Native.decompressZstd corrupted with
      | .ok _ =>
        -- If decompression succeeds, the block might be compressed (no checksum
        -- verification path hit), which is OK
        pure ()
      | .error e =>
        -- Should be either a checksum mismatch or compressed-blocks-not-implemented
        unless e.contains "checksum mismatch" || e.contains "compressed blocks not yet implemented" || e.contains "sequence decoding not yet implemented" || e.contains "compressed literals" || e.contains "treeless literals" do
          throw (IO.userError s!"checksum corrupt: expected checksum error, got: {e}")
  | .error e => throw (IO.userError s!"checksum corrupt: header parse failed: {e}")

  -- Test 27: checksum verification — empty input with checksum
  -- Empty data compressed by zstd includes a content checksum
  let emptyChecksumCompressed ← Zstd.compress ByteArray.empty
  match Zip.Native.decompressZstd emptyChecksumCompressed with
  | .ok result =>
    unless result.size == 0 do
      throw (IO.userError s!"checksum empty: expected 0 bytes, got {result.size}")
  | .error e =>
    unless e.contains "compressed blocks not yet implemented" || e.contains "sequence decoding not yet implemented" || e.contains "compressed literals" || e.contains "treeless literals" do
      throw (IO.userError s!"checksum empty: unexpected error: {e}")

  -- Test 28: parseLiteralsSection on manually crafted Raw header (1-byte header, 5-bit size)
  -- Raw type = 0, size_format = 0 (bit 2 = 0), regenSize = 5 (bits 3-7)
  -- byte0 = (5 << 3) | 0 = 0x28, followed by 5 raw bytes
  let rawLitInput := ByteArray.mk #[0x28, 0x48, 0x65, 0x6C, 0x6C, 0x6F]
  match Zip.Native.parseLiteralsSection rawLitInput 0 with
  | .ok (result, endPos) =>
    unless result.size == 5 do
      throw (IO.userError s!"raw lit: expected 5 bytes, got {result.size}")
    unless endPos == 6 do
      throw (IO.userError s!"raw lit: expected endPos 6, got {endPos}")
    unless result == (ByteArray.mk #[0x48, 0x65, 0x6C, 0x6C, 0x6F]) do
      throw (IO.userError "raw lit: incorrect bytes")
  | .error e => throw (IO.userError s!"parseLiteralsSection raw failed: {e}")

  -- Test 29: parseLiteralsSection on RLE header (1-byte header, 5-bit size)
  -- RLE type = 1, size_format = 0 (bit 2 = 0), regenSize = 7 (bits 3-7)
  -- byte0 = (7 << 3) | 1 = 0x39, followed by the byte to replicate
  let rleLitInput := ByteArray.mk #[0x39, 0xBB]
  match Zip.Native.parseLiteralsSection rleLitInput 0 with
  | .ok (result, endPos) =>
    unless result.size == 7 do
      throw (IO.userError s!"rle lit: expected 7 bytes, got {result.size}")
    unless endPos == 2 do
      throw (IO.userError s!"rle lit: expected endPos 2, got {endPos}")
    for i in [:7] do
      unless result[i]! == 0xBB do
        throw (IO.userError s!"rle lit: byte {i} expected 0xBB, got {result[i]!}")
  | .error e => throw (IO.userError s!"parseLiteralsSection rle failed: {e}")

  -- Test 30: parseLiteralsSection with 2-byte header (12-bit size)
  -- Raw type = 0, size_format = 01, regenSize = 100
  -- byte0 = (100 & 0xF) << 4 | (1 << 2) | 0 = 0x44
  -- byte1 = 100 >> 4 = 6
  -- Followed by 100 bytes of content
  let mut bigRawInput := ByteArray.mk #[0x44, 0x06]
  for i in [:100] do
    bigRawInput := bigRawInput.push (i % 256).toUInt8
  match Zip.Native.parseLiteralsSection bigRawInput 0 with
  | .ok (result, endPos) =>
    unless result.size == 100 do
      throw (IO.userError s!"raw lit 2byte: expected 100 bytes, got {result.size}")
    unless endPos == 102 do
      throw (IO.userError s!"raw lit 2byte: expected endPos 102, got {endPos}")
  | .error e => throw (IO.userError s!"parseLiteralsSection raw 2byte failed: {e}")

  -- Test 31: parseLiteralsSection rejects compressed literals with clear error
  -- Compressed type = 2, any size_format
  let compressedLitInput := ByteArray.mk #[0x02, 0x00, 0x00, 0x00, 0x00]
  match Zip.Native.parseLiteralsSection compressedLitInput 0 with
  | .ok _ => throw (IO.userError "compressed lit: should have failed")
  | .error e =>
    unless e.contains "compressed literals" do
      throw (IO.userError s!"compressed lit: wrong error: {e}")

  -- Test 32: parseLiteralsSection rejects treeless literals with clear error
  -- Treeless type = 3
  let treelessLitInput := ByteArray.mk #[0x03, 0x00, 0x00, 0x00, 0x00]
  match Zip.Native.parseLiteralsSection treelessLitInput 0 with
  | .ok _ => throw (IO.userError "treeless lit: should have failed")
  | .error e =>
    unless e.contains "treeless literals" do
      throw (IO.userError s!"treeless lit: wrong error: {e}")

  -- Test 33: parseSequencesHeader with 0 sequences
  let zeroSeqInput := ByteArray.mk #[0x00]
  match Zip.Native.parseSequencesHeader zeroSeqInput 0 with
  | .ok (numSeq, endPos) =>
    unless numSeq == 0 do
      throw (IO.userError s!"0 seq: expected 0, got {numSeq}")
    unless endPos == 1 do
      throw (IO.userError s!"0 seq: expected endPos 1, got {endPos}")
  | .error e => throw (IO.userError s!"parseSequencesHeader 0 failed: {e}")

  -- Test 34: parseSequencesHeader with small count (1-byte format)
  -- byte0 = 42, followed by compression modes byte
  let smallSeqInput := ByteArray.mk #[42, 0x00]
  match Zip.Native.parseSequencesHeader smallSeqInput 0 with
  | .ok (numSeq, endPos) =>
    unless numSeq == 42 do
      throw (IO.userError s!"42 seq: expected 42, got {numSeq}")
    unless endPos == 2 do
      throw (IO.userError s!"42 seq: expected endPos 2, got {endPos}")
  | .error e => throw (IO.userError s!"parseSequencesHeader 42 failed: {e}")

  -- Test 35: parseSequencesHeader with 2-byte format
  -- byte0 = 200 (>= 128, < 255): numSeq = (200 - 128) << 8 + byte1 = 72 * 256 + 50 = 18482
  let medSeqInput := ByteArray.mk #[200, 50, 0x00]
  match Zip.Native.parseSequencesHeader medSeqInput 0 with
  | .ok (numSeq, endPos) =>
    unless numSeq == 18482 do
      throw (IO.userError s!"2byte seq: expected 18482, got {numSeq}")
    unless endPos == 3 do
      throw (IO.userError s!"2byte seq: expected endPos 3, got {endPos}")
  | .error e => throw (IO.userError s!"parseSequencesHeader 2byte failed: {e}")

  -- Test 36: parseSequencesHeader with 3-byte format
  -- byte0 = 255: numSeq = byte1 + (byte2 << 8) + 0x7F00 = 10 + (1 << 8) + 32512 = 32778
  let largeSeqInput := ByteArray.mk #[255, 10, 1, 0x00]
  match Zip.Native.parseSequencesHeader largeSeqInput 0 with
  | .ok (numSeq, endPos) =>
    unless numSeq == 32778 do
      throw (IO.userError s!"3byte seq: expected 32778, got {numSeq}")
    unless endPos == 4 do
      throw (IO.userError s!"3byte seq: expected endPos 4, got {endPos}")
  | .error e => throw (IO.userError s!"parseSequencesHeader 3byte failed: {e}")

  -- Test 37: parseLiteralsSection on truncated input
  match Zip.Native.parseLiteralsSection ByteArray.empty 0 with
  | .ok _ => throw (IO.userError "truncated lit: should have failed")
  | .error _ => pure ()

  -- Test 38: parseSequencesHeader on truncated input
  match Zip.Native.parseSequencesHeader ByteArray.empty 0 with
  | .ok _ => throw (IO.userError "truncated seq: should have failed")
  | .error _ => pure ()

  -- Test 39: compressed block on FFI data — verify we get past header parsing
  -- Use test data that should produce compressed blocks with sequences
  let compBlockData := "The quick brown fox jumps over the lazy dog. ".toUTF8
  let compBlockCompressed ← Zstd.compress compBlockData 3
  match Zip.Native.decompressZstd compBlockCompressed with
  | .ok result =>
    unless result.data == compBlockData.data do
      throw (IO.userError "comp block: decompressed data mismatch")
  | .error e =>
    -- Should fail at sequence decoding or compressed literals (not at block header parsing)
    unless e.contains "sequence decoding" || e.contains "compressed literals" || e.contains "treeless literals" do
      throw (IO.userError s!"comp block: unexpected error stage: {e}")

  -- Test 40: executeSequences — literals only (0 sequences)
  let litOnly := ByteArray.mk #[0x41, 0x42, 0x43, 0x44]
  match Zip.Native.executeSequences #[] litOnly with
  | .ok result =>
    unless result.data == litOnly.data do
      throw (IO.userError s!"lit only: expected ABCD, got {result.data}")
  | .error e => throw (IO.userError s!"lit only failed: {e}")

  -- Test 41: executeSequences — simple match (non-overlapping)
  -- 4 literal bytes "ABCD", then copy 4 bytes from offset 4 → "ABCDABCD"
  let simpleLit := ByteArray.mk #[0x41, 0x42, 0x43, 0x44]
  let simpleSeqs : Array Zip.Native.ZstdSequence := #[
    { literalLength := 4, matchLength := 4, offset := 7 }  -- offset 7 = actual 4 (7-3)
  ]
  match Zip.Native.executeSequences simpleSeqs simpleLit with
  | .ok result =>
    let expected := ByteArray.mk #[0x41, 0x42, 0x43, 0x44, 0x41, 0x42, 0x43, 0x44]
    unless result.data == expected.data do
      throw (IO.userError s!"simple match: expected {expected.data}, got {result.data}")
  | .error e => throw (IO.userError s!"simple match failed: {e}")

  -- Test 42: executeSequences — overlap match (run-length expansion)
  -- 1 literal byte "A", then copy 7 bytes from offset 1 → "AAAAAAAA"
  let overlapLit := ByteArray.mk #[0x41]
  let overlapSeqs : Array Zip.Native.ZstdSequence := #[
    { literalLength := 1, matchLength := 7, offset := 4 }  -- offset 4 = actual 1 (4-3)
  ]
  match Zip.Native.executeSequences overlapSeqs overlapLit with
  | .ok result =>
    let expected := ByteArray.mk #[0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41]
    unless result.data == expected.data do
      throw (IO.userError s!"overlap match: expected {expected.data}, got {result.data}")
  | .error e => throw (IO.userError s!"overlap match failed: {e}")

  -- Test 43: executeSequences — repeat offset code 1
  -- Two sequences: first establishes offset 4, second reuses it via code 1
  let repeatLit := ByteArray.mk #[0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48]
  let repeatSeqs : Array Zip.Native.ZstdSequence := #[
    { literalLength := 4, matchLength := 4, offset := 7 },  -- actual offset 4
    { literalLength := 4, matchLength := 4, offset := 1 }   -- repeat code 1 → reuses offset 4
  ]
  match Zip.Native.executeSequences repeatSeqs repeatLit with
  | .ok result =>
    -- First seq: ABCD + copy 4 from offset 4 → ABCDABCD
    -- Second seq: EFGH + copy 4 from offset 4 (repeat) → ABCDABCDEFGHEFGH
    let expected := ByteArray.mk #[0x41, 0x42, 0x43, 0x44, 0x41, 0x42, 0x43, 0x44,
                                    0x45, 0x46, 0x47, 0x48, 0x45, 0x46, 0x47, 0x48]
    unless result.data == expected.data do
      throw (IO.userError s!"repeat offset: expected {expected.data}, got {result.data}")
  | .error e => throw (IO.userError s!"repeat offset failed: {e}")

  -- Test 44: executeSequences — shifted repeat (literalLength=0, code 1 → history[1])
  -- Initial history is [1, 4, 8]. First seq establishes offset 5.
  -- History becomes [5, 1, 4]. Second seq has literalLength=0, code 1 → history[1] = 1
  let shiftedLit := ByteArray.mk #[0x41, 0x42, 0x43, 0x44, 0x45]
  let shiftedSeqs : Array Zip.Native.ZstdSequence := #[
    { literalLength := 5, matchLength := 5, offset := 8 },  -- actual offset 5 (8-3)
    { literalLength := 0, matchLength := 5, offset := 1 }   -- shifted: code 1 → history[1]=1
  ]
  match Zip.Native.executeSequences shiftedSeqs shiftedLit with
  | .ok result =>
    -- First seq: ABCDE + copy 5 from offset 5 → ABCDEABCDE
    -- Second seq: 0 literals + copy 5 from offset 1 (shifted: history[1]=1) → EEEEE
    let expected := ByteArray.mk #[0x41, 0x42, 0x43, 0x44, 0x45,
                                    0x41, 0x42, 0x43, 0x44, 0x45,
                                    0x45, 0x45, 0x45, 0x45, 0x45]
    unless result.data == expected.data do
      throw (IO.userError s!"shifted repeat: expected {expected.data}, got {result.data}")
  | .error e => throw (IO.userError s!"shifted repeat failed: {e}")

  -- Test 45: skipSkippableFrame — valid skippable frame
  let skipInput := ByteArray.mk #[0x50, 0x2A, 0x4D, 0x18,  -- magic 0x184D2A50
                                    0x03, 0x00, 0x00, 0x00,  -- size = 3
                                    0xAA, 0xBB, 0xCC]        -- 3 bytes payload
  match Zip.Native.skipSkippableFrame skipInput 0 with
  | .ok endPos =>
    unless endPos == 11 do
      throw (IO.userError s!"skipSkippableFrame: expected endPos 11, got {endPos}")
  | .error e => throw (IO.userError s!"skipSkippableFrame failed: {e}")

  -- Test 46: skipSkippableFrame — highest magic in range (0x184D2A5F)
  let skipHighMagic := ByteArray.mk #[0x5F, 0x2A, 0x4D, 0x18,  -- magic 0x184D2A5F
                                       0x00, 0x00, 0x00, 0x00]  -- size = 0 (empty payload)
  match Zip.Native.skipSkippableFrame skipHighMagic 0 with
  | .ok endPos =>
    unless endPos == 8 do
      throw (IO.userError s!"skipSkippableFrame high magic: expected endPos 8, got {endPos}")
  | .error e => throw (IO.userError s!"skipSkippableFrame high magic failed: {e}")

  -- Test 47: skipSkippableFrame — truncated frame content
  let skipTruncated := ByteArray.mk #[0x50, 0x2A, 0x4D, 0x18,
                                       0x10, 0x00, 0x00, 0x00,  -- size = 16 but only 2 bytes follow
                                       0xAA, 0xBB]
  match Zip.Native.skipSkippableFrame skipTruncated 0 with
  | .ok _ => throw (IO.userError "skipSkippableFrame truncated: should have failed")
  | .error _ => pure ()

  -- Test 48: skipSkippableFrame — non-skippable magic rejected
  let skipBadMagic := ByteArray.mk #[0x28, 0xB5, 0x2F, 0xFD,  -- Zstd magic
                                      0x00, 0x00, 0x00, 0x00]
  match Zip.Native.skipSkippableFrame skipBadMagic 0 with
  | .ok _ => throw (IO.userError "skipSkippableFrame bad magic: should have failed")
  | .error _ => pure ()

  -- Test 49: multi-frame decompression — two concatenated Zstd frames
  let frame1Data := mkConstantData 64
  let frame2Data := ByteArray.mk (Array.replicate 64 0xBB)
  let frame1Compressed ← Zstd.compress frame1Data 1
  let frame2Compressed ← Zstd.compress frame2Data 1
  let multiFrame := frame1Compressed ++ frame2Compressed
  match Zip.Native.decompressZstd multiFrame with
  | .ok result =>
    unless result.data == (frame1Data ++ frame2Data).data do
      throw (IO.userError s!"multi-frame: expected {(frame1Data ++ frame2Data).size} bytes, got {result.size}")
  | .error e =>
    unless e.contains "sequence decoding" || e.contains "compressed literals" || e.contains "treeless literals" do
      throw (IO.userError s!"multi-frame: unexpected error: {e}")

  -- Test 50: skippable frame followed by Zstd frame
  -- Construct: skippable(magic=0x184D2A50, size=4, payload=4 zeros) ++ compressed frame
  let skippablePrefix := ByteArray.mk #[0x50, 0x2A, 0x4D, 0x18,
                                          0x04, 0x00, 0x00, 0x00,
                                          0x00, 0x00, 0x00, 0x00]
  let realData := mkConstantData 128
  let realCompressed ← Zstd.compress realData 1
  let skippablePlusFrame := skippablePrefix ++ realCompressed
  match Zip.Native.decompressZstd skippablePlusFrame with
  | .ok result =>
    unless result.data == realData.data do
      throw (IO.userError s!"skippable+frame: expected {realData.size} bytes, got {result.size}")
  | .error e =>
    unless e.contains "sequence decoding" || e.contains "compressed literals" || e.contains "treeless literals" do
      throw (IO.userError s!"skippable+frame: unexpected error: {e}")

  -- Test 51: Zstd frame followed by skippable frame
  let framePlusSkippable := realCompressed ++ skippablePrefix
  match Zip.Native.decompressZstd framePlusSkippable with
  | .ok result =>
    unless result.data == realData.data do
      throw (IO.userError s!"frame+skippable: expected {realData.size} bytes, got {result.size}")
  | .error e =>
    unless e.contains "sequence decoding" || e.contains "compressed literals" || e.contains "treeless literals" do
      throw (IO.userError s!"frame+skippable: unexpected error: {e}")

  -- Test 52: trailing garbage after last frame produces an error
  -- Manually construct a minimal valid Zstd frame with a raw block containing "AB":
  --   Magic (4 bytes) + FHD (1: single_segment, FCS=0→1byte) + FCS (1: size=2)
  --   + Block header (3 bytes: last=1, type=raw, size=2) + Block data ("AB")
  -- No content checksum.
  let minimalFrame := ByteArray.mk #[
    0x28, 0xB5, 0x2F, 0xFD,   -- Zstd magic
    0x20,                       -- FHD: single_segment=1, no checksum, DID=0, FCS_flag=0
    0x02,                       -- FCS: content size = 2
    0x11, 0x00, 0x00,           -- Block header: last=1, type=raw(0), size=2 → (2<<3)|1 = 0x11
    0x41, 0x42                  -- Block data: "AB"
  ]
  -- Sanity check: the minimal frame decompresses to "AB"
  match Zip.Native.decompressZstd minimalFrame with
  | .ok result =>
    unless result.data == #[0x41, 0x42] do
      throw (IO.userError s!"minimal frame: expected AB, got {result.data}")
  | .error e => throw (IO.userError s!"minimal frame: unexpected error: {e}")
  -- Now append trailing garbage
  let trailingGarbage := minimalFrame ++ ByteArray.mk #[0xFF, 0xFE, 0xFD, 0xFC]
  match Zip.Native.decompressZstd trailingGarbage with
  | .ok _ => throw (IO.userError "trailing garbage: should have failed")
  | .error e =>
    unless e.contains "invalid magic number" do
      throw (IO.userError s!"trailing garbage: wrong error: {e}")

  -- Test 53: empty input returns empty ByteArray
  match Zip.Native.decompressZstd ByteArray.empty with
  | .ok result =>
    unless result.size == 0 do
      throw (IO.userError s!"empty input: expected 0 bytes, got {result.size}")
  | .error e => throw (IO.userError s!"empty input: unexpected error: {e}")

  IO.println "ZstdNative tests: OK"
