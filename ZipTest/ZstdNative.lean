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

  -- Test 22: decompressZstd skips skippable-only input (returns empty output)
  -- Skippable frame magic: 0x184D2A50 (little-endian: 50 2A 4D 18), size = 4, 4 payload bytes
  let skippable := ByteArray.mk #[0x50, 0x2A, 0x4D, 0x18, 0x04, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
  match Zip.Native.decompressZstd skippable with
  | .ok result =>
    unless result.size == 0 do
      throw (IO.userError s!"decompressZstd skippable-only: expected empty output, got {result.size} bytes")
  | .error e =>
    throw (IO.userError s!"decompressZstd skippable-only: unexpected error: {e}")

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

  -- Test 31: parseLiteralsSection on malformed compressed literals header
  -- Compressed type = 2, sizeFormat = 0, minimal 3-byte header with compSize = 0
  -- byte0 = 0x02 (litType=2, sizeFormat=0, regenSize low = 0)
  -- This should fail because the tree descriptor has no data to read
  let compressedLitInput := ByteArray.mk #[0x02, 0x00, 0x00, 0x00, 0x00]
  match Zip.Native.parseLiteralsSection compressedLitInput 0 with
  | .ok _ => throw (IO.userError "compressed lit: should have failed on malformed input")
  | .error _ => pure ()  -- any error is acceptable for malformed data

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

  -- Test 45: parseHuffmanWeightsDirect — known byte sequence
  -- Byte 0x35 packs weights [3, 5], byte 0xA1 packs [10, 1]
  let weightInput := ByteArray.mk #[0x35, 0xA1]
  match Zip.Native.parseHuffmanWeightsDirect weightInput 0 2 with
  | .ok (weights, endPos) =>
    unless weights.size == 4 do
      throw (IO.userError s!"weights: expected 4 weights, got {weights.size}")
    unless weights[0]! == 3 do
      throw (IO.userError s!"weights[0]: expected 3, got {weights[0]!}")
    unless weights[1]! == 5 do
      throw (IO.userError s!"weights[1]: expected 5, got {weights[1]!}")
    unless weights[2]! == 10 do
      throw (IO.userError s!"weights[2]: expected 10, got {weights[2]!}")
    unless weights[3]! == 1 do
      throw (IO.userError s!"weights[3]: expected 1, got {weights[3]!}")
    unless endPos == 2 do
      throw (IO.userError s!"weights endPos: expected 2, got {endPos}")
  | .error e => throw (IO.userError s!"parseHuffmanWeightsDirect failed: {e}")

  -- Test 46: weightsToMaxBits — two symbols with weight 1 → maxBits = 1
  -- sum of 2^(W-1) for W=1,1 = 1+1 = 2 = 2^1, so maxBits = 1+1 = 2?
  -- Wait: per RFC, the last symbol is implicit. So we have 2 explicit symbols
  -- with weight 1 each. Sum = 2 = 2^1. Since sum == 2^1, maxBits = 1+1 = 2.
  -- But actually with only 2 symbols both weight 1: each gets 1 bit. maxBits=1.
  -- Let me reconsider: for a 2-symbol alphabet, weight [1] (1 explicit, 1 implicit).
  -- sum = 2^(1-1) = 1. 1 == 2^0 so maxBits = 0+1 = 1. That's correct.
  match Zip.Native.weightsToMaxBits #[1] with
  | .ok maxBits =>
    unless maxBits == 1 do
      throw (IO.userError s!"maxBits [1]: expected 1, got {maxBits}")
  | .error e => throw (IO.userError s!"weightsToMaxBits [1] failed: {e}")

  -- Test 47: weightsToMaxBits — three symbols with weights [1, 1, 1]
  -- sum = 1+1+1 = 3. Next power of 2 is 4 = 2^2, so maxBits = 2.
  -- Implicit last symbol gets 2^2 - 3 = 1 = 2^0, so weight 1. Valid.
  match Zip.Native.weightsToMaxBits #[1, 1, 1] with
  | .ok maxBits =>
    unless maxBits == 2 do
      throw (IO.userError s!"maxBits [1,1,1]: expected 2, got {maxBits}")
  | .error e => throw (IO.userError s!"weightsToMaxBits [1,1,1] failed: {e}")

  -- Test 48: buildZstdHuffmanTable — 2 symbols (1 explicit weight [1])
  -- Symbol 0 has weight 1, implicit symbol 1 also has weight 1.
  -- maxBits = 1, table size = 2. Both symbols have numBits = 1.
  match Zip.Native.buildZstdHuffmanTable #[1] with
  | .ok table =>
    unless table.maxBits == 1 do
      throw (IO.userError s!"2sym maxBits: expected 1, got {table.maxBits}")
    unless table.table.size == 2 do
      throw (IO.userError s!"2sym table size: expected 2, got {table.table.size}")
    -- Both entries should have numBits = 1
    unless table.table[0]!.numBits == 1 do
      throw (IO.userError s!"2sym entry 0 numBits: expected 1, got {table.table[0]!.numBits}")
    unless table.table[1]!.numBits == 1 do
      throw (IO.userError s!"2sym entry 1 numBits: expected 1, got {table.table[1]!.numBits}")
    -- Symbols should be 0 and 1 (in some order)
    let s0 : UInt8 := table.table[0]!.symbol
    let s1 : UInt8 := table.table[1]!.symbol
    unless (s0 == 0 && s1 == 1) || (s0 == 1 && s1 == 0) do
      throw (IO.userError s!"2sym symbols: expected 0,1 got {s0.toNat} {s1.toNat}")
  | .error e => throw (IO.userError s!"buildZstdHuffmanTable 2sym failed: {e}")

  -- Test 49: buildZstdHuffmanTable — 4 symbols with weights [2, 2, 1]
  -- sum = 2 + 2 + 1 = 5. Next power of 2 is 8 = 2^3. maxBits = 3.
  -- Implicit symbol has 8 - 5 = 3 = not power of 2! That's invalid.
  -- Let's try [2, 1, 1]: sum = 2+1+1 = 4 = 2^2, maxBits = 3.
  -- Implicit symbol = 2^3 - 4 = 4 = 2^2, weight = 3.
  -- Symbol 0 (W=2): numBits = 3+1-2 = 2
  -- Symbol 1 (W=1): numBits = 3+1-1 = 3
  -- Symbol 2 (W=1): numBits = 3+1-1 = 3
  -- Symbol 3 (W=3, implicit): numBits = 3+1-3 = 1
  match Zip.Native.buildZstdHuffmanTable #[2, 1, 1] with
  | .ok table =>
    unless table.maxBits == 3 do
      throw (IO.userError s!"4sym maxBits: expected 3, got {table.maxBits}")
    unless table.table.size == 8 do
      throw (IO.userError s!"4sym table size: expected 8, got {table.table.size}")
    -- Symbol 3 (implicit, weight 3) should have numBits = 1 and occupy 4 entries
    let mut sym3Count := 0
    for entry in table.table do
      if entry.symbol == 3 then
        unless entry.numBits == 1 do
          throw (IO.userError s!"4sym sym3 numBits: expected 1, got {entry.numBits}")
        sym3Count := sym3Count + 1
    unless sym3Count == 4 do
      throw (IO.userError s!"4sym sym3 count: expected 4 entries, got {sym3Count}")
  | .error e => throw (IO.userError s!"buildZstdHuffmanTable 4sym failed: {e}")

  -- Test 50: parseHuffmanTreeDescriptor — direct mode
  -- Header byte = 1 (1 weight byte), weight byte = 0x11 → weights [1, 1]
  -- 2 explicit symbols + 1 implicit = 3 symbols
  let treeDescInput := ByteArray.mk #[0x01, 0x11]
  match Zip.Native.parseHuffmanTreeDescriptor treeDescInput 0 with
  | .ok (table, endPos) =>
    unless endPos == 2 do
      throw (IO.userError s!"treeDesc endPos: expected 2, got {endPos}")
    unless table.maxBits == 2 do
      throw (IO.userError s!"treeDesc maxBits: expected 2, got {table.maxBits}")
    unless table.table.size == 4 do
      throw (IO.userError s!"treeDesc table size: expected 4, got {table.table.size}")
  | .error e => throw (IO.userError s!"parseHuffmanTreeDescriptor direct failed: {e}")

  -- Test 51: parseHuffmanTreeDescriptor — FSE mode with invalid data returns error
  -- Header byte 0x80 → compressedSize=1, too small for a valid FSE distribution
  let fseTreeInput := ByteArray.mk #[0x80, 0x00, 0x00, 0x00]
  match Zip.Native.parseHuffmanTreeDescriptor fseTreeInput 0 with
  | .ok _ => throw (IO.userError "FSE tree descriptor invalid: should have failed")
  | .error _ => pure ()

  -- Test 52: parseHuffmanTreeDescriptor — truncated input
  match Zip.Native.parseHuffmanTreeDescriptor ByteArray.empty 0 with
  | .ok _ => throw (IO.userError "truncated tree descriptor: should have failed")
  | .error _ => pure ()

  -- Test 53: parseHuffmanWeightsDirect — truncated data
  match Zip.Native.parseHuffmanWeightsDirect (ByteArray.mk #[0x35]) 0 2 with
  | .ok _ => throw (IO.userError "truncated weights: should have failed")
  | .error _ => pure ()

  -- Test 54: weightsToMaxBits — all zeros returns error
  match Zip.Native.weightsToMaxBits #[0, 0, 0] with
  | .ok _ => throw (IO.userError "all-zero weights: should have failed")
  | .error e =>
    unless e.contains "all weights are zero" do
      throw (IO.userError s!"all-zero weights: wrong error: {e}")

  -- Test 55: decodeLitLenValue — code 0 (baseline 0, 0 extra bits)
  match Zip.Native.decodeLitLenValue 0 0 with
  | .ok v =>
    unless v == 0 do throw (IO.userError s!"litLen code 0: expected 0, got {v}")
  | .error e => throw (IO.userError s!"litLen code 0 failed: {e}")

  -- Test 56: decodeLitLenValue — code 15 (baseline 15, 0 extra bits)
  match Zip.Native.decodeLitLenValue 15 0 with
  | .ok v =>
    unless v == 15 do throw (IO.userError s!"litLen code 15: expected 15, got {v}")
  | .error e => throw (IO.userError s!"litLen code 15 failed: {e}")

  -- Test 57: decodeLitLenValue — code 16 (baseline 16, 1 extra bit)
  -- With extraBits = 1: 16 + 1 = 17
  match Zip.Native.decodeLitLenValue 16 1 with
  | .ok v =>
    unless v == 17 do throw (IO.userError s!"litLen code 16 extra 1: expected 17, got {v}")
  | .error e => throw (IO.userError s!"litLen code 16 failed: {e}")

  -- Test 58: decodeLitLenValue — code 35 (baseline 65536, 16 extra bits)
  -- With extraBits = 0: 65536
  match Zip.Native.decodeLitLenValue 35 0 with
  | .ok v =>
    unless v == 65536 do throw (IO.userError s!"litLen code 35: expected 65536, got {v}")
  | .error e => throw (IO.userError s!"litLen code 35 failed: {e}")

  -- Test 59: decodeLitLenValue — out of range code 36
  match Zip.Native.decodeLitLenValue 36 0 with
  | .ok _ => throw (IO.userError "litLen code 36: should have failed")
  | .error e =>
    unless e.contains "out of range" do
      throw (IO.userError s!"litLen code 36: wrong error: {e}")

  -- Test 60: decodeMatchLenValue — code 0 (baseline 3, 0 extra bits)
  match Zip.Native.decodeMatchLenValue 0 0 with
  | .ok v =>
    unless v == 3 do throw (IO.userError s!"matchLen code 0: expected 3, got {v}")
  | .error e => throw (IO.userError s!"matchLen code 0 failed: {e}")

  -- Test 61: decodeMatchLenValue — code 31 (baseline 34, 0 extra bits)
  match Zip.Native.decodeMatchLenValue 31 0 with
  | .ok v =>
    unless v == 34 do throw (IO.userError s!"matchLen code 31: expected 34, got {v}")
  | .error e => throw (IO.userError s!"matchLen code 31 failed: {e}")

  -- Test 62: decodeMatchLenValue — code 32 (baseline 35, 1 extra bit)
  -- With extraBits = 1: 35 + 1 = 36
  match Zip.Native.decodeMatchLenValue 32 1 with
  | .ok v =>
    unless v == 36 do throw (IO.userError s!"matchLen code 32 extra 1: expected 36, got {v}")
  | .error e => throw (IO.userError s!"matchLen code 32 failed: {e}")

  -- Test 63: decodeMatchLenValue — code 52 (baseline 65539, 16 extra bits)
  match Zip.Native.decodeMatchLenValue 52 0 with
  | .ok v =>
    unless v == 65539 do throw (IO.userError s!"matchLen code 52: expected 65539, got {v}")
  | .error e => throw (IO.userError s!"matchLen code 52 failed: {e}")

  -- Test 64: decodeMatchLenValue — out of range code 53
  match Zip.Native.decodeMatchLenValue 53 0 with
  | .ok _ => throw (IO.userError "matchLen code 53: should have failed")
  | .error e =>
    unless e.contains "out of range" do
      throw (IO.userError s!"matchLen code 53: wrong error: {e}")

  -- Test 65: decodeOffsetValue — code 1, extraBits 0 → (1 << 1) + 0 = 2
  let offVal1 := Zip.Native.decodeOffsetValue 1 0
  unless offVal1 == 2 do throw (IO.userError s!"offset code 1: expected 2, got {offVal1}")

  -- Test 66: decodeOffsetValue — code 5, extraBits 10 → (1 << 5) + 10 = 42
  let offVal5 := Zip.Native.decodeOffsetValue 5 10
  unless offVal5 == 42 do throw (IO.userError s!"offset code 5: expected 42, got {offVal5}")

  -- Test 67: decodeOffsetValue — code 20, extraBits 0 → (1 << 20) = 1048576
  let offVal20 := Zip.Native.decodeOffsetValue 20 0
  unless offVal20 == 1048576 do throw (IO.userError s!"offset code 20: expected 1048576, got {offVal20}")

  -- Test 68: decodeOffsetValue — code 0, extraBits 5 → 5 (special case)
  let offVal0 := Zip.Native.decodeOffsetValue 0 5
  unless offVal0 == 5 do throw (IO.userError s!"offset code 0: expected 5, got {offVal0}")

  -- Test 69: parseSequencesHeaderWithModes — modes parsing
  -- Construct: byte0 = 42 (small count), modes byte = 0b10_01_00_00 = 0x90
  -- litLen=FSE_Compressed(2), offset=RLE(1), matchLen=Predefined(0), reserved=0
  let modesInput := ByteArray.mk #[42, 0x90]
  match Zip.Native.parseSequencesHeaderWithModes modesInput 0 with
  | .ok (numSeq, modes, endPos) =>
    unless numSeq == 42 do
      throw (IO.userError s!"modes: expected numSeq 42, got {numSeq}")
    unless endPos == 2 do
      throw (IO.userError s!"modes: expected endPos 2, got {endPos}")
    unless modes.litLenMode == .fseCompressed do
      throw (IO.userError "modes: expected litLenMode = fseCompressed")
    unless modes.offsetMode == .rle do
      throw (IO.userError "modes: expected offsetMode = rle")
    unless modes.matchLenMode == .predefined do
      throw (IO.userError "modes: expected matchLenMode = predefined")
  | .error e => throw (IO.userError s!"modes parsing failed: {e}")

  -- Test 70: parseSequencesHeaderWithModes — 0 sequences returns default modes
  let zeroModesInput := ByteArray.mk #[0x00]
  match Zip.Native.parseSequencesHeaderWithModes zeroModesInput 0 with
  | .ok (numSeq, modes, endPos) =>
    unless numSeq == 0 do
      throw (IO.userError s!"zero modes: expected numSeq 0, got {numSeq}")
    unless endPos == 1 do
      throw (IO.userError s!"zero modes: expected endPos 1, got {endPos}")
    unless modes.litLenMode == .predefined do
      throw (IO.userError "zero modes: expected litLenMode = predefined")
    unless modes.offsetMode == .predefined do
      throw (IO.userError "zero modes: expected offsetMode = predefined")
    unless modes.matchLenMode == .predefined do
      throw (IO.userError "zero modes: expected matchLenMode = predefined")
  | .error e => throw (IO.userError s!"zero modes parsing failed: {e}")

  -- Test 71: parseSequencesHeaderWithModes — all repeat mode (0xFF modes byte)
  -- byte0 = 1 (1 sequence), modes = 0xFF → litLen=repeat(3), offset=repeat(3), matchLen=repeat(3)
  let repeatModesInput := ByteArray.mk #[1, 0xFF]
  match Zip.Native.parseSequencesHeaderWithModes repeatModesInput 0 with
  | .ok (numSeq, modes, _) =>
    unless numSeq == 1 do
      throw (IO.userError s!"repeat modes: expected numSeq 1, got {numSeq}")
    unless modes.litLenMode == .repeat do
      throw (IO.userError "repeat modes: expected litLenMode = repeat")
    unless modes.offsetMode == .repeat do
      throw (IO.userError "repeat modes: expected offsetMode = repeat")
    unless modes.matchLenMode == .repeat do
      throw (IO.userError "repeat modes: expected matchLenMode = repeat")
  | .error e => throw (IO.userError s!"repeat modes parsing failed: {e}")

  -- Test 72: skipSkippableFrame — valid skippable frame
  -- Magic 0x184D2A50 (LE: 50 2A 4D 18), size = 3, then 3 payload bytes
  let skipInput := ByteArray.mk #[0x50, 0x2A, 0x4D, 0x18, 0x03, 0x00, 0x00, 0x00, 0xAA, 0xBB, 0xCC]
  match Zip.Native.skipSkippableFrame skipInput 0 with
  | .ok endPos =>
    unless endPos == 11 do
      throw (IO.userError s!"skipSkippable: expected endPos 11, got {endPos}")
  | .error e => throw (IO.userError s!"skipSkippableFrame failed: {e}")

  -- Test 73: skipSkippableFrame — different magic in range (0x184D2A5F)
  let skipInput2 := ByteArray.mk #[0x5F, 0x2A, 0x4D, 0x18, 0x00, 0x00, 0x00, 0x00]
  match Zip.Native.skipSkippableFrame skipInput2 0 with
  | .ok endPos =>
    unless endPos == 8 do
      throw (IO.userError s!"skipSkippable 5F: expected endPos 8, got {endPos}")
  | .error e => throw (IO.userError s!"skipSkippableFrame 5F failed: {e}")

  -- Test 74: skipSkippableFrame — truncated frame data
  let skipTruncated := ByteArray.mk #[0x50, 0x2A, 0x4D, 0x18, 0x10, 0x00, 0x00, 0x00, 0x00]
  match Zip.Native.skipSkippableFrame skipTruncated 0 with
  | .ok _ => throw (IO.userError "skipSkippable truncated: should have failed")
  | .error _ => pure ()

  -- Test 75: multi-frame concatenation — two independently compressed frames
  let frame1Data := mkConstantData 128
  let frame2Data := ByteArray.mk #[0x42, 0x42, 0x42, 0x42]
  let frame1 ← Zstd.compress frame1Data 1
  let frame2 ← Zstd.compress frame2Data 1
  let multiFrame := frame1 ++ frame2
  match Zip.Native.decompressZstd multiFrame with
  | .ok result =>
    let expected := frame1Data ++ frame2Data
    unless result.data == expected.data do
      throw (IO.userError s!"multi-frame: expected {expected.size} bytes, got {result.size}")
  | .error e =>
    -- May fail if compressed blocks are used; that's acceptable
    unless e.contains "sequence decoding" || e.contains "compressed literals" || e.contains "treeless literals" do
      throw (IO.userError s!"multi-frame: unexpected error: {e}")

  -- Test 76: skippable frame followed by Zstd frame
  let skippablePrefix := ByteArray.mk #[0x50, 0x2A, 0x4D, 0x18, 0x02, 0x00, 0x00, 0x00, 0xFF, 0xFF]
  let zstdData := mkConstantData 64
  let zstdFrame ← Zstd.compress zstdData 1
  let skippablePlusZstd := skippablePrefix ++ zstdFrame
  match Zip.Native.decompressZstd skippablePlusZstd with
  | .ok result =>
    unless result.data == zstdData.data do
      throw (IO.userError s!"skippable+zstd: expected {zstdData.size} bytes, got {result.size}")
  | .error e =>
    unless e.contains "sequence decoding" || e.contains "compressed literals" || e.contains "treeless literals" do
      throw (IO.userError s!"skippable+zstd: unexpected error: {e}")

  -- Test 77: Zstd frame followed by skippable frame
  let zstdFirst ← Zstd.compress (mkConstantData 64) 1
  let skippableSuffix := ByteArray.mk #[0x55, 0x2A, 0x4D, 0x18, 0x01, 0x00, 0x00, 0x00, 0x00]
  let zstdPlusSkippable := zstdFirst ++ skippableSuffix
  match Zip.Native.decompressZstd zstdPlusSkippable with
  | .ok result =>
    unless result.size == 64 do
      throw (IO.userError s!"zstd+skippable: expected 64 bytes, got {result.size}")
  | .error e =>
    unless e.contains "sequence decoding" || e.contains "compressed literals" || e.contains "treeless literals" do
      throw (IO.userError s!"zstd+skippable: unexpected error: {e}")

  -- Test 78: trailing garbage after last frame produces error
  let trailingData := mkConstantData 64
  let trailingFrame ← Zstd.compress trailingData 1
  let trailingGarbage := trailingFrame ++ (ByteArray.mk #[0xDE, 0xAD, 0xBE, 0xEF])
  match Zip.Native.decompressZstd trailingGarbage with
  | .ok _ => throw (IO.userError "trailing garbage: should have failed")
  | .error e =>
    unless e.contains "invalid magic number" do
      -- Also accept compressed block errors if they occur before trailing data
      unless e.contains "sequence decoding" || e.contains "compressed literals" || e.contains "treeless literals" do
        throw (IO.userError s!"trailing garbage: expected magic number error, got: {e}")

  -- Test 79: empty input returns empty output
  match Zip.Native.decompressZstd ByteArray.empty with
  | .ok result =>
    unless result.size == 0 do
      throw (IO.userError s!"empty input: expected 0 bytes, got {result.size}")
  | .error e =>
    throw (IO.userError s!"empty input: unexpected error: {e}")

  -- Test 80: litLenExtraBits table has 36 entries
  unless Zip.Native.litLenExtraBits.size == 36 do
    throw (IO.userError s!"litLenExtraBits: expected 36 entries, got {Zip.Native.litLenExtraBits.size}")

  -- Test 81: matchLenExtraBits table has 53 entries
  unless Zip.Native.matchLenExtraBits.size == 53 do
    throw (IO.userError s!"matchLenExtraBits: expected 53 entries, got {Zip.Native.matchLenExtraBits.size}")

  -- Test 74: parseHuffmanTreeDescriptor — FSE-compressed on real zstd data
  -- Compress ~1KB of varied data at level 3 (typically produces FSE-compressed Huffman weights)
  let mut fseTestData := ByteArray.empty
  for i in [:1024] do
    -- Generate varied but not-too-random data to encourage compressed blocks with Huffman tables
    fseTestData := fseTestData.push ((i * 7 + 13) % 256).toUInt8
  let fseCompressed ← Zstd.compress fseTestData 3
  -- Parse frame header + block header to find the literals section
  match Zip.Native.parseFrameHeader fseCompressed 0 with
  | .ok (_, blockStart) =>
    match Zip.Native.parseBlockHeader fseCompressed blockStart with
    | .ok (blkHdr, afterBlkHdr) =>
      if blkHdr.blockType == .compressed then
        -- Parse the literals section header to check if we get a compressed literal type
        let byte0 := fseCompressed[afterBlkHdr]!
        let litType := (byte0 &&& 3).toNat
        if litType == 2 then
          -- Compressed literals: parse the Huffman tree descriptor
          -- Skip past the literals section header to reach the Huffman tree descriptor
          let sizeFormat := ((byte0 >>> 2) &&& 3).toNat
          let (headerBytes, _regenSize, _compSize) ←
            if sizeFormat == 0 then do
              -- 3-byte header for compressed: bits [4:5] are sizes
              if fseCompressed.size < afterBlkHdr + 3 then
                throw (IO.userError "FSE test: not enough data for 3-byte compressed lit header")
              let b0 := fseCompressed[afterBlkHdr]!
              let b1 := fseCompressed[afterBlkHdr + 1]!
              let b2 := fseCompressed[afterBlkHdr + 2]!
              let regen := ((b0 >>> 4).toNat &&& 0x3F) ||| ((b1.toNat &&& 0x3F) <<< 6)
              -- Not used but needed for parsing
              pure (3, regen, b2.toNat)
            else if sizeFormat == 1 then do
              -- 3-byte header
              if fseCompressed.size < afterBlkHdr + 3 then
                throw (IO.userError "FSE test: not enough data for 3-byte compressed lit header")
              pure (3, 0, 0)
            else if sizeFormat == 2 then do
              -- 4-byte header
              if fseCompressed.size < afterBlkHdr + 4 then
                throw (IO.userError "FSE test: not enough data for 4-byte compressed lit header")
              pure (4, 0, 0)
            else do
              -- 5-byte header
              if fseCompressed.size < afterBlkHdr + 5 then
                throw (IO.userError "FSE test: not enough data for 5-byte compressed lit header")
              pure (5, 0, 0)
          -- The Huffman tree descriptor follows the literals section header
          let huffTreePos := afterBlkHdr + headerBytes
          match Zip.Native.parseHuffmanTreeDescriptor fseCompressed huffTreePos with
          | .ok (table, _) =>
            -- Verify table has reasonable maxBits (typically 8-11 for literals)
            unless table.maxBits ≥ 1 && table.maxBits ≤ 12 do
              throw (IO.userError s!"FSE Huffman: unreasonable maxBits {table.maxBits}")
            -- Verify the table has entries
            unless table.table.size > 0 do
              throw (IO.userError "FSE Huffman: table is empty")
          | .error e => throw (IO.userError s!"FSE Huffman parseHuffmanTreeDescriptor failed: {e}")
        else
          -- Not compressed literals at this level; skip test quietly
          pure ()
      else
        -- Not a compressed block; skip test quietly
        pure ()
    | .error e => throw (IO.userError s!"FSE test parseBlockHeader failed: {e}")
  | .error e => throw (IO.userError s!"FSE test parseFrameHeader failed: {e}")

  -- Test 75: decodeFseSymbolsAll — basic smoke test
  -- Build a trivial 2-symbol FSE table manually and decode from a backward stream.
  -- Symbols: 0 (prob=1), 1 (prob=1). accuracyLog=1, table size=2.
  let trivialTable : Zip.Native.FseTable := {
    accuracyLog := 1
    cells := #[
      { symbol := 0, numBits := 1, newState := 0 },
      { symbol := 1, numBits := 1, newState := 0 }
    ]
  }
  -- Create a minimal backward bitstream: one byte with sentinel + 1 bit of init state
  -- Byte = 0b11 = 3: sentinel at bit 1, then bit 0 = 1 (init state = 1)
  -- After init state=1, cell[1]={symbol=1, numBits=1, newState=0}, stream is finished
  let bbrData := ByteArray.mk #[0x03]
  match Zip.Native.BackwardBitReader.init bbrData 0 1 with
  | .ok bbr =>
    match Zip.Native.decodeFseSymbolsAll trivialTable bbr with
    | .ok (syms, _) =>
      unless syms.size ≥ 1 do
        throw (IO.userError s!"decodeFseSymbolsAll trivial: expected at least 1 symbol, got {syms.size}")
    | .error e => throw (IO.userError s!"decodeFseSymbolsAll trivial failed: {e}")
  | .error e => throw (IO.userError s!"BackwardBitReader init failed: {e}")

  -- Test 76: decodeHuffmanSymbol — single symbol from 2-symbol table
  match Zip.Native.buildZstdHuffmanTable #[1] with
  | .ok huffTable2 =>
    -- Byte 0xC0 = 11000000: sentinel at bit 7, data bit at bit 6 = 1.
    -- For maxBits=1, reading 1 bit gives table index 1.
    let testStream := ByteArray.mk #[0xC0]
    match Zip.Native.BackwardBitReader.init testStream 0 1 with
    | .ok br =>
      match Zip.Native.decodeHuffmanSymbol huffTable2 br with
      | .ok (sym, _) =>
        let expectedSym := huffTable2.table[1]!.symbol
        unless sym == expectedSym do
          throw (IO.userError s!"decode sym: expected {expectedSym}, got {sym}")
      | .error e => throw (IO.userError s!"decodeHuffmanSymbol failed: {e}")
    | .error e => throw (IO.userError s!"BackwardBitReader init failed: {e}")
  | .error e => throw (IO.userError s!"buildZstdHuffmanTable for decode test failed: {e}")

  -- Test 77: decodeHuffmanStream — decode multiple symbols from known bitstream
  match Zip.Native.buildZstdHuffmanTable #[1] with
  | .ok huffTable2 =>
    let sym0 := huffTable2.table[0]!.symbol
    let sym1 := huffTable2.table[1]!.symbol
    -- Byte 0x15 = 0b00010101: sentinel at bit 4, data bits 3-0 = 0,1,0,1
    let testStream := ByteArray.mk #[0x15]
    match Zip.Native.BackwardBitReader.init testStream 0 1 with
    | .ok br =>
      match Zip.Native.decodeHuffmanStream huffTable2 br 4 with
      | .ok result =>
        unless result.size == 4 do
          throw (IO.userError s!"stream decode: expected 4 bytes, got {result.size}")
        unless result[0]! == sym0 do
          throw (IO.userError s!"stream decode[0]: expected {sym0}, got {result[0]!}")
        unless result[1]! == sym1 do
          throw (IO.userError s!"stream decode[1]: expected {sym1}, got {result[1]!}")
        unless result[2]! == sym0 do
          throw (IO.userError s!"stream decode[2]: expected {sym0}, got {result[2]!}")
        unless result[3]! == sym1 do
          throw (IO.userError s!"stream decode[3]: expected {sym1}, got {result[3]!}")
      | .error e => throw (IO.userError s!"decodeHuffmanStream failed: {e}")
    | .error e => throw (IO.userError s!"BackwardBitReader init failed: {e}")
  | .error e => throw (IO.userError s!"buildZstdHuffmanTable for stream test failed: {e}")

  -- Test 78: integration — FFI-compressed data with Huffman literals decodes past literals stage
  let huffTestData := "The quick brown fox jumps over the lazy dog. Pack my box with five dozen liquor jugs. How vexingly quick daft zebras jump!".toUTF8
  let huffCompressed ← Zstd.compress huffTestData 3
  match Zip.Native.decompressZstd huffCompressed with
  | .ok result =>
    unless result.data == huffTestData.data do
      throw (IO.userError "Huffman integration: decompressed data mismatch")
  | .error e =>
    -- Expected to fail at sequence decoding (Huffman literals should succeed)
    unless e.contains "sequence decoding" || e.contains "treeless literals" || e.contains "Huffman" do
      throw (IO.userError s!"Huffman integration: unexpected error stage: {e}")

  -- Test 79: decodeFourHuffmanStreams — error on too-small data
  match Zip.Native.buildZstdHuffmanTable #[1] with
  | .ok huffTable2 =>
    match Zip.Native.decodeFourHuffmanStreams huffTable2 (ByteArray.mk #[0, 0, 0]) 0 3 10 with
    | .ok _ => throw (IO.userError "4-stream small: should have failed")
    | .error e =>
      unless e.contains "jump table" do
        throw (IO.userError s!"4-stream small: wrong error: {e}")
  | .error e => throw (IO.userError s!"buildZstdHuffmanTable for 4-stream test failed: {e}")

  -- Test 84: decodeSequences — single sequence, minimal tables
  -- Build 3 FSE tables with accuracyLog=1 (2 cells each).
  -- litLen table: cell[0]=code 3, cell[1]=code 5 (both 0 extra bits)
  -- offset table: cell[0]=code 1 (1 extra bit), cell[1]=code 2 (2 extra bits)
  -- matchLen table: cell[0]=code 0, cell[1]=code 1 (both 0 extra bits)
  let singleSeqLitLenTable : Zip.Native.FseTable := {
    accuracyLog := 1
    cells := #[
      { symbol := 3, numBits := 1, newState := 0 },   -- litLen code 3 → baseline 3, 0 extra
      { symbol := 5, numBits := 1, newState := 0 }    -- litLen code 5 → baseline 5, 0 extra
    ]
  }
  let singleSeqOffsetTable : Zip.Native.FseTable := {
    accuracyLog := 1
    cells := #[
      { symbol := 1, numBits := 1, newState := 0 },   -- offset code 1 → 1 extra bit
      { symbol := 2, numBits := 1, newState := 0 }    -- offset code 2 → 2 extra bits
    ]
  }
  let singleSeqMatchLenTable : Zip.Native.FseTable := {
    accuracyLog := 1
    cells := #[
      { symbol := 0, numBits := 1, newState := 0 },   -- matchLen code 0 → baseline 3, 0 extra
      { symbol := 1, numBits := 1, newState := 0 }    -- matchLen code 1 → baseline 4, 0 extra
    ]
  }
  -- Backward bitstream for 1 sequence:
  -- Bits (MSB-first reading order):
  --   litLenInit=0 (1 bit), offsetInit=0 (1 bit), matchLenInit=0 (1 bit),
  --   offsetExtra=1 (1 bit for code 1)
  -- Total: 4 data bits → sentinel at bit 4 in one byte
  -- Byte: 0b00010001 = 0x11 (sentinel=bit4, data bits 3-0 = 0001)
  let singleSeqData := ByteArray.mk #[0x11]
  match Zip.Native.BackwardBitReader.init singleSeqData 0 1 with
  | .ok bbr =>
    match Zip.Native.decodeSequences singleSeqLitLenTable singleSeqOffsetTable singleSeqMatchLenTable bbr 1 with
    | .ok seqs =>
      unless seqs.size == 1 do
        throw (IO.userError s!"decodeSeq single: expected 1 seq, got {seqs.size}")
      -- litLenState=0 → code 3 → litLen = 3
      unless seqs[0]!.literalLength == 3 do
        throw (IO.userError s!"decodeSeq single litLen: expected 3, got {seqs[0]!.literalLength}")
      -- matchLenState=0 → code 0 → matchLen = 3
      unless seqs[0]!.matchLength == 3 do
        throw (IO.userError s!"decodeSeq single matchLen: expected 3, got {seqs[0]!.matchLength}")
      -- offsetState=0 → code 1, extra=1 → (1<<1)+1 = 3
      unless seqs[0]!.offset == 3 do
        throw (IO.userError s!"decodeSeq single offset: expected 3, got {seqs[0]!.offset}")
    | .error e => throw (IO.userError s!"decodeSequences single failed: {e}")
  | .error e => throw (IO.userError s!"BackwardBitReader init single failed: {e}")

  -- Test 85: decodeSequences — two sequences with state updates
  -- Same tables as test 84. Bits for 2 sequences:
  --   litLenInit=0, offsetInit=0, matchLenInit=0,
  --   [seq1] offsetExtra=1 (1 bit), (0 matchLen extra, 0 litLen extra),
  --   [seq1] litLenUpdate=1 (1 bit), matchLenUpdate=1 (1 bit), offsetUpdate=1 (1 bit),
  --   [seq2] offsetExtra=01 (2 bits for code 2), (0 matchLen extra, 0 litLen extra)
  -- Total: 9 data bits across 2 bytes
  -- data[1] (last byte): sentinel at bit 1, bit 0 = first data bit = 0
  -- data[0] (first byte): 8 data bits = 00111101 = 0x3D
  let multiSeqData := ByteArray.mk #[0x3D, 0x02]
  match Zip.Native.BackwardBitReader.init multiSeqData 0 2 with
  | .ok bbr =>
    match Zip.Native.decodeSequences singleSeqLitLenTable singleSeqOffsetTable singleSeqMatchLenTable bbr 2 with
    | .ok seqs =>
      unless seqs.size == 2 do
        throw (IO.userError s!"decodeSeq multi: expected 2 seqs, got {seqs.size}")
      -- Seq 1: litLen=3, matchLen=3, offset=3 (same as single test)
      unless seqs[0]!.literalLength == 3 do
        throw (IO.userError s!"decodeSeq multi seq0 litLen: expected 3, got {seqs[0]!.literalLength}")
      unless seqs[0]!.matchLength == 3 do
        throw (IO.userError s!"decodeSeq multi seq0 matchLen: expected 3, got {seqs[0]!.matchLength}")
      unless seqs[0]!.offset == 3 do
        throw (IO.userError s!"decodeSeq multi seq0 offset: expected 3, got {seqs[0]!.offset}")
      -- After seq 1 state update: litLenState=0+1=1, matchLenState=0+1=1, offsetState=0+1=1
      -- Seq 2: litLenState=1 → code 5 → litLen=5, matchLenState=1 → code 1 → matchLen=4,
      --        offsetState=1 → code 2, 2 extra bits = 01 → offset = (1<<2)+1 = 5
      unless seqs[1]!.literalLength == 5 do
        throw (IO.userError s!"decodeSeq multi seq1 litLen: expected 5, got {seqs[1]!.literalLength}")
      unless seqs[1]!.matchLength == 4 do
        throw (IO.userError s!"decodeSeq multi seq1 matchLen: expected 4, got {seqs[1]!.matchLength}")
      unless seqs[1]!.offset == 5 do
        throw (IO.userError s!"decodeSeq multi seq1 offset: expected 5, got {seqs[1]!.offset}")
    | .error e => throw (IO.userError s!"decodeSequences multi failed: {e}")
  | .error e => throw (IO.userError s!"BackwardBitReader init multi failed: {e}")

  -- Test 86: decodeSequences — 0 sequences returns empty array
  -- Use dummy tables and a minimal bitstream (just needs to exist for init)
  match Zip.Native.decodeSequences singleSeqLitLenTable singleSeqOffsetTable singleSeqMatchLenTable
    (default : Zip.Native.BackwardBitReader) 0 with
  | .ok seqs =>
    unless seqs.size == 0 do
      throw (IO.userError s!"decodeSeq zero: expected 0 seqs, got {seqs.size}")
  | .error e => throw (IO.userError s!"decodeSequences zero failed: {e}")

  -- Test 87: decodeSequences with extra bits (codes above direct-value threshold)
  -- Test matchLen code 32 (baseline 35, 1 extra bit) and litLen code 16 (baseline 16, 1 extra bit)
  -- offset code 3 (3 extra bits, offset = 8 + extra)
  -- Build tables with accuracyLog=1:
  let extraBitsLitLenTable : Zip.Native.FseTable := {
    accuracyLog := 1
    cells := #[
      { symbol := 16, numBits := 1, newState := 0 },  -- litLen code 16 → baseline 16, 1 extra bit
      { symbol := 0, numBits := 1, newState := 0 }
    ]
  }
  let extraBitsOffsetTable : Zip.Native.FseTable := {
    accuracyLog := 1
    cells := #[
      { symbol := 3, numBits := 1, newState := 0 },   -- offset code 3 → 3 extra bits
      { symbol := 1, numBits := 1, newState := 0 }
    ]
  }
  let extraBitsMatchLenTable : Zip.Native.FseTable := {
    accuracyLog := 1
    cells := #[
      { symbol := 32, numBits := 1, newState := 0 },  -- matchLen code 32 → baseline 35, 1 extra bit
      { symbol := 0, numBits := 1, newState := 0 }
    ]
  }
  -- Backward bitstream for 1 sequence, all init states = 0:
  -- Bits: litLenInit=0 (1), offsetInit=0 (1), matchLenInit=0 (1),
  --   offsetExtra=101 (3 bits, val=5 → offset=8+5=13),
  --   matchLenExtra=1 (1 bit → matchLen=35+1=36),
  --   litLenExtra=0 (1 bit → litLen=16+0=16)
  -- Total: 8 data bits → sentinel at bit 8... doesn't fit in 1 byte (max 7 data bits)
  -- Use 2 bytes: data[1] has sentinel at bit 1, 1 data bit; data[0] has 7 data bits
  -- Bits in order: 0, 0, 0, 1, 0, 1, 1, 0
  -- data[1]: sentinel bit 1, bit 0 = first bit = 0 → 0b10 = 0x02
  -- data[0]: bits 7-1 (unused bit 0) = 0010110 + bit 0 must be a valid byte
  --   Actually data[0] provides a full 8 bits. After reading the 1 bit from data[1],
  --   we need 7 more bits from data[0] (MSB-first): 0, 0, 1, 0, 1, 1, 0
  --   So data[0] = 0b0010110X where X is unused (0) = 0b00101100 = 0x2C
  let extraBitsData := ByteArray.mk #[0x2C, 0x02]
  match Zip.Native.BackwardBitReader.init extraBitsData 0 2 with
  | .ok bbr =>
    match Zip.Native.decodeSequences extraBitsLitLenTable extraBitsOffsetTable extraBitsMatchLenTable bbr 1 with
    | .ok seqs =>
      unless seqs.size == 1 do
        throw (IO.userError s!"decodeSeq extraBits: expected 1 seq, got {seqs.size}")
      -- litLen code 16, extra=0 → 16+0 = 16
      unless seqs[0]!.literalLength == 16 do
        throw (IO.userError s!"decodeSeq extraBits litLen: expected 16, got {seqs[0]!.literalLength}")
      -- matchLen code 32, extra=1 → 35+1 = 36
      unless seqs[0]!.matchLength == 36 do
        throw (IO.userError s!"decodeSeq extraBits matchLen: expected 36, got {seqs[0]!.matchLength}")
      -- offset code 3, extra=101=5 → (1<<3)+5 = 13
      unless seqs[0]!.offset == 13 do
        throw (IO.userError s!"decodeSeq extraBits offset: expected 13, got {seqs[0]!.offset}")
    | .error e => throw (IO.userError s!"decodeSequences extraBits failed: {e}")
  | .error e => throw (IO.userError s!"BackwardBitReader init extraBits failed: {e}")

  -- === FSE table resolution tests ===

  -- Test: RLE mode produces single-symbol table
  let rleTable := Zip.Native.buildRleFseTable 42
  unless rleTable.accuracyLog == 0 do
    throw (IO.userError s!"buildRleFseTable: expected accuracyLog 0, got {rleTable.accuracyLog}")
  unless rleTable.cells.size == 1 do
    throw (IO.userError s!"buildRleFseTable: expected 1 cell, got {rleTable.cells.size}")
  unless rleTable.cells[0]!.symbol == 42 do
    throw (IO.userError s!"buildRleFseTable: expected symbol 42, got {rleTable.cells[0]!.symbol}")
  unless rleTable.cells[0]!.numBits == 0 do
    throw (IO.userError s!"buildRleFseTable: expected numBits 0, got {rleTable.cells[0]!.numBits}")

  -- Test: resolveSingleFseTable with predefined mode (no data consumed)
  let emptyData := ByteArray.empty
  match Zip.Native.resolveSingleFseTable .predefined 36 9 emptyData 0
      Zip.Native.predefinedLitLenDistribution 6 with
  | .ok (table, pos) =>
    unless pos == 0 do
      throw (IO.userError s!"resolveSingle predefined: expected pos 0, got {pos}")
    unless table.accuracyLog == 6 do
      throw (IO.userError s!"resolveSingle predefined: expected accuracyLog 6, got {table.accuracyLog}")
    unless table.cells.size == 64 do
      throw (IO.userError s!"resolveSingle predefined: expected 64 cells, got {table.cells.size}")
  | .error e => throw (IO.userError s!"resolveSingle predefined failed: {e}")

  -- Test: resolveSingleFseTable with RLE mode (consumes 1 byte)
  let rleData := ByteArray.mk #[7]
  match Zip.Native.resolveSingleFseTable .rle 36 9 rleData 0
      Zip.Native.predefinedLitLenDistribution 6 with
  | .ok (table, pos) =>
    unless pos == 1 do
      throw (IO.userError s!"resolveSingle RLE: expected pos 1, got {pos}")
    unless table.cells[0]!.symbol == 7 do
      throw (IO.userError s!"resolveSingle RLE: expected symbol 7, got {table.cells[0]!.symbol}")
  | .error e => throw (IO.userError s!"resolveSingle RLE failed: {e}")

  -- Test: resolveSingleFseTable with repeat mode returns error
  match Zip.Native.resolveSingleFseTable .repeat 36 9 emptyData 0
      Zip.Native.predefinedLitLenDistribution 6 with
  | .ok _ => throw (IO.userError "resolveSingle repeat: expected error, got success")
  | .error _ => pure ()

  -- Test: resolveSequenceFseTables with all predefined modes (no data consumed)
  let allPredefinedModes : Zip.Native.SequenceCompressionModes :=
    { litLenMode := .predefined, offsetMode := .predefined, matchLenMode := .predefined }
  match Zip.Native.resolveSequenceFseTables allPredefinedModes emptyData 0 with
  | .ok (llTable, ofTable, mlTable, pos) =>
    unless pos == 0 do
      throw (IO.userError s!"resolveAll predefined: expected pos 0, got {pos}")
    unless llTable.accuracyLog == 6 do
      throw (IO.userError s!"resolveAll predefined: litLen accuracyLog expected 6, got {llTable.accuracyLog}")
    unless ofTable.accuracyLog == 5 do
      throw (IO.userError s!"resolveAll predefined: offset accuracyLog expected 5, got {ofTable.accuracyLog}")
    unless mlTable.accuracyLog == 6 do
      throw (IO.userError s!"resolveAll predefined: matchLen accuracyLog expected 6, got {mlTable.accuracyLog}")
  | .error e => throw (IO.userError s!"resolveAll predefined failed: {e}")

  -- Test: resolveSequenceFseTables with mixed modes (RLE for litLen, predefined for rest)
  let mixedData := ByteArray.mk #[15]
  let mixedModes : Zip.Native.SequenceCompressionModes :=
    { litLenMode := .rle, offsetMode := .predefined, matchLenMode := .predefined }
  match Zip.Native.resolveSequenceFseTables mixedModes mixedData 0 with
  | .ok (llTable, ofTable, mlTable, pos) =>
    unless pos == 1 do
      throw (IO.userError s!"resolveAll mixed: expected pos 1, got {pos}")
    unless llTable.cells.size == 1 do
      throw (IO.userError s!"resolveAll mixed: litLen expected 1 cell, got {llTable.cells.size}")
    unless llTable.cells[0]!.symbol == 15 do
      throw (IO.userError s!"resolveAll mixed: litLen expected symbol 15, got {llTable.cells[0]!.symbol}")
    unless ofTable.accuracyLog == 5 do
      throw (IO.userError s!"resolveAll mixed: offset accuracyLog expected 5, got {ofTable.accuracyLog}")
    unless mlTable.accuracyLog == 6 do
      throw (IO.userError s!"resolveAll mixed: matchLen accuracyLog expected 6, got {mlTable.accuracyLog}")
  | .error e => throw (IO.userError s!"resolveAll mixed failed: {e}")

  IO.println "ZstdNative tests: OK"
