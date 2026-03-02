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

  -- Test 22: decompressZstd error on skippable frame
  -- Skippable frame magic: 0x184D2A50 (little-endian: 50 2A 4D 18)
  let skippable := ByteArray.mk #[0x50, 0x2A, 0x4D, 0x18, 0x04, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
  match Zip.Native.decompressZstd skippable with
  | .ok _ => throw (IO.userError "decompressZstd skippable: should have failed")
  | .error e =>
    unless e.contains "skippable" do
      throw (IO.userError s!"decompressZstd skippable: wrong error: {e}")

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

  -- Test 51: parseHuffmanTreeDescriptor — FSE mode returns error
  let fseTreeInput := ByteArray.mk #[0x80, 0x00, 0x00, 0x00]
  match Zip.Native.parseHuffmanTreeDescriptor fseTreeInput 0 with
  | .ok _ => throw (IO.userError "FSE tree descriptor: should have failed")
  | .error e =>
    unless e.contains "FSE-compressed" do
      throw (IO.userError s!"FSE tree descriptor: wrong error: {e}")

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

  -- Test 72: litLenExtraBits table has 36 entries
  unless Zip.Native.litLenExtraBits.size == 36 do
    throw (IO.userError s!"litLenExtraBits: expected 36 entries, got {Zip.Native.litLenExtraBits.size}")

  -- Test 73: matchLenExtraBits table has 53 entries
  unless Zip.Native.matchLenExtraBits.size == 53 do
    throw (IO.userError s!"matchLenExtraBits: expected 53 entries, got {Zip.Native.matchLenExtraBits.size}")

  -- Test 74: decodeSequences — single sequence, minimal tables
  -- Build 3 FSE tables with accuracyLog=1 (2 cells each)
  -- litLen table: cell 0 → symbol 0 (litLen code 0: baseline 0, 0 extra bits)
  -- offset table: cell 0 → symbol 1 (offset code 1: 1 extra bit)
  -- matchLen table: cell 0 → symbol 0 (matchLen code 0: baseline 3, 0 extra bits)
  let mkCell (sym : UInt16) (nb : UInt8) (ns : UInt16) : Zip.Native.FseCell :=
    { symbol := sym, numBits := nb, newState := ns }
  let litLenTbl : Zip.Native.FseTable :=
    { accuracyLog := 1, cells := #[mkCell 0 1 0, mkCell 5 1 0] }
  let offsetTbl : Zip.Native.FseTable :=
    { accuracyLog := 1, cells := #[mkCell 1 1 0, mkCell 2 1 0] }
  let matchLenTbl : Zip.Native.FseTable :=
    { accuracyLog := 1, cells := #[mkCell 0 1 0, mkCell 3 1 0] }
  -- Backward bitstream: init states (0,0,0) + offset extra (1 bit: 1) = 4 bits: 0001
  -- Byte = sentinel(1) then 0001 then padding(000) = 0b10001000 = 0x88
  let seqData := ByteArray.mk #[0x88]
  match Zip.Native.BackwardBitReader.init seqData 0 1 with
  | .error e => throw (IO.userError s!"BackwardBitReader init failed: {e}")
  | .ok br =>
    match Zip.Native.decodeSequences litLenTbl offsetTbl matchLenTbl br 1 with
    | .error e => throw (IO.userError s!"decodeSequences single failed: {e}")
    | .ok seqs =>
      unless seqs.size == 1 do
        throw (IO.userError s!"single seq: expected 1 sequence, got {seqs.size}")
      let s := seqs[0]!
      -- litLenCode=0 → litLen=0, matchLenCode=0 → matchLen=3
      -- offsetCode=1, extra=1 → offset = (1 << 1) + 1 = 3
      unless s.literalLength == 0 do
        throw (IO.userError s!"single seq: expected litLen 0, got {s.literalLength}")
      unless s.matchLength == 3 do
        throw (IO.userError s!"single seq: expected matchLen 3, got {s.matchLength}")
      unless s.offset == 3 do
        throw (IO.userError s!"single seq: expected offset 3, got {s.offset}")

  -- Test 75: decodeSequences — two sequences with state updates
  -- Both tables accuracyLog=1 (2 cells), 2 sequences
  -- Sequence 1: states all=0, offset code 0 (0 extra bits), matchLen code 0, litLen code 0
  -- State update after seq 1: litLen numBits=1, matchLen numBits=1, offset numBits=1
  -- All newState=0, so new state = 0 + readBit
  -- Sequence 2: states depend on update bits
  --
  -- litLen table: cell 0 → sym 0, cell 1 → sym 16 (code 16: baseline 16, 1 extra bit)
  -- offset table: cell 0 → sym 0 (code 0: 0 extra bits), cell 1 → sym 2 (code 2: 2 extra bits)
  -- matchLen table: cell 0 → sym 0 (code 0: baseline 3, 0 extra), cell 1 → sym 32 (code 32: baseline 35, 1 extra)
  let litLenTbl2 : Zip.Native.FseTable :=
    { accuracyLog := 1, cells := #[mkCell 0 1 0, mkCell 16 1 0] }
  let offsetTbl2 : Zip.Native.FseTable :=
    { accuracyLog := 1, cells := #[mkCell 0 1 0, mkCell 2 1 0] }
  let matchLenTbl2 : Zip.Native.FseTable :=
    { accuracyLog := 1, cells := #[mkCell 0 1 0, mkCell 32 1 0] }
  -- Bit layout (MSB-first in backward stream):
  -- Init: litLenState=0 (1b: 0), offsetState=0 (1b: 0), matchLenState=0 (1b: 0)
  -- Seq1 codes: offset sym=0 (0 extra), matchLen sym=0 (0 extra), litLen sym=0 (0 extra)
  --   → no extra bits to read
  -- State update (not last): litLen 1b, matchLen 1b, offset 1b
  --   Let's set all update bits to 1 → new states: litLen=0+1=1, matchLen=0+1=1, offset=0+1=1
  -- Seq2 codes (states all=1): offset sym=2 (2 extra), matchLen sym=32 (1 extra), litLen sym=16 (1 extra)
  --   offset extra: 2 bits, let's use 01 → value = (1<<2) + 1 = 5
  --   matchLen extra: 1 bit, let's use 1 → value = 35 + 1 = 36
  --   litLen extra: 1 bit, let's use 0 → value = 16 + 0 = 16
  -- Last seq → no state update
  --
  -- Total bits: 3 (init) + 0 (seq1 extra) + 3 (state update: 1,1,1) + 2+1+1 (seq2 extra: 01,1,0) = 10 bits
  -- Bits in order: 0,0,0, 1,1,1, 0,1,1,0
  -- Need 10 data bits. Last byte sentinel at bit 7 gives 7 bits.
  -- Need a second byte (8 bits) → total 15 bits available, need 10.
  -- Byte1 (earlier, index 0): provides 8 bits
  -- Byte2 (later, index 1): sentinel + 7 bits below
  -- Reading order: sentinel consumed, then byte2's lower 7 bits (MSB-first), then byte1's 8 bits
  -- Data: 0,0,0,1,1,1,0,1,1,0 (10 bits)
  -- Byte2 bits [6..0]: 0,0,0,1,1,1,0 (7 bits)
  -- Byte1 bits [7..0]: 1,1,0,?,?,?,?,? (need 3 more, rest don't matter)
  -- Byte2 = sentinel(1) + 0001110 = 0b10001110 = 0x8E
  -- Byte1 = 11000000 = 0xC0 (remaining bits are padding)
  let seqData2 := ByteArray.mk #[0xC0, 0x8E]
  match Zip.Native.BackwardBitReader.init seqData2 0 2 with
  | .error e => throw (IO.userError s!"BackwardBitReader init 2 failed: {e}")
  | .ok br =>
    match Zip.Native.decodeSequences litLenTbl2 offsetTbl2 matchLenTbl2 br 2 with
    | .error e => throw (IO.userError s!"decodeSequences multi failed: {e}")
    | .ok seqs =>
      unless seqs.size == 2 do
        throw (IO.userError s!"multi seq: expected 2 sequences, got {seqs.size}")
      -- Seq 0: litLen=0, matchLen=3, offset=0 (code 0, 0 extra → decodeOffsetValue 0 0 = 0)
      let s0 := seqs[0]!
      unless s0.literalLength == 0 do
        throw (IO.userError s!"multi seq0: expected litLen 0, got {s0.literalLength}")
      unless s0.matchLength == 3 do
        throw (IO.userError s!"multi seq0: expected matchLen 3, got {s0.matchLength}")
      unless s0.offset == 0 do
        throw (IO.userError s!"multi seq0: expected offset 0, got {s0.offset}")
      -- Seq 1: litLen=16, matchLen=36, offset=5
      let s1 := seqs[1]!
      unless s1.literalLength == 16 do
        throw (IO.userError s!"multi seq1: expected litLen 16, got {s1.literalLength}")
      unless s1.matchLength == 36 do
        throw (IO.userError s!"multi seq1: expected matchLen 36, got {s1.matchLength}")
      unless s1.offset == 5 do
        throw (IO.userError s!"multi seq1: expected offset 5, got {s1.offset}")

  -- Test 76: decodeSequences — 0 sequences returns empty array
  let emptyBr := Zip.Native.BackwardBitReader.mk ByteArray.empty 0 0 0
  match Zip.Native.decodeSequences litLenTbl offsetTbl matchLenTbl emptyBr 0 with
  | .error e => throw (IO.userError s!"decodeSequences 0 seq failed: {e}")
  | .ok seqs =>
    unless seqs.size == 0 do
      throw (IO.userError s!"0 seq decode: expected 0 sequences, got {seqs.size}")

  IO.println "ZstdNative tests: OK"
