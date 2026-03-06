import ZipTest.Helpers
import Zip.Native.ZstdFrame
import Zip.Native.XxHash

/-! Tests for Zstd native component-level parsing: literals section, sequences header,
    executeSequences, Huffman weights/table building, extra bits tables, compression modes,
    and skippable/multi-frame handling (tests 28–81). -/

def ZipTest.ZstdNativeComponents.tests : IO Unit := do
  -- Test 28: parseLiteralsSection on manually crafted Raw header (1-byte header, 5-bit size)
  -- Raw type = 0, size_format = 0 (bit 2 = 0), regenSize = 5 (bits 3-7)
  -- byte0 = (5 << 3) | 0 = 0x28, followed by 5 raw bytes
  let rawLitInput := ByteArray.mk #[0x28, 0x48, 0x65, 0x6C, 0x6C, 0x6F]
  match Zip.Native.parseLiteralsSection rawLitInput 0 with
  | .ok (result, endPos, _) =>
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
  | .ok (result, endPos, _) =>
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
  | .ok (result, endPos, _) =>
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

  -- Test 32: parseLiteralsSection rejects treeless literals without previous Huffman tree
  -- Treeless type = 3
  let treelessLitInput := ByteArray.mk #[0x03, 0x00, 0x00, 0x00, 0x00]
  match Zip.Native.parseLiteralsSection treelessLitInput 0 with
  | .ok _ => throw (IO.userError "treeless lit: should have failed")
  | .error e =>
    unless e.contains "no previous Huffman tree" do
      throw (IO.userError s!"treeless lit: wrong error: {e}")

  -- Test 33: parseSequencesHeader with 0 sequences
  let zeroSeqInput := ByteArray.mk #[0x00]
  match Zip.Native.parseSequencesHeader zeroSeqInput 0 with
  | .ok (numSeq, _modes, endPos) =>
    unless numSeq == 0 do
      throw (IO.userError s!"0 seq: expected 0, got {numSeq}")
    unless endPos == 1 do
      throw (IO.userError s!"0 seq: expected endPos 1, got {endPos}")
  | .error e => throw (IO.userError s!"parseSequencesHeader 0 failed: {e}")

  -- Test 34: parseSequencesHeader with small count (1-byte format)
  -- byte0 = 42, followed by compression modes byte
  let smallSeqInput := ByteArray.mk #[42, 0x00]
  match Zip.Native.parseSequencesHeader smallSeqInput 0 with
  | .ok (numSeq, _modes, endPos) =>
    unless numSeq == 42 do
      throw (IO.userError s!"42 seq: expected 42, got {numSeq}")
    unless endPos == 2 do
      throw (IO.userError s!"42 seq: expected endPos 2, got {endPos}")
  | .error e => throw (IO.userError s!"parseSequencesHeader 42 failed: {e}")

  -- Test 35: parseSequencesHeader with 2-byte format
  -- byte0 = 200 (>= 128, < 255): numSeq = (200 - 128) << 8 + byte1 = 72 * 256 + 50 = 18482
  let medSeqInput := ByteArray.mk #[200, 50, 0x00]
  match Zip.Native.parseSequencesHeader medSeqInput 0 with
  | .ok (numSeq, _modes, endPos) =>
    unless numSeq == 18482 do
      throw (IO.userError s!"2byte seq: expected 18482, got {numSeq}")
    unless endPos == 3 do
      throw (IO.userError s!"2byte seq: expected endPos 3, got {endPos}")
  | .error e => throw (IO.userError s!"parseSequencesHeader 2byte failed: {e}")

  -- Test 36: parseSequencesHeader with 3-byte format
  -- byte0 = 255: numSeq = byte1 + (byte2 << 8) + 0x7F00 = 10 + (1 << 8) + 32512 = 32778
  let largeSeqInput := ByteArray.mk #[255, 10, 1, 0x00]
  match Zip.Native.parseSequencesHeader largeSeqInput 0 with
  | .ok (numSeq, _modes, endPos) =>
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
  | .ok (result, _) =>
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
  | .ok (result, _) =>
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
  | .ok (result, _) =>
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
  | .ok (result, _) =>
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
  | .ok (result, _) =>
    -- First seq: ABCDE + copy 5 from offset 5 → ABCDEABCDE
    -- Second seq: 0 literals + copy 5 from offset 1 (shifted: history[1]=1) → EEEEE
    let expected := ByteArray.mk #[0x41, 0x42, 0x43, 0x44, 0x45,
                                    0x41, 0x42, 0x43, 0x44, 0x45,
                                    0x45, 0x45, 0x45, 0x45, 0x45]
    unless result.data == expected.data do
      throw (IO.userError s!"shifted repeat: expected {expected.data}, got {result.data}")
  | .error e => throw (IO.userError s!"shifted repeat failed: {e}")

  -- Test 44b: executeSequences — offset history threading across blocks
  -- Block 1: establish offset 4 (raw code 7 = 4+3). Block 2 uses repeat code 1
  -- with the offset history returned from block 1.
  let block1Lit := ByteArray.mk #[0x41, 0x42, 0x43, 0x44]
  let block1Seqs : Array Zip.Native.ZstdSequence := #[
    { literalLength := 4, matchLength := 4, offset := 7 }  -- actual offset 4
  ]
  match Zip.Native.executeSequences block1Seqs block1Lit with
  | .ok (block1Out, history1) =>
    -- block1Out should be "ABCDABCD"
    let expected1 := ByteArray.mk #[0x41, 0x42, 0x43, 0x44, 0x41, 0x42, 0x43, 0x44]
    unless block1Out.data == expected1.data do
      throw (IO.userError s!"cross-block history block1: expected {expected1.data}, got {block1Out.data}")
    -- history1 should be [4, 1, 4] (offset 4 pushed, old [1, 4] shifted right)
    unless history1[0]! == 4 do
      throw (IO.userError s!"cross-block history[0]: expected 4, got {history1[0]!}")
    -- Block 2: use history from block 1, repeat code 1 → reuses offset 4
    let block2Lit := ByteArray.mk #[0x45, 0x46, 0x47, 0x48]
    let block2Seqs : Array Zip.Native.ZstdSequence := #[
      { literalLength := 4, matchLength := 4, offset := 1 }  -- repeat code 1 → history1[0] = 4
    ]
    match Zip.Native.executeSequences block2Seqs block2Lit (offsetHistory := history1) with
    | .ok (block2Out, _) =>
      -- block2Out: "EFGH" + copy 4 from offset 4 → "EFGHEFGH"
      let expected2 := ByteArray.mk #[0x45, 0x46, 0x47, 0x48, 0x45, 0x46, 0x47, 0x48]
      unless block2Out.data == expected2.data do
        throw (IO.userError s!"cross-block history block2: expected {expected2.data}, got {block2Out.data}")
    | .error e => throw (IO.userError s!"cross-block history block2 failed: {e}")
  | .error e => throw (IO.userError s!"cross-block history block1 failed: {e}")

  -- Test 44c: executeSequences — cross-block back-reference via windowPrefix
  -- Block 1 produces "ABCD". Block 2 references block 1's data via windowPrefix.
  let prefixData := ByteArray.mk #[0x41, 0x42, 0x43, 0x44]  -- "ABCD" from block 1
  let block2cLit := ByteArray.mk #[0x45, 0x46]  -- "EF"
  let block2cSeqs : Array Zip.Native.ZstdSequence := #[
    { literalLength := 2, matchLength := 4, offset := 9 }  -- actual offset 6 (9-3), reaches into prefix
  ]
  match Zip.Native.executeSequences block2cSeqs block2cLit (windowPrefix := prefixData) with
  | .ok (block2cOut, _) =>
    -- Working buffer starts as "ABCD" (prefix), then "EF" appended → "ABCDEF"
    -- Match: offset 6 from position 6 → starts at 0 → copies "ABCD"
    -- Result (stripped of prefix): "EFABCD"
    let expected2c := ByteArray.mk #[0x45, 0x46, 0x41, 0x42, 0x43, 0x44]
    unless block2cOut.data == expected2c.data do
      throw (IO.userError s!"cross-block prefix: expected {expected2c.data}, got {block2cOut.data}")
  | .error e => throw (IO.userError s!"cross-block prefix failed: {e}")

  -- Test 44d: executeSequences — prefix stripping (returned output excludes prefix)
  -- Even with a non-empty prefix and no sequences, only new literals are returned.
  let prefixOnly := ByteArray.mk #[0x01, 0x02, 0x03]
  let newLiterals := ByteArray.mk #[0x04, 0x05]
  match Zip.Native.executeSequences #[] newLiterals (windowPrefix := prefixOnly) with
  | .ok (result, _) =>
    unless result.data == newLiterals.data do
      throw (IO.userError s!"prefix strip: expected {newLiterals.data}, got {result.data}")
  | .error e => throw (IO.userError s!"prefix strip failed: {e}")

  -- Test 45: parseHuffmanWeightsDirect — known byte sequence
  -- Byte 0x35 packs weights [3, 5], byte 0xA1 packs [10, 1]
  -- numWeights=4 means 4 weight symbols from ceil(4/2)=2 bytes
  let weightInput := ByteArray.mk #[0x35, 0xA1]
  match Zip.Native.parseHuffmanWeightsDirect weightInput 0 4 with
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
  -- Header byte = 0x81 (129, >= 128 → direct), numWeights = 129 - 127 = 2
  -- ceil(2/2) = 1 weight byte: 0x11 → weights [1, 1]
  -- 2 explicit symbols + 1 implicit = 3 symbols
  let treeDescInput := ByteArray.mk #[0x81, 0x11]
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
  -- Header byte 0x01 (< 128 → FSE), compressedSize=1, too small for a valid FSE distribution
  let fseTreeInput := ByteArray.mk #[0x01, 0x00, 0x00, 0x00]
  match Zip.Native.parseHuffmanTreeDescriptor fseTreeInput 0 with
  | .ok _ => throw (IO.userError "FSE tree descriptor invalid: should have failed")
  | .error _ => pure ()

  -- Test 52: parseHuffmanTreeDescriptor — truncated input
  match Zip.Native.parseHuffmanTreeDescriptor ByteArray.empty 0 with
  | .ok _ => throw (IO.userError "truncated tree descriptor: should have failed")
  | .error _ => pure ()

  -- Test 53: parseHuffmanWeightsDirect — truncated data
  -- 3 weights need ceil(3/2) = 2 bytes, but only 1 byte provided
  match Zip.Native.parseHuffmanWeightsDirect (ByteArray.mk #[0x35]) 0 3 with
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

  -- Test 69: parseSequencesHeader — modes parsing
  -- Construct: byte0 = 42 (small count), modes byte = 0b10_01_00_00 = 0x90
  -- litLen=FSE_Compressed(2), offset=RLE(1), matchLen=Predefined(0), reserved=0
  let modesInput := ByteArray.mk #[42, 0x90]
  match Zip.Native.parseSequencesHeader modesInput 0 with
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

  -- Test 70: parseSequencesHeader — 0 sequences returns default modes
  let zeroModesInput := ByteArray.mk #[0x00]
  match Zip.Native.parseSequencesHeader zeroModesInput 0 with
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

  -- Test 71: parseSequencesHeader — all repeat mode (0xFF modes byte)
  -- byte0 = 1 (1 sequence), modes = 0xFF → litLen=repeat(3), offset=repeat(3), matchLen=repeat(3)
  let repeatModesInput := ByteArray.mk #[1, 0xFF]
  match Zip.Native.parseSequencesHeader repeatModesInput 0 with
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

  IO.println "ZstdNativeComponents tests: OK"
