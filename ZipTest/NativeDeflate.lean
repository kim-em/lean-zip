import ZipTest.Helpers
import Zip.Native.Deflate
import Zip.Native.DeflateDynamic
import Zip.Native.Inflate

/-! Tests for native DEFLATE: stored, fixed Huffman, dynamic Huffman, and lazy matching modes
    with cross-implementation verification against FFI inflate. -/

def ZipTest.NativeDeflate.tests : IO Unit := do
  IO.println "  NativeDeflate tests..."
  let big ← mkTestData
  let helloBytes := "Hello, world!".toUTF8

  -- Native deflateStored → native inflate: small data
  let compressed := Zip.Native.Deflate.deflateStored helloBytes
  match Zip.Native.Inflate.inflate compressed with
  | .ok result => assert! result == helloBytes
  | .error e => throw (IO.userError s!"deflateStored→inflate failed on hello: {e}")

  -- Native deflateStored → native inflate: empty data
  let compressedEmpty := Zip.Native.Deflate.deflateStored ByteArray.empty
  match Zip.Native.Inflate.inflate compressedEmpty with
  | .ok result => assert! result == ByteArray.empty
  | .error e => throw (IO.userError s!"deflateStored→inflate failed on empty: {e}")

  -- Native deflateStored → native inflate: single byte
  let singleByte := ByteArray.mk #[42]
  let compressedSingle := Zip.Native.Deflate.deflateStored singleByte
  match Zip.Native.Inflate.inflate compressedSingle with
  | .ok result => assert! result == singleByte
  | .error e => throw (IO.userError s!"deflateStored→inflate failed on single byte: {e}")

  -- Native deflateStored → native inflate: larger repetitive data
  let compressedBig := Zip.Native.Deflate.deflateStored big
  match Zip.Native.Inflate.inflate compressedBig with
  | .ok result => assert! result == big
  | .error e => throw (IO.userError s!"deflateStored→inflate failed on big: {e}")

  -- Native deflateStored → native inflate: data > 65535 bytes (multi-block)
  let large := mkConstantData 100000
  let compressedLarge := Zip.Native.Deflate.deflateStored large
  match Zip.Native.Inflate.inflate compressedLarge with
  | .ok result => assert! result == large
  | .error e => throw (IO.userError s!"deflateStored→inflate failed on large: {e}")

  -- Native deflateStored → native inflate: random data > 65535 bytes
  let largeRandom := mkPrngData 131072
  let compressedRandom := Zip.Native.Deflate.deflateStored largeRandom
  match Zip.Native.Inflate.inflate compressedRandom with
  | .ok result => assert! result == largeRandom
  | .error e => throw (IO.userError s!"deflateStored→inflate failed on large random: {e}")

  -- Native deflateStored → FFI inflate (cross-implementation)
  let compressedCross := Zip.Native.Deflate.deflateStored helloBytes
  let decompressedCross ← RawDeflate.decompress compressedCross
  assert! decompressedCross == helloBytes

  -- FFI compress level 0 → native inflate (stored blocks from zlib)
  let ffiStored ← RawDeflate.compress helloBytes 0
  match Zip.Native.Inflate.inflate ffiStored with
  | .ok result => assert! result == helloBytes
  | .error e => throw (IO.userError s!"FFI level 0→native inflate failed: {e}")

  -- Level 1 (fixed Huffman) tests

  -- deflateFixed → native inflate: small data
  let fixedHello := Zip.Native.Deflate.deflateFixed helloBytes
  match Zip.Native.Inflate.inflate fixedHello with
  | .ok result => assert! result == helloBytes
  | .error e => throw (IO.userError s!"deflateFixed→inflate failed on hello: {e}")

  -- deflateFixed → native inflate: empty data
  let fixedEmpty := Zip.Native.Deflate.deflateFixed ByteArray.empty
  match Zip.Native.Inflate.inflate fixedEmpty with
  | .ok result => assert! result == ByteArray.empty
  | .error e => throw (IO.userError s!"deflateFixed→inflate failed on empty: {e}")

  -- deflateFixed → native inflate: single byte
  let fixedSingle := Zip.Native.Deflate.deflateFixed singleByte
  match Zip.Native.Inflate.inflate fixedSingle with
  | .ok result => assert! result == singleByte
  | .error e => throw (IO.userError s!"deflateFixed→inflate failed on single byte: {e}")

  -- deflateFixed → native inflate: repetitive data
  let fixedBig := Zip.Native.Deflate.deflateFixed big
  match Zip.Native.Inflate.inflate fixedBig with
  | .ok result => assert! result == big
  | .error e => throw (IO.userError s!"deflateFixed→inflate failed on big: {e}")

  -- deflateFixed → FFI inflate (cross-implementation)
  let fixedCross := Zip.Native.Deflate.deflateFixed helloBytes
  let decompFixedCross ← RawDeflate.decompress fixedCross
  assert! decompFixedCross == helloBytes

  -- deflateFixed → FFI inflate: larger data (cross-implementation)
  let fixedCrossBig := Zip.Native.Deflate.deflateFixed big
  let decompFixedCrossBig ← RawDeflate.decompress fixedCrossBig
  assert! decompFixedCrossBig == big

  -- deflateFixed achieves compression on repetitive data
  let storedSize := (Zip.Native.Deflate.deflateStored big).size
  let fixedSize := fixedBig.size
  assert! fixedSize < storedSize

  -- deflateFixed → native inflate: all-same-byte data
  let allSame := mkConstantData 1000
  let fixedSame := Zip.Native.Deflate.deflateFixed allSame
  match Zip.Native.Inflate.inflate fixedSame with
  | .ok result => assert! result == allSame
  | .error e => throw (IO.userError s!"deflateFixed→inflate failed on all-same: {e}")

  -- deflateFixed → native inflate: pseudo-random data
  let random := mkPrngData 1000
  let fixedRandom := Zip.Native.Deflate.deflateFixed random
  match Zip.Native.Inflate.inflate fixedRandom with
  | .ok result => assert! result == random
  | .error e => throw (IO.userError s!"deflateFixed→inflate failed on random: {e}")

  -- Level 2 (lazy LZ77) tests

  -- deflateLazy → native inflate: small data
  let lazyHello := Zip.Native.Deflate.deflateLazy helloBytes
  match Zip.Native.Inflate.inflate lazyHello with
  | .ok result => assert! result == helloBytes
  | .error e => throw (IO.userError s!"deflateLazy→inflate failed on hello: {e}")

  -- deflateLazy → native inflate: empty data
  let lazyEmpty := Zip.Native.Deflate.deflateLazy ByteArray.empty
  match Zip.Native.Inflate.inflate lazyEmpty with
  | .ok result => assert! result == ByteArray.empty
  | .error e => throw (IO.userError s!"deflateLazy→inflate failed on empty: {e}")

  -- deflateLazy → native inflate: single byte
  let lazySingle := Zip.Native.Deflate.deflateLazy singleByte
  match Zip.Native.Inflate.inflate lazySingle with
  | .ok result => assert! result == singleByte
  | .error e => throw (IO.userError s!"deflateLazy→inflate failed on single byte: {e}")

  -- deflateLazy → native inflate: repetitive data
  let lazyBig := Zip.Native.Deflate.deflateLazy big
  match Zip.Native.Inflate.inflate lazyBig with
  | .ok result => assert! result == big
  | .error e => throw (IO.userError s!"deflateLazy→inflate failed on big: {e}")

  -- deflateLazy → FFI inflate (cross-implementation)
  let lazyCross := Zip.Native.Deflate.deflateLazy helloBytes
  let decompLazyCross ← RawDeflate.decompress lazyCross
  assert! decompLazyCross == helloBytes

  -- deflateLazy → FFI inflate: larger data (cross-implementation)
  let lazyCrossBig := Zip.Native.Deflate.deflateLazy big
  let decompLazyCrossBig ← RawDeflate.decompress lazyCrossBig
  assert! decompLazyCrossBig == big

  -- deflateLazy achieves equal or better compression than deflateFixed on repetitive data
  let lazySize := lazyBig.size
  let fixedSize := fixedBig.size
  assert! lazySize ≤ fixedSize

  -- deflateLazy → native inflate: all-same-byte data
  let lazySame := Zip.Native.Deflate.deflateLazy allSame
  match Zip.Native.Inflate.inflate lazySame with
  | .ok result => assert! result == allSame
  | .error e => throw (IO.userError s!"deflateLazy→inflate failed on all-same: {e}")

  -- deflateLazy → native inflate: pseudo-random data
  let lazyRandom := Zip.Native.Deflate.deflateLazy random
  match Zip.Native.Inflate.inflate lazyRandom with
  | .ok result => assert! result == random
  | .error e => throw (IO.userError s!"deflateLazy→inflate failed on random: {e}")

  -- Level 5 (dynamic Huffman) tests

  -- deflateDynamic → native inflate: small data
  let dynHello := Zip.Native.Deflate.deflateDynamic helloBytes
  match Zip.Native.Inflate.inflate dynHello with
  | .ok result => assert! result == helloBytes
  | .error e => throw (IO.userError s!"deflateDynamic→inflate failed on hello: {e}")

  -- deflateDynamic → native inflate: empty data
  let dynEmpty := Zip.Native.Deflate.deflateDynamic ByteArray.empty
  match Zip.Native.Inflate.inflate dynEmpty with
  | .ok result => assert! result == ByteArray.empty
  | .error e => throw (IO.userError s!"deflateDynamic→inflate failed on empty: {e}")

  -- deflateDynamic → native inflate: single byte
  let dynSingle := Zip.Native.Deflate.deflateDynamic singleByte
  match Zip.Native.Inflate.inflate dynSingle with
  | .ok result => assert! result == singleByte
  | .error e => throw (IO.userError s!"deflateDynamic→inflate failed on single byte: {e}")

  -- deflateDynamic → native inflate: repetitive data
  let dynBig := Zip.Native.Deflate.deflateDynamic big
  match Zip.Native.Inflate.inflate dynBig with
  | .ok result => assert! result == big
  | .error e => throw (IO.userError s!"deflateDynamic→inflate failed on big: {e}")

  -- deflateDynamic → native inflate: all-same-byte data
  let dynSame := Zip.Native.Deflate.deflateDynamic allSame
  match Zip.Native.Inflate.inflate dynSame with
  | .ok result => assert! result == allSame
  | .error e => throw (IO.userError s!"deflateDynamic→inflate failed on all-same: {e}")

  -- deflateDynamic → native inflate: pseudo-random data
  let dynRandom := Zip.Native.Deflate.deflateDynamic random
  match Zip.Native.Inflate.inflate dynRandom with
  | .ok result => assert! result == random
  | .error e => throw (IO.userError s!"deflateDynamic→inflate failed on random: {e}")

  -- deflateDynamic → FFI inflate (cross-implementation)
  let dynCross := Zip.Native.Deflate.deflateDynamic helloBytes
  let decompDynCross ← RawDeflate.decompress dynCross
  assert! decompDynCross == helloBytes

  -- deflateDynamic → FFI inflate: larger data (cross-implementation)
  let dynCrossBig := Zip.Native.Deflate.deflateDynamic big
  let decompDynCrossBig ← RawDeflate.decompress dynCrossBig
  assert! decompDynCrossBig == big

  -- deflateDynamic achieves equal or better compression than deflateLazy on repetitive data
  let dynSize := dynBig.size
  let lazySize := lazyBig.size
  assert! dynSize ≤ lazySize

  -- Unified deflateRaw dispatch tests

  -- deflateRaw level 0 (stored) → native inflate
  let rawStored := Zip.Native.Deflate.deflateRaw helloBytes 0
  match Zip.Native.Inflate.inflate rawStored with
  | .ok result => assert! result == helloBytes
  | .error e => throw (IO.userError s!"deflateRaw(0)→inflate failed on hello: {e}")

  -- deflateRaw level 1 (fixed) → native inflate
  let rawFixed := Zip.Native.Deflate.deflateRaw helloBytes 1
  match Zip.Native.Inflate.inflate rawFixed with
  | .ok result => assert! result == helloBytes
  | .error e => throw (IO.userError s!"deflateRaw(1)→inflate failed on hello: {e}")

  -- deflateRaw level 3 (lazy) → native inflate
  let rawLazy := Zip.Native.Deflate.deflateRaw big 3
  match Zip.Native.Inflate.inflate rawLazy with
  | .ok result => assert! result == big
  | .error e => throw (IO.userError s!"deflateRaw(3)→inflate failed on big: {e}")

  -- deflateRaw level 6 (dynamic) → native inflate
  let rawDyn := Zip.Native.Deflate.deflateRaw big 6
  match Zip.Native.Inflate.inflate rawDyn with
  | .ok result => assert! result == big
  | .error e => throw (IO.userError s!"deflateRaw(6)→inflate failed on big: {e}")

  -- deflateRaw level 6 → FFI inflate (cross-implementation)
  let rawDynCross := Zip.Native.Deflate.deflateRaw helloBytes 6
  let decompRawCross ← RawDeflate.decompress rawDynCross
  assert! decompRawCross == helloBytes

  -- deflateRaw level 6 → FFI inflate: larger data
  let rawDynCrossBig := Zip.Native.Deflate.deflateRaw big 6
  let decompRawCrossBig ← RawDeflate.decompress rawDynCrossBig
  assert! decompRawCrossBig == big

  -- deflateRaw on empty data (all levels)
  for level in [0, 1, 3, 6] do
    let rawEmpty := Zip.Native.Deflate.deflateRaw ByteArray.empty level.toUInt8
    match Zip.Native.Inflate.inflate rawEmpty with
    | .ok result => assert! result == ByteArray.empty
    | .error e => throw (IO.userError s!"deflateRaw({level})→inflate failed on empty: {e}")

  -- deflateRaw on single byte (all levels)
  for level in [0, 1, 3, 6] do
    let rawSingle := Zip.Native.Deflate.deflateRaw singleByte level.toUInt8
    match Zip.Native.Inflate.inflate rawSingle with
    | .ok result => assert! result == singleByte
    | .error e => throw (IO.userError s!"deflateRaw({level})→inflate failed on single byte: {e}")

  -- Iterative LZ77 conformance tests

  -- lz77GreedyIter matches lz77Greedy on small inputs
  for (name, data) in [("empty", ByteArray.empty), ("single", singleByte),
                        ("hello", helloBytes), ("big", big),
                        ("constant1K", mkConstantData 1024),
                        ("cyclic1K", mkCyclicData 1024),
                        ("prng1K", mkPrngData 1024)] do
    let iterTokens := Zip.Native.Deflate.lz77GreedyIter data
    let recTokens := Zip.Native.Deflate.lz77Greedy data
    unless iterTokens == recTokens do
      throw (IO.userError s!"lz77GreedyIter vs lz77Greedy mismatch on {name}: {iterTokens.size} vs {recTokens.size} tokens")

  -- lz77GreedyIter on large inputs (would stack-overflow with lz77Greedy)
  for (name, size) in [("64KB", 65536), ("256KB", 262144)] do
    let data := mkCyclicData size
    let tokens := Zip.Native.Deflate.lz77GreedyIter data
    unless tokens.size > 0 do
      throw (IO.userError s!"lz77GreedyIter produced no tokens on {name}")

  -- deflateFixedIter roundtrip on large inputs via native inflate
  for (name, data) in [("64KB-const", mkConstantData 65536),
                        ("256KB-cyclic", mkCyclicData 262144),
                        ("256KB-prng", mkPrngData 262144)] do
    let compressed := Zip.Native.Deflate.deflateFixedIter data
    match Zip.Native.Inflate.inflate compressed with
    | .ok result => unless result == data do
        throw (IO.userError s!"deflateFixedIter→inflate mismatch on {name}")
    | .error e => throw (IO.userError s!"deflateFixedIter→inflate failed on {name}: {e}")

  -- deflateFixedIter → FFI inflate roundtrip on 256KB
  let largeCyclic := mkCyclicData 262144
  let compressedLarge := Zip.Native.Deflate.deflateFixedIter largeCyclic
  let decompLarge ← RawDeflate.decompress compressedLarge
  assert! decompLarge == largeCyclic

  -- deflateRaw level 1 now uses iterative path — roundtrip 256KB
  let rawLargeFixed := Zip.Native.Deflate.deflateRaw largeCyclic 1
  match Zip.Native.Inflate.inflate rawLargeFixed with
  | .ok result => assert! result == largeCyclic
  | .error e => throw (IO.userError s!"deflateRaw(1) 256KB roundtrip failed: {e}")

  -- Cross-block (shared-window) block splitting: deflateDynamicBlocksShared runs
  -- one whole-file match pass (full window) and partitions the token stream into
  -- per-block groups whose back-references cross block boundaries. Verify the
  -- roundtrip via both native and FFI inflate, across token-group sizes (small
  -- tokChunk forces many blocks and genuine cross-block references).
  let textRepeat := String.toUTF8 (String.join (List.replicate 300
    "the quick brown fox jumps over the lazy dog. "))
  for (name, data) in [("empty", ByteArray.empty), ("single", singleByte),
                        ("hello", helloBytes), ("big", big),
                        ("text", textRepeat), ("cyclic16K", mkCyclicData 16384)] do
    for tokChunk in [4, 256, 8192] do
      let shared := Zip.Native.Deflate.deflateDynamicBlocksShared data tokChunk 9
      match Zip.Native.Inflate.inflate shared with
      | .ok result => unless result == data do
          throw (IO.userError s!"deflateDynamicBlocksShared→native inflate mismatch on {name} (tokChunk={tokChunk})")
      | .error e => throw (IO.userError s!"deflateDynamicBlocksShared→native inflate failed on {name} (tokChunk={tokChunk}): {e}")
      let decomp ← RawDeflate.decompress shared
      unless decomp == data do
        throw (IO.userError s!"deflateDynamicBlocksShared→FFI inflate mismatch on {name} (tokChunk={tokChunk})")

  -- Stress the many-block cross-reference path: one token per block on a highly
  -- repetitive input, so almost every block references earlier blocks' output.
  let sharedTiny := Zip.Native.Deflate.deflateDynamicBlocksShared textRepeat 1 9
  match Zip.Native.Inflate.inflate sharedTiny with
  | .ok result => unless result == textRepeat do
      throw (IO.userError "deflateDynamicBlocksShared(tokChunk=1)→inflate mismatch on text")
  | .error e => throw (IO.userError s!"deflateDynamicBlocksShared(tokChunk=1)→inflate failed: {e}")

  -- deflateRaw at the max-compression tiers (≥ 7) now considers the shared-window
  -- split via pickSmaller; verify roundtrip on text and large inputs.
  for level in [7, 8, 9] do
    for (name, data) in [("text", textRepeat), ("256K-cyclic", largeCyclic),
                          ("256K-prng", mkPrngData 262144)] do
      let raw := Zip.Native.Deflate.deflateRaw data level.toUInt8
      match Zip.Native.Inflate.inflate raw with
      | .ok result => unless result == data do
          throw (IO.userError s!"deflateRaw({level})→inflate mismatch on {name}")
      | .error e => throw (IO.userError s!"deflateRaw({level})→inflate failed on {name}: {e}")

  IO.println "  NativeDeflate tests passed."
