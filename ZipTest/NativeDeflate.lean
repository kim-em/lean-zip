import ZipTest.Helpers
import Zip.Native.Deflate
import Zip.Native.DeflateDynamic
import Zip.Native.Inflate

/-! Tests for native DEFLATE: stored, fixed Huffman, dynamic Huffman, and lazy matching modes
    with cross-implementation verification against FFI inflate. -/

set_option maxRecDepth 4000 in
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

  -- Incompressible pre-scan: classification of the escape heuristic. All sample
  -- inputs are ≥ the 1 MiB size gate so the repeat/entropy tests are actually
  -- exercised (smaller inputs short-circuit on size alone). Random bytes must be
  -- detected; compressible or restricted inputs (text, base64-style alphabet,
  -- repeated blocks, all-zeros) and inputs below the gate must NOT be.
  let prngBig := mkPrngData (2 * 1024 * 1024)
  assert! Zip.Native.Deflate.incompressiblePrescan prngBig
  assert! Zip.Native.Deflate.incompressiblePrescan (mkPrngData Zip.Native.Deflate.prescanMinSize)
  assert! !Zip.Native.Deflate.incompressiblePrescan (mkPrngData (Zip.Native.Deflate.prescanMinSize - 1))
  assert! !Zip.Native.Deflate.incompressiblePrescan (mkTextData (2 * 1024 * 1024))
  assert! !Zip.Native.Deflate.incompressiblePrescan (mkConstantData (2 * 1024 * 1024))
  -- Repetition the matcher can actually use (period ≤ 32 KiB window) must NOT be
  -- flagged, even when the repeated bytes are themselves high-entropy: a fixed
  -- random block tiled to >1 MiB compresses to a few percent but its within-region
  -- 4-grams all recur.
  let block8k := mkPrngData 8192
  let repeated8k : ByteArray := Id.run do
    let mut r := ByteArray.empty
    for _ in [:160] do r := r ++ block8k       -- 8 KiB period, 1.25 MiB total
    return r
  assert! !Zip.Native.Deflate.incompressiblePrescan repeated8k
  let block16k := mkPrngData 16384
  let repeated16k : ByteArray := Id.run do
    let mut r := ByteArray.empty
    for _ in [:80] do r := r ++ block16k       -- 16 KiB period, 1.25 MiB total
    return r
  assert! !Zip.Native.Deflate.incompressiblePrescan repeated16k
  let base64Alpha := "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".toUTF8
  let base64ish : ByteArray := Id.run do
    let mut st : UInt32 := 99
    let mut r := ByteArray.empty
    for _ in [:2 * 1024 * 1024] do
      st := st ^^^ (st <<< 13); st := st ^^^ (st >>> 17); st := st ^^^ (st <<< 5)
      r := r.push base64Alpha[(st.toNat % 64)]!
    return r
  assert! !Zip.Native.Deflate.incompressiblePrescan base64ish  -- entropy ≈ 6 bits/byte

  -- Blind-spot regression (Codex review): a file that is only ~half random must
  -- NOT be flagged — the spread sample regions land on the compressible part.
  let randHalf := mkPrngData (768 * 1024)
  let zerosHalf := mkConstantData (768 * 1024)
  let textHalf := mkTextData (768 * 1024)
  assert! !Zip.Native.Deflate.incompressiblePrescan (zerosHalf ++ randHalf)  -- compressible head
  assert! !Zip.Native.Deflate.incompressiblePrescan (randHalf ++ zerosHalf)  -- compressible tail (last region)
  assert! !Zip.Native.Deflate.incompressiblePrescan (randHalf ++ textHalf)   -- compressible tail
  -- Interleaved: alternate 4 KiB random / 4 KiB zeros — every region spans both.
  let interleaved : ByteArray := Id.run do
    let mut r := ByteArray.empty
    for k in [:160] do
      r := r ++ (mkPrngData 4096 (k.toUInt32 + 1)) ++ mkConstantData 4096
    return r
  assert! !Zip.Native.Deflate.incompressiblePrescan interleaved

  -- The pre-scan only ever routes to a stored block, so deflateRaw stays a
  -- roundtrip for incompressible input at every level — and the heuristic input
  -- must decompress back to itself via both native and FFI inflate.
  for level in [1, 3, 6, 7, 9] do
    let rawPrng := Zip.Native.Deflate.deflateRaw prngBig level.toUInt8
    match Zip.Native.Inflate.inflate rawPrng with
    | .ok result => unless result == prngBig do
        throw (IO.userError s!"deflateRaw({level})→inflate mismatch on incompressible 1MB")
    | .error e => throw (IO.userError s!"deflateRaw({level})→inflate failed on incompressible 1MB: {e}")
    let decompFFI ← RawDeflate.decompress rawPrng
    assert! decompFFI == prngBig

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

  -- Lazy chain matcher (zlib deflate_slow): levels ≥ 4 dispatch to lz77ChainLazyIter.
  -- lz77ChainLazyIter must equal the recursive lz77ChainLazy (the Array==List bridge).
  for (name, data) in [("empty", ByteArray.empty), ("single", singleByte),
                        ("hello", helloBytes), ("big", big),
                        ("constant1K", mkConstantData 1024),
                        ("cyclic1K", mkCyclicData 1024),
                        ("prng1K", mkPrngData 1024),
                        ("text4K", mkTextData 4096)] do
    let iterTokens := Zip.Native.Deflate.lz77ChainLazyIter data 64
    let recTokens := Zip.Native.Deflate.lz77ChainLazy data 64
    unless iterTokens == recTokens do
      throw (IO.userError s!"lz77ChainLazyIter vs lz77ChainLazy mismatch on {name}: \
        {iterTokens.size} vs {recTokens.size} tokens")
    -- Reduced lookahead probe depth (#2763 half-depth lazy probe): the three
    -- twins must stay in lockstep at any `lazyDepth`, not just the default.
    -- Exercise a non-default depth (32) that actually changes deferral choices.
    let iterShallow := Zip.Native.Deflate.lz77ChainLazyIter data 64 32768 1000000000 259 258 32
    let recShallow := Zip.Native.Deflate.lz77ChainLazy data 64 32768 1000000000 259 258 32
    unless iterShallow == recShallow do
      throw (IO.userError s!"lz77ChainLazyIter vs lz77ChainLazy (lazyDepth=32) mismatch on {name}: \
        {iterShallow.size} vs {recShallow.size} tokens")
    let packedShallow := Zip.Native.Deflate.lz77ChainLazyIterP data 64 32768 1000000000 259 258 32
    unless packedShallow == iterShallow.map Zip.Native.Deflate.packTok do
      throw (IO.userError s!"lz77ChainLazyIterP vs lz77ChainLazyIter (lazyDepth=32) mismatch on {name}: \
        {packedShallow.size} vs {iterShallow.size} tokens")

  -- deflateRaw at every lazy level (4–9) → native inflate AND FFI decompress, on
  -- varied shapes incl. edge cases. Exercises the lazy path end to end.
  let lazyShapes : List (String × ByteArray) :=
    [("empty", ByteArray.empty), ("single", singleByte), ("hello", helloBytes),
     ("text64K", mkTextData 65536), ("cyclic128K", mkCyclicData 131072),
     ("prng64K", mkPrngData 65536), ("const100K", mkConstantData 100000)]
  for level in [4, 5, 6, 7, 8, 9] do
    for (name, data) in lazyShapes do
      let raw := Zip.Native.Deflate.deflateRaw data level.toUInt8
      match Zip.Native.Inflate.inflate raw with
      | .ok result => unless result == data do
          throw (IO.userError s!"deflateRaw({level})→native inflate mismatch on {name}")
      | .error e => throw (IO.userError s!"deflateRaw({level})→native inflate failed on {name}: {e}")
      let ffi ← RawDeflate.decompress raw
      unless ffi == data do
        throw (IO.userError s!"deflateRaw({level})→FFI inflate mismatch on {name}")

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

  -- Cut-list shared-window splitting: deflateDynamicBlocksSharedAt clamps every
  -- cut to (pos, toks.size], so ANY selector — empty, all-zero, out-of-range,
  -- non-monotone, or exactly-at-the-end — must yield a valid partition. Verify
  -- the roundtrip via both native and FFI inflate for adversarial cut lists.
  let adversarialChoosers : List (String × (Array Zip.Native.Deflate.LZ77Token → List Nat)) :=
    [("empty", fun _ => []),
     ("zeros", fun _ => [0, 0, 0]),
     ("huge", fun _ => [1000000000]),
     ("nonmonotone", fun _ => [5, 3, 7]),
     ("atEnd", fun toks => [toks.size]),
     ("mixed", fun _ => [0, 7, 7, 100000])]
  for (name, data) in [("empty", ByteArray.empty), ("hello", helloBytes), ("big", big),
                        ("text", textRepeat), ("cyclic16K", mkCyclicData 16384)] do
    for (cname, choose) in adversarialChoosers do
      let sharedAt := Zip.Native.Deflate.deflateDynamicBlocksSharedAt data choose 9
      match Zip.Native.Inflate.inflate sharedAt with
      | .ok result => unless result == data do
          throw (IO.userError s!"deflateDynamicBlocksSharedAt→native inflate mismatch on {name} (cuts={cname})")
      | .error e => throw (IO.userError s!"deflateDynamicBlocksSharedAt→native inflate failed on {name} (cuts={cname}): {e}")
      let decomp ← RawDeflate.decompress sharedAt
      unless decomp == data do
        throw (IO.userError s!"deflateDynamicBlocksSharedAt→FFI inflate mismatch on {name} (cuts={cname})")

  -- Regression: text followed by PRNG bytes in one dynamic block used to drive
  -- the length-limiter's bl_count repair into losing leaves (chained stale
  -- `set!` reads) and under-repairing (overflow-pair counting vs actual Kraft
  -- excess), so `fixKraftList` flattened the CL tree to a uniform 7-bit code —
  -- incomplete, which zlib's inflate rejects ("invalid code lengths set") even
  -- though our native inflate tolerates it. Pin zlib (FFI) interop at the
  -- default and max levels.
  let textPrng := textRepeat ++ mkPrngData 4096
  for level in [6, 9] do
    let out := Zip.Native.Deflate.deflateRaw textPrng level.toUInt8
    let decomp ← RawDeflate.decompress out
    unless decomp == textPrng do
      throw (IO.userError s!"deflateRaw({level}) text+prng→FFI inflate mismatch")

  -- Entropy-divergence splitting (#2528): on a heterogeneous input whose symbol
  -- statistics shift (prose, then PRNG bytes, then cyclic binary — each well
  -- above the splitMinBlockBytes floor), the heuristic must propose at least one
  -- cut, and the arbitrated shared-window stream must roundtrip via both
  -- inflate implementations.
  let hetero := String.toUTF8 (String.join (List.replicate 1600
    "the quick brown fox jumps over the lazy dog. "))
    ++ mkPrngData 65536 ++ mkCyclicData 65536
  let heteroToks := Zip.Native.Deflate.lzMatch hetero 9
  let heteroCuts := Zip.Native.Deflate.chooseSplitsHeuristic heteroToks
  unless heteroCuts.length ≥ 1 do
    throw (IO.userError s!"chooseSplitsHeuristic found no cuts on heterogeneous input \
      ({heteroToks.size} tokens)")
  for (name, data) in [("hetero", hetero), ("text", textRepeat),
                        ("cyclic16K", mkCyclicData 16384), ("empty", ByteArray.empty)] do
    let arb := Zip.Native.Deflate.deflateDynamicBlocksSharedAt data
      Zip.Native.Deflate.chooseSplitsArbitrated 9
    match Zip.Native.Inflate.inflate arb with
    | .ok result => unless result == data do
        throw (IO.userError s!"arbitrated shared split→native inflate mismatch on {name}")
    | .error e => throw (IO.userError s!"arbitrated shared split→native inflate failed on {name}: {e}")
    let decomp ← RawDeflate.decompress arb
    unless decomp == data do
      throw (IO.userError s!"arbitrated shared split→FFI inflate mismatch on {name}")

  -- Observation-divergence dispatch (#2737): levels 6–8 route through the
  -- packed split candidate whenever the heuristic proposes cuts. On the
  -- heterogeneous input it must (assert, so this test really exercises the
  -- multi-block dispatch path), and the emitted stream must roundtrip via
  -- both inflate implementations across the mid-band (4–5 single-block,
  -- 6–8 split).
  unless (Zip.Native.Deflate.chooseSplitsHeuristicP
      (Zip.Native.Deflate.lzMatchP hetero 6) hetero.size).length ≥ 1 do
    throw (IO.userError "chooseSplitsHeuristicP found no cuts on heterogeneous input")
  for level in [4, 5, 6, 7, 8] do
    let out := Zip.Native.Deflate.deflateRaw hetero level.toUInt8
    match Zip.Native.Inflate.inflate out with
    | .ok result => unless result == hetero do
        throw (IO.userError s!"deflateRaw({level}) obs-split→native inflate mismatch")
    | .error e =>
        throw (IO.userError s!"deflateRaw({level}) obs-split→native inflate failed: {e}")
    let decomp ← RawDeflate.decompress out
    unless decomp == hetero do
      throw (IO.userError s!"deflateRaw({level}) obs-split→FFI inflate mismatch")

  -- Stress the many-block cross-reference path: one token per block on a highly
  -- repetitive input, so almost every block references earlier blocks' output.
  let sharedTiny := Zip.Native.Deflate.deflateDynamicBlocksShared textRepeat 1 9
  match Zip.Native.Inflate.inflate sharedTiny with
  | .ok result => unless result == textRepeat do
      throw (IO.userError "deflateDynamicBlocksShared(tokChunk=1)→inflate mismatch on text")
  | .error e => throw (IO.userError s!"deflateDynamicBlocksShared(tokChunk=1)→inflate failed: {e}")

  -- deflateRaw at the max-compression tiers (≥ 8) considers the shared-window
  -- split via pickSmaller; level 7 is the top single-block point (#2698). Verify
  -- roundtrip across the single-block/split boundary on text and large inputs.
  for level in [7, 8, 9] do
    for (name, data) in [("text", textRepeat), ("256K-cyclic", largeCyclic),
                          ("256K-prng", mkPrngData 262144)] do
      let raw := Zip.Native.Deflate.deflateRaw data level.toUInt8
      match Zip.Native.Inflate.inflate raw with
      | .ok result => unless result == data do
          throw (IO.userError s!"deflateRaw({level})→inflate mismatch on {name}")
      | .error e => throw (IO.userError s!"deflateRaw({level})→inflate failed on {name}: {e}")

  IO.println "  NativeDeflate tests passed."
