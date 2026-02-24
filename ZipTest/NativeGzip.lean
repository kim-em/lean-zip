import ZipTest.Helpers
import Zip.Native.Gzip

def ZipTest.NativeGzip.tests : IO Unit := do
  IO.println "  NativeGzip tests..."
  let big ← mkTestData
  let helloBytes := "Hello, world!".toUTF8

  -- Gzip: FFI compress → native decompress
  let gzipped ← Gzip.compress helloBytes
  match Zip.Native.GzipDecode.decompress gzipped with
  | .ok result => assert! result == helloBytes
  | .error e => throw (IO.userError s!"native gzip decompress failed on hello: {e}")

  -- Gzip: FFI compress → native decompress: larger data
  let gzippedBig ← Gzip.compress big
  match Zip.Native.GzipDecode.decompress gzippedBig with
  | .ok result => assert! result == big
  | .error e => throw (IO.userError s!"native gzip decompress failed on big data: {e}")

  -- Gzip: various compression levels
  for level in [0, 1, 6, 9] do
    let compressed ← Gzip.compress helloBytes level
    match Zip.Native.GzipDecode.decompress compressed with
    | .ok result => assert! result == helloBytes
    | .error e => throw (IO.userError s!"native gzip level {level} failed: {e}")

  -- Gzip: empty data
  let gzippedEmpty ← Gzip.compress ByteArray.empty
  match Zip.Native.GzipDecode.decompress gzippedEmpty with
  | .ok result => assert! result == ByteArray.empty
  | .error e => throw (IO.userError s!"native gzip decompress (empty) failed: {e}")

  -- Gzip: single byte
  let singleByte := ByteArray.mk #[42]
  let gzippedSingle ← Gzip.compress singleByte
  match Zip.Native.GzipDecode.decompress gzippedSingle with
  | .ok result => assert! result == singleByte
  | .error e => throw (IO.userError s!"native gzip decompress (single) failed: {e}")

  -- Gzip: large data
  let large ← mkLargeData
  let gzippedLarge ← Gzip.compress large
  match Zip.Native.GzipDecode.decompress gzippedLarge with
  | .ok result => assert! result == large
  | .error e => throw (IO.userError s!"native gzip decompress (large) failed: {e}")

  -- Gzip: concatenated streams (compress two pieces, concatenate gzip output)
  let gz1 ← Gzip.compress helloBytes
  let gz2 ← Gzip.compress singleByte
  let concatenated := gz1 ++ gz2
  match Zip.Native.GzipDecode.decompress concatenated with
  | .ok result => assert! result == (helloBytes ++ singleByte)
  | .error e => throw (IO.userError s!"native gzip decompress (concatenated) failed: {e}")

  -- Zlib: FFI compress → native decompress
  let zlibbed ← Zlib.compress helloBytes
  match Zip.Native.ZlibDecode.decompress zlibbed with
  | .ok result => assert! result == helloBytes
  | .error e => throw (IO.userError s!"native zlib decompress failed on hello: {e}")

  -- Zlib: larger data
  let zlibbedBig ← Zlib.compress big
  match Zip.Native.ZlibDecode.decompress zlibbedBig with
  | .ok result => assert! result == big
  | .error e => throw (IO.userError s!"native zlib decompress failed on big data: {e}")

  -- Zlib: various compression levels
  for level in [1, 6, 9] do
    let compressed ← Zlib.compress helloBytes level
    match Zip.Native.ZlibDecode.decompress compressed with
    | .ok result => assert! result == helloBytes
    | .error e => throw (IO.userError s!"native zlib level {level} failed: {e}")

  -- Zlib: empty data
  let zlibbedEmpty ← Zlib.compress ByteArray.empty
  match Zip.Native.ZlibDecode.decompress zlibbedEmpty with
  | .ok result => assert! result == ByteArray.empty
  | .error e => throw (IO.userError s!"native zlib decompress (empty) failed: {e}")

  -- Zlib: large data
  let zlibbedLarge ← Zlib.compress large
  match Zip.Native.ZlibDecode.decompress zlibbedLarge with
  | .ok result => assert! result == large
  | .error e => throw (IO.userError s!"native zlib decompress (large) failed: {e}")

  -- Auto-detect: gzip
  match Zip.Native.decompressAuto gzipped with
  | .ok result => assert! result == helloBytes
  | .error e => throw (IO.userError s!"decompressAuto (gzip) failed: {e}")

  -- Auto-detect: zlib
  match Zip.Native.decompressAuto zlibbed with
  | .ok result => assert! result == helloBytes
  | .error e => throw (IO.userError s!"decompressAuto (zlib) failed: {e}")

  -- Auto-detect: raw deflate
  let raw ← RawDeflate.compress helloBytes
  match Zip.Native.decompressAuto raw with
  | .ok result => assert! result == helloBytes
  | .error e => throw (IO.userError s!"decompressAuto (raw) failed: {e}")

  -- Incompressible data
  let random := mkRandomData
  let gzippedRandom ← Gzip.compress random
  match Zip.Native.GzipDecode.decompress gzippedRandom with
  | .ok result => assert! result == random
  | .error e => throw (IO.userError s!"native gzip decompress (random) failed: {e}")

  let zlibbedRandom ← Zlib.compress random
  match Zip.Native.ZlibDecode.decompress zlibbedRandom with
  | .ok result => assert! result == random
  | .error e => throw (IO.userError s!"native zlib decompress (random) failed: {e}")

  -- Native gzip compress → native decompress (level 0, stored)
  match Zip.Native.GzipDecode.decompress (Zip.Native.GzipEncode.compress helloBytes 0) with
  | .ok result => assert! result == helloBytes
  | .error e => throw (IO.userError s!"native gzip compress/decompress L0 failed: {e}")

  -- Native gzip compress → native decompress (level 1, fixed Huffman)
  match Zip.Native.GzipDecode.decompress (Zip.Native.GzipEncode.compress helloBytes 1) with
  | .ok result => assert! result == helloBytes
  | .error e => throw (IO.userError s!"native gzip compress/decompress L1 failed: {e}")

  -- Native gzip: empty input
  match Zip.Native.GzipDecode.decompress (Zip.Native.GzipEncode.compress ByteArray.empty 1) with
  | .ok result => assert! result == ByteArray.empty
  | .error e => throw (IO.userError s!"native gzip compress/decompress (empty) failed: {e}")

  -- Native gzip: large input (>65535 bytes, tests multi-block stored)
  match Zip.Native.GzipDecode.decompress (Zip.Native.GzipEncode.compress large 0) with
  | .ok result => assert! result == large
  | .error e => throw (IO.userError s!"native gzip compress/decompress (large L0) failed: {e}")

  -- Native gzip: large input with fixed Huffman
  match Zip.Native.GzipDecode.decompress (Zip.Native.GzipEncode.compress large 1) with
  | .ok result => assert! result == large
  | .error e => throw (IO.userError s!"native gzip compress/decompress (large L1) failed: {e}")

  -- Cross-implementation: native gzip compress → FFI decompress
  let nativeGz := Zip.Native.GzipEncode.compress helloBytes 1
  let ffiDecompressed ← Gzip.decompress nativeGz
  assert! ffiDecompressed == helloBytes

  -- Cross-implementation: FFI gzip compress → native decompress (already tested above)

  -- Native zlib compress → native decompress (level 0)
  match Zip.Native.ZlibDecode.decompress (Zip.Native.ZlibEncode.compress helloBytes 0) with
  | .ok result => assert! result == helloBytes
  | .error e => throw (IO.userError s!"native zlib compress/decompress L0 failed: {e}")

  -- Native zlib compress → native decompress (level 1)
  match Zip.Native.ZlibDecode.decompress (Zip.Native.ZlibEncode.compress helloBytes 1) with
  | .ok result => assert! result == helloBytes
  | .error e => throw (IO.userError s!"native zlib compress/decompress L1 failed: {e}")

  -- Native zlib: empty input
  match Zip.Native.ZlibDecode.decompress (Zip.Native.ZlibEncode.compress ByteArray.empty 1) with
  | .ok result => assert! result == ByteArray.empty
  | .error e => throw (IO.userError s!"native zlib compress/decompress (empty) failed: {e}")

  -- Cross-implementation: native zlib compress → FFI decompress
  let nativeZlib := Zip.Native.ZlibEncode.compress helloBytes 1
  let ffiZlibDecompressed ← Zlib.decompress nativeZlib
  assert! ffiZlibDecompressed == helloBytes

  -- compressAuto roundtrip: gzip
  match Zip.Native.decompressAuto (Zip.Native.compressAuto helloBytes .gzip 1) with
  | .ok result => assert! result == helloBytes
  | .error e => throw (IO.userError s!"compressAuto gzip roundtrip failed: {e}")

  -- compressAuto roundtrip: zlib
  match Zip.Native.decompressAuto (Zip.Native.compressAuto helloBytes .zlib 1) with
  | .ok result => assert! result == helloBytes
  | .error e => throw (IO.userError s!"compressAuto zlib roundtrip failed: {e}")

  -- compressAuto roundtrip: raw deflate
  match Zip.Native.decompressAuto (Zip.Native.compressAuto helloBytes .rawDeflate 1) with
  | .ok result => assert! result == helloBytes
  | .error e => throw (IO.userError s!"compressAuto raw roundtrip failed: {e}")

  -- Native gzip compress level 5 (dynamic Huffman) → native decompress
  match Zip.Native.GzipDecode.decompress (Zip.Native.GzipEncode.compress helloBytes 5) with
  | .ok result => assert! result == helloBytes
  | .error e => throw (IO.userError s!"native gzip compress/decompress L5 failed: {e}")

  -- Native gzip compress level 5 → FFI decompress (cross-implementation)
  let nativeGzL5 := Zip.Native.GzipEncode.compress helloBytes 5
  let ffiDecompL5 ← Gzip.decompress nativeGzL5
  assert! ffiDecompL5 == helloBytes

  -- Native gzip level 5: empty data
  match Zip.Native.GzipDecode.decompress (Zip.Native.GzipEncode.compress ByteArray.empty 5) with
  | .ok result => assert! result == ByteArray.empty
  | .error e => throw (IO.userError s!"native gzip L5 (empty) failed: {e}")

  -- Native gzip level 5: large data
  match Zip.Native.GzipDecode.decompress (Zip.Native.GzipEncode.compress large 5) with
  | .ok result => assert! result == large
  | .error e => throw (IO.userError s!"native gzip L5 (large) failed: {e}")

  -- Native zlib compress level 5 → native decompress
  match Zip.Native.ZlibDecode.decompress (Zip.Native.ZlibEncode.compress helloBytes 5) with
  | .ok result => assert! result == helloBytes
  | .error e => throw (IO.userError s!"native zlib compress/decompress L5 failed: {e}")

  -- Native zlib compress level 5 → FFI decompress (cross-implementation)
  let nativeZlibL5 := Zip.Native.ZlibEncode.compress helloBytes 5
  let ffiZlibDecompL5 ← Zlib.decompress nativeZlibL5
  assert! ffiZlibDecompL5 == helloBytes

  -- compressAuto level 5 roundtrip: gzip
  match Zip.Native.decompressAuto (Zip.Native.compressAuto helloBytes .gzip 5) with
  | .ok result => assert! result == helloBytes
  | .error e => throw (IO.userError s!"compressAuto gzip L5 roundtrip failed: {e}")

  -- compressAuto level 5 roundtrip: zlib
  match Zip.Native.decompressAuto (Zip.Native.compressAuto helloBytes .zlib 5) with
  | .ok result => assert! result == helloBytes
  | .error e => throw (IO.userError s!"compressAuto zlib L5 roundtrip failed: {e}")

  -- compressAuto level 5 roundtrip: raw deflate
  match Zip.Native.decompressAuto (Zip.Native.compressAuto helloBytes .rawDeflate 5) with
  | .ok result => assert! result == helloBytes
  | .error e => throw (IO.userError s!"compressAuto raw L5 roundtrip failed: {e}")

  -- Error cases
  -- Error cases: gzip
  match Zip.Native.GzipDecode.decompress ByteArray.empty with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "gzip: expected error on empty input")

  match Zip.Native.GzipDecode.decompress (ByteArray.mk #[0x1f, 0x8b]) with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "gzip: expected error on short input")

  match Zip.Native.GzipDecode.decompress (ByteArray.mk #[0x00, 0x00, 0, 0, 0, 0, 0, 0, 0, 0]) with
  | .error e => assert! e.contains "magic"
  | .ok _ => throw (IO.userError "gzip: expected error on bad magic")

  let gzippedHello ← Gzip.compress helloBytes
  let truncated := gzippedHello.extract 0 (gzippedHello.size - 4)
  match Zip.Native.GzipDecode.decompress truncated with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "gzip: expected error on truncated trailer")

  let mut corruptCrc := gzippedHello
  let crcPos := corruptCrc.size - 8
  corruptCrc := corruptCrc.set! crcPos (corruptCrc[crcPos]! ^^^ 0xFF)
  match Zip.Native.GzipDecode.decompress corruptCrc with
  | .error e => assert! e.contains "CRC32"
  | .ok _ => throw (IO.userError "gzip: expected CRC mismatch error")

  -- Error cases: zlib
  match Zip.Native.ZlibDecode.decompress ByteArray.empty with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "zlib: expected error on empty input")

  match Zip.Native.ZlibDecode.decompress (ByteArray.mk #[0x78, 0x00, 0, 0, 0, 0]) with
  | .error e => assert! e.contains "header check"
  | .ok _ => throw (IO.userError "zlib: expected error on bad header")

  match Zip.Native.ZlibDecode.decompress (ByteArray.mk #[0x09, 0x15, 0, 0, 0, 0]) with
  | .error e => assert! e.contains "compression method"
  | .ok _ => throw (IO.userError "zlib: expected error on wrong method")

  let zlibbedHello ← Zlib.compress helloBytes
  let mut corruptAdler := zlibbedHello
  let adlerPos := corruptAdler.size - 1
  corruptAdler := corruptAdler.set! adlerPos (corruptAdler[adlerPos]! ^^^ 0xFF)
  match Zip.Native.ZlibDecode.decompress corruptAdler with
  | .error e => assert! e.contains "Adler32"
  | .ok _ => throw (IO.userError "zlib: expected Adler32 mismatch error")

  -- Error cases: raw deflate
  match Zip.Native.Inflate.inflate (ByteArray.mk #[0x07]) with
  | .error e => assert! e.contains "reserved"
  | .ok _ => throw (IO.userError "inflate: expected error on reserved block type")

  match Zip.Native.Inflate.inflate (ByteArray.mk #[0x01, 0x05, 0x00]) with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "inflate: expected error on truncated stored block")

  IO.println "  NativeGzip tests passed."
