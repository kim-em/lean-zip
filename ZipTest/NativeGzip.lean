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
  let mut random := ByteArray.empty
  for i in [:1000] do
    random := random.push ((i * 73 + 137) % 256).toUInt8
  let gzippedRandom ← Gzip.compress random
  match Zip.Native.GzipDecode.decompress gzippedRandom with
  | .ok result => assert! result == random
  | .error e => throw (IO.userError s!"native gzip decompress (random) failed: {e}")

  let zlibbedRandom ← Zlib.compress random
  match Zip.Native.ZlibDecode.decompress zlibbedRandom with
  | .ok result => assert! result == random
  | .error e => throw (IO.userError s!"native zlib decompress (random) failed: {e}")

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
