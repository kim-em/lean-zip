import ZipTest.Helpers
import Zip.Native.Inflate

/-! Tests for native inflate (raw DEFLATE decompression) against FFI-compressed data
    across compression levels and block types. -/

def ZipTest.NativeInflate.tests : IO Unit := do
  IO.println "  NativeInflate tests..."
  let big ← mkTestData
  let helloBytes := "Hello, world!".toUTF8

  -- FFI compress (raw deflate) → native inflate: small data
  let compressed ← RawDeflate.compress helloBytes
  match Zip.Native.Inflate.inflate compressed with
  | .ok result => assert! result == helloBytes
  | .error e => throw (IO.userError s!"native inflate failed on hello: {e}")

  -- FFI compress → native inflate: larger repetitive data
  let compressedBig ← RawDeflate.compress big
  match Zip.Native.Inflate.inflate compressedBig with
  | .ok result => assert! result == big
  | .error e => throw (IO.userError s!"native inflate failed on big data: {e}")

  -- FFI compress level 1 → native inflate
  let compressed1 ← RawDeflate.compress helloBytes 1
  match Zip.Native.Inflate.inflate compressed1 with
  | .ok result => assert! result == helloBytes
  | .error e => throw (IO.userError s!"native inflate (level 1) failed: {e}")

  -- FFI compress level 9 → native inflate
  let compressed9 ← RawDeflate.compress big 9
  match Zip.Native.Inflate.inflate compressed9 with
  | .ok result => assert! result == big
  | .error e => throw (IO.userError s!"native inflate (level 9) failed: {e}")

  -- Empty data
  let compressedEmpty ← RawDeflate.compress ByteArray.empty
  match Zip.Native.Inflate.inflate compressedEmpty with
  | .ok result => assert! result == ByteArray.empty
  | .error e => throw (IO.userError s!"native inflate (empty) failed: {e}")

  -- Single byte
  let singleByte := ByteArray.mk #[42]
  let compressedSingle ← RawDeflate.compress singleByte
  match Zip.Native.Inflate.inflate compressedSingle with
  | .ok result => assert! result == singleByte
  | .error e => throw (IO.userError s!"native inflate (single byte) failed: {e}")

  -- Stored block (level 0 = no compression)
  let stored ← RawDeflate.compress helloBytes 0
  match Zip.Native.Inflate.inflate stored with
  | .ok result => assert! result == helloBytes
  | .error e => throw (IO.userError s!"native inflate (stored) failed: {e}")

  -- Large data with stored blocks (level 0)
  let storedBig ← RawDeflate.compress big 0
  match Zip.Native.Inflate.inflate storedBig with
  | .ok result => assert! result == big
  | .error e => throw (IO.userError s!"native inflate (stored big) failed: {e}")

  -- Large data to exercise dynamic Huffman and long back-references
  let large ← mkLargeData
  let compressedLarge ← RawDeflate.compress large
  match Zip.Native.Inflate.inflate compressedLarge with
  | .ok result => assert! result == large
  | .error e => throw (IO.userError s!"native inflate (large) failed: {e}")

  -- Incompressible data (random-ish bytes)
  let random := mkRandomData
  let compressedRandom ← RawDeflate.compress random
  match Zip.Native.Inflate.inflate compressedRandom with
  | .ok result => assert! result == random
  | .error e => throw (IO.userError s!"native inflate (random) failed: {e}")

  IO.println "  NativeInflate tests passed."
