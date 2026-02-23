import ZipTest.Helpers
import Zip.Native.Deflate
import Zip.Native.Inflate

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

  IO.println "  NativeDeflate tests passed."
