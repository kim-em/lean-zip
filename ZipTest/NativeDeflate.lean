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

  IO.println "  NativeDeflate tests passed."
