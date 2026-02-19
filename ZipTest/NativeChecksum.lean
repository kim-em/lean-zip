import ZipTest.Helpers
import Zip.Native.Adler32

def ZipTest.NativeChecksum.tests : IO Unit := do
  let big ← mkTestData
  let helloBytes := "Hello, world!".toUTF8

  -- Native Adler32 matches FFI on known data
  let ffiAdler := Checksum.adler32 1 helloBytes
  let nativeAdler := Adler32.Native.adler32 1 helloBytes
  assert! ffiAdler == nativeAdler

  -- Native Adler32 matches FFI on large data
  let ffiAdlerBig := Checksum.adler32 1 big
  let nativeAdlerBig := Adler32.Native.adler32 1 big
  assert! ffiAdlerBig == nativeAdlerBig

  -- Incremental native matches whole-buffer native
  let half := big.size / 2
  let firstHalf := big.extract 0 half
  let secondHalf := big.extract half big.size
  let nativeInc1 := Adler32.Native.adler32 1 firstHalf
  let nativeInc2 := Adler32.Native.adler32 nativeInc1 secondHalf
  let nativeWhole := Adler32.Native.adler32 1 big
  assert! nativeInc2 == nativeWhole

  -- Incremental native matches incremental FFI
  let ffiInc1 := Checksum.adler32 1 firstHalf
  let ffiInc2 := Checksum.adler32 ffiInc1 secondHalf
  assert! nativeInc2 == ffiInc2

  -- Empty input
  let nativeEmpty := Adler32.Native.adler32 1 ByteArray.empty
  assert! nativeEmpty == 1

  -- Single byte
  let singleByte := ByteArray.mk #[42]
  let ffiSingle := Checksum.adler32 1 singleByte
  let nativeSingle := Adler32.Native.adler32 1 singleByte
  assert! ffiSingle == nativeSingle

  IO.println "Native checksum tests: OK"
