import ZipTest.Helpers
import Zip.Native.Adler32
import Zip.Native.Crc32

/-! Conformance tests comparing native Adler32 and CRC32 implementations against FFI. -/

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

  -- Incremental native Adler32 matches whole-buffer
  let half := big.size / 2
  let firstHalf := big.extract 0 half
  let secondHalf := big.extract half big.size
  let nativeInc1 := Adler32.Native.adler32 1 firstHalf
  let nativeInc2 := Adler32.Native.adler32 nativeInc1 secondHalf
  let nativeWhole := Adler32.Native.adler32 1 big
  assert! nativeInc2 == nativeWhole

  -- Incremental native Adler32 matches incremental FFI
  let ffiInc1 := Checksum.adler32 1 firstHalf
  let ffiInc2 := Checksum.adler32 ffiInc1 secondHalf
  assert! nativeInc2 == ffiInc2

  -- Empty Adler32
  let nativeEmpty := Adler32.Native.adler32 1 ByteArray.empty
  assert! nativeEmpty == 1

  -- Single byte Adler32
  let singleByte := ByteArray.mk #[42]
  let ffiSingle := Checksum.adler32 1 singleByte
  let nativeSingle := Adler32.Native.adler32 1 singleByte
  assert! ffiSingle == nativeSingle

  -- Native CRC32 matches FFI on known data
  let ffiCrc := Checksum.crc32 0 helloBytes
  let nativeCrc := Crc32.Native.crc32 0 helloBytes
  assert! ffiCrc == nativeCrc

  -- Native CRC32 matches FFI on large data
  let ffiCrcBig := Checksum.crc32 0 big
  let nativeCrcBig := Crc32.Native.crc32 0 big
  assert! ffiCrcBig == nativeCrcBig

  -- Incremental native CRC32 matches whole-buffer
  let nativeCrcInc1 := Crc32.Native.crc32 0 firstHalf
  let nativeCrcInc2 := Crc32.Native.crc32 nativeCrcInc1 secondHalf
  let nativeCrcWhole := Crc32.Native.crc32 0 big
  assert! nativeCrcInc2 == nativeCrcWhole

  -- Incremental native CRC32 matches incremental FFI
  let ffiCrcInc1 := Checksum.crc32 0 firstHalf
  let ffiCrcInc2 := Checksum.crc32 ffiCrcInc1 secondHalf
  assert! nativeCrcInc2 == ffiCrcInc2

  -- Empty CRC32
  let nativeCrcEmpty := Crc32.Native.crc32 0 ByteArray.empty
  assert! nativeCrcEmpty == 0

  -- Single byte CRC32
  let ffiCrcSingle := Checksum.crc32 0 singleByte
  let nativeCrcSingle := Crc32.Native.crc32 0 singleByte
  assert! ffiCrcSingle == nativeCrcSingle

  IO.println "Native checksum tests: OK"
