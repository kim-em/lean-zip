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

  -- adler32_combine on six (xs, ys) pairs: empty-ys, single-byte ys, moderate ys,
  -- moderate-on-both, empty-xs boundary, and a deterministic 1000-byte split-at-500.
  let combineEmpty : ByteArray := ByteArray.empty
  let combineOne : ByteArray := ByteArray.mk #[7]
  let combineTen : ByteArray := ByteArray.mk #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
  let emptyXsYs : ByteArray := ByteArray.mk #[0x42, 0x07, 0xFF, 0x00, 0x80]
  let largeData : ByteArray :=
    ByteArray.mk ((List.range 1000).map (fun i => (i * 31 + 17).toUInt8)).toArray
  let largeXs := largeData.extract 0 500
  let largeYs := largeData.extract 500 1000
  let prefix₁ := ByteArray.mk #[100, 101, 102]
  let prefix₂ := helloBytes
  let cases : List (ByteArray × ByteArray) :=
    [(prefix₁, combineEmpty), (prefix₂, combineOne),
     (combineOne, combineTen), (prefix₂, combineTen),
     (combineEmpty, emptyXsYs), (largeXs, largeYs)]
  for (xs, ys) in cases do
    let ax := Adler32.Native.adler32 1 xs
    let ay := Adler32.Native.adler32 1 ys
    let combined := Adler32.Native.adler32_combine ax ay ys.size
    let whole := Adler32.Native.adler32 1 (xs ++ ys)
    assert! combined == whole

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
