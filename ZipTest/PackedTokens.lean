import ZipTest.Helpers
import Zip.Native.DeflateDynamic

/-! Element-wise identity between the packed token stream and the boxed one
    (Wave 3b stage A): `(lzMatchP data level).map unpackTok` must equal
    `lzMatch data level` token-for-token. The theorem `lzMatchP_map`
    (`Zip/Spec/LZ77PackedCorrect.lean`) proves exactly this; the test keeps
    the *compiled* packed twins honest against the proof-level statement
    (codegen, `@[inline]` packing, accumulator reuse) on real text and the
    synthetic edge shapes at one level per matcher tier. -/

namespace ZipTest.PackedTokens

open Zip.Native.Deflate

/-- Check `(lzMatchP data level).map unpackTok == lzMatch data level`
    element-wise at levels 1 (greedy fast), 4 (lazy shallow), 6 (lazy
    default) and 9 (lazy deep). -/
private def checkView (label : String) (data : ByteArray) : IO Unit := do
  for level in [(1 : UInt8), 4, 6, 9] do
    let boxed := lzMatch data level
    let packed := lzMatchP data level
    unless packed.size == boxed.size do
      throw (IO.userError
        s!"{label} level {level}: size mismatch ({packed.size} packed vs {boxed.size} boxed)")
    for i in [0:boxed.size] do
      unless unpackTok packed[i]! == boxed[i]! do
        throw (IO.userError s!"{label} level {level}: token mismatch at index {i}")

/-- Stage B gate: the packed base candidate must be byte-identical to the
    boxed reference dispatch — `deflateRawBaseP data (lzMatchP data level)`
    (= `deflateRawBase data level` by definition) against
    `deflateRawBaseTokens data (lzMatch data level)` (the boxed reference,
    kept for exactly this conformance check). The theorem
    `deflateRawBase_def` (`Zip/Spec/LZ77PackedCorrect.lean`) proves the
    equality; this test keeps the compiled packed pipeline (`tokenFreqsP`,
    emit-boundary unpacking) honest against it. -/
private def checkBaseP (label : String) (data : ByteArray) : IO Unit := do
  for level in [(1 : UInt8), 4, 6, 9] do
    let packed := deflateRawBaseP data (lzMatchP data level)
    let boxed := deflateRawBaseTokens data (lzMatch data level)
    unless packed == boxed do
      throw (IO.userError
        s!"{label} level {level}: deflateRawBaseP ({packed.size} bytes) ≠ \
           deflateRawBaseTokens ({boxed.size} bytes)")

def tests : IO Unit := do
  IO.println "  PackedTokens tests..."
  let alice ← IO.FS.readBinFile "bench/corpora/canterbury/alice29.txt"
  checkView "alice29" alice
  checkView "text64k" (mkTextData 65536)
  checkView "cyclic64k" (mkCyclicData 65536)
  checkView "prng64k" (mkPrngData 65536)
  checkView "constant64k" (mkConstantData 65536)
  checkView "size0" ByteArray.empty
  checkView "size1" (ByteArray.mk #[42])
  checkView "size2" (ByteArray.mk #[42, 42])
  checkView "size3" (ByteArray.mk #[7, 7, 7])
  checkBaseP "alice29" alice
  checkBaseP "text64k" (mkTextData 65536)
  checkBaseP "cyclic64k" (mkCyclicData 65536)
  checkBaseP "prng64k" (mkPrngData 65536)
  checkBaseP "constant64k" (mkConstantData 65536)
  checkBaseP "size0" ByteArray.empty
  checkBaseP "size1" (ByteArray.mk #[42])
  checkBaseP "size2" (ByteArray.mk #[42, 42])
  checkBaseP "size3" (ByteArray.mk #[7, 7, 7])
  IO.println "  PackedTokens tests passed"

end ZipTest.PackedTokens
