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

/-- Stage C gate: the packed single-block cores must be byte-identical to
    the boxed ones over the same token stream — `deflateFixedBlockP` against
    `deflateFixedBlock` and `deflateDynamicBlockCoreP` against
    `deflateDynamicBlockCore`, fed this level's `lzMatchP` stream and its
    boxed view. The theorems `deflateFixedBlockP_eq` /
    `deflateDynamicBlockCoreP_eq` (`Zip/Spec/EmitPackedCorrect.lean`) prove
    the equalities; this test keeps the compiled packed emitters
    (`emitTokensP`/`emitTokensWithCodesP` and their opaque reference-arm
    helpers) honest against them. -/
private def checkCoresP (label : String) (data : ByteArray) : IO Unit := do
  for level in [(1 : UInt8), 4, 6, 9] do
    let ptoks := lzMatchP data level
    let toks := ptoks.map unpackTok
    let fixedP := deflateFixedBlockP data ptoks
    let fixedB := deflateFixedBlock data toks
    unless fixedP == fixedB do
      throw (IO.userError
        s!"{label} level {level}: deflateFixedBlockP ({fixedP.size} bytes) ≠ \
           deflateFixedBlock ({fixedB.size} bytes)")
    let f := tokenFreqs toks
    let lens := dynamicCodeLengths f.1 f.2
    let dynP := deflateDynamicBlockCoreP data ptoks lens.1 lens.2
      (dynamicCodeLengths_length f.1 f.2).1 (dynamicCodeLengths_length f.1 f.2).2
    let dynB := deflateDynamicBlockCore data toks lens.1 lens.2
      (dynamicCodeLengths_length f.1 f.2).1 (dynamicCodeLengths_length f.1 f.2).2
    unless dynP == dynB do
      throw (IO.userError
        s!"{label} level {level}: deflateDynamicBlockCoreP ({dynP.size} bytes) ≠ \
           deflateDynamicBlockCore ({dynB.size} bytes)")

/-- #2737 gate: the packed observation-divergence split pipeline must match
    the boxed reference — `chooseSplitsHeuristicP` against
    `chooseSplitsHeuristic` over the `unpackTok` view (cut-list equality), and
    `deflateDynamicBlocksSharedAtP` against
    `deflateDynamicBlocksSharedAtTokens … (fun _ => cuts)` (byte identity; the
    theorem is `deflateDynamicBlocksSharedAtP_eq`,
    `Zip/Spec/LZ77PackedCorrect.lean`) — at the heuristic's own cuts and at
    adversarial cut lists (empty, non-monotone/out-of-range, all-ones), which
    both emitters must clamp identically. -/
private def checkSplitP (label : String) (data : ByteArray) : IO Unit := do
  for level in [(4 : UInt8), 6, 8] do
    let ptoks := lzMatchP data level
    let toks := ptoks.map unpackTok
    let cutsP := chooseSplitsHeuristicP ptoks data.size
    let cutsB := chooseSplitsHeuristic toks
    unless cutsP == cutsB do
      throw (IO.userError
        s!"{label} level {level}: chooseSplitsHeuristicP {cutsP} ≠ boxed {cutsB}")
    for cuts in [cutsP, ([] : List Nat), [0, 5, 3, 1000000000], [1]] do
      let splitP := deflateDynamicBlocksSharedAtP data ptoks cuts
      let splitB := deflateDynamicBlocksSharedAtTokens data toks (fun _ => cuts)
      unless splitP == splitB do
        throw (IO.userError
          s!"{label} level {level}: deflateDynamicBlocksSharedAtP ({splitP.size} bytes) ≠ \
             boxed reference ({splitB.size} bytes) at cuts {cuts}")

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
  checkCoresP "alice29" alice
  checkCoresP "text64k" (mkTextData 65536)
  checkCoresP "cyclic64k" (mkCyclicData 65536)
  checkCoresP "prng64k" (mkPrngData 65536)
  checkCoresP "constant64k" (mkConstantData 65536)
  checkCoresP "size0" ByteArray.empty
  checkCoresP "size1" (ByteArray.mk #[42])
  checkCoresP "size2" (ByteArray.mk #[42, 42])
  checkCoresP "size3" (ByteArray.mk #[7, 7, 7])
  -- #2737: packed split pipeline against the boxed reference. The
  -- heterogeneous input's statistics shift well above the block-byte floor,
  -- so the packed heuristic must propose at least one cut there (the
  -- conformance check then covers a real multi-block partition, not just
  -- the clamping edge cases).
  let hetero := mkTextData 65536 ++ mkPrngData 65536 ++ mkCyclicData 65536
  unless (chooseSplitsHeuristicP (lzMatchP hetero 6) hetero.size).length ≥ 1 do
    throw (IO.userError "chooseSplitsHeuristicP found no cuts on heterogeneous input")
  checkSplitP "hetero192k" hetero
  checkSplitP "alice29" alice
  checkSplitP "text64k" (mkTextData 65536)
  checkSplitP "prng64k" (mkPrngData 65536)
  checkSplitP "size0" ByteArray.empty
  checkSplitP "size1" (ByteArray.mk #[42])
  IO.println "  PackedTokens tests passed"

end ZipTest.PackedTokens
