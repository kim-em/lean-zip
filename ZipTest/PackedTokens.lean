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
    element-wise at levels 1 (greedy fast), 4 (greedy high-speed), 5 (lazy
    shallow), 6 (lazy default), and 9 (lazy deep). -/
private def checkView (label : String) (data : ByteArray) : IO Unit := do
  for level in [(1 : UInt8), 4, 5, 6, 9] do
    let boxed := lzMatch data level
    let packed := lzMatchP data level
    unless packed.size == boxed.size do
      throw (IO.userError
        s!"{label} level {level}: size mismatch ({packed.size} packed vs {boxed.size} boxed)")
    for i in [0:boxed.size] do
      unless unpackTok packed.toArray[i]! == boxed[i]! do
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
  for level in [(1 : UInt8), 4, 5, 6, 9] do
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
  for level in [(1 : UInt8), 4, 5, 6, 9] do
    let ptoks := lzMatchP data level
    let toks := ptoks.toArray.map unpackTok
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

/-- Compiled-path gate for the specialized level-one matcher.  Compare the
    production native-word/wide-histogram entry first with its boxed specialized
    twin, then with the pre-specialization generic fused entry.  The final
    `deflateRawBase*` comparison also exercises the actual production shell and
    its established packed reference; no proof equality is used to discharge
    any of these runtime checks. -/
private def checkL1WideFused (label : String) (data : ByteArray) : IO Unit := do
  let (wideTokens, wideLit, wideDist) := lz77ChainIterPMergedF1U64 data
  let (boxedTokens, boxedLit, boxedDist) := lz77ChainIterPMergedF1U data
  let (genericTokens, genericLit, genericDist) :=
    lz77ChainIterPMergedF data 4 32768 2 258
  unless wideTokens.toArray == boxedTokens.toArray do
    throw (IO.userError
      s!"{label}: lz77ChainIterPMergedF1U64 token stream \
         ({wideTokens.size} tokens) ≠ boxed F1U ({boxedTokens.size} tokens)")
  unless wideLit == boxedLit.val do
    throw (IO.userError s!"{label}: wide L1 lit/length histogram ≠ boxed F1U")
  unless wideDist == boxedDist.val do
    throw (IO.userError s!"{label}: wide L1 distance histogram ≠ boxed F1U")
  unless wideTokens.toArray == genericTokens.toArray do
    throw (IO.userError
      s!"{label}: specialized L1 token stream ≠ generic fused L1 \
         ({wideTokens.size} vs {genericTokens.size} tokens)")
  unless wideLit == genericLit.val do
    throw (IO.userError s!"{label}: specialized L1 lit/length histogram ≠ generic fused L1")
  unless wideDist == genericDist.val do
    throw (IO.userError s!"{label}: specialized L1 distance histogram ≠ generic fused L1")
  let counted := tokenFreqsPTA wideTokens
  unless wideLit == counted.1 && wideDist == counted.2 do
    throw (IO.userError s!"{label}: wide L1 histograms ≠ compiled tokenFreqsPTA recount")
  let production := deflateRawBaseFU64Level1 data
  let boxedOut := deflateRawBaseFLevel1Impl data 1
  let established := deflateRawBase data 1
  unless production == boxedOut do
    throw (IO.userError
      s!"{label}: deflateRawBaseFU64Level1 ({production.size} bytes) ≠ \
         boxed L1 implementation ({boxedOut.size} bytes)")
  unless production == established do
    throw (IO.userError
      s!"{label}: deflateRawBaseFU64Level1 ({production.size} bytes) ≠ \
         established deflateRawBase L1 ({established.size} bytes)")

/-- Direct compiled conformance for the narrowly routed flat token emitter and
    its single-block core.  Canonical tables built from a real L1 token stream
    satisfy the production route's bounds.  Starting the two emitters at every
    pending-bit offset 0–7 covers byte-boundary flushes that a whole-block-only
    comparison can miss; comparing `flush` observes the complete bit sequence
    while intentionally ignoring when each implementation drains full bytes. -/
private def checkFlatDynamicP (label : String) (data : ByteArray) : IO Unit := do
  let ptoks := lzMatchP data 1
  let f := tokenFreqsPTA ptoks
  let lens := dynamicCodeLengths f.1 f.2
  let plan := dynHeaderCodes lens.1 lens.2
  have hcl : plan.clCodes.size ≥ 19 :=
    Nat.le_of_eq (dynHeaderCodes_clCodes_size lens.1 lens.2).symm
  have hlit : lens.1.length = 286 := (dynamicCodeLengths_length f.1 f.2).1
  have hdist : lens.2.length = 30 := (dynamicCodeLengths_length f.1 f.2).2
  have hlitBound : ∀ x ∈ lens.1, x ≤ 15 := (dynamicCodeLengths_bounded f.1 f.2).1
  have hdistBound : ∀ x ∈ lens.2, x ≤ 15 := (dynamicCodeLengths_bounded f.1 f.2).2
  let cap := dynBlockBytesWith f.1 f.2 lens.1 lens.2 plan hcl
  let flatCore := deflateDynamicBlockCorePWithFlat data ptoks lens.1 lens.2 plan hcl
    hlit hdist hlitBound hdistBound cap
  let referenceCore := deflateDynamicBlockCorePWith data ptoks lens.1 lens.2 plan hcl
    hlit hdist cap
  unless flatCore == referenceCore do
    throw (IO.userError
      s!"{label}: flat dynamic core ({flatCore.size} bytes) ≠ \
         scalar packed core ({referenceCore.size} bytes)")

  let litCodes := canonicalCodes (lens.1.toArray.map Nat.toUInt8)
  let distCodes := canonicalCodes (lens.2.toArray.map Nat.toUInt8)
  let litT := packCodeTab litCodes
  let distT := packCodeTab distCodes
  have hlitCodes : litCodes.size ≥ 286 := by
    show (canonicalCodes (lens.1.toArray.map Nat.toUInt8)).size ≥ 286
    rw [canonicalCodes_size, Array.size_map, List.size_toArray, hlit]
    omega
  have hdistCodes : distCodes.size ≥ 30 := by
    show (canonicalCodes (lens.2.toArray.map Nat.toUInt8)).size ≥ 30
    rw [canonicalCodes_size, Array.size_map, List.size_toArray, hdist]
    omega
  have hlitT : litT.size ≥ 286 := by
    simpa only [litT, packCodeTab_size] using hlitCodes
  have hdistT : distT.size ≥ 30 := by
    simpa only [distT, packCodeTab_size] using hdistCodes
  let seeds : List (Nat × UInt32) :=
    [(0, 0), (1, 1), (2, 2), (3, 5), (4, 10), (5, 21), (6, 42), (7, 85)]
  for (seedBits, seedVal) in seeds do
    let bw := (Zip.Native.BitWriter.emptyWithCapacity (cap + 1)).writeBits seedBits seedVal
    let flat := emitTokensWithCodesTAPTFlatZero bw ptoks litT distT hlitT hdistT
    let reference := emitTokensWithCodesTAPT bw ptoks litT distT hlitT hdistT 0
    unless flat.flush == reference.flush do
      throw (IO.userError
        s!"{label}: flat token emitter ≠ scalar emitter from bit offset {seedBits}")

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
  for level in [(5 : UInt8), 6, 8] do
    let ptoks := lzMatchP data level
    let toks := ptoks.toArray.map unpackTok
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

/-- A 4 MiB fixture that defeats the incompressible pre-scan, then repeats one
    random 32 KiB window. It exercises mixed packed-counter traffic,
    exact-window matches, and nonempty split arbitration while keeping CI
    bounded. -/
private def largeL5ExerciseData : ByteArray :=
  let seed := mkPrngData chainWinSize 0xC0FFEE
  ByteArray.mk (Array.ofFn (n := l5LargeInputMinSize) (fun i =>
    if i.val < prescanRegionBytes then 0x42
    else seed[(i.val - prescanRegionBytes) % seed.size]!))

/-- Emit the established level-5 base/split arbitration from an explicit token
    stream and cut list, independently of the production matcher dispatch. -/
private def emitL5Reference (data : ByteArray) (ptokens : TokenArray)
    (cuts : List Nat) : ByteArray :=
  let withObs : Nat × (Unit → ByteArray) :=
    if cuts.isEmpty then
      deflateRawBasePPrep data ptokens
    else
      let obsFreqs := deflateObsSplitSizedFreqsP data ptokens cuts
      let basePrep := deflateRawBasePPrepF data ptokens obsFreqs.2
      if basePrep.1 < obsFreqs.1.1 then basePrep else obsFreqs.1
  withObs.2 ()

/-- Compiled-path coverage for the ≥4 MiB L5 specialization. Compare its
    native-word matcher, packed-counter splitter, and production output against
    their established separately-array/scalar compiled references. -/
private def checkLargeL5CompiledPath : IO Unit := do
  let data := largeL5ExerciseData
  let belowThreshold := data.extract 0 (l5LargeInputMinSize - 1)
  if useL5LargeInputPolicy belowThreshold 5 then
    throw (IO.userError "large-L5 policy engaged below its size threshold")
  unless lazyChainDepthFor belowThreshold 5 == chainDepth 5 &&
      lazyDepthFor belowThreshold 5 == lazyDepth 5 &&
      splitCheckTokensFor belowThreshold 5 == splitCheckTokens do
    throw (IO.userError "below-threshold L5 policy did not retain its fallback parameters")
  unless useL5LargeInputPolicy data 5 do
    throw (IO.userError "large-L5 policy did not engage")
  if incompressiblePrescan data then
    throw (IO.userError "large-L5 fixture hit the stored pre-scan")

  let specialized := lzMatchP data 5
  let reference := lz77ChainLazyIterP data 22 32768
    (insertCap 5) (goodMatch 5) (niceLen 5) 5 false 1
  unless specialized.toArray == reference.toArray do
    throw (IO.userError "large-L5 specialized/reference token mismatch")

  let cadence := splitCheckTokensFor data 5
  let packedCuts :=
    chooseSplitsHeuristicPUPacked specialized data.size cadence
  let scalarCuts :=
    chooseSplitsHeuristicPU specialized data.size cadence
  let referenceCuts :=
    chooseSplitsHeuristicP reference data.size
      splitMinBlockBytes splitSoftMaxBlockBytes cadence
  unless packedCuts == scalarCuts && packedCuts == referenceCuts do
    throw (IO.userError "large-L5 split-walker mismatch")
  if packedCuts.isEmpty then
    throw (IO.userError "large-L5 fixture did not exercise split arbitration")

  let production := deflateRaw data 5
  let established := emitL5Reference data reference referenceCuts
  unless production == established do
    throw (IO.userError "large-L5 production/reference output mismatch")

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
  -- The production L1 implementation has two nested refinements that broad
  -- roundtrip coverage does not isolate: native-word outer matcher state and
  -- wide byte-backed frequency counters.  Exercise the <3 fallback, the
  -- three-byte hash tail, the four-byte wide-hash boundary, long max-length
  -- matches, literal-heavy input, a 32 KiB window-edge repeat, and real text.
  let l1Text64k := mkTextData 65536
  let l1Constant64k := mkConstantData 65536
  let l1Prng64k := mkPrngData 65536
  let windowBlock := mkPrngData 32768 0xC0FFEE
  let l1WindowEdge := windowBlock ++ windowBlock
  for (label, data) in
      [("size0", ByteArray.empty), ("size1", ByteArray.mk #[42]),
       ("size2", ByteArray.mk #[42, 42]), ("hash-tail3", ByteArray.mk #[7, 7, 7]),
       ("wide-hash4", ByteArray.mk #[1, 2, 3, 4]),
       ("constant64k", l1Constant64k), ("prng64k", l1Prng64k),
       ("window-edge64k", l1WindowEdge), ("text64k", l1Text64k),
       ("alice29", alice)] do
    checkL1WideFused label data

  -- Force the flat emitter independently of stored/fixed/dynamic arbitration.
  -- The three nonempty shapes cover reference-heavy, literal-heavy, and mixed
  -- token streams; empty also pins the core's EOB-only arm.
  checkFlatDynamicP "size0" ByteArray.empty
  checkFlatDynamicP "hash-tail3" (ByteArray.mk #[7, 7, 7])
  checkFlatDynamicP "constant64k" l1Constant64k
  checkFlatDynamicP "prng64k" l1Prng64k
  checkFlatDynamicP "text64k" l1Text64k
  checkFlatDynamicP "alice29" alice
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
  checkLargeL5CompiledPath
  IO.println "  PackedTokens tests passed"

end ZipTest.PackedTokens
