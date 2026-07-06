import ZipTest.Helpers

/-! Conformance tests for the size-then-emit dispatch (`deflateRaw`/`deflateCompressed`).

The level-≥5 dispatch sizes the stored/fixed/dynamic candidates from a single
token pass and emits only the winner, replacing the old "emit all three, keep the
smallest" `pickSmaller` cascade. That refactor is byte-identical *iff* the
`fixedBlockBytes`/`dynBlockBytes` cost models equal the emitted block sizes — a
fact the roundtrip proofs do not establish (they hold for whichever block is
chosen). These tests pin that invariant:

1. `fixedBlockBytes`/`dynBlockBytes` equal the actual emitted `.size`.
2. The new `deflateRaw` is byte-identical to the old pickSmaller-of-emitted-blocks
   reference across diverse inputs.
-/

open Zip.Native.Deflate

namespace ZipTest.SizeHelpers

/-- Old level-≥5 behaviour: emit stored, fixed, and dynamic, keep the smallest. -/
private def deflateRawReference (data : ByteArray) : ByteArray :=
  let tokens := lz77LazyIter data
  pickSmaller (Zip.Spec.DeflateStoredCorrect.deflateStoredPure data)
    (pickSmaller (deflateFixedBlock data tokens) (deflateDynamicBlock data tokens))

/-- A small deterministic LCG byte generator for assorted test inputs. -/
private def lcgBytes (seed n : Nat) : ByteArray := Id.run do
  let mut s := seed
  let mut acc := ByteArray.empty
  for _ in [0:n] do
    s := (s * 1103515245 + 12345) % 2147483648
    acc := acc.push (UInt8.ofNat (s / 65536 % 256))
  return acc

/-- `i`-byte block of byte value `b`. -/
private def repeatByte (b n : Nat) : ByteArray :=
  ByteArray.mk (Array.replicate n (UInt8.ofNat b))

private def asciiText (n : Nat) : ByteArray := Id.run do
  let pat := "the quick brown fox jumps over the lazy dog. ".toUTF8
  let mut acc := ByteArray.empty
  let mut i := 0
  while acc.size < n do
    acc := acc.push (pat.get! (i % pat.size))
    i := i + 1
  return acc

/-- All the inputs we check: edge cases, compressible, and incompressible. -/
private def samples : List (String × ByteArray) :=
  [ ("empty", ByteArray.empty),
    ("single", ByteArray.mk #[42]),
    ("two", ByteArray.mk #[0, 255]),
    ("zeros-1k", repeatByte 0 1024),
    ("ones-300", repeatByte 1 300),
    ("text-2k", asciiText 2048),
    ("text-tiny", asciiText 7),
    ("prng-2k", lcgBytes 1 2048),
    ("prng-37", lcgBytes 99 37),
    ("prng-1", lcgBytes 7 1) ]

def tests : IO Unit := do
  IO.println "  SizeHelpers (size-then-emit conformance) tests..."
  for (name, data) in samples do
    let tokens := lz77LazyIter data
    let (lf, df) := tokenFreqs tokens
    -- 1a. fixed cost model == emitted fixed block size
    let fixedSize := fixedBlockBytes lf df
    let fixedEmit := (deflateFixedBlock data tokens).size
    unless fixedSize == fixedEmit do
      throw (IO.userError
        s!"fixedBlockBytes mismatch on {name}: model={fixedSize} emit={fixedEmit}")
    -- 1b. dynamic cost model == emitted dynamic block size
    let (litLens, distLens) := dynamicCodeLengths lf df
    let dynSize := dynBlockBytes lf df litLens distLens
    let dynEmit := (deflateDynamicBlock data tokens).size
    unless dynSize == dynEmit do
      throw (IO.userError
        s!"dynBlockBytes mismatch on {name}: model={dynSize} emit={dynEmit}")
    -- 2. new deflateRaw byte-identical to the old emit-all reference (level 6)
    let newOut := deflateRaw data 6
    let refOut := deflateRawReference data
    unless newOut.beq refOut do
      throw (IO.userError
        s!"deflateRaw(6) not byte-identical to reference on {name}: \
           new.size={newOut.size} ref.size={refOut.size}")
    -- the chosen output must still inflate back to the input
    match Zip.Native.Inflate.inflate newOut (data.size + 64) with
    | .ok back =>
      unless back.beq data do
        throw (IO.userError s!"deflateRaw(6) roundtrip mismatch on {name}")
    | .error e => throw (IO.userError s!"deflateRaw(6) inflate failed on {name}: {e}")

  -- 3. Shared-window partition cost model (`sharedPartitionBits`) equals the
  -- emitted bit length of `emitSharedBlocksAt` for the same cuts — the invariant
  -- that makes `chooseSplitsArbitrated`'s never-worse-than-fixed-cadence
  -- guarantee trustworthy. Checked across adversarial, fixed-cadence, and
  -- heuristic cut lists; the flushed byte size must be ⌈bits/8⌉.
  for (name, data) in samples do
    if data.size > 0 then
      let toks := lzMatch data 9
      let cutsLists : List (String × List Nat) :=
        [ ("empty", []),
          ("zeros", [0, 0, 0]),
          ("huge", [1000000000]),
          ("nonmonotone", [5, 3, 7]),
          ("fixed", fixedCadenceCuts sharedTokChunk toks.size),
          ("fixed-tiny", fixedCadenceCuts 3 toks.size),
          ("heuristic", chooseSplitsHeuristic toks) ]
      for (cname, cuts) in cutsLists do
        let modelBits := sharedPartitionBits toks cuts 0
        let bw := emitSharedBlocksAt data toks cuts 0 Zip.Native.BitWriter.empty
        unless modelBits == bw.bitLength do
          throw (IO.userError
            s!"sharedPartitionBits mismatch on {name}/{cname}: \
               model={modelBits} emitted={bw.bitLength}")
        unless bw.flush.size == (modelBits + 7) / 8 do
          throw (IO.userError
            s!"flushed size mismatch on {name}/{cname}: \
               bytes={bw.flush.size} bits={modelBits}")
      -- 4. Arbitration never sizes worse than the fixed cadence, and the emitted
      -- shared candidate never exceeds the old fixed-cadence emitter's output.
      let fixedCuts := fixedCadenceCuts sharedTokChunk toks.size
      let arbCuts := chooseSplitsArbitrated toks
      unless sharedPartitionBits toks arbCuts 0 ≤ sharedPartitionBits toks fixedCuts 0 do
        throw (IO.userError s!"chooseSplitsArbitrated sized worse than fixed on {name}")
      let arbOut := deflateDynamicBlocksSharedAt data chooseSplitsArbitrated 9
      let fixedOut := deflateDynamicBlocksShared data sharedTokChunk 9
      unless arbOut.size ≤ fixedOut.size do
        throw (IO.userError
          s!"arbitrated shared output larger than fixed on {name}: \
             {arbOut.size} > {fixedOut.size}")
    -- 5. The cut-list emitter with fixed-cadence cuts is byte-identical to the
    -- fixed-cadence emitter (also covers the empty input, where both emit the
    -- single final block).
    let viaCuts := deflateDynamicBlocksSharedAt data
      (fun toks => fixedCadenceCuts sharedTokChunk toks.size) 9
    let viaChunk := deflateDynamicBlocksShared data sharedTokChunk 9
    unless viaCuts.beq viaChunk do
      throw (IO.userError
        s!"fixedCadenceCuts not byte-identical to fixed-cadence emitter on {name}: \
           {viaCuts.size} vs {viaChunk.size}")
    -- 6. The sized-tree pipeline (Wave 5, #2552) is byte-identical to the
    -- reference arbitrated candidate, and the fused sizing pass agrees with
    -- `sharedPartitionBits` (both proved in `Zip/Spec/DeflateBlockSplit.lean`;
    -- this pins the compiled code).
    let toks9 := lzMatch data 9
    let sizedOut := deflateDynamicBlocksSharedSized data toks9
    let refOut := deflateDynamicBlocksSharedAtTokens data toks9 chooseSplitsArbitrated
    unless sizedOut.beq refOut do
      throw (IO.userError
        s!"deflateDynamicBlocksSharedSized not byte-identical on {name}: \
           {sizedOut.size} vs {refOut.size}")
    let arbCuts := chooseSplitsArbitrated toks9
    unless (sharedPartitionSized toks9 arbCuts 0).1 == sharedPartitionBits toks9 arbCuts 0 do
      throw (IO.userError s!"sharedPartitionSized bits mismatch on {name}")

  -- 7. Size-arbitrated split dispatch with sized-tree reuse (#2753): each
  -- candidate is *prepared* — the winner's flushed byte size paired with an
  -- emit thunk that reuses the trees built during sizing. The prepared sizes
  -- must equal the emitted `.size` (so the arbitration decides by the true
  -- flushed byte counts), the emit thunks must be byte-identical to the
  -- reference emitters (`deflateRawBaseP` / `deflateDynamicBlocksSharedAtP`,
  -- proven — this pins the compiled code), and the new emit-only-the-winner
  -- `deflateRaw` at levels 6/7/8 must be byte-identical to the retired
  -- emit-every-candidate dispatch.
  for (name, data) in samples do
    for level in [(6 : UInt8), 7, 8] do
      let ptokens := lzMatchP data level
      -- 7a. base prep: size == emitted size, thunk == reference emit
      let basePrep := deflateRawBasePPrep data ptokens
      let baseEmit := deflateRawBaseP data ptokens
      unless basePrep.1 == baseEmit.size do
        throw (IO.userError
          s!"deflateRawBasePPrep size mismatch on {name}@L{level}: model={basePrep.1} emit={baseEmit.size}")
      unless (basePrep.2 ()).beq baseEmit do
        throw (IO.userError s!"deflateRawBasePPrep emit not byte-identical on {name}@L{level}")
      -- 7b. split prep: size == emitted size and thunk == reference emit, over
      -- diverse cut lists (the tree-reuse emit must match the recompute emit)
      if data.size > 0 then
        let cutsLists : List (String × List Nat) :=
          [ ("heuristic", chooseSplitsHeuristicP ptokens data.size),
            ("fixed", fixedCadenceCuts sharedTokChunk ptokens.size),
            ("empty", []),
            ("nonmonotone", [5, 3, 7]),
            ("huge", [1000000000]) ]
        for (cname, cuts) in cutsLists do
          let splitPrep := deflateDynamicBlocksSharedAtSizedP data ptokens cuts
          let splitEmit := deflateDynamicBlocksSharedAtP data ptokens cuts
          unless splitPrep.1 == splitEmit.size do
            throw (IO.userError
              s!"deflateDynamicBlocksSharedAtSizedP size mismatch on {name}@L{level}/{cname}: \
                 model={splitPrep.1} emit={splitEmit.size}")
          unless (splitPrep.2 ()).beq splitEmit do
            throw (IO.userError
              s!"deflateDynamicBlocksSharedAtSizedP emit not byte-identical on {name}@L{level}/{cname}")
      -- 7c. the size-arbitrated dispatch is byte-identical to the old
      -- emit-every-candidate one (`pickSmaller` over emitted blocks).
      let base := deflateRawBaseP data ptokens
      let cuts := chooseSplitsHeuristicP ptokens data.size
      let withObs := if cuts.isEmpty then base
        else pickSmaller base (deflateDynamicBlocksSharedAtP data ptokens cuts)
      let refOut := if 8 ≤ level then
          pickSmaller withObs (deflateDynamicBlocksSharedAtP data ptokens
            (fixedCadenceCuts sharedTokChunk ptokens.size))
        else withObs
      let newOut := deflateRaw data level
      unless newOut.beq refOut do
        throw (IO.userError
          s!"deflateRaw(L{level}) not byte-identical to emit-all reference on {name}: \
             new.size={newOut.size} ref.size={refOut.size}")
  IO.println "  SizeHelpers tests passed."

end ZipTest.SizeHelpers
