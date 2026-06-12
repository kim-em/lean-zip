import Zip.Native.DeflateDynamic

/-!
  Fast-tier fused matcher-emitters (Wave 5.1 measurement slice — NO proofs
  in this round).

  The level-1 pipeline materializes the whole packed token stream
  (`lz77ChainIterP`), then walks it again to histogram (`tokenFreqsP`) and a
  third time to emit. The two variants here fuse those passes into the
  matcher loop itself, zlib `deflate_fast`-style:

  * **Variant F** (`deflateFastF`): each literal/match is emitted *inline*
    as fixed-Huffman codes into a running `BitWriter` — one pass total, one
    block (`BFINAL=1, BTYPE=01`), no token array at all.
  * **Variant D** (`deflateFastD`): each literal/match is appended to a
    packed token buffer *and* histogrammed inline; every ~`blockBytes` input
    bytes the buffer is flushed as one dynamic-Huffman block
    (`emitDynBlockP`) and the buffer/histograms reset — so the token buffer
    and frequency arrays stay block-sized and the second/third passes run
    only over the current block.

  Both variants instantiate **one** shared fused loop (`fastFuseLoop`), the
  greedy `lz77ChainIterP.mainLoop` shape (hash3 + `headProbeGuarded` +
  `guardedSet` + `chainWalkGuardedPacked` + `updateHashesGuarded`, min-match
  3, `min 258` clamp) with token-array accumulation replaced by two
  `@[specialize]`d emitter parameters. All knobs (`windowSize`, `hashSize`,
  `depth`, `cap`) are *parameters*, never literal constants inside the WF
  body (the `buildCache` landmine, `Zip/Native/DeflateParse.lean`).

  Phase instrumentation: `deflateFastF_matchOnly` / `deflateFastD_matchOnly`
  run the same loop with the bit emission compiled out (sink emitters), so a
  driver can measure the matcher-vs-emit split as (full − matchOnly).

  Nothing here is wired into `deflateRaw`; correctness for this slice is the
  driver's roundtrip assertion (`ProfileMain --fast`), not spec theorems.
-/

namespace Zip.Native.Deflate

open Zip.Spec.DeflateStoredCorrect (deflateStoredPure storedBlockBytes)

/-! ## The shared fused matcher loop -/

/-- Trailing tail of the fused loop: the last ≤ 3 bytes (or the whole input
    when `data.size < 3`) are emitted as literals. Generic twin of
    `lz77GreedyIter.trailing`/`trailingP` with the push replaced by the
    `emitLit` parameter. -/
@[specialize] def fastFuseTrailing {σ : Type} (emitLit : σ → UInt8 → σ)
    (data : ByteArray) (pos : Nat) (st : σ) : σ :=
  if h : pos < data.size then
    fastFuseTrailing emitLit data (pos + 1) (emitLit st data[pos])
  else st
termination_by data.size - pos

/-- The shared fused matcher-emitter skeleton: greedy hash-chain matching
    (no lazy lookahead) over positions — exactly the `lz77ChainIterP.mainLoop`
    shape minus the token-array accumulator. Each found literal/match is fed
    to the `emitLit`/`emitRef` parameters threading an arbitrary emitter
    state `σ` (a `BitWriter` for variant F, a block-accumulator record for
    variant D, a `Nat` sink for the match-only instrumentation).

    `emitRef st len dist` receives `3 ≤ len ≤ 258` and
    `1 ≤ dist ≤ windowSize` (the chain-walk guards), same as the packed
    matchers' encodability envelope.

    Knobs (`windowSize hashSize depth cap`) are parameters: literal
    constants inside a WF body send the well-founded elaboration into deep
    reduction (see `buildCache`'s docstring in `Zip/Native/DeflateParse.lean`).
    `depth` is the chain-walk fuel (`chainDepth` ladder), `cap` the interior
    insertion cap (`insertCap` ladder). -/
@[specialize] def fastFuseLoop {σ : Type} (emitLit : σ → UInt8 → σ)
    (emitRef : σ → Nat → Nat → σ)
    (data : ByteArray) (windowSize hashSize depth cap : Nat)
    (hashTable prev : Array Nat) (pos : Nat) (st : σ) : σ :=
  if hlt : pos + 2 < data.size then
    let h := lz77Greedy.hash3 data pos hashSize hlt
    let head := headProbeGuarded hashTable h
    let hashTable := guardedSet hashTable h pos
    let prev := guardedSet prev pos head
    let maxLen := min 258 (data.size - pos)
    have hmaxLenP : pos + maxLen ≤ data.size := by omega
    let r := chainWalkGuardedPacked data prev windowSize pos maxLen hmaxLenP head depth 0 0
    let matchLen := r % 512
    let matchPos := r / 512
    if hge : matchLen ≥ 3 then
      if hle : pos + matchLen ≤ data.size then
        have : data.size - (pos + matchLen) < data.size - pos := by omega
        let (hashTable, prev) :=
          updateHashesGuarded data hashSize hashTable prev pos 1 matchLen cap
        fastFuseLoop emitLit emitRef data windowSize hashSize depth cap hashTable prev
          (pos + matchLen) (emitRef st matchLen (pos - matchPos))
      else
        fastFuseLoop emitLit emitRef data windowSize hashSize depth cap hashTable prev
          (pos + 1) (emitLit st (data[pos]'(by omega)))
    else
      fastFuseLoop emitLit emitRef data windowSize hashSize depth cap hashTable prev
        (pos + 1) (emitLit st (data[pos]'(by omega)))
  else
    fastFuseTrailing emitLit data pos st
termination_by data.size - pos
decreasing_by all_goals omega

/-- Run the fused loop over `data` with fresh chain state (buckets and `prev`
    initialised to the `data.size` sentinel, as `lz77ChainIterP` does), with
    the standard 32 KiB window and 65536-bucket hash. Inputs under 3 bytes go
    straight to the trailing-literals tail. -/
@[inline] def fastFuseRun {σ : Type} (emitLit : σ → UInt8 → σ)
    (emitRef : σ → Nat → Nat → σ) (data : ByteArray) (depth cap : Nat) (st : σ) : σ :=
  if data.size < 3 then
    fastFuseTrailing emitLit data 0 st
  else
    fastFuseLoop emitLit emitRef data 32768 65536 depth cap
      (.replicate 65536 data.size) (.replicate data.size data.size) 0 st

/-! ## Variant F: inline fixed-Huffman emission -/

/-- Emit one literal as its fixed-Huffman code (the literal arm of
    `emitTokensP`, as a standalone emitter). -/
@[inline] def fastEmitLitF (bw : BitWriter) (b : UInt8) : BitWriter :=
  have : b.toNat < fixedLitCodes.size := by
    have := UInt8.toNat_lt b; rw [Deflate.fixedLitCodes_size]; omega
  let (code, len) := fixedLitCodes[b.toNat]
  bw.writeHuffCode code len

/-- Emit one reference as fixed-Huffman codes directly from `(len, dist)` —
    the `emitRefFixedP` arm logic (dense-table `findLengthCodeFast`/
    `findDistCodeFast`, dead-code `else` fallbacks) without the packed-word
    round-trip. Non-recursive on purpose: a match scrutinee over
    `findLengthCodeFast` must never sit inside a WF loop body (the
    `tokenFreqsP` landmine, `Zip/Native/DeflateFreqs.lean`). -/
@[inline] def fastEmitRefF (bw : BitWriter) (length dist : Nat) : BitWriter :=
  match findLengthCodeFast length with
  | some (idx, extraCount, extraVal) =>
    if hlit : idx + 257 < fixedLitCodes.size then
      let (code, len) := fixedLitCodes[idx + 257]
      let bw := bw.writeHuffCode code len
      let bw := bw.writeBits extraCount extraVal
      match findDistCodeFast dist with
      | some (dIdx, dExtraCount, dExtraVal) =>
        if hdist : dIdx < fixedDistCodes.size then
          let (dCode, dLen) := fixedDistCodes[dIdx]
          let bw := bw.writeHuffCode dCode dLen
          bw.writeBits dExtraCount dExtraVal
        else bw
      | none => bw
    else bw
  | none => bw

/-- Variant F without the stored fallback: one fused pass matching and
    emitting fixed-Huffman codes inline; a single block mirroring
    `deflateFixedBlock`'s frame (BFINAL=1, BTYPE=01 header, end-of-block
    symbol 256, flush). -/
def deflateFastFCore (data : ByteArray) (depth cap : Nat) : ByteArray :=
  let bw := BitWriter.empty
  let bw := bw.writeBits 1 1  -- BFINAL = 1
  let bw := bw.writeBits 2 1  -- BTYPE = 01 (fixed Huffman)
  let bw := fastFuseRun fastEmitLitF fastEmitRefF data depth cap bw
  have h256 : 256 < fixedLitCodes.size := by rw [Deflate.fixedLitCodes_size]; omega
  let (code, len) := fixedLitCodes[256]
  (bw.writeHuffCode code len).flush

/-- Variant F (fast tier, fixed Huffman): fused greedy match + inline
    fixed-code emission, with a whole-output stored fallback so
    incompressible input never expands. The fallback compares *after*
    building (slice simplicity); `storedBlockBytes` sizes the stored
    candidate without materializing it unless it wins. -/
def deflateFastF (data : ByteArray) (depth cap : Nat) : ByteArray :=
  let out := deflateFastFCore data depth cap
  if storedBlockBytes data < out.size then deflateStoredPure data else out

/-! ## Variant D: fused histogram + per-block dynamic emission -/

/-- Fresh per-block lit/len histogram: 286 zeros with the end-of-block
    symbol (256) pre-counted, exactly `tokenFreqsP`'s initial state. -/
def freshLitFreqs : {a : Array Nat // a.size = 286} :=
  ⟨(Array.replicate 286 0).set! 256 1,
    by rw [Array.size_set!, Array.size_replicate]⟩

/-- Fresh per-block distance histogram: 30 zeros. -/
def freshDistFreqs : {a : Array Nat // a.size = 30} :=
  ⟨Array.replicate 30 0, by rw [Array.size_replicate]⟩

/-- Packed-token twin of `emitDynBlock`: emit one dynamic Huffman block
    (`BFINAL = isFinal`, BTYPE=10) onto a running writer directly from the
    packed `UInt32` stream, via `emitTokensWithCodesP`. The boxed
    `emitDynBlock`'s `data.size == 0` guard is dropped: `emitTokensWithCodesP`
    over an empty token array writes nothing, so a token-empty block emits
    just the tree header and end-of-block (still a valid block). -/
def emitDynBlockP (bw : BitWriter) (tokens : Array UInt32)
    (litLens distLens : List Nat)
    (hlit : litLens.length = 286) (hdist : distLens.length = 30)
    (isFinal : Bool) : BitWriter :=
  let litCodes := canonicalCodes (litLens.toArray.map Nat.toUInt8)
  let distCodes := canonicalCodes (distLens.toArray.map Nat.toUInt8)
  let bw := bw.writeBits 1 (if isFinal then 1 else 0)  -- BFINAL (1 bit)
  let bw := bw.writeBits 2 2                            -- BTYPE = 10 (dynamic)
  let bw := writeDynamicHeader bw litLens distLens
  have hlit_size : litCodes.size ≥ 286 := by
    show (canonicalCodes (litLens.toArray.map Nat.toUInt8)).size ≥ 286
    rw [canonicalCodes_size, Array.size_map, List.size_toArray]; omega
  have hdist_size : distCodes.size ≥ 30 := by
    show (canonicalCodes (distLens.toArray.map Nat.toUInt8)).size ≥ 30
    rw [canonicalCodes_size, Array.size_map, List.size_toArray]; omega
  have h256 : 256 < litCodes.size := by
    show 256 < (canonicalCodes (litLens.toArray.map Nat.toUInt8)).size
    rw [canonicalCodes_size, Array.size_map, List.size_toArray]; omega
  let bw := emitTokensWithCodesP bw tokens litCodes distCodes hlit_size hdist_size 0
  let (code, len) := litCodes[256]'h256
  bw.writeHuffCode code len

/-- Flush one accumulated block: fit dynamic code lengths to the block's own
    histograms and emit the packed tokens as one dynamic block. -/
def fastFlushBlockD (bw : BitWriter) (toks : Array UInt32)
    (lit : {a : Array Nat // a.size = 286}) (dist : {a : Array Nat // a.size = 30})
    (isFinal : Bool) : BitWriter :=
  let lens := dynamicCodeLengths lit.val dist.val
  emitDynBlockP bw toks lens.1 lens.2
    (dynamicCodeLengths_length lit.val dist.val).1
    (dynamicCodeLengths_length lit.val dist.val).2 isFinal

/-- Variant D emitter state: the running bitstream, the current block's
    packed tokens and fused histograms, the block-size knob, and the input
    bytes covered by the current block. -/
structure FastDState where
  bw : BitWriter
  toks : Array UInt32
  lit : {a : Array Nat // a.size = 286}
  dist : {a : Array Nat // a.size = 30}
  blockBytes : Nat
  bytes : Nat

/-- Close the current block as a non-final dynamic block once it covers
    `blockBytes` input bytes, resetting the accumulator and histograms.
    The final block is emitted by `deflateFastDCore` after the loop. -/
@[inline] def fastMaybeFlushD (st : FastDState) : FastDState :=
  if st.bytes ≥ st.blockBytes then
    match st with
    | ⟨bw, toks, lit, dist, blockBytes, _⟩ =>
      ⟨fastFlushBlockD bw toks lit dist false, #[], freshLitFreqs, freshDistFreqs,
        blockBytes, 0⟩
  else st

/-- Variant D literal emitter: push the packed word, bump the lit/len
    histogram (`bumpLitFreqP`, the opaque-helper pattern from
    `Zip/Native/DeflateFreqs.lean`), and flush at the block boundary.
    Destructures the state so the token buffer stays uniquely referenced
    across the push (no copy-on-write). -/
@[inline] def fastEmitLitD (st : FastDState) (b : UInt8) : FastDState :=
  match st with
  | ⟨bw, toks, lit, dist, blockBytes, bytes⟩ =>
    let w := packTok (.literal b)
    fastMaybeFlushD ⟨bw, toks.push w, bumpLitFreqP lit w, dist, blockBytes, bytes + 1⟩

/-- Variant D reference emitter: push the packed word, bump both histograms
    (`bumpRefLitFreqP`/`bumpRefDistFreqP`), and flush at the block boundary. -/
@[inline] def fastEmitRefD (st : FastDState) (len dist : Nat) : FastDState :=
  match st with
  | ⟨bw, toks, litF, distF, blockBytes, bytes⟩ =>
    let w := packTok (.reference len dist)
    fastMaybeFlushD ⟨bw, toks.push w, bumpRefLitFreqP litF w, bumpRefDistFreqP distF w,
      blockBytes, bytes + len⟩

/-- Variant D without the stored fallback: fused greedy match + per-block
    token/histogram accumulation, one dynamic block per ~`blockBytes` input
    bytes (non-final), and a final block for the remainder (always emitted,
    possibly token-empty, so the stream always carries BFINAL=1). References
    legally cross block boundaries — the 32 KiB window spans the whole
    bitstream (RFC 1951 §3.2). -/
def deflateFastDCore (data : ByteArray) (depth cap blockBytes : Nat) : ByteArray :=
  let st0 : FastDState := ⟨BitWriter.empty, #[], freshLitFreqs, freshDistFreqs, blockBytes, 0⟩
  let st := fastFuseRun fastEmitLitD fastEmitRefD data depth cap st0
  (fastFlushBlockD st.bw st.toks st.lit st.dist true).flush

/-- Variant D (fast tier, per-block dynamic Huffman): fused greedy match +
    inline histogram, dynamic block per `blockBytes` input bytes, with the
    same whole-output stored fallback as `deflateFastF`. -/
def deflateFastD (data : ByteArray) (depth cap blockBytes : Nat) : ByteArray :=
  let out := deflateFastDCore data depth cap blockBytes
  if storedBlockBytes data < out.size then deflateStoredPure data else out

/-! ## Phase instrumentation: the loop with emission compiled out

`(full − matchOnly)` is the emit share. The F sink does only trivial `Nat`
arithmetic per token (pure matcher cost); the D sink keeps the token pushes,
histogram bumps, and per-block resets but drops all bit emission (matcher +
histogram cost). Each sink folds its accumulators into the returned `Nat` so
nothing is dead code. -/

/-- F-sink literal emitter: fold the byte into the sink. -/
@[inline] def fastSinkLitF (s : Nat) (b : UInt8) : Nat := s + b.toNat

/-- F-sink reference emitter: fold length and distance into the sink. -/
@[inline] def fastSinkRefF (s len dist : Nat) : Nat := s + len + dist

/-- Variant F with the emission compiled out: the identical fused loop
    feeding a `Nat` sink. The driver measures (deflateFastF − this) as the
    fixed-Huffman emit share. -/
def deflateFastF_matchOnly (data : ByteArray) (depth cap : Nat) : Nat :=
  fastFuseRun fastSinkLitF fastSinkRefF data depth cap 0

/-- Variant D match+histogram state: `FastDState` minus the bitstream, plus
    a sink the per-block resets fold into. -/
structure FastDSinkState where
  toks : Array UInt32
  lit : {a : Array Nat // a.size = 286}
  dist : {a : Array Nat // a.size = 30}
  blockBytes : Nat
  bytes : Nat
  sink : Nat

/-- Fold a block's accumulators into the sink (stands in for
    `fastFlushBlockD` so the histogram/token work is observed, not emitted). -/
@[inline] def fastSinkBlockD (toks : Array UInt32)
    (lit : {a : Array Nat // a.size = 286}) (dist : {a : Array Nat // a.size = 30})
    (sink : Nat) : Nat :=
  sink + toks.size + lit.val[256]! + dist.val[0]!

/-- Sink twin of `fastMaybeFlushD`: same boundary test and resets, block
    consumed by `fastSinkBlockD` instead of emitted. -/
@[inline] def fastMaybeFlushSinkD (st : FastDSinkState) : FastDSinkState :=
  if st.bytes ≥ st.blockBytes then
    match st with
    | ⟨toks, lit, dist, blockBytes, _, sink⟩ =>
      ⟨#[], freshLitFreqs, freshDistFreqs, blockBytes, 0,
        fastSinkBlockD toks lit dist sink⟩
  else st

/-- Sink twin of `fastEmitLitD`: token push + histogram bump, no emission. -/
@[inline] def fastSinkLitD (st : FastDSinkState) (b : UInt8) : FastDSinkState :=
  match st with
  | ⟨toks, lit, dist, blockBytes, bytes, sink⟩ =>
    let w := packTok (.literal b)
    fastMaybeFlushSinkD ⟨toks.push w, bumpLitFreqP lit w, dist, blockBytes, bytes + 1, sink⟩

/-- Sink twin of `fastEmitRefD`: token push + both histogram bumps, no
    emission. -/
@[inline] def fastSinkRefD (st : FastDSinkState) (len dist : Nat) : FastDSinkState :=
  match st with
  | ⟨toks, litF, distF, blockBytes, bytes, sink⟩ =>
    let w := packTok (.reference len dist)
    fastMaybeFlushSinkD ⟨toks.push w, bumpRefLitFreqP litF w, bumpRefDistFreqP distF w,
      blockBytes, bytes + len, sink⟩

/-- Variant D with the dynamic-block emission compiled out: the identical
    fused loop with token accumulation and fused histograms, feeding a sink.
    The driver measures (deflateFastD − this) as the dynamic emit share
    (tree fitting + header + bit packing). -/
def deflateFastD_matchOnly (data : ByteArray) (depth cap blockBytes : Nat) : Nat :=
  let st0 : FastDSinkState := ⟨#[], freshLitFreqs, freshDistFreqs, blockBytes, 0, 0⟩
  let st := fastFuseRun fastSinkLitD fastSinkRefD data depth cap st0
  fastSinkBlockD st.toks st.lit st.dist st.sink

end Zip.Native.Deflate
