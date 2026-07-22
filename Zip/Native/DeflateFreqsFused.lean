import Zip.Native.DeflateFreqs

/-!
# Fused greedy matcher: tokens and frequencies in one pass

`tokenFreqsP` is a full second walk over the packed token array (8.5% of L1
time on dickens; ~2.4% of total compress on the large Silesia binaries whose
token array spills L3 cache). The greedy merged matcher already touches every
token as it pushes it, so counting frequencies at each `acc.push` site removes
the re-read.

`lz77GreedyMergedLoopF` is the fused twin of `lz77GreedyMergedLoop`
(`Zip.Native.Deflate`): byte-for-byte the same control flow and token
accumulator, but it additionally threads the two histogram arrays, bumping at
each push site with the *same* helpers `tokenFreqsP` uses
(`bumpLitFreqP`/`bumpRefLitFreqP`/`bumpRefDistFreqP`). The histograms are seeded
exactly like `tokenFreqsP` (286 lit/len with EOB pre-counted, 30 distance), so
the running frequencies are `tokenFreqsP` of the running token accumulator at
every step — the invariant proved in `Zip/Spec/DeflateFreqsFusedCorrect.lean`.

As with `tokenFreqsP`/`emitTokensP`, the per-token frequency work lives inside
the opaque `bump*FreqP` helpers, so the well-founded-recursion body never forces
a `findTableCode` reduction (the landmine documented in `DeflateFreqs.lean`).
-/

namespace Zip.Native.Deflate

/-- Lit/len histogram seeded with the EOB pre-count, exactly `tokenFreqsP`'s
    initial `litLenFreqs` (`(replicate 286 0).set! 256 1`). -/
def initLitFreqF : {a : Array Nat // a.size = 286} :=
  ⟨(Array.replicate 286 0).set! 256 1, by rw [Array.size_set!, Array.size_replicate]⟩

/-- Distance histogram seeded to all-zero, exactly `tokenFreqsP`'s initial
    `distFreqs` (`replicate 30 0`). -/
def initDistFreqF : {a : Array Nat // a.size = 30} :=
  ⟨Array.replicate 30 0, by rw [Array.size_replicate]⟩

/-- Fused twin of `trailingP`: pushes each remaining byte as a literal token and
    bumps the lit/len histogram at the same site (`bumpLitFreqP`). -/
def trailingPF (data : ByteArray) (pos : Nat) (acc : Array UInt32)
    (litF : {a : Array Nat // a.size = 286}) (distF : {a : Array Nat // a.size = 30}) :
    Array UInt32 × {a : Array Nat // a.size = 286} × {a : Array Nat // a.size = 30} :=
  if h : pos < data.size then
    let w := packTok (.literal data[pos])
    trailingPF data (pos + 1) (acc.push w) (bumpLitFreqP litF w) distF
  else (acc, litF, distF)
termination_by data.size - pos

/-- Fused twin of `lz77GreedyMergedLoop` (`Zip.Native.Deflate`): identical
    control flow and token accumulator, additionally threading the two
    histograms. Every `acc.push (packTok t)` site is paired with the histogram
    bump `tokenFreqsP` performs on that packed word — literals through
    `bumpLitFreqP`, references through `bumpRefLitFreqP` + `bumpRefDistFreqP`.
    Proven equal to `(lz77GreedyMergedLoop ..., tokenFreqsP-of-tokens)` in
    `Zip/Spec/DeflateFreqsFusedCorrect.lean`. -/
def lz77GreedyMergedLoopF (data : ByteArray)
    (windowSize hashSize prevSize maxChain insertCap niceLen : Nat)
    (c : Array Nat) (pos : Nat) (acc : Array UInt32)
    (litF : {a : Array Nat // a.size = 286}) (distF : {a : Array Nat // a.size = 30}) :
    Array UInt32 × {a : Array Nat // a.size = 286} × {a : Array Nat // a.size = 30} :=
  if hlt : pos + 2 < data.size then
    let h := lz77Greedy.hash3 data pos hashSize hlt
    let head := headProbeGuarded c (prevSize + h)
    let c := guardedSet c (prevSize + h) pos
    let c := guardedSet c (pos &&& 0x7FFF) head
    let maxLen := min 258 (data.size - pos)
    have hmaxLenP : pos + maxLen ≤ data.size := by omega
    let r := chainWalkGuardedPackedU data c windowSize pos maxLen niceLen hmaxLenP head maxChain 0 0
    let matchLen := r % 512
    let matchPos := r / 512
    if hge : matchLen ≥ 3 then
      if hle : pos + matchLen ≤ data.size then
        have : data.size - (pos + matchLen) < data.size - pos := by omega
        let c := updateHashesMergedGuarded data hashSize prevSize c pos 1 matchLen insertCap
        let w := packTok (.reference matchLen (pos - matchPos))
        lz77GreedyMergedLoopF data windowSize hashSize prevSize maxChain insertCap niceLen c (pos + matchLen)
          (acc.push w) (bumpRefLitFreqP litF w) (bumpRefDistFreqP distF w)
      else
        let w := packTok (.literal (data[pos]'(by omega)))
        lz77GreedyMergedLoopF data windowSize hashSize prevSize maxChain insertCap niceLen c (pos + 1)
          (acc.push w) (bumpLitFreqP litF w) distF
    else
      let w := packTok (.literal (data[pos]'(by omega)))
      lz77GreedyMergedLoopF data windowSize hashSize prevSize maxChain insertCap niceLen c (pos + 1)
        (acc.push w) (bumpLitFreqP litF w) distF
  else
    trailingPF data pos acc litF distF
termination_by data.size - pos
decreasing_by all_goals omega

/-- Fused entry mirroring `lz77ChainIterPMerged` (`Zip.Native.Deflate`): builds
    the combined `prevSize + hashSize` array and runs `lz77GreedyMergedLoopF`,
    returning the packed token stream and its `tokenFreqsP` histograms in one
    pass. Proven equal to `(lz77ChainIterPMerged ..., tokenFreqsP-of-tokens)` in
    `Zip/Spec/DeflateFreqsFusedCorrect.lean`. -/
def lz77ChainIterPMergedF (data : ByteArray) (maxChain : Nat) (windowSize : Nat := 32768)
    (insertCap : Nat := 1000000000) (niceLen : Nat := 258) :
    Array UInt32 × {a : Array Nat // a.size = 286} × {a : Array Nat // a.size = 30} :=
  if data.size < 3 then
    trailingPF data 0 #[] initLitFreqF initDistFreqF
  else
    let hashSize := 65536
    let prevSize := min chainWinSize data.size
    lz77GreedyMergedLoopF data windowSize hashSize prevSize maxChain insertCap niceLen
      (.replicate (prevSize + hashSize) data.size) 0
      (Array.emptyWithCapacity data.size) initLitFreqF initDistFreqF

end Zip.Native.Deflate
