import Zip
/-! # Stage-0 ceiling probe: fuse token-frequency counting into the greedy matcher

Bench-only scratch (issue: `perf/freq-fusion`). `tokenFreqsP` is a full second
walk over the packed token array. The greedy matcher already touches every token
as it pushes it, so counting frequencies *there* would eliminate the re-read.
This exe measures whether that fusion is worth doing before any proof work:

* **matcher alone**    — `lz77ChainIterPMerged data 4` (the L1 greedy path)
* **matcher + freqs**  — a copy of the greedy merged loop that also threads the
                          two histogram arrays, bumping at each `acc.push` site
                          (same bump helpers `tokenFreqsP` uses)
* **matcher + separate `tokenFreqsP`** — the status quo: match, then re-walk

The fusion pays iff `matcher+freqs` is meaningfully cheaper than
`matcher + tokenFreqsP`. The saving is judged against total L1 compress time
(`deflateRaw data 1`): if it is < 2% of that, STOP (no proofs).

Run pinned: `bench/pin_core.sh lake exe freq-fusion bench/corpora/silesia/mozilla`
-/

open Zip.Native.Deflate

/-- 286-entry lit/len histogram seeded with the end-of-block pre-count, exactly
    `tokenFreqsP`'s initialization. -/
def initLitF : {a : Array Nat // a.size = 286} :=
  ⟨(Array.replicate 286 0).set! 256 1, by rw [Array.size_set!, Array.size_replicate]⟩

def initDistF : {a : Array Nat // a.size = 30} :=
  ⟨Array.replicate 30 0, by rw [Array.size_replicate]⟩

/-- Fused twin of `trailingP`: pushes each remaining byte as a literal token and
    bumps the lit/len histogram at the same site (`bumpLitFreqP`). -/
partial def fusedTrailing (data : ByteArray) (pos : Nat) (acc : Array UInt32)
    (litF : {a : Array Nat // a.size = 286}) (distF : {a : Array Nat // a.size = 30}) :
    Array UInt32 × {a : Array Nat // a.size = 286} × {a : Array Nat // a.size = 30} :=
  if _h : pos < data.size then
    let w := packTok (.literal data[pos]!)
    fusedTrailing data (pos + 1) (acc.push w) (bumpLitFreqP litF w) distF
  else (acc, litF, distF)

/-- Fused twin of `lz77GreedyMergedLoop`: byte-for-byte the same control flow,
    but every `acc.push (packTok t)` site is paired with the histogram bump
    `tokenFreqsP` would perform on that packed word. Literals go through
    `bumpLitFreqP`; references through `bumpRefLitFreqP` + `bumpRefDistFreqP`.
    `partial` (this is a throwaway ceiling probe, no termination proof). -/
partial def fusedGreedyLoop (data : ByteArray)
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
        let c := updateHashesMergedGuarded data hashSize prevSize c pos 1 matchLen insertCap
        let w := packTok (.reference matchLen (pos - matchPos))
        fusedGreedyLoop data windowSize hashSize prevSize maxChain insertCap niceLen c (pos + matchLen)
          (acc.push w) (bumpRefLitFreqP litF w) (bumpRefDistFreqP distF w)
      else
        let w := packTok (.literal (data[pos]!))
        fusedGreedyLoop data windowSize hashSize prevSize maxChain insertCap niceLen c (pos + 1)
          (acc.push w) (bumpLitFreqP litF w) distF
    else
      let w := packTok (.literal (data[pos]!))
      fusedGreedyLoop data windowSize hashSize prevSize maxChain insertCap niceLen c (pos + 1)
        (acc.push w) (bumpLitFreqP litF w) distF
  else
    fusedTrailing data pos acc litF distF

/-- Fused entry mirroring `lz77ChainIterPMerged` at L1 knobs (chain 4, cap 2,
    niceLen 258). Returns the tokens and the two histograms in one pass. -/
def fusedMatchWithFreqs (data : ByteArray) (maxChain insertCap niceLen : Nat) :
    Array UInt32 × {a : Array Nat // a.size = 286} × {a : Array Nat // a.size = 30} :=
  if data.size < 3 then
    fusedTrailing data 0 #[] initLitF initDistF
  else
    let hashSize := 65536
    let prevSize := min chainWinSize data.size
    fusedGreedyLoop data 32768 hashSize prevSize maxChain insertCap niceLen
      (.replicate (prevSize + hashSize) data.size) 0
      (Array.emptyWithCapacity data.size) initLitF initDistF

/-! ## Timing harness (mirrors `ZipL1Attrib`) -/

def medianNs (xs : List Nat) : Nat :=
  let a := xs.toArray.qsort (· < ·)
  if a.size == 0 then 0 else a[a.size / 2]!

def mbps (bytes nsPerOp : Nat) : Float :=
  if nsPerOp == 0 then 0.0
  else (bytes.toFloat / (1024.0 * 1024.0)) / (nsPerOp.toFloat / 1.0e9)

def round1 (f : Float) : Float := (f * 10.0).round / 10.0

/-- Live-sum a histogram pair so the counting work cannot be elided. -/
def sumFreqs (f : Array Nat × Array Nat) : Nat :=
  f.1.foldl (· + ·) 0 + f.2.foldl (· + ·) 0

/-! ### Elision-proof timed ops

The three matcher-based operations are pure functions of loop-invariant inputs,
so a naive `fun _ => expr` thunk lets the optimizer hoist the whole computation
out of the timing loop (a 51 MB matcher "measured" at 255 ns). Each op is a
top-level `@[noinline]` function that folds a per-iteration `salt` into its
result, and the timing loop threads the previous result back in as `salt`
(`acc := f acc`). That loop-carried dependency through an opaque `@[noinline]`
call forces a genuine recomputation every iteration. -/

@[noinline] def opAlone (data : ByteArray) (mc ic nl salt : Nat) : Nat :=
  (lz77ChainIterPMerged data mc 32768 ic nl).size + (salt &&& 1)

@[noinline] def opFused (data : ByteArray) (mc ic nl salt : Nat) : Nat :=
  let r := fusedMatchWithFreqs data mc ic nl
  r.1.size + sumFreqs (r.2.1.val, r.2.2.val) + (salt &&& 1)

@[noinline] def opSep (data : ByteArray) (mc ic nl salt : Nat) : Nat :=
  let t := lz77ChainIterPMerged data mc 32768 ic nl
  t.size + sumFreqs (tokenFreqsP t) + (salt &&& 1)

@[noinline] def opTotal (data : ByteArray) (salt : Nat) : Nat :=
  (deflateRaw data 1).size + (salt &&& 1)

/-- Time `f` `iters` times, threading the result back as the next `salt`; ns/op. -/
@[noinline] def timeOp (iters : Nat) (f : Nat → Nat) : IO Nat := do
  let t0 ← IO.monoNanosNow
  let mut acc : Nat := 1
  for _ in [:iters] do
    acc := f acc
  let t1 ← IO.monoNanosNow
  if acc == 0 then IO.eprintln "unreachable"
  return (t1 - t0) / (max iters 1)

def analyzeFile (name : String) (data : ByteArray) (iters reps : Nat) : IO Unit := do
  let size := data.size
  -- L1 knobs: chain 4, cap 2, niceLen 258.
  let maxChain := 4
  let insertCap := 2
  let niceLen := 258
  -- Correctness sanity: fused tokens == real matcher tokens, fused freqs ==
  -- tokenFreqsP over those tokens.
  let realToks := lz77ChainIterPMerged data maxChain 32768 insertCap niceLen
  let fused := fusedMatchWithFreqs data maxChain insertCap niceLen
  let freqRef := tokenFreqsP realToks
  let toksOk := fused.1 == realToks
  let freqOk := fused.2.1.val == freqRef.1 && fused.2.2.val == freqRef.2
  IO.println s!"  {name}: {size} bytes, {realToks.size} tokens; toksOk={toksOk} freqOk={freqOk}"
  unless toksOk && freqOk do
    IO.eprintln s!"  !! MISMATCH on {name} (toksOk={toksOk} freqOk={freqOk}) — numbers unreliable"

  -- Interleave the three variants (+ total) within each rep to share drift.
  let mut aloneT : List Nat := []
  let mut fusedT : List Nat := []
  let mut sepT   : List Nat := []
  let mut totalT : List Nat := []
  for _ in [:reps] do
    aloneT := (← timeOp iters (fun s => opAlone data maxChain insertCap niceLen s)) :: aloneT
    fusedT := (← timeOp iters (fun s => opFused data maxChain insertCap niceLen s)) :: fusedT
    sepT   := (← timeOp iters (fun s => opSep data maxChain insertCap niceLen s)) :: sepT
    totalT := (← timeOp iters (fun s => opTotal data s)) :: totalT

  let aloneNs := medianNs aloneT
  let fusedNs := medianNs fusedT
  let sepNs := medianNs sepT
  let totalNs := medianNs totalT
  let savingNs : Int := (sepNs : Int) - (fusedNs : Int)
  let savingF : Float := sepNs.toFloat - fusedNs.toFloat
  let savingPctTotal : Float :=
    if totalNs == 0 then 0.0 else (savingF / totalNs.toFloat) * 100.0
  IO.println s!"    matcher alone        : {aloneNs} ns  ({round1 (mbps size aloneNs)} MB/s)"
  IO.println s!"    matcher + freqs      : {fusedNs} ns  ({round1 (mbps size fusedNs)} MB/s)"
  IO.println s!"    matcher + tokenFreqsP: {sepNs} ns  ({round1 (mbps size sepNs)} MB/s)"
  IO.println s!"    total compress (L1)  : {totalNs} ns  ({round1 (mbps size totalNs)} MB/s)"
  IO.println s!"    tokenFreqsP-alone (sep-alone): {(sepNs : Int) - (aloneNs : Int)} ns"
  IO.println s!"    saving (sep - fused) : {savingNs} ns  =  {round1 savingPctTotal}% of total compress"
  IO.println s!"    reps alone={aloneT.reverse} fused={fusedT.reverse} sep={sepT.reverse}"
  IO.println ""

def main (args : List String) : IO Unit := do
  let reps := (args[1]? |>.bind (·.toNat?)).getD 4
  let paths := match args.head? with
    | some p => [p]
    | none => ["bench/corpora/silesia/mozilla"]
  IO.println s!"# Stage-0 freq-fusion ceiling probe (reps={reps})"
  IO.println ""
  for p in paths do
    let path := System.FilePath.mk p
    unless ← path.pathExists do
      IO.eprintln s!"not found: {path}"
      continue
    let data ← IO.FS.readBinFile path
    let iters := if data.size ≤ 262144 then 20 else if data.size ≤ 4194304 then 3 else 2
    analyzeFile (path.fileName.getD p) data iters reps
