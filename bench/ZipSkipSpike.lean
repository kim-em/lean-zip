import Zip

/-! # skip-sweep — incompressible-stretch skip-ahead ladder sweep (#2766)

Sweeps the LZ4/zstd-style skip-ahead shift (`DeflateDynamic.skipShift`) of the
lazy matcher over corpus members, for tuning the per-level ladder. Uses the
shipped, proven matcher `lz77ChainLazyIterP` directly (the `skipShift` argument
is the last positional parameter); `skipShift = 63` disables skip-ahead and
reproduces the pre-skip output.

On a run of positions with no match the matcher advances by
`stride = 1 + (missStreak >>> skipShift)`, emitting the skipped bytes as
literals. A smaller shift lets the stride grow sooner (faster, more ratio cost);
the threshold rarely triggers on dense-match data (text, `sao`), so those pay
almost nothing. See the PR discussion for the measured speed/ratio table that
chose the shipped ladder.

Usage: lake exe skip-spike <file> [<file> ...]          # ratio (deterministic)
       lake exe skip-spike --time <file> [<file> ...]   # speed (pin the core)
-/

open Zip.Native.Deflate

/-- One sweep config: matcher knobs plus the skip-ahead shift (`63` disables). -/
structure SkipConfig where
  label : String
  chain : Nat
  gm : Nat
  nl : Nat
  shift : Nat

/-- Compress under one config with the shipped lazy matcher (skip-ahead at
    `cfg.shift`, half-depth lookahead like production), returning the single-block
    size. -/
def runSkip (cfg : SkipConfig) (data : ByteArray) : Nat :=
  let ptoks := lz77ChainLazyIterP data cfg.chain 32768 1000000000 cfg.gm cfg.nl (cfg.chain / 2) cfg.shift
  (deflateRawBaseP data ptoks).size

/-- The shift ladder swept per corpus member: disabled, then progressively more
    aggressive skip-ahead (smaller shift → the stride grows sooner). -/
def skipConfigs (chain gm nl : Nat) : List SkipConfig :=
  [ ⟨s!"off", chain, gm, nl, 63⟩,
    ⟨s!"sh7", chain, gm, nl, 7⟩,
    ⟨s!"sh6", chain, gm, nl, 6⟩,
    ⟨s!"sh5", chain, gm, nl, 5⟩,
    ⟨s!"sh4", chain, gm, nl, 4⟩ ]

/-- L6-like production slot (chain 64, gate off, nice 65), the issue's target. -/
def sweepConfigs : List SkipConfig := skipConfigs 64 259 65

def timeMain (paths : List String) : IO Unit := do
  let mut files : List ByteArray := []
  for path in paths do
    files := files ++ [← IO.FS.readBinFile path]
  let total := files.foldl (fun a f => a + f.size) 0
  IO.println s!"corpus: {paths.length} files, {total} bytes"
  for rep in [0:3] do
    for cfg in sweepConfigs do
      let t0 ← IO.monoNanosNow
      let mut sink := 0
      for f in files do
        sink := sink + runSkip cfg f
      let t1 ← IO.monoNanosNow
      let mbps := total.toFloat / 1048576.0 / ((t1 - t0).toFloat / 1.0e9)
      IO.println s!"rep {rep} {cfg.label}: {mbps} MB/s (out {sink})"
      (← IO.getStdout).flush

/-- Faithful copy of `deflateRaw`'s level-6 path (base vs observation-divergence
    split, size-arbitrated) with an explicit `skipShift` so the only variable in
    an A/B is skip-ahead on vs off. Mirrors `DeflateDynamic.deflateRaw` levels 6-8. -/
def prodL6 (data : ByteArray) (skipShift : Nat) : Nat :=
  let ptokens := lz77ChainLazyIterP data (chainDepth 6) 32768 (insertCap 6) (goodMatch 6) (niceLen 6) (lazyDepth 6) skipShift
  let basePrep := deflateRawBasePPrep data ptokens
  let cuts := chooseSplitsHeuristicP ptokens data.size
  let withObs : Nat × (Unit → ByteArray) :=
    if cuts.isEmpty then basePrep
    else
      let obsPrep := deflateDynamicBlocksSharedAtSizedP data ptokens cuts
      if basePrep.1 < obsPrep.1 then basePrep else obsPrep
  (withObs.2 ()).size

/-- Just the matcher (`lzMatchP`-equivalent for L6) at a given `skipShift` — the
    83-84% of `deflateRaw` where 100% of the skip-ahead effect lives. -/
def matcherL6 (data : ByteArray) (skipShift : Nat) : Nat :=
  (lz77ChainLazyIterP data (chainDepth 6) 32768 (insertCap 6) (goodMatch 6) (niceLen 6) (lazyDepth 6) skipShift).size

/-- Controlled same-binary A/B: for each file, time skip-ahead OFF (63) vs the
    shipped shift (7) for both the matcher alone and the full L6 `deflateRaw` path,
    interleaved per rep (so drift cancels). The ONLY variable is `skipShift`. -/
def abMain (paths : List String) (shift : Nat) (reps : Nat) : IO Unit := do
  let mut files : List (String × ByteArray) := []
  for path in paths do
    files := files ++ [((path.splitOn "/").getLastD path, ← IO.FS.readBinFile path)]
  IO.println s!"same-binary A/B: skip OFF (shift 63) vs ON (shift {shift}); {reps} reps interleaved"
  let time (f : ByteArray → Nat) (d : ByteArray) : IO Float := do
    let t0 ← IO.monoNanosNow
    let mut s := 0
    for _ in [0:1] do s := s + f d
    let t1 ← IO.monoNanosNow
    return ((t1 - t0).toFloat / 1.0e6) + (s.toFloat * 0.0)
  for (name, d) in files do
    let mut mOff := #[]; let mut mOn := #[]; let mut pOff := #[]; let mut pOn := #[]
    for _ in [0:reps] do
      -- interleave off/on each rep so slow drift cancels
      mOff := mOff.push (← time (matcherL6 · 63) d)
      mOn  := mOn.push  (← time (matcherL6 · shift) d)
      pOff := pOff.push (← time (prodL6 · 63) d)
      pOn  := pOn.push  (← time (prodL6 · shift) d)
    let med (a : Array Float) : Float := (a.qsort (· < ·))[a.size / 2]!
    let mo := med mOff; let mn := med mOn; let po := med pOff; let pn := med pOn
    IO.println s!"{name}: matcher off={mo}ms on={mn}ms → {(mo/mn - 1.0)*100.0}% | prodL6 off={po}ms on={pn}ms → {(po/pn - 1.0)*100.0}%"
    (← IO.getStdout).flush

def main (args : List String) : IO Unit := do
  if args.head? == some "--ab" then
    abMain (args.tail.drop 1) ((args.tail.head?.bind (·.toNat?)).getD 7) 7
    return
  if args.head? == some "--time" then
    timeMain args.tail
    return
  IO.println "file,config,inBytes,outBytes,ratio"
  for path in args do
    let data ← IO.FS.readBinFile path
    let name := (path.splitOn "/").getLastD path
    for cfg in sweepConfigs do
      let out := runSkip cfg data
      let ratio := data.size.toFloat / out.toFloat
      IO.println s!"{name},{cfg.label},{data.size},{out},{ratio}"
      (← IO.getStdout).flush
