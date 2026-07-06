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

def main (args : List String) : IO Unit := do
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
