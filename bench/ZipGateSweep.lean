import Zip

/-! # gate-sweep — intermediate lazy-gate (`goodMatch`) + probe-depth sweep at the split tier

The #2737 `mid-sweep` grid only ever tried `goodMatch ∈ {8, 259}` (full gating
vs. disabled). This sweep probes the *intermediate* gate values at the L6 split
config: with the gate at `g`, a first match of length ≥ `g` skips the lazy
`pos+1` lookahead walk entirely — on match-rich files that deletes a large
fraction of the second chain walks for a ratio cost that shrinks as `g` grows.
Also grids the lazy probe depth (`lazyDepth`, production `chain/2`; #2781
suggests `/4`) and deeper chains re-paired with a gate.

Ratio rows go through the *exact* production L6–L8 dispatch (sized prep,
base-vs-obs-split arbitration — the same code `deflateRaw` runs), so `out`
is byte-for-byte what the shipped encoder would emit at that config.

    <file>,<label>,<inBytes>,<outBytes>

`--time` interleaves configs round-robin over the files (3 reps) and prints
per-config corpus MB/s. Pin it (`bench/pin_core.sh`) on a quiet machine.

Usage: lake -d bench exe gate-sweep [--time] <file> [<file> ...]
-/

open Zip.Native.Deflate

namespace ZipGateSweep

structure Cfg where
  label : String
  chain : Nat
  gm : Nat
  nl : Nat
  lazyD : Nat
  h3 : Bool := false

/-- The grid: production L6 first (the certification row — must reproduce the
    shipped L6 bytes), then gate values, probe depths, and deeper chains. -/
def cfgs : List Cfg := [
  ⟨"h3-prod-c64-gm259-ld32",  64, 259, 65, 32, true⟩,
  ⟨"noh3-c64-gm259-ld32",     64, 259, 65, 32, false⟩,
  ⟨"h3-ld16",                 64, 259, 65, 16, true⟩,
  ⟨"h3-gm64",                 64,  64, 65, 32, true⟩,
  ⟨"h3-gm64-ld16",            64,  64, 65, 16, true⟩,
  ⟨"h3-gm32-ld16",            64,  32, 65, 16, true⟩,
  ⟨"h3-c48-gm259-ld24",       48, 259, 65, 24, true⟩,
  ⟨"h3-c48-gm64-ld16",        48,  64, 65, 16, true⟩,
  ⟨"h3-c96-gm259-ld48",       96, 259, 65, 48, true⟩,
  ⟨"h3-ld8",                  64, 259, 65,  8, true⟩,
  ⟨"h3-gm64-ld8",             64,  64, 65,  8, true⟩ ]

/-- One config through the exact production split-tier dispatch (the L6–L7
    arm of `deflateRaw`: sized preps, obs-split arbitration, winner emitted). -/
def runCfg (cfg : Cfg) (data : ByteArray) : Nat :=
  let ptokens := lz77ChainLazyIterPMerged data cfg.chain 32768 1000000000 cfg.gm cfg.nl cfg.lazyD cfg.h3
  let cuts := chooseSplitsHeuristicP ptokens data.size
  let withObs : Nat × (Unit → ByteArray) :=
    if cuts.isEmpty then deflateRawBasePPrep data ptokens
    else
      let obsFreqs := deflateObsSplitSizedFreqsP data ptokens cuts
      let basePrep := deflateRawBasePPrepF data ptokens obsFreqs.2
      if basePrep.1 < obsFreqs.1.1 then basePrep else obsFreqs.1
  (withObs.2 ()).size

def timeMain (paths : List String) : IO Unit := do
  let mut files : List ByteArray := []
  for path in paths do
    files := files ++ [← IO.FS.readBinFile path]
  let total := files.foldl (fun a f => a + f.size) 0
  IO.println s!"corpus: {paths.length} files, {total} bytes"
  for rep in [0:3] do
    for cfg in cfgs do
      let t0 ← IO.monoNanosNow
      let mut sink := 0
      for f in files do
        sink := sink + runCfg cfg f
      let t1 ← IO.monoNanosNow
      let mbps := total.toFloat / 1048576.0 / ((t1 - t0).toFloat / 1.0e9)
      IO.println s!"rep {rep} {cfg.label}: {mbps} MB/s (out {sink})"
      (← IO.getStdout).flush

def ratioMain (paths : List String) : IO Unit := do
  for path in paths do
    let data ← IO.FS.readBinFile path
    let name := (path.splitOn "/").getLastD path
    for cfg in cfgs do
      IO.println s!"{name},{cfg.label},{data.size},{runCfg cfg data}"
      (← IO.getStdout).flush
    (← IO.getStderr).putStr "."
  IO.eprintln " done"

end ZipGateSweep

def main (args : List String) : IO Unit := do
  if args.head? == some "--time" then
    ZipGateSweep.timeMain args.tail
  else
    ZipGateSweep.ratioMain args
