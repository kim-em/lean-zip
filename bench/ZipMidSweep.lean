import Zip

/-! # mid-sweep — mid-band (L4–L8) ladder knob sweep (#2737)

Grids the mid-band compression knobs over corpus files and prints one CSV row
per configuration, for choosing the L4–L8 ladder that unions the old
single-block frontier with the observation-divergence split frontier:

    <file>,<chain>,<goodMatch>,<minBlock>,<checkTokens>,<inBytes>,<base>,<obs>,<obsCad>,<cuts>

* `chain` × `goodMatch` — the lazy matcher's depth and lazy-gate knobs
  (`chainDepth` / `goodMatch` ladder values); one matcher pass per pair,
  shared by all candidates below.
* `base`   — the single-block cost-model dispatch (`deflateRawBaseP`) size:
  the old L4–L7 behaviour at this matcher setting.
* `obs`    — `min(base, observation-divergence split)` at the given
  `minBlock`/`checkTokens` heuristic constants (soft max fixed at
  `splitSoftMaxBlockBytes`): the new split-tier behaviour.
* `obsCad` — `min(obs, fixed-cadence split)`: the L8 (max split tier)
  behaviour with the sao-guard cadence candidate.
* `cuts`   — number of divergence cuts the heuristic proposed.

Ratios are deterministic, so this needs no pinning or quiet machine; speed
verdicts for the chosen ladder come from paired interleaved `bench-report`
runs (see the #2745 PR discussion).

Usage: lake exe mid-sweep <file> [<file> ...]
       lake exe mid-sweep --time <file> [<file> ...]

`--time` runs the ladder-candidate configurations (see `timedConfigs`) over the
files round-robin (config-interleaved so ambient machine drift cancels across
configs, reps interleaved likewise) and prints per-config corpus MB/s per rep.
Pin it (`bench/pin_core.sh`) and run on a quiet machine.
-/

open Zip.Native.Deflate

/-- Matcher chain depths bracketing the old L4–L8 ladder values. -/
def chainGrid : List Nat := [48, 64, 128, 256, 512]

/-- Lazy `good_match` gate: 8 (old L4–L6 gating) or 259 (disabled, old L7+). -/
def gmGrid : List Nat := [8, 259]

/-- `(minBlockBytes, checkTokens)` variants for the divergence heuristic
    (soft max fixed): the #2527 default (10000, 512), libdeflate's floor
    (5000), a coarser floor, and a finer check cadence. -/
def splitVariants : List (Nat × Nat) := [(10000, 512), (5000, 512), (20000, 512), (10000, 256)]

/-- One mid-band candidate: matcher knobs plus which candidates to emit.
    `mode`: 0 = single-block base only, 1 = base + obs split,
    2 = base + obs split + fixed-cadence split. -/
structure TimedConfig where
  label : String
  chain : Nat
  gm : Nat
  nl : Nat
  mode : Nat

/-- The ladder candidates whose speed decides the L4–L8 assignment. The
    knob-selection round ran chain × gm at `nl = 258` (no early-out); the
    `niceLen` round (post-#2744 rebase) grids the early-out cutoff for each
    chosen ladder slot's config. -/
def timedConfigs : List TimedConfig := [
  ⟨"L4:base-64-8-nl30",       64, 8,   30,  0⟩,
  ⟨"L4:base-64-8-nl65",       64, 8,   65,  0⟩,
  ⟨"L4:base-64-8-nl130",      64, 8,   130, 0⟩,
  ⟨"L4:base-64-8-nl258",      64, 8,   258, 0⟩,
  ⟨"L5:base-128-259-nl30",   128, 259, 30,  0⟩,
  ⟨"L5:base-128-259-nl65",   128, 259, 65,  0⟩,
  ⟨"L5:base-128-259-nl130",  128, 259, 130, 0⟩,
  ⟨"L5:base-128-259-nl258",  128, 259, 258, 0⟩,
  ⟨"L6:split-64-259-nl30",    64, 259, 30,  1⟩,
  ⟨"L6:split-64-259-nl65",    64, 259, 65,  1⟩,
  ⟨"L6:split-64-259-nl258",   64, 259, 258, 1⟩,
  ⟨"L7:split-256-259-nl65",  256, 259, 65,  1⟩,
  ⟨"L7:split-256-259-nl130", 256, 259, 130, 1⟩,
  ⟨"L7:split-256-259-nl258", 256, 259, 258, 1⟩,
  ⟨"L8:splitcad-512-259-nl130", 512, 259, 130, 2⟩,
  ⟨"L8:splitcad-512-259-nl258", 512, 259, 258, 2⟩ ]

/-- Compress `data` under one candidate config, returning the emitted size
    (consumed so the work is not dead-code-eliminated). -/
def runConfig (cfg : TimedConfig) (data : ByteArray) : Nat :=
  -- Half-depth lazy lookahead probe (#2763): the `pos+1` walk runs at `chain / 2`,
  -- matching production `DeflateDynamic.lazyDepth`, so timings model the shipped path.
  let ptoks := lz77ChainLazyIterP data cfg.chain 32768 1000000000 cfg.gm cfg.nl (cfg.chain / 2)
  let base := deflateRawBaseP data ptoks
  if cfg.mode == 0 then base.size
  else
    let cuts := chooseSplitsHeuristicP ptoks data.size
    let obs := if cuts.isEmpty then base
      else pickSmaller base (deflateDynamicBlocksSharedAtP data ptoks cuts)
    if cfg.mode == 1 then obs.size
    else
      let cad := fixedCadenceCuts sharedTokChunk ptoks.size
      if cad.isEmpty then obs.size
      else (pickSmaller obs (deflateDynamicBlocksSharedAtP data ptoks cad)).size

def timeMain (paths : List String) : IO Unit := do
  let mut files : List ByteArray := []
  for path in paths do
    files := files ++ [← IO.FS.readBinFile path]
  let total := files.foldl (fun a f => a + f.size) 0
  IO.println s!"corpus: {paths.length} files, {total} bytes"
  for rep in [0:3] do
    for cfg in timedConfigs do
      let t0 ← IO.monoNanosNow
      let mut sink := 0
      for f in files do
        sink := sink + runConfig cfg f
      let t1 ← IO.monoNanosNow
      let mbps := total.toFloat / 1048576.0 / ((t1 - t0).toFloat / 1.0e9)
      IO.println s!"rep {rep} {cfg.label}: {mbps} MB/s (out {sink})"
      (← IO.getStdout).flush

def main (args : List String) : IO Unit := do
  if args.head? == some "--time" then
    timeMain args.tail
    return
  for path in args do
    let data ← IO.FS.readBinFile path
    let name := (path.splitOn "/").getLastD path
    for chain in chainGrid do
      for gm in gmGrid do
        let ptoks := lz77ChainLazyIterP data chain 32768 1000000000 gm 258 (chain / 2)
        let base := (deflateRawBaseP data ptoks).size
        let cad := fixedCadenceCuts sharedTokChunk ptoks.size
        let cadSize := if cad.isEmpty then base
          else min base (deflateDynamicBlocksSharedAtP data ptoks cad).size
        for (minB, chk) in splitVariants do
          let cuts := chooseSplitsHeuristicP ptoks data.size minB splitSoftMaxBlockBytes chk
          let obs := if cuts.isEmpty then base
            else min base (deflateDynamicBlocksSharedAtP data ptoks cuts).size
          let obsCad := min obs cadSize
          IO.println s!"{name},{chain},{gm},{minB},{chk},{data.size},{base},{obs},{obsCad},{cuts.length}"
      (← IO.getStderr).putStr "."
  IO.eprintln " done"
