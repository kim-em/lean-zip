import Zip

/-! # l68-sweep — re-grid the L6–L8 ladder (#2785)

Re-baselines the L6–L8 tuning ladder after the Huffman-build (#2769),
cost-based lazy-accept (#2776), half-depth-probe (#2774), and fused-split-pass
(#2762) landings shifted the per-file cost balance. Zero-proof-risk: every knob
here is a search/emit heuristic re-verified at emission, so any value keeps the
encoder contracts.

The matcher pass models production exactly: `lz77ChainLazyIterPMerged` with
`lazyDepth = chain / 2` (the shipped `DeflateDynamic.lazyDepth`), and the
per-level size is the base-vs-observation-divergence-split arbitration
`deflateRaw` runs for levels 6–8 (`min(base, obs-split)`; no fixed-cadence
candidate on that path). At the current ladder knobs the emitted size matches
`(deflateRaw data level).size` for level ∈ {6,7,8}, cross-checked by
`--verify`.

Two ratio grids (deterministic — no pinning needed):

* **matcher** — `chain × goodMatch × niceLen` at the default split constants,
  one CSV row per config:

      M,<file>,<chain>,<gm>,<nl>,<inBytes>,<base>,<obs>,<cuts>

  Answers the chain L6/L5 inversion, the L8 `niceLen` cutoff (130/180/258),
  and the L5+ `goodMatch` gate.

* **split** — `minBlockBytes × softMaxBlockBytes × checkTokens` at each level's
  current matcher config, one CSV row per config:

      S,<file>,<level>,<minB>,<softMax>,<chk>,<inBytes>,<base>,<obs>,<cuts>

Speed verdicts for the finalists come from `--time` (config-interleaved reps,
corpus MB/s per rep) — pin the core (`bench/pin_core.sh`) on a quiet machine.

Usage: lake exe l68-sweep [--verify] <file> [<file> ...]
       lake exe l68-sweep --time <file> [<file> ...]
-/

open Zip.Native.Deflate

/-- Matcher chain depths bracketing the L6–L8 ladder (L6=64, L7=256, L8=512),
    plus L5=128 to re-check the L6<L5 inversion. -/
def chainGrid : List Nat := [64, 128, 256, 512]

/-- Lazy `good_match` gate: 8 (gating on) or 259 (disabled). -/
def gmGrid : List Nat := [8, 259]

/-- `niceLen` early-out cutoff: the issue's 130/180/258 for L8, plus 65 (the
    current L6 knee) to keep the whole ladder in one grid. -/
def nlGrid : List Nat := [65, 130, 180, 258]

/-- Block-split floor-on-output-bytes candidates (current `splitMinBlockBytes`
    = 10000). -/
def minBGrid : List Nat := [5000, 10000, 20000]

/-- Soft-max block-bytes ceiling candidates (current `splitSoftMaxBlockBytes`
    = 300000). -/
def softMaxGrid : List Nat := [150000, 300000, 600000]

/-- Divergence-check cadence in tokens (current `splitCheckTokens` = 512). -/
def chkGrid : List Nat := [256, 512, 1024]

/-- Production matcher pass for the given knobs (mirrors `lzMatchP` at level ≥ 4:
    merged-array lazy chain, insert-cap off, half-depth lookahead probe). -/
def matchP (data : ByteArray) (chain gm nl : Nat) : Array UInt32 :=
  lz77ChainLazyIterPMerged data chain 32768 1000000000 gm nl (chain / 2)

/-- The base single-block size and the base-vs-obs-split arbitrated size at the
    given split constants — exactly `deflateRaw`'s levels 6–8 path — plus the
    number of divergence cuts the heuristic proposed. -/
def sizesAt (data : ByteArray) (ptoks : Array UInt32) (minB softMax chk : Nat) :
    Nat × Nat × Nat :=
  let base := (deflateRawBaseP data ptoks).size
  let cuts := chooseSplitsHeuristicP ptoks data.size minB softMax chk
  let obs := if cuts.isEmpty then base
    else min base (deflateDynamicBlocksSharedAtP data ptoks cuts).size
  (base, obs, cuts.length)

/-- Current per-level matcher config: `(label, chain, goodMatch, niceLen)`. -/
def levelConfigs : List (String × Nat × Nat × Nat) :=
  [("L6", 64, 259, 65), ("L7", 256, 259, 130), ("L8", 512, 259, 258)]

def ratioMain (verify : Bool) (paths : List String) : IO Unit := do
  for path in paths do
    let data ← IO.FS.readBinFile path
    let name := (path.splitOn "/").getLastD path
    -- matcher grid at default split constants
    for chain in chainGrid do
      for gm in gmGrid do
        for nl in nlGrid do
          let ptoks := matchP data chain gm nl
          let (base, obs, cuts) :=
            sizesAt data ptoks splitMinBlockBytes splitSoftMaxBlockBytes splitCheckTokens
          IO.println s!"M,{name},{chain},{gm},{nl},{data.size},{base},{obs},{cuts}"
      (← IO.getStderr).putStr "."
    -- split grid at each level's current matcher config
    for (lbl, chain, gm, nl) in levelConfigs do
      let ptoks := matchP data chain gm nl
      for minB in minBGrid do
        for softMax in softMaxGrid do
          for chk in chkGrid do
            let (base, obs, cuts) := sizesAt data ptoks minB softMax chk
            IO.println s!"S,{name},{lbl},{minB},{softMax},{chk},{data.size},{base},{obs},{cuts}"
      (← IO.getStderr).putStr "+"
    -- cross-check the default-knob per-level size against real deflateRaw
    if verify then
      for (lbl, lvl) in [("L6", (6 : UInt8)), ("L7", 7), ("L8", 8)] do
        let ptoks := matchP data (chainDepth lvl) (goodMatch lvl) (niceLen lvl)
        let (_, obs, _) :=
          sizesAt data ptoks splitMinBlockBytes splitSoftMaxBlockBytes splitCheckTokens
        let real := (deflateRaw data lvl).size
        unless obs == real do
          throw (IO.userError s!"{name} {lbl}: sweep {obs} ≠ deflateRaw {real}")
      (← IO.getStderr).putStr "✓"
    (← IO.getStderr).putStr "\n"

/-- One timed candidate: a per-level ladder slot's matcher + split knobs. -/
structure TimedConfig where
  label : String
  chain : Nat
  gm : Nat
  nl : Nat
  minB : Nat
  softMax : Nat
  chk : Nat

/-- The finalists whose speed decides adoption. The ratio grids settled the
    ratio side (chain 128 ≥ 64 everywhere; `niceLen`/`gm` cutoffs only ever cost
    ratio; `minB` 5000 helps binary); these configs price the speed of each
    ratio-relevant move so a change is adopted only when the speed pays. -/
def timedConfigs : List TimedConfig := [
  ⟨"L6:cur-64-259-nl65-mb10k",   64,  259, 65,  10000, 300000, 512⟩,
  ⟨"L6:alt-128-259-nl65-mb10k",  128, 259, 65,  10000, 300000, 512⟩,
  ⟨"L6:alt-128-259-nl65-mb5k",   128, 259, 65,  5000,  300000, 512⟩,
  ⟨"L7:cur-256-259-nl130-mb10k", 256, 259, 130, 10000, 300000, 512⟩,
  ⟨"L7:alt-256-259-nl130-mb5k",  256, 259, 130, 5000,  300000, 512⟩,
  ⟨"L8:cur-512-259-nl258-mb10k", 512, 259, 258, 10000, 300000, 512⟩,
  ⟨"L8:alt-512-259-nl130-mb10k", 512, 259, 130, 10000, 300000, 512⟩,
  ⟨"L8:alt-512-259-nl180-mb10k", 512, 259, 180, 10000, 300000, 512⟩,
  ⟨"L8:alt-512-259-nl258-mb5k",  512, 259, 258, 5000,  300000, 512⟩,
  ⟨"L8:alt-512-8-nl258-mb10k",   512, 8,   258, 10000, 300000, 512⟩ ]

/-- Compress `data` under a timed config, returning the emitted size (consumed
    so the matcher/emit work is not dead-code-eliminated). -/
def runTimed (cfg : TimedConfig) (data : ByteArray) : Nat :=
  let ptoks := matchP data cfg.chain cfg.gm cfg.nl
  let (_, obs, _) := sizesAt data ptoks cfg.minB cfg.softMax cfg.chk
  obs

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
        sink := sink + runTimed cfg f
      let t1 ← IO.monoNanosNow
      let mbps := total.toFloat / 1048576.0 / ((t1 - t0).toFloat / 1.0e9)
      IO.println s!"rep {rep} {cfg.label}: {mbps} MB/s (out {sink})"
      (← IO.getStdout).flush

def main (args : List String) : IO Unit := do
  if args.head? == some "--time" then
    timeMain args.tail
  else
    ratioMain (args.contains "--verify") (args.filter (· ≠ "--verify"))
