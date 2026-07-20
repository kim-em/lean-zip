import Zip

/-! # gate-sweep — lazy-gate/probe-depth sweep, now regridding the L5 slot

Originally the intermediate `goodMatch` sweep at the L6 split config (#2781/
#2824 grid history preserved in git). This revision points the same harness at
the **L5 slot**: the committed dashboard has L5 (single-block, chain 128, gate
off, probe /2, no singleton) 15.6% *inside* the L4↔L6 mixing line — it predates
the hash3-singleton (#2824), gm/ld re-grid (#2825), and greedy re-grid (#2830)
landings. The grid pits cheaper single-block points against shallow split-tier
points (with and without the hash3 singleton) for the L5 ratio band.

Each `Cfg` now carries a `split` flag: `split = true` rows go through the
*exact* production L6–L8 dispatch (sized prep, base-vs-obs-split arbitration —
the same code `deflateRaw` runs at the split tier); `split = false` rows go through the
production single-block base path (`deflateRawBasePPrep`, forced — exactly
`deflateRawBaseP`, the L4–L5 dispatch), so `out` is byte-for-byte what the
shipped encoder would emit at that config. The grid includes the pre-re-grid
production L4, L5, and L6 knob rows as anchors: the old L5 was the
certification row (byte-identical to `deflateRaw · 5` on pre-re-grid master,
checked per-file against the extra `prod-deflateRaw-l5` ratio row), and L4/L6
let the mixing line be computed in this harness's own units.

Verdict (landed as the L5 re-grid): `split-noh3-c24-gm64-ld6` — every deeper
single-block point stayed 3-4% inside the L4↔L6 blend, every split point
cleared it, and c24/gm64/ld6 peaked at +4% with the old L5's speed at −0.53pp
weighted ratio. Since that landing, `prod-deflateRaw-l5` matches the
`split-noh3-c24-gm64-ld6` row (production L5) rather than `prod-l5-single-*`.

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
  split : Bool := true
  lazy2 : Nat := 1

/-- The grid: the production L5 row first (the certification row — single-block,
    must reproduce the shipped L5 bytes), the production L4/L6 rows as mixing-line
    anchors, then the L5-slot candidates: cheaper single-block points, shallow
    split points without the singleton, and shallow split points with it. -/
def cfgs : List Cfg := [
  -- L6 slot re-grid (#2837 rolling deferral at L6): all cells run the exact
  -- production L6 split config (split-h3, chain 64, gm 64, nl 65), varying the
  -- lazy probe depth × rolling lazy2 cap. `l6-ld18-s1` is the certification
  -- row: it must reproduce the shipped L6 bytes (`prod-deflateRaw-l6`).
  ⟨"l6-ld8-s1",   64, 64, 65,  8, true, true, 1⟩,
  ⟨"l6-ld8-s2",   64, 64, 65,  8, true, true, 2⟩,
  ⟨"l6-ld8-s4",   64, 64, 65,  8, true, true, 4⟩,
  ⟨"l6-ld10-s1",  64, 64, 65, 10, true, true, 1⟩,
  ⟨"l6-ld10-s2",  64, 64, 65, 10, true, true, 2⟩,
  ⟨"l6-ld10-s4",  64, 64, 65, 10, true, true, 4⟩,
  ⟨"l6-ld12-s1",  64, 64, 65, 12, true, true, 1⟩,
  ⟨"l6-ld12-s2",  64, 64, 65, 12, true, true, 2⟩,
  ⟨"l6-ld12-s4",  64, 64, 65, 12, true, true, 4⟩,
  ⟨"l6-ld18-s1",  64, 64, 65, 18, true, true, 1⟩,
  ⟨"l6-ld18-s2",  64, 64, 65, 18, true, true, 2⟩,
  ⟨"l6-ld18-s4",  64, 64, 65, 18, true, true, 4⟩ ]

/-- One config through the exact production dispatch for its mode: `split = true`
    is the split-tier arm of `deflateRaw` (sized preps, obs-split arbitration,
    winner emitted); `split = false` is the single-block lazy-base arm (`deflateRawBasePPrep`
    forced — definitionally `deflateRawBaseP`). -/
def runCfg (cfg : Cfg) (data : ByteArray) : Nat :=
  let ptokens := lz77ChainLazyIterPMerged data cfg.chain 32768 1000000000 cfg.gm cfg.nl cfg.lazyD cfg.h3 cfg.lazy2
  if cfg.split then
    let cuts := chooseSplitsHeuristicP ptokens data.size
    let withObs : Nat × (Unit → ByteArray) :=
      if cuts.isEmpty then deflateRawBasePPrep data ptokens
      else
        let obsFreqs := deflateObsSplitSizedFreqsP data ptokens cuts
        let basePrep := deflateRawBasePPrepF data ptokens obsFreqs.2
        if basePrep.1 < obsFreqs.1.1 then basePrep else obsFreqs.1
    (withObs.2 ()).size
  else
    ((deflateRawBasePPrep data ptokens).2 ()).size

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
    -- Certification reference: the *actual* production level-6 output (through
    -- `deflateRaw`, prescan included) — the `l6-ld18-s1` row must match it.
    IO.println s!"{name},prod-deflateRaw-l6,{data.size},{(Zip.Native.Deflate.deflateRaw data 6).size}"
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
