import Zip

/-! # singleton-sweep — hash3 length-3 singleton probe at the split tier (L6–L8)

Measurement-only spike quantifying the ratio prize of libdeflate's length-3
`hash3` singleton probe on the barely-compressible Silesia binaries, weighted
over the full corpus. Our production lazy matcher walks hash4-keyed chains
only, so length-3 matches are invisible at L1–L8; on `x-ray`/`sao`/`ooffice`
this is our entire weighted-ratio deficit to miniz_oxide L6.

The machinery (`hash3Single` / `hash3Probe`, with the `TOO_FAR=4096`
seed-distance cap) already ships on master — it is used today only by the
L9/L10 cache build. A full lazy-tier singleton was built and rejected once
(#2742 / PR #2759) on an *unweighted*-geomean framing; the implementation
survives at commit `d4e86ca9`. This spike re-measures it under the
corpus-*weighted* ratio the shipped comparison now uses.

## What this reimplements

`singletonMergedLoop` is a `partial def` copy of the production merged lazy
loop `lz77LazyMergedLoop` (Zip/Native/Deflate.lean), with the proof arguments
dropped and the chain state extended by a 32768-entry `h3tab` (layout: prev
ring `[0, prevSize)`, hash4 table `[prevSize, prevSize+hashSize)`, `h3tab`
`[prevSize+hashSize, prevSize+hashSize+32768)`, all initialised to the same
`data.size` sentinel). With `useSingleton := false` it is a faithful mirror of
production — the `mirror` rows below must reproduce the shipped bytes exactly
(certification: a divergent mirror invalidates every delta).

With `useSingleton := true`, at each match-search position it reads
`cand3 := h3tab[hash3Single data pos]` *before* the chain walk, verifies with
`hash3Probe data (min windowSize tooFar) pos cand3` (returns `cand3*512+3` on a
verified in-window length-3 match, else 0), and **seeds** the chain walk with
that packed `(bestLen=3, bestPos=cand3)` — the walk only improves on it. When
the walk returns length 3, a length-3 reference is emitted. The h3tab is also
updated at every interior insertion (à la `updateHashesMerged`).

The historical d4e86ca9 policy deliberately did **not** seed the `pos+1`
lookahead walk (a deferral needs `matchLen2 > matchLen ≥ 3`, so a length-3
seed at `pos+1` can never change the deferral decision — it is output-neutral).
This spike seeds `pos+1` too (per the task), which is a proven no-op for the
emitted bytes and costs only a marginal extra hash3 probe per lazy position;
the `--time` numbers therefore slightly *over*-charge the singleton's speed
cost relative to a landed version.

## Output

Ratio mode:  `<file>,<label>,<inBytes>,<outBytes>`, one row per (file, cfg).
`--time` mode: 3 reps, configs interleaved round-robin over the files, printing
per-config corpus MB/s. Pin it (`bench/pin_core.sh`) on a quiet machine.

The copied loop is a `guardedSet`-based `partial def`, so it runs somewhat
slower than the production proven-bounds path would — read the `--time` deltas
as *h3-on vs h3-off within this same copy*, not as an absolute throughput.

Usage: lake -d bench exe singleton-sweep [--time] <file> [<file> ...]
-/

open Zip.Native.Deflate

namespace ZipSingletonSweep

/-- Combined-array interior-hash insertion, extended with the hash3 singleton.
    Mirrors `updateHashesMerged` (hash4 bucket + prev ring, single array), and
    when `useSingleton` additionally writes `h3tab[hash3Single (pos+j)] = pos+j`.
    With `useSingleton := false` this is byte-for-byte `updateHashesMerged`
    (the `h3base` region is never touched), so the mirror stays exact. -/
partial def updateHashesMergedSingle (useSingleton : Bool) (data : ByteArray)
    (hashSize prevSize h3base : Nat) (c : Array Nat) (pos j matchLen insertCap : Nat) :
    Array Nat :=
  if j < matchLen ∧ j ≤ insertCap then
    if h : pos + j + 2 < data.size then
      let hsh := lz77Greedy.hash3 data (pos + j) hashSize h
      let head := headProbeGuarded c (prevSize + hsh)
      let c := guardedSet (guardedSet c (prevSize + hsh) (pos + j)) ((pos + j) &&& 0x7FFF) head
      let c := if useSingleton then guardedSet c (h3base + hash3Single data (pos + j) h) (pos + j) else c
      updateHashesMergedSingle useSingleton data hashSize prevSize h3base c pos (j + 1) matchLen insertCap
    else
      updateHashesMergedSingle useSingleton data hashSize prevSize h3base c pos (j + 1) matchLen insertCap
  else c

/-- `partial` copy of the production merged lazy loop `lz77LazyMergedLoop`,
    extended with the hash3 singleton (gated on `useSingleton`) and the probe
    window cap `tooFar` (`min windowSize tooFar`). With `useSingleton := false`
    every singleton read/write vanishes and the chain walks are seeded `(0,0)`,
    so the emitted token stream is identical to `lz77LazyMergedLoop`. -/
partial def singletonMergedLoop (useSingleton : Bool) (tooFar : Nat) (data : ByteArray)
    (windowSize hashSize prevSize h3base maxChain insertCap goodMatch niceLen lazyDepth : Nat)
    (c : Array Nat) (pos : Nat) (acc : Array UInt32) : Array UInt32 :=
  if hlt : pos + 2 < data.size then
    let h := lz77Greedy.hash3 data pos hashSize hlt
    let head := headProbeGuarded c (prevSize + h)
    let c := guardedSet c (prevSize + h) pos
    let c := guardedSet c (pos &&& 0x7FFF) head
    -- hash3 singleton: read the length-3 candidate, refresh the bucket, build the seed.
    let (c, seed) :=
      if useSingleton then
        let cand3 := headProbeGuarded c (h3base + hash3Single data pos hlt)
        let c := guardedSet c (h3base + hash3Single data pos hlt) pos
        (c, hash3Probe data (min windowSize tooFar) pos cand3 hlt)
      else (c, 0)
    let maxLen := min 258 (data.size - pos)
    have hmaxLenP : pos + maxLen ≤ data.size := by omega
    let r := chainWalkGuardedPackedU data c windowSize pos maxLen niceLen hmaxLenP head maxChain (seed % 512) (seed / 512)
    let matchLen := r % 512
    let matchPos := r / 512
    if hge : matchLen ≥ 3 then
      if hle : pos + matchLen ≤ data.size then
        if h3lt : pos + 3 < data.size then
          if matchLen < goodMatch then
            let h2 := lz77Greedy.hash3 data (pos + 1) hashSize (by omega)
            let head2 := headProbeGuarded c (prevSize + h2)
            -- Seed the pos+1 walk too (output-neutral; see the module note).
            let seed2 :=
              if useSingleton then
                let cand3b := headProbeGuarded c (h3base + hash3Single data (pos + 1) (by omega))
                hash3Probe data (min windowSize tooFar) (pos + 1) cand3b (by omega)
              else 0
            let maxLen2 := min 258 (data.size - (pos + 1))
            have hmaxLen2P : (pos + 1) + maxLen2 ≤ data.size := by omega
            let r2 :=
              chainWalkGuardedPackedU data c windowSize (pos + 1) maxLen2 niceLen hmaxLen2P head2 lazyDepth (seed2 % 512) (seed2 / 512)
            let matchLen2 := r2 % 512
            let matchPos2 := r2 / 512
            if lazyAcceptCost matchLen (pos - matchPos) matchLen2 (pos + 1 - matchPos2) then
              if pos + 1 + matchLen2 ≤ data.size then
                let c := updateHashesMergedSingle useSingleton data hashSize prevSize h3base c pos 1 (matchLen2 + 1) insertCap
                singletonMergedLoop useSingleton tooFar data windowSize hashSize prevSize h3base maxChain insertCap goodMatch niceLen lazyDepth c (pos + 1 + matchLen2)
                  (acc.push (packTok (.literal (data[pos]'(by omega)))) |>.push
                    (packTok (.reference matchLen2 (pos + 1 - matchPos2))))
              else
                let c := updateHashesMergedSingle useSingleton data hashSize prevSize h3base c pos 1 matchLen insertCap
                singletonMergedLoop useSingleton tooFar data windowSize hashSize prevSize h3base maxChain insertCap goodMatch niceLen lazyDepth c (pos + matchLen)
                  (acc.push (packTok (.reference matchLen (pos - matchPos))))
            else
              let c := updateHashesMergedSingle useSingleton data hashSize prevSize h3base c pos 1 matchLen insertCap
              singletonMergedLoop useSingleton tooFar data windowSize hashSize prevSize h3base maxChain insertCap goodMatch niceLen lazyDepth c (pos + matchLen)
                (acc.push (packTok (.reference matchLen (pos - matchPos))))
          else
            let c := updateHashesMergedSingle useSingleton data hashSize prevSize h3base c pos 1 matchLen insertCap
            singletonMergedLoop useSingleton tooFar data windowSize hashSize prevSize h3base maxChain insertCap goodMatch niceLen lazyDepth c (pos + matchLen)
              (acc.push (packTok (.reference matchLen (pos - matchPos))))
        else
          singletonMergedLoop useSingleton tooFar data windowSize hashSize prevSize h3base maxChain insertCap goodMatch niceLen lazyDepth c (pos + matchLen)
            (acc.push (packTok (.reference matchLen (pos - matchPos))))
      else
        singletonMergedLoop useSingleton tooFar data windowSize hashSize prevSize h3base maxChain insertCap goodMatch niceLen lazyDepth c (pos + 1)
          (acc.push (packTok (.literal (data[pos]'(by omega)))))
    else
      singletonMergedLoop useSingleton tooFar data windowSize hashSize prevSize h3base maxChain insertCap goodMatch niceLen lazyDepth c (pos + 1)
        (acc.push (packTok (.literal (data[pos]'(by omega)))))
  else
    trailingP data pos acc

/-- Run the (possibly singleton-augmented) matcher over `data`, returning the
    packed token stream. `hashSize = 65536`, `prevSize = min chainWinSize
    data.size`, `h3base = prevSize + hashSize`; the combined array carries the
    extra 32768 `h3tab` entries even when `useSingleton := false` (unused there,
    so the mirror stays byte-identical to the production array). -/
def runMatcher (useSingleton : Bool) (tooFar : Nat) (data : ByteArray)
    (maxChain windowSize insertCap goodMatch niceLen lazyDepth : Nat) : Array UInt32 :=
  if data.size < 3 then
    trailingP data 0 (Array.emptyWithCapacity data.size)
  else
    let hashSize := 65536
    let prevSize := min chainWinSize data.size
    let h3base := prevSize + hashSize
    singletonMergedLoop useSingleton tooFar data windowSize hashSize prevSize h3base maxChain insertCap goodMatch niceLen lazyDepth
      (.replicate (prevSize + hashSize + 32768) data.size) 0
      (Array.emptyWithCapacity data.size)

structure Cfg where
  label : String
  /-- `none` ⇒ production reference row (`lz77ChainLazyIterPMerged`), no copy. -/
  useSingleton : Option Bool
  tooFar : Nat
  chain : Nat
  gm : Nat
  nl : Nat
  lazyD : Nat

/-- L6/L7/L8 production knobs (from `DeflateDynamic.chainDepth`/`goodMatch`/
    `niceLen`/`lazyDepth`; `insertCap = 1e9`, `windowSize = 32768`, gate off):
    L6 = chain 64, nl 65, ld 32; L7 = chain 256, nl 130, ld 128;
    L8 = chain 512, nl 258, ld 256. `tooFar` only matters when the singleton
    is on. -/
def cfgs : List Cfg := [
  -- L6: prod reference, mirror (certification), singleton, and TOO_FAR variants.
  ⟨"prod-L6",       none,            4096,  64, 259,  65,  32⟩,
  ⟨"mirror-L6",     some false,      4096,  64, 259,  65,  32⟩,
  ⟨"h3-L6",         some true,       4096,  64, 259,  65,  32⟩,
  ⟨"h3-L6-tf2048",  some true,       2048,  64, 259,  65,  32⟩,
  ⟨"h3-L6-tffull",  some true,      32768,  64, 259,  65,  32⟩,
  -- L7
  ⟨"prod-L7",       none,            4096, 256, 259, 130, 128⟩,
  ⟨"mirror-L7",     some false,      4096, 256, 259, 130, 128⟩,
  ⟨"h3-L7",         some true,       4096, 256, 259, 130, 128⟩,
  -- L8
  ⟨"prod-L8",       none,            4096, 512, 259, 258, 256⟩,
  ⟨"mirror-L8",     some false,      4096, 512, 259, 258, 256⟩,
  ⟨"h3-L8",         some true,       4096, 512, 259, 258, 256⟩ ]

/-- The packed token stream for one config: `none` ⇒ the production merged
    matcher; `some useSingleton` ⇒ the copied loop. -/
def tokensFor (cfg : Cfg) (data : ByteArray) : Array UInt32 :=
  match cfg.useSingleton with
  | none => lz77ChainLazyIterPMerged data cfg.chain 32768 1000000000 cfg.gm cfg.nl cfg.lazyD
  | some us => runMatcher us cfg.tooFar data cfg.chain 32768 1000000000 cfg.gm cfg.nl cfg.lazyD

/-- One config through the *exact* production split-tier dispatch (the L6–L8 arm
    of `deflateRaw`: sized preps, obs-split arbitration, winner emitted), copied
    from `ZipGateSweep.runCfg`, so `out` is byte-for-byte the shipped encoder's. -/
def runCfg (cfg : Cfg) (data : ByteArray) : Nat :=
  let ptokens := tokensFor cfg data
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

end ZipSingletonSweep

def main (args : List String) : IO Unit := do
  if args.head? == some "--time" then
    ZipSingletonSweep.timeMain args.tail
  else
    ZipSingletonSweep.ratioMain args
