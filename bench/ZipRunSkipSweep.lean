import Zip

/-! # runskip-sweep — zstd-style accelerating skip through matchless runs (L6/L7)

At level 6 the barely-compressible Silesia files (x-ray, sao, ooffice) dominate
wall-clock share: the lazy matcher pays a full chain walk + hash insertion at
*every* position through long matchless stretches. zstd advances its search
cursor by an accelerating stride through such runs
(`ip += 1 + (ip - anchor) >> kSearchStrength`); zlib's `deflate_fast` has a
related trick. This spike measures the (ratio, speed) trade of that idea at our
L6/L7 configs, weighted over Silesia.

The matcher is a `partial def` copy of the production merged lazy loop
(`lz77LazyMergedLoop`, `Zip/Native/Deflate.lean`), extended with a `literalRun`
accumulator and a skip policy parameterized by `(trigger T, strength S, cap C)`
plus an `ins`/`noins` choice for whether skipped positions still hash-insert.
It uses only the public runtime-guarded helpers the production loop uses
(`chainWalkGuardedPackedU`, `updateHashesMergedGuarded`, `headProbeGuarded`,
`guardedSet`, `lz77Greedy.hash3`, `packTok`, `trailingP`), so no proven code is
touched. Sizes go through the *exact* production split-tier dispatch (the same
code `deflateRaw` runs at L6–L8), so `out` is byte-for-byte the shipped bytes.

Skip policy at a matchless position (`matchLen < 3`): emit the literal, extend
`literalRun`. Once `literalRun ≥ T`, advance by `step = min C (1 + (run - T) / S)`
instead of 1, emitting the skipped positions' literals directly (and, for `ins`,
hash-inserting them) — the chain WALK is skipped either way (the point). Any
found match (`matchLen ≥ 3`) resets `literalRun := 0`. The lazy `pos+1` probe
only runs when a match was found, so it is unaffected.

Certification: the `mirror` config (skip disabled, `T = ∞`) runs the *same*
loop and must emit byte-identically to the production `lz77ChainLazyIterPMerged`
at the same knobs (the `prod` rows). If mirror ≠ prod, the reimplementation is
untrustworthy.

    <file>,<label>,<inBytes>,<outBytes>

`--time` interleaves configs round-robin over the files (3 reps) and prints
per-config corpus MB/s. Pin it (`bench/pin_core.sh`) on a quiet machine.

Usage: lake -d bench exe runskip-sweep [--time] <file> [<file> ...]
-/

open Zip.Native.Deflate

namespace ZipRunSkipSweep

/-- Sentinel trigger meaning "skip disabled" (`literalRun` never reaches it), so
    the loop reduces to the production merged lazy loop exactly. -/
def noSkip : Nat := 1000000000000

/-- Emit literals for the skipped positions `[q, endPos)` directly onto `acc`,
    optionally hash-inserting each (variant `ins`). No chain walk runs — that is
    the whole point of the skip. `endPos ≤ data.size` (`hend`) makes each
    `data[q]` in range. Bench-only `partial`, so no termination obligation. -/
partial def emitSkipLits (data : ByteArray) (hashSize prevSize : Nat) (doIns : Bool)
    (c : Array Nat) (q endPos : Nat) (hend : endPos ≤ data.size) (acc : Array UInt32) :
    Array Nat × Array UInt32 :=
  if hq : q < endPos then
    let acc := acc.push (packTok (.literal (data[q]'(by omega))))
    let c :=
      if doIns then
        if h : q + 2 < data.size then
          let hsh := lz77Greedy.hash3 data q hashSize h
          let head := headProbeGuarded c (prevSize + hsh)
          guardedSet (guardedSet c (prevSize + hsh) q) (q &&& 0x7FFF) head
        else c
      else c
    emitSkipLits data hashSize prevSize doIns c (q + 1) endPos hend acc
  else (c, acc)

/-- Merged-array lazy loop with a zstd-style accelerating skip through matchless
    runs. A `partial def` copy of `lz77LazyMergedLoop`, extended with a
    `literalRun` accumulator and the skip policy. When `T = noSkip` this is
    byte-identical to `lz77LazyMergedLoop` (the `mirror` certification). -/
partial def runSkipLoop (data : ByteArray)
    (windowSize hashSize prevSize maxChain insertCap goodMatch niceLen lazyDepth : Nat)
    (skipT skipS skipC : Nat) (doIns : Bool)
    (c : Array Nat) (pos literalRun : Nat) (acc : Array UInt32) : Array UInt32 :=
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
      -- A usable match resets the matchless-run counter (`literalRun := 0`).
      if hle : pos + matchLen ≤ data.size then
        if h3lt : pos + 3 < data.size then
          if matchLen < goodMatch then
            let h2 := lz77Greedy.hash3 data (pos + 1) hashSize (by omega)
            let head2 := headProbeGuarded c (prevSize + h2)
            let maxLen2 := min 258 (data.size - (pos + 1))
            have hmaxLen2P : (pos + 1) + maxLen2 ≤ data.size := by omega
            let r2 :=
              chainWalkGuardedPackedU data c windowSize (pos + 1) maxLen2 niceLen hmaxLen2P head2 lazyDepth 0 0
            let matchLen2 := r2 % 512
            let matchPos2 := r2 / 512
            if lazyAcceptCost matchLen (pos - matchPos) matchLen2 (pos + 1 - matchPos2) then
              if hle2 : pos + 1 + matchLen2 ≤ data.size then
                let c := updateHashesMergedGuarded data hashSize prevSize c pos 1 (matchLen2 + 1) insertCap
                runSkipLoop data windowSize hashSize prevSize maxChain insertCap goodMatch niceLen lazyDepth
                  skipT skipS skipC doIns c (pos + 1 + matchLen2) 0
                  (acc.push (packTok (.literal (data[pos]'(by omega)))) |>.push
                    (packTok (.reference matchLen2 (pos + 1 - matchPos2))))
              else
                let c := updateHashesMergedGuarded data hashSize prevSize c pos 1 matchLen insertCap
                runSkipLoop data windowSize hashSize prevSize maxChain insertCap goodMatch niceLen lazyDepth
                  skipT skipS skipC doIns c (pos + matchLen) 0
                  (acc.push (packTok (.reference matchLen (pos - matchPos))))
            else
              let c := updateHashesMergedGuarded data hashSize prevSize c pos 1 matchLen insertCap
              runSkipLoop data windowSize hashSize prevSize maxChain insertCap goodMatch niceLen lazyDepth
                skipT skipS skipC doIns c (pos + matchLen) 0
                (acc.push (packTok (.reference matchLen (pos - matchPos))))
          else
            let c := updateHashesMergedGuarded data hashSize prevSize c pos 1 matchLen insertCap
            runSkipLoop data windowSize hashSize prevSize maxChain insertCap goodMatch niceLen lazyDepth
              skipT skipS skipC doIns c (pos + matchLen) 0
              (acc.push (packTok (.reference matchLen (pos - matchPos))))
        else
          runSkipLoop data windowSize hashSize prevSize maxChain insertCap goodMatch niceLen lazyDepth
            skipT skipS skipC doIns c (pos + matchLen) 0
            (acc.push (packTok (.reference matchLen (pos - matchPos))))
      else
        -- matchLen ≥ 3 but the match would overrun EOF: emit a literal. A match
        -- was found, so the run resets. (Degenerate near-EOF case.)
        runSkipLoop data windowSize hashSize prevSize maxChain insertCap goodMatch niceLen lazyDepth
          skipT skipS skipC doIns c (pos + 1) 0
          (acc.push (packTok (.literal (data[pos]'(by omega)))))
    else
      -- No usable match at `pos`: emit its literal and extend the matchless run.
      let acc := acc.push (packTok (.literal (data[pos]'(by omega))))
      let newRun := literalRun + 1
      if newRun < skipT then
        -- Below the trigger: ordinary one-position step (identical to production).
        runSkipLoop data windowSize hashSize prevSize maxChain insertCap goodMatch niceLen lazyDepth
          skipT skipS skipC doIns c (pos + 1) newRun acc
      else
        -- Accelerate: advance by `step`, emitting the skipped positions' literals
        -- (walk skipped; hash-inserted only for the `ins` variant).
        let step := min skipC (1 + (newRun - skipT) / skipS)
        let next := pos + step
        let endPos := min next data.size
        let (c, acc) := emitSkipLits data hashSize prevSize doIns c (pos + 1) endPos
          (Nat.min_le_right _ _) acc
        runSkipLoop data windowSize hashSize prevSize maxChain insertCap goodMatch niceLen lazyDepth
          skipT skipS skipC doIns c next (literalRun + (endPos - pos)) acc
  else
    trailingP data pos acc

/-- Entry mirroring `lz77ChainLazyIterPMerged`: builds the combined
    `prevSize + hashSize` array and runs `runSkipLoop` from `pos = 0`,
    `literalRun = 0`. With `skipT = noSkip` this is byte-identical to
    `lz77ChainLazyIterPMerged`. -/
def runSkipMatcher (data : ByteArray)
    (maxChain windowSize insertCap goodMatch niceLen lazyDepth : Nat)
    (skipT skipS skipC : Nat) (doIns : Bool) : Array UInt32 :=
  if data.size < 3 then
    trailingP data 0 #[]
  else
    let hashSize := 65536
    let prevSize := min chainWinSize data.size
    runSkipLoop data windowSize hashSize prevSize maxChain insertCap goodMatch niceLen lazyDepth
      skipT skipS skipC doIns
      (.replicate (prevSize + hashSize) data.size) 0 0
      (Array.emptyWithCapacity data.size)

/-- One config: level knobs (`chain`, `gm`, `nl`, `lazyD`, `ic`) plus the skip
    policy (`skipT`, `skipS`, `skipC`, `doIns`). `isProd` selects the production
    matcher directly (the certification ground truth); otherwise `runSkipMatcher`
    runs, with `skipT = noSkip` giving the `mirror` (skip-disabled) row. -/
structure Cfg where
  label : String
  chain : Nat
  gm : Nat
  nl : Nat
  lazyD : Nat
  ic : Nat := 1000000000
  skipT : Nat := noSkip
  skipS : Nat := 64
  skipC : Nat := 8
  doIns : Bool := false
  isProd : Bool := false

/-- The token stream for a config: the production matcher (`isProd`) or the
    skip matcher. -/
def matcherTokens (cfg : Cfg) (data : ByteArray) : Array UInt32 :=
  if cfg.isProd then
    lz77ChainLazyIterPMerged data cfg.chain 32768 cfg.ic cfg.gm cfg.nl cfg.lazyD
  else
    runSkipMatcher data cfg.chain 32768 cfg.ic cfg.gm cfg.nl cfg.lazyD
      cfg.skipT cfg.skipS cfg.skipC cfg.doIns

/-- One config through the exact production split-tier dispatch (the L6–L7 arm of
    `deflateRaw`: sized preps, obs-split arbitration, winner emitted). Byte-for-byte
    what the shipped encoder would emit for this token stream. -/
def runCfg (cfg : Cfg) (data : ByteArray) : Nat :=
  let ptokens := matcherTokens cfg data
  let cuts := chooseSplitsHeuristicP ptokens data.size
  let withObs : Nat × (Unit → ByteArray) :=
    if cuts.isEmpty then deflateRawBasePPrep data ptokens
    else
      let obsFreqs := deflateObsSplitSizedFreqsP data ptokens cuts
      let basePrep := deflateRawBasePPrepF data ptokens obsFreqs.2
      if basePrep.1 < obsFreqs.1.1 then basePrep else obsFreqs.1
  (withObs.2 ()).size

/-- The grid.

    L6 knobs (chain 64, gm 259, nl 65, ld 32): `prod`, `mirror`, the 12
    `noins` (T,S,C) points, and one `ins` point. L7 knobs (chain 256, gm 259,
    nl 130, ld 128): `prod`, `mirror`, and one `noins` point. -/
def cfgs : List Cfg := Id.run do
  let mut out : List Cfg := []
  -- L6 certification rows.
  out := out ++ [
    { label := "prod-L6", chain := 64, gm := 259, nl := 65, lazyD := 32, isProd := true },
    { label := "mirror-L6", chain := 64, gm := 259, nl := 65, lazyD := 32 } ]
  -- L6 noins grid.
  for t in [32, 64, 128] do
    for s in [32, 64] do
      for cc in [4, 8] do
        out := out ++ [{
          label := s!"L6-T{t}-S{s}-C{cc}-noins",
          chain := 64, gm := 259, nl := 65, lazyD := 32,
          skipT := t, skipS := s, skipC := cc, doIns := false }]
  -- L6 ins point.
  out := out ++ [{
    label := "L6-T64-S64-C8-ins",
    chain := 64, gm := 259, nl := 65, lazyD := 32,
    skipT := 64, skipS := 64, skipC := 8, doIns := true }]
  -- L7 rows.
  out := out ++ [
    { label := "prod-L7", chain := 256, gm := 259, nl := 130, lazyD := 128, isProd := true },
    { label := "mirror-L7", chain := 256, gm := 259, nl := 130, lazyD := 128 },
    { label := "L7-T64-S64-C8-noins", chain := 256, gm := 259, nl := 130, lazyD := 128,
      skipT := 64, skipS := 64, skipC := 8, doIns := false } ]
  return out

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

end ZipRunSkipSweep

def main (args : List String) : IO Unit := do
  if args.head? == some "--time" then
    ZipRunSkipSweep.timeMain args.tail
  else
    ZipRunSkipSweep.ratioMain args
