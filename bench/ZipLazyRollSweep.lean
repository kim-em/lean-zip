import Zip

/-! # lazyroll-sweep — rolling multi-step lazy2 deferral spike (#2783)

Measurement-first probe for issue #2783: does libdeflate's *rolling* deferral
(`deflate_compress_lazy2`) — keep deferring while each next position strictly
improves the pending match, re-probing at descending chain depths — move L7/L8
ratio over our one-step lookahead?

Unlike the earlier `lazy2-sweep` (a bounded best-of-{pos,pos+1,pos+2} cascade),
this spike carries a genuine *pending match* forward: at each accept it emits the
old match-start byte as a literal, rolls the pending match to the new (strictly
better) one, inserts the vacated position into the hash state, and re-probes the
next position at the next rung of a depth ladder — exactly libdeflate's loop.

The matcher is a `partial def` copy of the *production* packed merged loop
(`lz77LazyMergedLoop`), composing with both the hash3 length-3 singleton
(`h3Seed`/`updateHash3`, #2824) and the seeded `pos+1` probe (#2822). With
`cap = 1` (single deferral) it is byte-identical to production by construction:
the rolling arm is gated off and the accept commit uses the exact production
`updateHashesMergedH3Guarded pos 1 (matchLen2+1)` batch. The `mirror` row
certifies this against `lzMatchP` before any variant delta is trusted.

Sizes are computed through the *exact* L6–L8 dispatch `deflateRaw` uses
(base-vs-observation-split, size arbitrated), reusing `lazy2-sweep`'s `sizeAt`.

Grid (per file, level ∈ {7,8}):
  * `prod`   — production `lzMatchP` (ground truth).
  * `mirror` — this loop at cap=1 (must equal prod byte-for-byte).
  * `c<cap>m<mode>` — rolling: cap ∈ {2,4,64(=unbounded)}, ladder mode ∈
                      {0 = /4 constant after the first /2 probe,
                       1 = /2,/4,/8,… descending}.

    <file>,<level>,<variant>,<inBytes>,<outBytes>[,<ms>]

Usage:
  lake -d bench exe lazyroll-sweep <file> [<file> ...]        # ratio only
  lake -d bench exe lazyroll-sweep --time <reps> <file> ...   # + timed reps
-/

open Zip.Native.Deflate

namespace ZipLazyRollSweep

/-- Ladder depth for the rolling probe at defer-step `step` (≥1 inside the roll;
    the mainLoop's own `pos+1` probe is step 0 and always runs at production
    `lazyDepth`). Mode 0 holds `maxChain/4` constant; mode 1 descends
    `maxChain/2^(step+1)` (so step 1 → /4, step 2 → /8, …). Floored at 1 so a
    probe never runs at zero fuel. -/
@[inline] def probeDepth (maxChain step mode : Nat) : Nat :=
  let d := if mode == 0 then maxChain / 4 else maxChain / (2 ^ (step + 1))
  max 1 d

mutual

/-- Production `lz77LazyMergedLoop` copy, with the single accept commit replaced
    by an entry into `rollDefer`. Everything else is byte-for-byte production. -/
partial def mainLoop (data : ByteArray)
    (windowSize hashSize prevSize maxChain insertCap goodMatch niceLen lazyDepth cap mode : Nat)
    (useH3 : Bool) (c h3tab : Array Nat) (pos : Nat) (acc : Array UInt32) : Array UInt32 :=
  if hlt : pos + 2 < data.size then
    let h := lz77Greedy.hash3 data pos hashSize hlt
    let head := headProbeGuarded c (prevSize + h)
    let c := guardedSet c (prevSize + h) pos
    let c := guardedSet c (pos &&& 0x7FFF) head
    let seed := h3Seed useH3 data h3tab windowSize pos hlt
    let h3tab := if useH3 then guardedSet h3tab (hash3Single data pos hlt) pos else h3tab
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
            let maxLen2 := min 258 (data.size - (pos + 1))
            have hmaxLen2P : (pos + 1) + maxLen2 ≤ data.size := by omega
            let cutoff2 := min niceLen maxLen2
            let seed := if matchLen < cutoff2 then matchLen else 0
            let r2 :=
              chainWalkGuardedPackedU data c windowSize (pos + 1) maxLen2 niceLen hmaxLen2P head2 lazyDepth seed 0
            let matchLen2 := r2 % 512
            let matchPos2 := r2 / 512
            if lazyAcceptCost matchLen (pos - matchPos) matchLen2 (pos + 1 - matchPos2) then
              if pos + 1 + matchLen2 ≤ data.size then
                -- ROLLING entry: pending match M2 starts at pos+1; pos becomes a
                -- literal. At cap=1 rollDefer commits exactly like production.
                rollDefer data windowSize hashSize prevSize maxChain insertCap goodMatch niceLen lazyDepth cap mode useH3
                  c h3tab (pos + 1) matchLen2 matchPos2 1
                  (acc.push (packTok (.literal (data[pos]'(by omega)))))
              else
                let (c, h3tab) := updateHashesMergedH3Guarded useH3 data hashSize prevSize c h3tab pos 1 matchLen insertCap
                mainLoop data windowSize hashSize prevSize maxChain insertCap goodMatch niceLen lazyDepth cap mode useH3 c h3tab (pos + matchLen)
                  (acc.push (packTok (.reference matchLen (pos - matchPos))))
            else
              let (c, h3tab) := updateHashesMergedH3Guarded useH3 data hashSize prevSize c h3tab pos 1 matchLen insertCap
              mainLoop data windowSize hashSize prevSize maxChain insertCap goodMatch niceLen lazyDepth cap mode useH3 c h3tab (pos + matchLen)
                (acc.push (packTok (.reference matchLen (pos - matchPos))))
          else
            let (c, h3tab) := updateHashesMergedH3Guarded useH3 data hashSize prevSize c h3tab pos 1 matchLen insertCap
            mainLoop data windowSize hashSize prevSize maxChain insertCap goodMatch niceLen lazyDepth cap mode useH3 c h3tab (pos + matchLen)
              (acc.push (packTok (.reference matchLen (pos - matchPos))))
        else
          let (c, h3tab) := updateHashesMergedH3Guarded useH3 data hashSize prevSize c h3tab pos 1 matchLen insertCap
          mainLoop data windowSize hashSize prevSize maxChain insertCap goodMatch niceLen lazyDepth cap mode useH3 c h3tab (pos + matchLen)
            (acc.push (packTok (.reference matchLen (pos - matchPos))))
      else
        mainLoop data windowSize hashSize prevSize maxChain insertCap goodMatch niceLen lazyDepth cap mode useH3 c h3tab (pos + 1)
          (acc.push (packTok (.literal (data[pos]'(by omega)))))
    else
      mainLoop data windowSize hashSize prevSize maxChain insertCap goodMatch niceLen lazyDepth cap mode useH3 c h3tab (pos + 1)
        (acc.push (packTok (.literal (data[pos]'(by omega)))))
  else
    trailingP data pos acc

/-- Rolling deferral state. Pending match `(pLen, pMatchPos)` starts at position
    `mp`; positions `< mp` are decided (literals in `acc`, heads inserted through
    `mp-1`); `mp` is *not* yet inserted. `step` = number of defers already
    committed (≥1). If another defer is allowed and the next probe strictly
    improves the pending match, emit `lit(mp)`, insert `mp`, roll to the new
    match at `mp+1`, and recurse. Otherwise commit the pending match. The
    no-more-defers commit uses the production batch `updateHashes (mp-1) 1
    (pLen+1)` (inserts `mp..mp+pLen-1`), so cap=1 reproduces production exactly;
    the rolled commit uses `updateHashes mp 1 pLen` since `mp` was already
    inserted for the probe. -/
partial def rollDefer (data : ByteArray)
    (windowSize hashSize prevSize maxChain insertCap goodMatch niceLen lazyDepth cap mode : Nat)
    (useH3 : Bool) (c h3tab : Array Nat) (mp pLen pMatchPos step : Nat) (acc : Array UInt32) : Array UInt32 :=
  if hcan : step < cap ∧ mp + 3 < data.size ∧ pLen < goodMatch ∧ mp + pLen ≤ data.size then
    -- Insert mp (loop-top style) so mp+1 can match against it.
    let hmp := lz77Greedy.hash3 data mp hashSize (by omega)
    let headmp := headProbeGuarded c (prevSize + hmp)
    let c := guardedSet c (prevSize + hmp) mp
    let c := guardedSet c (mp &&& 0x7FFF) headmp
    let h3tab := if useH3 then guardedSet h3tab (hash3Single data mp (by omega)) mp else h3tab
    -- Probe mp+1 at the ladder rung, length-seeded with the pending length.
    let h2 := lz77Greedy.hash3 data (mp + 1) hashSize (by omega)
    let head2 := headProbeGuarded c (prevSize + h2)
    let maxLen2 := min 258 (data.size - (mp + 1))
    have hmaxLen2P : (mp + 1) + maxLen2 ≤ data.size := by omega
    let cutoff2 := min niceLen maxLen2
    let seed := if pLen < cutoff2 then pLen else 0
    let depth := probeDepth maxChain step mode
    let r2 := chainWalkGuardedPackedU data c windowSize (mp + 1) maxLen2 niceLen hmaxLen2P head2 depth seed 0
    let len' := r2 % 512
    let pos' := r2 / 512
    if lazyAcceptCost pLen (mp - pMatchPos) len' (mp + 1 - pos') ∧ mp + 1 + len' ≤ data.size then
      -- Strictly improves: mp becomes a literal, roll pending to (len', pos') at mp+1.
      rollDefer data windowSize hashSize prevSize maxChain insertCap goodMatch niceLen lazyDepth cap mode useH3
        c h3tab (mp + 1) len' pos' (step + 1)
        (acc.push (packTok (.literal (data[mp]'(by omega)))))
    else
      -- No improvement: commit pending match at mp. mp already inserted above, so
      -- insert only the interior mp+1..mp+pLen-1.
      let (c, h3tab) := updateHashesMergedH3Guarded useH3 data hashSize prevSize c h3tab mp 1 pLen insertCap
      mainLoop data windowSize hashSize prevSize maxChain insertCap goodMatch niceLen lazyDepth cap mode useH3 c h3tab (mp + pLen)
        (acc.push (packTok (.reference pLen (mp - pMatchPos))))
  else
    -- No more defers: commit pending match at mp via the production batch
    -- (inserts mp..mp+pLen-1). At cap=1 with mp=pos+1 this is exactly the
    -- production accept commit.
    let (c, h3tab) := updateHashesMergedH3Guarded useH3 data hashSize prevSize c h3tab (mp - 1) 1 (pLen + 1) insertCap
    mainLoop data windowSize hashSize prevSize maxChain insertCap goodMatch niceLen lazyDepth cap mode useH3 c h3tab (mp + pLen)
      (acc.push (packTok (.reference pLen (mp - pMatchPos))))

end

/-- Entry: builds the combined `prevSize + hashSize` array and h3 singleton table
    exactly as `lz77ChainLazyIterPMerged`, then runs the rolling loop. -/
def runRoll (data : ByteArray) (maxChain insertCap goodMatch niceLen lazyDepth cap mode : Nat)
    (useH3 : Bool) : Array UInt32 :=
  if data.size < 3 then
    trailingP data 0 #[]
  else
    let hashSize := 65536
    let prevSize := min chainWinSize data.size
    mainLoop data 32768 hashSize prevSize maxChain insertCap goodMatch niceLen lazyDepth cap mode useH3
      (.replicate (prevSize + hashSize) data.size) (.replicate 32768 data.size) 0
      (Array.emptyWithCapacity data.size)

/-- Compressed size through the exact L6–L8 dispatch (copied from `lazy2-sweep`). -/
def sizeAt (data : ByteArray) (level : UInt8) (ptoks : Array UInt32) : Nat :=
  if level < 6 then
    (deflateRawBasePPrep data ptoks).1
  else
    let basePrep := deflateRawBasePPrep data ptoks
    let cuts := chooseSplitsHeuristicP ptoks data.size
    let withObs : Nat × (Unit → ByteArray) :=
      if cuts.isEmpty then basePrep
      else
        let obsPrep := deflateDynamicBlocksSharedAtSizedP data ptoks cuts
        if basePrep.1 < obsPrep.1 then basePrep else obsPrep
    withObs.1

/-- Run the rolling matcher at a level's production knobs, for a given cap/mode. -/
def runAt (data : ByteArray) (level : UInt8) (cap mode : Nat) : Array UInt32 :=
  runRoll data (chainDepth level) (insertCap level) (goodMatch level) (niceLen level)
    (lazyDepth level) cap mode (useH3Level level)

def levels : List UInt8 := [7, 8]

/-- (cap, mode, label) grid. cap 64 stands in for "unbounded" (no file defers
    64 times in a row). -/
def grid : List (Nat × Nat × String) :=
  [ (2, 0, "c2m0"), (2, 1, "c2m1"),
    (4, 0, "c4m0"), (4, 1, "c4m1"),
    (64, 0, "c64m0"), (64, 1, "c64m1") ]

def label (path : String) : String :=
  let p := System.FilePath.mk path
  match p.parent >>= (·.fileName), p.fileName with
  | some d, some f => s!"{d}/{f}"
  | _, some f => f
  | _, _ => path

def runFileRatio (path : String) : IO Unit := do
  let data ← IO.FS.readBinFile path
  let lbl := label path
  for level in levels do
    let row (v : String) (sz : Nat) : IO Unit :=
      IO.println s!"{lbl},{level},{v},{data.size},{sz}"
    row "prod" (sizeAt data level (lzMatchP data level))
    -- mirror: cap=1 must equal prod
    row "mirror" (sizeAt data level (runAt data level 1 0))
    for (cap, mode, v) in grid do
      row v (sizeAt data level (runAt data level cap mode))
    (← IO.getStdout).flush

/-- A matcher variant reduced to a checksum `Nat` (sum of token words), so the
    timed region's result escapes into a printed sink and the compiler cannot
    hoist the pure matcher call out of the rep loop (the `ZipMidSweep` pattern). -/
@[inline] def matchChecksum (toks : Array UInt32) : Nat :=
  toks.foldl (fun a w => a + w.toNat) toks.size

def timedVariants (data : ByteArray) (level : UInt8) : List (String × (Unit → Nat)) :=
  [ ("prod",   fun _ => matchChecksum (lzMatchP data level)),
    ("mirror", fun _ => matchChecksum (runAt data level 1 0)),
    ("c2m0",   fun _ => matchChecksum (runAt data level 2 0)),
    ("c4m0",   fun _ => matchChecksum (runAt data level 4 0)),
    ("c64m0",  fun _ => matchChecksum (runAt data level 64 0)) ]

/-- Interleaved, pinned matcher timing over the whole corpus. Outer loop over
    reps; inner loop over (level, variant); each cell times a single pass over
    all files, reducing to a printed sink. Report every rep; the min across reps
    is the pinned estimate. -/
def timeMain (reps : Nat) (paths : List String) : IO Unit := do
  let mut files : List ByteArray := []
  for path in paths do
    files := files ++ [← IO.FS.readBinFile path]
  let total := files.foldl (fun a f => a + f.size) 0
  IO.println s!"corpus: {paths.length} files, {total} bytes, {reps} reps"
  for rep in [0:reps] do
    for level in levels do
      for (v, _) in timedVariants (files.headD default) level do
        let t0 ← IO.monoNanosNow
        let mut sink := 0
        for f in files do
          -- rebuild the closure per file so `data` is this file
          let fn := (timedVariants f level).lookup v |>.getD (fun _ => 0)
          sink := sink + fn ()
        let t1 ← IO.monoNanosNow
        let ms := (Float.ofNat (t1 - t0)) / 1e6
        let mbps := (Float.ofNat total) / 1048576.0 / ((Float.ofNat (t1 - t0)) / 1e9)
        IO.println s!"rep{rep},L{level},{v},{ms},{mbps},{sink}"
        (← IO.getStdout).flush

def main (args : List String) : IO Unit := do
  match args with
  | "--time" :: reps :: paths =>
    timeMain ((reps.toNat?).getD 5) paths
  | paths =>
    for path in paths do runFileRatio path

end ZipLazyRollSweep

def main (args : List String) : IO Unit := ZipLazyRollSweep.main args
