import Zip

/-! # rung-4 acceptance — production rolling loop == certified spike (#2837)

Verifies that the production merged matcher `lz77ChainLazyIterPMerged` driven at
`lazy2Steps = 4` (through the split-tier dispatch knobs) reproduces the certified
spike's `c4m0` rolling row (`bench/ZipLazyRollSweep.lean` on `perf/lazy2-deferral`,
commit 0a42c3d5) **byte-for-byte** on every Silesia file at L7. The spike loop is
copied verbatim below (namespaced) as the behavioral reference.

Also checks the cap=1 mirror: production `lzMatchP` == `runRoll .. cap=1`, the
spike's own certification that its harness matches production.

Usage: lake -d bench exe rung4-accept <file> ... -/

open Zip.Native.Deflate

namespace Rung4Spike

/-- Verbatim copy of the spike's mode-0/1 probe-depth ladder. -/
@[inline] def probeDepth (maxChain step mode : Nat) : Nat :=
  let d := if mode == 0 then maxChain / 4 else maxChain / (2 ^ (step + 1))
  max 1 d

mutual

/-- Verbatim copy of the spike's production-`lz77LazyMergedLoop` mainLoop, single
    accept commit replaced by an entry into `rollDefer`. -/
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

/-- Verbatim copy of the spike's rolling-deferral state machine. -/
partial def rollDefer (data : ByteArray)
    (windowSize hashSize prevSize maxChain insertCap goodMatch niceLen lazyDepth cap mode : Nat)
    (useH3 : Bool) (c h3tab : Array Nat) (mp pLen pMatchPos step : Nat) (acc : Array UInt32) : Array UInt32 :=
  if hcan : step < cap ∧ mp + 3 < data.size ∧ pLen < goodMatch ∧ mp + pLen ≤ data.size then
    let hmp := lz77Greedy.hash3 data mp hashSize (by omega)
    let headmp := headProbeGuarded c (prevSize + hmp)
    let c := guardedSet c (prevSize + hmp) mp
    let c := guardedSet c (mp &&& 0x7FFF) headmp
    let h3tab := if useH3 then guardedSet h3tab (hash3Single data mp (by omega)) mp else h3tab
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
      rollDefer data windowSize hashSize prevSize maxChain insertCap goodMatch niceLen lazyDepth cap mode useH3
        c h3tab (mp + 1) len' pos' (step + 1)
        (acc.push (packTok (.literal (data[mp]'(by omega)))))
    else
      let (c, h3tab) := updateHashesMergedH3Guarded useH3 data hashSize prevSize c h3tab mp 1 pLen insertCap
      mainLoop data windowSize hashSize prevSize maxChain insertCap goodMatch niceLen lazyDepth cap mode useH3 c h3tab (mp + pLen)
        (acc.push (packTok (.reference pLen (mp - pMatchPos))))
  else
    let (c, h3tab) := updateHashesMergedH3Guarded useH3 data hashSize prevSize c h3tab (mp - 1) 1 (pLen + 1) insertCap
    mainLoop data windowSize hashSize prevSize maxChain insertCap goodMatch niceLen lazyDepth cap mode useH3 c h3tab (mp + pLen)
      (acc.push (packTok (.reference pLen (mp - pMatchPos))))

end

/-- Verbatim copy of the spike entry. -/
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

end Rung4Spike

/-- Production merged matcher at a given `lazy2Steps` through the L-knob dispatch. -/
def prodMerged (data : ByteArray) (level : UInt8) (lazy2Steps : Nat) : Array UInt32 :=
  lz77ChainLazyIterPMerged data (chainDepth level) 32768 (insertCap level) (goodMatch level)
    (niceLen level) (lazyDepth level) (useH3Level level) lazy2Steps

def label (path : String) : String :=
  (System.FilePath.mk path).fileName.getD path

def main (args : List String) : IO Unit := do
  let level : UInt8 := 7
  let cap := 4
  let mut allOk := true
  IO.println "file,prodTokens,spikeTokens,accept4_match,mirror_match"
  for path in args do
    let data ← IO.FS.readBinFile path
    -- production merged loop at lazy2Steps = 4
    let prod4 := prodMerged data level cap
    -- certified spike, c4m0
    let spike4 := Rung4Spike.runRoll data (chainDepth level) (insertCap level) (goodMatch level)
      (niceLen level) (lazyDepth level) cap 0 (useH3Level level)
    -- mirror: production at lazy2Steps = 1 vs spike cap = 1
    let prod1 := prodMerged data level 1
    let spike1 := Rung4Spike.runRoll data (chainDepth level) (insertCap level) (goodMatch level)
      (niceLen level) (lazyDepth level) 1 0 (useH3Level level)
    let ok4 := prod4 == spike4
    -- `prod1 == spike1`: the fused loop at lazy2Steps=1 reproduces the spike's
    --   cap=1 row, i.e. old (single-lazy) production, byte-for-byte.
    -- `prod4 == dispatch`: the split-tier dispatch (`lzMatchP`, which at L7 runs
    --   `lazy2StepsLevel 7 = 4`) equals the direct lazy2Steps=4 production loop.
    let okMirror1 := prod1 == spike1
    let okDispatch := prod4 == lzMatchP data level
    -- Non-vacuity: outputs must be non-empty.
    if prod4.size == 0 || spike4.size == 0 || prod1.size == 0 then allOk := false
    if !ok4 || !okMirror1 || !okDispatch then allOk := false
    IO.println s!"{label path},{prod4.size},{spike4.size},{ok4},{okMirror1},{okDispatch}"
    (← IO.getStdout).flush
  if allOk then
    IO.println "ACCEPT: all files byte-identical (prod lazy2Steps=4 == spike c4m0; lazy2Steps=1 mirror == spike cap1; dispatch == prod4)"
  else
    IO.println "FAIL: mismatch detected"
