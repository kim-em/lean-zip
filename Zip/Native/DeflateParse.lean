import Zip.Native.Deflate
import Zip.Native.DeflateFreqs

/-!
  Near-optimal LZ parsing support (#2496), part 1: the per-position
  match-candidate cache and the bit-cost model consumed by the backward-DP
  parser (`lz77Optimal`, in the sequel).

  Everything in this file is *heuristic*: the candidate cache and the cost
  tables never enter any correctness proof. Validity of the final token
  stream is re-established at emission by `lz77Greedy.countMatch` plus
  explicit guards, following the same discipline as `lz77Chain` (see its
  docstring): the proofs are completely independent of what this file
  computes, so it can be tuned freely.
-/

namespace Zip.Native.Deflate

/-! ## Tunables -/

/-- Candidate-cache slots per position (fixed stride). Candidates are kept
    with strictly increasing length in nearest-first order, so each slot is a
    point on the (length, distance) Pareto frontier; 8 covers the useful
    frontier in practice. Pure ratio/speed knob. -/
def optCacheSlots : Nat := 8

/-- Stop the candidate chain walk once a match of at least this length is
    found ("nice length", zlib terminology): further candidates can improve
    the parse only marginally and the walk dominates the cost. With 258 the
    walk stops only at the absolute maximum, which also keeps highly
    repetitive input fast (first candidate hits 258 immediately). -/
def optNiceLen : Nat := 258

/-- Chain-walk depth for the candidate cache. The optimal parser walks the
    chain at *every* position (greedy matchers skip match interiors), so this
    is deliberately lower than `chainDepth 9 = 1024`; the DP recovers more
    ratio from candidate *choice* than raw depth buys. Pure ratio/speed knob. -/
def optChainDepth : Nat := 256

/-- DP region size in bytes. The cost/cache arrays live per region (memory
    cap); cost continuity across the region end is approximated by a baseline
    tail estimate, and matches may extend past the region end, so the region
    size is a memory/locality knob, not a parse barrier. -/
def optRegionSize : Nat := 262144

/-- Bit cost charged for a symbol the current cost model assigns no code
    (zero frequency in the fitting histogram): the maximum DEFLATE code
    length. Never 0 — a free unseen symbol degenerates the DP — and low
    enough that genuinely useful new symbols can still be introduced (the
    final emission re-fits real Huffman trees to whatever the DP chose). -/
def zeroFreqCodeLen : Nat := 15

/-- Cost-table default for index ranges no slot covers (lengths 0–2,
    distance 0): large enough that the DP never prefers them. Defensive — the
    DP only prices candidates with `len ≥ 3`, `dist ≥ 1`. -/
def badCost : Nat := 1000000

/-! ## Candidate cache

Fixed-stride flat arrays: position `base + j` owns slots
`[optCacheSlots * j, optCacheSlots * (j+1))` of `lens`/`dists`; a zero
length marks an empty slot (`Array.replicate _ 0` = all empty). No nested
arrays or pairs (boxing). -/

/-- Walk the `prev` chain from `cand` (nearest-first), recording candidates
    of strictly increasing length into slots `slotBase + k` of `lens`/`dists`.
    Stops at chain end (the `data.size` sentinel fails `cand < pos`), fuel
    exhaustion, a full slot block, or a match reaching
    `min optNiceLen maxLen`. Nearest-first + strictly increasing length makes
    the recorded set a Pareto frontier: any dropped candidate is no longer
    and no nearer than some recorded one (distance cost is monotone in
    distance), given that the DP also evaluates truncated lengths. -/
def chainWalkAll (data : ByteArray) (prev : Array Nat) (pos maxLen : Nat)
    (hpm : pos + maxLen ≤ data.size) (cand fuel bestLen k slotBase : Nat)
    (lens dists : Array Nat) : Array Nat × Array Nat :=
  if fuel = 0 then (lens, dists)
  else if optCacheSlots ≤ k then (lens, dists)
  else if hc : cand < pos ∧ pos - cand ≤ 32768 then
    have hcand : cand + maxLen ≤ data.size := by omega
    let ml := lz77Greedy.countMatch data cand pos maxLen hcand hpm
    if 3 ≤ ml ∧ bestLen < ml then
      let lens := lens.set! (slotBase + k) ml
      let dists := dists.set! (slotBase + k) (pos - cand)
      if min optNiceLen maxLen ≤ ml then (lens, dists)
      else chainWalkAll data prev pos maxLen hpm (prev[cand]!) (fuel - 1) ml (k + 1)
        slotBase lens dists
    else
      chainWalkAll data prev pos maxLen hpm (prev[cand]!) (fuel - 1) bestLen k
        slotBase lens dists
  else (lens, dists)
termination_by fuel
decreasing_by all_goals omega

/-- Proven-bounds copy of `chainWalkAll` (Wave 3 Step 0.1, same generational
    pattern as `chainWalkFast`/`updateHashesFast` in `Deflate.lean`):
    `prev[cand]` is in range because the walk guard gives `cand < pos` and
    `hps : pos ≤ prev.size`; the slot writes are in range because the slot
    guard gives `k < optCacheSlots` and `hsl`/`hsd` bound the whole slot
    block. Once established, the three hypotheses discharge every access in
    the loop statically. -/
def chainWalkAllFast (data : ByteArray) (prev : Array Nat) (pos maxLen : Nat)
    (hpm : pos + maxLen ≤ data.size) (cand fuel bestLen k slotBase : Nat)
    (lens dists : Array Nat) (hps : pos ≤ prev.size)
    (hsl : slotBase + optCacheSlots ≤ lens.size)
    (hsd : slotBase + optCacheSlots ≤ dists.size) : Array Nat × Array Nat :=
  if fuel = 0 then (lens, dists)
  else if hk : optCacheSlots ≤ k then (lens, dists)
  else if hc : cand < pos ∧ pos - cand ≤ 32768 then
    have hcand : cand + maxLen ≤ data.size := by omega
    let ml := lz77Greedy.countMatch data cand pos maxLen hcand hpm
    if 3 ≤ ml ∧ bestLen < ml then
      have hbl : slotBase + k < lens.size := by omega
      have hbd : slotBase + k < dists.size := by omega
      if min optNiceLen maxLen ≤ ml then
        (lens.set (slotBase + k) ml hbl, dists.set (slotBase + k) (pos - cand) hbd)
      else chainWalkAllFast data prev pos maxLen hpm (prev[cand]'(by omega)) (fuel - 1) ml (k + 1)
        slotBase (lens.set (slotBase + k) ml hbl) (dists.set (slotBase + k) (pos - cand) hbd)
        hps (by simpa using hsl) (by simpa using hsd)
    else
      chainWalkAllFast data prev pos maxLen hpm (prev[cand]'(by omega)) (fuel - 1) bestLen k
        slotBase lens dists hps hsl hsd
  else (lens, dists)
termination_by fuel
decreasing_by all_goals omega

/-- One runtime check (`pos ≤ prev.size` plus the slot block fitting in
    `lens`/`dists`) guards the whole `chainWalkAllFast` walk; the fallback is
    the original panic-checked `chainWalkAll` (unreachable in practice —
    `buildCache` callers size `prev` to the input and the cache arrays to
    `slots * r`), so the wrapper is value-identical to `chainWalkAll`. -/
@[inline] def chainWalkAllGuarded (data : ByteArray) (prev : Array Nat) (pos maxLen : Nat)
    (hpm : pos + maxLen ≤ data.size) (cand fuel bestLen k slotBase : Nat)
    (lens dists : Array Nat) : Array Nat × Array Nat :=
  if hg : pos ≤ prev.size ∧ slotBase + optCacheSlots ≤ lens.size ∧
      slotBase + optCacheSlots ≤ dists.size then
    chainWalkAllFast data prev pos maxLen hpm cand fuel bestLen k slotBase lens dists
      hg.1 hg.2.1 hg.2.2
  else
    chainWalkAll data prev pos maxLen hpm cand fuel bestLen k slotBase lens dists

/-- Build the candidate cache for region `[base, base + r)`: at **every**
    position (the DP can land anywhere, so none may be skipped) insert the
    position into the hash chains and record its candidate frontier.
    `hashTable`/`prev` are the same global chain state `lz77Chain` uses
    (sentinel `data.size`), threaded across regions so distances legally
    reach up to 32 KiB into prior regions. Returns the filled cache and the
    updated chain state.

    `depth`/`slots` are passed as parameters (callers supply `optChainDepth`/
    `optCacheSlots`): literal constants in the body make the well-founded
    elaboration attempt deep reduction of the `chainWalkAll` application and
    blow the recursion limit. -/
def buildCache (data : ByteArray) (hashTable prev : Array Nat) (depth slots base r j : Nat)
    (lens dists : Array Nat) : Array Nat × Array Nat × Array Nat × Array Nat :=
  if hj : j < r then
    let pos := base + j
    if hlt : pos + 2 < data.size then
      let h := lz77Greedy.hash3 data pos 65536 hlt
      let head := headProbeGuarded hashTable h
      let hashTable := guardedSet hashTable h pos
      let prev := guardedSet prev pos head
      let maxLen := min 258 (data.size - pos)
      have hpm : pos + maxLen ≤ data.size := by omega
      let (lens, dists) := chainWalkAllGuarded data prev pos maxLen hpm head depth
        0 0 (slots * j) lens dists
      buildCache data hashTable prev depth slots base r (j + 1) lens dists
    else
      buildCache data hashTable prev depth slots base r (j + 1) lens dists
  else (lens, dists, hashTable, prev)
termination_by r - j
decreasing_by all_goals omega

/-! ## Cost model

Dense `Nat` tables so the DP hot loop does no `Option` lookups:
`litCost` (256 entries, bits per literal byte), `lenCost` (259 entries,
index = match length 3–258, length-code extra bits folded in), `distCost`
(32769 entries, index = distance 1–32768, distance extra bits folded in). -/

/-- Bit cost of a code length, substituting `zeroFreqCodeLen` for symbols
    the fitting histogram never saw (code length 0). -/
@[inline] def costOfLen (l : Nat) : Nat :=
  if l = 0 then zeroFreqCodeLen else l

/-- Fill `table[lo..hi)` with `cost`. -/
def fillCostRange (table : Array Nat) (lo hi cost : Nat) : Array Nat :=
  if lo < hi then fillCostRange (table.set! lo cost) (lo + 1) hi cost
  else table
termination_by hi - lo
decreasing_by omega

/-- Fill a dense value→bits table from a base/extra slot family (RFC 1951
    §3.2.5): slot `i` covers values `[base[i], base[i+1])` (the last slot up
    to `table.size`), each costing
    `costOfLen codeLens[symOffset + i] + extra[i]` bits. -/
def fillCostSlots (base : Array UInt16) (extra : Array UInt8) (codeLens : Array Nat)
    (symOffset : Nat) (table : Array Nat) (i : Nat) : Array Nat :=
  if h : i < base.size then
    let lo := base[i].toNat
    let hi := if h1 : i + 1 < base.size then base[i + 1].toNat else table.size
    let c := costOfLen codeLens[symOffset + i]! + extra[i]!.toNat
    fillCostSlots base extra codeLens symOffset (fillCostRange table lo hi c) (i + 1)
  else table
termination_by base.size - i
decreasing_by omega

/-- Build the three dense cost tables from lit/len and distance code-length
    arrays (286 and 30 entries; longer is fine — fixed-Huffman tables have
    288/32). -/
def mkCostTables (litLens distLens : Array Nat) :
    Array Nat × Array Nat × Array Nat :=
  let litCost := litLoop litLens (Array.replicate 256 0) 0
  let lenCost := fillCostSlots Inflate.lengthBase Inflate.lengthExtra litLens 257
    (Array.replicate 259 badCost) 0
  let distCost := fillCostSlots Inflate.distBase Inflate.distExtra distLens 0
    (Array.replicate 32769 badCost) 0
  (litCost, lenCost, distCost)
where
  litLoop (lens table : Array Nat) (b : Nat) : Array Nat :=
    if b < 256 then litLoop lens (table.set! b (costOfLen lens[b]!)) (b + 1)
    else table
  termination_by 256 - b
  decreasing_by omega

/-- Round-1 (static) cost model: fixed-Huffman code lengths (RFC 1951
    §3.2.6) — libdeflate's seeding choice. No dependence on a prior parse,
    so no seed-quality failure mode. -/
def staticCostTables : Array Nat × Array Nat × Array Nat :=
  mkCostTables (Inflate.fixedLitLengths.map (·.toNat))
    (Inflate.fixedDistLengths.map (·.toNat))

/-- Cost tables fitted to a token stream: histogram (`tokenFreqs`) →
    length-limited Huffman code lengths (`dynamicCodeLengths`) → dense
    tables. Used for DP rounds after the first. -/
def fittedCostTables (tokens : Array LZ77Token) :
    Array Nat × Array Nat × Array Nat :=
  let f := tokenFreqs tokens
  let lens := dynamicCodeLengths f.1 f.2
  mkCostTables lens.1.toArray lens.2.toArray

/-! ## Backward DP

Per region `[base, base + r)`: `cost[i]` (region-local, size `r + 259`)
estimates the bits to encode `data[base + i ..]`; the choice arrays `chLen`/
`chDist` (global, absolute positions, default `(1, 0)` = literal) record the
arg-min. The tail entries `cost[r ..r + 258]` are seeded with a baseline
per-byte estimate — never 0, which would price the region end as "free" and
bias every parse near the boundary — so matches may extend up to 258 bytes
past the region end (the emitter just skips the next region's prefix). -/

/-- Average literal bit cost (rounded up) under a cost table: the baseline
    used to price bytes beyond the DP region end. -/
def avgLitBits (litCost : Array Nat) : Nat :=
  (litCost.foldl (· + ·) 0 + 255) / 256

/-- Seed the 259 tail entries: `cost[r + j] = j * perByte`. -/
def seedTailCosts (cost : Array Nat) (r perByte j : Nat) : Array Nat :=
  if j < 259 then seedTailCosts (cost.set! (r + j) (j * perByte)) r perByte (j + 1)
  else cost
termination_by 259 - j
decreasing_by omega

/-- Evaluate one candidate at the length-code lower boundaries inside
    `(prevLen, len)` (its covered interval, exclusive of `len` which the
    caller already evaluated): truncating a match to a boundary can buy a
    cheaper length code or a better continuation. `(bestC, bestL, bestD)`
    is the running arg-min. -/
def scanBounds (lenCost distCost cost : Array Nat) (i dist prevLen len s : Nat)
    (bestC bestL bestD : Nat) : Nat × Nat × Nat :=
  if h : s < Inflate.lengthBase.size then
    let b := Inflate.lengthBase[s].toNat
    if prevLen < b ∧ b < len then
      let c := lenCost[b]! + distCost[dist]! + cost[i + b]!
      if c < bestC then
        scanBounds lenCost distCost cost i dist prevLen len (s + 1) c b dist
      else
        scanBounds lenCost distCost cost i dist prevLen len (s + 1) bestC bestL bestD
    else
      scanBounds lenCost distCost cost i dist prevLen len (s + 1) bestC bestL bestD
  else (bestC, bestL, bestD)
termination_by Inflate.lengthBase.size - s
decreasing_by all_goals omega

/-- Scan the candidate slots of region-local position `i` (cache block at
    `slotBase`), evaluating each candidate at its full length and at the
    length-code boundaries of its covered interval. Slots hold strictly
    increasing lengths; a zero length terminates the block. -/
def scanCands (cacheLens cacheDists lenCost distCost cost : Array Nat)
    (slotBase i slots k prevLen : Nat) (bestC bestL bestD : Nat) : Nat × Nat × Nat :=
  if _h : k < slots then
    let len := cacheLens[slotBase + k]!
    if len = 0 then (bestC, bestL, bestD)
    else
      let dist := cacheDists[slotBase + k]!
      let cFull := lenCost[len]! + distCost[dist]! + cost[i + len]!
      let (bestC, bestL, bestD) :=
        if cFull < bestC then (cFull, len, dist) else (bestC, bestL, bestD)
      let (bestC, bestL, bestD) :=
        scanBounds lenCost distCost cost i dist prevLen len 0 bestC bestL bestD
      scanCands cacheLens cacheDists lenCost distCost cost slotBase i slots
        (k + 1) len bestC bestL bestD
  else (bestC, bestL, bestD)
termination_by slots - k
decreasing_by all_goals omega

/-- Backward DP fill for region `[base, base + r)`: process region-local
    index `i - 1` down to 0, choosing literal vs the best cached candidate
    and recording the choice at the *absolute* position in `chLen`/`chDist`.
    Heuristic only — the emitter re-verifies everything. -/
def fillRegion (data : ByteArray) (base r slots : Nat)
    (cacheLens cacheDists litCost lenCost distCost : Array Nat)
    (i : Nat) (cost chLen chDist : Array Nat) :
    Array Nat × Array Nat :=
  if i = 0 then (chLen, chDist)
  else
    let idx := i - 1
    let pos := base + idx
    let lit := litCost[(data[pos]!).toNat]! + cost[idx + 1]!
    let (bc, bl, bd) := scanCands cacheLens cacheDists lenCost distCost cost
      (slots * idx) idx slots 0 0 lit 1 0
    let cost := cost.set! idx bc
    let chLen := chLen.set! pos bl
    let chDist := chDist.set! pos bd
    fillRegion data base r slots cacheLens cacheDists litCost lenCost distCost
      idx cost chLen chDist
termination_by i
decreasing_by omega

/-- Collect the region's parse implied by the current choice arrays (used to
    refit the cost model between DP rounds). Heuristic walk — no guards. -/
def collectRegionTokens (data : ByteArray) (chLen chDist : Array Nat)
    (bound pos : Nat) (acc : Array LZ77Token) : Array LZ77Token :=
  if h : pos < bound ∧ pos < data.size then
    let len := chLen[pos]!
    if hl : 3 ≤ len then
      collectRegionTokens data chLen chDist bound (pos + len)
        (acc.push (.reference len (chDist[pos]!)))
    else
      collectRegionTokens data chLen chDist bound (pos + 1)
        (acc.push (.literal data[pos]!))
  else acc
termination_by bound - pos
decreasing_by all_goals omega

/-- Run the candidate-cache + two-round DP over one region and write its
    choices. Round 1 prices with the static tables; round 2 refits to the
    region's own round-1 parse. Returns the updated chain state and choice
    arrays. -/
def fillRegionRounds (data : ByteArray) (depth slots base r : Nat)
    (slit slen sdist : Array Nat) (hashTable prev chLen chDist : Array Nat) :
    Array Nat × Array Nat × Array Nat × Array Nat :=
  let (cacheLens, cacheDists, hashTable, prev) := buildCache data hashTable prev
    depth slots base r 0 (Array.replicate (slots * r) 0) (Array.replicate (slots * r) 0)
  -- round 1: static cost model
  let cost := seedTailCosts (Array.replicate (r + 259) 0) r (avgLitBits slit) 0
  let (chLen, chDist) := fillRegion data base r slots cacheLens cacheDists
    slit slen sdist r cost chLen chDist
  -- round 2: refit to this region's round-1 parse
  let toks := collectRegionTokens data chLen chDist (base + r) base #[]
  let (flit, flen, fdist) := fittedCostTables toks
  let cost := seedTailCosts (Array.replicate (r + 259) 0) r (avgLitBits flit) 0
  let (chLen, chDist) := fillRegion data base r slots cacheLens cacheDists
    flit flen fdist r cost chLen chDist
  (hashTable, prev, chLen, chDist)

/-- Region driver for `computeChoices`: regions advance by
    `min regionSize (data.size - base)` bytes; the hash-chain state persists
    across regions (cross-region distances are legal and wanted). -/
def computeChoicesLoop (data : ByteArray) (depth slots regionSize : Nat)
    (slit slen sdist : Array Nat) (hashTable prev : Array Nat) (base : Nat)
    (chLen chDist : Array Nat) : Array Nat × Array Nat :=
  if hb : base < data.size ∧ 0 < regionSize then
    let r := min regionSize (data.size - base)
    have hdec : data.size - (base + r) < data.size - base := by omega
    let (hashTable, prev, chLen, chDist) := fillRegionRounds data depth slots base r
      slit slen sdist hashTable prev chLen chDist
    computeChoicesLoop data depth slots regionSize slit slen sdist hashTable prev
      (base + r) chLen chDist
  else (chLen, chDist)
termination_by data.size - base
decreasing_by omega

/-- Compute the global DP choice arrays for the whole input: per region,
    build the candidate cache and run the two-round backward DP. Defaults
    `(1, 0)` = literal everywhere, so unfilled entries are always safe.
    Heuristic only: consumed by the re-verifying emitter `optimalEmit`. -/
def computeChoices (data : ByteArray) : Array Nat × Array Nat :=
  let (slit, slen, sdist) := staticCostTables
  computeChoicesLoop data optChainDepth optCacheSlots optRegionSize slit slen sdist
    (Array.replicate 65536 data.size) (Array.replicate data.size data.size)
    0 (Array.replicate data.size 1) (Array.replicate data.size 0)

/-! ## Token emission (the proof-bearing boundary)

The choice arrays are *untrusted*: `optimalEmit` re-establishes validity for
every match it emits — the same guards `lz77Chain.mainLoop` uses plus a fresh
`countMatch` confirming the stored length — and falls back to a literal
otherwise (never fires for choices the DP actually wrote). The `ValidDecomp`
and encodability proofs in `Zip.Spec.LZ77OptimalCorrect` are stated for
**arbitrary** `chLen`/`chDist`, so nothing about the DP enters them. -/

/-- Emit tokens for `data[pos ..]` from the choice arrays, re-verifying every
    match. List-cons version for proofs; `optimalEmitIter` is the runtime
    twin (proven equal in `LZ77OptimalCorrect`). -/
def optimalEmit (data : ByteArray) (chLen chDist : Array Nat) (pos : Nat) :
    List LZ77Token :=
  if hpos : pos < data.size then
    let len := chLen[pos]!
    let dist := chDist[pos]!
    if hg : 3 ≤ len ∧ len ≤ 258 ∧ pos + len ≤ data.size ∧
        1 ≤ dist ∧ dist ≤ pos ∧ dist ≤ 32768 then
      have h1 : (pos - dist) + len ≤ data.size := by omega
      if hml : lz77Greedy.countMatch data (pos - dist) pos len h1 hg.2.2.1 = len then
        .reference len dist :: optimalEmit data chLen chDist (pos + len)
      else
        .literal (data[pos]'hpos) :: optimalEmit data chLen chDist (pos + 1)
    else
      .literal (data[pos]'hpos) :: optimalEmit data chLen chDist (pos + 1)
  else []
termination_by data.size - pos
decreasing_by all_goals omega

/-- Iterative (tail-recursive, `Array`-accumulating) twin of `optimalEmit`.
    Same output (`optimalEmitIter_eq` in `LZ77OptimalCorrect`); does not
    overflow the stack on large inputs. -/
def optimalEmitIter (data : ByteArray) (chLen chDist : Array Nat) (pos : Nat)
    (acc : Array LZ77Token) : Array LZ77Token :=
  if hpos : pos < data.size then
    let len := chLen[pos]!
    let dist := chDist[pos]!
    if hg : 3 ≤ len ∧ len ≤ 258 ∧ pos + len ≤ data.size ∧
        1 ≤ dist ∧ dist ≤ pos ∧ dist ≤ 32768 then
      have h1 : (pos - dist) + len ≤ data.size := by omega
      if hml : lz77Greedy.countMatch data (pos - dist) pos len h1 hg.2.2.1 = len then
        optimalEmitIter data chLen chDist (pos + len) (acc.push (.reference len dist))
      else
        optimalEmitIter data chLen chDist (pos + 1) (acc.push (.literal (data[pos]'hpos)))
    else
      optimalEmitIter data chLen chDist (pos + 1) (acc.push (.literal (data[pos]'hpos)))
  else acc
termination_by data.size - pos
decreasing_by all_goals omega

/-- Near-optimal LZ77 parse: cost-model backward DP over the candidate
    cache, then re-verified emission. List-backed reference version (the
    proofs' subject); `lz77OptimalIter` is the runtime entry point. -/
def lz77Optimal (data : ByteArray) : Array LZ77Token :=
  let (chLen, chDist) := computeChoices data
  (optimalEmit data chLen chDist 0).toArray

/-- Runtime entry point: same tokens as `lz77Optimal` (proven in
    `LZ77OptimalCorrect`), tail-recursive emission. -/
def lz77OptimalIter (data : ByteArray) : Array LZ77Token :=
  let (chLen, chDist) := computeChoices data
  optimalEmitIter data chLen chDist 0 #[]

end Zip.Native.Deflate
