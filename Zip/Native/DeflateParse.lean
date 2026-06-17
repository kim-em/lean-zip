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
    -- Prefilter (#2622): mirror of `chainWalkAllFast` — skip the compare when the
    -- byte at offset `bestLen` mismatches (the candidate can't beat `bestLen`).
    -- The byte reads are proven-bounds (`bestLen < maxLen` plus `hcand`/`hpm`);
    -- the chain reads below stay panic-checked because this is the fallback
    -- reference, invoked by `chainWalkAllGuarded` precisely when the
    -- `pos ≤ prev.size` invariant cannot be established (the proven-bounds hot
    -- path is `chainWalkAllFast`).
    let skip : Bool := if hbl : bestLen < maxLen then
        data[cand + bestLen]'(by omega) != data[pos + bestLen]'(by omega) else false
    if skip then
      chainWalkAll data prev pos maxLen hpm (prev[cand]!) (fuel - 1) bestLen k slotBase lens dists
    else
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
    -- Prefilter (#2622): a candidate is recorded only if it beats `bestLen`; if its
    -- byte at offset `bestLen` mismatches it cannot (`countMatch ≤ bestLen`), so skip
    -- the compare. The cache is heuristic (opaque to correctness), and this is also
    -- output-preserving — the same candidate set is recorded.
    let skip : Bool := if hbl : bestLen < maxLen then
        data[cand + bestLen]'(by omega) != data[pos + bestLen]'(by omega)
      else false
    if skip then
      chainWalkAllFast data prev pos maxLen hpm (prev[cand]'(by omega)) (fuel - 1) bestLen k
        slotBase lens dists hps hsl hsd
    else
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
    (symOffset : Nat) (table : Array Nat) (i : Nat)
    (hext : base.size ≤ extra.size) (hcl : symOffset + base.size ≤ codeLens.size) :
    Array Nat :=
  if h : i < base.size then
    let lo := base[i].toNat
    let hi := if h1 : i + 1 < base.size then base[i + 1].toNat else table.size
    let c := costOfLen (codeLens[symOffset + i]'(by omega)) + (extra[i]'(by omega)).toNat
    fillCostSlots base extra codeLens symOffset (fillCostRange table lo hi c) (i + 1) hext hcl
  else table
termination_by base.size - i
decreasing_by omega

/-- Fill the 256-entry literal cost table: `table[b] = costOfLen lens[b]`. -/
private def litCostLoop (lens table : Array Nat) (b : Nat) (hlen : 256 ≤ lens.size) :
    Array Nat :=
  if hb : b < 256 then
    litCostLoop lens (table.set! b (costOfLen (lens[b]'(by omega)))) (b + 1) hlen
  else table
termination_by 256 - b
decreasing_by omega

/-- `litCostLoop` only `set!`s, so it preserves the table size. -/
private theorem litCostLoop_size (lens table : Array Nat) (b : Nat) (hlen : 256 ≤ lens.size) :
    (litCostLoop lens table b hlen).size = table.size := by
  unfold litCostLoop
  by_cases hb : b < 256
  · simp only [hb, ↓reduceDIte]; rw [litCostLoop_size]; simp
  · simp only [hb, ↓reduceDIte]
termination_by 256 - b
decreasing_by omega

/-- Build the three dense cost tables from lit/len and distance code-length
    arrays (286 and 30 entries; longer is fine — fixed-Huffman tables have
    288/32). -/
def mkCostTables (litLens distLens : Array Nat)
    (hlit : 257 + Inflate.lengthBase.size ≤ litLens.size)
    (hdist : Inflate.distBase.size ≤ distLens.size) :
    Array Nat × Array Nat × Array Nat :=
  let litCost := litCostLoop litLens (Array.replicate 256 0) 0
    (by have := Inflate.lengthBase_size; omega)
  let lenCost := fillCostSlots Inflate.lengthBase Inflate.lengthExtra litLens 257
    (Array.replicate 259 badCost) 0 (by simp) hlit
  let distCost := fillCostSlots Inflate.distBase Inflate.distExtra distLens 0
    (Array.replicate 32769 badCost) 0 (by simp) (by omega)
  (litCost, lenCost, distCost)

/-- The literal cost table has exactly 256 entries (one per byte value). -/
private theorem mkCostTables_fst_size (litLens distLens : Array Nat)
    (hlit : 257 + Inflate.lengthBase.size ≤ litLens.size)
    (hdist : Inflate.distBase.size ≤ distLens.size) :
    (mkCostTables litLens distLens hlit hdist).1.size = 256 := by
  unfold mkCostTables
  simp only [litCostLoop_size, Array.size_replicate]

/-- Round-1 (static) cost model: fixed-Huffman code lengths (RFC 1951
    §3.2.6) — libdeflate's seeding choice. No dependence on a prior parse,
    so no seed-quality failure mode. -/
def staticCostTables : Array Nat × Array Nat × Array Nat :=
  mkCostTables (Inflate.fixedLitLengths.map (·.toNat))
    (Inflate.fixedDistLengths.map (·.toNat))
    (by simp only [Array.size_map, Inflate.fixedLitLengths, Array.size_append,
      Array.size_replicate, Inflate.lengthBase_size]; omega)
    (by simp only [Array.size_map, Inflate.fixedDistLengths,
      Array.size_replicate, Inflate.distBase_size]; omega)

/-- Cost tables fitted to a token stream: histogram (`tokenFreqs`) →
    length-limited Huffman code lengths (`dynamicCodeLengths`) → dense
    tables. Used for DP rounds after the first. -/
def fittedCostTables (tokens : Array LZ77Token) :
    Array Nat × Array Nat × Array Nat :=
  -- Dense histogram (#2622): pack the tokens (cheap bit-ops, no code lookup) and use
  -- the O(1) dense-table `tokenFreqsP` instead of the boxed `tokenFreqs`, whose
  -- `findLengthCode`/`findDistCode` are the *linear* search (6.9% of L9). Same
  -- histogram for the DP's valid matches (`unpackTok ∘ packTok = id`).
  let f := tokenFreqsP (tokens.map packTok)
  let lens := dynamicCodeLengths f.1 f.2
  have hlitsz : lens.1.toArray.size = 286 := by
    rw [List.size_toArray]; exact (dynamicCodeLengths_length f.1 f.2).1
  have hdistsz : lens.2.toArray.size = 30 := by
    rw [List.size_toArray]; exact (dynamicCodeLengths_length f.1 f.2).2
  mkCostTables lens.1.toArray lens.2.toArray
    (by rw [hlitsz]; have := Inflate.lengthBase_size; omega)
    (by rw [hdistsz]; have := Inflate.distBase_size; omega)

/-- Both cost-table builders produce a 256-entry literal table. -/
private theorem staticCostTables_fst_size : staticCostTables.1.size = 256 := by
  unfold staticCostTables; rw [mkCostTables_fst_size]

private theorem fittedCostTables_fst_size (tokens : Array LZ77Token) :
    (fittedCostTables tokens).1.size = 256 := by
  unfold fittedCostTables; rw [mkCostTables_fst_size]

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

/-- `seedTailCosts` only `set!`s, so it preserves the cost-array size. -/
private theorem seedTailCosts_size (cost : Array Nat) (r perByte j : Nat) :
    (seedTailCosts cost r perByte j).size = cost.size := by
  unfold seedTailCosts
  by_cases hj : j < 259
  · simp only [hj, ↓reduceIte]
    rw [seedTailCosts_size]; simp
  · simp only [hj, ↓reduceIte]
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
      -- These three reads stay panic-checked: the indices (`b` a length-base
      -- value, `dist` a cached distance, `i + b` a cost-array offset) are
      -- heuristic cache/table values whose bounds would require cache-content
      -- invariants the design deliberately keeps out of the proof boundary.
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
    -- The two cache-slot reads are structurally in range (`k < slots`, and the
    -- block `[slotBase, slotBase + slots)` fits the cache), but discharging that
    -- needs a length-preservation chain for the heuristic cache builder
    -- (`buildCache` → `chainWalkAllGuarded`), orthogonal to this conversion, so
    -- they stay panic-checked.
    let len := cacheLens[slotBase + k]!
    if len = 0 then (bestC, bestL, bestD)
    else
      let dist := cacheDists[slotBase + k]!
      -- Same as `scanBounds`: `len`/`dist` are cached values and `i + len` a
      -- cost-array offset — heuristic indices with no proven bound.
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
    (i : Nat) (cost chLen chDist : Array Nat)
    (hr : base + r ≤ data.size) (hlit : 256 ≤ litCost.size)
    (hcost : r + 259 ≤ cost.size) (hir : i ≤ r) :
    Array Nat × Array Nat :=
  if h0 : i = 0 then (chLen, chDist)
  else
    let idx := i - 1
    let pos := base + idx
    let byte := data[pos]'(by omega)
    let lit := litCost[byte.toNat]'(by have := UInt8.toNat_lt byte; omega) + cost[idx + 1]'(by omega)
    let (bc, bl, bd) := scanCands cacheLens cacheDists lenCost distCost cost
      (slots * idx) idx slots 0 0 lit 1 0
    let chLen := chLen.set! pos bl
    let chDist := chDist.set! pos bd
    fillRegion data base r slots cacheLens cacheDists litCost lenCost distCost
      idx (cost.set! idx bc) chLen chDist hr hlit
      (by simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]; exact hcost) (by omega)
termination_by i
decreasing_by omega

/-- `fillRegion` only `set!`s `chLen`/`chDist`, so it preserves their sizes. -/
private theorem fillRegion_fst_size (data : ByteArray) (base r slots : Nat)
    (cacheLens cacheDists litCost lenCost distCost : Array Nat) (i : Nat)
    (cost chLen chDist : Array Nat) (hr : base + r ≤ data.size) (hlit : 256 ≤ litCost.size)
    (hcost : r + 259 ≤ cost.size) (hir : i ≤ r) :
    (fillRegion data base r slots cacheLens cacheDists litCost lenCost distCost
      i cost chLen chDist hr hlit hcost hir).1.size = chLen.size := by
  unfold fillRegion
  by_cases h0 : i = 0
  · simp only [h0, ↓reduceDIte]
  · simp only [h0, ↓reduceDIte]; rw [fillRegion_fst_size]; simp
termination_by i
decreasing_by omega

private theorem fillRegion_snd_size (data : ByteArray) (base r slots : Nat)
    (cacheLens cacheDists litCost lenCost distCost : Array Nat) (i : Nat)
    (cost chLen chDist : Array Nat) (hr : base + r ≤ data.size) (hlit : 256 ≤ litCost.size)
    (hcost : r + 259 ≤ cost.size) (hir : i ≤ r) :
    (fillRegion data base r slots cacheLens cacheDists litCost lenCost distCost
      i cost chLen chDist hr hlit hcost hir).2.size = chDist.size := by
  unfold fillRegion
  by_cases h0 : i = 0
  · simp only [h0, ↓reduceDIte]
  · simp only [h0, ↓reduceDIte]; rw [fillRegion_snd_size]; simp
termination_by i
decreasing_by omega

/-- Collect the region's parse implied by the current choice arrays (used to
    refit the cost model between DP rounds). Heuristic walk — no guards. -/
def collectRegionTokens (data : ByteArray) (chLen chDist : Array Nat)
    (bound pos : Nat) (acc : Array LZ77Token)
    (hchL : data.size ≤ chLen.size) (hchD : data.size ≤ chDist.size) : Array LZ77Token :=
  if h : pos < bound ∧ pos < data.size then
    let len := chLen[pos]'(by omega)
    if hl : 3 ≤ len then
      collectRegionTokens data chLen chDist bound (pos + len)
        (acc.push (.reference len (chDist[pos]'(by omega)))) hchL hchD
    else
      collectRegionTokens data chLen chDist bound (pos + 1)
        (acc.push (.literal (data[pos]'(by omega)))) hchL hchD
  else acc
termination_by bound - pos
decreasing_by all_goals omega

/-- Run the candidate-cache + two-round DP over one region and write its
    choices. Round 1 prices with the static tables; round 2 refits to the
    region's own round-1 parse. Returns the updated chain state and choice
    arrays. -/
def fillRegionRounds (data : ByteArray) (depth slots base r : Nat)
    (slit slen sdist : Array Nat) (hashTable prev chLen chDist : Array Nat)
    (hr : base + r ≤ data.size) (hslit : 256 ≤ slit.size)
    (hchL : data.size ≤ chLen.size) (hchD : data.size ≤ chDist.size) :
    Array Nat × Array Nat × Array Nat × Array Nat :=
  let cache := buildCache data hashTable prev
    depth slots base r 0 (Array.replicate (slots * r) 0) (Array.replicate (slots * r) 0)
  let cacheLens := cache.1
  let cacheDists := cache.2.1
  let hashTable := cache.2.2.1
  let prev := cache.2.2.2
  -- round 1: static cost model
  let cost := seedTailCosts (Array.replicate (r + 259) 0) r (avgLitBits slit) 0
  have hcost1 : r + 259 ≤ cost.size := by
    show r + 259 ≤ (seedTailCosts (Array.replicate (r + 259) 0) r (avgLitBits slit) 0).size
    rw [seedTailCosts_size, Array.size_replicate]; omega
  let res1 := fillRegion data base r slots cacheLens cacheDists
    slit slen sdist r cost chLen chDist hr hslit hcost1 (Nat.le_refl r)
  have hchL1 : data.size ≤ res1.1.size :=
    Nat.le_trans hchL (Nat.le_of_eq (fillRegion_fst_size data base r slots cacheLens cacheDists
      slit slen sdist r cost chLen chDist hr hslit hcost1 (Nat.le_refl r)).symm)
  have hchD1 : data.size ≤ res1.2.size :=
    Nat.le_trans hchD (Nat.le_of_eq (fillRegion_snd_size data base r slots cacheLens cacheDists
      slit slen sdist r cost chLen chDist hr hslit hcost1 (Nat.le_refl r)).symm)
  -- round 2: refit to this region's round-1 parse
  let toks := collectRegionTokens data res1.1 res1.2 (base + r) base #[] hchL1 hchD1
  let fitted := fittedCostTables toks
  have hflit : 256 ≤ fitted.1.size := Nat.le_of_eq (fittedCostTables_fst_size toks).symm
  let cost2 := seedTailCosts (Array.replicate (r + 259) 0) r (avgLitBits fitted.1) 0
  have hcost2 : r + 259 ≤ cost2.size := by
    show r + 259 ≤ (seedTailCosts (Array.replicate (r + 259) 0) r (avgLitBits fitted.1) 0).size
    rw [seedTailCosts_size, Array.size_replicate]; omega
  let res2 := fillRegion data base r slots cacheLens cacheDists
    fitted.1 fitted.2.1 fitted.2.2 r cost2 res1.1 res1.2 hr hflit hcost2 (Nat.le_refl r)
  (hashTable, prev, res2.1, res2.2)

/-- `fillRegionRounds` only `set!`s the choice arrays, so it preserves their
    sizes (both DP rounds go through `fillRegion`). -/
private theorem fillRegionRounds_chLen_size (data : ByteArray) (depth slots base r : Nat)
    (slit slen sdist : Array Nat) (hashTable prev chLen chDist : Array Nat)
    (hr : base + r ≤ data.size) (hslit : 256 ≤ slit.size)
    (hchL : data.size ≤ chLen.size) (hchD : data.size ≤ chDist.size) :
    (fillRegionRounds data depth slots base r slit slen sdist hashTable prev chLen chDist
      hr hslit hchL hchD).2.2.1.size = chLen.size := by
  unfold fillRegionRounds
  simp only [fillRegion_fst_size]

private theorem fillRegionRounds_chDist_size (data : ByteArray) (depth slots base r : Nat)
    (slit slen sdist : Array Nat) (hashTable prev chLen chDist : Array Nat)
    (hr : base + r ≤ data.size) (hslit : 256 ≤ slit.size)
    (hchL : data.size ≤ chLen.size) (hchD : data.size ≤ chDist.size) :
    (fillRegionRounds data depth slots base r slit slen sdist hashTable prev chLen chDist
      hr hslit hchL hchD).2.2.2.size = chDist.size := by
  unfold fillRegionRounds
  simp only [fillRegion_snd_size]

/-- Region driver for `computeChoices`: regions advance by
    `min regionSize (data.size - base)` bytes; the hash-chain state persists
    across regions (cross-region distances are legal and wanted).

    Recurses on explicit `fuel` (structural) rather than `data.size - base`
    (well-founded): the per-region proof `hr : base + r ≤ data.size` passed to
    `fillRegionRounds` depends on the recursion variable `base`, which makes the
    well-founded elaborator try to reduce the `fillRegionRounds` scrutinee and
    diverge. With `fuel = data.size` (≥ the region count, since each region
    advances `base` by `r ≥ 1`) the guard always fails before fuel runs out, so
    the result is identical to the unfueled loop. Marked `private`: the fuel
    parameter is a footgun (too little fuel silently yields a partial fill), so
    only `computeChoices` (which passes `data.size`) may call it. -/
private def computeChoicesLoop (data : ByteArray) (depth slots regionSize : Nat)
    (slit slen sdist : Array Nat) (hashTable prev : Array Nat) (base : Nat)
    (chLen chDist : Array Nat) (hslit : 256 ≤ slit.size)
    (hchL : data.size ≤ chLen.size) (hchD : data.size ≤ chDist.size) (fuel : Nat) :
    Array Nat × Array Nat :=
  match fuel with
  | 0 => (chLen, chDist)
  | fuel + 1 =>
    if hb : base < data.size ∧ 0 < regionSize then
      let r := min regionSize (data.size - base)
      have hr : base + r ≤ data.size := by omega
      let result := fillRegionRounds data depth slots base r
        slit slen sdist hashTable prev chLen chDist hr hslit hchL hchD
      have hchL' : data.size ≤ result.2.2.1.size := Nat.le_trans hchL
        (Nat.le_of_eq (fillRegionRounds_chLen_size data depth slots base r slit slen sdist
          hashTable prev chLen chDist hr hslit hchL hchD).symm)
      have hchD' : data.size ≤ result.2.2.2.size := Nat.le_trans hchD
        (Nat.le_of_eq (fillRegionRounds_chDist_size data depth slots base r slit slen sdist
          hashTable prev chLen chDist hr hslit hchL hchD).symm)
      computeChoicesLoop data depth slots regionSize slit slen sdist result.1 result.2.1
        (base + r) result.2.2.1 result.2.2.2 hslit hchL' hchD' fuel
    else (chLen, chDist)

/-- Compute the global DP choice arrays for the whole input: per region,
    build the candidate cache and run the two-round backward DP. Defaults
    `(1, 0)` = literal everywhere, so unfilled entries are always safe.
    Heuristic only: consumed by the re-verifying emitter `optimalEmit`. -/
def computeChoices (data : ByteArray) : Array Nat × Array Nat :=
  let st := staticCostTables
  computeChoicesLoop data optChainDepth optCacheSlots optRegionSize st.1 st.2.1 st.2.2
    (Array.replicate 65536 data.size) (Array.replicate data.size data.size)
    0 (Array.replicate data.size 1) (Array.replicate data.size 0)
    (by have h : st.1.size = 256 := staticCostTables_fst_size; omega)
    (by simp) (by simp) data.size

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
    -- `chLen`/`chDist` are *arbitrary* choice arrays here (the correctness
    -- theorems in `LZ77OptimalCorrect` quantify over them with no size
    -- hypothesis), so there is no `pos < chLen.size` to capture: these reads
    -- stay panic-checked by design. The emitted token is re-verified below.
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
    -- As in `optimalEmit`: arbitrary choice arrays, so these reads stay
    -- panic-checked; the emitted token is re-verified below.
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
