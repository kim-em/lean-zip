import Zip.Native.Deflate
import Zip.Native.DeflateDynamic

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
      let head := hashTable[h]!
      let hashTable := hashTable.set! h pos
      let prev := prev.set! pos head
      let maxLen := min 258 (data.size - pos)
      have hpm : pos + maxLen ≤ data.size := by omega
      let (lens, dists) := chainWalkAll data prev pos maxLen hpm head depth
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

end Zip.Native.Deflate
