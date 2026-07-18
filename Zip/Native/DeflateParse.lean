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

/-- Skip-ahead threshold for `buildCache` (#2740, libdeflate's
    `nice_len` skip): once the deepest candidate recorded at a position
    reaches this length, the match interior — the next `bestLen - 1`
    positions — is only hash-inserted into the chains, never searched or
    cached. A long repeated region then costs one chain walk instead of one
    per byte (the match finder is ~70% of the L9/L10 cost). The DP still sees
    the long match at its start position, so it can take it and jump the
    interior; interior positions with no cached candidate fall back to a
    literal or a shorter step. Pure ratio/speed knob — the emitter re-verifies
    every match, so this is ratio-risk only.

    Level 10 (exact DP). Swept on the Silesia geomean: `64` sits at the knee —
    ~2.5× on xml, ~1.8× on nci for +0.3% geomean ratio; dropping to 48 falls off
    a cliff (nci +5.3%) as length-48–64 matches start being skipped. -/
def optNiceSkip : Nat := 64

/-- `optNiceSkip` for the L9-fast tier (`computeChoicesFast`). Separate from
    the level-10 value so each tier's speed/ratio balance can be swept
    independently. The L9 matcher is shallower (`fastChainDepth = 64`, single
    round), so skipping saves less and costs proportionally more ratio; `128`
    keeps the Silesia geomean under budget (~+0.45%) while still buying ~1.5× on
    xml. Pure ratio/speed knob. -/
def fastNiceSkip : Nat := 128

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
    (lens dists : Array Nat) : Array Nat × Array Nat × Nat :=
  if fuel = 0 then (lens, dists, bestLen)
  else if optCacheSlots ≤ k then (lens, dists, bestLen)
  else if hc : cand < pos ∧ pos - cand ≤ 32768 then
    have hcand : cand + maxLen ≤ data.size := by omega
    -- Prefilter (#2622): mirror of `chainWalkAllFast` — skip the compare when the
    -- byte at offset `bestLen` mismatches (the candidate can't beat `bestLen`).
    -- The byte reads are proven-bounds (`bestLen < maxLen` plus `hcand`/`hpm`);
    -- the chain reads below stay panic-checked because this is the fallback
    -- reference, invoked by `chainWalkAllGuarded` precisely when the
    -- `min chainWinSize data.size ≤ prev.size` invariant cannot be established (the
    -- proven-bounds hot path is `chainWalkAllFast`).
    let skip : Bool := if hbl : bestLen < maxLen then
        data[cand + bestLen]'(by omega) != data[pos + bestLen]'(by omega) else false
    if skip then
      chainWalkAll data prev pos maxLen hpm prev[cand &&& 0x7FFF]! (fuel - 1) bestLen k slotBase lens dists
    else
    let ml := lz77Greedy.countMatch data cand pos maxLen hcand hpm
    if 3 ≤ ml ∧ bestLen < ml then
      let lens := lens.set! (slotBase + k) ml
      let dists := dists.set! (slotBase + k) (pos - cand)
      if min optNiceLen maxLen ≤ ml then (lens, dists, ml)
      else chainWalkAll data prev pos maxLen hpm prev[cand &&& 0x7FFF]! (fuel - 1) ml (k + 1)
        slotBase lens dists
    else
      chainWalkAll data prev pos maxLen hpm prev[cand &&& 0x7FFF]! (fuel - 1) bestLen k
        slotBase lens dists
  else (lens, dists, bestLen)
termination_by fuel
decreasing_by all_goals omega

/-- Proven-bounds copy of `chainWalkAll` (Wave 3 Step 0.1, same generational
    pattern as `chainWalkFast`/`updateHashesFast` in `Deflate.lean`):
    the circular `prev[cand &&& 0x7FFF]` is in range because the mask gives
    `cand &&& 0x7FFF < chainWinSize` and `hps : min chainWinSize data.size ≤ prev.size`; the
    slot writes are in range because the slot
    guard gives `k < optCacheSlots` and `hsl`/`hsd` bound the whole slot
    block. Once established, the three hypotheses discharge every access in
    the loop statically. -/
def chainWalkAllFast (data : ByteArray) (prev : Array Nat) (pos maxLen : Nat)
    (hpm : pos + maxLen ≤ data.size) (cand fuel bestLen k slotBase : Nat)
    (lens dists : Array Nat) (hps : min chainWinSize data.size ≤ prev.size)
    (hsl : slotBase + optCacheSlots ≤ lens.size)
    (hsd : slotBase + optCacheSlots ≤ dists.size) : Array Nat × Array Nat × Nat :=
  if fuel = 0 then (lens, dists, bestLen)
  else if hk : optCacheSlots ≤ k then (lens, dists, bestLen)
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
      chainWalkAllFast data prev pos maxLen hpm (prev[cand &&& 0x7FFF]'(by have := winMask_lt cand; have := Nat.and_le_left (n := cand) (m := 0x7FFF); omega)) (fuel - 1) bestLen k
        slotBase lens dists hps hsl hsd
    else
    let ml := lz77Greedy.countMatch data cand pos maxLen hcand hpm
    if 3 ≤ ml ∧ bestLen < ml then
      have hbl : slotBase + k < lens.size := by omega
      have hbd : slotBase + k < dists.size := by omega
      if min optNiceLen maxLen ≤ ml then
        (lens.set (slotBase + k) ml hbl, dists.set (slotBase + k) (pos - cand) hbd, ml)
      else chainWalkAllFast data prev pos maxLen hpm (prev[cand &&& 0x7FFF]'(by have := winMask_lt cand; have := Nat.and_le_left (n := cand) (m := 0x7FFF); omega)) (fuel - 1) ml (k + 1)
        slotBase (lens.set (slotBase + k) ml hbl) (dists.set (slotBase + k) (pos - cand) hbd)
        hps (by simpa using hsl) (by simpa using hsd)
    else
      chainWalkAllFast data prev pos maxLen hpm (prev[cand &&& 0x7FFF]'(by have := winMask_lt cand; have := Nat.and_le_left (n := cand) (m := 0x7FFF); omega)) (fuel - 1) bestLen k
        slotBase lens dists hps hsl hsd
  else (lens, dists, bestLen)
termination_by fuel
decreasing_by all_goals omega

/-- One runtime check (`min chainWinSize data.size ≤ prev.size` plus the slot block fitting in
    `lens`/`dists`) guards the whole `chainWalkAllFast` walk; the fallback is
    the original panic-checked `chainWalkAll` (unreachable in practice —
    `buildCache` callers give `prev` the fixed 32768-entry ring and the cache
    arrays `slots * r`), so the wrapper is value-identical to `chainWalkAll`. -/
@[inline] def chainWalkAllGuarded (data : ByteArray) (prev : Array Nat) (pos maxLen : Nat)
    (hpm : pos + maxLen ≤ data.size) (cand fuel bestLen k slotBase : Nat)
    (lens dists : Array Nat) : Array Nat × Array Nat × Nat :=
  if hg : min chainWinSize data.size ≤ prev.size ∧ slotBase + optCacheSlots ≤ lens.size ∧
      slotBase + optCacheSlots ≤ dists.size then
    chainWalkAllFast data prev pos maxLen hpm cand fuel bestLen k slotBase lens dists
      hg.1 hg.2.1 hg.2.2
  else
    chainWalkAll data prev pos maxLen hpm cand fuel bestLen k slotBase lens dists

/-- `chainWalkAll` only `set!`s the cache arrays, so it preserves their sizes. -/
private theorem chainWalkAll_fst_size (data : ByteArray) (prev : Array Nat) (pos maxLen : Nat)
    (hpm : pos + maxLen ≤ data.size) (cand fuel bestLen k slotBase : Nat) (lens dists : Array Nat) :
    (chainWalkAll data prev pos maxLen hpm cand fuel bestLen k slotBase lens dists).1.size =
      lens.size := by
  fun_induction chainWalkAll data prev pos maxLen hpm cand fuel bestLen k slotBase lens dists <;>
    simp_all (config := { zetaDelta := true })

private theorem chainWalkAll_snd_size (data : ByteArray) (prev : Array Nat) (pos maxLen : Nat)
    (hpm : pos + maxLen ≤ data.size) (cand fuel bestLen k slotBase : Nat) (lens dists : Array Nat) :
    (chainWalkAll data prev pos maxLen hpm cand fuel bestLen k slotBase lens dists).2.1.size =
      dists.size := by
  fun_induction chainWalkAll data prev pos maxLen hpm cand fuel bestLen k slotBase lens dists <;>
    simp_all (config := { zetaDelta := true })

/-- `chainWalkAllFast` only `set`s the cache arrays, so it preserves their sizes. -/
private theorem chainWalkAllFast_fst_size (data : ByteArray) (prev : Array Nat) (pos maxLen : Nat)
    (hpm : pos + maxLen ≤ data.size) (cand fuel bestLen k slotBase : Nat) (lens dists : Array Nat)
    (hps : min chainWinSize data.size ≤ prev.size) (hsl : slotBase + optCacheSlots ≤ lens.size)
    (hsd : slotBase + optCacheSlots ≤ dists.size) :
    (chainWalkAllFast data prev pos maxLen hpm cand fuel bestLen k slotBase lens dists
      hps hsl hsd).1.size = lens.size := by
  fun_induction chainWalkAllFast data prev pos maxLen hpm cand fuel bestLen k slotBase lens dists
    hps hsl hsd <;> simp_all (config := { zetaDelta := true }) [Array.size_set]

private theorem chainWalkAllFast_snd_size (data : ByteArray) (prev : Array Nat) (pos maxLen : Nat)
    (hpm : pos + maxLen ≤ data.size) (cand fuel bestLen k slotBase : Nat) (lens dists : Array Nat)
    (hps : min chainWinSize data.size ≤ prev.size) (hsl : slotBase + optCacheSlots ≤ lens.size)
    (hsd : slotBase + optCacheSlots ≤ dists.size) :
    (chainWalkAllFast data prev pos maxLen hpm cand fuel bestLen k slotBase lens dists
      hps hsl hsd).2.1.size = dists.size := by
  fun_induction chainWalkAllFast data prev pos maxLen hpm cand fuel bestLen k slotBase lens dists
    hps hsl hsd <;> simp_all (config := { zetaDelta := true }) [Array.size_set]

/-- `chainWalkAllGuarded` dispatches to two size-preserving walks, so it too
    preserves the cache-array sizes. -/
private theorem chainWalkAllGuarded_fst_size (data : ByteArray) (prev : Array Nat)
    (pos maxLen : Nat) (hpm : pos + maxLen ≤ data.size) (cand fuel bestLen k slotBase : Nat)
    (lens dists : Array Nat) :
    (chainWalkAllGuarded data prev pos maxLen hpm cand fuel bestLen k slotBase lens dists).1.size =
      lens.size := by
  unfold chainWalkAllGuarded
  split
  · exact chainWalkAllFast_fst_size ..
  · exact chainWalkAll_fst_size ..

private theorem chainWalkAllGuarded_snd_size (data : ByteArray) (prev : Array Nat)
    (pos maxLen : Nat) (hpm : pos + maxLen ≤ data.size) (cand fuel bestLen k slotBase : Nat)
    (lens dists : Array Nat) :
    (chainWalkAllGuarded data prev pos maxLen hpm cand fuel bestLen k slotBase lens dists).2.1.size =
      dists.size := by
  unfold chainWalkAllGuarded
  split
  · exact chainWalkAllFast_snd_size ..
  · exact chainWalkAll_snd_size ..

/-- Hash-insert positions `[base + j, base + stop)` into the chains without
    searching or caching them — libdeflate's `bt_matchfinder_skip_byte`, used
    for the interior of a long match. Later positions can still find matches
    reaching back into the skipped span (the chain stays complete), but the
    span itself costs no chain walk. Both tables are updated: the hash4-keyed
    chain (`hashTable`/`prev`) and the hash3 singleton (`h3tab`) — mirroring
    the dual-table scheme of the search path (#2742). Stops early at the first
    position too close to the end to hash (positions only advance, so all
    later ones are too). Heuristic — only mutates the finder state, never the
    cache. -/
def insertChainRange (data : ByteArray) (hashTable prev h3tab : Array Nat)
    (base j stop : Nat) : Array Nat × Array Nat × Array Nat :=
  if j < stop then
    let pos := base + j
    if hlt : pos + 2 < data.size then
      let h := lz77Greedy.hash3 data pos 65536 hlt
      let head := headProbeGuarded hashTable h
      let hashTable := guardedSet hashTable h pos
      let prev := guardedSet prev (pos &&& 0x7FFF) head
      let h3tab := guardedSet h3tab (hash3Single data pos hlt) pos
      insertChainRange data hashTable prev h3tab base (j + 1) stop
    else (hashTable, prev, h3tab)
  else (hashTable, prev, h3tab)
termination_by stop - j
decreasing_by omega

/-- Build the candidate cache for region `[base, base + r)`: **every** position
    is inserted into the hash chains (the DP can land anywhere, so the chain
    must stay complete), and every *searched* position also records its
    candidate frontier. The one exception is the interior of a long match, which
    is inserted but not searched or cached (see skip-ahead below).
    `hashTable`/`prev` are the same global chain state `lz77Chain` uses
    (sentinel `data.size`), threaded across regions so distances legally
    reach up to 32 KiB into prior regions. Returns the filled cache and the
    updated finder state.

    Dual hash4 + hash3 finder (#2742, libdeflate `hc_matchfinder.h`): the
    chains are keyed on the **4-byte** hash (`lz77Greedy.hash3`), so every
    chain candidate can extend to length ≥ 4 — plain hash4 chains alone cost
    ratio here (x-ray +7.4%, ooffice +3.5%, the #2620 note) because the
    ratio-maximising DP must also see length-3 candidates. Those come from the
    `h3tab` **singleton** (most recent position per 15-bit 3-byte-hash
    bucket): `hash3Probe` verifies its candidate and, on a hit, it is
    recorded as slot 0 with length exactly 3 and seeds the walk's `bestLen`,
    so the chain then records only strictly longer candidates — the frontier
    stays strictly increasing with the length-3 point restored. On a miss the
    slot-0 write is `lens[slot] := 0` (a no-op: each position's slot block is
    untouched before its own search, and a zero length terminates the block,
    so the paired garbage distance is never read).

    `depth`/`slots`/`niceSkip` are passed as parameters (callers supply
    `optChainDepth`/`optCacheSlots`/`optNiceSkip`): literal constants in the
    body make the well-founded elaboration attempt deep reduction of the
    `chainWalkAll` application and blow the recursion limit.

    Skip-ahead (#2740): when the deepest candidate recorded at a position
    reaches `niceSkip`, the interior of that match — the next `bestLen - 1`
    positions, clamped to the region end — is only hash-inserted into the
    chains (`insertChainRange`), never searched or cached, and the search
    resumes past it. This is libdeflate's `nice_len` skip: a long repeated
    region costs one chain walk instead of one per byte, at a small ratio
    cost (the DP sees the long match at its start and takes it; interior
    positions with no cached candidate fall back to a literal). -/
def buildCache (data : ByteArray) (hashTable : Array Nat) (prev : Array Nat)
    (h3tab : Array Nat) (depth slots niceSkip base r j : Nat)
    (lens dists : Array Nat) :
    Array Nat × Array Nat × Array Nat × Array Nat × Array Nat :=
  if hj : j < r then
    let pos := base + j
    if hlt : pos + 2 < data.size then
      let h := lz77Greedy.hash3 data pos 65536 hlt
      let head := headProbeGuarded hashTable h
      let hashTable := guardedSet hashTable h pos
      let prev := guardedSet prev (pos &&& 0x7FFF) head
      let h3 := hash3Single data pos hlt
      let cand3 := headProbeGuarded h3tab h3
      let h3tab := guardedSet h3tab h3 pos
      let seed := hash3Probe data 32768 pos cand3 hlt
      let bl0 := seed % 512
      let bp0 := seed / 512
      let lens := lens.set! (slots * j) bl0
      let dists := dists.set! (slots * j) (pos - bp0)
      let k0 := if bl0 = 0 then 0 else 1
      let maxLen := min 258 (data.size - pos)
      have hpm : pos + maxLen ≤ data.size := by omega
      let cache := chainWalkAllGuarded data prev pos maxLen hpm head depth
        bl0 k0 (slots * j) lens dists
      -- `cache.2.2` is the longest match the walk found at `pos` (it threads the
      -- running best out), so the skip decision costs nothing beyond the walk.
      let best := cache.2.2
      if hsk : niceSkip ≤ best ∧ 1 ≤ best then
        -- skip the match interior: hash-insert positions `(j, j + best)` only,
        -- then resume the search at `j + best`. The interior insert is clamped
        -- to the region end (`min (j + best) r`) so no next-region position is
        -- inserted twice; if `j + best ≥ r` the resumed call returns at once.
        let hp := insertChainRange data hashTable prev h3tab base (j + 1) (min (j + best) r)
        buildCache data hp.1 hp.2.1 hp.2.2 depth slots niceSkip base r (j + best) cache.1 cache.2.1
      else
        buildCache data hashTable prev h3tab depth slots niceSkip base r (j + 1) cache.1 cache.2.1
    else
      buildCache data hashTable prev h3tab depth slots niceSkip base r (j + 1) lens dists
  else (lens, dists, hashTable, prev, h3tab)
termination_by r - j
decreasing_by
  -- The `j + 1` calls close by plain omega. The skip call recurses at
  -- `j + best`: rewrite `r - (j + best)` to `(r - j) - best` and apply
  -- `Nat.sub_lt` with `0 < r - j` (from `hj`) and `0 < best` (from `hsk`) —
  -- omega will not decompose the `r - j` measure atom on its own.
  all_goals first
    | omega
    | (rw [Nat.sub_add_eq]; exact Nat.sub_lt (Nat.sub_pos_of_lt hj) hsk.2)

/-- `buildCache` only feeds the cache arrays through `chainWalkAllGuarded`
    (size-preserving), so the returned `lens`/`dists` keep their input sizes.
    This is the chain that lets `fillRegion`/`scanCands` read the cache slots
    with proven bounds. -/
private theorem buildCache_fst_size (data : ByteArray) (hashTable prev h3tab : Array Nat)
    (depth slots niceSkip base r j : Nat) (lens dists : Array Nat) :
    (buildCache data hashTable prev h3tab depth slots niceSkip base r j lens dists).1.size = lens.size := by
  fun_induction buildCache data hashTable prev h3tab depth slots niceSkip base r j lens dists <;>
    simp_all (config := { zetaDelta := true }) [chainWalkAllGuarded_fst_size]

private theorem buildCache_snd_fst_size (data : ByteArray) (hashTable prev h3tab : Array Nat)
    (depth slots niceSkip base r j : Nat) (lens dists : Array Nat) :
    (buildCache data hashTable prev h3tab depth slots niceSkip base r j lens dists).2.1.size =
      dists.size := by
  fun_induction buildCache data hashTable prev h3tab depth slots niceSkip base r j lens dists <;>
    simp_all (config := { zetaDelta := true }) [chainWalkAllGuarded_snd_size]

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

/-- `lengthBoundaryStart[v]` is the smallest length-code slot `s` with
    `lengthBase[s] > v` (equivalently, the count of length bases `≤ v`),
    `29` if none. `Inflate.lengthBase` is sorted ascending, so this is the
    first slot a covered interval `(v, len)` can include — `scanBounds`
    starts its scan here instead of from slot 0, skipping the boundaries that
    cannot qualify. Indexed by the previous candidate length, `0..258`. -/
def lengthBoundaryStart : Array Nat :=
  Array.ofFn (n := 259) fun v =>
    (Inflate.lengthBase.filter fun b => decide (b.toNat ≤ v.val)).size

/-- Evaluate one candidate at the length-code lower boundaries inside
    `(prevLen, len)` (its covered interval, exclusive of `len` which the
    caller already evaluated): truncating a match to a boundary can buy a
    cheaper length code or a better continuation. `(bestC, bestL, bestD)`
    is the running arg-min.

    The caller starts `s` at `lengthBoundaryStart[prevLen]`, the first slot
    with `lengthBase[s] > prevLen`, so the lower bound `prevLen < b` already
    holds for every slot scanned (`lengthBase` ascending). Only the upper
    bound `b < len` is tested, and once it fails the scan stops — all later
    slots have an even larger base. Same boundaries, same order, same
    arg-min as a full `0..28` scan with the `prevLen < b ∧ b < len`
    predicate, just without the iterations that cannot qualify. -/
def scanBounds (lenCost distCost cost : Array Nat) (i dist len s : Nat)
    (bestC bestL bestD : Nat) : Nat × Nat × Nat :=
  if h : s < Inflate.lengthBase.size then
    let b := Inflate.lengthBase[s].toNat
    if b < len then
      -- These three reads stay panic-checked: the indices (`b` a length-base
      -- value, `dist` a cached distance, `i + b` a cost-array offset) are
      -- heuristic cache/table values whose bounds would require cache-content
      -- invariants the design deliberately keeps out of the proof boundary.
      let c := lenCost[b]! + distCost[dist]! + cost[i + b]!
      if c < bestC then
        scanBounds lenCost distCost cost i dist len (s + 1) c b dist
      else
        scanBounds lenCost distCost cost i dist len (s + 1) bestC bestL bestD
    else (bestC, bestL, bestD)
  else (bestC, bestL, bestD)
termination_by Inflate.lengthBase.size - s
decreasing_by all_goals omega

-- The dependent cache-size hypotheses deepen the well-founded elaboration past
-- the default recursion limit (as for several defs in `Inflate.lean`).
set_option maxRecDepth 4096 in
/-- Scan the candidate slots of region-local position `i` (cache block at
    `slotBase`), evaluating each candidate at its full length and at the
    length-code boundaries of its covered interval. Slots hold strictly
    increasing lengths; a zero length terminates the block.

    The two cache-slot reads are proven in range: the slot guard gives
    `k < slots` and `hcl`/`hcd` bound the whole slot block
    `[slotBase, slotBase + slots)` inside the cache arrays (`buildCache`
    sizes them `slots * r`; the bound is threaded from `fillRegion`). -/
def scanCands (cacheLens cacheDists lenCost distCost cost : Array Nat)
    (slotBase i slots k prevLen : Nat) (bestC bestL bestD : Nat)
    (hcl : slotBase + slots ≤ cacheLens.size) (hcd : slotBase + slots ≤ cacheDists.size) :
    Nat × Nat × Nat :=
  if _h : k < slots then
    let len := cacheLens[slotBase + k]'(by omega)
    if len = 0 then (bestC, bestL, bestD)
    else
      let dist := cacheDists[slotBase + k]'(by omega)
      -- Same as `scanBounds`: `len`/`dist` are cached values and `i + len` a
      -- cost-array offset — heuristic indices with no proven bound.
      let cFull := lenCost[len]! + distCost[dist]! + cost[i + len]!
      let (bestC, bestL, bestD) :=
        if cFull < bestC then (cFull, len, dist) else (bestC, bestL, bestD)
      -- `lengthBoundaryStart[prevLen]!` stays panic-checked like the value
      -- reads above: `prevLen` is `0` or a prior cached `len`, both `≤ 258`
      -- (matches are capped at the DEFLATE maximum), so it indexes the
      -- 259-entry table in range — the same bound `lenCost[len]!` already
      -- assumes for the current `len`.
      let (bestC, bestL, bestD) :=
        scanBounds lenCost distCost cost i dist len (lengthBoundaryStart[prevLen]!) bestC bestL bestD
      scanCands cacheLens cacheDists lenCost distCost cost slotBase i slots
        (k + 1) len bestC bestL bestD hcl hcd
  else (bestC, bestL, bestD)
termination_by slots - k
decreasing_by all_goals omega

-- As `scanCands`: the extra cache-size hypotheses deepen WF elaboration.
set_option maxRecDepth 4096 in
/-- Backward DP fill for region `[base, base + r)`: process region-local
    index `i - 1` down to 0, choosing literal vs the best cached candidate
    and recording the choice at the *absolute* position in `chLen`/`chDist`.
    Heuristic only — the emitter re-verifies everything. -/
def fillRegion (data : ByteArray) (base r slots : Nat)
    (cacheLens cacheDists litCost lenCost distCost : Array Nat)
    (i : Nat) (cost chLen chDist : Array Nat)
    (hr : base + r ≤ data.size) (hlit : 256 ≤ litCost.size)
    (hcost : r + 259 ≤ cost.size) (hir : i ≤ r)
    (hcl : slots * r ≤ cacheLens.size) (hcd : slots * r ≤ cacheDists.size) :
    Array Nat × Array Nat :=
  if h0 : i = 0 then (chLen, chDist)
  else
    let idx := i - 1
    let pos := base + idx
    let byte := data[pos]'(by omega)
    let lit := litCost[byte.toNat]'(by have := UInt8.toNat_lt byte; omega) + cost[idx + 1]'(by omega)
    -- The candidate block `[slots * idx, slots * idx + slots)` fits the cache:
    -- `idx + 1 ≤ r` gives `slots * (idx + 1) = slots * idx + slots ≤ slots * r`,
    -- and `slots * r` bounds both arrays (`hcl`/`hcd`, threaded from the
    -- `slots * r`-sized `buildCache`). `omega` then chains these linear facts.
    have hidx : idx + 1 ≤ r := by omega
    have hm := Nat.mul_le_mul (Nat.le_refl slots) hidx
    have heq : slots * (idx + 1) = slots * idx + slots := Nat.mul_succ slots idx
    let (bc, bl, bd) := scanCands cacheLens cacheDists lenCost distCost cost
      (slots * idx) idx slots 0 0 lit 1 0 (by omega) (by omega)
    let chLen := chLen.set! pos bl
    let chDist := chDist.set! pos bd
    fillRegion data base r slots cacheLens cacheDists litCost lenCost distCost
      idx (cost.set! idx bc) chLen chDist hr hlit
      (by simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]; exact hcost) (by omega)
      hcl hcd
termination_by i
decreasing_by omega

/-- `fillRegion` only `set!`s `chLen`/`chDist`, so it preserves their sizes. -/
private theorem fillRegion_fst_size (data : ByteArray) (base r slots : Nat)
    (cacheLens cacheDists litCost lenCost distCost : Array Nat) (i : Nat)
    (cost chLen chDist : Array Nat) (hr : base + r ≤ data.size) (hlit : 256 ≤ litCost.size)
    (hcost : r + 259 ≤ cost.size) (hir : i ≤ r)
    (hcl : slots * r ≤ cacheLens.size) (hcd : slots * r ≤ cacheDists.size) :
    (fillRegion data base r slots cacheLens cacheDists litCost lenCost distCost
      i cost chLen chDist hr hlit hcost hir hcl hcd).1.size = chLen.size := by
  unfold fillRegion
  by_cases h0 : i = 0
  · simp only [h0, ↓reduceDIte]
  · simp only [h0, ↓reduceDIte]; rw [fillRegion_fst_size]; simp
termination_by i
decreasing_by omega

private theorem fillRegion_snd_size (data : ByteArray) (base r slots : Nat)
    (cacheLens cacheDists litCost lenCost distCost : Array Nat) (i : Nat)
    (cost chLen chDist : Array Nat) (hr : base + r ≤ data.size) (hlit : 256 ≤ litCost.size)
    (hcost : r + 259 ≤ cost.size) (hir : i ≤ r)
    (hcl : slots * r ≤ cacheLens.size) (hcd : slots * r ≤ cacheDists.size) :
    (fillRegion data base r slots cacheLens cacheDists litCost lenCost distCost
      i cost chLen chDist hr hlit hcost hir hcl hcd).2.size = chDist.size := by
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
def fillRegionRounds (data : ByteArray) (depth slots niceSkip base r : Nat)
    (slit slen sdist : Array Nat) (hashTable : Array Nat) (prev : Array Nat)
    (h3tab : Array Nat) (chLen chDist : Array Nat)
    (hr : base + r ≤ data.size) (hslit : 256 ≤ slit.size)
    (hchL : data.size ≤ chLen.size) (hchD : data.size ≤ chDist.size) :
    Array Nat × Array Nat × Array Nat × Array Nat × Array Nat :=
  let cache := buildCache data hashTable prev h3tab
    depth slots niceSkip base r 0 (Array.replicate (slots * r) 0) (Array.replicate (slots * r) 0)
  let cacheLens := cache.1
  let cacheDists := cache.2.1
  -- The cache arrays are built `slots * r`-sized and `buildCache` preserves
  -- size, so the DP's cache-slot reads (in `scanCands`) are provably in range.
  have hcl : slots * r ≤ cacheLens.size := by
    have : cacheLens.size = slots * r := by
      show (buildCache data hashTable prev h3tab depth slots niceSkip base r 0
        (Array.replicate (slots * r) 0) (Array.replicate (slots * r) 0)).1.size = slots * r
      rw [buildCache_fst_size, Array.size_replicate]
    omega
  have hcd : slots * r ≤ cacheDists.size := by
    have : cacheDists.size = slots * r := by
      show (buildCache data hashTable prev h3tab depth slots niceSkip base r 0
        (Array.replicate (slots * r) 0) (Array.replicate (slots * r) 0)).2.1.size = slots * r
      rw [buildCache_snd_fst_size, Array.size_replicate]
    omega
  let hashTable := cache.2.2.1
  let prev := cache.2.2.2.1
  let h3tab := cache.2.2.2.2
  -- round 1: static cost model
  let cost := seedTailCosts (Array.replicate (r + 259) 0) r (avgLitBits slit) 0
  have hcost1 : r + 259 ≤ cost.size := by
    show r + 259 ≤ (seedTailCosts (Array.replicate (r + 259) 0) r (avgLitBits slit) 0).size
    rw [seedTailCosts_size, Array.size_replicate]; omega
  let res1 := fillRegion data base r slots cacheLens cacheDists
    slit slen sdist r cost chLen chDist hr hslit hcost1 (Nat.le_refl r) hcl hcd
  have hchL1 : data.size ≤ res1.1.size :=
    Nat.le_trans hchL (Nat.le_of_eq (fillRegion_fst_size data base r slots cacheLens cacheDists
      slit slen sdist r cost chLen chDist hr hslit hcost1 (Nat.le_refl r) hcl hcd).symm)
  have hchD1 : data.size ≤ res1.2.size :=
    Nat.le_trans hchD (Nat.le_of_eq (fillRegion_snd_size data base r slots cacheLens cacheDists
      slit slen sdist r cost chLen chDist hr hslit hcost1 (Nat.le_refl r) hcl hcd).symm)
  -- round 2: refit to this region's round-1 parse
  let toks := collectRegionTokens data res1.1 res1.2 (base + r) base #[] hchL1 hchD1
  let fitted := fittedCostTables toks
  have hflit : 256 ≤ fitted.1.size := Nat.le_of_eq (fittedCostTables_fst_size toks).symm
  let cost2 := seedTailCosts (Array.replicate (r + 259) 0) r (avgLitBits fitted.1) 0
  have hcost2 : r + 259 ≤ cost2.size := by
    show r + 259 ≤ (seedTailCosts (Array.replicate (r + 259) 0) r (avgLitBits fitted.1) 0).size
    rw [seedTailCosts_size, Array.size_replicate]; omega
  let res2 := fillRegion data base r slots cacheLens cacheDists
    fitted.1 fitted.2.1 fitted.2.2 r cost2 res1.1 res1.2 hr hflit hcost2 (Nat.le_refl r) hcl hcd
  (hashTable, prev, h3tab, res2.1, res2.2)

/-- `fillRegionRounds` only `set!`s the choice arrays, so it preserves their
    sizes (both DP rounds go through `fillRegion`). -/
private theorem fillRegionRounds_chLen_size (data : ByteArray) (depth slots niceSkip base r : Nat)
    (slit slen sdist : Array Nat) (hashTable : Array Nat) (prev : Array Nat)
    (h3tab : Array Nat) (chLen chDist : Array Nat)
    (hr : base + r ≤ data.size) (hslit : 256 ≤ slit.size)
    (hchL : data.size ≤ chLen.size) (hchD : data.size ≤ chDist.size) :
    (fillRegionRounds data depth slots niceSkip base r slit slen sdist hashTable prev h3tab chLen chDist
      hr hslit hchL hchD).2.2.2.1.size = chLen.size := by
  unfold fillRegionRounds
  simp only [fillRegion_fst_size]

private theorem fillRegionRounds_chDist_size (data : ByteArray) (depth slots niceSkip base r : Nat)
    (slit slen sdist : Array Nat) (hashTable : Array Nat) (prev : Array Nat)
    (h3tab : Array Nat) (chLen chDist : Array Nat)
    (hr : base + r ≤ data.size) (hslit : 256 ≤ slit.size)
    (hchL : data.size ≤ chLen.size) (hchD : data.size ≤ chDist.size) :
    (fillRegionRounds data depth slots niceSkip base r slit slen sdist hashTable prev h3tab chLen chDist
      hr hslit hchL hchD).2.2.2.2.size = chDist.size := by
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
private def computeChoicesLoop (data : ByteArray) (depth slots niceSkip regionSize : Nat)
    (slit slen sdist : Array Nat) (hashTable : Array Nat) (prev : Array Nat)
    (h3tab : Array Nat) (base : Nat)
    (chLen chDist : Array Nat) (hslit : 256 ≤ slit.size)
    (hchL : data.size ≤ chLen.size) (hchD : data.size ≤ chDist.size) (fuel : Nat) :
    Array Nat × Array Nat :=
  match fuel with
  | 0 => (chLen, chDist)
  | fuel + 1 =>
    if hb : base < data.size ∧ 0 < regionSize then
      let r := min regionSize (data.size - base)
      have hr : base + r ≤ data.size := by omega
      let result := fillRegionRounds data depth slots niceSkip base r
        slit slen sdist hashTable prev h3tab chLen chDist hr hslit hchL hchD
      have hchL' : data.size ≤ result.2.2.2.1.size := Nat.le_trans hchL
        (Nat.le_of_eq (fillRegionRounds_chLen_size data depth slots niceSkip base r slit slen sdist
          hashTable prev h3tab chLen chDist hr hslit hchL hchD).symm)
      have hchD' : data.size ≤ result.2.2.2.2.size := Nat.le_trans hchD
        (Nat.le_of_eq (fillRegionRounds_chDist_size data depth slots niceSkip base r slit slen sdist
          hashTable prev h3tab chLen chDist hr hslit hchL hchD).symm)
      computeChoicesLoop data depth slots niceSkip regionSize slit slen sdist result.1 result.2.1
        result.2.2.1 (base + r) result.2.2.2.1 result.2.2.2.2 hslit hchL' hchD' fuel
    else (chLen, chDist)

/-- Compute the global DP choice arrays for the whole input: per region,
    build the candidate cache and run the two-round backward DP. Defaults
    `(1, 0)` = literal everywhere, so unfilled entries are always safe.
    Heuristic only: consumed by the re-verifying emitter `optimalEmit`. -/
def computeChoices (data : ByteArray) : Array Nat × Array Nat :=
  let st := staticCostTables
  computeChoicesLoop data optChainDepth optCacheSlots optNiceSkip optRegionSize st.1 st.2.1 st.2.2
    (Array.replicate 65536 data.size) (Array.replicate (min chainWinSize data.size) data.size)
    (Array.replicate 32768 data.size)
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

/-! ## L9-fast parser (#2638): a cheaper approximate-optimal parse

The exact backward DP above stays the max-ratio crown (level 10). This is the
*cheaper* tier deployed at level 9: three cost cuts, each a per-position saving,
measured to land ~20% outside the L8↔L9 mixing frontier at near-crown ratio
(Silesia, `lake exe l9-fast` sweep):

* **single round** — no round-2 refit (one `fillRegion` pass, no region-token
  collection / histogram / Huffman fit);
* **no length-code boundary scan** — `scanCandsFast` prices each candidate only
  at its full cached length, dropping the inner `scanBounds` truncation scan
  (the largest single DP cost, #2622; the sweep confirmed keeping it costs more
  speed than it buys ratio at every depth);
* **shallower candidate cache** — `fastChainDepth < optChainDepth`, so the
  `buildCache` chain walk (the dominant remaining cost) does ~4× less work.

The choice-array format is byte-identical to the exact DP's, so the same
re-verifying emitter (`optimalEmit`/`optimalEmitIter`) and the same
arbitrary-choice-array validity proofs (`LZ77OptimalCorrect`) apply verbatim.
Everything here is heuristic — opaque to correctness. -/

/-- Candidate-cache chain-walk depth for the L9-fast tier. Lower than
    `optChainDepth = 256`: the original sweep's outside-the-frontier gain
    peaked at 64, and the #2782 cheap-optimal spike re-gridded it against the
    L8↔L9 mixing line after the split-tier/singleton landings moved the
    neighbors — **32 now beats the line by +8.8%** (weighted Silesia
    0.3149 @ 6.0 MB/s vs 0.3137 @ 4.3 at depth 64, ~+40% L9 speed for
    +0.12pp), and the old depth-64 point stays covered by the new-L9↔L10
    blend. Depth 16 falls 26% below the line (cache too weak); 64 remains
    the better ratio point but is dominated as a ladder rung. Pure
    ratio/speed knob.

    #2782 postscript: depth 32 was implemented and measured in production —
    weighted Silesia 0.3146 @ ~5.0 MB/s — and REJECTED by the mixing-frontier
    test: the point lands 3.6% below the old L8↔L9 blend and leaves the old
    depth-64 point uncovered by 3.4% (the spike's +8.8% margin belonged to the
    standalone parse without the pipeline's floor and emit overheads). 64
    stands. -/
def fastChainDepth : Nat := 64

/-- `scanCands` without the `scanBounds` length-code boundary scan: price each
    candidate slot only at its full cached length. Slots hold strictly
    increasing lengths; a zero length terminates the block. Cache reads stay
    panic-checked (`[..]!`) exactly like the value reads in `scanBounds` — the
    cache is heuristic and opaque to correctness. -/
def scanCandsFast (cacheLens cacheDists lenCost distCost cost : Array Nat)
    (slotBase i slots k : Nat) (bestC bestL bestD : Nat) : Nat × Nat × Nat :=
  if _h : k < slots then
    let len := cacheLens[slotBase + k]!
    if len = 0 then (bestC, bestL, bestD)
    else
      let dist := cacheDists[slotBase + k]!
      let cFull := lenCost[len]! + distCost[dist]! + cost[i + len]!
      let (bestC, bestL, bestD) :=
        if cFull < bestC then (cFull, len, dist) else (bestC, bestL, bestD)
      scanCandsFast cacheLens cacheDists lenCost distCost cost slotBase i slots
        (k + 1) bestC bestL bestD
  else (bestC, bestL, bestD)
termination_by slots - k
decreasing_by omega

/-- Backward DP fill using the bounds-free `scanCandsFast`. Same structure as
    `fillRegion` (literal vs best cached candidate, choice recorded at the
    absolute position), minus the cache-size hypotheses (the cache reads are
    panic-checked in `scanCandsFast`). Heuristic only. -/
def fillRegionFast (data : ByteArray) (base r slots : Nat)
    (cacheLens cacheDists litCost lenCost distCost : Array Nat)
    (i : Nat) (cost chLen chDist : Array Nat)
    (hr : base + r ≤ data.size) (hlit : 256 ≤ litCost.size)
    (hcost : r + 259 ≤ cost.size) (hir : i ≤ r) : Array Nat × Array Nat :=
  if h0 : i = 0 then (chLen, chDist)
  else
    let idx := i - 1
    let pos := base + idx
    let byte := data[pos]'(by omega)
    let lit := litCost[byte.toNat]'(by have := UInt8.toNat_lt byte; omega) + cost[idx + 1]'(by omega)
    let (bc, bl, bd) := scanCandsFast cacheLens cacheDists lenCost distCost cost
      (slots * idx) idx slots 0 lit 1 0
    let chLen := chLen.set! pos bl
    let chDist := chDist.set! pos bd
    fillRegionFast data base r slots cacheLens cacheDists litCost lenCost distCost
      idx (cost.set! idx bc) chLen chDist hr hlit
      (by simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]; exact hcost) (by omega)
termination_by i
decreasing_by omega

/-- One region of the L9-fast parse: build the candidate cache (at `depth`) and
    run a single static-cost backward DP over it. No round-2 refit. Returns the
    threaded chain state and choice arrays. -/
def fillRegionFastRound (data : ByteArray) (depth slots niceSkip base r : Nat)
    (slit slen sdist : Array Nat) (hashTable : Array Nat) (prev : Array Nat)
    (h3tab : Array Nat) (chLen chDist : Array Nat)
    (hr : base + r ≤ data.size) (hslit : 256 ≤ slit.size) :
    Array Nat × Array Nat × Array Nat × Array Nat × Array Nat :=
  let cache := buildCache data hashTable prev h3tab depth slots niceSkip base r 0
    (Array.replicate (slots * r) 0) (Array.replicate (slots * r) 0)
  let cacheLens := cache.1
  let cacheDists := cache.2.1
  let hashTable := cache.2.2.1
  let prev := cache.2.2.2.1
  let h3tab := cache.2.2.2.2
  let cost := seedTailCosts (Array.replicate (r + 259) 0) r (avgLitBits slit) 0
  have hcost : r + 259 ≤ cost.size := by
    show r + 259 ≤ (seedTailCosts (Array.replicate (r + 259) 0) r (avgLitBits slit) 0).size
    rw [seedTailCosts_size, Array.size_replicate]; omega
  let res := fillRegionFast data base r slots cacheLens cacheDists
    slit slen sdist r cost chLen chDist hr hslit hcost (Nat.le_refl r)
  (hashTable, prev, h3tab, res.1, res.2)

/-- Region driver for `computeChoicesFast` (fast twin of `computeChoicesLoop`).
    No `chLen`/`chDist` size hypotheses are threaded: the single-round fill
    never reads them back (no region-token collection), so only their `set!`s
    matter. Fuel = `data.size` bounds the region count as in the exact loop. -/
private def computeChoicesFastLoop (data : ByteArray) (depth slots niceSkip regionSize : Nat)
    (slit slen sdist : Array Nat) (hashTable : Array Nat) (prev : Array Nat)
    (h3tab : Array Nat) (base : Nat)
    (chLen chDist : Array Nat) (hslit : 256 ≤ slit.size) (fuel : Nat) :
    Array Nat × Array Nat :=
  match fuel with
  | 0 => (chLen, chDist)
  | fuel + 1 =>
    if hb : base < data.size ∧ 0 < regionSize then
      let r := min regionSize (data.size - base)
      have hr : base + r ≤ data.size := by omega
      let result := fillRegionFastRound data depth slots niceSkip base r
        slit slen sdist hashTable prev h3tab chLen chDist hr hslit
      computeChoicesFastLoop data depth slots niceSkip regionSize slit slen sdist result.1 result.2.1
        result.2.2.1 (base + r) result.2.2.2.1 result.2.2.2.2 hslit fuel
    else (chLen, chDist)

/-- L9-fast choice arrays: like `computeChoices` but the cheaper single-round,
    bounds-free, shallow-cache DP. Defaults `(1, 0)` = literal everywhere.
    Heuristic only — consumed by the re-verifying emitter. -/
def computeChoicesFast (data : ByteArray) : Array Nat × Array Nat :=
  let st := staticCostTables
  computeChoicesFastLoop data fastChainDepth optCacheSlots fastNiceSkip optRegionSize
    st.1 st.2.1 st.2.2
    (Array.replicate 65536 data.size) (Array.replicate (min chainWinSize data.size) data.size)
    (Array.replicate 32768 data.size)
    0 (Array.replicate data.size 1) (Array.replicate data.size 0)
    (by have h : st.1.size = 256 := staticCostTables_fst_size; omega)
    data.size

/-- L9-fast parse (list-backed reference version, the proofs' subject); same
    re-verifying emission as `lz77Optimal`. `lz77OptimalFastIter` is the runtime
    entry point. -/
def lz77OptimalFast (data : ByteArray) : Array LZ77Token :=
  let (chLen, chDist) := computeChoicesFast data
  (optimalEmit data chLen chDist 0).toArray

/-- L9-fast runtime entry point: cheaper approximate-optimal parse, then the
    same re-verifying tail-recursive emission as `lz77OptimalIter`. -/
def lz77OptimalFastIter (data : ByteArray) : Array LZ77Token :=
  let (chLen, chDist) := computeChoicesFast data
  optimalEmitIter data chLen chDist 0 #[]

/-! ## Windowed parse (#2787): bounded live DP state past the 64 MiB gate

`computeChoices`/`computeChoicesFast` allocate two `data.size`-sized `Array Nat`
choice arrays (the exact-DP peak's dominant cost — ≈2/3 of the resident set at
64 MiB, so ≈16 B of the ≈27 B/byte marginal, which is what forces the
`optimalMaxSize` gate). This windowed twin caps that live state to **one region**
at a time: it fills a region's choices into *region-local* buffers (relative
index), emits that region's tokens immediately, and discards the buffers before
the next region. The hash-chain finder state (`hashTable`/`prev`/`h3tab`, itself
already bounded to the 32 KiB window) is threaded across regions exactly as
`computeChoicesLoop` threads it, so cross-region matches survive and the choices
— hence the token stream — are those of the global parse. Only the choice
storage is bounded; the token array itself is still materialized (inherent to
`emitSharedBlocks`), so the residual marginal is the ≈10 B/byte token stream.

Everything here is heuristic — opaque to correctness, like the rest of this file.
The region-local fills use panic-checked (`[..]!`) data/cost reads (they never
fire: every access is in range by construction), which keeps the fills free of
proof obligations so they compose as a plain `fillFn` the shared emitter calls. -/

set_option maxRecDepth 4096 in
/-- Relative-index twin of `fillRegion`: identical backward DP, but the chosen
    length/distance are recorded at the *region-local* index `idx` (into a
    region-sized buffer) rather than the absolute position `base + idx`, and the
    data/cost reads are panic-checked (heuristic). The cache-slot reads stay
    proven in range (`hcl`/`hcd`/`hir`), exactly as in `fillRegion`. -/
def fillRegionWin (data : ByteArray) (base r slots : Nat)
    (cacheLens cacheDists litCost lenCost distCost : Array Nat)
    (i : Nat) (cost chLen chDist : Array Nat) (hir : i ≤ r)
    (hcl : slots * r ≤ cacheLens.size) (hcd : slots * r ≤ cacheDists.size) :
    Array Nat × Array Nat :=
  if h0 : i = 0 then (chLen, chDist)
  else
    let idx := i - 1
    let pos := base + idx
    let byte := data[pos]!
    let lit := litCost[byte.toNat]! + cost[idx + 1]!
    have hidx : idx + 1 ≤ r := by omega
    have hm := Nat.mul_le_mul (Nat.le_refl slots) hidx
    have heq : slots * (idx + 1) = slots * idx + slots := Nat.mul_succ slots idx
    let (bc, bl, bd) := scanCands cacheLens cacheDists lenCost distCost cost
      (slots * idx) idx slots 0 0 lit 1 0 (by omega) (by omega)
    let chLen := chLen.set! idx bl
    let chDist := chDist.set! idx bd
    fillRegionWin data base r slots cacheLens cacheDists litCost lenCost distCost
      idx (cost.set! idx bc) chLen chDist (by omega) hcl hcd
termination_by i
decreasing_by omega

/-- Relative-index twin of `fillRegionFast` (bounds-free `scanCandsFast`, no
    cache-size hypotheses): records the choice at region-local index `idx`. -/
def fillRegionFastWin (data : ByteArray) (base r slots : Nat)
    (cacheLens cacheDists litCost lenCost distCost : Array Nat)
    (i : Nat) (cost chLen chDist : Array Nat) (hir : i ≤ r) :
    Array Nat × Array Nat :=
  if h0 : i = 0 then (chLen, chDist)
  else
    let idx := i - 1
    let pos := base + idx
    let byte := data[pos]!
    let lit := litCost[byte.toNat]! + cost[idx + 1]!
    let (bc, bl, bd) := scanCandsFast cacheLens cacheDists lenCost distCost cost
      (slots * idx) idx slots 0 lit 1 0
    let chLen := chLen.set! idx bl
    let chDist := chDist.set! idx bd
    fillRegionFastWin data base r slots cacheLens cacheDists litCost lenCost distCost
      idx (cost.set! idx bc) chLen chDist (by omega)
termination_by i
decreasing_by omega

/-- Relative-index twin of `collectRegionTokens` (round-2 refit input): walks the
    region-local choice buffers `[0, r)`, reading the data at the absolute
    position `base + pos` so the fitted literal frequencies match the global
    parse. Panic-checked (heuristic). -/
def collectRegionTokensWin (data : ByteArray) (base : Nat) (chLen chDist : Array Nat)
    (r pos : Nat) (acc : Array LZ77Token) : Array LZ77Token :=
  if h : pos < r ∧ base + pos < data.size then
    let len := chLen[pos]!
    if 3 ≤ len then
      collectRegionTokensWin data base chLen chDist r (pos + len)
        (acc.push (.reference len (chDist[pos]!)))
    else
      collectRegionTokensWin data base chLen chDist r (pos + 1)
        (acc.push (.literal (data[base + pos]'(by omega))))
  else acc
termination_by r - pos
decreasing_by all_goals omega

/-- Region-local twin of `fillRegionRounds` (exact two-round DP): returns the
    threaded chain state and the region-sized choice buffers. Total — no `hr`/
    `hslit` obligations (the internal reads are panic-checked), so it composes as
    a plain `fillFn` for `windowedEmit`. -/
def fillRegionRoundsWin (data : ByteArray) (depth slots niceSkip base r : Nat)
    (slit slen sdist : Array Nat) (hashTable prev h3tab : Array Nat) :
    Array Nat × Array Nat × Array Nat × Array Nat × Array Nat :=
  let cache := buildCache data hashTable prev h3tab
    depth slots niceSkip base r 0 (Array.replicate (slots * r) 0) (Array.replicate (slots * r) 0)
  let cacheLens := cache.1
  let cacheDists := cache.2.1
  have hcl : slots * r ≤ cacheLens.size := by
    have : cacheLens.size = slots * r := by
      show (buildCache data hashTable prev h3tab depth slots niceSkip base r 0
        (Array.replicate (slots * r) 0) (Array.replicate (slots * r) 0)).1.size = slots * r
      rw [buildCache_fst_size, Array.size_replicate]
    omega
  have hcd : slots * r ≤ cacheDists.size := by
    have : cacheDists.size = slots * r := by
      show (buildCache data hashTable prev h3tab depth slots niceSkip base r 0
        (Array.replicate (slots * r) 0) (Array.replicate (slots * r) 0)).2.1.size = slots * r
      rw [buildCache_snd_fst_size, Array.size_replicate]
    omega
  let hashTable := cache.2.2.1
  let prev := cache.2.2.2.1
  let h3tab := cache.2.2.2.2
  let cost := seedTailCosts (Array.replicate (r + 259) 0) r (avgLitBits slit) 0
  let res1 := fillRegionWin data base r slots cacheLens cacheDists
    slit slen sdist r cost (Array.replicate r 1) (Array.replicate r 0) (Nat.le_refl r) hcl hcd
  let toks := collectRegionTokensWin data base res1.1 res1.2 r 0 #[]
  let fitted := fittedCostTables toks
  let cost2 := seedTailCosts (Array.replicate (r + 259) 0) r (avgLitBits fitted.1) 0
  let res2 := fillRegionWin data base r slots cacheLens cacheDists
    fitted.1 fitted.2.1 fitted.2.2 r cost2 res1.1 res1.2 (Nat.le_refl r) hcl hcd
  (hashTable, prev, h3tab, res2.1, res2.2)

/-- Region-local twin of `fillRegionFastRound` (single-round L9-fast DP). -/
def fillRegionFastRoundWin (data : ByteArray) (depth slots niceSkip base r : Nat)
    (slit slen sdist : Array Nat) (hashTable prev h3tab : Array Nat) :
    Array Nat × Array Nat × Array Nat × Array Nat × Array Nat :=
  let cache := buildCache data hashTable prev h3tab
    depth slots niceSkip base r 0 (Array.replicate (slots * r) 0) (Array.replicate (slots * r) 0)
  let cacheLens := cache.1
  let cacheDists := cache.2.1
  let hashTable := cache.2.2.1
  let prev := cache.2.2.2.1
  let h3tab := cache.2.2.2.2
  let cost := seedTailCosts (Array.replicate (r + 259) 0) r (avgLitBits slit) 0
  let res := fillRegionFastWin data base r slots cacheLens cacheDists
    slit slen sdist r cost (Array.replicate r 1) (Array.replicate r 0) (Nat.le_refl r)
  (hashTable, prev, h3tab, res.1, res.2)

/-- The region-fill closure the windowed emitter calls to (re)fill each window:
    `fill base r hashTable prev h3tab` returns the updated finder state and the
    region-local choice buffers for `[base, base + r)`. `fillRegionRoundsWin`
    (exact) and `fillRegionFastRoundWin` (L9-fast) are the two instances. -/
abbrev WindowFill : Type :=
  Nat → Nat → Array Nat → Array Nat → Array Nat →
    Array Nat × Array Nat × Array Nat × Array Nat × Array Nat

/-- Interleaved windowed emitter (list-cons version, the proofs' subject). Emits
    `data[pos ..]` re-verifying every match exactly as `optimalEmit`, but reading
    the choice at the *region-local* index `pos - base` from the current window's
    buffers `cLen`/`cDist`; when `pos` runs off the window (`pos ≥ base + r`) it
    refills the next window `[base + r, ..)` via `fill` (threading the finder
    state) and continues. `fill`'s output is never inspected by the correctness
    proofs — validity comes solely from the re-verification, as for `optimalEmit`. -/
def windowedEmit (data : ByteArray) (fill : WindowFill) (regionSize : Nat)
    (base : Nat) (cLen cDist : Array Nat) (hashTable prev h3tab : Array Nat)
    (r pos : Nat) (hrs : 1 ≤ regionSize) (hr1 : 1 ≤ r) : List LZ77Token :=
  if hpos : pos < data.size then
    if hpr : pos < base + r then
      let len := cLen[pos - base]!
      let dist := cDist[pos - base]!
      if hg : 3 ≤ len ∧ len ≤ 258 ∧ pos + len ≤ data.size ∧
          1 ≤ dist ∧ dist ≤ pos ∧ dist ≤ 32768 then
        have h1 : (pos - dist) + len ≤ data.size := by omega
        if hml : lz77Greedy.countMatch data (pos - dist) pos len h1 hg.2.2.1 = len then
          .reference len dist :: windowedEmit data fill regionSize base cLen cDist
            hashTable prev h3tab r (pos + len) hrs hr1
        else
          .literal (data[pos]'hpos) :: windowedEmit data fill regionSize base cLen cDist
            hashTable prev h3tab r (pos + 1) hrs hr1
      else
        .literal (data[pos]'hpos) :: windowedEmit data fill regionSize base cLen cDist
          hashTable prev h3tab r (pos + 1) hrs hr1
    else
      let base' := base + r
      let r' := min regionSize (data.size - base')
      have hr1' : 1 ≤ r' := by omega
      let res := fill base' r' hashTable prev h3tab
      windowedEmit data fill regionSize base' res.2.2.2.1 res.2.2.2.2
        res.1 res.2.1 res.2.2.1 r' pos hrs hr1'
  else []
termination_by 2 * (data.size - pos) + (data.size - base)
decreasing_by all_goals omega

/-- Iterative (`Array`-accumulating) twin of `windowedEmit`; the runtime entry
    point (proven equal to `windowedEmit` in `LZ77OptimalCorrect`). -/
def windowedEmitIter (data : ByteArray) (fill : WindowFill) (regionSize : Nat)
    (base : Nat) (cLen cDist : Array Nat) (hashTable prev h3tab : Array Nat)
    (r pos : Nat) (acc : Array LZ77Token) (hrs : 1 ≤ regionSize) (hr1 : 1 ≤ r) :
    Array LZ77Token :=
  if hpos : pos < data.size then
    if hpr : pos < base + r then
      let len := cLen[pos - base]!
      let dist := cDist[pos - base]!
      if hg : 3 ≤ len ∧ len ≤ 258 ∧ pos + len ≤ data.size ∧
          1 ≤ dist ∧ dist ≤ pos ∧ dist ≤ 32768 then
        have h1 : (pos - dist) + len ≤ data.size := by omega
        if hml : lz77Greedy.countMatch data (pos - dist) pos len h1 hg.2.2.1 = len then
          windowedEmitIter data fill regionSize base cLen cDist hashTable prev h3tab
            r (pos + len) (acc.push (.reference len dist)) hrs hr1
        else
          windowedEmitIter data fill regionSize base cLen cDist hashTable prev h3tab
            r (pos + 1) (acc.push (.literal (data[pos]'hpos))) hrs hr1
      else
        windowedEmitIter data fill regionSize base cLen cDist hashTable prev h3tab
          r (pos + 1) (acc.push (.literal (data[pos]'hpos))) hrs hr1
    else
      let base' := base + r
      let r' := min regionSize (data.size - base')
      have hr1' : 1 ≤ r' := by omega
      let res := fill base' r' hashTable prev h3tab
      windowedEmitIter data fill regionSize base' res.2.2.2.1 res.2.2.2.2
        res.1 res.2.1 res.2.2.1 r' pos acc hrs hr1'
  else acc
termination_by 2 * (data.size - pos) + (data.size - base)
decreasing_by all_goals omega

/-- Shared driver for both windowed parsers: set up the first window and run the
    interleaved emitter with the given region-fill closure. -/
def lz77OptimalWindowedWith (data : ByteArray) (fill : WindowFill) : Array LZ77Token :=
  if h : data.size = 0 then #[]
  else
    let r0 := min optRegionSize data.size
    have hr0 : 1 ≤ r0 := by
      have h2 : 1 ≤ optRegionSize := by decide
      omega
    let ht0 := Array.replicate 65536 data.size
    let prev0 := Array.replicate (min chainWinSize data.size) data.size
    let h3tab0 := Array.replicate 32768 data.size
    let init := fill 0 r0 ht0 prev0 h3tab0
    windowedEmitIter data fill optRegionSize 0 init.2.2.2.1 init.2.2.2.2
      init.1 init.2.1 init.2.2.1 r0 0 #[] (by decide) hr0

/-- Windowed exact-DP parse (#2787): bit-for-bit the tokens of `lz77OptimalIter`,
    but with the choice storage capped to one region. Deployed at level ≥ 10
    above the memory gate. -/
def lz77OptimalWindowedIter (data : ByteArray) : Array LZ77Token :=
  let st := staticCostTables
  lz77OptimalWindowedWith data
    (fun base r ht prev h3 =>
      fillRegionRoundsWin data optChainDepth optCacheSlots optNiceSkip base r
        st.1 st.2.1 st.2.2 ht prev h3)

/-- Windowed L9-fast parse (#2787): the region-capped twin of
    `lz77OptimalFastIter`. Deployed at level 9 above the memory gate. -/
def lz77OptimalWindowedFastIter (data : ByteArray) : Array LZ77Token :=
  let st := staticCostTables
  lz77OptimalWindowedWith data
    (fun base r ht prev h3 =>
      fillRegionFastRoundWin data fastChainDepth optCacheSlots fastNiceSkip base r
        st.1 st.2.1 st.2.2 ht prev h3)

end Zip.Native.Deflate
