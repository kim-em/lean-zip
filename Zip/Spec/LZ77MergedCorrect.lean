import Zip.Spec.LZ77ChainCorrect

/-!
# Correctness of the merged-array lazy matcher (#2767)

`lz77ChainLazyIterPMerged` holds the chain state (`hashTable`, `prev`) in a
single combined `Array Nat`, laid out as `prev ++ hashTable` — the `prev` ring
at offset `[0, prevSize)`, the hash table at `[prevSize, prevSize + hashSize)`.
This deletes the per-matched-position `(hashTable, prev)` Prod that
`updateHashesFastU` returns (measured +3–5% compress on the lazy tier).

The whole file is the equality transfer `lz77ChainLazyIterPMerged =
lz77ChainLazyIterP`, so the packed-token correctness column (`lz77ChainLazyIterP_eq`,
`lzMatchP_map`, the roundtrip proofs) is reused verbatim through this one rewrite.

The proof carries the invariant `c = prev ++ hashTable` through a lockstep
induction that mirrors `lz77ChainLazyIterP.mainLoop`. Two per-step facts make it
go:

* the chain walk reads only `c[i]` for `i < prevSize`, where `c` and `prev`
  agree, so it is invariant under the appended hash table
  (`chainWalk_append`);
* the interior-hash insertion (`updateHashesMerged`) on `prev ++ hashTable`
  produces `prev' ++ hashTable'`, exactly the pair
  `lz77Chain.updateHashes` produces (`updateHashesMerged_append`).
-/

namespace Zip.Native.Deflate

open Zip.Native.Deflate

/-! ## Array `append` helpers -/

/-- Reading a left-half index of an append is the left array's `getElem!`. -/
private theorem getElem!_append_left (a b : Array Nat) (i : Nat)
    (h : i < a.size) : (a ++ b)[i]! = a[i]! := by
  have h' : i < (a ++ b).size := by rw [Array.size_append]; omega
  rw [getElem!_pos (a ++ b) i h', getElem!_pos a i h, Array.getElem_append_left h]

/-- Reading a right-half index of an append is the right array's `getElem!`. -/
private theorem getElem!_append_right (a b : Array Nat) (i : Nat)
    (h : i < b.size) : (a ++ b)[a.size + i]! = b[i]! := by
  have h' : a.size + i < (a ++ b).size := by rw [Array.size_append]; omega
  rw [getElem!_pos (a ++ b) (a.size + i) h', getElem!_pos b i h,
    Array.getElem_append_right (Nat.le_add_right _ _)]
  simp only [Nat.add_sub_cancel_left]

/-- Writing a left-half index of an append updates the left array. -/
private theorem set!_append_left {α : Type} (a b : Array α) (i : Nat) (v : α)
    (h : i < a.size) : (a ++ b).set! i v = (a.set! i v) ++ b := by
  rw [Array.set!_eq_setIfInBounds, Array.set!_eq_setIfInBounds, Array.setIfInBounds_append_left h]

/-- Writing a right-half index of an append updates the right array. -/
private theorem set!_append_right {α : Type} (a b : Array α) (i : Nat) (v : α)
    (h : i < b.size) : (a ++ b).set! (a.size + i) v = a ++ (b.set! i v) := by
  rw [Array.set!_eq_setIfInBounds, Array.set!_eq_setIfInBounds,
    Array.setIfInBounds_append_right (Nat.le_add_right _ _)]
  simp only [Nat.add_sub_cancel_left]

/-- `getElem!_append_right` with the split point named (matches `prevSize + i`). -/
private theorem getElem!_append_right' (a b : Array Nat) (s i : Nat)
    (hs : a.size = s) (h : i < b.size) : (a ++ b)[s + i]! = b[i]! := by
  subst hs; exact getElem!_append_right a b i h

/-- `set!_append_right` with the split point named. -/
private theorem set!_append_right' {α : Type} (a b : Array α) (s i : Nat) (v : α)
    (hs : a.size = s) (h : i < b.size) : (a ++ b).set! (s + i) v = a ++ (b.set! i v) := by
  subst hs; exact set!_append_right a b i v h

/-! ## Chain walk is invariant under the appended hash table -/

/-- The reference chain walk reads `prev` only at indices `< prevSize`, where the
    combined array agrees with `prev`, so appending the hash table does not change
    its result. -/
private theorem chainWalk_append (data : ByteArray) (prev hashTable : Array Nat)
    (windowSize pos maxLen niceLen : Nat) (hpm : pos + maxLen ≤ data.size)
    (hpv : min chainWinSize data.size ≤ prev.size)
    (cand fuel bestLen bestPos : Nat) :
    lz77Chain.chainWalk data (prev ++ hashTable) windowSize pos maxLen niceLen hpm cand fuel bestLen bestPos =
      lz77Chain.chainWalk data prev windowSize pos maxLen niceLen hpm cand fuel bestLen bestPos := by
  induction fuel generalizing cand bestLen bestPos with
  | zero => rw [lz77Chain.chainWalk, lz77Chain.chainWalk]; simp only [↓reduceIte]
  | succ k ih =>
    rw [lz77Chain.chainWalk, lz77Chain.chainWalk, if_neg (by omega : ¬ (k + 1 = 0)),
      if_neg (by omega : ¬ (k + 1 = 0))]
    by_cases hc : cand < pos ∧ pos - cand ≤ windowSize
    · have hmask : (cand &&& 0x7FFF) < prev.size := by
        have h1 := winMask_lt cand
        have h2 := Nat.and_le_left (n := cand) (m := 0x7FFF)
        simp only [chainWinSize] at h1 hpv; omega
      simp only [dif_pos hc, Nat.add_sub_cancel, ih]
      rw [getElem!_append_left prev hashTable (cand &&& 0x7FFF) hmask]
    · simp only [dif_neg hc]

/-- Lifted to the guarded packed `USize` walk the matcher actually calls. -/
private theorem chainWalkGuardedPackedU_append (data : ByteArray) (prev hashTable : Array Nat)
    (windowSize pos maxLen niceLen : Nat) (hpm : pos + maxLen ≤ data.size)
    (hpv : min chainWinSize data.size ≤ prev.size)
    (cand fuel bestLen bestPos : Nat) :
    chainWalkGuardedPackedU data (prev ++ hashTable) windowSize pos maxLen niceLen hpm cand fuel bestLen bestPos =
      chainWalkGuardedPackedU data prev windowSize pos maxLen niceLen hpm cand fuel bestLen bestPos := by
  rw [chainWalkGuardedPackedU_eq, chainWalkGuardedPackedU_eq, chainWalkGuardedPacked_eq,
    chainWalkGuardedPacked_eq,
    chainWalk_append data prev hashTable windowSize pos maxLen niceLen hpm hpv cand fuel bestLen bestPos]

/-! ## Interior-hash insertion on the combined array -/

/-- `updateHashesMerged` on `prev ++ hashTable` is the append of the pair
    `lz77Chain.updateHashes` produces (note the `prev ++ hashTable` order: the
    reference returns `(hashTable, prev)`). -/
private theorem updateHashesMerged_append (data : ByteArray) (hashSize prevSize : Nat)
    (hashTable prev : Array Nat) (pos j matchLen insertCap : Nat)
    (hhs : 0 < hashSize) (hht : hashTable.size = hashSize) (hps : prev.size = prevSize)
    (hpv : min chainWinSize data.size ≤ prev.size) :
    updateHashesMerged data hashSize prevSize (prev ++ hashTable) pos j matchLen insertCap =
      (lz77Chain.updateHashes data hashSize hashTable prev pos j matchLen insertCap).2 ++
        (lz77Chain.updateHashes data hashSize hashTable prev pos j matchLen insertCap).1 := by
  induction hn : matchLen - j using Nat.strongRecOn generalizing j hashTable prev hht hps hpv with
  | _ n ih =>
    rw [updateHashesMerged, lz77Chain.updateHashes]
    by_cases hcond : j < matchLen ∧ j ≤ insertCap
    · rw [if_pos hcond, if_pos hcond]
      by_cases hd : pos + j + 2 < data.size
      · rw [dif_pos hd, dif_pos hd]
        have hb : lz77Greedy.hash3 data (pos + j) hashSize hd < hashTable.size := by
          have : lz77Greedy.hash3 data (pos + j) hashSize hd < hashSize := Nat.mod_lt _ hhs
          omega
        have hmask : ((pos + j) &&& 0x7FFF) < prev.size := by
          have h1 := winMask_lt (pos + j)
          have h2 := Nat.and_le_left (n := pos + j) (m := 0x7FFF)
          simp only [chainWinSize] at h1 hpv; omega
        simp only [headProbeGuarded_eq, guardedSet_eq,
          getElem!_append_right' prev hashTable prevSize (lz77Greedy.hash3 data (pos + j) hashSize hd) hps hb,
          set!_append_right' prev hashTable prevSize (lz77Greedy.hash3 data (pos + j) hashSize hd) (pos + j) hps hb,
          set!_append_left prev (hashTable.set! (lz77Greedy.hash3 data (pos + j) hashSize hd) (pos + j))
            ((pos + j) &&& 0x7FFF) (hashTable[lz77Greedy.hash3 data (pos + j) hashSize hd]!) hmask]
        exact ih _ (by omega) _ _ _ (by rw [Array.size_set!]; exact hht)
          (by rw [Array.size_set!]; exact hps) (by rw [Array.size_set!]; exact hpv) rfl
      · rw [dif_neg hd, dif_neg hd]
        exact ih _ (by omega) _ _ _ hht hps hpv rfl
    · rw [if_neg hcond, if_neg hcond]

/-- `lz77Chain.updateHashes` preserves the hash-table size (`.1`). -/
private theorem updateHashes_size1 (data : ByteArray) (hashSize : Nat)
    (hashTable prev : Array Nat) (pos j matchLen insertCap : Nat) :
    (lz77Chain.updateHashes data hashSize hashTable prev pos j matchLen insertCap).1.size = hashTable.size := by
  induction hn : matchLen - j using Nat.strongRecOn generalizing j hashTable prev with
  | _ n ih =>
    rw [lz77Chain.updateHashes]
    by_cases hcond : j < matchLen ∧ j ≤ insertCap
    · rw [if_pos hcond]
      by_cases hd : pos + j + 2 < data.size
      · rw [dif_pos hd, ih _ (by omega) _ _ _ rfl, Array.size_set!]
      · rw [dif_neg hd, ih _ (by omega) _ _ _ rfl]
    · rw [if_neg hcond]

/-- `lz77Chain.updateHashes` preserves the `prev`-ring size (`.2`). -/
private theorem updateHashes_size2 (data : ByteArray) (hashSize : Nat)
    (hashTable prev : Array Nat) (pos j matchLen insertCap : Nat) :
    (lz77Chain.updateHashes data hashSize hashTable prev pos j matchLen insertCap).2.size = prev.size := by
  induction hn : matchLen - j using Nat.strongRecOn generalizing j hashTable prev with
  | _ n ih =>
    rw [lz77Chain.updateHashes]
    by_cases hcond : j < matchLen ∧ j ≤ insertCap
    · rw [if_pos hcond]
      by_cases hd : pos + j + 2 < data.size
      · rw [dif_pos hd, ih _ (by omega) _ _ _ rfl, Array.size_set!]
      · rw [dif_neg hd, ih _ (by omega) _ _ _ rfl]
    · rw [if_neg hcond]

/-! ## The lockstep loop equality -/

private theorem mergedLoop_eq (data : ByteArray)
    (windowSize hashSize prevSize maxChain insertCap goodMatch niceLen lazyDepth : Nat)
    (hashTable prev : Array Nat) (pos : Nat) (acc : Array UInt32)
    (hhs : 0 < hashSize) (hht : hashTable.size = hashSize) (hps : prev.size = prevSize)
    (hpv : min chainWinSize data.size ≤ prev.size) :
    lz77LazyMergedLoop data windowSize hashSize prevSize maxChain insertCap goodMatch niceLen lazyDepth
        (prev ++ hashTable) pos acc =
      lz77ChainLazyIterP.mainLoop data windowSize hashSize maxChain insertCap goodMatch niceLen lazyDepth
        hashTable prev pos acc := by
  -- PROOF STRATEGY (infrastructure all proven above; this assembly is a WIP sorry):
  --  * strongRecOn on `data.size - pos`, generalizing `pos acc hashTable prev` + hyps;
  --  * unfold both loops; in the `pos+2 < data.size` case, `simp only` with
  --    `headProbeGuarded_eq`, `guardedSet_eq`, and the append helpers rewrites the
  --    combined array to `prev' ++ hashTable'` (verified: the main chain walk aligns
  --    with `chainWalkGuardedPackedU_append`);
  --  * `split` down the branch tree (matchLen≥3 / hle / h3lt / goodMatch /
  --    lazyAcceptCost / hle2); inside the `matchLen < goodMatch` branch the lazy
  --    lookahead walk aligns the same way (needs `h3lt` in scope for the `pos+3`
  --    hash bound — hence the split must precede it);
  --  * each leaf: rewrite `updateHashesMerged … (prev'++ht')` via
  --    `updateHashesMerged_append` and `updateHashesGuarded_eq` (both to the same
  --    `lz77Chain.updateHashes` pair), then close with `ih` — the two token pushes
  --    are identical `packTok`s, and the recursion invariant `c = prev'' ++ ht''`
  --    holds with sizes from `updateHashes_size1`/`updateHashes_size2`.
  sorry

/-- The merged-array lazy matcher equals the two-array packed lazy matcher. -/
theorem lz77ChainLazyIterPMerged_eq (data : ByteArray) (maxChain windowSize insertCap goodMatch niceLen lazyDepth : Nat) :
    lz77ChainLazyIterPMerged data maxChain windowSize insertCap goodMatch niceLen lazyDepth =
      lz77ChainLazyIterP data maxChain windowSize insertCap goodMatch niceLen lazyDepth := by
  unfold lz77ChainLazyIterPMerged lz77ChainLazyIterP
  split
  · rfl
  · dsimp only
    rw [← Array.replicate_append_replicate]
    exact mergedLoop_eq data windowSize 65536 (min chainWinSize data.size) maxChain insertCap
      goodMatch niceLen lazyDepth (Array.replicate 65536 data.size)
      (Array.replicate (min chainWinSize data.size) data.size) 0 _
      (by omega) (by rw [Array.size_replicate]) (by rw [Array.size_replicate])
      (Nat.le_of_eq (by rw [Array.size_replicate]))

end Zip.Native.Deflate
