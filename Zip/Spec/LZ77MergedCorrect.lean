import Zip.Spec.LZ77ChainCorrect

/-!
# Correctness of the merged-array matchers (#2767, greedy port)

`lz77ChainLazyIterPMerged` (lazy tier, levels 4–8) and `lz77ChainIterPMerged`
(greedy tier, levels 1–3) hold the chain state (`hashTable`, `prev`) in a
single combined `Array Nat`, laid out as `prev ++ hashTable` — the `prev` ring
at offset `[0, prevSize)`, the hash table at `[prevSize, prevSize + hashSize)`.
This deletes the per-matched-position `(hashTable, prev)` Prod that
`updateHashesFastU` returns (measured +3–5% compress on the lazy tier).

The whole file is the pair of equality transfers `lz77ChainLazyIterPMerged =
lz77ChainLazyIterP` and `lz77ChainIterPMerged = lz77ChainIterP`, so the
packed-token correctness column (`lz77ChainLazyIterP_eq`, `lz77ChainIterP_eq`,
`lzMatchP_map`, the roundtrip proofs) is reused verbatim through these rewrites.

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

/-- Proven-bounds `set` is the panic-checked `set!` in bounds. -/
private theorem set_eq_set! {α : Type} (a : Array α) (i : Nat) (v : α) (h : i < a.size) :
    a.set i v h = a.set! i v := by
  rw [Array.set!_eq_setIfInBounds, Array.setIfInBounds, dif_pos h]

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

/-- The proven-bounds merged walk equals the runtime-guarded one: identical
    control flow, each `set`/`getElem` collapsing to `set!`/`[]!` in bounds. -/
private theorem updateHashesMergedFast_eq (data : ByteArray) (hashSize prevSize : Nat)
    (c : Array Nat) (pos j matchLen insertCap : Nat)
    (hhs : 0 < hashSize) (hph : prevSize + hashSize ≤ c.size)
    (hpv : min chainWinSize data.size ≤ prevSize) :
    updateHashesMergedFast data hashSize prevSize c pos j matchLen insertCap hhs hph hpv =
      updateHashesMerged data hashSize prevSize c pos j matchLen insertCap := by
  induction hn : matchLen - j using Nat.strongRecOn generalizing j c hph with
  | _ n ih =>
    rw [updateHashesMergedFast, updateHashesMerged]
    by_cases hcond : j < matchLen ∧ j ≤ insertCap
    · rw [if_pos hcond, if_pos hcond]
      by_cases hd : pos + j + 2 < data.size
      · rw [dif_pos hd, dif_pos hd]
        have hb : prevSize + lz77Greedy.hash3 data (pos + j) hashSize hd < c.size := by
          have : lz77Greedy.hash3 data (pos + j) hashSize hd < hashSize := Nat.mod_lt _ hhs
          omega
        have hmask : ((pos + j) &&& 0x7FFF) < c.size := by
          have h1 := winMask_lt (pos + j)
          have h2 := Nat.and_le_left (n := pos + j) (m := 0x7FFF)
          simp only [chainWinSize] at h1 hpv; omega
        have ehead : c[prevSize + lz77Greedy.hash3 data (pos + j) hashSize hd]'hb =
            c[prevSize + lz77Greedy.hash3 data (pos + j) hashSize hd]! := (getElem!_pos c _ hb).symm
        simp only [headProbeGuarded_eq, guardedSet_eq, ehead, set_eq_set!]
        exact ih _ (by omega) _ _ (by rw [Array.size_set!, Array.size_set!]; exact hph) rfl
      · rw [dif_neg hd, dif_neg hd]
        exact ih _ (by omega) _ _ hph rfl
    · rw [if_neg hcond, if_neg hcond]

/-! ## The de-boxed `USize` insertion walk -/

/-- `lz77Greedy.hash3` congruence in the position (the bounds proof transports). -/
private theorem hash3_congr (data : ByteArray) (hashSize : Nat) {p q : Nat} (e : p = q)
    (hp : p + 2 < data.size) (hq : q + 2 < data.size) :
    lz77Greedy.hash3 data p hashSize hp = lz77Greedy.hash3 data q hashSize hq := by
  subst e; rfl

/-- `hash3U` computes exactly `hash3`'s bucket whenever the buffer is
    `USize`-addressable: the hoisted witness makes `hash3`'s per-call
    addressability check always take the wide-load branch (whose reference body
    `hash3U` shares), and the `USize` mod is the faithful image of the `Nat`
    mod. -/
private theorem hash3U_toNat (data : ByteArray) (p hashSize : Nat) (pU hashSizeU : USize)
    (hpU : pU.toNat = p) (hhsU : hashSizeU.toNat = hashSize)
    (hsz : data.size < USize.size) (h : p + 2 < data.size) :
    (hash3U data p pU hashSizeU hpU h).toNat = lz77Greedy.hash3 data p hashSize h := by
  have hplt : p < USize.size := by omega
  have hpUe : pU = p.toUSize := by
    apply USize.toNat_inj.mp; rw [hpU, toUSize_toNat_of_lt hplt]
  subst hpUe
  unfold hash3U lz77Greedy.hash3
  have tail : ∀ w : UInt32,
      (((w * 2654435761) >>> 16).toUSize % hashSizeU).toNat
        = ((w * 2654435761) >>> 16).toNat % hashSize := by
    intro w; rw [USize.toNat_mod, UInt32.toNat_toUSize, hhsU]
  by_cases h4 : p + 4 ≤ data.size
  · rw [dif_pos h4, dif_pos h4, dif_pos (toUSize_toNat_of_lt hsz)]
    exact tail _
  · rw [dif_neg h4, dif_neg h4]
    exact tail _

/-- The de-boxed `USize` merged walk equals the reference merged walk: identical
    control flow (each `USize` compare the faithful image of its `Nat` twin
    through the `toNat` identities), the hash via `hash3U_toNat`, and the
    `uget`/`uset` accesses collapsing to `[]!`/`set!` in bounds. -/
private theorem updateHashesMergedFastU_eq (data : ByteArray) (hashSize prevSize : Nat)
    (c : Array Nat) (pos j matchLen insertCap : Nat)
    (hhs : 0 < hashSize) (hph : prevSize + hashSize ≤ c.size)
    (hpv : min chainWinSize data.size ≤ prevSize)
    (hsz : data.size < USize.size) (hphlt : prevSize + hashSize < USize.size)
    (posU prevSizeU hashSizeU rem2U capU jU matchLenU : USize)
    (hposU : posU.toNat = pos) (hpsU : prevSizeU.toNat = prevSize)
    (hhsU : hashSizeU.toNat = hashSize) (hrem2U : rem2U.toNat = data.size - pos - 2)
    (hcapU : capU.toNat = insertCap) (hjU : jU.toNat = j) (hmlU : matchLenU.toNat = matchLen) :
    updateHashesMergedFastU data hashSize prevSize pos c hhs hph hpv hsz hphlt
        posU prevSizeU hashSizeU rem2U capU hposU hpsU hhsU hrem2U jU matchLenU =
      updateHashesMerged data hashSize prevSize c pos j matchLen insertCap := by
  induction hn : matchLen - j using Nat.strongRecOn generalizing j c jU hph hjU with
  | _ n ih =>
    rw [updateHashesMergedFastU, updateHashesMerged]
    have hUS : USize.size = 2 ^ System.Platform.numBits := rfl
    have hcond : (jU < matchLenU ∧ jU ≤ capU) ↔ (j < matchLen ∧ j ≤ insertCap) := by
      rw [USize.lt_iff_toNat_lt, USize.le_iff_toNat_le, hjU, hmlU, hcapU]
    by_cases hc : j < matchLen ∧ j ≤ insertCap
    · rw [if_pos (hcond.mpr hc), if_pos hc]
      have hmllt := USize.toNat_lt_two_pow_numBits matchLenU
      have hj1 : (jU + 1).toNat = j + 1 := by
        rw [USize.toNat_add, USize.toNat_one, hjU]
        exact Nat.mod_eq_of_lt (by omega)
      have hdata : (jU < rem2U) ↔ (pos + j + 2 < data.size) := by
        rw [USize.lt_iff_toNat_lt, hjU, hrem2U]; omega
      by_cases hd : pos + j + 2 < data.size
      · rw [dif_pos (hdata.mpr hd), dif_pos hd]
        have e1 : (posU + jU).toNat = pos + j := by
          rw [USize.toNat_add, hposU, hjU]; exact Nat.mod_eq_of_lt (by omega)
        have hb3 : lz77Greedy.hash3 data (pos + j) hashSize hd < hashSize := Nat.mod_lt _ hhs
        -- The bucket index: `USize` add over `hash3U` = the `Nat` index over `hash3`.
        have eidx : ∀ (hx : (posU + jU).toNat + 2 < data.size),
            (prevSizeU + hash3U data ((posU + jU).toNat) (posU + jU) hashSizeU rfl hx).toNat
              = prevSize + lz77Greedy.hash3 data (pos + j) hashSize hd := by
          intro hx
          rw [USize.toNat_add, hpsU, hash3U_toNat data _ hashSize _ _ rfl hhsU hsz hx,
            hash3_congr data hashSize e1 hx hd]
          exact Nat.mod_eq_of_lt (by omega)
        -- The chain mask: `USize` and = the `Nat` and.
        have emask : ((posU + jU) &&& 0x7FFF).toNat = (pos + j) &&& 0x7FFF := by
          rw [USize.toNat_and,
            USize.toNat_ofNat_of_lt (Nat.lt_of_lt_of_le (by decide) USize.le_size), e1]
        -- Collapse `uget`/`uset` to `[]!`/`set!`, then align the indices.
        have eget : ∀ (a : Array Nat) (i : Nat) (h : i < a.size), a[i]'h = a[i]! :=
          fun a i h => (getElem!_pos a i h).symm
        -- Two stages: `eidx` must consume the composite bucket index before `e1`
        -- can rewrite the `(posU + jU).toNat` inside `hash3U`'s arguments.
        simp only [Array.uget, Array.uset, set_eq_set!, eget, headProbeGuarded_eq,
          guardedSet_eq, eidx, emask]
        simp only [e1]
        exact ih _ (by omega) _ _
          (by rw [Array.size_set!, Array.size_set!]; exact hph) _ hj1 rfl
      · rw [dif_neg (fun hx => hd (hdata.mp hx)), dif_neg hd]
        exact ih _ (by omega) _ _ hph _ hj1 rfl
    · rw [if_neg (fun hx => hc (hcond.mp hx)), if_neg hc]

/-- `hash3Single` congruence in the position (the bounds proof transports). -/
private theorem hash3Single_congr (data : ByteArray) {p q : Nat} (e : p = q)
    (hp : p + 2 < data.size) (hq : q + 2 < data.size) :
    hash3Single data p hp = hash3Single data q hq := by
  subst e; rfl

/-- `hash3SingleU` computes exactly `hash3Single`'s bucket whenever the buffer
    is `USize`-addressable: the hoisted witness makes `hash3Single`'s per-call
    addressability check always take the wide-load branch (whose body
    `hash3SingleU` shares), and the trailing `.toUSize` round-trips (a `UInt32`
    always fits a `USize`). -/
private theorem hash3SingleU_toNat (data : ByteArray) (p : Nat) (pU : USize)
    (hpU : pU.toNat = p) (hsz : data.size < USize.size) (h : p + 2 < data.size) :
    (hash3SingleU data p pU hpU h).toNat = hash3Single data p h := by
  have hplt : p < USize.size := by omega
  have hpUe : pU = p.toUSize := by
    apply USize.toNat_inj.mp; rw [hpU, toUSize_toNat_of_lt hplt]
  subst hpUe
  unfold hash3SingleU hash3Single
  have tail : ∀ w : UInt32,
      ((((w &&& 0xFFFFFF) * 2654435761) >>> 17).toUSize).toNat
        = (((w &&& 0xFFFFFF) * 2654435761) >>> 17).toNat := by
    intro w; rw [UInt32.toNat_toUSize]
  by_cases h4 : p + 4 ≤ data.size
  · rw [dif_pos h4, dif_pos h4, dif_pos (toUSize_toNat_of_lt hsz)]
    exact tail _
  · rw [dif_neg h4, dif_neg h4]
    exact tail _

/-- The fused de-boxed walk computes exactly the pair of reference walks: `.1`
    is `updateHashesMerged` (the hash4 interior insertion) and `.2` is
    `updateHash3` (the singleton insertion) — one traversal, byte-identical
    state. Mirrors `updateHashesMergedFastU_eq` with the `h3tab` component
    riding along (its store aligned by `hash3SingleU_toNat`). -/
private theorem updateHashesMergedH3FastU_eq (data : ByteArray) (hashSize prevSize : Nat)
    (c h3tab : Array Nat) (pos j matchLen insertCap : Nat)
    (hhs : 0 < hashSize) (hph : prevSize + hashSize ≤ c.size)
    (hpv : min chainWinSize data.size ≤ prevSize) (hh3 : 32768 ≤ h3tab.size)
    (hsz : data.size < USize.size) (hphlt : prevSize + hashSize < USize.size)
    (posU prevSizeU hashSizeU rem2U capU jU matchLenU : USize)
    (hposU : posU.toNat = pos) (hpsU : prevSizeU.toNat = prevSize)
    (hhsU : hashSizeU.toNat = hashSize) (hrem2U : rem2U.toNat = data.size - pos - 2)
    (hcapU : capU.toNat = insertCap) (hjU : jU.toNat = j) (hmlU : matchLenU.toNat = matchLen) :
    updateHashesMergedH3FastU data hashSize prevSize pos c h3tab hhs hph hpv hh3 hsz hphlt
        posU prevSizeU hashSizeU rem2U capU hposU hpsU hhsU hrem2U jU matchLenU =
      (updateHashesMerged data hashSize prevSize c pos j matchLen insertCap,
       updateHash3 data h3tab pos j matchLen insertCap) := by
  induction hn : matchLen - j using Nat.strongRecOn generalizing j c h3tab jU hph hh3 hjU with
  | _ n ih =>
    rw [updateHashesMergedH3FastU, updateHashesMerged, updateHash3]
    have hUS : USize.size = 2 ^ System.Platform.numBits := rfl
    have hcond : (jU < matchLenU ∧ jU ≤ capU) ↔ (j < matchLen ∧ j ≤ insertCap) := by
      rw [USize.lt_iff_toNat_lt, USize.le_iff_toNat_le, hjU, hmlU, hcapU]
    by_cases hc : j < matchLen ∧ j ≤ insertCap
    · rw [if_pos (hcond.mpr hc), if_pos hc, if_pos hc]
      have hmllt := USize.toNat_lt_two_pow_numBits matchLenU
      have hj1 : (jU + 1).toNat = j + 1 := by
        rw [USize.toNat_add, USize.toNat_one, hjU]
        exact Nat.mod_eq_of_lt (by omega)
      have hdata : (jU < rem2U) ↔ (pos + j + 2 < data.size) := by
        rw [USize.lt_iff_toNat_lt, hjU, hrem2U]; omega
      by_cases hd : pos + j + 2 < data.size
      · rw [dif_pos (hdata.mpr hd), dif_pos hd, dif_pos hd]
        have e1 : (posU + jU).toNat = pos + j := by
          rw [USize.toNat_add, hposU, hjU]; exact Nat.mod_eq_of_lt (by omega)
        have hb3 : lz77Greedy.hash3 data (pos + j) hashSize hd < hashSize := Nat.mod_lt _ hhs
        have eidx : ∀ (hx : (posU + jU).toNat + 2 < data.size),
            (prevSizeU + hash3U data ((posU + jU).toNat) (posU + jU) hashSizeU rfl hx).toNat
              = prevSize + lz77Greedy.hash3 data (pos + j) hashSize hd := by
          intro hx
          rw [USize.toNat_add, hpsU, hash3U_toNat data _ hashSize _ _ rfl hhsU hsz hx,
            hash3_congr data hashSize e1 hx hd]
          exact Nat.mod_eq_of_lt (by omega)
        have emask : ((posU + jU) &&& 0x7FFF).toNat = (pos + j) &&& 0x7FFF := by
          rw [USize.toNat_and,
            USize.toNat_ofNat_of_lt (Nat.lt_of_lt_of_le (by decide) USize.le_size), e1]
        -- The singleton bucket: `USize` hash = the `Nat` hash at the aligned position.
        have eh3 : ∀ (hx : (posU + jU).toNat + 2 < data.size),
            (hash3SingleU data ((posU + jU).toNat) (posU + jU) rfl hx).toNat
              = hash3Single data (pos + j) hd := by
          intro hx
          rw [hash3SingleU_toNat data _ _ rfl hsz hx, hash3Single_congr data e1 hx hd]
        have eget : ∀ (a : Array Nat) (i : Nat) (h : i < a.size), a[i]'h = a[i]! :=
          fun a i h => (getElem!_pos a i h).symm
        simp only [Array.uget, Array.uset, set_eq_set!, eget, headProbeGuarded_eq,
          guardedSet_eq, eidx, emask, eh3]
        simp only [e1]
        exact ih _ (by omega) _ _ _
          (by rw [Array.size_set!, Array.size_set!]; exact hph)
          (by rw [Array.size_set!]; exact hh3) _ hj1 rfl
      · rw [dif_neg (fun hx => hd (hdata.mp hx)), dif_neg hd, dif_neg hd]
        exact ih _ (by omega) _ _ _ hph hh3 _ hj1 rfl
    · rw [if_neg (fun hx => hc (hcond.mp hx)), if_neg hc, if_neg hc]

/-- The guarded merged walk equals the reference merged walk (the de-boxed
    `USize` branch via `updateHashesMergedFastU_eq`, the proven-bounds `Nat`
    branch via `updateHashesMergedFast_eq`; the fallback branch is definitionally
    it). -/
private theorem updateHashesMergedGuarded_eq (data : ByteArray) (hashSize prevSize : Nat)
    (c : Array Nat) (pos j matchLen insertCap : Nat) :
    updateHashesMergedGuarded data hashSize prevSize c pos j matchLen insertCap =
      updateHashesMerged data hashSize prevSize c pos j matchLen insertCap := by
  unfold updateHashesMergedGuarded
  split
  · rename_i hg
    split
    · rename_i hu
      have hsz : data.size < USize.size := by
        rw [← hu.1]; exact USize.toNat_lt_two_pow_numBits _
      have hphlt : prevSize + hashSize < USize.size := by
        rw [← hu.2.1]; exact USize.toNat_lt_two_pow_numBits _
      exact updateHashesMergedFastU_eq data hashSize prevSize c pos j matchLen insertCap
        hg.1 hg.2.1 hg.2.2 hsz hphlt pos.toUSize prevSize.toUSize hashSize.toUSize
        (data.size - pos - 2).toUSize insertCap.toUSize j.toUSize matchLen.toUSize
        hu.2.2.1 (toUSize_toNat_of_lt (by omega)) (toUSize_toNat_of_lt (by omega))
        (toUSize_toNat_of_lt (by omega)) hu.2.2.2.2.2 hu.2.2.2.1 hu.2.2.2.2.1
    · exact updateHashesMergedFast_eq data hashSize prevSize c pos j matchLen insertCap
        hg.1 hg.2.1 hg.2.2
  · rfl

/-- The fused split-tier insertion equals the pair of reference walks the loop
    previously computed separately: `.1` is `updateHashesMerged`, `.2` the
    `useH3`-gated `updateHash3` — exactly the two `let`s it replaces, so the
    lockstep loop proof rewrites through this one equation. -/
private theorem updateHashesMergedH3Guarded_eq (useH3 : Bool) (data : ByteArray)
    (hashSize prevSize : Nat) (c h3tab : Array Nat) (pos j matchLen insertCap : Nat) :
    updateHashesMergedH3Guarded useH3 data hashSize prevSize c h3tab pos j matchLen insertCap =
      (updateHashesMerged data hashSize prevSize c pos j matchLen insertCap,
       if useH3 then updateHash3 data h3tab pos j matchLen insertCap else h3tab) := by
  unfold updateHashesMergedH3Guarded
  by_cases hu3 : useH3
  · rw [if_pos hu3, if_pos hu3]
    split
    · rename_i hg
      split
      · rename_i hu
        have hsz : data.size < USize.size := by
          rw [← hu.1]; exact USize.toNat_lt_two_pow_numBits _
        have hphlt : prevSize + hashSize < USize.size := by
          rw [← hu.2.1]; exact USize.toNat_lt_two_pow_numBits _
        exact updateHashesMergedH3FastU_eq data hashSize prevSize c h3tab pos j matchLen insertCap
          hg.1 hg.2.1 hg.2.2.1 hg.2.2.2 hsz hphlt pos.toUSize prevSize.toUSize hashSize.toUSize
          (data.size - pos - 2).toUSize insertCap.toUSize j.toUSize matchLen.toUSize
          hu.2.2.1 (toUSize_toNat_of_lt (by omega)) (toUSize_toNat_of_lt (by omega))
          (toUSize_toNat_of_lt (by omega)) hu.2.2.2.2.2 hu.2.2.2.1 hu.2.2.2.2.1
      · rw [updateHashesMergedFast_eq data hashSize prevSize c pos j matchLen insertCap
          hg.1 hg.2.1 hg.2.2.1]
    · rfl
  · rw [if_neg hu3, if_neg hu3, updateHashesMergedGuarded_eq]

/-! ## Seeded lookahead probe: byte-identity bridge -/

/-- A lookahead match no longer than the current one is never cost-accepted:
    `lazyAcceptCost` requires `len1 < len2`. -/
private theorem lazyAcceptCost_of_le {l1 d1 l2 d2 : Nat} (h : l2 ≤ l1) :
    lazyAcceptCost l1 d1 l2 d2 = false := by
  unfold lazyAcceptCost
  rw [decide_eq_false (show ¬ l1 < l2 by omega), Bool.false_and]

/-- The seeded lookahead probe produces the same lazy decision as the unseeded
    one, and — whenever that decision is *accept* — the same probe result.
    `.1`: the cost decision is identical for the seeded and unseeded probe. `.2`:
    the seeded probe either equals the unseeded one outright, or its decision is
    *reject* (so the branch it selects never depends on the probe value). Together
    these make seeding the `pos+1` walk with the `pos` match length
    byte-identical. The seed is `matchLen` below the walk's cutoff and `0` at or
    above it; both cases collapse via `chainWalkGuardedPackedU_seed`. -/
private theorem seeded_probe_bridge (data : ByteArray) (prev : Array Nat)
    (windowSize pos1 maxLen niceLen : Nat) (hpm : pos1 + maxLen ≤ data.size)
    (hml511 : maxLen ≤ 511) (cand fuel : Nat) (len1 dist1 base : Nat) :
    (lazyAcceptCost len1 dist1
        (chainWalkGuardedPackedU data prev windowSize pos1 maxLen niceLen hpm cand fuel
          (if len1 < min niceLen maxLen then len1 else 0) 0 % 512)
        (base - chainWalkGuardedPackedU data prev windowSize pos1 maxLen niceLen hpm cand fuel
          (if len1 < min niceLen maxLen then len1 else 0) 0 / 512)
      = lazyAcceptCost len1 dist1
        (chainWalkGuardedPackedU data prev windowSize pos1 maxLen niceLen hpm cand fuel 0 0 % 512)
        (base - chainWalkGuardedPackedU data prev windowSize pos1 maxLen niceLen hpm cand fuel 0 0 / 512))
    ∧ (chainWalkGuardedPackedU data prev windowSize pos1 maxLen niceLen hpm cand fuel
          (if len1 < min niceLen maxLen then len1 else 0) 0
        = chainWalkGuardedPackedU data prev windowSize pos1 maxLen niceLen hpm cand fuel 0 0
       ∨ lazyAcceptCost len1 dist1
           (chainWalkGuardedPackedU data prev windowSize pos1 maxLen niceLen hpm cand fuel
             (if len1 < min niceLen maxLen then len1 else 0) 0 % 512)
           (base - chainWalkGuardedPackedU data prev windowSize pos1 maxLen niceLen hpm cand fuel
             (if len1 < min niceLen maxLen then len1 else 0) 0 / 512) = false) := by
  by_cases hc1 : len1 < min niceLen maxLen
  · rw [if_pos hc1]
    obtain ⟨hEq, hLe⟩ := chainWalkGuardedPackedU_seed data prev windowSize pos1 maxLen niceLen hpm hml511 len1 hc1 cand fuel
    by_cases hgt : len1 < chainWalkGuardedPackedU data prev windowSize pos1 maxLen niceLen hpm cand fuel 0 0 % 512
    · rw [hEq hgt]; exact ⟨rfl, Or.inl rfl⟩
    · rw [hLe (Nat.le_of_not_lt hgt)]
      have hfL : lazyAcceptCost len1 dist1 (len1 % 512) (base - len1 / 512) = false :=
        lazyAcceptCost_of_le (Nat.mod_le len1 512)
      have hfR : lazyAcceptCost len1 dist1
          (chainWalkGuardedPackedU data prev windowSize pos1 maxLen niceLen hpm cand fuel 0 0 % 512)
          (base - chainWalkGuardedPackedU data prev windowSize pos1 maxLen niceLen hpm cand fuel 0 0 / 512) = false :=
        lazyAcceptCost_of_le (Nat.le_of_not_lt hgt)
      exact ⟨by rw [hfL, hfR], Or.inr hfL⟩
  · rw [if_neg hc1]; exact ⟨rfl, Or.inl rfl⟩

/-! ## The lockstep loop equality -/

set_option maxHeartbeats 1000000 in
private theorem mergedLoop_eq (data : ByteArray)
    (windowSize hashSize prevSize maxChain insertCap goodMatch niceLen lazyDepth : Nat) (useH3 : Bool)
    (hashTable prev h3tab : Array Nat) (pos : Nat) (acc : Array UInt32)
    (hhs : 0 < hashSize) (hht : hashTable.size = hashSize) (hps : prev.size = prevSize)
    (hpv : min chainWinSize data.size ≤ prev.size) :
    lz77LazyMergedLoop data windowSize hashSize prevSize maxChain insertCap goodMatch niceLen lazyDepth useH3
        (prev ++ hashTable) h3tab pos acc =
      lz77ChainLazyIterP.mainLoop data windowSize hashSize maxChain insertCap goodMatch niceLen lazyDepth useH3
        hashTable prev h3tab pos acc := by
  induction hn : data.size - pos using Nat.strongRecOn generalizing pos acc hashTable prev h3tab hht hps hpv with
  | _ n ih =>
    unfold lz77LazyMergedLoop lz77ChainLazyIterP.mainLoop
    by_cases hlt : pos + 2 < data.size
    · have hh : lz77Greedy.hash3 data pos hashSize hlt < hashTable.size := by
        have : lz77Greedy.hash3 data pos hashSize hlt < hashSize := Nat.mod_lt _ hhs
        omega
      have hmask0 : (pos &&& 0x7FFF) < prev.size := by
        have h1 := winMask_lt pos
        have h2 := Nat.and_le_left (n := pos) (m := 0x7FFF)
        simp only [chainWinSize] at h1 hpv; omega
      -- Reduce the outer dite with `zeta := false`, then abstract the opaque
      -- hash3 seed (identical on both sides — it reads the separate `h3tab`) so
      -- the append/head-insert simp below does not duplicate it across branches.
      simp (config := { zeta := false }) only [hlt, ↓reduceDIte]
      generalize hsd : h3Seed useH3 data h3tab windowSize pos hlt = sd
      generalize hash3Single data pos hlt = hsg
      simp only [headProbeGuarded_eq, guardedSet_eq,
        getElem!_append_right' prev hashTable prevSize (lz77Greedy.hash3 data pos hashSize hlt) hps hh,
        set!_append_right' prev hashTable prevSize (lz77Greedy.hash3 data pos hashSize hlt) pos hps hh,
        set!_append_left prev (hashTable.set! (lz77Greedy.hash3 data pos hashSize hlt) pos)
          (pos &&& 0x7FFF) (hashTable[lz77Greedy.hash3 data pos hashSize hlt]!) hmask0]
      generalize ht'eq : hashTable.set! (lz77Greedy.hash3 data pos hashSize hlt) pos = t'
      generalize hp'eq : prev.set! (pos &&& 0x7FFF) (hashTable[lz77Greedy.hash3 data pos hashSize hlt]!) = p'
      have hht' : t'.size = hashSize := by rw [← ht'eq, Array.size_set!]; exact hht
      have hps' : p'.size = prevSize := by rw [← hp'eq, Array.size_set!]; exact hps
      have hpv' : min chainWinSize data.size ≤ p'.size := by rw [← hp'eq, Array.size_set!]; exact hpv
      rw [chainWalkGuardedPackedU_append data p' t' windowSize pos (min 258 (data.size - pos))
        niceLen (by omega) hpv' (hashTable[lz77Greedy.hash3 data pos hashSize hlt]!) maxChain (sd % 512) (sd / 512)]
      -- Abstract the (now identical on both sides) main walk result so `split`'s
      -- normalisation does not carry its many `matchLen`/`matchPos`/interior-insert
      -- copies (which the split-tier `updateHash3` range multiplied).
      generalize chainWalkGuardedPackedU data p' windowSize pos (min 258 (data.size - pos)) niceLen
        (by omega) (hashTable[lz77Greedy.hash3 data pos hashSize hlt]!) maxChain (sd % 512) (sd / 512) = rmain
      split
      · split
        · split
          · -- h3lt-T: align the lazy lookahead walk, then split goodMatch / lazyAccept / hle2
            have hh2 : lz77Greedy.hash3 data (pos + 1) hashSize (by omega) < t'.size := by
              rw [hht']
              have : lz77Greedy.hash3 data (pos + 1) hashSize (by omega) < hashSize := Nat.mod_lt _ hhs
              omega
            simp only [getElem!_append_right' p' t' prevSize
              (lz77Greedy.hash3 data (pos + 1) hashSize (by omega)) hps' hh2]
            rw [chainWalkGuardedPackedU_append data p' t' windowSize (pos + 1)
              (min 258 (data.size - (pos + 1))) niceLen (by omega) hpv'
              (t'[lz77Greedy.hash3 data (pos + 1) hashSize (by omega)]!) lazyDepth]
            split
            · -- goodMatch-T: bridge the *seeded* `pos+1` probe to the unseeded one.
              -- The seeding lemma makes the lazy decision (and, on accept, the probe
              -- result itself) identical, so the branch tree stays in lockstep.
              have hbr := seeded_probe_bridge data p' windowSize (pos + 1)
                (min 258 (data.size - (pos + 1))) niceLen (by omega) (by omega)
                (t'[lz77Greedy.hash3 data (pos + 1) hashSize (by omega)]!) lazyDepth
                (rmain % 512)
                (pos - rmain / 512)
                (pos + 1)
              rw [hbr.1]
              split
              · -- accept
                rename_i hacc
                rcases hbr.2 with heq | hfalse
                · rw [heq]
                  split
                  · rw [updateHashesMergedH3Guarded_eq,
                      updateHashesMerged_append data hashSize prevSize t' p' pos 1 _ insertCap hhs hht' hps' hpv',
                      updateHashesGuarded_eq]
                    exact ih _ (by omega) _ _ _ _ _ (by rw [updateHashes_size1]; exact hht')
                      (by rw [updateHashes_size2]; exact hps') (by rw [updateHashes_size2]; exact hpv') rfl
                  · rw [updateHashesMergedH3Guarded_eq,
                      updateHashesMerged_append data hashSize prevSize t' p' pos 1 _ insertCap hhs hht' hps' hpv',
                      updateHashesGuarded_eq]
                    exact ih _ (by omega) _ _ _ _ _ (by rw [updateHashes_size1]; exact hht')
                      (by rw [updateHashes_size2]; exact hps') (by rw [updateHashes_size2]; exact hpv') rfl
                · rw [← hbr.1, hfalse] at hacc; simp at hacc
              · -- reject: the emitted token uses only the `pos` match, not the probe.
                rw [updateHashesMergedH3Guarded_eq,
                  updateHashesMerged_append data hashSize prevSize t' p' pos 1 _ insertCap hhs hht' hps' hpv',
                  updateHashesGuarded_eq]
                exact ih _ (by omega) _ _ _ _ _ (by rw [updateHashes_size1]; exact hht')
                  (by rw [updateHashes_size2]; exact hps') (by rw [updateHashes_size2]; exact hpv') rfl
            · -- goodMatch-F (gated): no probe.
              rw [updateHashesMergedH3Guarded_eq,
                updateHashesMerged_append data hashSize prevSize t' p' pos 1 _ insertCap hhs hht' hps' hpv',
                updateHashesGuarded_eq]
              exact ih _ (by omega) _ _ _ _ _ (by rw [updateHashes_size1]; exact hht')
                (by rw [updateHashes_size2]; exact hps') (by rw [updateHashes_size2]; exact hpv') rfl
          · exact ih _ (by omega) _ _ _ _ _ hht' hps' hpv' rfl
        · exact ih _ (by omega) _ _ _ _ _ hht' hps' hpv' rfl
      · exact ih _ (by omega) _ _ _ _ _ hht' hps' hpv' rfl
    · simp only [hlt, ↓reduceDIte]

/-- Greedy-tier lockstep equality (the twin of `mergedLoop_eq` minus the lazy
    branch and the hash3 seed): `lz77GreedyMergedLoop` on `prev ++ hashTable`
    is `lz77ChainIterP.mainLoop` on the separate arrays. -/
private theorem greedyMergedLoop_eq (data : ByteArray)
    (windowSize hashSize prevSize maxChain insertCap niceLen : Nat)
    (hashTable prev : Array Nat) (pos : Nat) (acc : Array UInt32)
    (hhs : 0 < hashSize) (hht : hashTable.size = hashSize) (hps : prev.size = prevSize)
    (hpv : min chainWinSize data.size ≤ prev.size) :
    lz77GreedyMergedLoop data windowSize hashSize prevSize maxChain insertCap niceLen
        (prev ++ hashTable) pos acc =
      lz77ChainIterP.mainLoop data windowSize hashSize maxChain insertCap niceLen
        hashTable prev pos acc := by
  induction hn : data.size - pos using Nat.strongRecOn generalizing pos acc hashTable prev hht hps hpv with
  | _ n ih =>
    unfold lz77GreedyMergedLoop lz77ChainIterP.mainLoop
    by_cases hlt : pos + 2 < data.size
    · have hh : lz77Greedy.hash3 data pos hashSize hlt < hashTable.size := by
        have : lz77Greedy.hash3 data pos hashSize hlt < hashSize := Nat.mod_lt _ hhs
        omega
      have hmask0 : (pos &&& 0x7FFF) < prev.size := by
        have h1 := winMask_lt pos
        have h2 := Nat.and_le_left (n := pos) (m := 0x7FFF)
        simp only [chainWinSize] at h1 hpv; omega
      simp (config := { zeta := false }) only [hlt, ↓reduceDIte]
      simp only [headProbeGuarded_eq, guardedSet_eq,
        getElem!_append_right' prev hashTable prevSize (lz77Greedy.hash3 data pos hashSize hlt) hps hh,
        set!_append_right' prev hashTable prevSize (lz77Greedy.hash3 data pos hashSize hlt) pos hps hh,
        set!_append_left prev (hashTable.set! (lz77Greedy.hash3 data pos hashSize hlt) pos)
          (pos &&& 0x7FFF) (hashTable[lz77Greedy.hash3 data pos hashSize hlt]!) hmask0]
      generalize ht'eq : hashTable.set! (lz77Greedy.hash3 data pos hashSize hlt) pos = t'
      generalize hp'eq : prev.set! (pos &&& 0x7FFF) (hashTable[lz77Greedy.hash3 data pos hashSize hlt]!) = p'
      have hht' : t'.size = hashSize := by rw [← ht'eq, Array.size_set!]; exact hht
      have hps' : p'.size = prevSize := by rw [← hp'eq, Array.size_set!]; exact hps
      have hpv' : min chainWinSize data.size ≤ p'.size := by rw [← hp'eq, Array.size_set!]; exact hpv
      rw [chainWalkGuardedPackedU_append data p' t' windowSize pos (min 258 (data.size - pos))
        niceLen (by omega) hpv' (hashTable[lz77Greedy.hash3 data pos hashSize hlt]!) maxChain 0 0]
      generalize chainWalkGuardedPackedU data p' windowSize pos (min 258 (data.size - pos)) niceLen
        (by omega) (hashTable[lz77Greedy.hash3 data pos hashSize hlt]!) maxChain 0 0 = rmain
      split
      · split
        · rw [updateHashesMergedGuarded_eq,
            updateHashesMerged_append data hashSize prevSize t' p' pos 1 _ insertCap hhs hht' hps' hpv',
            updateHashesGuarded_eq]
          exact ih _ (by omega) _ _ _ _ (by rw [updateHashes_size1]; exact hht')
            (by rw [updateHashes_size2]; exact hps') (by rw [updateHashes_size2]; exact hpv') rfl
        · exact ih _ (by omega) _ _ _ _ hht' hps' hpv' rfl
      · exact ih _ (by omega) _ _ _ _ hht' hps' hpv' rfl
    · simp only [hlt, ↓reduceDIte]

/-- The merged-array greedy matcher equals the two-array packed greedy matcher. -/
theorem lz77ChainIterPMerged_eq (data : ByteArray) (maxChain windowSize insertCap niceLen : Nat) :
    lz77ChainIterPMerged data maxChain windowSize insertCap niceLen =
      lz77ChainIterP data maxChain windowSize insertCap niceLen := by
  unfold lz77ChainIterPMerged lz77ChainIterP
  split
  · rfl
  · dsimp only
    rw [← Array.replicate_append_replicate]
    exact greedyMergedLoop_eq data windowSize 65536 (min chainWinSize data.size) maxChain insertCap
      niceLen (Array.replicate 65536 data.size)
      (Array.replicate (min chainWinSize data.size) data.size) 0 _
      (by omega) (by rw [Array.size_replicate]) (by rw [Array.size_replicate])
      (Nat.le_of_eq (by rw [Array.size_replicate]))

/-- The merged-array lazy matcher equals the two-array packed lazy matcher. -/
theorem lz77ChainLazyIterPMerged_eq (data : ByteArray) (maxChain windowSize insertCap goodMatch niceLen lazyDepth : Nat) (useH3 : Bool) :
    lz77ChainLazyIterPMerged data maxChain windowSize insertCap goodMatch niceLen lazyDepth useH3 =
      lz77ChainLazyIterP data maxChain windowSize insertCap goodMatch niceLen lazyDepth useH3 := by
  unfold lz77ChainLazyIterPMerged lz77ChainLazyIterP
  split
  · rfl
  · dsimp only
    rw [← Array.replicate_append_replicate]
    exact mergedLoop_eq data windowSize 65536 (min chainWinSize data.size) maxChain insertCap
      goodMatch niceLen lazyDepth useH3 (Array.replicate 65536 data.size)
      (Array.replicate (min chainWinSize data.size) data.size) (Array.replicate 32768 data.size) 0 _
      (by omega) (by rw [Array.size_replicate]) (by rw [Array.size_replicate])
      (Nat.le_of_eq (by rw [Array.size_replicate]))

end Zip.Native.Deflate
