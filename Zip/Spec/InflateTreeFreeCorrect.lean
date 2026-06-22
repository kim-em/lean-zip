import Zip.Spec.InflateCanonical
import Zip.Native.InflateTreeFree

/-!
# Tree-free canonical decode: correctness

Proves the tree-free canonical decoder (`Zip.Native.InflateTreeFree`) decodes
exactly like the Huffman tree walk, with the tree (`fromLengthsTree lengths`) as a
**proof-only** object — never built at runtime. The chain, bottom-up:

1. `buildFirstIndex` / `buildSymbols` structure invariants (counting sort places
   each symbol at `firstIndex[len] + offset`).
2. arithmetic ↔ `codeFor`: a matched code value `c` of length `len` selects the
   symbol whose canonical codeword is `natToBits c len`.
3. `walkCanonical = (fromLengthsTree lengths).decode` on the fallback bits, hence
   the tree-free decoder equals the canonical `decodeHuffman` spec.

Reuses the `#2679` foundation: `nextCodes` / `countLengths` / `codeFor` /
`allCodes` / `fromLengths_hasLeaf` / `fromLengths_leaf_spec`.
-/

namespace Zip.Native.HuffTree

/-! ## `buildFirstIndex` structure invariant -/

/-- `psumCount count n = ∑_{k=1}^{n} count[k]!` — the cumulative symbol count
    through length `n`, so `firstIndex[len]` is `psumCount count (len-1)`. -/
def psumCount (count : Array Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => psumCount count n + count[n + 1]!

/-- The `buildFirstIndex` loop fills `fi[L] = psumCount count (L-1)` for every
    `1 ≤ L ≤ maxBits`, the offset where length-`L` symbols begin in `symbols`. -/
theorem buildFirstIndex_go_spec (count : Array Nat) (maxBits : Nat) :
    ∀ (n len idx : Nat) (fi : Array Nat), maxBits + 1 - len ≤ n → 1 ≤ len →
      fi.size = maxBits + 2 →
      idx = psumCount count (len - 1) →
      (∀ L, 1 ≤ L → L < len → fi[L]! = psumCount count (L - 1)) →
      ∀ L, 1 ≤ L → L ≤ maxBits →
        (buildFirstIndex.go count maxBits len idx fi)[L]! = psumCount count (L - 1) := by
  intro n
  induction n with
  | zero =>
    intro len idx fi hn hlen1 hsz hidx hfi L hL1 hLmax
    rw [buildFirstIndex.go, if_pos (by omega)]
    exact hfi L hL1 (by omega)
  | succ n ih =>
    intro len idx fi hn hlen1 hsz hidx hfi L hL1 hLmax
    rw [buildFirstIndex.go]
    by_cases hgt : len > maxBits
    · rw [if_pos hgt]; exact hfi L hL1 (by omega)
    · rw [if_neg hgt]
      refine ih (len + 1) (idx + count[len]!) (fi.set! len idx) (by omega) (by omega)
        (by rw [Array.size_set!]; exact hsz) ?_ ?_ L hL1 hLmax
      · -- idx + count[len]! = psumCount count len
        rw [hidx]
        obtain ⟨len', rfl⟩ : ∃ m, len = m + 1 := ⟨len - 1, by omega⟩
        simp only [Nat.add_sub_cancel, psumCount]
      · -- fi.set! len idx preserves the invariant and extends it to len
        intro L' hL'1 hL'lt
        by_cases hL'len : L' = len
        · subst hL'len
          rw [Array.getElem!_set!_self _ _ _ (by rw [hsz]; omega), hidx]
        · rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
          exact hfi L' hL'1 (by omega)

/-- `buildFirstIndex count maxBits`'s `L`-th entry is the cumulative count of
    symbols of length `< L`. -/
theorem buildFirstIndex_spec (count : Array Nat) (maxBits L : Nat)
    (hL1 : 1 ≤ L) (hLmax : L ≤ maxBits) :
    (buildFirstIndex count maxBits)[L]! = psumCount count (L - 1) :=
  buildFirstIndex_go_spec count maxBits (maxBits + 1) 1 0 (Array.replicate (maxBits + 2) 0)
    (by omega) (by omega) (Array.size_replicate) (by simp [psumCount])
    (fun _ h1 hlt => by omega) L hL1 hLmax

/-- `buildFirstIndex.go` preserves the array size (every write is an in-bounds
    `set!`), so `buildFirstIndex` keeps the `maxBits + 2` size of its seed. -/
theorem buildFirstIndex_go_size (count : Array Nat) (maxBits : Nat) :
    ∀ (n len idx : Nat) (fi : Array Nat), maxBits + 1 - len ≤ n →
      (buildFirstIndex.go count maxBits len idx fi).size = fi.size := by
  intro n
  induction n with
  | zero => intro len idx fi hn; rw [buildFirstIndex.go, if_pos (by omega)]
  | succ n ih =>
    intro len idx fi hn
    rw [buildFirstIndex.go]
    by_cases hgt : len > maxBits
    · rw [if_pos hgt]
    · rw [if_neg hgt, ih (len + 1) (idx + count[len]!) (fi.set! len idx) (by omega),
          Array.size_set!]

/-- `buildFirstIndex count maxBits` has size `maxBits + 2`. -/
@[simp] theorem buildFirstIndex_size (count : Array Nat) (maxBits : Nat) :
    (buildFirstIndex count maxBits).size = maxBits + 2 := by
  rw [buildFirstIndex, buildFirstIndex_go_size count maxBits (maxBits + 1) 1 0 _ (by omega),
      Array.size_replicate]

/-- `psumCount` is a prefix sum, hence monotone in its index. -/
theorem psumCount_mono (count : Array Nat) (a : Nat) :
    ∀ {b : Nat}, a ≤ b → psumCount count a ≤ psumCount count b := by
  intro b
  induction b with
  | zero => intro h; have : a = 0 := Nat.le_zero.mp h; subst this; exact Nat.le_refl _
  | succ k ih =>
    intro h
    by_cases hk : a ≤ k
    · exact Nat.le_trans (ih hk) (by simp only [psumCount]; omega)
    · have : a = k + 1 := by omega
      subst this; exact Nat.le_refl _

/-- One prefix-sum step: `psumCount count l = psumCount count (l-1) + count[l]!`. -/
theorem psumCount_succ_pred (count : Array Nat) (l : Nat) (hl : 1 ≤ l) :
    psumCount count l = psumCount count (l - 1) + count[l]! := by
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
  simp only [Nat.add_sub_cancel, psumCount]

/-! ## `buildSymbols` counting-sort placement

`numEarlier lsList len s` is the count of earlier symbols (`< s`) of length `len`,
matching `codeFor`'s offset exactly. The counting sort places symbol `s` of length
`len` at `firstIndex[len] + numEarlier lsList len s`. -/

/-- Count of symbols of length `len` among the first `s` code lengths. This is
    `codeFor`'s offset; see `Huffman.Spec.codeFor`. -/
def numEarlier (lsList : List Nat) (len s : Nat) : Nat :=
  (lsList.take s).foldl (fun acc l => if (l == len) = true then acc + 1 else acc) 0

/-- Processing one more length increments `numEarlier` exactly when that length
    matches. -/
theorem numEarlier_succ (lsList : List Nat) (len s : Nat) (hs : s < lsList.length) :
    numEarlier lsList len (s + 1)
      = numEarlier lsList len s + (if lsList[s] = len then 1 else 0) := by
  unfold numEarlier
  rw [List.take_add_one, List.getElem?_eq_getElem hs]
  simp only [Option.toList_some, List.foldl_append, List.foldl_cons, List.foldl_nil]
  by_cases h : lsList[s] = len
  · simp [h]
  · simp [h]

/-- Strict monotonicity of `numEarlier` across a matching position: if `s₁ < s₂`
    and the symbol at `s₁` has length `len`, the count strictly grows. Local copy
    of `Huffman.Spec.offset_of_lt` (which is `private`), phrased via `numEarlier`. -/
theorem numEarlier_lt (lsList : List Nat) (s₁ s₂ len : Nat)
    (hs₁ : s₁ < lsList.length) (hlen₁ : lsList[s₁] = len) (hlt : s₁ < s₂)
    (hs₂ : s₂ ≤ lsList.length) :
    numEarlier lsList len s₁ < numEarlier lsList len s₂ := by
  unfold numEarlier
  suffices ∀ (init : Nat),
      List.foldl (fun acc l => if (l == len) = true then acc + 1 else acc)
        init (List.take s₁ lsList) <
      List.foldl (fun acc l => if (l == len) = true then acc + 1 else acc)
        init (List.take s₂ lsList) from this 0
  induction lsList generalizing s₁ s₂ with
  | nil => simp only [List.length_nil, Nat.not_lt_zero] at hs₁
  | cons x xs ih =>
    intro init
    cases s₁ with
    | zero =>
      simp only [List.take_zero, List.foldl_nil, List.getElem_cons_zero] at hlen₁ ⊢
      rw [List.take_cons (by omega : 0 < s₂)]
      simp only [List.foldl_cons, show (x == len) = true from beq_iff_eq.mpr hlen₁, ite_true]
      exact Nat.lt_of_lt_of_le (by omega) (Huffman.Spec.count_foldl_mono len _ _)
    | succ n =>
      simp only [List.length_cons] at hs₁ hs₂
      rw [List.take_cons (by omega : 0 < n + 1), List.take_cons (by omega : 0 < s₂)]
      simp only [List.foldl_cons]
      have hlen₁' : xs[n] = len := by
        simp only [List.getElem_cons_succ] at hlen₁; exact hlen₁
      exact ih n (s₂ - 1) (by omega) hlen₁' (by omega) (by omega) _

/-- `(lengths.toList.map UInt8.toNat)[s] = lengths[s]!.toNat` for in-range `s`. -/
theorem map_toNat_getElem (lengths : Array UInt8) (s : Nat) (hs : s < lengths.size) :
    (lengths.toList.map UInt8.toNat)[s]'(by rw [List.length_map, Array.length_toList]; exact hs)
      = lengths[s]!.toNat := by
  rw [List.getElem_map, Array.getElem_toList, getElem!_pos lengths s hs]

/-- `numEarlier_succ` specialized to the `Array UInt8` length vector. -/
theorem numEarlier_succ_arr (lengths : Array UInt8) (len s : Nat) (hs : s < lengths.size) :
    numEarlier (lengths.toList.map UInt8.toNat) len (s + 1)
      = numEarlier (lengths.toList.map UInt8.toNat) len s
        + (if lengths[s]!.toNat = len then 1 else 0) := by
  rw [numEarlier_succ _ _ _ (by rw [List.length_map, Array.length_toList]; exact hs),
      map_toNat_getElem lengths s hs]

/-- `numEarlier_lt` specialized to the `Array UInt8` length vector. -/
theorem numEarlier_lt_arr (lengths : Array UInt8) (s₁ s₂ len : Nat)
    (hs₁ : s₁ < lengths.size) (hlen₁ : lengths[s₁]!.toNat = len)
    (hlt : s₁ < s₂) (hs₂ : s₂ ≤ lengths.size) :
    numEarlier (lengths.toList.map UInt8.toNat) len s₁
      < numEarlier (lengths.toList.map UInt8.toNat) len s₂ :=
  numEarlier_lt (lengths.toList.map UInt8.toNat) s₁ s₂ len
    (by rw [List.length_map, Array.length_toList]; exact hs₁)
    (by rw [map_toNat_getElem lengths s₁ hs₁]; exact hlen₁)
    hlt
    (by rw [List.length_map, Array.length_toList]; exact hs₂)

/-- The placement position of symbol `s` lies strictly within its length's block
    `[psumCount count (len-1), psumCount count len)`. -/
theorem place_upper (lengths : Array UInt8) (maxBits : Nat) (count firstIndex : Array Nat)
    (hfi : ∀ L, 1 ≤ L → L ≤ maxBits → firstIndex[L]! = psumCount count (L - 1))
    (hcount : ∀ L, 1 ≤ L → L ≤ maxBits →
      count[L]! = numEarlier (lengths.toList.map UInt8.toNat) L lengths.size)
    (s : Nat) (hs : s < lengths.size)
    (h0 : 0 < lengths[s]!.toNat) (hm : lengths[s]!.toNat ≤ maxBits) :
    firstIndex[lengths[s]!.toNat]! +
        numEarlier (lengths.toList.map UInt8.toNat) lengths[s]!.toNat s
      < psumCount count lengths[s]!.toNat := by
  rw [hfi _ h0 hm, psumCount_succ_pred count _ h0, hcount _ h0 hm]
  have := numEarlier_lt_arr lengths s lengths.size lengths[s]!.toNat hs rfl hs (Nat.le_refl _)
  omega

/-- Distinct placed symbols land at distinct positions: the counting sort never
    overwrites an earlier placement. -/
theorem place_ne (lengths : Array UInt8) (maxBits : Nat) (count firstIndex : Array Nat)
    (hfi : ∀ L, 1 ≤ L → L ≤ maxBits → firstIndex[L]! = psumCount count (L - 1))
    (hcount : ∀ L, 1 ≤ L → L ≤ maxBits →
      count[L]! = numEarlier (lengths.toList.map UInt8.toNat) L lengths.size)
    (s s' : Nat) (hs : s < lengths.size) (hs' : s' < lengths.size) (hlt : s' < s)
    (h0 : 0 < lengths[s]!.toNat) (hm : lengths[s]!.toNat ≤ maxBits)
    (h0' : 0 < lengths[s']!.toNat) (hm' : lengths[s']!.toNat ≤ maxBits) :
    firstIndex[lengths[s']!.toNat]! +
        numEarlier (lengths.toList.map UInt8.toNat) lengths[s']!.toNat s'
      ≠ firstIndex[lengths[s]!.toNat]! +
        numEarlier (lengths.toList.map UInt8.toNat) lengths[s]!.toNat s := by
  by_cases hll : lengths[s']!.toNat = lengths[s]!.toNat
  · -- same length: the earlier symbol has a strictly smaller offset
    rw [hll]
    have hlt' := numEarlier_lt_arr lengths s' s lengths[s]!.toNat hs' hll hlt (Nat.le_of_lt hs)
    omega
  · -- different lengths: the two length-blocks are disjoint
    have hub := place_upper lengths maxBits count firstIndex hfi hcount s hs h0 hm
    have hub' := place_upper lengths maxBits count firstIndex hfi hcount s' hs' h0' hm'
    have hlbA : firstIndex[lengths[s]!.toNat]! = psumCount count (lengths[s]!.toNat - 1) :=
      hfi _ h0 hm
    have hlbA' : firstIndex[lengths[s']!.toNat]! = psumCount count (lengths[s']!.toNat - 1) :=
      hfi _ h0' hm'
    rcases Nat.lt_or_gt_of_ne hll with hcmp | hcmp
    · have hmono := psumCount_mono count lengths[s']!.toNat
        (show lengths[s']!.toNat ≤ lengths[s]!.toNat - 1 by omega)
      omega
    · have hmono := psumCount_mono count lengths[s]!.toNat
        (show lengths[s]!.toNat ≤ lengths[s']!.toNat - 1 by omega)
      omega

/-- **`buildSymbols.go` placement invariant.** Carrying the offset-tracking
    invariant (A) and the placements-so-far invariant (B), every symbol `s'` of
    valid length lands at `firstIndex[len] + numEarlier lsList len s'`. -/
theorem buildSymbols_go_spec
    (lengths : Array UInt8) (maxBits total : Nat) (count firstIndex : Array Nat)
    (hfi : ∀ L, 1 ≤ L → L ≤ maxBits → firstIndex[L]! = psumCount count (L - 1))
    (hcount : ∀ L, 1 ≤ L → L ≤ maxBits →
      count[L]! = numEarlier (lengths.toList.map UInt8.toNat) L lengths.size)
    (htotal : total = psumCount count maxBits) :
    ∀ (n s : Nat) (offset : Array Nat) (symbols : Array UInt16),
      lengths.size - s ≤ n →
      offset.size = maxBits + 2 →
      symbols.size = total →
      (∀ L, 1 ≤ L → L ≤ maxBits →
        offset[L]! = firstIndex[L]! +
          numEarlier (lengths.toList.map UInt8.toNat) L s) →
      (∀ s', s' < s → 0 < lengths[s']!.toNat → lengths[s']!.toNat ≤ maxBits →
        symbols[firstIndex[lengths[s']!.toNat]! +
          numEarlier (lengths.toList.map UInt8.toNat) lengths[s']!.toNat s']!
          = s'.toUInt16) →
      ∀ s', s' < lengths.size → 0 < lengths[s']!.toNat → lengths[s']!.toNat ≤ maxBits →
        (buildSymbols.go lengths maxBits s offset symbols)[
          firstIndex[lengths[s']!.toNat]! +
          numEarlier (lengths.toList.map UInt8.toNat) lengths[s']!.toNat s']!
          = s'.toUInt16 := by
  intro n
  induction n with
  | zero =>
    intro s offset symbols hn hosz hssz hA hB s' hs' h0' hm'
    rw [buildSymbols.go, if_pos (by omega)]
    exact hB s' (by omega) h0' hm'
  | succ n ih =>
    intro s offset symbols hn hosz hssz hA hB s' hs' h0' hm'
    rw [buildSymbols.go]
    by_cases hge : s ≥ lengths.size
    · rw [if_pos hge]; exact hB s' (by omega) h0' hm'
    · rw [if_neg hge]
      have hslt : s < lengths.size := by omega
      simp only []
      by_cases hcond : 0 < lengths[s]!.toNat ∧ lengths[s]!.toNat ≤ maxBits
      · rw [if_pos hcond]
        obtain ⟨h0, hm⟩ := hcond
        -- the new offset still tracks (A) at s+1
        have hA' : ∀ L, 1 ≤ L → L ≤ maxBits →
            (offset.set! lengths[s]!.toNat (offset[lengths[s]!.toNat]! + 1))[L]!
              = firstIndex[L]! +
                numEarlier (lengths.toList.map UInt8.toNat) L (s + 1) := by
          intro L hL1 hLmax
          rw [numEarlier_succ_arr lengths L s hslt]
          by_cases hLl : L = lengths[s]!.toNat
          · subst hLl
            rw [Array.getElem!_set!_self _ _ _ (by rw [hosz]; omega), hA _ hL1 hLmax,
                if_pos rfl]; omega
          · rw [Array.getElem!_set!_ne _ _ _ _ (by omega), hA L hL1 hLmax,
                if_neg (by omega), Nat.add_zero]
        -- the placement position of s itself
        have hpos_s : offset[lengths[s]!.toNat]!
            = firstIndex[lengths[s]!.toNat]! +
              numEarlier (lengths.toList.map UInt8.toNat) lengths[s]!.toNat s :=
          hA _ h0 hm
        have hpos_lt : offset[lengths[s]!.toNat]! < symbols.size := by
          rw [hpos_s, hssz, htotal]
          exact Nat.lt_of_lt_of_le
            (place_upper lengths maxBits count firstIndex hfi hcount s hslt h0 hm)
            (psumCount_mono count _ hm)
        -- the new symbols array still witnesses (B) at s+1
        have hB' : ∀ s'', s'' < s + 1 → 0 < lengths[s'']!.toNat → lengths[s'']!.toNat ≤ maxBits →
            (symbols.set! offset[lengths[s]!.toNat]! s.toUInt16)[
              firstIndex[lengths[s'']!.toNat]! +
              numEarlier (lengths.toList.map UInt8.toNat) lengths[s'']!.toNat s'']!
              = s''.toUInt16 := by
          intro s'' hs''1 h0'' hm''
          by_cases heq : s'' = s
          · subst heq
            rw [← hpos_s, Array.getElem!_set!_self _ _ _ hpos_lt]
          · have hs''lt : s'' < s := by omega
            rw [Array.getElem!_set!_ne _ _ _ _
                  (by rw [hpos_s];
                      exact (place_ne lengths maxBits count firstIndex hfi hcount s s''
                        hslt (by omega) hs''lt h0 hm h0'' hm'').symm),
                hB s'' hs''lt h0'' hm'']
        exact ih (s + 1) _ _ (by omega) (by rw [Array.size_set!]; exact hosz)
          (by rw [Array.size_set!]; exact hssz) hA' hB' s' hs' h0' hm'
      · rw [if_neg hcond]
        -- skipped length: offset and symbols unchanged; (A)/(B) carry to s+1
        have hA' : ∀ L, 1 ≤ L → L ≤ maxBits →
            offset[L]! = firstIndex[L]! +
              numEarlier (lengths.toList.map UInt8.toNat) L (s + 1) := by
          intro L hL1 hLmax
          rw [numEarlier_succ_arr lengths L s hslt, hA L hL1 hLmax,
              if_neg (by omega), Nat.add_zero]
        have hB' : ∀ s'', s'' < s + 1 → 0 < lengths[s'']!.toNat → lengths[s'']!.toNat ≤ maxBits →
            symbols[firstIndex[lengths[s'']!.toNat]! +
              numEarlier (lengths.toList.map UInt8.toNat) lengths[s'']!.toNat s'']!
              = s''.toUInt16 := by
          intro s'' hs''1 h0'' hm''
          have hs''lt : s'' < s := by
            rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hs''1) with h | h
            · exact h
            · exact absurd (h ▸ ⟨h0'', hm''⟩) hcond
          exact hB s'' hs''lt h0'' hm''
        exact ih (s + 1) offset symbols (by omega) hosz hssz hA' hB' s' hs' h0' hm'

/-- **`buildSymbols` placement.** Every valid-length symbol `s'` is written at
    `firstIndex[len] + numEarlier lsList len s'` — the counting sort lists symbols
    in `(length, symbol)` order. -/
theorem buildSymbols_placement
    (lengths : Array UInt8) (maxBits total : Nat) (count firstIndex : Array Nat)
    (hfi : ∀ L, 1 ≤ L → L ≤ maxBits → firstIndex[L]! = psumCount count (L - 1))
    (hcount : ∀ L, 1 ≤ L → L ≤ maxBits →
      count[L]! = numEarlier (lengths.toList.map UInt8.toNat) L lengths.size)
    (htotal : total = psumCount count maxBits)
    (hfisz : firstIndex.size = maxBits + 2)
    (s' : Nat) (hs' : s' < lengths.size)
    (h0' : 0 < lengths[s']!.toNat) (hm' : lengths[s']!.toNat ≤ maxBits) :
    (buildSymbols lengths maxBits total firstIndex)[
        firstIndex[lengths[s']!.toNat]! +
        numEarlier (lengths.toList.map UInt8.toNat) lengths[s']!.toNat s']!
      = s'.toUInt16 :=
  buildSymbols_go_spec lengths maxBits total count firstIndex hfi hcount htotal
    lengths.size 0 firstIndex (Array.replicate total 0) (by omega) hfisz
    (Array.size_replicate) (fun L _ _ => by simp [numEarlier]) (fun _ h _ _ => absurd h (by omega))
    s' hs' h0' hm'

/-! ## `buildLongDecode` instantiation and `codeFor` correspondence -/

/-- The fast histogram equals the spec `countLengths` on the mapped lengths.
    (Local restatement of the `hcount` step inside `buildTableCanonicalFast_eq`.) -/
theorem countLengthsFast_eq (lengths : Array UInt8) (maxBits : Nat) :
    countLengthsFast lengths maxBits
      = Huffman.Spec.countLengths (lengths.toList.map UInt8.toNat) maxBits := by
  rw [countLengthsFast,
      countLengthsFast_go_eq lengths maxBits lengths.size 0 _ (by omega), List.drop_zero]
  rfl

/-- `numEarlier` over the whole length vector is the spec `countLengths`. -/
theorem numEarlier_size_eq (lengths : Array UInt8) (maxBits L : Nat)
    (hL1 : 1 ≤ L) (hLm : L ≤ maxBits) :
    (countLengthsFast lengths maxBits)[L]!
      = numEarlier (lengths.toList.map UInt8.toNat) L lengths.size := by
  rw [countLengthsFast_eq,
      Huffman.Spec.countLengths_eq (lengths.toList.map UInt8.toNat) maxBits L (by omega) hLm]
  unfold numEarlier
  rw [List.take_of_length_le (by rw [List.length_map, Array.length_toList]; exact Nat.le_refl _)]

/-- **Placement for `buildLongDecode`.** Symbol `s` of valid length lands at
    `firstIndex[len] + numEarlier lsList len s` in the sorted `symbols` array. -/
theorem buildLongDecode_placement (lengths : Array UInt8) (maxBits : Nat) (hmb : 1 ≤ maxBits)
    (s : Nat) (hs : s < lengths.size)
    (h0 : 0 < lengths[s]!.toNat) (hm : lengths[s]!.toNat ≤ maxBits) :
    (buildLongDecode lengths maxBits).symbols[
        (buildLongDecode lengths maxBits).firstIndex[lengths[s]!.toNat]! +
        numEarlier (lengths.toList.map UInt8.toNat) lengths[s]!.toNat s]!
      = s.toUInt16 := by
  have hcount : ∀ L, 1 ≤ L → L ≤ maxBits →
      (countLengthsFast lengths maxBits)[L]!
        = numEarlier (lengths.toList.map UInt8.toNat) L lengths.size :=
    fun L hL1 hLm => numEarlier_size_eq lengths maxBits L hL1 hLm
  have hfi : ∀ L, 1 ≤ L → L ≤ maxBits →
      (buildFirstIndex (countLengthsFast lengths maxBits) maxBits)[L]!
        = psumCount (countLengthsFast lengths maxBits) (L - 1) :=
    fun L hL1 hLm => buildFirstIndex_spec _ maxBits L hL1 hLm
  have htotal :
      (buildFirstIndex (countLengthsFast lengths maxBits) maxBits)[maxBits]!
          + (countLengthsFast lengths maxBits)[maxBits]!
        = psumCount (countLengthsFast lengths maxBits) maxBits := by
    rw [buildFirstIndex_spec _ maxBits maxBits hmb (Nat.le_refl _),
        ← psumCount_succ_pred _ maxBits hmb]
  show (buildSymbols lengths maxBits _ (buildFirstIndex (countLengthsFast lengths maxBits) maxBits))[_]!
      = s.toUInt16
  exact buildSymbols_placement lengths maxBits _ (countLengthsFast lengths maxBits)
    (buildFirstIndex (countLengthsFast lengths maxBits) maxBits) hfi hcount htotal
    (buildFirstIndex_size _ maxBits) s hs h0 hm

/-- **`codeFor` of a placed symbol.** The canonical codeword of symbol `s` (valid
    length `len`) is `natToBits (firstCode[len] + numEarlier lsList len s) len`,
    where `firstCode = nextCodes (countLengths lsList) maxBits`. This is the
    arithmetic ↔ `codeFor` correspondence: `walkCanonical`'s accumulated value
    `firstCode[len] + offset` selects exactly this symbol's codeword. -/
theorem codeFor_placed (lengths : Array UInt8) (maxBits : Nat)
    (s : Nat) (hs : s < lengths.size)
    (h0 : 0 < lengths[s]!.toNat) (hm : lengths[s]!.toNat ≤ maxBits) :
    Huffman.Spec.codeFor (lengths.toList.map UInt8.toNat) maxBits s
      = some (Huffman.Spec.natToBits
          ((Huffman.Spec.nextCodes
             (Huffman.Spec.countLengths (lengths.toList.map UInt8.toNat) maxBits)
             maxBits)[lengths[s]!.toNat]!
           + numEarlier (lengths.toList.map UInt8.toNat) lengths[s]!.toNat s)
          lengths[s]!.toNat) := by
  obtain ⟨cw, hcw⟩ := Deflate.Correctness.codeFor_some (lengths.toList.map UInt8.toNat) maxBits s
    (by rw [List.length_map, Array.length_toList]; exact hs)
    (by rw [map_toNat_getElem lengths s hs]; omega)
    (by rw [map_toNat_getElem lengths s hs]; exact hm)
  rw [hcw]
  obtain ⟨hs', hlen', hcweq⟩ := Huffman.Spec.codeFor_spec hcw
  have hidx : (lengths.toList.map UInt8.toNat)[s]'hs' = lengths[s]!.toNat :=
    map_toNat_getElem lengths s hs
  rw [hcweq, hidx]
  rfl

end Zip.Native.HuffTree
