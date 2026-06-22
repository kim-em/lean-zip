import Zip.Spec.InflateCanonical
import Zip.Spec.InflateBufCorrect
import Zip.Spec.DynamicTreesCorrect
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

/-! ## Surjectivity: every value in a length's canonical range is a real codeword

The error-soundness direction of the tree-free decoder needs the converse of
`codeFor_placed`: if `walkCanonical` accepts a value `c` in length `len`'s range,
that value is a genuine codeword (so the returned symbol is a real tree leaf).
`numEarlier` reaches every value below the total count, so each range slot is
filled. -/

/-- `numEarlier xs len` is surjective onto `[0, numEarlier xs len N)`: every count
    below the running total is hit at some earlier matching position. -/
theorem numEarlier_surj (xs : List Nat) (len : Nat) :
    ∀ N, N ≤ xs.length → ∀ j, j < numEarlier xs len N →
      ∃ s, ∃ _ : s < xs.length, s < N ∧ xs[s] = len ∧ numEarlier xs len s = j := by
  intro N
  induction N with
  | zero => intro _ j hj; simp only [numEarlier, List.take_zero, List.foldl_nil] at hj; omega
  | succ k ih =>
    intro hN j hj
    have hk : k < xs.length := by omega
    rw [numEarlier_succ xs len k hk] at hj
    by_cases hxk : xs[k] = len
    · rw [if_pos hxk] at hj
      by_cases hjk : j < numEarlier xs len k
      · obtain ⟨s, hs, hsk, hxs, hns⟩ := ih (by omega) j hjk
        exact ⟨s, hs, by omega, hxs, hns⟩
      · exact ⟨k, hk, by omega, hxk, by omega⟩
    · rw [if_neg hxk, Nat.add_zero] at hj
      obtain ⟨s, hs, hsk, hxs, hns⟩ := ih (by omega) j hj
      exact ⟨s, hs, by omega, hxs, hns⟩

/-- `numEarlier` surjectivity for the `Array UInt8` length vector, against the
    fast histogram count. -/
theorem numEarlier_surj_arr (lengths : Array UInt8) (maxBits len : Nat)
    (hlen1 : 1 ≤ len) (hlenm : len ≤ maxBits)
    (j : Nat) (hj : j < (countLengthsFast lengths maxBits)[len]!) :
    ∃ s, s < lengths.size ∧ lengths[s]!.toNat = len ∧
      numEarlier (lengths.toList.map UInt8.toNat) len s = j := by
  rw [numEarlier_size_eq lengths maxBits len hlen1 hlenm] at hj
  obtain ⟨s, hs, _, hxs, hns⟩ := numEarlier_surj (lengths.toList.map UInt8.toNat) len
    lengths.size (Nat.le_of_eq (by rw [List.length_map, Array.length_toList])) j hj
  have hssize : s < lengths.size := by rw [List.length_map, Array.length_toList] at hs; exact hs
  exact ⟨s, hssize, by rw [← map_toNat_getElem lengths s hssize]; exact hxs, hns⟩

/-- **Value → codeword (the `(←)` direction).** Any value `c` in length `len`'s
    canonical range `[firstCode[len], firstCode[len] + count[len])` is the codeword
    of a real symbol `s`, and `walkCanonical`'s lookup `symbols[firstIndex[len] +
    (c - firstCode[len])]` returns exactly that `s`. This makes the tree-free
    accept-set match the canonical code: no value matches that isn't a leaf. -/
theorem codeFor_of_value (lengths : Array UInt8) (maxBits : Nat) (hmb : 1 ≤ maxBits)
    (len c : Nat) (hlen1 : 1 ≤ len) (hlenm : len ≤ maxBits)
    (hc_lo : (buildLongDecode lengths maxBits).firstCode[len]! ≤ c)
    (hc_hi : c < (buildLongDecode lengths maxBits).firstCode[len]!
        + (buildLongDecode lengths maxBits).count[len]!) :
    ∃ s, s < lengths.size ∧ lengths[s]!.toNat = len ∧
      Huffman.Spec.codeFor (lengths.toList.map UInt8.toNat) maxBits s
        = some (Huffman.Spec.natToBits c len) ∧
      (buildLongDecode lengths maxBits).symbols[
        (buildLongDecode lengths maxBits).firstIndex[len]! +
        (c - (buildLongDecode lengths maxBits).firstCode[len]!)]! = s.toUInt16 := by
  have hfc : (buildLongDecode lengths maxBits).firstCode
      = Huffman.Spec.nextCodes
          (Huffman.Spec.countLengths (lengths.toList.map UInt8.toNat) maxBits) maxBits := by
    show Huffman.Spec.nextCodes (countLengthsFast lengths maxBits) maxBits = _
    rw [countLengthsFast_eq]
  have hcnt : (buildLongDecode lengths maxBits).count = countLengthsFast lengths maxBits := rfl
  -- the offset of `c` within its length block reaches a real symbol
  have hj_lt : c - (buildLongDecode lengths maxBits).firstCode[len]!
      < (countLengthsFast lengths maxBits)[len]! := by rw [hcnt] at hc_hi; omega
  obtain ⟨s, hssize, hlen_s, hne⟩ := numEarlier_surj_arr lengths maxBits len hlen1 hlenm
    (c - (buildLongDecode lengths maxBits).firstCode[len]!) hj_lt
  have h0 : 0 < lengths[s]!.toNat := by rw [hlen_s]; omega
  have hm : lengths[s]!.toNat ≤ maxBits := by rw [hlen_s]; exact hlenm
  have hfc_len : (Huffman.Spec.nextCodes
        (Huffman.Spec.countLengths (lengths.toList.map UInt8.toNat) maxBits) maxBits)[len]!
      = (buildLongDecode lengths maxBits).firstCode[len]! := by rw [hfc]
  refine ⟨s, hssize, hlen_s, ?_, ?_⟩
  · -- codeFor s = natToBits c len
    rw [codeFor_placed lengths maxBits s hssize h0 hm, hlen_s, hne, hfc_len,
        Nat.add_sub_cancel' hc_lo]
  · -- symbols[firstIndex[len] + (c - firstCode[len])] = s
    have hplace := buildLongDecode_placement lengths maxBits hmb s hssize h0 hm
    rw [hlen_s, hne] at hplace
    exact hplace

/-! ## Bit bridges for the runtime `walkCanonical` accumulation

`walkCanonical` accumulates a code value `code := code * 2 + (bitBuf &&& 1)`,
reading the buffer LSB-first. After consuming `k` bits the value is
`bitReverse bitBuf.toNat k 0`, whose `natToBits` is the codeword the spec reads
(`cwOf bitBuf.toNat k`). These two arithmetic facts feed that induction. -/

/-- One step of the bit reversal: `bitReverse x (k+1) 0` splits off the low bit
    as the new high-order summand. -/
theorem bitReverse_succ (x k : Nat) :
    bitReverse x (k + 1) 0 = 2 ^ k * (x % 2) + bitReverse (x / 2) k 0 := by
  simp only [bitReverse]
  rw [bitReverse_acc, Nat.zero_mul, Nat.zero_add, Nat.mul_comm (x % 2) (2 ^ k)]

/-- `natToBits` of a bit-reversed value is the `cwOf` window: both list the low
    `k` bits of `x` in reading order. So `walkCanonical`'s accumulated value
    `c = bitReverse bitBuf.toNat k 0` has `natToBits c k = cwOf bitBuf.toNat k`,
    the exact codeword the canonical/tree spec consumes. -/
theorem natToBits_bitReverse (x k : Nat) :
    Huffman.Spec.natToBits (bitReverse x k 0) k = cwOf x k := by
  apply List.ext_getElem (by rw [Huffman.Spec.natToBits_length, cwOf_length])
  intro j h1 _
  rw [Huffman.Spec.natToBits_length] at h1
  rw [natToBits_getElem _ _ _ h1, cwOf_getElem x k j h1,
      bitReverse_testBit x k (k - 1 - j) (by omega)]
  congr 1; omega

/-- The low bit of the buffer as a `Nat`: `(buf &&& 1).toNat = buf.toNat % 2`. -/
theorem and_one_toNat (buf : UInt64) : (buf &&& 1).toNat = buf.toNat % 2 := by
  rw [UInt64.toNat_and, show (1 : UInt64).toNat = 1 from rfl, Nat.and_one_is_mod]

/-- Shifting the buffer right by one bit halves its `Nat` value. -/
theorem shr_one_toNat (buf : UInt64) : (buf >>> (1 : UInt64)).toNat = buf.toNat / 2 := by
  rw [UInt64.toNat_shiftRight, show (1 : UInt64).toNat % 64 = 1 from rfl,
      Nat.shiftRight_eq_div_pow, Nat.pow_one]

/-- Single-shift composition: `(buf >>> 1) >>> m = buf >>> (m+1)` for `m+1 < 64`. -/
theorem ushr_succ (buf : UInt64) (m : Nat) (hm : m + 1 < 64) :
    (buf >>> (1 : UInt64)) >>> ((m : Nat).toUInt64) = buf >>> ((m + 1 : Nat).toUInt64) := by
  apply UInt64.toNat_inj.mp
  have hm' : (m : Nat).toUInt64.toNat % 64 = m := by
    simp [Nat.toUInt64, UInt64.toNat_ofNat]; omega
  have hm1' : (m + 1 : Nat).toUInt64.toNat % 64 = m + 1 := by
    simp [Nat.toUInt64, UInt64.toNat_ofNat]; omega
  rw [UInt64.toNat_shiftRight, UInt64.toNat_shiftRight, UInt64.toNat_shiftRight,
      show (1 : UInt64).toNat % 64 = 1 from rfl, hm', hm1',
      show m + 1 = 1 + m from by omega, Nat.shiftRight_add]

/-- One accumulation step: reading the low bit `buf % 2` as the new MSB grows the
    `(k+1)`-bit value by `code · 2^(k+1) + bitReverse buf (k+1)`. -/
theorem accum_step (code buf k : Nat) :
    code * 2 ^ (k + 1) + bitReverse buf (k + 1) 0
      = (code * 2 + buf % 2) * 2 ^ k + bitReverse (buf / 2) k 0 := by
  rw [bitReverse_succ, Nat.pow_succ, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm 2 (2 ^ k),
      Nat.mul_comm (buf % 2) (2 ^ k)]
  omega

/-! ## `walkCanonical` forward characterization

`walkCanonical` reads the buffer LSB-first, accumulating `code := code*2 + bit`.
A successful run consumes `used` bits forming the value `bitReverse buf.toNat
used 0`, lands in length `used`'s canonical range, and returns the symbol whose
codeword is `cwOf buf.toNat used`. The generalized `go` form carries the partial
accumulator `code` (the bits read before this call). -/

/-- Generalized `walkCanonical.go` success characterization, by fuel induction on
    `maxBits + 1 - len`. -/
theorem walkCanonical_go_ok (lengths : Array UInt8) (maxBits : Nat) (hmb : 1 ≤ maxBits)
    (hmb64 : maxBits < 64)
    (ld : LongDecode) (hld : ld = buildLongDecode lengths maxBits) :
    ∀ (fuel len code : Nat) (buf : UInt64) (cnt : Nat) (sym : UInt16) (bb : UInt64) (c used : Nat),
      maxBits + 1 - len ≤ fuel → 1 ≤ len →
      walkCanonical.go ld maxBits len code buf cnt = .ok (sym, bb, c, used) →
      len ≤ used ∧ used ≤ maxBits ∧ used + 1 - len ≤ cnt ∧
        bb = buf >>> ((used + 1 - len : Nat).toUInt64) ∧ c = cnt - (used + 1 - len) ∧
        ∃ s, s < lengths.size ∧ sym = s.toUInt16 ∧ lengths[s]!.toNat = used ∧
          Huffman.Spec.codeFor (lengths.toList.map UInt8.toNat) maxBits s
            = some (Huffman.Spec.natToBits
                (code * 2 ^ (used + 1 - len) + bitReverse buf.toNat (used + 1 - len) 0) used) := by
  subst hld
  intro fuel
  induction fuel with
  | zero =>
    intro len code buf cnt sym bb c used hfuel hlen1 h
    rw [walkCanonical.go, dif_pos (by omega : len > maxBits)] at h
    exact absurd h (by simp)
  | succ fuel ih =>
    intro len code buf cnt sym bb c used hfuel hlen1 h
    rw [walkCanonical.go] at h
    by_cases hlen : len > maxBits
    · rw [dif_pos hlen] at h; exact absurd h (by simp)
    · rw [dif_neg hlen] at h
      by_cases hcnt0 : cnt = 0
      · rw [if_pos hcnt0] at h; exact absurd h (by simp)
      · rw [if_neg hcnt0] at h
        have h1u : (1 : Nat).toUInt64 = (1 : UInt64) := rfl
        simp only [] at h
        split at h
        · -- matched at length `len`: used = len
          rename_i hmatch
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨hsym, hbb, hc, hused⟩ := h
          subst hused
          refine ⟨Nat.le_refl _, by omega, by omega, ?_, by omega, ?_⟩
          · rw [← hbb, show len + 1 - len = 1 from by omega, h1u]
          · rw [show len + 1 - len = 1 from by omega]
            have hval : code * 2 ^ 1 + bitReverse buf.toNat 1 0
                = code * 2 + (buf &&& 1).toNat := by
              rw [and_one_toNat]; simp [bitReverse, Nat.pow_one]
            rw [hval]
            obtain ⟨s, hs, hlen_s, hcf, hsymlk⟩ :=
              codeFor_of_value lengths maxBits hmb len (code * 2 + (buf &&& 1).toNat)
                hlen1 (by omega) hmatch.1 hmatch.2
            exact ⟨s, hs, hsym.symm.trans hsymlk, hlen_s, hcf⟩
        · -- no match: recurse at len+1
          rename_i hmatch
          obtain ⟨hlu, humax, hcnt', hbb, hc, s, hs, hsym, hlen_s, hcf⟩ :=
            ih (len + 1) (code * 2 + (buf &&& 1).toNat) (buf >>> 1) (cnt - 1) sym bb c used
              (by omega) (by omega) h
          have hexp : used + 1 - (len + 1) = used + 1 - len - 1 := by omega
          have hsplit : used + 1 - len = (used + 1 - len - 1) + 1 := by omega
          refine ⟨by omega, humax, by omega, ?_, by omega, s, hs, hsym, hlen_s, ?_⟩
          · rw [hbb, hexp, ushr_succ buf (used + 1 - len - 1) (by omega),
                show used + 1 - len - 1 + 1 = used + 1 - len from by omega]
          · rw [hcf, hexp, Option.some.injEq]
            congr 1
            rw [and_one_toNat, shr_one_toNat, hsplit]
            exact (accum_step code buf.toNat (used + 1 - len - 1)).symm

/-- **`walkCanonical` success characterization.** A successful `walkCanonical`
    consumes `used` bits (`1 ≤ used ≤ maxBits`, `used ≤ cnt`), advances the buffer
    by `used`, and returns the symbol `s` whose canonical codeword is exactly the
    `used`-bit window `cwOf buf.toNat used` the spec reads. -/
theorem walkCanonical_ok_spec (lengths : Array UInt8) (maxBits : Nat) (hmb : 1 ≤ maxBits)
    (hmb64 : maxBits < 64) (buf : UInt64) (cnt : Nat) (sym : UInt16) (bb : UInt64) (c used : Nat)
    (h : walkCanonical (buildLongDecode lengths maxBits) maxBits buf cnt = .ok (sym, bb, c, used)) :
    1 ≤ used ∧ used ≤ maxBits ∧ used ≤ cnt ∧
      bb = buf >>> (used : Nat).toUInt64 ∧ c = cnt - used ∧
      ∃ s, s < lengths.size ∧ sym = s.toUInt16 ∧ lengths[s]!.toNat = used ∧
        Huffman.Spec.codeFor (lengths.toList.map UInt8.toNat) maxBits s
          = some (cwOf buf.toNat used) := by
  obtain ⟨hlu, humax, hcnt, hbb, hc, s, hs, hsym, hlen_s, hcf⟩ :=
    walkCanonical_go_ok lengths maxBits hmb hmb64 _ rfl (maxBits + 1) 1 0 buf cnt sym bb c used
      (by omega) (Nat.le_refl _) h
  refine ⟨by omega, humax, by omega, ?_, by omega, s, hs, hsym, hlen_s, ?_⟩
  · rw [hbb, show used + 1 - 1 = used from by omega]
  · rw [hcf, Option.some.injEq, show used + 1 - 1 = used from by omega, Nat.zero_mul,
        Nat.zero_add, natToBits_bitReverse]

/-! ## `walkCanonical` completeness

The converse of `walkCanonical_ok_spec`: if the buffer bits spell a genuine
codeword (`codeFor s = cwOf buf.toNat L` for `L ≤ cnt`), `walkCanonical` succeeds
returning `s` after `L` bits. Prefix-freeness guarantees it does not match at any
shorter length first. -/

/-- `natToBits val (w₁ + w₂)` splits into the high `w₁` bits then the low `w₂`.
    Local copy of the `private` `Huffman.Spec.natToBits_append`. -/
theorem natToBits_append (val w₁ w₂ : Nat) :
    Huffman.Spec.natToBits val (w₁ + w₂)
      = Huffman.Spec.natToBits (val / 2 ^ w₂) w₁ ++ Huffman.Spec.natToBits val w₂ := by
  induction w₁ with
  | zero => simp only [Nat.zero_add, Huffman.Spec.natToBits, List.nil_append]
  | succ n ih =>
    rw [Nat.add_right_comm]
    simp only [Huffman.Spec.natToBits]
    rw [ih, List.cons_append, ← Nat.testBit_div_two_pow]

/-- Generalized completeness of `walkCanonical.go`, by fuel induction. `code`
    (`< 2^(len-1)`) is the value of the `len-1` bits already read; the buffer's
    next `L-(len-1)` bits complete symbol `s`'s length-`L` codeword. -/
theorem walkCanonical_go_complete (lengths : Array UInt8) (maxBits : Nat) (hmb : 1 ≤ maxBits)
    (hmb64 : maxBits < 64)
    (hv : Huffman.Spec.ValidLengths (lengths.toList.map UInt8.toNat) maxBits)
    (s L : Nat) (hL : L ≤ maxBits) :
    ∀ (fuel len code : Nat) (buf : UInt64) (cnt : Nat),
      maxBits + 1 - len ≤ fuel → 1 ≤ len → len ≤ L → L - (len - 1) ≤ cnt →
      code < 2 ^ (len - 1) →
      Huffman.Spec.codeFor (lengths.toList.map UInt8.toNat) maxBits s
        = some (Huffman.Spec.natToBits
            (code * 2 ^ (L - (len - 1)) + bitReverse buf.toNat (L - (len - 1)) 0) L) →
      walkCanonical.go (buildLongDecode lengths maxBits) maxBits len code buf cnt
        = .ok (s.toUInt16, buf >>> ((L - (len - 1) : Nat).toUInt64), cnt - (L - (len - 1)), L) := by
  intro fuel
  induction fuel with
  | zero => intro len code buf cnt hfuel hlen1 hlenL hcnt _ _; omega
  | succ fuel ih =>
    intro len code buf cnt hfuel hlen1 hlenL hcnt hcode hcf
    have hlmax : len ≤ maxBits := by omega
    have hlow : (buf &&& 1).toNat = buf.toNat % 2 := and_one_toNat buf
    -- accumulation: the full codeword value, viewed one bit deeper
    have hCVAL : code * 2 ^ (L - (len - 1)) + bitReverse buf.toNat (L - (len - 1)) 0
        = (code * 2 + (buf &&& 1).toNat) * 2 ^ (L - len)
          + bitReverse (buf.toNat / 2) (L - len) 0 := by
      rw [hlow, show L - (len - 1) = (L - len) + 1 from by omega]
      exact accum_step code buf.toNat (L - len)
    rw [walkCanonical.go, dif_neg (by omega : ¬ len > maxBits), if_neg (by omega : ¬ cnt = 0)]
    simp only []
    have hc'_lt : code * 2 + (buf &&& 1).toNat < 2 ^ len := by
      have hbit : (buf &&& 1).toNat < 2 := by rw [hlow]; omega
      rw [show len = (len - 1) + 1 from by omega, Nat.pow_succ]; omega
    by_cases hLlen : len = L
    · -- final bit: the value lands in length-`L`'s range, returning `s`
      subst hLlen
      have hval : code * 2 ^ (len - (len - 1)) + bitReverse buf.toNat (len - (len - 1)) 0
          = code * 2 + (buf &&& 1).toNat := by
        rw [show len - (len - 1) = 1 from by omega, hlow]
        simp [bitReverse, Nat.pow_one]
      have hcf' : Huffman.Spec.codeFor (lengths.toList.map UInt8.toNat) maxBits s
          = some (Huffman.Spec.natToBits (code * 2 + (buf &&& 1).toNat) len) := by rw [hcf, hval]
      obtain ⟨hslen, hlenbnd, hcfval⟩ := Huffman.Spec.codeFor_spec hcf'
      have hsize : s < lengths.size := by
        rw [List.length_map, Array.length_toList] at hslen; exact hslen
      have hsidx : (lengths.toList.map UInt8.toNat)[s]'hslen = lengths[s]!.toNat :=
        map_toNat_getElem lengths s hsize
      have hbnds := Huffman.Spec.codeFor_len_bounds (hsidx ▸ hlenbnd)
      have hpos : 0 < lengths[s]!.toNat := Nat.pos_of_ne_zero hbnds.1
      have hposm : lengths[s]!.toNat ≤ maxBits := hbnds.2
      have hlen_eq : lengths[s]!.toNat = len := by
        have := congrArg List.length hcfval
        rw [Huffman.Spec.natToBits_length, Huffman.Spec.natToBits_length, hsidx] at this; omega
      -- placed value `firstCode[len] + numEarlier` equals the read value
      have hcfp := codeFor_placed lengths maxBits s hsize hpos hposm
      rw [hlen_eq] at hcfp
      have hfc_len : (Huffman.Spec.nextCodes
            (Huffman.Spec.countLengths (lengths.toList.map UInt8.toNat) maxBits) maxBits)[len]!
          = (buildLongDecode lengths maxBits).firstCode[len]! := by
        show _ = (Huffman.Spec.nextCodes (countLengthsFast lengths maxBits) maxBits)[len]!
        rw [countLengthsFast_eq]
      have hcb := Huffman.Spec.code_value_bound (lengths.toList.map UInt8.toNat) maxBits s hv
        hslen (hsidx ▸ hlenbnd)
      rw [hsidx, hlen_eq] at hcb
      have hceq : (buildLongDecode lengths maxBits).firstCode[len]! +
          numEarlier (lengths.toList.map UInt8.toNat) len s = code * 2 + (buf &&& 1).toNat := by
        have hinj := Huffman.Spec.natToBits_injective _ _ _ hcb hc'_lt
          (hcfp.symm.trans hcf' |> Option.some.inj)
        rw [← hfc_len]; exact hinj
      have hnum_lt : numEarlier (lengths.toList.map UInt8.toNat) len s
          < (buildLongDecode lengths maxBits).count[len]! := by
        show _ < (countLengthsFast lengths maxBits)[len]!
        rw [numEarlier_size_eq lengths maxBits len (by omega) hlmax]
        exact numEarlier_lt_arr lengths s lengths.size len hsize hlen_eq hsize (Nat.le_refl _)
      have hcond : (buildLongDecode lengths maxBits).firstCode[len]! ≤ code * 2 + (buf &&& 1).toNat ∧
          code * 2 + (buf &&& 1).toNat < (buildLongDecode lengths maxBits).firstCode[len]!
            + (buildLongDecode lengths maxBits).count[len]! := by omega
      rw [if_pos hcond]
      have hsymlk : (buildLongDecode lengths maxBits).symbols[
          (buildLongDecode lengths maxBits).firstIndex[len]! +
          (code * 2 + (buf &&& 1).toNat - (buildLongDecode lengths maxBits).firstCode[len]!)]!
          = s.toUInt16 := by
        rw [show code * 2 + (buf &&& 1).toNat - (buildLongDecode lengths maxBits).firstCode[len]!
              = numEarlier (lengths.toList.map UInt8.toNat) len s from by omega]
        have := buildLongDecode_placement lengths maxBits hmb s hsize hpos hposm
        rwa [hlen_eq] at this
      rw [hsymlk, show len - (len - 1) = 1 from by omega,
          show ((1 : Nat).toUInt64) = (1 : UInt64) from rfl]
    · -- len < L : no match here (prefix-free); recurse one bit deeper
      have hltL : len < L := by omega
      have hnomatch : ¬ ((buildLongDecode lengths maxBits).firstCode[len]! ≤ code * 2 + (buf &&& 1).toNat ∧
          code * 2 + (buf &&& 1).toNat < (buildLongDecode lengths maxBits).firstCode[len]!
            + (buildLongDecode lengths maxBits).count[len]!) := by
        rintro hcond
        obtain ⟨s', hs', hlen_s', hcf_s', _⟩ :=
          codeFor_of_value lengths maxBits hmb len (code * 2 + (buf &&& 1).toNat)
            (by omega) hlmax hcond.1 hcond.2
        have hne : s' ≠ s := by
          rintro rfl
          have heq := hcf_s'.symm.trans hcf
          rw [Option.some.injEq] at heq
          have := congrArg List.length heq
          rw [Huffman.Spec.natToBits_length, Huffman.Spec.natToBits_length] at this; omega
        have hdiv : (code * 2 ^ (L - (len - 1)) + bitReverse buf.toNat (L - (len - 1)) 0)
            / 2 ^ (L - len) = code * 2 + (buf &&& 1).toNat := by
          rw [hCVAL, Nat.mul_comm (code * 2 + (buf &&& 1).toNat) (2 ^ (L - len)),
              Nat.mul_add_div (Nat.two_pow_pos (L - len)),
              Nat.div_eq_of_lt (bitReverse_lt _ _), Nat.add_zero]
        have happ : Huffman.Spec.natToBits (code * 2 + (buf &&& 1).toNat) len
            ++ Huffman.Spec.natToBits
                (code * 2 ^ (L - (len - 1)) + bitReverse buf.toNat (L - (len - 1)) 0) (L - len)
            = Huffman.Spec.natToBits
                (code * 2 ^ (L - (len - 1)) + bitReverse buf.toNat (L - (len - 1)) 0) L := by
          have e := natToBits_append
            (code * 2 ^ (L - (len - 1)) + bitReverse buf.toNat (L - (len - 1)) 0) len (L - len)
          rw [show len + (L - len) = L from by omega, hdiv] at e
          exact e.symm
        exact Huffman.Spec.canonical_prefix_free (lengths.toList.map UInt8.toNat) maxBits hv
          s' s _ _ hcf_s' hcf hne ⟨_, happ⟩
      rw [if_neg hnomatch]
      have hexp : L - ((len + 1) - 1) = L - len := by omega
      have hrec := ih (len + 1) (code * 2 + (buf &&& 1).toNat) (buf >>> 1) (cnt - 1)
        (by omega) (by omega) (by omega) (by omega)
        (by rw [show (len + 1) - 1 = len from by omega]; exact hc'_lt)
        (by rw [hexp, hcf, hCVAL, shr_one_toNat])
      rw [hrec, hexp, ushr_succ buf (L - len) (by omega),
          show L - len + 1 = L - (len - 1) from by omega,
          show cnt - 1 - (L - len) = cnt - (L - (len - 1)) from by omega]

/-- **`walkCanonical` completeness.** If the buffer bits spell symbol `s`'s
    canonical codeword (`codeFor s = cwOf buf.toNat L`, `L ≤ cnt`), `walkCanonical`
    succeeds: it returns `s` after consuming exactly `L` bits. -/
theorem walkCanonical_complete (lengths : Array UInt8) (maxBits : Nat) (hmb : 1 ≤ maxBits)
    (hmb64 : maxBits < 64)
    (hv : Huffman.Spec.ValidLengths (lengths.toList.map UInt8.toNat) maxBits)
    (s L : Nat) (hL1 : 1 ≤ L) (hL : L ≤ maxBits) (buf : UInt64) (cnt : Nat) (hcnt : L ≤ cnt)
    (hcf : Huffman.Spec.codeFor (lengths.toList.map UInt8.toNat) maxBits s
        = some (cwOf buf.toNat L)) :
    walkCanonical (buildLongDecode lengths maxBits) maxBits buf cnt
      = .ok (s.toUInt16, buf >>> (L : Nat).toUInt64, cnt - L, L) := by
  have h := walkCanonical_go_complete lengths maxBits hmb hmb64 hv s L hL (maxBits + 1) 1 0 buf cnt
    (by omega) (Nat.le_refl _) hL1 (by omega) (by simp) (by
      rw [show L - (1 - 1) = L from by omega, Nat.zero_mul, Nat.zero_add, natToBits_bitReverse]
      exact hcf)
  rwa [show L - (1 - 1) = L from by omega] at h

/-! ## `walkTree` success characterization (mirror of `walkCanonical`)

`walkTree` and `walkCanonical` read the same `bitBuf`. To relate them I give
`walkTree` the same kind of forward/backward characterization, then prove they
succeed on exactly the same inputs (`walkCanonical_ok_iff_walkTree`). All in
UInt64-land — no BitReader. -/

open Zip.Native.InflateBuf (walkTree decodeSym)

/-- `buf >>> (0 : Nat) = buf`. -/
theorem ushr_zero (buf : UInt64) : buf >>> ((0 : Nat).toUInt64) = buf := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_shiftRight, show (0 : Nat).toUInt64.toNat % 64 = 0 from by decide,
      Nat.shiftRight_zero]

/-- The `cwOf` head bit is `walkTree`'s branch test (`buf &&& 1 == 0` chooses the
    left/`false` child). -/
theorem cwOf_head_branch (buf : UInt64) :
    (buf.toNat % 2 == 1) = !(buf &&& 1 == 0) := by
  have hand : (buf &&& 1).toNat = buf.toNat % 2 := and_one_toNat buf
  rcases (show buf.toNat % 2 = 0 ∨ buf.toNat % 2 = 1 from by omega) with hm | hm
  · have h0 : buf &&& 1 = 0 := UInt64.toNat_inj.mp (by rw [hand, hm]; rfl)
    rw [hm]; simp [h0]
  · have h1 : buf &&& 1 = 1 := UInt64.toNat_inj.mp (by rw [hand, hm]; rfl)
    rw [hm]; simp [h1]

/-- **`walkTree` forward.** A successful `walkTree` reaches a leaf whose path is
    the `used`-bit window `cwOf buf.toNat used`, advancing the buffer by `used`. -/
theorem walkTree_ok_spec (t : HuffTree) :
    ∀ (buf : UInt64) (cnt depth : Nat) (sym : UInt16) (bb : UInt64) (c used : Nat),
      depth ≤ 21 → walkTree t buf cnt depth = .ok (sym, bb, c, used) →
      Deflate.Correctness.TreeHasLeaf t (cwOf buf.toNat used) sym ∧
        bb = buf >>> (used : Nat).toUInt64 ∧ depth + used ≤ 21 := by
  induction t with
  | leaf s =>
    intro buf cnt depth sym bb c used hd h
    simp only [walkTree, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, _, rfl⟩ := h
    exact ⟨by rw [show cwOf buf.toNat 0 = [] from rfl]; exact Deflate.Correctness.TreeHasLeaf.leaf,
      (ushr_zero buf).symm, by omega⟩
  | empty => intro buf cnt depth sym bb c used hd h; simp only [walkTree] at h; exact absurd h (by simp)
  | node z o ihz iho =>
    intro buf cnt depth sym bb c used hd h
    rw [walkTree] at h
    by_cases hdg : depth > 20
    · rw [if_pos hdg] at h; exact absurd h (by simp)
    · rw [if_neg hdg] at h
      by_cases hcnt : cnt = 0
      · rw [if_pos hcnt] at h; exact absurd h (by simp)
      · rw [if_neg hcnt] at h
        by_cases hb : (buf &&& 1 == 0) = true
        · rw [if_pos hb] at h
          cases hrec : walkTree z (buf >>> 1) (cnt - 1) (depth + 1) with
          | error e => rw [hrec] at h; exact absurd h (by simp)
          | ok r =>
            obtain ⟨s', bb', c', u'⟩ := r
            rw [hrec] at h
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl, rfl⟩ := h
            obtain ⟨hleaf, hbb, hdu⟩ := ihz (buf >>> 1) (cnt - 1) (depth + 1) s' bb' c' u'
              (by omega) hrec
            refine ⟨?_, ?_, by omega⟩
            · rw [show cwOf buf.toNat (u' + 1) = false :: cwOf (buf >>> 1).toNat u' from by
                  rw [cwOf, ← shr_one_toNat, cwOf_head_branch]; simp [hb]]
              exact Deflate.Correctness.TreeHasLeaf.left hleaf
            · rw [hbb, ushr_succ buf u' (by omega)]
        · rw [if_neg hb] at h
          cases hrec : walkTree o (buf >>> 1) (cnt - 1) (depth + 1) with
          | error e => rw [hrec] at h; exact absurd h (by simp)
          | ok r =>
            obtain ⟨s', bb', c', u'⟩ := r
            rw [hrec] at h
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl, rfl⟩ := h
            obtain ⟨hleaf, hbb, hdu⟩ := iho (buf >>> 1) (cnt - 1) (depth + 1) s' bb' c' u'
              (by omega) hrec
            refine ⟨?_, ?_, by omega⟩
            · rw [show cwOf buf.toNat (u' + 1) = true :: cwOf (buf >>> 1).toNat u' from by
                  rw [cwOf, ← shr_one_toNat, cwOf_head_branch]; simp [hb]]
              exact Deflate.Correctness.TreeHasLeaf.right hleaf
            · rw [hbb, ushr_succ buf u' (by omega)]

/-- **`walkTree` completeness.** If the tree has a leaf `sym` on the path
    `cwOf buf.toNat L` and the buffer has `≥ L` bits within the depth budget,
    `walkTree` succeeds returning `sym` after `L` bits. -/
theorem walkTree_complete (t : HuffTree) (cw : List Bool) (sym : UInt16)
    (hleaf : Deflate.Correctness.TreeHasLeaf t cw sym) :
    ∀ (buf : UInt64) (cnt depth : Nat),
      cw = cwOf buf.toNat cw.length → cw.length ≤ cnt → depth + cw.length ≤ 21 →
      walkTree t buf cnt depth
        = .ok (sym, buf >>> (cw.length : Nat).toUInt64, cnt - cw.length, cw.length) := by
  induction hleaf with
  | leaf =>
    intro buf cnt depth _ _ _
    simp only [List.length_nil, Nat.sub_zero]
    rw [walkTree, ushr_zero]
  | @left z cw' s o hl ih =>
    intro buf cnt depth hcweq hlen hdep
    simp only [List.length_cons] at hlen hdep hcweq ⊢
    rw [cwOf] at hcweq
    have hhead : (buf.toNat % 2 == 1) = false := by
      have := (List.cons.injEq _ _ _ _).mp hcweq; exact this.1.symm
    have htail : cw' = cwOf (buf >>> 1).toNat cw'.length := by
      have := (List.cons.injEq _ _ _ _).mp hcweq; rw [shr_one_toNat]; exact this.2
    have hb : (buf &&& 1 == 0) = true := by
      have := cwOf_head_branch buf; rw [hhead] at this; simpa using this.symm
    rw [walkTree, if_neg (by omega : ¬ depth > 20), if_neg (by omega : ¬ cnt = 0), if_pos hb,
        ih (buf >>> 1) (cnt - 1) (depth + 1) htail (by omega) (by omega),
        ushr_succ buf cw'.length (by omega),
        show cnt - 1 - cw'.length = cnt - (cw'.length + 1) from by omega]
  | @right o cw' s z ho ih =>
    intro buf cnt depth hcweq hlen hdep
    simp only [List.length_cons] at hlen hdep hcweq ⊢
    rw [cwOf] at hcweq
    have hhead : (buf.toNat % 2 == 1) = true := by
      have := (List.cons.injEq _ _ _ _).mp hcweq; exact this.1.symm
    have htail : cw' = cwOf (buf >>> 1).toNat cw'.length := by
      have := (List.cons.injEq _ _ _ _).mp hcweq; rw [shr_one_toNat]; exact this.2
    have hb : (buf &&& 1 == 0) = false := by
      have := cwOf_head_branch buf; rw [hhead] at this; simpa using this.symm
    rw [walkTree, if_neg (by omega : ¬ depth > 20), if_neg (by omega : ¬ cnt = 0), if_neg (by simp [hb]),
        ih (buf >>> 1) (cnt - 1) (depth + 1) htail (by omega) (by omega),
        ushr_succ buf cw'.length (by omega),
        show cnt - 1 - cw'.length = cnt - (cw'.length + 1) from by omega]

/-- **`walkCanonical` and `walkTree` accept exactly the same inputs.** For valid
    lengths, the canonical long-code decode and the tree walk over the same buffer
    succeed on the same inputs with the *same* result — even though their error
    strings may differ. This is the per-symbol bridge that lets the tree-free
    decoder join the verified path. -/
theorem walkCanonical_ok_iff_walkTree (lengths : Array UInt8) (maxBits : Nat)
    (hmb : 1 ≤ maxBits) (hmb15 : maxBits ≤ 15)
    (hv : Huffman.Spec.ValidLengths (lengths.toList.map UInt8.toNat) maxBits)
    (hbound : lengths.size ≤ UInt16.size)
    (buf : UInt64) (cnt : Nat) (r : UInt16 × UInt64 × Nat × Nat) :
    walkCanonical (buildLongDecode lengths maxBits) maxBits buf cnt = .ok r ↔
      walkTree (fromLengthsTree lengths maxBits) buf cnt 0 = .ok r := by
  obtain ⟨sym, bb, c, used⟩ := r
  constructor
  · intro h
    obtain ⟨h1used, humax, hcnt, hbb, hc, s, hs, hsym, hlen_s, hcf⟩ :=
      walkCanonical_ok_spec lengths maxBits hmb (by omega) buf cnt sym bb c used h
    have hmem : (s, cwOf buf.toNat used)
        ∈ Huffman.Spec.allCodes (lengths.toList.map UInt8.toNat) maxBits :=
      (Huffman.Spec.allCodes_mem_iff _ maxBits s _).mpr
        ⟨by rw [List.length_map, Array.length_toList]; exact hs, hcf⟩
    have hleaf : Deflate.Correctness.TreeHasLeaf (fromLengthsTree lengths maxBits)
        (cwOf buf.toNat used) s.toUInt16 :=
      Deflate.Correctness.fromLengths_hasLeaf lengths maxBits (by omega) _
        (fromLengths_ok_of_valid lengths maxBits hv) hv s _ hmem
    have hwt := walkTree_complete (fromLengthsTree lengths maxBits) (cwOf buf.toNat used)
      s.toUInt16 hleaf buf cnt 0 (by rw [cwOf_length]) (by rw [cwOf_length]; exact hcnt)
      (by rw [cwOf_length]; omega)
    rw [cwOf_length] at hwt
    rw [hsym, hbb, hc]; exact hwt
  · intro h
    obtain ⟨hleaf, hbb, hdu⟩ :=
      walkTree_ok_spec (fromLengthsTree lengths maxBits) buf cnt 0 sym bb c used (by omega) h
    have hcons : c + used = cnt := InflateBuf.walkTree_consumed _ h
    have hmem := Deflate.Correctness.fromLengths_leaf_spec lengths maxBits (by omega) _
      (fromLengths_ok_of_valid lengths maxBits hv) hv hbound _ _ hleaf
    rw [Huffman.Spec.allCodes_mem_iff] at hmem
    obtain ⟨hsymlt, hcf⟩ := hmem
    obtain ⟨_, hlenbnd, hcwval⟩ := Huffman.Spec.codeFor_spec hcf
    have ⟨hpos, hposm⟩ := Huffman.Spec.codeFor_len_bounds hlenbnd
    have hused_eq : (lengths.toList.map UInt8.toNat)[sym.toNat]'hsymlt = used := by
      have := congrArg List.length hcwval
      rw [Huffman.Spec.natToBits_length, cwOf_length] at this; omega
    rw [hused_eq] at hpos hposm
    have hwc := walkCanonical_complete lengths maxBits hmb (by omega) hv sym.toNat used
      (by omega) hposm buf cnt (by omega) hcf
    have hsymrt : sym.toNat.toUInt16 = sym := by
      have : sym.toNat.toUInt16 = UInt16.ofNat sym.toNat := rfl
      rw [this, UInt16.ofNat_toNat]
    rw [hwc, hsymrt, ← hbb, show cnt - used = c from by omega]

/-- **`decodeSymCanon` and `decodeSym` accept the same inputs.** They share the
    9-bit table branch verbatim; the long-code fallback agrees by
    `walkCanonical_ok_iff_walkTree`. -/
theorem decodeSymCanon_ok_iff_decodeSym (lengths : Array UInt8) (maxBits : Nat)
    (hmb : 1 ≤ maxBits) (hmb15 : maxBits ≤ 15)
    (hv : Huffman.Spec.ValidLengths (lengths.toList.map UInt8.toNat) maxBits)
    (hbound : lengths.size ≤ UInt16.size)
    (table : DecodeTable) (buf : UInt64) (cnt : Nat) (r : UInt16 × UInt64 × Nat × Nat) :
    decodeSymCanon (buildLongDecode lengths maxBits) table maxBits buf cnt = .ok r ↔
      decodeSym (fromLengthsTree lengths maxBits) table buf cnt = .ok r := by
  simp only [decodeSymCanon, decodeSym]
  split
  · exact walkCanonical_ok_iff_walkTree lengths maxBits hmb hmb15 hv hbound buf cnt r
  · exact Iff.rfl

/-- A successful `walkCanonical` leaves at most `cnt` bits (it only consumes). -/
theorem walkCanonical_go_cnt_le (ld : LongDecode) (maxBits : Nat) :
    ∀ (fuel len code : Nat) (buf : UInt64) (cnt : Nat) (sym : UInt16) (bb : UInt64) (c used : Nat),
      maxBits + 1 - len ≤ fuel →
      walkCanonical.go ld maxBits len code buf cnt = .ok (sym, bb, c, used) → c ≤ cnt := by
  intro fuel
  induction fuel with
  | zero => intro len code buf cnt sym bb c used hf h
            rw [walkCanonical.go, dif_pos (by omega)] at h; exact absurd h (by simp)
  | succ fuel ih =>
    intro len code buf cnt sym bb c used hf h
    rw [walkCanonical.go] at h
    by_cases hlen : len > maxBits
    · rw [dif_pos hlen] at h; exact absurd h (by simp)
    · rw [dif_neg hlen] at h
      by_cases hcnt : cnt = 0
      · rw [if_pos hcnt] at h; exact absurd h (by simp)
      · rw [if_neg hcnt] at h
        simp only at h
        split at h
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h; omega
        · have := ih (len + 1) _ (buf >>> 1) (cnt - 1) sym bb c used (by omega) h; omega

/-- `walkCanonical` never increases the bit count. -/
theorem walkCanonical_cnt_le (ld : LongDecode) (maxBits : Nat) (buf : UInt64) (cnt : Nat)
    {sym : UInt16} {bb : UInt64} {c used : Nat}
    (h : walkCanonical ld maxBits buf cnt = .ok (sym, bb, c, used)) : c ≤ cnt :=
  walkCanonical_go_cnt_le ld maxBits (maxBits + 1) 1 0 buf cnt sym bb c used (by omega) h

/-- `decodeSymCanon` never increases the bit count (table or long-code path). -/
theorem decodeSymCanon_cnt_le (ld : LongDecode) (table : DecodeTable) (maxBits : Nat)
    (buf : UInt64) (cnt : Nat) {s : UInt16} {bb : UInt64} {c used : Nat}
    (h : decodeSymCanon ld table maxBits buf cnt = .ok (s, bb, c, used)) : c ≤ cnt := by
  simp only [decodeSymCanon] at h
  split at h
  · exact walkCanonical_cnt_le ld maxBits buf cnt h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h; omega

/-- The fast canonical table build equals the tree-built table (composition of the
    two merged refinements), so the tree-free decoder uses the verified table. -/
theorem buildTableCanonicalFast_eq_buildTable (lengths : Array UInt8) (maxBits : Nat)
    (hmb : maxBits < 32) (hv : Huffman.Spec.ValidLengths (lengths.toList.map UInt8.toNat) maxBits)
    (hbound : lengths.size ≤ UInt16.size) :
    buildTableCanonicalFast lengths maxBits = (fromLengthsTree lengths maxBits).buildTable := by
  rw [buildTableCanonicalFast_eq, buildTableCanonical_eq lengths maxBits hmb hv hbound]

end Zip.Native.HuffTree

namespace Zip.Native.InflateBuf
open ZipCommon (BitReader)
open Zip.Native.HuffTree (buildLongDecode fromLengthsTree decodeSymCanon decodeSymCanon_ok_iff_decodeSym
  buildTableCanonicalFast buildTableCanonicalFast_eq_buildTable)

/-- If two `Except` values succeed on the same outputs, binding both with the same
    continuation preserves that (success-)equivalence. -/
theorem bind_ok_iff {α β : Type} {f g : Except String α} (h : ∀ x, f = .ok x ↔ g = .ok x)
    (k : α → Except String β) (r : β) : (f >>= k) = .ok r ↔ (g >>= k) = .ok r := by
  cases hf : f with
  | error e => cases hg : g with
    | error e' => simp [bind, Except.bind]
    | ok x => exact absurd ((h x).mpr hg) (by rw [hf]; simp)
  | ok x =>
    have hg : g = .ok x := (h x).mp hf
    rw [hg]

/-- **Tree-free symbol loop ≈ verified symbol loop.** For valid lengths, the
    tree-free wide-buffer loop and the verified `goFusedP` (with the proof-only
    trees `fromLengthsTree`) succeed on exactly the same inputs with the same
    result. The bodies are byte-identical except `decodeSymCanon` vs `decodeSym`,
    which agree on success (`decodeSymCanon_ok_iff_decodeSym`); on a decode error
    both loops reject. Recursive — its own `termination_by` provides the IH. -/
theorem goTreeFree_ok_iff_goFusedP (litTable distTable : HuffTree.DecodeTable)
    (litLengths distLengths : Array UInt8)
    (hlv : Huffman.Spec.ValidLengths (litLengths.toList.map UInt8.toNat) 15)
    (hlb : litLengths.size ≤ UInt16.size)
    (hdv : Huffman.Spec.ValidLengths (distLengths.toList.map UInt8.toNat) 15)
    (hdb : distLengths.size ≤ UInt16.size)
    (data : ByteArray) (maxOut : Nat) (pos : Nat) (bitBuf : UInt64) (cnt : Nat)
    (output : ByteArray) (r : ByteArray × Nat × UInt64 × Nat) :
    goTreeFree litTable distTable (buildLongDecode litLengths 15) (buildLongDecode distLengths 15)
        15 data maxOut pos bitBuf cnt output = .ok r ↔
      goFusedP litTable distTable data (fromLengthsTree litLengths 15) (fromLengthsTree distLengths 15)
        maxOut pos bitBuf cnt output = .ok r := by
  have hlit_iff := fun (b : UInt64) (n : Nat) (x : UInt16 × UInt64 × Nat × Nat) =>
    decodeSymCanon_ok_iff_decodeSym litLengths 15 (by omega) (by omega) hlv hlb litTable b n x
  have hdist_iff := fun (b : UInt64) (n : Nat) (x : UInt16 × UInt64 × Nat × Nat) =>
    decodeSymCanon_ok_iff_decodeSym distLengths 15 (by omega) (by omega) hdv hdb distTable b n x
  rw [goTreeFree, goFusedP]
  by_cases hrc : cnt ≤ 56 ∧ pos < data.size
  · rw [dif_pos hrc, dif_pos hrc]
    exact goTreeFree_ok_iff_goFusedP litTable distTable litLengths distLengths hlv hlb hdv hdb
      data maxOut (pos + 1) (bitBuf ||| (data[pos]!.toUInt64 <<< cnt.toUInt64)) (cnt + 8) output r
  · rw [dif_neg hrc, dif_neg hrc]
    by_cases hlit : (litTable.lenAt (bitBuf &&& 0x1FF).toNat).toNat ≠ 0
        ∧ (litTable.lenAt (bitBuf &&& 0x1FF).toNat).toNat ≤ cnt
        ∧ litTable.symAt (bitBuf &&& 0x1FF).toNat < 256
    · rw [dif_pos hlit, dif_pos hlit]
      by_cases hout : output.size ≥ maxOut
      · simp [hout]
      · rw [if_neg hout, if_neg hout]
        exact goTreeFree_ok_iff_goFusedP litTable distTable litLengths distLengths hlv hlb hdv hdb
          data maxOut pos (bitBuf >>> ((litTable.lenAt (bitBuf &&& 0x1FF).toNat).toNat).toUInt64)
          (cnt - (litTable.lenAt (bitBuf &&& 0x1FF).toNat).toNat)
          (output.push (litTable.symAt (bitBuf &&& 0x1FF).toNat).toUInt8) r
    · rw [dif_neg hlit, dif_neg hlit]
      -- literal/length symbol decode
      cases hdec : decodeSymCanon (buildLongDecode litLengths 15) litTable 15 bitBuf cnt with
      | error e =>
        cases hdec2 : decodeSym (fromLengthsTree litLengths 15) litTable bitBuf cnt with
        | error e' => simp
        | ok x => exact absurd ((hlit_iff bitBuf cnt x).mpr hdec2) (by rw [hdec]; simp)
      | ok x =>
        have hdec2 : decodeSym (fromLengthsTree litLengths 15) litTable bitBuf cnt = .ok x :=
          (hlit_iff bitBuf cnt x).mp hdec
        rw [hdec2]
        obtain ⟨sym, bb, c, used⟩ := x
        simp only []
        by_cases hsym : sym < 256
        · rw [if_pos hsym, if_pos hsym]
          by_cases hout : output.size ≥ maxOut
          · simp [hout]
          · rw [if_neg hout, if_neg hout]
            by_cases hnp : cnt ≤ c
            · simp [hnp]
            · rw [dif_neg hnp, dif_neg hnp]
              exact goTreeFree_ok_iff_goFusedP litTable distTable litLengths distLengths hlv hlb hdv hdb
                data maxOut pos bb c (output.push sym.toUInt8) r
        · rw [if_neg hsym, if_neg hsym]
          by_cases h256 : sym == 256
          · rw [if_pos h256, if_pos h256]
          · rw [if_neg h256, if_neg h256]
            by_cases hidx : sym.toNat - 257 ≥ Inflate.lengthBase.size
            · rw [dif_pos hidx, dif_pos hidx]
            · rw [dif_neg hidx, dif_neg hidx]
              cases htb : takeBits bb c (Inflate.lengthExtra[sym.toNat - 257]'(by
                  simp [Inflate.lengthExtra_size, Inflate.lengthBase_size] at hidx ⊢; omega)).toNat with
              | error e => simp [bind, Except.bind]
              | ok y =>
                obtain ⟨extraBits, bb2, c2⟩ := y
                simp only [bind, Except.bind]
                cases hdec3 : decodeSymCanon (buildLongDecode distLengths 15) distTable 15 bb2 c2 with
                | error e =>
                  cases hdec4 : decodeSym (fromLengthsTree distLengths 15) distTable bb2 c2 with
                  | error e' => simp
                  | ok z => exact absurd ((hdist_iff bb2 c2 z).mpr hdec4) (by rw [hdec3]; simp)
                | ok z =>
                  have hdec4 : decodeSym (fromLengthsTree distLengths 15) distTable bb2 c2 = .ok z :=
                    (hdist_iff bb2 c2 z).mp hdec3
                  rw [hdec4]
                  obtain ⟨distSym, bb3, c3, dused⟩ := z
                  simp only []
                  by_cases hdidx : distSym.toNat ≥ Inflate.distBase.size
                  · rw [dif_pos hdidx, dif_pos hdidx]
                  · rw [dif_neg hdidx, dif_neg hdidx]
                    cases htb2 : takeBits bb3 c3 (Inflate.distExtra[distSym.toNat]'(by
                        simp [Inflate.distExtra_size, Inflate.distBase_size] at hdidx ⊢; omega)).toNat with
                    | error e => simp [bind, Except.bind]
                    | ok w =>
                      obtain ⟨dExtraBits, bb4, c4⟩ := w
                      simp only [bind, Except.bind]
                      by_cases hz : Inflate.distBase[distSym.toNat].toNat + dExtraBits = 0
                      · rw [dif_pos hz, dif_pos hz]
                      · rw [dif_neg hz, dif_neg hz]
                        by_cases hds : Inflate.distBase[distSym.toNat].toNat + dExtraBits > output.size
                        · rw [dif_pos hds, dif_pos hds]
                        · rw [dif_neg hds, dif_neg hds]
                          by_cases hmo : output.size + (Inflate.lengthBase[sym.toNat - 257].toNat + extraBits) > maxOut
                          · rw [if_pos hmo, if_pos hmo]
                          · rw [if_neg hmo, if_neg hmo]
                            by_cases hnp : cnt ≤ c4
                            · rw [dif_pos hnp, dif_pos hnp]
                            · rw [dif_neg hnp, dif_neg hnp]
                              exact goTreeFree_ok_iff_goFusedP litTable distTable litLengths distLengths
                                hlv hlb hdv hdb data maxOut pos bb4 c4 _ r
  termination_by (data.size - pos) * 9 + cnt
  decreasing_by
    all_goals first
      | (obtain ⟨_, hp⟩ := hrc; omega)
      | (obtain ⟨hne, hle, _⟩ := hlit; omega)
      | omega

/-- **The USize-scalar tree-free loop projects to the boxed one** (mirror of
    `goFusedPU_eq`): the `pos`/`cnt` round-trips are decode-independent, so the
    same `goFusedPU.induct`-style argument applies with `decodeSymCanon`. -/
theorem goTreeFreeU_eq (litTable distTable : HuffTree.DecodeTable) (data : ByteArray)
    (litLD distLD : HuffTree.LongDecode) (maxBits : Nat) (maxOut : Nat)
    (hsz : data.size < USize.size) :
    ∀ (pos : USize) (bitBuf : UInt64) (cnt : USize) (output : ByteArray),
    pos.toNat ≤ data.size →
    Except.map (fun x => (x.1, x.2.1.toNat, x.2.2.1, x.2.2.2.toNat))
        (goTreeFreeU litTable distTable litLD distLD maxBits data maxOut pos bitBuf cnt hsz output)
      = goTreeFree litTable distTable litLD distLD maxBits data maxOut pos.toNat bitBuf cnt.toNat output := by
  intro pos bitBuf cnt output
  induction pos, bitBuf, cnt, output using goTreeFreeU.induct
    (litTable := litTable) (litLD := litLD)
    (maxBits := maxBits) (data := data) (maxOut := maxOut) (hsz := hsz) with
  | case1 pos bitBuf cnt output hrc ih =>
      intro hpos
      have hgN := (refillGuard_usize data pos cnt hsz).mp hrc
      have hpn : pos.toNat < data.size := hgN.2
      have hbig : (64 : Nat) < 2 ^ System.Platform.numBits :=
        USize.size_eq_two_pow ▸ Nat.lt_of_lt_of_le (by decide) USize.le_size
      have h8 : (8 : USize).toNat = 8 :=
        USize.toNat_ofNat_of_lt (Nat.lt_of_lt_of_le (by decide) USize.le_size)
      have e1 : (pos + 1).toNat = pos.toNat + 1 := by
        rw [USize.toNat_add, USize.toNat_one]; apply Nat.mod_eq_of_lt
        exact USize.size_eq_two_pow ▸ (show pos.toNat + 1 < USize.size by omega)
      have e2 : (cnt + 8).toNat = cnt.toNat + 8 := by
        rw [USize.toNat_add, h8]; apply Nat.mod_eq_of_lt; omega
      rw [goTreeFreeU, dif_pos hrc, goTreeFree, dif_pos hgN,
          ih (by rw [e1]; omega), e1, e2,
          uget_eq_getElem! data pos hpn, usize_toUInt64_toNat]
  | case2 pos bitBuf cnt output hrc hlit hmax =>
      intro hpos
      rw [goTreeFreeU, dif_neg hrc, dif_pos hlit, if_pos hmax,
          goTreeFree, dif_neg (fun h => hrc ((refillGuard_usize data pos cnt hsz).mpr h)),
          dif_pos ((litGuard_usize litTable bitBuf cnt).mp hlit), if_pos hmax]
      rfl
  | case3 pos bitBuf cnt output hrc hlit hmax ih =>
      intro hpos
      obtain ⟨hl0, hl1, hl2⟩ := hlit
      have hlen : ((litTable.lenAt (bitBuf &&& 0x1FF).toNat).toNat).toUSize.toNat
          = (litTable.lenAt (bitBuf &&& 0x1FF).toNat).toNat :=
        toUSize_toNat_of_lt (UInt8.toNat_lt_usizeSize _)
      have hsub : (cnt - ((litTable.lenAt (bitBuf &&& 0x1FF).toNat).toNat).toUSize).toNat
          = cnt.toNat - (litTable.lenAt (bitBuf &&& 0x1FF).toNat).toNat := by
        rw [USize.toNat_sub_of_le _ _ hl1, hlen]
      rw [goTreeFreeU, dif_neg hrc, dif_pos ⟨hl0, hl1, hl2⟩, if_neg hmax,
          goTreeFree, dif_neg (fun h => hrc ((refillGuard_usize data pos cnt hsz).mpr h)),
          dif_pos ((litGuard_usize litTable bitBuf cnt).mp ⟨hl0, hl1, hl2⟩), if_neg hmax,
          ih hpos, hsub]
  | case4 pos bitBuf cnt output hrc hlit e hde =>
      intro hpos
      rw [goTreeFreeU, dif_neg hrc, dif_neg hlit,
          goTreeFree, dif_neg (fun h => hrc ((refillGuard_usize data pos cnt hsz).mpr h)),
          dif_neg (fun h => hlit ((litGuard_usize litTable bitBuf cnt).mpr h))]
      simp only [hde, Except.map]
  | case5 pos bitBuf cnt output hrc hlit sym bb c used hde hsym hmax =>
      intro hpos
      rw [goTreeFreeU, dif_neg hrc, dif_neg hlit,
          goTreeFree, dif_neg (fun h => hrc ((refillGuard_usize data pos cnt hsz).mpr h)),
          dif_neg (fun h => hlit ((litGuard_usize litTable bitBuf cnt).mpr h))]
      simp only [hde, if_pos hsym, if_pos hmax]
      rfl
  | case6 pos bitBuf cnt output hrc hlit cnt0 sym bb c used hde hsym hmax hnp =>
      intro hpos
      have hnp' : cnt.toNat ≤ c := hnp
      rw [goTreeFreeU, dif_neg hrc, dif_neg hlit,
          goTreeFree, dif_neg (fun h => hrc ((refillGuard_usize data pos cnt hsz).mpr h)),
          dif_neg (fun h => hlit ((litGuard_usize litTable bitBuf cnt).mpr h))]
      simp only [hde, if_pos hsym, if_neg hmax, dif_pos hnp']
      rfl
  | case7 pos bitBuf cnt output hrc hlit cnt0 sym bb c used hde hsym hmax hnp ih =>
      intro hpos
      have hnp' : ¬ cnt.toNat ≤ c := hnp
      have hcle : c ≤ cnt.toNat := HuffTree.decodeSymCanon_cnt_le litLD litTable maxBits bitBuf cnt.toNat hde
      have hcrt : c.toUSize.toNat = c :=
        toUSize_toNat_of_lt (Nat.lt_of_le_of_lt hcle cnt.toNat_lt_two_pow_numBits)
      rw [goTreeFreeU, dif_neg hrc, dif_neg hlit,
          goTreeFree, dif_neg (fun h => hrc ((refillGuard_usize data pos cnt hsz).mpr h)),
          dif_neg (fun h => hlit ((litGuard_usize litTable bitBuf cnt).mpr h))]
      simp only [hde, if_pos hsym, if_neg hmax, dif_neg hnp']
      rw [ih hpos, hcrt]
  | case8 pos bitBuf cnt output hrc hlit sym bb c used hde hsym heob =>
      intro hpos
      have hcle : c ≤ cnt.toNat := HuffTree.decodeSymCanon_cnt_le litLD litTable maxBits bitBuf cnt.toNat hde
      have hcrt : c.toUSize.toNat = c :=
        toUSize_toNat_of_lt (Nat.lt_of_le_of_lt hcle cnt.toNat_lt_two_pow_numBits)
      rw [goTreeFreeU, dif_neg hrc, dif_neg hlit,
          goTreeFree, dif_neg (fun h => hrc ((refillGuard_usize data pos cnt hsz).mpr h)),
          dif_neg (fun h => hlit ((litGuard_usize litTable bitBuf cnt).mpr h))]
      simp only [hde, if_neg hsym, if_pos heob, Except.map, hcrt]
  | case9 pos bitBuf cnt output hrc hlit sym bb c used hde hsym hneob idx hidx =>
      intro hpos
      have hidxc : sym.toNat - 257 ≥ Inflate.lengthBase.size := hidx
      rw [goTreeFreeU, dif_neg hrc, dif_neg hlit,
          goTreeFree, dif_neg (fun h => hrc ((refillGuard_usize data pos cnt hsz).mpr h)),
          dif_neg (fun h => hlit ((litGuard_usize litTable bitBuf cnt).mpr h))]
      simp only [hde, if_neg hsym, if_neg hneob, dif_pos hidxc]
      rfl
  | case10 pos bitBuf cnt output hrc hlit cnt0 sym bb c used hde hsym hneob idx hh base ih =>
      intro hpos
      have hhc : ¬ sym.toNat - 257 ≥ Inflate.lengthBase.size := hh
      rw [goTreeFreeU, dif_neg hrc, dif_neg hlit,
          goTreeFree, dif_neg (fun h => hrc ((refillGuard_usize data pos cnt hsz).mpr h)),
          dif_neg (fun h => hlit ((litGuard_usize litTable bitBuf cnt).mpr h))]
      simp only [hde, if_neg hsym, if_neg hneob, dif_neg hhc]
      cases hex : takeBits bb c
          (Inflate.lengthExtra[sym.toNat - 257]'(by
            simp only [Inflate.lengthExtra_size]
            simp only [Inflate.lengthBase_size, ge_iff_le, Nat.not_le] at hhc; omega)).toNat with
      | error e => rfl
      | ok pe =>
          obtain ⟨eb, bb2, c2⟩ := pe
          simp only [bind, Except.bind]
          cases hdd : decodeSymCanon distLD distTable maxBits bb2 c2 with
          | error e => rfl
          | ok pd =>
              obtain ⟨distSym, bb3, c3, dused⟩ := pd
              simp only []
              split
              · rfl
              · rename_i hdi
                cases hex2 : takeBits bb3 c3
                    (Inflate.distExtra[distSym.toNat]'(by
                      simp only [Inflate.distExtra_size]
                      simp only [Inflate.distBase_size, ge_iff_le, Nat.not_le] at hdi; omega)).toNat with
                | error e => rfl
                | ok pd2 =>
                    obtain ⟨deb, bb4, c4⟩ := pd2
                    simp only [bind, Except.bind]
                    have hc4le : c4 ≤ cnt.toNat := by
                      have h1 := takeBits_le bb c _ hex
                      have h2 := HuffTree.decodeSymCanon_cnt_le distLD distTable maxBits bb2 c2 hdd
                      have h3 := takeBits_le bb3 c3 _ hex2
                      have h0 := HuffTree.decodeSymCanon_cnt_le litLD litTable maxBits bitBuf cnt.toNat hde
                      omega
                    have hc4rt : c4.toUSize.toNat = c4 :=
                      toUSize_toNat_of_lt (Nat.lt_of_le_of_lt hc4le cnt.toNat_lt_two_pow_numBits)
                    repeat' (first | rfl | split)
                    all_goals exact (ih eb distSym hdi deb bb4 c4 (by assumption) (by assumption)
                      (by assumption) hpos).trans (by rw [hc4rt])

/-- **Tree-free wide-buffer block decode = verified wide-buffer block decode** (on
    success). With the proof-only trees `fromLengthsTree`, `decodeHuffmanFastBufTreeFree`
    accepts exactly the inputs `decodeHuffmanFastBuf` does, with the same output:
    the tables coincide (`buildTableCanonicalFast_eq_buildTable`), the addressability
    dispatch collapses to the boxed loop on both sides (`goTreeFreeU_eq`,
    `goFusedPDispatch_eq`), and the loops agree (`goTreeFree_ok_iff_goFusedP`). -/
theorem decodeHuffmanFastBufTreeFree_ok_iff (br : BitReader) (output : ByteArray)
    (litLengths distLengths : Array UInt8)
    (hlv : Huffman.Spec.ValidLengths (litLengths.toList.map UInt8.toNat) 15)
    (hlb : litLengths.size ≤ UInt16.size)
    (hdv : Huffman.Spec.ValidLengths (distLengths.toList.map UInt8.toNat) 15)
    (hdb : distLengths.size ≤ UInt16.size)
    (maxOut : Nat) (hwf : br.bitOff < 8) (hbp : br.bitPos ≤ br.data.size * 8)
    (r : ByteArray × BitReader) :
    decodeHuffmanFastBufTreeFree br output litLengths distLengths maxOut = .ok r ↔
      decodeHuffmanFastBuf br output (fromLengthsTree litLengths 15)
        (fromLengthsTree distLengths 15) maxOut = .ok r := by
  have htlit : buildTableCanonicalFast litLengths 15 = (fromLengthsTree litLengths 15).buildTable :=
    buildTableCanonicalFast_eq_buildTable litLengths 15 (by omega) hlv hlb
  have htdist : buildTableCanonicalFast distLengths 15 = (fromLengthsTree distLengths 15).buildTable :=
    buildTableCanonicalFast_eq_buildTable distLengths 15 (by omega) hdv hdb
  -- buffer invariant after the entry refill: gives the dispatch bounds
  have hbpe : br.bitPos = br.pos * 8 + br.bitOff := rfl
  have hposle : br.pos ≤ br.data.size := by omega
  have hbc0 : BufCorr br.data (br.pos * 8) br.pos 0 0 :=
    ⟨by omega, hposle, by omega, by simp, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  rcases hrf : refill br.data br.pos 0 0 with ⟨pos0, bitBuf0, cnt0⟩
  obtain ⟨hbc1, hr1⟩ := refill_corr hbc0 hrf
  have hboff : br.bitOff ≤ cnt0 := by
    rcases hr1 with h56 | hpe
    · omega
    · have hs := hbc1.span; rw [hpe] at hs; omega
  have hbc2 : BufCorr br.data br.bitPos pos0 (bitBuf0 >>> br.bitOff.toUInt64) (cnt0 - br.bitOff) :=
    consume_corr hbc1 hboff (by omega)
  unfold decodeHuffmanFastBufTreeFree decodeHuffmanFastBuf
  rw [hrf]
  dsimp only []
  rw [htlit, htdist,
      goFusedPDispatch_eq (fromLengthsTree litLengths 15).buildTable
        (fromLengthsTree distLengths 15).buildTable br.data (fromLengthsTree litLengths 15)
        (fromLengthsTree distLengths 15) maxOut pos0 (bitBuf0 >>> br.bitOff.toUInt64)
        (cnt0 - br.bitOff) output hbc2.posLe hbc2.cntLe]
  -- collapse the tree-free addressability dispatch to the boxed `goTreeFree`,
  -- then thread the loop correspondence through the shared reconstruction
  split
  · rename_i hsz
    have hsz' : br.data.size < USize.size := by rw [← hsz]; exact USize.toNat_lt_two_pow_numBits _
    have hcsz : (cnt0 - br.bitOff) < USize.size :=
      Nat.lt_of_le_of_lt hbc2.cntLe (Nat.lt_of_lt_of_le (by decide) USize.le_size)
    rw [goTreeFreeU_eq (fromLengthsTree litLengths 15).buildTable
          (fromLengthsTree distLengths 15).buildTable br.data (buildLongDecode litLengths 15)
          (buildLongDecode distLengths 15) 15 maxOut hsz' pos0.toUSize
          (bitBuf0 >>> br.bitOff.toUInt64) (cnt0 - br.bitOff).toUSize output
          (by rw [toUSize_toNat_of_lt (Nat.lt_of_le_of_lt hbc2.posLe hsz')]; exact hbc2.posLe),
        toUSize_toNat_of_lt (Nat.lt_of_le_of_lt hbc2.posLe hsz'), toUSize_toNat_of_lt hcsz]
    exact bind_ok_iff (fun x => goTreeFree_ok_iff_goFusedP (fromLengthsTree litLengths 15).buildTable
      (fromLengthsTree distLengths 15).buildTable litLengths distLengths hlv hlb hdv hdb br.data maxOut
      pos0 (bitBuf0 >>> br.bitOff.toUInt64) (cnt0 - br.bitOff) output x) _ r
  · exact bind_ok_iff (fun x => goTreeFree_ok_iff_goFusedP (fromLengthsTree litLengths 15).buildTable
      (fromLengthsTree distLengths 15).buildTable litLengths distLengths hlv hlb hdv hdb br.data maxOut
      pos0 (bitBuf0 >>> br.bitOff.toUInt64) (cnt0 - br.bitOff) output x) _ r

end Zip.Native.InflateBuf

namespace Zip.Native.Inflate
open ZipCommon (BitReader)

/-- Peel one monadic bind from a successful `Except` computation. -/
private theorem bindOk {α β : Type} {e : Except String α} {f : α → Except String β} {r : β}
    (he : (e >>= f) = .ok r) : ∃ a, e = .ok a ∧ f a = .ok r := by
  cases e with
  | error e => simp [bind, Except.bind] at he
  | ok a => exact ⟨a, rfl, by simpa only [bind, Except.bind] using he⟩

/-- A single `readBit` yields a value `< 2` (it is `(…) &&& 1`). -/
theorem readBit_lt {br br' : BitReader} {bit : UInt32} (h : br.readBit = .ok (bit, br')) :
    bit.toNat < 2 := by
  unfold BitReader.readBit at h
  split at h
  · exact absurd h (by simp)
  · split at h <;>
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      rw [UInt32.toNat_and, show (1 : UInt32).toNat = 1 from rfl, Nat.and_one_is_mod]
      omega

/-- `readBits.go` accumulates `n` bits into positions `[shift, shift+n)`, so the
    result stays below `2^(shift+n)` (for `shift+n ≤ 32`). -/
theorem readBits_go_lt : ∀ (n : Nat) (br : BitReader) (acc : UInt32) (shift : Nat)
    (v : UInt32) (br' : BitReader),
    BitReader.readBits.go br acc shift n = .ok (v, br') →
    acc.toNat < 2 ^ shift → shift + n ≤ 32 → v.toNat < 2 ^ (shift + n) := by
  intro n
  induction n with
  | zero =>
    intro br acc shift v br' h hacc _
    simp only [BitReader.readBits.go, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h; simpa using hacc
  | succ k ih =>
    intro br acc shift v br' h hacc hle
    rw [BitReader.readBits.go] at h
    cases hrb : br.readBit with
    | error e => rw [hrb] at h; simp only [bind, Except.bind] at h; exact absurd h (by simp)
    | ok p =>
      obtain ⟨bit, br1⟩ := p
      rw [hrb] at h; simp only [bind, Except.bind] at h
      have hbit : bit.toNat < 2 := readBit_lt hrb
      have hsh : shift < 32 := by omega
      have hshift : shift.toUInt32.toNat % 32 = shift := by
        have h2 : shift.toUInt32.toNat = shift := by
          simp only [Nat.toUInt32, UInt32.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
        rw [h2, Nat.mod_eq_of_lt hsh]
      have hnw : bit.toNat * 2 ^ shift < 2 ^ 32 := by
        calc bit.toNat * 2 ^ shift < 2 * 2 ^ shift :=
              (Nat.mul_lt_mul_right (Nat.two_pow_pos shift)).mpr hbit
          _ = 2 ^ (shift + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
          _ ≤ 2 ^ 32 := Nat.pow_le_pow_right (by omega) (by omega)
      have hsl : (bit <<< shift.toUInt32).toNat = bit.toNat * 2 ^ shift := by
        rw [UInt32.toNat_shiftLeft, hshift, Nat.shiftLeft_eq, Nat.mod_eq_of_lt hnw]
      have hacc' : (acc ||| (bit <<< shift.toUInt32)).toNat < 2 ^ (shift + 1) := by
        rw [UInt32.toNat_or]
        refine Nat.or_lt_two_pow
          (Nat.lt_of_lt_of_le hacc (Nat.pow_le_pow_right (by omega) (by omega))) ?_
        rw [hsl]
        calc bit.toNat * 2 ^ shift < 2 * 2 ^ shift :=
              (Nat.mul_lt_mul_right (Nat.two_pow_pos shift)).mpr hbit
          _ = 2 ^ (shift + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
      have hv := ih br1 (acc ||| (bit <<< shift.toUInt32)) (shift + 1) v br' h hacc' (by omega)
      rwa [show shift + 1 + k = shift + (k + 1) from by omega] at hv

/-- `readBits n` returns a value `< 2^n` (for `n ≤ 32`). -/
theorem readBits_lt {br br' : BitReader} {n : Nat} {v : UInt32} (hn : n ≤ 32)
    (h : br.readBits n = .ok (v, br')) : v.toNat < 2 ^ n := by
  have := readBits_go_lt n br 0 0 v br' h (by simp) (by omega); simpa using this

/-- **`decodeDynamicTrees` extraction.** A successful `decodeDynamicTrees` shares
    its whole prefix with `decodeDynamicLengthsOnly`: it yields the same code-length
    arrays and reader, the two trees are `fromLengths` of those arrays, and the
    arrays fit `UInt16` (`hlit`/`hdist` are 5-bit, so `≤ 288`/`32`). -/
theorem decodeDynamicTrees_extract {br : BitReader} {litTree distTree : HuffTree} {br' : BitReader}
    (h : decodeDynamicTrees br = .ok (litTree, distTree, br')) :
    ∃ litLens distLens, decodeDynamicLengthsOnly br = .ok (litLens, distLens, br') ∧
      HuffTree.fromLengths litLens 15 = .ok litTree ∧ HuffTree.fromLengths distLens 15 = .ok distTree ∧
      litLens.size ≤ UInt16.size ∧ distLens.size ≤ UInt16.size := by
  unfold decodeDynamicTrees at h
  obtain ⟨a1, he1, h⟩ := bindOk h; obtain ⟨hlit, br1⟩ := a1
  obtain ⟨a2, he2, h⟩ := bindOk h; obtain ⟨hdist, br2⟩ := a2
  obtain ⟨a3, he3, h⟩ := bindOk h; obtain ⟨hclen, br3⟩ := a3
  obtain ⟨a4, he4, h⟩ := bindOk h; obtain ⟨clLengths, br4⟩ := a4
  obtain ⟨a5, he5, h⟩ := bindOk h
  obtain ⟨a6, he6, h⟩ := bindOk h; obtain ⟨codeLengths, br6⟩ := a6
  obtain ⟨lt', hlitT, h⟩ := bindOk h
  obtain ⟨dt', hdistT, h⟩ := bindOk h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  have hlitb : hlit.toNat < 32 := readBits_lt (n := 5) (by omega) he1
  have hdistb : hdist.toNat < 32 := readBits_lt (n := 5) (by omega) he2
  refine ⟨_, _, ?_, hlitT, hdistT, ?_, ?_⟩
  · unfold decodeDynamicLengthsOnly
    simp [he1, he2, he3, he4, he5, he6, bind, Except.bind, pure, Except.pure]
  · rw [Array.size_extract]
    exact Nat.le_trans (Nat.le_trans (Nat.sub_le _ _) (Nat.min_le_left _ _))
      (Nat.le_trans (by omega : hlit.toNat + 257 ≤ 288) (by decide : 288 ≤ UInt16.size))
  · rw [Array.size_extract]
    exact Nat.le_trans (Nat.le_trans (Nat.sub_le _ _) (Nat.min_le_left _ _))
      (Nat.le_trans (by omega : hlit.toNat + 257 + (hdist.toNat + 1) ≤ 320)
        (by decide : 320 ≤ UInt16.size))

set_option maxRecDepth 4096 in
open InflateBuf in
/-- **Tree-free block loop forward.** If the verified `inflateLoop` (with the
    proof-only fixed trees) succeeds, the tree-free `inflateLoopTreeFree` succeeds
    with the same result. Stored blocks are identical; fixed/dynamic Huffman blocks
    go through `decodeHuffmanFastBufTreeFree_ok_iff` (dynamic lengths valid via
    `fromLengths_valid`, sizes bounded via `decodeDynamicTrees_extract`). The reader
    invariant is re-established each iteration. -/
theorem inflateLoopTreeFree_of_inflateLoop (data : ByteArray)
    (hflv : Huffman.Spec.ValidLengths (fixedLitLengths.toList.map UInt8.toNat) 15)
    (hflb : fixedLitLengths.size ≤ UInt16.size)
    (hfdv : Huffman.Spec.ValidLengths (fixedDistLengths.toList.map UInt8.toNat) 15)
    (hfdb : fixedDistLengths.size ≤ UInt16.size) (maxOut : Nat) :
    ∀ (br : BitReader) (output : ByteArray),
      (br.bitOff = 0 ∨ br.pos < br.data.size) → br.pos ≤ br.data.size → br.data.size = data.size →
      ∀ r, inflateLoop br output (HuffTree.fromLengthsTree fixedLitLengths 15)
            (HuffTree.fromLengthsTree fixedDistLengths 15) maxOut data.size = .ok r →
        inflateLoopTreeFree br output maxOut data.size = .ok r := by
  intro br output
  induction br, output using inflateLoop.induct (dataSize := data.size) with
  | _ br output ih =>
    intro hpos hple hds r h
    rw [inflateLoop] at h
    obtain ⟨p1, hrb1, h⟩ := bindOk h; obtain ⟨bfinal, br₁⟩ := p1; simp only [] at h
    obtain ⟨p2, hrb2, h⟩ := bindOk h; obtain ⟨btype, br₂⟩ := p2; simp only [] at h
    have hbo₂ : br₂.bitOff < 8 := readBits_bitOff_lt_pos (by omega) hrb2
    obtain ⟨_, hp₁, hl₁⟩ := ZipCommon.readBits_inv br br₁ 1 bfinal hrb1 hpos hple
    obtain ⟨hd₂, hp₂, hl₂⟩ := ZipCommon.readBits_inv br₁ br₂ 2 btype hrb2 hp₁ hl₁
    have hdata₂ : br₂.data.size = data.size := by
      rw [hd₂, ZipCommon.readBits_data_eq br br₁ 1 bfinal hrb1]; exact hds
    have hwf₂ : br₂.bitPos ≤ br₂.data.size * 8 := by
      simp only [ZipCommon.BitReader.bitPos]; rcases hp₂ with h' | h' <;> omega
    have hldep := InflateBuf.fromLengths_depthLE (HuffTree.fromLengths_ok_of_valid fixedLitLengths 15 hflv)
    have hddep := InflateBuf.fromLengths_depthLE (HuffTree.fromLengths_ok_of_valid fixedDistLengths 15 hfdv)
    -- the tail (block result already fixed) is identical except the recursive call
    have tailfwd : ∀ (o' : ByteArray) (br'' : BitReader),
        (br''.bitOff = 0 ∨ br''.pos < br''.data.size) → br''.pos ≤ br''.data.size →
        br''.data.size = data.size →
        (if bfinal == 1 then pure (o', br''.alignToByte.pos)
         else if _h : br''.bitPos ≤ br.bitPos then throw "Inflate: no progress in inflate loop"
              else if _h : data.size * 8 < br''.bitPos then throw "Inflate: bit position out of range"
              else inflateLoop br'' o' (HuffTree.fromLengthsTree fixedLitLengths 15)
                    (HuffTree.fromLengthsTree fixedDistLengths 15) maxOut data.size) = .ok r →
        (if bfinal == 1 then pure (o', br''.alignToByte.pos)
         else if _h : br''.bitPos ≤ br.bitPos then throw "Inflate: no progress in inflate loop"
              else if _h : data.size * 8 < br''.bitPos then throw "Inflate: bit position out of range"
              else inflateLoopTreeFree br'' o' maxOut data.size) = .ok r := by
      intro o' br'' hp'' hl'' hd'' ht
      by_cases hbf : (bfinal == 1) = true
      · rw [if_pos hbf] at ht ⊢; exact ht
      · rw [if_neg hbf] at ht ⊢
        by_cases hg1 : br''.bitPos ≤ br.bitPos
        · rw [dif_pos hg1] at ht; exact absurd ht (by simp)
        · rw [dif_neg hg1] at ht ⊢
          by_cases hg2 : data.size * 8 < br''.bitPos
          · rw [dif_pos hg2] at ht; exact absurd ht (by simp)
          · rw [dif_neg hg2] at ht ⊢
            exact ih o' br'' hg1 hg2 hp'' hl'' hd'' r ht
    rw [inflateLoopTreeFree]
    simp only [hrb1, hrb2, bind, Except.bind]
    have hbtv : btype = 0 ∨ btype = 1 ∨ btype = 2 ∨ btype = 3 := by
      have hb4 : btype.toNat < 4 := readBits_lt (n := 2) (by omega) hrb2
      rcases (show btype.toNat = 0 ∨ btype.toNat = 1 ∨ btype.toNat = 2 ∨ btype.toNat = 3 from by omega)
        with h' | h' | h' | h'
      · exact Or.inl (UInt32.toNat_inj.mp (by rw [h']; rfl))
      · exact Or.inr (Or.inl (UInt32.toNat_inj.mp (by rw [h']; rfl)))
      · exact Or.inr (Or.inr (Or.inl (UInt32.toNat_inj.mp (by rw [h']; rfl))))
      · exact Or.inr (Or.inr (Or.inr (UInt32.toNat_inj.mp (by rw [h']; rfl))))
    rcases hbtv with rfl | rfl | rfl | rfl
    · -- stored block (identical)
      obtain ⟨pb, hblock, htail⟩ := bindOk h; obtain ⟨output', br'⟩ := pb
      obtain ⟨hd', hp', hl'⟩ := Zip.Native.decodeStored_inv br₂ br' output output' maxOut hblock
      rw [hblock]; dsimp only [bind, Except.bind]
      exact tailfwd output' br' hp' hl' (by rw [hd']; exact hdata₂) htail
    · -- fixed Huffman block
      obtain ⟨pb, hblock, htail⟩ := bindOk h; obtain ⟨output', br'⟩ := pb
      have htf := (decodeHuffmanFastBufTreeFree_ok_iff br₂ output fixedLitLengths fixedDistLengths
        hflv hflb hfdv hfdb maxOut hbo₂ hwf₂ (output', br')).mpr hblock
      have hhf' : Inflate.decodeHuffman br₂ output (HuffTree.fromLengthsTree fixedLitLengths 15)
          (HuffTree.fromLengthsTree fixedDistLengths 15) maxOut = .ok (output', br') := by
        rw [← decodeHuffmanFast_eq br₂ output _ _ maxOut hldep hddep hbo₂ hwf₂]; exact hblock
      obtain ⟨hd', hp', hl'⟩ := Zip.Native.decodeHuffman_inv _ _ br₂ br' output output' maxOut hhf' hp₂ hl₂
      rw [htf]; dsimp only [bind, Except.bind]
      exact tailfwd output' br' hp' hl' (by rw [hd']; exact hdata₂) htail
    · -- dynamic Huffman block
      obtain ⟨pdt, hdt, h⟩ := bindOk h; obtain ⟨lt, dt, br₃⟩ := pdt; simp only [] at h
      obtain ⟨pb, hblock, htail⟩ := bindOk h; obtain ⟨output', br'⟩ := pb
      obtain ⟨ll, dl, hlonly, hflt, hfdt, hllb, hdlb⟩ := decodeDynamicTrees_extract hdt
      have hltv := Deflate.Correctness.fromLengths_valid ll 15 lt hflt
      have hdlv := Deflate.Correctness.fromLengths_valid dl 15 dt hfdt
      have hlteq : lt = HuffTree.fromLengthsTree ll 15 :=
        Except.ok.inj (hflt.symm.trans (HuffTree.fromLengths_ok_of_valid ll 15 hltv))
      have hdteq : dt = HuffTree.fromLengthsTree dl 15 :=
        Except.ok.inj (hfdt.symm.trans (HuffTree.fromLengths_ok_of_valid dl 15 hdlv))
      obtain ⟨hd3, hp3, hl3⟩ := Zip.Native.decodeDynamicTrees_inv br₂ br₃ lt dt hdt hp₂ hl₂
      have hbo3 := InflateBuf.decodeDynamicTrees_bitOff_pres hbo₂ hdt
      have hwf3 : br₃.bitPos ≤ br₃.data.size * 8 := by
        simp only [ZipCommon.BitReader.bitPos]; rcases hp3 with h' | h' <;> omega
      have hbuf : decodeHuffmanFastBuf br₃ output (HuffTree.fromLengthsTree ll 15)
          (HuffTree.fromLengthsTree dl 15) maxOut = .ok (output', br') := by
        rw [← hlteq, ← hdteq]; exact hblock
      have htf := (decodeHuffmanFastBufTreeFree_ok_iff br₃ output ll dl hltv hllb hdlv hdlb
        maxOut hbo3 hwf3 (output', br')).mpr hbuf
      have hhf' : Inflate.decodeHuffman br₃ output lt dt maxOut = .ok (output', br') := by
        rw [← decodeHuffmanFast_eq br₃ output lt dt maxOut
          (InflateBuf.fromLengths_depthLE hflt) (InflateBuf.fromLengths_depthLE hfdt) hbo3 hwf3]
        exact hblock
      obtain ⟨hd', hp', hl'⟩ := Zip.Native.decodeHuffman_inv lt dt br₃ br' output output' maxOut hhf' hp3 hl3
      rw [hlonly]; dsimp only [bind, Except.bind]
      rw [htf]; dsimp only [bind, Except.bind]
      exact tailfwd output' br' hp' hl' (by rw [hd', hd3]; exact hdata₂) htail
    · -- reserved block type 3
      simp only [bind, Except.bind] at h
      exact absurd h (by simp)

end Zip.Native.Inflate
