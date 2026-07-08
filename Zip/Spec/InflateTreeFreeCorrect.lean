import Zip.Spec.InflateCanonical
import Zip.Spec.InflateBufCorrect
import Zip.Spec.DynamicTreesCorrect
import Zip.Native.InflateTreeFree

/-!
# Tree-free canonical decode: correctness

Proves that the production tree-free decoder (`Inflate.inflate` / `inflateRaw`,
defined in `Zip.Native.InflateTreeFree`) has **exactly the same accept-set** as the
verified reference (`Inflate.inflateReference` / `inflateRawReference`), producing
identical output, with the tree (`fromLengthsTree lengths`) as a **proof-only**
object — never built at runtime. The top-level statements are the two-sided
`inflate_ok_iff_reference` (`inflate data = .ok out ↔ inflateReference data = .ok
out`) and `inflateRaw_ok_iff_reference`, built from the forward direction
(`inflate_of_inflateReference`, present since #2681) and the backward direction
(`inflateReference_of_inflate`) the closed code-length validation gap enables:
`decodeDynamicLengthsOnly` now runs the same `validateLengths` (`maxBits`/Kraft)
check `decodeDynamicTrees` does, so on malformed dynamic length sets both paths
reject. The chain, bottom-up:

0. `validateLengths` ↔ `fromLengths` (`fromLengths_eq_validate`,
   `validateLengths_ok_iff_fromLengths`) — the factored code-length check.

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

/-! ## `validateLengths` ↔ `fromLengths` correspondence

`validateLengths` is exactly the `maxBits`/Kraft check `fromLengths` runs before
building the tree, factored out for the tree-free path. These lemmas certify that
running `validateLengths` rejects (and accepts) precisely the length sets
`fromLengths` does, with identical error messages — the foundation of closing the
tree-free code-length validation gap.

`fromLengths` computes its Kraft sum over a per-block `lengths.toList`/`filter`
`List`; `validateLengths` computes the same sum from the per-length `count`
histogram (`countLengthsFast`, the array the canonical table build already needs)
via the allocation-free `kraftSumFast`. `validate_kraft_eq` certifies the two Kraft
computations agree on every length set with no over-bound length, so the check
cascades stay identical. -/

/-- The fast histogram equals the spec `countLengths` on the mapped lengths.
    (Local restatement of the `hcount` step inside `buildTableCanonicalFast_eq`.) -/
theorem countLengthsFast_eq (lengths : Array UInt8) (maxBits : Nat) :
    countLengthsFast lengths maxBits
      = Huffman.Spec.countLengths (lengths.toList.map UInt8.toNat) maxBits := by
  rw [countLengthsFast,
      countLengthsFast_go_eq lengths maxBits lengths.size 0 _ (by omega), List.drop_zero]
  rfl

/-- Accumulator invariant for `kraftSumFast.go`: the loop threads the running Kraft
    sum, so it equals the accumulator plus the spec backward recurrence
    `Huffman.Spec.kraftSumFrom` from the current index. -/
theorem kraftSumFast_go_eq (count : Array Nat) (maxBits b acc : Nat) :
    kraftSumFast.go count maxBits b acc = acc + Huffman.Spec.kraftSumFrom count maxBits b := by
  rw [kraftSumFast.go]
  if h : b ≤ maxBits then
    rw [dif_pos h, kraftSumFast_go_eq count maxBits (b + 1) _,
        Huffman.Spec.kraftSumFrom_unfold count maxBits b h]
    simp only [Nat.shiftLeft_eq, Nat.one_mul]
    omega
  else
    rw [dif_neg h, Huffman.Spec.kraftSumFrom_gt count maxBits b (by omega), Nat.add_zero]
termination_by maxBits + 1 - b

/-- `kraftSumFast` equals the spec backward Kraft recurrence from index `0`. -/
theorem kraftSumFast_eq (count : Array Nat) (maxBits : Nat) :
    kraftSumFast count maxBits = Huffman.Spec.kraftSumFrom count maxBits 0 := by
  rw [kraftSumFast, kraftSumFast_go_eq, Nat.zero_add]

/-- The allocation-free Kraft sum `validateLengths` computes from the `count`
    histogram equals the per-element Kraft fold `fromLengths` computes over the
    non-zero lengths, whenever no length exceeds `maxBits` (the over-bound case is
    rejected first by the shared `Array.any` guard). -/
theorem validate_kraft_eq (lengths : Array UInt8) (maxBits : Nat)
    (h : ¬ (lengths.any (fun l => l.toNat > maxBits) = true)) :
    kraftSumFast (countLengthsFast lengths maxBits) maxBits
      = ((lengths.toList.map UInt8.toNat).filter (· != 0)).foldl
          (fun acc l => acc + 2 ^ (maxBits - l)) 0 := by
  rw [kraftSumFast_eq, countLengthsFast_eq]
  refine Huffman.Spec.kraftSumFrom_zero_eq_foldl (lengths.toList.map UInt8.toNat) maxBits ?_
  intro l hl
  simp only [List.mem_map] at hl
  obtain ⟨u, hu, rfl⟩ := hl
  rw [Array.mem_toList_iff, Array.mem_iff_getElem] at hu
  obtain ⟨i, hi, rfl⟩ := hu
  rw [Bool.not_eq_true, Array.any_eq_false] at h
  simpa only [gt_iff_lt, decide_eq_true_eq, Nat.not_lt] using h i hi

/-- `fromLengths` is `validateLengths` followed by the validation-free tree build:
    they share the identical `maxBits`/Kraft `if`-cascade, so `fromLengths` errors
    exactly when `validateLengths` errors, with the same message. -/
theorem fromLengths_eq_validate (lengths : Array UInt8) (maxBits : Nat) :
    fromLengths lengths maxBits
      = (validateLengths lengths maxBits).map (fun _ => fromLengthsTree lengths maxBits) := by
  unfold fromLengths validateLengths
  simp only [Nat.shiftLeft_eq, Nat.one_mul]
  by_cases h1 : lengths.any (fun l => l.toNat > maxBits) = true
  · rw [if_pos h1, if_pos h1]; rfl
  · rw [if_neg h1, if_neg h1, validate_kraft_eq lengths maxBits h1]
    by_cases h2 : ((lengths.toList.map UInt8.toNat).filter (· != 0)).foldl
        (fun acc l => acc + 2 ^ (maxBits - l)) 0 > 2 ^ maxBits
    · rw [if_pos h2, if_pos h2]; rfl
    · rw [if_neg h2, if_neg h2]; rfl

/-- `validateLengths` succeeds iff `fromLengths` succeeds (with the canonical tree). -/
theorem validateLengths_ok_iff_fromLengths (lengths : Array UInt8) (maxBits : Nat) :
    validateLengths lengths maxBits = .ok () ↔
      fromLengths lengths maxBits = .ok (fromLengthsTree lengths maxBits) := by
  rw [fromLengths_eq_validate]
  cases h : validateLengths lengths maxBits with
  | error e => simp [Except.map]
  | ok u => cases u; simp [Except.map]

/-- A successful `validateLengths` certifies `ValidLengths`. -/
theorem validateLengths_valid {lengths : Array UInt8} {maxBits : Nat}
    (h : validateLengths lengths maxBits = .ok ()) :
    Huffman.Spec.ValidLengths (lengths.toList.map UInt8.toNat) maxBits :=
  Deflate.Correctness.fromLengths_valid lengths maxBits _
    ((validateLengths_ok_iff_fromLengths lengths maxBits).mp h)

/-- `fromLengths` success yields `validateLengths` success. -/
theorem validateLengths_of_fromLengths {lengths : Array UInt8} {maxBits : Nat} {t : HuffTree}
    (h : fromLengths lengths maxBits = .ok t) : validateLengths lengths maxBits = .ok () := by
  rw [fromLengths_eq_validate] at h
  cases hv : validateLengths lengths maxBits with
  | error e => rw [hv] at h; simp [Except.map] at h
  | ok u => cases u; rfl

/-- A failing `validateLengths` makes `fromLengths` fail with the same message. -/
theorem fromLengths_error_of_validate {lengths : Array UInt8} {maxBits : Nat} {e : String}
    (h : validateLengths lengths maxBits = .error e) :
    fromLengths lengths maxBits = .error e := by
  rw [fromLengths_eq_validate, h]; rfl

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

/-! ## `subLookup` subtable characterization

The production long-code path resolves a >`fastBits` codeword by two masked loads
(`subLookup`) rather than the boxed per-bit `walkCanonical` scan. Correctness is a
generational refinement: `subLookup` is proven to return exactly what
`walkCanonical` returns, *in the context it is called* (the root table missed, so
any codeword present is longer than `fastBits`). The proof factors through the
same `codeFor` / `cwOf` characterization: the subtable fill places symbol `s` in
exactly the sub-slots whose bits spell `s`'s canonical codeword
(`subFill_complete` / `subFill_sound`, the `buildSubLoop` invariant), and
`walkCanonical`'s already-proven forward/backward specs supply the other half. -/

/-- The `fastBits`-bit prefix `subLookup` indexes `rootSub` with. -/
def subPrefix (buf : UInt64) : Nat := (buf &&& 0x7FF).toNat

/-- The sub-index (next `maxBits - fastBits` bits) `subLookup` indexes the block with. -/
def subIndex (maxBits : Nat) (buf : UInt64) : Nat :=
  ((buf >>> (fastBits : Nat).toUInt64) &&& (2 ^ (maxBits - fastBits) - 1 : Nat).toUInt64).toNat

/-- The single `subs` slot `subLookup` reads for `buf` (subtable block of
    `subPrefix buf` at sub-offset `subIndex maxBits buf`). -/
def subSlot (ld : LongDecode) (maxBits : Nat) (buf : UInt64) : UInt32 :=
  ld.subs[(ld.rootSub[subPrefix buf]!.toNat - 1) + subIndex maxBits buf]!

/-! ## Arithmetic bridges for the subtable indices

`subPrefix`/`subIndex` are the low `fastBits` and next `maxBits - fastBits` bits of
the buffer; below they are re-expressed as `Nat` `mod`/`div` so the fill algebra
matches the `bitReverse` slot progression `buildSubLoop` writes. -/

/-- `subPrefix` is the low-`fastBits` bits of the buffer as a `Nat`. -/
theorem subPrefix_eq_mod (buf : UInt64) :
    subPrefix buf = buf.toNat % 2 ^ fastBits := by
  rw [subPrefix, UInt64.toNat_and, show (0x7FF : UInt64).toNat = 2 ^ fastBits - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]

/-- `subPrefix buf < 2^fastBits`. -/
theorem subPrefix_lt (buf : UInt64) : subPrefix buf < 2 ^ fastBits := by
  rw [subPrefix_eq_mod]; exact Nat.mod_lt _ (Nat.two_pow_pos _)

/-- `subIndex` is the `maxBits - fastBits` bits above the `fastBits` window. -/
theorem subIndex_eq (maxBits : Nat) (hmb15 : maxBits ≤ 15) (buf : UInt64) :
    subIndex maxBits buf = (buf.toNat / 2 ^ fastBits) % 2 ^ (maxBits - fastBits) := by
  have htoNat : ∀ n : Nat, n.toUInt64.toNat = n % 2 ^ 64 := fun _ => rfl
  have hsh : ((fastBits : Nat).toUInt64).toNat % 64 = fastBits := by
    rw [htoNat]; rfl
  have hmask : ((2 ^ (maxBits - fastBits) - 1 : Nat).toUInt64).toNat
      = 2 ^ (maxBits - fastBits) - 1 := by
    rw [htoNat]
    apply Nat.mod_eq_of_lt
    have hle : maxBits - fastBits ≤ 4 := by simp only [fastBits]; omega
    calc 2 ^ (maxBits - fastBits) - 1 < 2 ^ (maxBits - fastBits) :=
          Nat.sub_lt (Nat.two_pow_pos _) (by decide)
      _ ≤ 2 ^ 4 := Nat.pow_le_pow_right (by decide) hle
      _ < 2 ^ 64 := by decide
  rw [subIndex, UInt64.toNat_and, hmask, UInt64.toNat_shiftRight, hsh,
      Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod]

/-- `subIndex maxBits buf < 2^(maxBits - fastBits)`. -/
theorem subIndex_lt (maxBits : Nat) (hmb15 : maxBits ≤ 15) (buf : UInt64) :
    subIndex maxBits buf < 2 ^ (maxBits - fastBits) := by
  rw [subIndex_eq maxBits hmb15]; exact Nat.mod_lt _ (Nat.two_pow_pos _)

/-! ## Block counting: the number of long codes bounds `nextBlock`

`buildSubLoop` allocates one subtable block per distinct `fastBits`-prefix of the
long codes; each such block is triggered by a distinct long symbol, so the number
of allocated blocks (`nextBlock`) never exceeds `countLongCodes`, the size divisor
of the flat `subs` array. `Lcount` counts long symbols processed so far. -/

/-- A finite `∑_{len ≤ j ≤ maxBits} f j`. -/
def rangeSum (f : Nat → Nat) (maxBits len : Nat) : Nat :=
  if len > maxBits then 0 else f len + rangeSum f maxBits (len + 1)
  termination_by maxBits + 1 - len

/-- One-step unfolding of `rangeSum` (targeted, to avoid `rw` rewriting the inner
    recursive occurrence). -/
theorem rangeSum_unfold (f : Nat → Nat) (maxBits lo : Nat) :
    rangeSum f maxBits lo = if lo > maxBits then 0 else f lo + rangeSum f maxBits (lo + 1) := by
  rw [rangeSum]

/-- Pointwise-equal summands give equal `rangeSum`. -/
theorem rangeSum_congr (f g : Nat → Nat) (maxBits lo : Nat)
    (h : ∀ j, lo ≤ j → j ≤ maxBits → f j = g j) :
    rangeSum f maxBits lo = rangeSum g maxBits lo := by
  rw [rangeSum_unfold f maxBits lo, rangeSum_unfold g maxBits lo]
  by_cases hlt : lo > maxBits
  · rw [if_pos hlt, if_pos hlt]
  · rw [if_neg hlt, if_neg hlt, h lo (Nat.le_refl _) (by omega),
        rangeSum_congr f g maxBits (lo + 1) (fun j hj hjm => h j (by omega) hjm)]
  termination_by maxBits + 1 - lo

/-- `rangeSum` of a sum is the sum of `rangeSum`s. -/
theorem rangeSum_add (f g : Nat → Nat) (maxBits lo : Nat) :
    rangeSum (fun j => f j + g j) maxBits lo
      = rangeSum f maxBits lo + rangeSum g maxBits lo := by
  rw [rangeSum_unfold (fun j => f j + g j) maxBits lo, rangeSum_unfold f maxBits lo,
      rangeSum_unfold g maxBits lo]
  by_cases hlt : lo > maxBits
  · rw [if_pos hlt, if_pos hlt, if_pos hlt]
  · rw [if_neg hlt, if_neg hlt, if_neg hlt, rangeSum_add f g maxBits (lo + 1)]
    omega
  termination_by maxBits + 1 - lo

/-- `∑_{lo ≤ j ≤ maxBits} [x = j] = [lo ≤ x ≤ maxBits]`. -/
theorem rangeSum_indicator (x maxBits lo : Nat) :
    rangeSum (fun j => if x = j then 1 else 0) maxBits lo
      = (if lo ≤ x ∧ x ≤ maxBits then 1 else 0) := by
  rw [rangeSum_unfold]
  by_cases hlt : lo > maxBits
  · rw [if_pos hlt, if_neg (by omega)]
  · rw [if_neg hlt, rangeSum_indicator x maxBits (lo + 1)]
    by_cases hx : x = lo
    · subst hx; rw [if_pos rfl, if_neg (by omega), if_pos (by omega)]
    · rw [if_neg hx]
      by_cases hmem : lo ≤ x ∧ x ≤ maxBits
      · rw [if_pos (by omega), if_pos (by omega)]
      · rw [if_neg (by omega), if_neg (by omega)]
  termination_by maxBits + 1 - lo

/-- `rangeSum` of the constant `0` is `0`. -/
theorem rangeSum_zero (maxBits lo : Nat) : rangeSum (fun _ => 0) maxBits lo = 0 := by
  rw [rangeSum_unfold]
  by_cases h : lo > maxBits
  · rw [if_pos h]
  · rw [if_neg h, rangeSum_zero maxBits (lo + 1), Nat.add_zero]
  termination_by maxBits + 1 - lo

/-- `countLongCodes.go` accumulates `acc + ∑_{len ≤ j ≤ maxBits} count[j]`. -/
theorem countLongCodes_go_eq (count : Array Nat) (maxBits len acc : Nat) :
    countLongCodes.go count maxBits len acc = acc + rangeSum (fun j => count[j]!) maxBits len := by
  rw [countLongCodes.go, rangeSum_unfold]
  by_cases hlt : len > maxBits
  · rw [if_pos hlt, if_pos hlt, Nat.add_zero]
  · rw [if_neg hlt, if_neg hlt, countLongCodes_go_eq count maxBits (len + 1) _]
    omega
  termination_by maxBits + 1 - len

/-- `countLongCodes` is `∑_{fastBits < j ≤ maxBits} count[j]`. -/
theorem countLongCodes_eq (count : Array Nat) (maxBits : Nat) :
    countLongCodes count maxBits = rangeSum (fun j => count[j]!) maxBits (fastBits + 1) := by
  rw [countLongCodes, countLongCodes_go_eq, Nat.zero_add]

/-- Number of long symbols (`fastBits < len ≤ maxBits`) among indices `< start`. -/
def Lcount (lengths : Array UInt8) (maxBits : Nat) : Nat → Nat
  | 0 => 0
  | start + 1 => Lcount lengths maxBits start
      + (if fastBits < lengths[start]!.toNat ∧ lengths[start]!.toNat ≤ maxBits then 1 else 0)

/-- `Lcount` is monotone in the processed prefix length. -/
theorem Lcount_mono (lengths : Array UInt8) (maxBits : Nat) {a b : Nat} (hab : a ≤ b) :
    Lcount lengths maxBits a ≤ Lcount lengths maxBits b := by
  induction b with
  | zero => have : a = 0 := Nat.le_zero.mp hab; subst this; exact Nat.le_refl _
  | succ k ih =>
    by_cases hk : a ≤ k
    · exact Nat.le_trans (ih hk) (by rw [Lcount]; omega)
    · have : a = k + 1 := by omega
      subst this; exact Nat.le_refl _

/-- `Lcount` over all symbols is the number of long codes: the per-length buckets
    (`numEarlier … size`, i.e. `count[len]`) summed over the long lengths. -/
theorem Lcount_eq_rangeSum (lengths : Array UInt8) (maxBits : Nat) (start : Nat) :
    Lcount lengths maxBits start
      = rangeSum (fun j => numEarlier (lengths.toList.map UInt8.toNat) j start) maxBits (fastBits + 1) := by
  induction start with
  | zero =>
    rw [Lcount]
    rw [rangeSum_congr _ (fun _ => 0) maxBits (fastBits + 1) (fun j _ _ => by simp [numEarlier])]
    exact (rangeSum_zero maxBits (fastBits + 1)).symm
  | succ n ih =>
    rw [Lcount, ih]
    by_cases hn : n < lengths.size
    · rw [show (fun j => numEarlier (lengths.toList.map UInt8.toNat) j (n + 1))
            = (fun j => numEarlier (lengths.toList.map UInt8.toNat) j n
                + (if lengths[n]!.toNat = j then 1 else 0)) from
          funext (fun j => numEarlier_succ_arr lengths j n hn)]
      rw [rangeSum_add, rangeSum_indicator]
      simp only [Nat.lt_iff_add_one_le]
    · -- n ≥ size: `lengths[n]!` is not a long length, and `numEarlier` is stable at `n+1`.
      have hnl : lengths.size ≤ n := by omega
      have hlen_eq : (lengths.toList.map UInt8.toNat).length = lengths.size := by
        rw [List.length_map, Array.length_toList]
      have hstable : rangeSum (fun j => numEarlier (lengths.toList.map UInt8.toNat) j (n + 1)) maxBits (fastBits + 1)
          = rangeSum (fun j => numEarlier (lengths.toList.map UInt8.toNat) j n) maxBits (fastBits + 1) := by
        apply rangeSum_congr
        intro j _ _
        unfold numEarlier
        rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
      have h0 : lengths[n]! = (0 : UInt8) := getElem!_neg lengths n (by omega)
      rw [h0]
      simp only [UInt8.toNat_ofNat, hstable]
      rw [if_neg (by simp only [fastBits]; omega), Nat.add_zero]

/-- The number of blocks bound: `Lcount` never exceeds `countLongCodes`. -/
theorem Lcount_le_countLongCodes (lengths : Array UInt8) (maxBits start : Nat)
    (hstart : start ≤ lengths.size) :
    Lcount lengths maxBits start
      ≤ countLongCodes (countLengthsFast lengths maxBits) maxBits := by
  refine Nat.le_trans (Lcount_mono lengths maxBits hstart) ?_
  rw [Lcount_eq_rangeSum, countLongCodes_eq]
  apply Nat.le_of_eq
  apply rangeSum_congr
  intro j hj hjm
  exact (numEarlier_size_eq lengths maxBits j (by omega) hjm).symm

/-- `Lcount` counts a subset of the indices `< n`, so is bounded by `n`. -/
theorem Lcount_le_self (lengths : Array UInt8) (maxBits n : Nat) :
    Lcount lengths maxBits n ≤ n := by
  induction n with
  | zero => simp [Lcount]
  | succ k ih => rw [Lcount]; split <;> omega

/-- `Lcount` over all symbols is exactly `countLongCodes`. -/
theorem Lcount_size_eq (lengths : Array UInt8) (maxBits : Nat) :
    Lcount lengths maxBits lengths.size
      = countLongCodes (countLengthsFast lengths maxBits) maxBits := by
  rw [Lcount_eq_rangeSum, countLongCodes_eq]
  apply rangeSum_congr
  intro j hj hjm
  exact (numEarlier_size_eq lengths maxBits j (by omega) hjm).symm

/-- `countLongCodes` (the `subs` block count) is at most the number of symbols. -/
theorem countLongCodes_le_size (lengths : Array UInt8) (maxBits : Nat) :
    countLongCodes (countLengthsFast lengths maxBits) maxBits ≤ lengths.size := by
  rw [← Lcount_size_eq]; exact Lcount_le_self lengths maxBits lengths.size

/-- **At most one long symbol matches `buf`.** Two matching codewords are `cwOf`
    prefixes of one another, so prefix-freeness forces the symbols equal. -/
theorem match_unique (lengths : Array UInt8) (maxBits : Nat)
    (hv : Huffman.Spec.ValidLengths (lengths.toList.map UInt8.toNat) maxBits) (buf : UInt64)
    (k1 k2 : Nat)
    (hcf1 : Huffman.Spec.codeFor (lengths.toList.map UInt8.toNat) maxBits k1
        = some (cwOf buf.toNat lengths[k1]!.toNat))
    (hcf2 : Huffman.Spec.codeFor (lengths.toList.map UInt8.toNat) maxBits k2
        = some (cwOf buf.toNat lengths[k2]!.toNat)) : k1 = k2 := by
  refine Decidable.by_contra (fun hne => ?_)
  rcases Nat.le_total lengths[k1]!.toNat lengths[k2]!.toNat with hle | hle
  · exact Huffman.Spec.canonical_prefix_free (lengths.toList.map UInt8.toNat) maxBits hv
      k1 k2 _ _ hcf1 hcf2 hne (cwOf_prefix buf.toNat _ _ hle)
  · exact Huffman.Spec.canonical_prefix_free (lengths.toList.map UInt8.toNat) maxBits hv
      k2 k1 _ _ hcf2 hcf1 (Ne.symm hne) (cwOf_prefix buf.toNat _ _ hle)

/-! ## The codeword ↔ subtable-index decomposition

A length-`len` long codeword `rev = bitReverse c len 0` matches `buf` iff `buf`'s
low `len` bits equal `rev`; that splits into: the `fastBits`-prefix agrees
(`subPrefix buf = rev % 2^fastBits`, selecting the block) and the next
`len - fastBits` bits agree (`subIndex … % 2^(len-fastBits) = rev / 2^fastBits`,
selecting the slot within the block). -/

/-- Decompose the length-`len` match on `buf` into a `subPrefix`/`subIndex`
    agreement, mirroring the block/slot split `buildSubLoop` fills along. -/
theorem match_decomp (maxBits len : Nat) (hmb15 : maxBits ≤ 15)
    (hfl : fastBits < len) (hlm : len ≤ maxBits) (buf : UInt64) (rev : Nat)
    (hrev : rev < 2 ^ len) :
    buf.toNat % 2 ^ len = rev ↔
      (subPrefix buf = rev % 2 ^ fastBits ∧
        subIndex maxBits buf % 2 ^ (len - fastBits) = rev / 2 ^ fastBits) := by
  have hAB : 2 ^ fastBits * 2 ^ (len - fastBits) = 2 ^ len := by
    rw [← Nat.pow_add, Nat.add_sub_cancel' (Nat.le_of_lt hfl)]
  have hdvd1 : (2 : Nat) ^ fastBits ∣ 2 ^ len := Nat.pow_dvd_pow 2 (Nat.le_of_lt hfl)
  have hdvd2 : (2 : Nat) ^ (len - fastBits) ∣ 2 ^ (maxBits - fastBits) :=
    Nat.pow_dvd_pow 2 (by omega)
  -- rewrite subIndex's inner mod to the `(buf / 2^fastBits) % 2^(len-fastBits)` form
  have hsubIdxMod : subIndex maxBits buf % 2 ^ (len - fastBits)
      = (buf.toNat / 2 ^ fastBits) % 2 ^ (len - fastBits) := by
    rw [subIndex_eq maxBits hmb15, Nat.mod_mod_of_dvd _ hdvd2]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rw [subPrefix_eq_mod, ← Nat.mod_mod_of_dvd buf.toNat hdvd1, h]
    · rw [hsubIdxMod, ← Nat.mod_mul_right_div_self buf.toNat (2 ^ fastBits) (2 ^ (len - fastBits)),
          hAB, h]
  · rintro ⟨h1, h2⟩
    rw [subPrefix_eq_mod] at h1
    rw [hsubIdxMod] at h2
    rw [← hAB, Nat.mod_mul, h1, h2, Nat.add_comm, Nat.div_add_mod]

/-! ## The `buildSubLoop` fill invariant

The single loop lemma below characterizes the final `rootSub`/`subs` at a fixed
`buf`: a processed long symbol matching `buf` records its packed entry at the
lookup slot (`fill`), and a non-sentinel slot is always a real match (`sent`,
contrapositive). The nine threaded hypotheses are the loop invariant — NC on
`nextCode`, the block-count bound, and the block-allocation / freshness /
slot-provenance facts. -/

/-- **`buildSubLoop` fill/sentinel invariant.** For a fixed `buf`, the loop's
    result pair `(R, S)` records exactly the long codewords matching `buf`:
    every processed long symbol whose canonical codeword is `cwOf buf L` writes
    its packed entry into the lookup slot, and a non-sentinel slot is such a match.
    Proved by well-founded induction threading the NC / block-count / allocation /
    freshness / slot invariants. -/
theorem buildSubLoop_spec
    (lengths : Array UInt8) (maxBits : Nat) (hmb15 : maxBits ≤ 15)
    (hv : Huffman.Spec.ValidLengths (lengths.toList.map UInt8.toNat) maxBits)
    (hbound : lengths.size ≤ UInt16.size) (buf : UInt64)
    (nextCode rootSub subs : Array UInt32) (start nextBlock : Nat)
    (hstart_le : start ≤ lengths.size)
    (hncsz : nextCode.size = maxBits + 1)
    (hrootsz : rootSub.size = 2 ^ fastBits)
    (hsubsz : subs.size
      = 2 ^ (maxBits - fastBits) * countLongCodes (countLengthsFast lengths maxBits) maxBits)
    (hnc : ∀ b, 1 ≤ b → b ≤ maxBits →
      nextCode[b]!.toNat
        = (Huffman.Spec.nextCodes
            (Huffman.Spec.countLengths (lengths.toList.map UInt8.toNat) maxBits) maxBits)[b]!
          + numEarlier (lengths.toList.map UInt8.toNat) b start)
    (hblock : nextBlock ≤ Lcount lengths maxBits start)
    (hE : ∀ q, q < 2 ^ fastBits → rootSub[q]! ≠ 0 →
      ∃ b, b < nextBlock ∧ rootSub[q]!.toNat = b * 2 ^ (maxBits - fastBits) + 1)
    (hINJ : ∀ q1 q2, q1 < 2 ^ fastBits → q2 < 2 ^ fastBits →
      rootSub[q1]! ≠ 0 → rootSub[q2]! ≠ 0 → rootSub[q1]!.toNat = rootSub[q2]!.toNat → q1 = q2)
    (hF : ∀ i, nextBlock * 2 ^ (maxBits - fastBits) ≤ i → i < subs.size → subs[i]! = packEntry 0 0)
    (hG : ∀ k, k < start → fastBits < lengths[k]!.toNat → lengths[k]!.toNat ≤ maxBits →
      Huffman.Spec.codeFor (lengths.toList.map UInt8.toNat) maxBits k
          = some (cwOf buf.toNat lengths[k]!.toNat) →
      rootSub[subPrefix buf]! ≠ 0 ∧
        subs[(rootSub[subPrefix buf]!.toNat - 1) + subIndex maxBits buf]!
          = packEntry k.toUInt16 lengths[k]!)
    (hH : (¬ ∃ k, k < start ∧ fastBits < lengths[k]!.toNat ∧ lengths[k]!.toNat ≤ maxBits ∧
        Huffman.Spec.codeFor (lengths.toList.map UInt8.toNat) maxBits k
          = some (cwOf buf.toNat lengths[k]!.toNat)) →
      rootSub[subPrefix buf]! ≠ 0 →
        subs[(rootSub[subPrefix buf]!.toNat - 1) + subIndex maxBits buf]! = packEntry 0 0) :
    ∀ R S : Array UInt32,
      buildSubLoop lengths nextCode maxBits start rootSub subs nextBlock = (R, S) →
      (∀ k, k < lengths.size → fastBits < lengths[k]!.toNat → lengths[k]!.toNat ≤ maxBits →
        Huffman.Spec.codeFor (lengths.toList.map UInt8.toNat) maxBits k
            = some (cwOf buf.toNat lengths[k]!.toNat) →
        R[subPrefix buf]! ≠ 0 ∧
          S[(R[subPrefix buf]!.toNat - 1) + subIndex maxBits buf]!
            = packEntry k.toUInt16 lengths[k]!) ∧
      ((¬ ∃ k, k < lengths.size ∧ fastBits < lengths[k]!.toNat ∧ lengths[k]!.toNat ≤ maxBits ∧
          Huffman.Spec.codeFor (lengths.toList.map UInt8.toNat) maxBits k
            = some (cwOf buf.toNat lengths[k]!.toNat)) →
        R[subPrefix buf]! ≠ 0 →
          S[(R[subPrefix buf]!.toNat - 1) + subIndex maxBits buf]! = packEntry 0 0) := by
  intro R S hRS
  rw [buildSubLoop] at hRS
  by_cases hstart : start < lengths.size
  · rw [dif_pos hstart] at hRS
    have hls_len : start < (lengths.toList.map UInt8.toNat).length := by
      rw [List.length_map, Array.length_toList]; exact hstart
    have hls_start : (lengths.toList.map UInt8.toNat)[start]'hls_len = lengths[start].toNat := by
      simp only [List.getElem_map, Array.getElem_toList]
    have hget! : lengths[start]! = lengths[start] := getElem!_pos lengths start hstart
    have hlen_le : lengths[start].toNat ≤ maxBits := by
      rw [← hls_start]; exact hv.1 _ (List.getElem_mem hls_len)
    by_cases hlen : 0 < lengths[start].toNat ∧ lengths[start].toNat < nextCode.size
    · rw [dif_pos hlen] at hRS
      have hc! : (nextCode[lengths[start].toNat]'hlen.2) = nextCode[lengths[start].toNat]! :=
        (getElem!_pos nextCode _ hlen.2).symm
      -- NC invariant threads through the `nextCode` increment
      have hnc' : ∀ b, 1 ≤ b → b ≤ maxBits →
          (nextCode.set! lengths[start].toNat (nextCode[lengths[start].toNat]! + 1))[b]!.toNat
            = (Huffman.Spec.nextCodes
                (Huffman.Spec.countLengths (lengths.toList.map UInt8.toNat) maxBits) maxBits)[b]!
              + numEarlier (lengths.toList.map UInt8.toNat) b (start + 1) := fun b hb1 hb15 =>
        Deflate.Correctness.nc_invariant_step lengths nextCode start
          (lengths.toList.map UInt8.toNat) maxBits _ rfl _ rfl hv (by omega)
          (Nat.le_of_eq hncsz.symm) hstart hls_len hls_start hlen_le hlen.1 hnc b hb1 hb15
      have hncsz' : (nextCode.set! lengths[start].toNat
          (nextCode[lengths[start].toNat]! + 1)).size = maxBits + 1 := by
        rw [Array.size_set!]; exact hncsz
      by_cases hfast : fastBits < lengths[start].toNat
      · rw [if_pos hfast] at hRS
        simp only [hc!] at hRS
        -- abbreviations used below (written inline in terms):
        --   L := lengths[start].toNat, cval := nextCode[L]!.toNat,
        --   rev := bitReverse cval L 0, pl := rev % 2^fastBits, sB := rev / 2^fastBits.
        have hL_lt256 : lengths[start].toNat < 256 := by omega
        have hrev_lt : bitReverse (nextCode[lengths[start].toNat]!).toNat lengths[start].toNat 0
            < 2 ^ lengths[start].toNat := bitReverse_lt _ _
        have hpl_lt : bitReverse (nextCode[lengths[start].toNat]!).toNat lengths[start].toNat 0
            % 2 ^ fastBits < 2 ^ fastBits := Nat.mod_lt _ (Nat.two_pow_pos _)
        have hlong_start : fastBits < lengths[start]!.toNat ∧ lengths[start]!.toNat ≤ maxBits := by
          rw [hget!]; exact ⟨hfast, hlen_le⟩
        -- canonical codeword of `start`
        have hcf_start : Huffman.Spec.codeFor (lengths.toList.map UInt8.toNat) maxBits start
            = some (Huffman.Spec.natToBits (nextCode[lengths[start].toNat]!).toNat
                lengths[start].toNat) := by
          rw [codeFor_placed lengths maxBits start hstart (by rw [hget!]; exact hlen.1)
                (by rw [hget!]; exact hlen_le), hget!,
              ← hnc lengths[start].toNat hlen.1 hlen_le]
        -- match characterization: `start` matches `buf` iff its low bits equal `rev`
        have hmatch_iff : (Huffman.Spec.codeFor (lengths.toList.map UInt8.toNat) maxBits start
              = some (cwOf buf.toNat lengths[start].toNat)) ↔
            buf.toNat % 2 ^ lengths[start].toNat
              = bitReverse (nextCode[lengths[start].toNat]!).toNat lengths[start].toNat 0 := by
          rw [hcf_start, Option.some.injEq, eq_comm]
          exact cwOf_eq_iff_mod buf.toNat _ _
        -- when `start` matches, its prefix is `subPrefix buf`
        have hpl_of_match : buf.toNat % 2 ^ lengths[start].toNat
              = bitReverse (nextCode[lengths[start].toNat]!).toNat lengths[start].toNat 0 →
            subPrefix buf
              = bitReverse (nextCode[lengths[start].toNat]!).toNat lengths[start].toNat 0
                % 2 ^ fastBits :=
          fun hm => ((match_decomp maxBits lengths[start].toNat hmb15 hfast hlen_le buf _ hrev_lt).mp hm).1
        -- `start` is a long symbol, so `Lcount` grows and `nextBlock` has room
        have hstart_long_L : Lcount lengths maxBits (start + 1) = Lcount lengths maxBits start + 1 := by
          rw [Lcount, if_pos (by rw [hget!]; exact ⟨hfast, hlen_le⟩)]
        have hnb_lt_num : nextBlock < countLongCodes (countLengthsFast lengths maxBits) maxBits := by
          have h1 : Lcount lengths maxBits (start + 1) ≤ countLongCodes (countLengthsFast lengths maxBits) maxBits :=
            Lcount_le_countLongCodes lengths maxBits (start + 1) (by omega)
          omega
        -- key power identity and the `2^m`-block containment of a codeword's fill
        have hpow_split : 2 ^ (lengths[start].toNat - fastBits) * 2 ^ (maxBits - lengths[start].toNat)
            = 2 ^ (maxBits - fastBits) := by
          rw [← Nat.pow_add]; congr 1; omega
        have hslot_bound : ∀ j, j < 2 ^ (maxBits - lengths[start].toNat) →
            bitReverse (nextCode[lengths[start].toNat]!).toNat lengths[start].toNat 0 / 2 ^ fastBits
              + j * 2 ^ (lengths[start].toNat - fastBits) < 2 ^ (maxBits - fastBits) := by
          intro j hj
          have hsB : bitReverse (nextCode[lengths[start].toNat]!).toNat lengths[start].toNat 0
              / 2 ^ fastBits < 2 ^ (lengths[start].toNat - fastBits) :=
            Nat.div_lt_of_lt_mul (by rw [← Nat.pow_add,
              Nat.add_sub_cancel' (Nat.le_of_lt hfast)]; exact hrev_lt)
          calc bitReverse (nextCode[lengths[start].toNat]!).toNat lengths[start].toNat 0 / 2 ^ fastBits
                + j * 2 ^ (lengths[start].toNat - fastBits)
              < 2 ^ (lengths[start].toNat - fastBits) + j * 2 ^ (lengths[start].toNat - fastBits) := by omega
            _ = (j + 1) * 2 ^ (lengths[start].toNat - fastBits) := by rw [Nat.succ_mul]; omega
            _ ≤ 2 ^ (maxBits - lengths[start].toNat) * 2 ^ (lengths[start].toNat - fastBits) :=
                Nat.mul_le_mul_right _ (by omega)
            _ = 2 ^ (maxBits - fastBits) := by rw [Nat.mul_comm]; exact hpow_split
        -- `nextBlock * 2^m + 1` fits in `UInt32`
        have hbound32 : nextBlock * 2 ^ (maxBits - fastBits) + 1 < 2 ^ 32 := by
          have h2m : 2 ^ (maxBits - fastBits) ≤ 16 := by
            calc 2 ^ (maxBits - fastBits) ≤ 2 ^ 4 :=
                  Nat.pow_le_pow_right (by decide) (by simp only [fastBits]; omega)
              _ = 16 := by decide
          have hnb : nextBlock ≤ 65536 := by
            have h1 := Nat.le_trans (Nat.le_of_lt hnb_lt_num) (countLongCodes_le_size lengths maxBits)
            have h2 : (UInt16.size : Nat) = 65536 := rfl
            omega
          have := Nat.mul_le_mul hnb h2m
          omega
        -- `nextBlock * 2^m` (the fresh block base) is a valid `UInt32`-roundtripped value
        have hoff_toNat : ((nextBlock * 2 ^ (maxBits - fastBits) + 1 : Nat).toUInt32).toNat
            = nextBlock * 2 ^ (maxBits - fastBits) + 1 := by
          rw [show ∀ n : Nat, n.toUInt32.toNat = n % 2 ^ 32 from fun _ => rfl,
              Nat.mod_eq_of_lt hbound32]
        by_cases hseen : (rootSub[bitReverse (nextCode[lengths[start].toNat]!).toNat
            lengths[start].toNat 0 % 2 ^ fastBits]! == 0) = true
        · -- allocation: `start`'s prefix `pl` gets a fresh block `nextBlock`
          simp only [if_pos hseen] at hRS
          have hseen0 : rootSub[bitReverse (nextCode[lengths[start].toNat]!).toNat
              lengths[start].toNat 0 % 2 ^ fastBits]! = 0 := by
            simpa only [beq_iff_eq] using hseen
          refine buildSubLoop_spec lengths maxBits hmb15 hv hbound buf _ _ _ (start + 1)
            (nextBlock + 1) (by omega) hncsz' (by rw [Array.size_set!]; exact hrootsz)
            (by rw [fillSlots_size]; exact hsubsz) hnc' (by rw [hstart_long_L]; omega) ?_ ?_ ?_ ?_ ?_
            R S hRS
          · -- hE': the new entry is `nextBlock * 2^m + 1`, all others as before
            intro q hq hqne
            by_cases hqpl : q = bitReverse (nextCode[lengths[start].toNat]!).toNat
                lengths[start].toNat 0 % 2 ^ fastBits
            · subst hqpl
              rw [Array.getElem!_set!_self _ _ _ (by rw [hrootsz]; exact hpl_lt)]
              exact ⟨nextBlock, by omega, by rw [hoff_toNat]⟩
            · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hqpl)] at hqne ⊢
              obtain ⟨b, hb, hbeq⟩ := hE q hq hqne
              exact ⟨b, by omega, hbeq⟩
          · -- hINJ': the fresh entry `nextBlock * 2^m + 1` differs from all earlier blocks
            intro q1 q2 hq1 hq2 hne1 hne2 heq
            by_cases hq1pl : q1 = bitReverse (nextCode[lengths[start].toNat]!).toNat
                lengths[start].toNat 0 % 2 ^ fastBits <;>
              by_cases hq2pl : q2 = bitReverse (nextCode[lengths[start].toNat]!).toNat
                lengths[start].toNat 0 % 2 ^ fastBits
            · rw [hq1pl, hq2pl]
            · exfalso
              rw [hq1pl, Array.getElem!_set!_self _ _ _ (by rw [hrootsz]; exact hpl_lt), hoff_toNat,
                  Array.getElem!_set!_ne _ _ _ _ (Ne.symm hq2pl)] at heq
              rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hq2pl)] at hne2
              obtain ⟨b2, hb2, hbeq2⟩ := hE q2 hq2 hne2
              rw [hbeq2] at heq
              have hmul : nextBlock * 2 ^ (maxBits - fastBits) = b2 * 2 ^ (maxBits - fastBits) := by omega
              have : nextBlock = b2 := Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos _) hmul
              omega
            · exfalso
              rw [hq2pl, Array.getElem!_set!_self _ _ _ (by rw [hrootsz]; exact hpl_lt), hoff_toNat,
                  Array.getElem!_set!_ne _ _ _ _ (Ne.symm hq1pl)] at heq
              rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hq1pl)] at hne1
              obtain ⟨b1, hb1, hbeq1⟩ := hE q1 hq1 hne1
              rw [hbeq1] at heq
              have hmul : b1 * 2 ^ (maxBits - fastBits) = nextBlock * 2 ^ (maxBits - fastBits) := by omega
              have : b1 = nextBlock := Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos _) hmul
              omega
            · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hq1pl)] at hne1 heq
              rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hq2pl)] at hne2 heq
              exact hINJ q1 q2 hq1 hq2 hne1 hne2 heq
          · -- hF': the fill stays within the new block, tail beyond `(nextBlock+1)*2^m` untouched
            intro i hi hisz
            rw [fillSlots_size] at hisz
            have hexp : (nextBlock + 1) * 2 ^ (maxBits - fastBits)
                = nextBlock * 2 ^ (maxBits - fastBits) + 2 ^ (maxBits - fastBits) := by
              rw [Nat.succ_mul]
            rw [fillSlots_getElem_ne subs _ _ _ i _ (fun j hj => by
              have := hslot_bound j hj; omega)]
            exact hF i (by omega) hisz
          · -- hG': a matching processed symbol records its packed entry
            intro k hk hlong hkm hcf
            rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hk) with hlt | heq
            · -- k < start: matches at a prefix already allocated (≠ the fresh one)
              obtain ⟨hrootpf_ne, hslot_old⟩ := hG k hlt hlong hkm hcf
              have hpl_ne_pf : bitReverse (nextCode[lengths[start].toNat]!).toNat
                  lengths[start].toNat 0 % 2 ^ fastBits ≠ subPrefix buf := fun h => hrootpf_ne (h ▸ hseen0)
              obtain ⟨bpf, hbpf, hbpfeq⟩ := hE (subPrefix buf) (subPrefix_lt buf) hrootpf_ne
              refine ⟨by rw [Array.getElem!_set!_ne _ _ _ _ hpl_ne_pf]; exact hrootpf_ne, ?_⟩
              rw [Array.getElem!_set!_ne _ _ _ _ hpl_ne_pf,
                  fillSlots_getElem_ne subs _ _ _ _ _ (fun j hj => by
                    have hT := subIndex_lt maxBits hmb15 buf
                    have hmul : (bpf + 1) * 2 ^ (maxBits - fastBits)
                        ≤ nextBlock * 2 ^ (maxBits - fastBits) :=
                      Nat.mul_le_mul_right _ (by omega)
                    rw [Nat.succ_mul] at hmul
                    have hkey : bpf * 2 ^ (maxBits - fastBits) + subIndex maxBits buf
                        < nextBlock * 2 ^ (maxBits - fastBits) :=
                      Nat.lt_of_lt_of_le (Nat.add_lt_add_left hT (bpf * 2 ^ (maxBits - fastBits))) hmul
                    rw [hbpfeq, Nat.add_sub_cancel]
                    exact Nat.ne_of_lt (Nat.lt_of_lt_of_le hkey
                      (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))))]
              exact hslot_old
            · -- k = start: the fill places `start`'s entry at the lookup slot
              subst k
              rw [hget!] at hcf
              have hmatch : buf.toNat % 2 ^ lengths[start].toNat
                  = bitReverse (nextCode[lengths[start].toNat]!).toNat lengths[start].toNat 0 :=
                hmatch_iff.mp hcf
              have hpf_eq_pl : subPrefix buf
                  = bitReverse (nextCode[lengths[start].toNat]!).toNat lengths[start].toNat 0
                    % 2 ^ fastBits := hpl_of_match hmatch
              have hThi : subIndex maxBits buf % 2 ^ (lengths[start].toNat - fastBits)
                  = bitReverse (nextCode[lengths[start].toNat]!).toNat lengths[start].toNat 0
                    / 2 ^ fastBits :=
                ((match_decomp maxBits lengths[start].toNat hmb15 hfast hlen_le buf _ hrev_lt).mp
                  hmatch).2
              have hrootpf_val : (rootSub.set! (bitReverse (nextCode[lengths[start].toNat]!).toNat
                    lengths[start].toNat 0 % 2 ^ fastBits)
                    ((nextBlock * 2 ^ (maxBits - fastBits) + 1).toUInt32))[subPrefix buf]!.toNat
                  = nextBlock * 2 ^ (maxBits - fastBits) + 1 := by
                rw [hpf_eq_pl, Array.getElem!_set!_self _ _ _ (by rw [hrootsz]; exact hpl_lt), hoff_toNat]
              have hne0 : (rootSub.set! (bitReverse (nextCode[lengths[start].toNat]!).toNat
                    lengths[start].toNat 0 % 2 ^ fastBits)
                    ((nextBlock * 2 ^ (maxBits - fastBits) + 1).toUInt32))[subPrefix buf]! ≠ 0 := by
                intro h0
                rw [h0, show ((0 : UInt32)).toNat = 0 from rfl] at hrootpf_val
                omega
              refine ⟨hne0, ?_⟩
              rw [hrootpf_val]
              have hj0_lt : subIndex maxBits buf / 2 ^ (lengths[start].toNat - fastBits)
                  < 2 ^ (maxBits - lengths[start].toNat) :=
                Nat.div_lt_of_lt_mul (by rw [hpow_split]; exact subIndex_lt maxBits hmb15 buf)
              have hidx_eq : nextBlock * 2 ^ (maxBits - fastBits) + 1 - 1 + subIndex maxBits buf
                  = nextBlock * 2 ^ (maxBits - fastBits)
                      + bitReverse (nextCode[lengths[start].toNat]!).toNat lengths[start].toNat 0
                        / 2 ^ fastBits
                    + subIndex maxBits buf / 2 ^ (lengths[start].toNat - fastBits)
                      * 2 ^ (lengths[start].toNat - fastBits) := by
                have hdm := Nat.div_add_mod (subIndex maxBits buf) (2 ^ (lengths[start].toNat - fastBits))
                rw [hThi, Nat.mul_comm] at hdm; omega
              rw [hidx_eq,
                  fillSlots_getElem_eq subs _ _ _ _ _ (Nat.two_pow_pos _) hj0_lt (by
                    rw [← hidx_eq, Nat.add_sub_cancel, hsubsz,
                        Nat.mul_comm (2 ^ (maxBits - fastBits))]
                    have hT := subIndex_lt maxBits hmb15 buf
                    have hmul : (nextBlock + 1) * 2 ^ (maxBits - fastBits)
                        ≤ countLongCodes (countLengthsFast lengths maxBits) maxBits
                          * 2 ^ (maxBits - fastBits) := Nat.mul_le_mul_right _ (by omega)
                    rw [Nat.succ_mul] at hmul
                    exact Nat.lt_of_lt_of_le
                      (Nat.add_lt_add_left hT (nextBlock * 2 ^ (maxBits - fastBits))) hmul)]
              rw [hget!]
          · -- hH': no processed match ⇒ the lookup slot is the sentinel
            intro hno hne
            by_cases hpf_pl : subPrefix buf = bitReverse (nextCode[lengths[start].toNat]!).toNat
                lengths[start].toNat 0 % 2 ^ fastBits
            · -- pf = pl: the fresh block, `start` itself does not match, slot stays fresh
              have hstart_nomatch : ¬ buf.toNat % 2 ^ lengths[start].toNat
                  = bitReverse (nextCode[lengths[start].toNat]!).toNat lengths[start].toNat 0 := by
                intro hm
                exact hno ⟨start, Nat.lt_succ_self start, hlong_start.1, hlong_start.2,
                  by rw [hget!]; exact hmatch_iff.mpr hm⟩
              have hval : (rootSub.set! (bitReverse (nextCode[lengths[start].toNat]!).toNat
                    lengths[start].toNat 0 % 2 ^ fastBits)
                    ((nextBlock * 2 ^ (maxBits - fastBits) + 1).toUInt32))[subPrefix buf]!.toNat
                  = nextBlock * 2 ^ (maxBits - fastBits) + 1 := by
                rw [hpf_pl, Array.getElem!_set!_self _ _ _ (by rw [hrootsz]; exact hpl_lt), hoff_toNat]
              rw [hval, Nat.add_sub_cancel,
                  fillSlots_getElem_ne subs _ _ _ _ _ (fun j hj => by
                    intro heq
                    apply hstart_nomatch
                    have hsB : bitReverse (nextCode[lengths[start].toNat]!).toNat lengths[start].toNat 0
                        / 2 ^ fastBits < 2 ^ (lengths[start].toNat - fastBits) :=
                      Nat.div_lt_of_lt_mul (by rw [← Nat.pow_add,
                        Nat.add_sub_cancel' (Nat.le_of_lt hfast)]; exact hrev_lt)
                    have hTmod : subIndex maxBits buf % 2 ^ (lengths[start].toNat - fastBits)
                        = bitReverse (nextCode[lengths[start].toNat]!).toNat lengths[start].toNat 0
                          / 2 ^ fastBits := by
                      have : subIndex maxBits buf
                          = bitReverse (nextCode[lengths[start].toNat]!).toNat lengths[start].toNat 0
                            / 2 ^ fastBits + j * 2 ^ (lengths[start].toNat - fastBits) := by omega
                      rw [this, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hsB]
                    exact (match_decomp maxBits lengths[start].toNat hmb15 hfast hlen_le buf _
                      hrev_lt).mpr ⟨hpf_pl, hTmod⟩)]
              refine hF _ (Nat.le_add_right _ _) ?_
              rw [hsubsz, Nat.mul_comm (2 ^ (maxBits - fastBits))]
              have hT := subIndex_lt maxBits hmb15 buf
              have hmul : (nextBlock + 1) * 2 ^ (maxBits - fastBits)
                  ≤ countLongCodes (countLengthsFast lengths maxBits) maxBits * 2 ^ (maxBits - fastBits) :=
                Nat.mul_le_mul_right _ (by omega)
              rw [Nat.succ_mul] at hmul
              exact Nat.lt_of_lt_of_le
                (Nat.add_lt_add_left hT (nextBlock * 2 ^ (maxBits - fastBits))) hmul
            · -- pf ≠ pl: the fill (fresh block) leaves `pf`'s slot; carry the old sentinel
              have hpl_ne_pf : bitReverse (nextCode[lengths[start].toNat]!).toNat lengths[start].toNat 0
                  % 2 ^ fastBits ≠ subPrefix buf := fun h => hpf_pl h.symm
              rw [Array.getElem!_set!_ne _ _ _ _ hpl_ne_pf] at hne
              obtain ⟨bpf, hbpf, hbpfeq⟩ := hE (subPrefix buf) (subPrefix_lt buf) hne
              rw [Array.getElem!_set!_ne _ _ _ _ hpl_ne_pf,
                  fillSlots_getElem_ne subs _ _ _ _ _ (fun j hj => by
                    have hT := subIndex_lt maxBits hmb15 buf
                    have hmul : (bpf + 1) * 2 ^ (maxBits - fastBits)
                        ≤ nextBlock * 2 ^ (maxBits - fastBits) := Nat.mul_le_mul_right _ (by omega)
                    rw [Nat.succ_mul] at hmul
                    have hkey : bpf * 2 ^ (maxBits - fastBits) + subIndex maxBits buf
                        < nextBlock * 2 ^ (maxBits - fastBits) :=
                      Nat.lt_of_lt_of_le (Nat.add_lt_add_left hT (bpf * 2 ^ (maxBits - fastBits))) hmul
                    rw [hbpfeq, Nat.add_sub_cancel]
                    exact Nat.ne_of_lt (Nat.lt_of_lt_of_le hkey
                      (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))))]
              exact hH (fun ⟨k, hk, rest⟩ => hno ⟨k, by omega, rest⟩) hne
        · -- existing block: `start`'s prefix already owns a block (`nextBlock`/`rootSub` unchanged)
          simp only [if_neg hseen] at hRS
          clear hoff_toNat hbound32
          have hseen_ne : rootSub[bitReverse (nextCode[lengths[start].toNat]!).toNat
              lengths[start].toNat 0 % 2 ^ fastBits]! ≠ 0 := by simpa only [beq_iff_eq] using hseen
          obtain ⟨bpl, hbpl, hbpleq⟩ :=
            hE (bitReverse (nextCode[lengths[start].toNat]!).toNat lengths[start].toNat 0
              % 2 ^ fastBits) hpl_lt hseen_ne
          refine buildSubLoop_spec lengths maxBits hmb15 hv hbound buf _ rootSub _ (start + 1)
            nextBlock (by omega) hncsz' hrootsz (by rw [fillSlots_size]; exact hsubsz) hnc'
            (by rw [hstart_long_L]; omega) hE hINJ ?_ ?_ ?_ R S hRS
          · -- hF': the fill stays inside `pl`'s (existing) block, tail beyond `nextBlock*2^m` untouched
            intro i hi hisz
            rw [fillSlots_size] at hisz
            rw [fillSlots_getElem_ne subs _ _ _ _ _ (fun j hj => by
              have hsb := hslot_bound j hj
              have hmul : (bpl + 1) * 2 ^ (maxBits - fastBits) ≤ nextBlock * 2 ^ (maxBits - fastBits) :=
                Nat.mul_le_mul_right _ (by omega)
              rw [Nat.succ_mul] at hmul
              rw [hbpleq, Nat.add_sub_cancel]
              refine Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le ?_ hmul) hi)
              rw [Nat.add_assoc]; exact Nat.add_lt_add_left hsb _)]
            exact hF i hi hisz
          · -- hG': a matching processed symbol records its packed entry
            intro k hk hlong hkm hcf
            rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hk) with hlt | heq
            · -- k < start: unique match; the fill leaves `pf`'s slot
              obtain ⟨hrootpf_ne, hslot_old⟩ := hG k hlt hlong hkm hcf
              obtain ⟨bpf, hbpf, hbpfeq⟩ := hE (subPrefix buf) (subPrefix_lt buf) hrootpf_ne
              refine ⟨hrootpf_ne, ?_⟩
              rw [fillSlots_getElem_ne subs _ _ _ _ _ (fun j hj => by
                intro heq
                have hT := subIndex_lt maxBits hmb15 buf
                have hsb := hslot_bound j hj
                have hsB : bitReverse (nextCode[lengths[start].toNat]!).toNat lengths[start].toNat 0
                    / 2 ^ fastBits < 2 ^ (lengths[start].toNat - fastBits) :=
                  Nat.div_lt_of_lt_mul (by rw [← Nat.pow_add,
                    Nat.add_sub_cancel' (Nat.le_of_lt hfast)]; exact hrev_lt)
                rw [hbpfeq, hbpleq, Nat.add_sub_cancel, Nat.add_sub_cancel] at heq
                have hbb : bpf = bpl := by
                  rcases Nat.lt_trichotomy bpf bpl with h | h | h
                  · exfalso
                    have hle := Nat.mul_le_mul_right (2 ^ (maxBits - fastBits)) h
                    rw [Nat.succ_mul] at hle
                    have h1 : bpl * 2 ^ (maxBits - fastBits)
                        ≤ bpf * 2 ^ (maxBits - fastBits) + subIndex maxBits buf := by rw [heq]; exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
                    omega
                  · exact h
                  · exfalso
                    have hle := Nat.mul_le_mul_right (2 ^ (maxBits - fastBits)) h
                    rw [Nat.succ_mul] at hle
                    have h1 : bpf * 2 ^ (maxBits - fastBits) + subIndex maxBits buf
                        < bpf * 2 ^ (maxBits - fastBits) := by
                      rw [heq]; exact Nat.lt_of_lt_of_le (by omega) hle
                    omega
                subst hbb
                have hpf_pl : subPrefix buf = bitReverse (nextCode[lengths[start].toNat]!).toNat
                    lengths[start].toNat 0 % 2 ^ fastBits :=
                  hINJ (subPrefix buf) _ (subPrefix_lt buf) hpl_lt hrootpf_ne hseen_ne
                    (by rw [hbpfeq, hbpleq])
                have hsub : subIndex maxBits buf
                    = bitReverse (nextCode[lengths[start].toNat]!).toNat lengths[start].toNat 0
                      / 2 ^ fastBits + j * 2 ^ (lengths[start].toNat - fastBits) := by omega
                have hTmod : subIndex maxBits buf % 2 ^ (lengths[start].toNat - fastBits)
                    = bitReverse (nextCode[lengths[start].toNat]!).toNat lengths[start].toNat 0
                      / 2 ^ fastBits := by
                  rw [hsub, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hsB]
                have hstart_match : buf.toNat % 2 ^ lengths[start].toNat
                    = bitReverse (nextCode[lengths[start].toNat]!).toNat lengths[start].toNat 0 :=
                  (match_decomp maxBits lengths[start].toNat hmb15 hfast hlen_le buf _ hrev_lt).mpr
                    ⟨hpf_pl, hTmod⟩
                have hstart_cf : Huffman.Spec.codeFor (lengths.toList.map UInt8.toNat) maxBits start
                    = some (cwOf buf.toNat lengths[start]!.toNat) := by
                  rw [hget!]; exact hmatch_iff.mpr hstart_match
                exact absurd (match_unique lengths maxBits hv buf start k hstart_cf hcf) (by omega))]
              exact hslot_old
            · -- k = start: the fill places `start`'s entry at the lookup slot
              subst k
              rw [hget!] at hcf
              have hmatch : buf.toNat % 2 ^ lengths[start].toNat
                  = bitReverse (nextCode[lengths[start].toNat]!).toNat lengths[start].toNat 0 :=
                hmatch_iff.mp hcf
              have hpf_eq_pl : subPrefix buf
                  = bitReverse (nextCode[lengths[start].toNat]!).toNat lengths[start].toNat 0
                    % 2 ^ fastBits := hpl_of_match hmatch
              have hThi : subIndex maxBits buf % 2 ^ (lengths[start].toNat - fastBits)
                  = bitReverse (nextCode[lengths[start].toNat]!).toNat lengths[start].toNat 0
                    / 2 ^ fastBits :=
                ((match_decomp maxBits lengths[start].toNat hmb15 hfast hlen_le buf _ hrev_lt).mp
                  hmatch).2
              have hrootpf_val : rootSub[subPrefix buf]!.toNat = bpl * 2 ^ (maxBits - fastBits) + 1 := by
                rw [hpf_eq_pl, hbpleq]
              have hne0 : rootSub[subPrefix buf]! ≠ 0 := by
                intro h0
                rw [h0, show ((0 : UInt32)).toNat = 0 from rfl] at hrootpf_val
                omega
              refine ⟨hne0, ?_⟩
              rw [hpf_eq_pl, hbpleq]
              simp only [Nat.add_sub_cancel]
              have hj0_lt : subIndex maxBits buf / 2 ^ (lengths[start].toNat - fastBits)
                  < 2 ^ (maxBits - lengths[start].toNat) :=
                Nat.div_lt_of_lt_mul (by rw [hpow_split]; exact subIndex_lt maxBits hmb15 buf)
              have hidx_eq : bpl * 2 ^ (maxBits - fastBits) + subIndex maxBits buf
                  = bpl * 2 ^ (maxBits - fastBits)
                      + bitReverse (nextCode[lengths[start].toNat]!).toNat lengths[start].toNat 0
                        / 2 ^ fastBits
                    + subIndex maxBits buf / 2 ^ (lengths[start].toNat - fastBits)
                      * 2 ^ (lengths[start].toNat - fastBits) := by
                have hdm := Nat.div_add_mod (subIndex maxBits buf) (2 ^ (lengths[start].toNat - fastBits))
                rw [hThi, Nat.mul_comm] at hdm; omega
              rw [hidx_eq,
                  fillSlots_getElem_eq subs _ _ _ _ _ (Nat.two_pow_pos _) hj0_lt (by
                    rw [← hidx_eq, hsubsz, Nat.mul_comm (2 ^ (maxBits - fastBits))]
                    have hT := subIndex_lt maxBits hmb15 buf
                    have hmul : (bpl + 1) * 2 ^ (maxBits - fastBits)
                        ≤ countLongCodes (countLengthsFast lengths maxBits) maxBits
                          * 2 ^ (maxBits - fastBits) := Nat.mul_le_mul_right _ (by omega)
                    rw [Nat.succ_mul] at hmul
                    exact Nat.lt_of_lt_of_le
                      (Nat.add_lt_add_left hT (bpl * 2 ^ (maxBits - fastBits))) hmul)]
              rw [hget!]
          · -- hH': no processed match ⇒ the lookup slot is the sentinel
            intro hno hne
            obtain ⟨bpf, hbpf, hbpfeq⟩ := hE (subPrefix buf) (subPrefix_lt buf) hne
            rw [fillSlots_getElem_ne subs _ _ _ _ _ (fun j hj => by
              intro heq
              have hT := subIndex_lt maxBits hmb15 buf
              have hsb := hslot_bound j hj
              have hsB : bitReverse (nextCode[lengths[start].toNat]!).toNat lengths[start].toNat 0
                  / 2 ^ fastBits < 2 ^ (lengths[start].toNat - fastBits) :=
                Nat.div_lt_of_lt_mul (by rw [← Nat.pow_add,
                  Nat.add_sub_cancel' (Nat.le_of_lt hfast)]; exact hrev_lt)
              rw [hbpfeq, hbpleq, Nat.add_sub_cancel, Nat.add_sub_cancel] at heq
              have hbb : bpf = bpl := by
                rcases Nat.lt_trichotomy bpf bpl with h | h | h
                · exfalso
                  have hle := Nat.mul_le_mul_right (2 ^ (maxBits - fastBits)) h
                  rw [Nat.succ_mul] at hle
                  have h1 : bpl * 2 ^ (maxBits - fastBits)
                      ≤ bpf * 2 ^ (maxBits - fastBits) + subIndex maxBits buf := by rw [heq]; exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
                  omega
                · exact h
                · exfalso
                  have hle := Nat.mul_le_mul_right (2 ^ (maxBits - fastBits)) h
                  rw [Nat.succ_mul] at hle
                  have h1 : bpf * 2 ^ (maxBits - fastBits) + subIndex maxBits buf
                      < bpf * 2 ^ (maxBits - fastBits) := by
                    rw [heq]; exact Nat.lt_of_lt_of_le (by omega) hle
                  omega
              subst hbb
              have hpf_pl : subPrefix buf = bitReverse (nextCode[lengths[start].toNat]!).toNat
                  lengths[start].toNat 0 % 2 ^ fastBits :=
                hINJ (subPrefix buf) _ (subPrefix_lt buf) hpl_lt hne hseen_ne (by rw [hbpfeq, hbpleq])
              have hsub : subIndex maxBits buf
                  = bitReverse (nextCode[lengths[start].toNat]!).toNat lengths[start].toNat 0
                    / 2 ^ fastBits + j * 2 ^ (lengths[start].toNat - fastBits) := by omega
              have hTmod : subIndex maxBits buf % 2 ^ (lengths[start].toNat - fastBits)
                  = bitReverse (nextCode[lengths[start].toNat]!).toNat lengths[start].toNat 0
                    / 2 ^ fastBits := by
                rw [hsub, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hsB]
              have hstart_match : buf.toNat % 2 ^ lengths[start].toNat
                  = bitReverse (nextCode[lengths[start].toNat]!).toNat lengths[start].toNat 0 :=
                (match_decomp maxBits lengths[start].toNat hmb15 hfast hlen_le buf _ hrev_lt).mpr
                  ⟨hpf_pl, hTmod⟩
              exact hno ⟨start, Nat.lt_succ_self start, hlong_start.1, hlong_start.2,
                by rw [hget!]; exact hmatch_iff.mpr hstart_match⟩)]
            exact hH (fun ⟨k, hk, rest⟩ => hno ⟨k, by omega, rest⟩) hne
      · rw [if_neg hfast] at hRS
        simp only [hc!] at hRS
        -- short positive length: `nextCode` advances, no fill
        refine buildSubLoop_spec lengths maxBits hmb15 hv hbound buf _ rootSub subs (start + 1)
          nextBlock (by omega) hncsz' hrootsz hsubsz hnc' ?_ hE hINJ hF ?_ ?_ R S hRS
        · -- block bound: `start` is not long (`len ≤ fastBits`)
          rw [Lcount, if_neg (by rw [hget!]; omega)]; exact hblock
        · -- hG': the new symbol is not long, so no new match
          intro k hk hlong hkm hcf
          rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hk) with hlt | heq
          · exact hG k hlt hlong hkm hcf
          · subst heq; rw [hget!] at hlong; omega
        · -- hH': fewer symbols processed, so the no-match premise is weaker
          intro hno hne
          exact hH (fun ⟨k, hk, rest⟩ => hno ⟨k, by omega, rest⟩) hne
    · rw [dif_neg hlen] at hRS
      -- length 0 (or over-bound, impossible under validity): skip, nothing changes
      have hlen0 : lengths[start].toNat = 0 := by
        rcases Nat.eq_zero_or_pos lengths[start].toNat with h | h
        · exact h
        · exact absurd ⟨h, by rw [hncsz]; omega⟩ hlen
      have hls_val : (lengths.toList.map UInt8.toNat)[start]'hls_len = 0 := by
        rw [hls_start]; exact hlen0
      have hnc' : ∀ b, 1 ≤ b → b ≤ maxBits →
          nextCode[b]!.toNat
            = (Huffman.Spec.nextCodes
                (Huffman.Spec.countLengths (lengths.toList.map UInt8.toNat) maxBits) maxBits)[b]!
              + numEarlier (lengths.toList.map UInt8.toNat) b (start + 1) := fun b hb1 hb15 =>
        Deflate.Correctness.nc_invariant_skip nextCode start (lengths.toList.map UInt8.toNat)
          maxBits _ hls_len hls_val hnc b hb1 hb15
      refine buildSubLoop_spec lengths maxBits hmb15 hv hbound buf nextCode rootSub subs (start + 1)
        nextBlock (by omega) hncsz hrootsz hsubsz hnc' ?_ hE hINJ hF ?_ ?_ R S hRS
      · rw [Lcount, if_neg (by rw [hget!, hlen0]; simp only [fastBits]; omega)]; exact hblock
      · intro k hk hlong hkm hcf
        rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hk) with hlt | heq
        · exact hG k hlt hlong hkm hcf
        · subst heq; rw [hget!, hlen0] at hlong; simp only [fastBits] at hlong; omega
      · intro hno hne
        exact hH (fun ⟨k, hk, rest⟩ => hno ⟨k, by omega, rest⟩) hne
  · rw [dif_neg hstart] at hRS
    -- base case: the loop is finished, result is the current arrays
    rw [Prod.mk.injEq] at hRS
    obtain ⟨hRe, hSe⟩ := hRS
    subst hRe; subst hSe
    have hsize : lengths.size ≤ start := by omega
    -- long symbols only exist below `lengths.size`
    have hlong_lt : ∀ k, fastBits < lengths[k]!.toNat → k < lengths.size := by
      intro k hlong
      rcases Nat.lt_or_ge k lengths.size with hk | hk
      · exact hk
      · exfalso
        have hz : lengths[k]! = 0 := getElem!_neg lengths k (by omega)
        rw [hz] at hlong; simp only [UInt8.toNat_ofNat, fastBits] at hlong; omega
    refine ⟨?_, ?_⟩
    · intro k _ hlong hkm hcf
      exact hG k (Nat.lt_of_lt_of_le (hlong_lt k hlong) hsize) hlong hkm hcf
    · intro hno hne
      exact hH (fun ⟨k, _, hlong, hkm, hcf⟩ =>
        hno ⟨k, hlong_lt k hlong, hlong, hkm, hcf⟩) hne
  termination_by lengths.size - start
  decreasing_by all_goals omega

/-- `nextCodesFast` on the fast histogram is the spec `nextCodes` mapped to
    `UInt32` (local copy of the `hnext` step in `buildTableCanonicalFast_eq`). -/
theorem nextCodesFast_eq (lengths : Array UInt8) (maxBits : Nat) :
    nextCodesFast (countLengthsFast lengths maxBits) maxBits
      = (Huffman.Spec.nextCodes
          (Huffman.Spec.countLengths (lengths.toList.map UInt8.toNat) maxBits) maxBits).map
          (·.toUInt32) := by
  have hinit : (Array.replicate (maxBits + 1) (0 : UInt32))
      = (Array.replicate (maxBits + 1) (0 : Nat)).map (·.toUInt32) := by
    rw [Array.map_replicate]; rfl
  rw [countLengthsFast_eq, nextCodesFast, Huffman.Spec.nextCodes, hinit]
  exact nextCodesFast_go_eq _ maxBits (maxBits + 1) 1 0 (Array.replicate (maxBits + 1) 0)
    (by omega)

/-- The `start = 0` instantiation of `buildSubLoop_spec` over `buildLongDecode`'s
    subtables: the initial invariants are all vacuous or immediate. -/
theorem buildLongDecode_sub_spec (lengths : Array UInt8) (maxBits : Nat)
    (hmb15 : maxBits ≤ 15)
    (hv : Huffman.Spec.ValidLengths (lengths.toList.map UInt8.toNat) maxBits)
    (hbound : lengths.size ≤ UInt16.size) (buf : UInt64) :
    (∀ k, k < lengths.size → fastBits < lengths[k]!.toNat → lengths[k]!.toNat ≤ maxBits →
      Huffman.Spec.codeFor (lengths.toList.map UInt8.toNat) maxBits k
          = some (cwOf buf.toNat lengths[k]!.toNat) →
      (buildLongDecode lengths maxBits).rootSub[subPrefix buf]! ≠ 0 ∧
        subSlot (buildLongDecode lengths maxBits) maxBits buf = packEntry k.toUInt16 lengths[k]!) ∧
    ((¬ ∃ k, k < lengths.size ∧ fastBits < lengths[k]!.toNat ∧ lengths[k]!.toNat ≤ maxBits ∧
        Huffman.Spec.codeFor (lengths.toList.map UInt8.toNat) maxBits k
          = some (cwOf buf.toNat lengths[k]!.toNat)) →
      (buildLongDecode lengths maxBits).rootSub[subPrefix buf]! ≠ 0 →
        subSlot (buildLongDecode lengths maxBits) maxBits buf = packEntry 0 0) := by
  -- initial invariants (all vacuous or immediate) applied to `buildSubLoop … 0 …`
  have hncsz : (nextCodesFast (countLengthsFast lengths maxBits) maxBits).size = maxBits + 1 := by
    rw [nextCodesFast_eq, Array.size_map, Huffman.Spec.nextCodes_size]
  have hrootsz : (Array.replicate (2 ^ fastBits) (0 : UInt32)).size = 2 ^ fastBits :=
    Array.size_replicate
  have hsubsz : (Array.replicate
        (2 ^ (maxBits - fastBits) * countLongCodes (countLengthsFast lengths maxBits) maxBits)
        (packEntry 0 0)).size
      = 2 ^ (maxBits - fastBits) * countLongCodes (countLengthsFast lengths maxBits) maxBits :=
    Array.size_replicate
  have hnc0 : ∀ b, 1 ≤ b → b ≤ maxBits →
      (nextCodesFast (countLengthsFast lengths maxBits) maxBits)[b]!.toNat
        = (Huffman.Spec.nextCodes
            (Huffman.Spec.countLengths (lengths.toList.map UInt8.toNat) maxBits) maxBits)[b]!
          + numEarlier (lengths.toList.map UInt8.toNat) b 0 := by
    intro b hb1 hbm
    rw [nextCodesFast_eq, show numEarlier (lengths.toList.map UInt8.toNat) b 0 = 0 from by
      simp [numEarlier], Nat.add_zero]
    exact canon_initial_nc_invariant lengths maxBits (by omega) hv b hb1 hbm
  have hzero_root : ∀ q, q < 2 ^ fastBits → (Array.replicate (2 ^ fastBits) (0 : UInt32))[q]! = 0 := by
    intro q hq
    rw [getElem!_pos _ q (by rw [Array.size_replicate]; exact hq), Array.getElem_replicate]
  have hzero_subs : ∀ i, i < (Array.replicate
        (2 ^ (maxBits - fastBits) * countLongCodes (countLengthsFast lengths maxBits) maxBits)
        (packEntry 0 0)).size →
      (Array.replicate
        (2 ^ (maxBits - fastBits) * countLongCodes (countLengthsFast lengths maxBits) maxBits)
        (packEntry 0 0))[i]! = packEntry 0 0 := by
    intro i hi
    rw [getElem!_pos _ i hi, Array.getElem_replicate]
  have hpair : buildSubLoop lengths (nextCodesFast (countLengthsFast lengths maxBits) maxBits)
        maxBits 0 (Array.replicate (2 ^ fastBits) 0)
        (Array.replicate
          (2 ^ (maxBits - fastBits) * countLongCodes (countLengthsFast lengths maxBits) maxBits)
          (packEntry 0 0)) 0
      = ((buildLongDecode lengths maxBits).rootSub, (buildLongDecode lengths maxBits).subs) := rfl
  have hspec := buildSubLoop_spec lengths maxBits hmb15 hv hbound buf
    (nextCodesFast (countLengthsFast lengths maxBits) maxBits)
    (Array.replicate (2 ^ fastBits) 0)
    (Array.replicate
      (2 ^ (maxBits - fastBits) * countLongCodes (countLengthsFast lengths maxBits) maxBits)
      (packEntry 0 0)) 0 0
    (Nat.zero_le _) hncsz hrootsz hsubsz hnc0 (Nat.zero_le _)
    (fun q hq hne => absurd (hzero_root q hq) hne)
    (fun q1 q2 hq1 _ hne1 _ _ => absurd (hzero_root q1 hq1) hne1)
    (fun i _ hi => hzero_subs i hi)
    (fun k hk _ _ _ => absurd hk (by omega))
    (fun _ hne => absurd (hzero_root (subPrefix buf) (subPrefix_lt buf)) hne)
    _ _ hpair
  obtain ⟨hfill, hsent⟩ := hspec
  constructor
  · intro k hk hlong hkm hcf
    obtain ⟨hne, hslot⟩ := hfill k hk hlong hkm hcf
    rw [subSlot]
    exact ⟨hne, hslot⟩
  · intro hno hne
    rw [subSlot]
    exact hsent hno hne

/-- **Subtable fill, completeness (`buildSubLoop` invariant, `←`).** If symbol `s`
    of length `L` (`fastBits < L ≤ maxBits`) has canonical codeword `cwOf buf L`,
    its `fastBits`-bit prefix owns a subtable block (`rootSub ≠ 0`) and the slot the
    lookup indexes holds `packEntry s L`. -/
theorem subFill_complete (lengths : Array UInt8) (maxBits : Nat) (hmb15 : maxBits ≤ 15)
    (hv : Huffman.Spec.ValidLengths (lengths.toList.map UInt8.toNat) maxBits)
    (hbound : lengths.size ≤ UInt16.size)
    (s L : Nat) (hs : s < lengths.size) (hL : fastBits < L) (hLm : L ≤ maxBits)
    (hlen_s : lengths[s]!.toNat = L) (buf : UInt64)
    (hcf : Huffman.Spec.codeFor (lengths.toList.map UInt8.toNat) maxBits s
        = some (cwOf buf.toNat L)) :
    (buildLongDecode lengths maxBits).rootSub[subPrefix buf]! ≠ 0 ∧
      subSlot (buildLongDecode lengths maxBits) maxBits buf = packEntry s.toUInt16 L.toUInt8 := by
  obtain ⟨hfill, _⟩ := buildLongDecode_sub_spec lengths maxBits hmb15 hv hbound buf
  have hcf' : Huffman.Spec.codeFor (lengths.toList.map UInt8.toNat) maxBits s
      = some (cwOf buf.toNat lengths[s]!.toNat) := by rw [hlen_s]; exact hcf
  obtain ⟨hne, hslot⟩ := hfill s hs (by rw [hlen_s]; exact hL) (by rw [hlen_s]; exact hLm) hcf'
  refine ⟨hne, ?_⟩
  have hlenU : lengths[s]! = L.toUInt8 := by
    have hLtoNat : (L.toUInt8).toNat = L :=
      UInt8.toNat_ofNat_of_lt (Nat.lt_of_le_of_lt (show L ≤ 15 by omega) (by decide))
    exact UInt8.toNat_inj.mp (by rw [hLtoNat]; exact hlen_s)
  rw [hslot, hlenU]

/-- **Subtable fill, soundness (`buildSubLoop` invariant, `→`).** A non-sentinel
    sub-slot at the lookup index holds `packEntry s L` for a real symbol `s` of a
    long length `L` whose canonical codeword is `cwOf buf L`. -/
theorem subFill_sound (lengths : Array UInt8) (maxBits : Nat) (hmb15 : maxBits ≤ 15)
    (hv : Huffman.Spec.ValidLengths (lengths.toList.map UInt8.toNat) maxBits)
    (hbound : lengths.size ≤ UInt16.size) (buf : UInt64)
    (hroot : (buildLongDecode lengths maxBits).rootSub[subPrefix buf]! ≠ 0)
    (hlen0 : (unpackLen (subSlot (buildLongDecode lengths maxBits) maxBits buf)).toNat ≠ 0) :
    ∃ s, s < lengths.size ∧ fastBits < lengths[s]!.toNat ∧ lengths[s]!.toNat ≤ maxBits ∧
      Huffman.Spec.codeFor (lengths.toList.map UInt8.toNat) maxBits s
        = some (cwOf buf.toNat lengths[s]!.toNat) ∧
      subSlot (buildLongDecode lengths maxBits) maxBits buf
        = packEntry s.toUInt16 lengths[s]! := by
  obtain ⟨hfill, hsent⟩ := buildLongDecode_sub_spec lengths maxBits hmb15 hv hbound buf
  by_cases hex : ∃ k, k < lengths.size ∧ fastBits < lengths[k]!.toNat ∧ lengths[k]!.toNat ≤ maxBits ∧
      Huffman.Spec.codeFor (lengths.toList.map UInt8.toNat) maxBits k
        = some (cwOf buf.toNat lengths[k]!.toNat)
  · obtain ⟨k, hk, hlong, hkm, hcf⟩ := hex
    obtain ⟨_, hslot⟩ := hfill k hk hlong hkm hcf
    exact ⟨k, hk, hlong, hkm, hcf, hslot⟩
  · exact absurd (by rw [hsent hex hroot, unpackLen_packEntry]; rfl) hlen0

/-- `subLookup` never increases the bit count (it only consumes `len ≤ cnt` bits). -/
theorem subLookup_cnt_le (ld : LongDecode) (maxBits : Nat) (buf : UInt64) (cnt : Nat)
    {sym : UInt16} {bb : UInt64} {c used : Nat}
    (h : subLookup ld maxBits buf cnt = .ok (sym, bb, c, used)) : c ≤ cnt := by
  simp only [subLookup] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h; omega

/-- **`subLookup` on a filled slot.** When the prefix owns a subtable block
    (`rootSub ≠ 0`) and the indexed slot holds `packEntry sq L` for a length
    `0 < L < 256` fitting the buffer (`L ≤ cnt`), `subLookup` returns that symbol.
    Isolates the two-masked-load evaluation so the accept-set proof needs no manual
    `if` juggling. -/
theorem subLookup_eval (ld : LongDecode) (maxBits : Nat) (buf : UInt64) (cnt : Nat)
    (sq L : Nat) (hL256 : L < 256) (hL0 : 0 < L) (hLc : L ≤ cnt)
    (hne : ld.rootSub[subPrefix buf]! ≠ 0)
    (hslot : subSlot ld maxBits buf = packEntry sq.toUInt16 L.toUInt8) :
    subLookup ld maxBits buf cnt = .ok (sq.toUInt16, buf >>> L.toUInt64, cnt - L, L) := by
  have hsub : ld.subs[(ld.rootSub[(buf &&& 0x7FF).toNat]!.toNat - 1)
      + ((buf >>> (fastBits : Nat).toUInt64)
          &&& (2 ^ (maxBits - fastBits) - 1 : Nat).toUInt64).toNat]!
      = subSlot ld maxBits buf := rfl
  have hlenNat : (L.toUInt8).toNat = L := UInt8.toNat_ofNat_of_lt (by omega)
  simp only [subLookup, hsub, hslot, unpackLen_packEntry, unpackSym_packEntry, hlenNat]
  rw [if_neg (by simpa only [beq_iff_eq] using (show ld.rootSub[(buf &&& 0x7FF).toNat]! ≠ 0 from hne)),
      if_neg (by simp only [beq_iff_eq]; omega), if_neg (by omega)]

/-- **A matched codeword is long when the root table misses.** If `walkCanonical`
    matches at length `used` but the fast table reports the sentinel (`0`) or too
    few bits for this window, the codeword must be longer than `fastBits` — else the
    fast table would resolve it at length `used ≤ cnt`. (Mirror of
    `walkCanonical_dead_of_no_long`'s length argument.) -/
theorem long_of_guard (lengths : Array UInt8) (maxBits : Nat) (hmb15 : maxBits ≤ 15)
    (hv : Huffman.Spec.ValidLengths (lengths.toList.map UInt8.toNat) maxBits)
    (buf : UInt64) (cnt : Nat) (s used : Nat)
    (hs : s < lengths.size) (h1u : 1 ≤ used) (hucnt : used ≤ cnt)
    (hcf : Huffman.Spec.codeFor (lengths.toList.map UInt8.toNat) maxBits s
        = some (cwOf buf.toNat used))
    (hg : ((fromLengthsTree lengths maxBits).buildTable.lenAt (buf &&& 0x7FF).toNat).toNat = 0
        ∨ ((fromLengthsTree lengths maxBits).buildTable.lenAt (buf &&& 0x7FF).toNat).toNat > cnt) :
    fastBits < used := by
  rcases Nat.lt_or_ge fastBits used with h | hle
  · exact h
  · exfalso
    have hle11 : used ≤ 11 := hle
    have hmem : (s, cwOf buf.toNat used)
        ∈ Huffman.Spec.allCodes (lengths.toList.map UInt8.toNat) maxBits :=
      (Huffman.Spec.allCodes_mem_iff _ maxBits s _).mpr
        ⟨by rw [List.length_map, Array.length_toList]; exact hs, hcf⟩
    have hleaf : Deflate.Correctness.TreeHasLeaf (fromLengthsTree lengths maxBits)
        (cwOf buf.toNat used) s.toUInt16 :=
      Deflate.Correctness.fromLengths_hasLeaf lengths maxBits (by omega) _
        (fromLengths_ok_of_valid lengths maxBits hv) hv s _ hmem
    have hand : (buf &&& 0x7FF).toNat = buf.toNat % 2 ^ 11 := by
      rw [UInt64.toNat_and, show (0x7FF : UInt64).toNat = 2 ^ 11 - 1 from rfl,
          Nat.and_two_pow_sub_one_eq_mod]
    have hcweq : cwOf buf.toNat used = cwOf (buf &&& 0x7FF).toNat used := by
      rw [hand, ← cwOf_mod buf.toNat used, ← cwOf_mod (buf.toNat % 2 ^ 11) used,
          Nat.mod_mod_of_dvd buf.toNat (Nat.pow_dvd_pow 2 hle11)]
    rw [hcweq] at hleaf
    have hge : tableEntry.go (fromLengthsTree lengths maxBits) (buf &&& 0x7FF).toNat 0
        = (s.toUInt16, (0 + used).toUInt8) :=
      tableEntry_go_of_hasLeaf (fromLengthsTree lengths maxBits) (buf &&& 0x7FF).toNat 0 used
        s.toUInt16 hleaf (by simpa using hle11)
    have hlenAt : ((fromLengthsTree lengths maxBits).buildTable.lenAt
        (buf &&& 0x7FF).toNat).toNat = used := by
      rw [buildTable_lenAt _ _ (InflateBuf.buf_idx_lt buf), tableEntry, hge]
      simp only [Nat.zero_add, Nat.toUInt8, UInt8.ofNat, UInt8.toNat, BitVec.toNat_ofNat,
        Nat.reducePow]
      omega
    rw [hlenAt] at hg
    omega

/-- **`subLookup` matches `walkCanonical` when the fast table misses.** In the
    fallback context (the root table reports sentinel / too-few-bits, `hg`), the
    subtable lookup and the boxed scan succeed on exactly the same inputs with the
    same result: the fill lemmas place / recover the codeword the `walkCanonical`
    spec reads. -/
theorem subLookup_ok_iff_walkCanonical (lengths : Array UInt8) (maxBits : Nat)
    (hmb : 1 ≤ maxBits) (hmb15 : maxBits ≤ 15)
    (hv : Huffman.Spec.ValidLengths (lengths.toList.map UInt8.toNat) maxBits)
    (hbound : lengths.size ≤ UInt16.size)
    (buf : UInt64) (cnt : Nat) (r : UInt16 × UInt64 × Nat × Nat)
    (hg : ((fromLengthsTree lengths maxBits).buildTable.lenAt (buf &&& 0x7FF).toNat).toNat = 0
        ∨ ((fromLengthsTree lengths maxBits).buildTable.lenAt (buf &&& 0x7FF).toNat).toNat > cnt) :
    subLookup (buildLongDecode lengths maxBits) maxBits buf cnt = .ok r ↔
      walkCanonical (buildLongDecode lengths maxBits) maxBits buf cnt = .ok r := by
  obtain ⟨sym, bb, c, used⟩ := r
  have hread : (buildLongDecode lengths maxBits).subs[
        ((buildLongDecode lengths maxBits).rootSub[(buf &&& 0x7FF).toNat]!.toNat - 1)
          + ((buf >>> (fastBits : Nat).toUInt64)
              &&& (2 ^ (maxBits - fastBits) - 1 : Nat).toUInt64).toNat]!
      = subSlot (buildLongDecode lengths maxBits) maxBits buf := rfl
  have hroot_eq : (buildLongDecode lengths maxBits).rootSub[(buf &&& 0x7FF).toNat]!
      = (buildLongDecode lengths maxBits).rootSub[subPrefix buf]! := rfl
  constructor
  · -- subLookup ok → the sub-slot holds a real long codeword → walkCanonical ok
    intro h
    simp only [subLookup] at h
    split at h
    · exact absurd h (by simp)
    · rename_i hseen
      split at h
      · exact absurd h (by simp)
      · rename_i hlen0
        split at h
        · exact absurd h (by simp)
        · rename_i hlencnt
          have hrootne : (buildLongDecode lengths maxBits).rootSub[subPrefix buf]! ≠ 0 := by
            simpa only [beq_iff_eq] using hseen
          have hlen0' : (unpackLen (subSlot (buildLongDecode lengths maxBits) maxBits buf)).toNat
              ≠ 0 := by simpa only [beq_iff_eq] using hlen0
          obtain ⟨sq, hsq, hlongq, hqmax, hcfq, hslot⟩ :=
            subFill_sound lengths maxBits hmb15 hv hbound buf hrootne hlen0'
          -- fold the raw slot read to `packEntry sq lengths[sq]!` (`hread` is `rfl`)
          have hfold := hread.trans hslot
          rw [hfold, unpackLen_packEntry] at hlencnt
          have hcnt' : lengths[sq]!.toNat ≤ cnt := Nat.le_of_not_lt hlencnt
          simp only [hfold, unpackSym_packEntry, unpackLen_packEntry,
            Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨hsym, hbb, hc, hused⟩ := h
          have hL1 : 1 ≤ lengths[sq]!.toNat := by omega
          have hwc := walkCanonical_complete lengths maxBits hmb (by omega) hv sq lengths[sq]!.toNat
            hL1 hqmax buf cnt hcnt' hcfq
          rw [hwc, hsym, hbb, hc, hused]
  · -- walkCanonical ok → a real long codeword is present → the fill placed it → subLookup ok
    intro h
    obtain ⟨h1u, humax, hucnt, hbb, hc, sq, hsq, hsymq, hlen_sq, hcf⟩ :=
      walkCanonical_ok_spec lengths maxBits hmb (by omega) buf cnt sym bb c used h
    have hlong : fastBits < used :=
      long_of_guard lengths maxBits hmb15 hv buf cnt sq used hsq h1u hucnt
        (hlen_sq ▸ hcf) hg
    obtain ⟨hrootne, hslot⟩ :=
      subFill_complete lengths maxBits hmb15 hv hbound sq used hsq hlong humax hlen_sq buf
        (hlen_sq ▸ hcf)
    have heval := subLookup_eval (buildLongDecode lengths maxBits) maxBits buf cnt sq used
      (by omega) (by omega) hucnt hrootne hslot
    rw [heval, ← hsymq, ← hbb, ← hc]

/-- **`decodeSymCanon` and `decodeSym` accept the same inputs.** They share the
    11-bit table branch verbatim; the long-code fallback (`subLookup` vs the tree
    walk) agrees by `subLookup_ok_iff_walkCanonical` composed with
    `walkCanonical_ok_iff_walkTree`. The table is fixed to the verified tree table:
    `subLookup` only resolves >`fastBits` codes, so the equivalence needs the fast
    table to be the *correct* one (the guard then implies any matched code is long).
    All callers pass the tree table. -/
theorem decodeSymCanon_ok_iff_decodeSym (lengths : Array UInt8) (maxBits : Nat)
    (hmb : 1 ≤ maxBits) (hmb15 : maxBits ≤ 15)
    (hv : Huffman.Spec.ValidLengths (lengths.toList.map UInt8.toNat) maxBits)
    (hbound : lengths.size ≤ UInt16.size)
    (buf : UInt64) (cnt : Nat) (r : UInt16 × UInt64 × Nat × Nat) :
    decodeSymCanon (buildLongDecode lengths maxBits) (fromLengthsTree lengths maxBits).buildTable
        maxBits buf cnt = .ok r ↔
      decodeSym (fromLengthsTree lengths maxBits) (fromLengthsTree lengths maxBits).buildTable
        buf cnt = .ok r := by
  simp only [decodeSymCanon, decodeSym, DecodeTable.lenAt_eq_unpackLen_entryAt,
    DecodeTable.symAt_eq_unpackSym_entryAt]
  split
  · rename_i hguard
    simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq,
      ← DecodeTable.lenAt_eq_unpackLen_entryAt] at hguard
    rw [subLookup_ok_iff_walkCanonical lengths maxBits hmb hmb15 hv hbound buf cnt r hguard]
    exact walkCanonical_ok_iff_walkTree lengths maxBits hmb hmb15 hv hbound buf cnt r
  · exact Iff.rfl

/-! ## Skipping the long-code build when no code exceeds the fast table

`buildLongDecodeWithCount` shares one `countLengthsFast` pass with the table build
and, when `hasLongCode` is false (no codeword longer than `fastBits`), skips the
`buildSymbols` counting sort, returning an empty `symbols` array. The decoder still
correctly matches the verified reference: with no long codeword the `walkCanonical`
fallback is *dead* — every codeword resolves in the fast table — so the (empty)
`symbols` array is never read. -/

/-- `buildTableCanonicalFastWithCount` fed its own histogram is `buildTableCanonicalFast`. -/
theorem buildTableCanonicalFastWithCount_eq (lengths : Array UInt8) (maxBits : Nat) :
    buildTableCanonicalFastWithCount lengths (countLengthsFast lengths maxBits) maxBits
      = buildTableCanonicalFast lengths maxBits := rfl

/-- The `count` field of `buildLongDecodeWithCount` is the histogram it was given. -/
theorem buildLongDecodeWithCount_count (lengths : Array UInt8) (count : Array Nat) (maxBits : Nat) :
    (buildLongDecodeWithCount lengths count maxBits).count = count := by
  unfold buildLongDecodeWithCount; split <;> rfl

/-- The `firstCode` field of `buildLongDecodeWithCount` is `nextCodes` of the histogram. -/
theorem buildLongDecodeWithCount_firstCode (lengths : Array UInt8) (count : Array Nat)
    (maxBits : Nat) :
    (buildLongDecodeWithCount lengths count maxBits).firstCode
      = Huffman.Spec.nextCodes count maxBits := by
  unfold buildLongDecodeWithCount; split <;> rfl

/-- When some codeword exceeds the fast table, `buildLongDecodeWithCount` (sharing the
    histogram) builds the full structures — exactly `buildLongDecode`. -/
theorem buildLongDecodeWithCount_eq (lengths : Array UInt8) (maxBits : Nat)
    (h : hasLongCode (countLengthsFast lengths maxBits) maxBits = true) :
    buildLongDecodeWithCount lengths (countLengthsFast lengths maxBits) maxBits
      = buildLongDecode lengths maxBits := by
  unfold buildLongDecodeWithCount buildLongDecode; rw [if_pos h]

/-- If a length `len ≤ maxBits` has a positive count, the `hasLongCode` scan from any
    `start ≤ len` reports `true`. -/
theorem hasLongCode_go_eq_true (count : Array Nat) (maxBits len : Nat)
    (hlm : len ≤ maxBits) (hpos : 0 < count[len]!) :
    ∀ start, start ≤ len → hasLongCode.go count maxBits start = true := by
  intro start hsl
  induction hk : (len - start) generalizing start with
  | zero =>
    have heq : start = len := by omega
    subst heq
    rw [hasLongCode.go, if_neg (by omega), if_pos hpos]
  | succ k ih =>
    rw [hasLongCode.go, if_neg (by omega : ¬ start > maxBits)]
    by_cases hs : 0 < count[start]!
    · rw [if_pos hs]
    · rw [if_neg hs]; exact ih (start + 1) (by omega) (by omega)

/-- A positive count at a length beyond `fastBits` makes `hasLongCode` true. -/
theorem hasLongCode_eq_true_of_pos (count : Array Nat) (maxBits len : Nat)
    (hfb : fastBits < len) (hlm : len ≤ maxBits) (hpos : 0 < count[len]!) :
    hasLongCode count maxBits = true :=
  hasLongCode_go_eq_true count maxBits len hlm hpos (fastBits + 1) (by omega)

/-- **`walkCanonical` success depends only on `count`/`firstCode`.** Two long-code
    structures agreeing on those fields succeed on exactly the same inputs (the
    branch test reads only them; the symbol returned reads `symbols`/`firstIndex`). -/
theorem walkCanonical_go_ok_of_count_eq (ld1 ld2 : LongDecode) (maxBits : Nat)
    (hc : ld1.count = ld2.count) (hfc : ld1.firstCode = ld2.firstCode) :
    ∀ (fuel len code : Nat) (buf : UInt64) (cnt : Nat) (r : UInt16 × UInt64 × Nat × Nat),
      maxBits + 1 - len ≤ fuel →
      walkCanonical.go ld1 maxBits len code buf cnt = .ok r →
      ∃ r', walkCanonical.go ld2 maxBits len code buf cnt = .ok r' := by
  intro fuel
  induction fuel with
  | zero =>
    intro len code buf cnt r hf h
    rw [walkCanonical.go, dif_pos (by omega)] at h; exact absurd h (by simp)
  | succ fuel ih =>
    intro len code buf cnt r hf h
    rw [walkCanonical.go] at h ⊢
    by_cases hlen : len > maxBits
    · rw [dif_pos hlen] at h; exact absurd h (by simp)
    · rw [dif_neg hlen] at h ⊢
      by_cases hcnt : cnt = 0
      · rw [if_pos hcnt] at h; exact absurd h (by simp)
      · rw [if_neg hcnt] at h ⊢
        simp only [] at h ⊢
        rw [← hc, ← hfc]
        by_cases hcond : ld1.firstCode[len]! ≤ code * 2 + (buf &&& 1).toNat
            ∧ code * 2 + (buf &&& 1).toNat < ld1.firstCode[len]! + ld1.count[len]!
        · rw [if_pos hcond]; exact ⟨_, rfl⟩
        · rw [if_neg hcond] at h ⊢
          exact ih (len + 1) (code * 2 + (buf &&& 1).toNat) (buf >>> 1) (cnt - 1) r (by omega) h

/-- `walkCanonical` success depends only on `count`/`firstCode` (wrapper). -/
theorem walkCanonical_ok_of_count_eq (ld1 ld2 : LongDecode) (maxBits : Nat)
    (hc : ld1.count = ld2.count) (hfc : ld1.firstCode = ld2.firstCode)
    (buf : UInt64) (cnt : Nat) {r : UInt16 × UInt64 × Nat × Nat}
    (h : walkCanonical ld1 maxBits buf cnt = .ok r) :
    ∃ r', walkCanonical ld2 maxBits buf cnt = .ok r' :=
  walkCanonical_go_ok_of_count_eq ld1 ld2 maxBits hc hfc (maxBits + 1) 1 0 buf cnt r (by omega) h

/-- **The long-code fallback is dead when no codeword exceeds the fast table.** With
    `hasLongCode = false` every codeword has length `≤ fastBits`, so the fast table
    holds it; when the table misses (length `0`) or has too few buffered bits, no
    codeword can be spelled, so `walkCanonical` over the full long-code structures
    fails. (The fast table's length at the buffer index equals the codeword length,
    contradicting the fallback guard.) -/
theorem walkCanonical_dead_of_no_long (lengths : Array UInt8)
    (hv : Huffman.Spec.ValidLengths (lengths.toList.map UInt8.toNat) 15)
    (hlong : hasLongCode (countLengthsFast lengths 15) 15 = false)
    (buf : UInt64) (cnt : Nat)
    (hg : ((fromLengthsTree lengths 15).buildTable.lenAt (buf &&& 0x7FF).toNat).toNat = 0
        ∨ ((fromLengthsTree lengths 15).buildTable.lenAt (buf &&& 0x7FF).toNat).toNat > cnt)
    (r : UInt16 × UInt64 × Nat × Nat) :
    walkCanonical (buildLongDecode lengths 15) 15 buf cnt ≠ .ok r := by
  intro h
  obtain ⟨sym, bb, c, used⟩ := r
  obtain ⟨h1u, humax, hucnt, hbb, hc, s, hs, hsym, hlen_s, hcf⟩ :=
    walkCanonical_ok_spec lengths 15 (by omega) (by omega) buf cnt sym bb c used h
  -- `used` is some real symbol's length, so the histogram counts it
  have hcount_pos : 0 < (countLengthsFast lengths 15)[used]! := by
    rw [numEarlier_size_eq lengths 15 used h1u humax]
    exact Nat.lt_of_le_of_lt (Nat.zero_le _)
      (numEarlier_lt_arr lengths s lengths.size used hs hlen_s hs (Nat.le_refl _))
  -- ¬hasLong ⇒ no codeword beyond the fast window, so `used ≤ fastBits`
  have hufast : used ≤ fastBits := by
    rcases Nat.lt_or_ge fastBits used with h | h
    · exfalso
      have := hasLongCode_eq_true_of_pos (countLengthsFast lengths 15) 15 used h humax hcount_pos
      rw [hlong] at this; exact absurd this (by simp)
    · exact h
  have hle11 : used ≤ 11 := hufast
  -- the tree has a leaf at this codeword
  have hmem : (s, cwOf buf.toNat used)
      ∈ Huffman.Spec.allCodes (lengths.toList.map UInt8.toNat) 15 :=
    (Huffman.Spec.allCodes_mem_iff _ 15 s _).mpr
      ⟨by rw [List.length_map, Array.length_toList]; exact hs, hcf⟩
  have hleaf : Deflate.Correctness.TreeHasLeaf (fromLengthsTree lengths 15)
      (cwOf buf.toNat used) s.toUInt16 :=
    Deflate.Correctness.fromLengths_hasLeaf lengths 15 (by omega) _
      (fromLengths_ok_of_valid lengths 15 hv) hv s _ hmem
  -- restrict the codeword to the low `fastBits` bits the table indexes
  have hand : (buf &&& 0x7FF).toNat = buf.toNat % 2 ^ 11 := by
    rw [UInt64.toNat_and, show (0x7FF : UInt64).toNat = 2 ^ 11 - 1 from rfl,
        Nat.and_two_pow_sub_one_eq_mod]
  have hcweq : cwOf buf.toNat used = cwOf (buf &&& 0x7FF).toNat used := by
    rw [hand, ← cwOf_mod buf.toNat used, ← cwOf_mod (buf.toNat % 2 ^ 11) used,
        Nat.mod_mod_of_dvd buf.toNat (Nat.pow_dvd_pow 2 hle11)]
  rw [hcweq, ← hsym] at hleaf
  -- the fast table reads exactly this length
  have hge : tableEntry.go (fromLengthsTree lengths 15) (buf &&& 0x7FF).toNat 0
      = (sym, (0 + used).toUInt8) :=
    tableEntry_go_of_hasLeaf (fromLengthsTree lengths 15) (buf &&& 0x7FF).toNat 0 used sym
      hleaf (by simpa using hufast)
  have hlenAt : ((fromLengthsTree lengths 15).buildTable.lenAt (buf &&& 0x7FF).toNat).toNat = used := by
    rw [buildTable_lenAt _ _ (InflateBuf.buf_idx_lt buf), tableEntry, hge]
    simp only [Nat.zero_add, Nat.toUInt8, UInt8.ofNat, UInt8.toNat, BitVec.toNat_ofNat, Nat.reducePow]
    omega
  rw [hlenAt] at hg
  omega

/-- **`decodeSymCanon` over `buildLongDecodeWithCount` agrees with `decodeSym`.** The
    histogram-sharing, `buildSymbols`-skipping long-code build still drives the
    tree-free symbol decode to the same accept-set as the verified tree decode. When
    a long code exists it is `buildLongDecode` (`decodeSymCanon_ok_iff_decodeSym`);
    when none does, both fall back into a dead path that always fails. -/
theorem decodeSymCanon_withCount_ok_iff_decodeSym (lengths : Array UInt8)
    (hv : Huffman.Spec.ValidLengths (lengths.toList.map UInt8.toNat) 15)
    (hbound : lengths.size ≤ UInt16.size)
    (buf : UInt64) (cnt : Nat) (r : UInt16 × UInt64 × Nat × Nat) :
    decodeSymCanon (buildLongDecodeWithCount lengths (countLengthsFast lengths 15) 15)
        (fromLengthsTree lengths 15).buildTable 15 buf cnt = .ok r ↔
      decodeSym (fromLengthsTree lengths 15) (fromLengthsTree lengths 15).buildTable buf cnt
        = .ok r := by
  by_cases hlong : hasLongCode (countLengthsFast lengths 15) 15
  · rw [buildLongDecodeWithCount_eq lengths 15 hlong]
    exact decodeSymCanon_ok_iff_decodeSym lengths 15 (by omega) (by omega) hv hbound buf cnt r
  · simp only [Bool.not_eq_true] at hlong
    have hrs : (buildLongDecodeWithCount lengths (countLengthsFast lengths 15) 15).rootSub = #[] := by
      unfold buildLongDecodeWithCount; rw [if_neg (by rw [hlong]; simp)]
    simp only [decodeSymCanon, decodeSym, DecodeTable.lenAt_eq_unpackLen_entryAt,
      DecodeTable.symAt_eq_unpackSym_entryAt]
    split
    · rename_i hguard
      simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq,
        ← DecodeTable.lenAt_eq_unpackLen_entryAt] at hguard
      constructor
      · intro h
        -- with no long code the subtable is empty (`rootSub = #[]`), so `subLookup`
        -- always errors: `#[][p]! = 0`, hitting the "invalid code" arm
        have herr : subLookup (buildLongDecodeWithCount lengths (countLengthsFast lengths 15) 15)
            15 buf cnt = .error "Inflate: invalid Huffman code" := by
          simp only [subLookup, hrs]
          rw [getElem!_neg _ ((buf &&& 0x7FF).toNat) (by simp)]
          rfl
        rw [herr] at h; exact absurd h (by simp)
      · intro h
        exact absurd ((walkCanonical_ok_iff_walkTree lengths 15 (by omega) (by omega) hv hbound
            buf cnt r).mpr h)
          (walkCanonical_dead_of_no_long lengths hv hlong buf cnt hguard r)
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
  · exact subLookup_cnt_le ld maxBits buf cnt h
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
  buildTableCanonicalFast buildTableCanonicalFast_eq_buildTable
  buildLongDecodeWithCount buildTableCanonicalFastWithCount buildTableCanonicalFastWithCount_eq
  decodeSymCanon_withCount_ok_iff_decodeSym countLengthsFast)

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
    (litLD distLD : HuffTree.LongDecode)
    (hlit_iff : ∀ (b : UInt64) (n : Nat) (x : UInt16 × UInt64 × Nat × Nat),
      decodeSymCanon litLD litTable 15 b n = .ok x
        ↔ decodeSym (fromLengthsTree litLengths 15) litTable b n = .ok x)
    (hdist_iff : ∀ (b : UInt64) (n : Nat) (x : UInt16 × UInt64 × Nat × Nat),
      decodeSymCanon distLD distTable 15 b n = .ok x
        ↔ decodeSym (fromLengthsTree distLengths 15) distTable b n = .ok x)
    (data : ByteArray) (maxOut : Nat) (pos : Nat) (bitBuf : UInt64) (cnt : Nat)
    (output : ByteArray) (r : ByteArray × Nat × UInt64 × Nat) :
    goTreeFree litTable distTable litLD distLD
        15 data maxOut pos bitBuf cnt output = .ok r ↔
      goFusedP litTable distTable data (fromLengthsTree litLengths 15) (fromLengthsTree distLengths 15)
        maxOut pos bitBuf cnt output = .ok r := by
  rw [goTreeFree, goFusedP]
  by_cases hrc : cnt ≤ 56 ∧ pos < data.size
  · -- `goFusedP`'s refill now reads `data[pos]'hrc.2`; normalise to `!` to match
    -- `goTreeFree`'s (unchanged) `data[pos]!` refill read
    rw [dif_pos hrc, dif_pos hrc, ← getElem!_pos data pos hrc.2]
    exact goTreeFree_ok_iff_goFusedP litTable distTable litLengths distLengths litLD distLD hlit_iff hdist_iff
      data maxOut (pos + 1) (bitBuf ||| (data[pos]!.toUInt64 <<< cnt.toUInt64)) (cnt + 8) output r
  · rw [dif_neg hrc, dif_neg hrc]
    by_cases hlit : (litTable.lenAt (bitBuf &&& 0x7FF).toNat).toNat ≠ 0
        ∧ (litTable.lenAt (bitBuf &&& 0x7FF).toNat).toNat ≤ cnt
        ∧ litTable.symAt (bitBuf &&& 0x7FF).toNat < 256
    · rw [dif_pos hlit, dif_pos hlit]
      by_cases hout : output.size ≥ maxOut
      · simp [hout]
      · rw [if_neg hout, if_neg hout]
        exact goTreeFree_ok_iff_goFusedP litTable distTable litLengths distLengths litLD distLD hlit_iff hdist_iff
          data maxOut pos (bitBuf >>> ((litTable.lenAt (bitBuf &&& 0x7FF).toNat).toNat).toUInt64)
          (cnt - (litTable.lenAt (bitBuf &&& 0x7FF).toNat).toNat)
          (output.push (litTable.symAt (bitBuf &&& 0x7FF).toNat).toUInt8) r
    · rw [dif_neg hlit, dif_neg hlit]
      -- literal/length symbol decode
      cases hdec : decodeSymCanon litLD litTable 15 bitBuf cnt with
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
              exact goTreeFree_ok_iff_goFusedP litTable distTable litLengths distLengths litLD distLD hlit_iff hdist_iff
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
                cases hdec3 : decodeSymCanon distLD distTable 15 bb2 c2 with
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
                              exact goTreeFree_ok_iff_goFusedP litTable distTable litLengths distLengths litLD distLD
                                hlit_iff hdist_iff data maxOut pos bb4 c4 _ r
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
    (hsz : data.size < USize.size)
    (hlp : litTable.packed.size = 2 ^ HuffTree.fastBits) :
    ∀ (pos : USize) (bitBuf : UInt64) (cnt : USize) (output : ByteArray),
    pos.toNat ≤ data.size →
    Except.map (fun x => (x.1, x.2.1.toNat, x.2.2.1, x.2.2.2.toNat))
        (goTreeFreeU litTable distTable litLD distLD maxBits data maxOut pos bitBuf cnt hsz hlp output)
      = goTreeFree litTable distTable litLD distLD maxBits data maxOut pos.toNat bitBuf cnt.toNat output := by
  intro pos bitBuf cnt output
  induction pos, bitBuf, cnt, output using goTreeFreeU.induct
    (litTable := litTable) (litLD := litLD)
    (maxBits := maxBits) (data := data) (maxOut := maxOut) (hsz := hsz) (hlp := hlp) with
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
  | case2 pos bitBuf cnt output hrc ent hlit hmax =>
      intro hpos
      rw [goTreeFreeU, dif_neg hrc, dif_pos hlit, if_pos hmax,
          goTreeFree, dif_neg (fun h => hrc ((refillGuard_usize data pos cnt hsz).mpr h)),
          dif_pos ((litGuardU_usize litTable bitBuf cnt _).mp hlit), if_pos hmax]
      rfl
  | case3 pos bitBuf cnt output hrc ent hlit hmax ih =>
      intro hpos
      obtain ⟨hl0, hl1, hl2⟩ := hlit
      have hle : litTable.lenAt (bitBuf &&& 0x7FF).toNat = HuffTree.unpackLen ent := by
        rw [litTable.lenAt_eq_unpackLen_entryAt]; congr 1
        exact (litTable.entryAtU_window_eq bitBuf _).symm
      have hse : litTable.symAt (bitBuf &&& 0x7FF).toNat = HuffTree.unpackSym ent := by
        rw [litTable.symAt_eq_unpackSym_entryAt]; congr 1
        exact (litTable.entryAtU_window_eq bitBuf _).symm
      have hsub : (cnt - (HuffTree.unpackLen ent).toUSize).toNat
          = cnt.toNat - (HuffTree.unpackLen ent).toNat := by
        rw [USize.toNat_sub_of_le _ _ hl1, UInt8.toNat_toUSize]
      rw [goTreeFreeU, dif_neg hrc, dif_pos ⟨hl0, hl1, hl2⟩, if_neg hmax,
          goTreeFree, dif_neg (fun h => hrc ((refillGuard_usize data pos cnt hsz).mpr h)),
          dif_pos ((litGuardU_usize litTable bitBuf cnt _).mp ⟨hl0, hl1, hl2⟩), if_neg hmax,
          ih hpos, hsub, hle, hse, uint8_toUInt64_toNat]
  | case4 pos bitBuf cnt output hrc ent hlit e hde =>
      intro hpos
      rw [goTreeFreeU, dif_neg hrc, dif_neg hlit,
          goTreeFree, dif_neg (fun h => hrc ((refillGuard_usize data pos cnt hsz).mpr h)),
          dif_neg (fun h => hlit ((litGuardU_usize litTable bitBuf cnt _).mpr h))]
      simp only [hde, Except.map]
  | case5 pos bitBuf cnt output hrc ent hlit sym bb c used hde hsym hmax =>
      intro hpos
      rw [goTreeFreeU, dif_neg hrc, dif_neg hlit,
          goTreeFree, dif_neg (fun h => hrc ((refillGuard_usize data pos cnt hsz).mpr h)),
          dif_neg (fun h => hlit ((litGuardU_usize litTable bitBuf cnt _).mpr h))]
      simp only [hde, if_pos hsym, if_pos hmax]
      rfl
  | case6 pos bitBuf cnt output hrc ent hlit cnt0 sym bb c used hde hsym hmax hnp =>
      intro hpos
      have hnp' : cnt.toNat ≤ c := hnp
      rw [goTreeFreeU, dif_neg hrc, dif_neg hlit,
          goTreeFree, dif_neg (fun h => hrc ((refillGuard_usize data pos cnt hsz).mpr h)),
          dif_neg (fun h => hlit ((litGuardU_usize litTable bitBuf cnt _).mpr h))]
      simp only [hde, if_pos hsym, if_neg hmax, dif_pos hnp']
      rfl
  | case7 pos bitBuf cnt output hrc ent hlit cnt0 sym bb c used hde hsym hmax hnp ih =>
      intro hpos
      have hnp' : ¬ cnt.toNat ≤ c := hnp
      have hcle : c ≤ cnt.toNat := HuffTree.decodeSymCanon_cnt_le litLD litTable maxBits bitBuf cnt.toNat hde
      have hcrt : c.toUSize.toNat = c :=
        toUSize_toNat_of_lt (Nat.lt_of_le_of_lt hcle cnt.toNat_lt_two_pow_numBits)
      rw [goTreeFreeU, dif_neg hrc, dif_neg hlit,
          goTreeFree, dif_neg (fun h => hrc ((refillGuard_usize data pos cnt hsz).mpr h)),
          dif_neg (fun h => hlit ((litGuardU_usize litTable bitBuf cnt _).mpr h))]
      simp only [hde, if_pos hsym, if_neg hmax, dif_neg hnp']
      rw [ih hpos, hcrt]
  | case8 pos bitBuf cnt output hrc ent hlit sym bb c used hde hsym heob =>
      intro hpos
      have hcle : c ≤ cnt.toNat := HuffTree.decodeSymCanon_cnt_le litLD litTable maxBits bitBuf cnt.toNat hde
      have hcrt : c.toUSize.toNat = c :=
        toUSize_toNat_of_lt (Nat.lt_of_le_of_lt hcle cnt.toNat_lt_two_pow_numBits)
      rw [goTreeFreeU, dif_neg hrc, dif_neg hlit,
          goTreeFree, dif_neg (fun h => hrc ((refillGuard_usize data pos cnt hsz).mpr h)),
          dif_neg (fun h => hlit ((litGuardU_usize litTable bitBuf cnt _).mpr h))]
      simp only [hde, if_neg hsym, if_pos heob, Except.map, hcrt]
  | case9 pos bitBuf cnt output hrc ent hlit sym bb c used hde hsym hneob idx hidx =>
      intro hpos
      have hidxc : sym.toNat - 257 ≥ Inflate.lengthBase.size := hidx
      rw [goTreeFreeU, dif_neg hrc, dif_neg hlit,
          goTreeFree, dif_neg (fun h => hrc ((refillGuard_usize data pos cnt hsz).mpr h)),
          dif_neg (fun h => hlit ((litGuardU_usize litTable bitBuf cnt _).mpr h))]
      simp only [hde, if_neg hsym, if_neg hneob, dif_pos hidxc]
      rfl
  | case10 pos bitBuf cnt output hrc ent hlit cnt0 sym bb c used hde hsym hneob idx hh base ih =>
      intro hpos
      have hhc : ¬ sym.toNat - 257 ≥ Inflate.lengthBase.size := hh
      rw [goTreeFreeU, dif_neg hrc, dif_neg hlit,
          goTreeFree, dif_neg (fun h => hrc ((refillGuard_usize data pos cnt hsz).mpr h)),
          dif_neg (fun h => hlit ((litGuardU_usize litTable bitBuf cnt _).mpr h))]
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
  have htlit : buildTableCanonicalFastWithCount litLengths (countLengthsFast litLengths 15) 15
      = (fromLengthsTree litLengths 15).buildTable :=
    buildTableCanonicalFast_eq_buildTable litLengths 15 (by omega) hlv hlb
  have htdist : buildTableCanonicalFastWithCount distLengths (countLengthsFast distLengths 15) 15
      = (fromLengthsTree distLengths 15).buildTable :=
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
  unfold decodeHuffmanFastBufTreeFree decodeHuffmanFastBufTables decodeHuffmanFastBuf
  rw [hrf]
  dsimp only []
  simp only [htlit, htdist]
  rw [goFusedPDispatch_eq (fromLengthsTree litLengths 15).buildTable
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
          (fromLengthsTree distLengths 15).buildTable br.data
          (buildLongDecodeWithCount litLengths (countLengthsFast litLengths 15) 15)
          (buildLongDecodeWithCount distLengths (countLengthsFast distLengths 15) 15) 15 maxOut hsz'
          (HuffTree.buildTable_size _)
          pos0.toUSize (bitBuf0 >>> br.bitOff.toUInt64) (cnt0 - br.bitOff).toUSize output
          (by rw [toUSize_toNat_of_lt (Nat.lt_of_le_of_lt hbc2.posLe hsz')]; exact hbc2.posLe),
        toUSize_toNat_of_lt (Nat.lt_of_le_of_lt hbc2.posLe hsz'), toUSize_toNat_of_lt hcsz]
    exact bind_ok_iff (fun x => goTreeFree_ok_iff_goFusedP (fromLengthsTree litLengths 15).buildTable
      (fromLengthsTree distLengths 15).buildTable litLengths distLengths
      (buildLongDecodeWithCount litLengths (countLengthsFast litLengths 15) 15)
      (buildLongDecodeWithCount distLengths (countLengthsFast distLengths 15) 15)
      (decodeSymCanon_withCount_ok_iff_decodeSym litLengths hlv hlb)
      (decodeSymCanon_withCount_ok_iff_decodeSym distLengths hdv hdb) br.data maxOut
      pos0 (bitBuf0 >>> br.bitOff.toUInt64) (cnt0 - br.bitOff) output x) _ r
  · exact bind_ok_iff (fun x => goTreeFree_ok_iff_goFusedP (fromLengthsTree litLengths 15).buildTable
      (fromLengthsTree distLengths 15).buildTable litLengths distLengths
      (buildLongDecodeWithCount litLengths (countLengthsFast litLengths 15) 15)
      (buildLongDecodeWithCount distLengths (countLengthsFast distLengths 15) 15)
      (decodeSymCanon_withCount_ok_iff_decodeSym litLengths hlv hlb)
      (decodeSymCanon_withCount_ok_iff_decodeSym distLengths hdv hdb) br.data maxOut
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

/-- The constant-table fixed-Huffman decode is the per-block build specialised to
    the fixed code lengths: `decodeHuffmanFastBufFixed` runs
    `decodeHuffmanFastBufTables` over the compile-time fixed tables, which are by
    definition the tables `decodeHuffmanFastBufTreeFree` builds from
    `fixedLitLengths`/`fixedDistLengths`. Definitionally equal, so every fixed-block
    correctness step goes through `decodeHuffmanFastBufTreeFree_ok_iff` unchanged. -/
theorem decodeHuffmanFastBufFixed_eq (br : BitReader) (output : ByteArray) (maxOut : Nat) :
    decodeHuffmanFastBufFixed br output maxOut
      = InflateBuf.decodeHuffmanFastBufTreeFree br output fixedLitLengths fixedDistLengths maxOut :=
  rfl

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
    simp [he1, he2, he3, he4, he5, he6,
      HuffTree.validateLengths_of_fromLengths hlitT,
      HuffTree.validateLengths_of_fromLengths hdistT,
      bind, Except.bind, pure, Except.pure]
  · rw [Array.size_extract]
    exact Nat.le_trans (Nat.le_trans (Nat.sub_le _ _) (Nat.min_le_left _ _))
      (Nat.le_trans (by omega : hlit.toNat + 257 ≤ 288) (by decide : 288 ≤ UInt16.size))
  · rw [Array.size_extract]
    exact Nat.le_trans (Nat.le_trans (Nat.sub_le _ _) (Nat.min_le_left _ _))
      (Nat.le_trans (by omega : hlit.toNat + 257 + (hdist.toNat + 1) ≤ 320)
        (by decide : 320 ≤ UInt16.size))

/-- **`decodeDynamicLengthsOnly` → `decodeDynamicTrees`.** The converse of
    `decodeDynamicTrees_extract`: once the tree-free length extractor's added
    `validateLengths` check passes, the lengths are `ValidLengths`, so
    `decodeDynamicTrees` rebuilds the canonical trees and succeeds with the same
    reader. This is exactly what closing the code-length validation gap buys. -/
theorem decodeDynamicTrees_of_lengthsOnly {br : BitReader} {litLens distLens : Array UInt8}
    {br' : BitReader}
    (h : decodeDynamicLengthsOnly br = .ok (litLens, distLens, br')) :
    decodeDynamicTrees br
        = .ok (HuffTree.fromLengthsTree litLens 15, HuffTree.fromLengthsTree distLens 15, br') ∧
      Huffman.Spec.ValidLengths (litLens.toList.map UInt8.toNat) 15 ∧
      Huffman.Spec.ValidLengths (distLens.toList.map UInt8.toNat) 15 ∧
      litLens.size ≤ UInt16.size ∧ distLens.size ≤ UInt16.size := by
  unfold decodeDynamicLengthsOnly at h
  obtain ⟨a1, he1, h⟩ := bindOk h; obtain ⟨hlit, br1⟩ := a1
  obtain ⟨a2, he2, h⟩ := bindOk h; obtain ⟨hdist, br2⟩ := a2
  obtain ⟨a3, he3, h⟩ := bindOk h; obtain ⟨hclen, br3⟩ := a3
  obtain ⟨a4, he4, h⟩ := bindOk h; obtain ⟨clLengths, br4⟩ := a4
  obtain ⟨a5, he5, h⟩ := bindOk h
  obtain ⟨a6, he6, h⟩ := bindOk h; obtain ⟨codeLengths, br6⟩ := a6
  obtain ⟨u1, hv1, h⟩ := bindOk h; cases u1
  obtain ⟨u2, hv2, h⟩ := bindOk h; cases u2
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  have hlitb : hlit.toNat < 32 := readBits_lt (n := 5) (by omega) he1
  have hdistb : hdist.toNat < 32 := readBits_lt (n := 5) (by omega) he2
  have hflt := (HuffTree.validateLengths_ok_iff_fromLengths _ 15).mp hv1
  have hfdt := (HuffTree.validateLengths_ok_iff_fromLengths _ 15).mp hv2
  refine ⟨?_, HuffTree.validateLengths_valid hv1, HuffTree.validateLengths_valid hv2, ?_, ?_⟩
  · unfold decodeDynamicTrees
    simp [he1, he2, he3, he4, he5, he6, hflt, hfdt, bind, Except.bind, pure, Except.pure]
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
      rw [decodeHuffmanFastBufFixed_eq, htf]; dsimp only [bind, Except.bind]
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

set_option maxRecDepth 4096 in
open InflateBuf in
/-- **Tree-free block loop backward.** With the code-length validation gap closed
    (`decodeDynamicLengthsOnly` now runs the same `validateLengths` check
    `decodeDynamicTrees` does), whenever the tree-free `inflateLoopTreeFree`
    succeeds, the verified `inflateLoop` (with the proof-only fixed trees) succeeds
    with the *same* result. Dynamic blocks rebuild via `decodeDynamicTrees_of_lengthsOnly`;
    the block correspondence `decodeHuffmanFastBufTreeFree_ok_iff` is already an `iff`.
    Together with `inflateLoopTreeFree_of_inflateLoop` this gives accept-set equality. -/
theorem inflateLoop_of_inflateLoopTreeFree (data : ByteArray)
    (hflv : Huffman.Spec.ValidLengths (fixedLitLengths.toList.map UInt8.toNat) 15)
    (hflb : fixedLitLengths.size ≤ UInt16.size)
    (hfdv : Huffman.Spec.ValidLengths (fixedDistLengths.toList.map UInt8.toNat) 15)
    (hfdb : fixedDistLengths.size ≤ UInt16.size) (maxOut : Nat) :
    ∀ (br : BitReader) (output : ByteArray),
      (br.bitOff = 0 ∨ br.pos < br.data.size) → br.pos ≤ br.data.size → br.data.size = data.size →
      ∀ r, inflateLoopTreeFree br output maxOut data.size = .ok r →
        inflateLoop br output (HuffTree.fromLengthsTree fixedLitLengths 15)
          (HuffTree.fromLengthsTree fixedDistLengths 15) maxOut data.size = .ok r := by
  intro br output
  induction br, output using inflateLoopTreeFree.induct (dataSize := data.size) with
  | _ br output ih =>
    intro hpos hple hds r h
    rw [inflateLoopTreeFree] at h
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
    have tailbwd : ∀ (o' : ByteArray) (br'' : BitReader),
        (br''.bitOff = 0 ∨ br''.pos < br''.data.size) → br''.pos ≤ br''.data.size →
        br''.data.size = data.size →
        (if bfinal == 1 then pure (o', br''.alignToByte.pos)
         else if _h : br''.bitPos ≤ br.bitPos then throw "Inflate: no progress in inflate loop"
              else if _h : data.size * 8 < br''.bitPos then throw "Inflate: bit position out of range"
              else inflateLoopTreeFree br'' o' maxOut data.size) = .ok r →
        (if bfinal == 1 then pure (o', br''.alignToByte.pos)
         else if _h : br''.bitPos ≤ br.bitPos then throw "Inflate: no progress in inflate loop"
              else if _h : data.size * 8 < br''.bitPos then throw "Inflate: bit position out of range"
              else inflateLoop br'' o' (HuffTree.fromLengthsTree fixedLitLengths 15)
                    (HuffTree.fromLengthsTree fixedDistLengths 15) maxOut data.size) = .ok r := by
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
    rw [inflateLoop]
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
      exact tailbwd output' br' hp' hl' (by rw [hd']; exact hdata₂) htail
    · -- fixed Huffman block
      obtain ⟨pb, hblock, htail⟩ := bindOk h; obtain ⟨output', br'⟩ := pb
      rw [decodeHuffmanFastBufFixed_eq] at hblock
      have hbuf := (decodeHuffmanFastBufTreeFree_ok_iff br₂ output fixedLitLengths fixedDistLengths
        hflv hflb hfdv hfdb maxOut hbo₂ hwf₂ (output', br')).mp hblock
      have hfast : Inflate.decodeHuffmanFast br₂ output (HuffTree.fromLengthsTree fixedLitLengths 15)
          (HuffTree.fromLengthsTree fixedDistLengths 15) maxOut = .ok (output', br') := hbuf
      have hhf' : Inflate.decodeHuffman br₂ output (HuffTree.fromLengthsTree fixedLitLengths 15)
          (HuffTree.fromLengthsTree fixedDistLengths 15) maxOut = .ok (output', br') := by
        rw [← decodeHuffmanFast_eq br₂ output _ _ maxOut hldep hddep hbo₂ hwf₂]; exact hfast
      obtain ⟨hd', hp', hl'⟩ := Zip.Native.decodeHuffman_inv _ _ br₂ br' output output' maxOut hhf' hp₂ hl₂
      rw [hfast]; dsimp only [bind, Except.bind]
      exact tailbwd output' br' hp' hl' (by rw [hd']; exact hdata₂) htail
    · -- dynamic Huffman block
      obtain ⟨pdt, hlonly, h⟩ := bindOk h; obtain ⟨ll, dl, br₃⟩ := pdt; simp only [] at h
      obtain ⟨pb, hblock, htail⟩ := bindOk h; obtain ⟨output', br'⟩ := pb
      obtain ⟨hdt, hllv, hdlv, hllb, hdlb⟩ := decodeDynamicTrees_of_lengthsOnly hlonly
      obtain ⟨hd3, hp3, hl3⟩ := Zip.Native.decodeDynamicTrees_inv br₂ br₃ _ _ hdt hp₂ hl₂
      have hbo3 := InflateBuf.decodeDynamicTrees_bitOff_pres hbo₂ hdt
      have hwf3 : br₃.bitPos ≤ br₃.data.size * 8 := by
        simp only [ZipCommon.BitReader.bitPos]; rcases hp3 with h' | h' <;> omega
      have hbuf := (decodeHuffmanFastBufTreeFree_ok_iff br₃ output ll dl hllv hllb hdlv hdlb
        maxOut hbo3 hwf3 (output', br')).mp hblock
      have hfast : Inflate.decodeHuffmanFast br₃ output (HuffTree.fromLengthsTree ll 15)
          (HuffTree.fromLengthsTree dl 15) maxOut = .ok (output', br') := hbuf
      have hhf' : Inflate.decodeHuffman br₃ output (HuffTree.fromLengthsTree ll 15)
          (HuffTree.fromLengthsTree dl 15) maxOut = .ok (output', br') := by
        rw [← decodeHuffmanFast_eq br₃ output _ _ maxOut
          (InflateBuf.fromLengths_depthLE (HuffTree.fromLengths_ok_of_valid ll 15 hllv))
          (InflateBuf.fromLengths_depthLE (HuffTree.fromLengths_ok_of_valid dl 15 hdlv)) hbo3 hwf3]
        exact hfast
      obtain ⟨hd', hp', hl'⟩ := Zip.Native.decodeHuffman_inv _ _ br₃ br' output output' maxOut hhf' hp3 hl3
      rw [hdt]; dsimp only [bind, Except.bind]
      rw [hfast]; dsimp only [bind, Except.bind]
      exact tailbwd output' br' hp' hl' (by rw [hd', hd3]; exact hdata₂) htail
    · -- reserved block type 3
      simp only [bind, Except.bind] at h
      exact absurd h (by simp)

/-- **Tree-free block loop ↔ verified block loop (accept set).** -/
theorem inflateLoopTreeFree_ok_iff (data : ByteArray)
    (hflv : Huffman.Spec.ValidLengths (fixedLitLengths.toList.map UInt8.toNat) 15)
    (hflb : fixedLitLengths.size ≤ UInt16.size)
    (hfdv : Huffman.Spec.ValidLengths (fixedDistLengths.toList.map UInt8.toNat) 15)
    (hfdb : fixedDistLengths.size ≤ UInt16.size) (maxOut : Nat)
    (br : BitReader) (output : ByteArray)
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size) (hple : br.pos ≤ br.data.size)
    (hds : br.data.size = data.size) (r : ByteArray × Nat) :
    inflateLoopTreeFree br output maxOut data.size = .ok r ↔
      inflateLoop br output (HuffTree.fromLengthsTree fixedLitLengths 15)
        (HuffTree.fromLengthsTree fixedDistLengths 15) maxOut data.size = .ok r :=
  ⟨inflateLoop_of_inflateLoopTreeFree data hflv hflb hfdv hfdb maxOut br output hpos hple hds r,
   inflateLoopTreeFree_of_inflateLoop data hflv hflb hfdv hfdb maxOut br output hpos hple hds r⟩

/-- The fixed lit/dist code lengths are valid (the `fromLengths` of the fixed
    tables always succeeds), packaged for the bridge lemmas below. -/
private theorem fixedLitLengths_valid' :
    Huffman.Spec.ValidLengths (fixedLitLengths.toList.map UInt8.toNat) 15 := by
  obtain ⟨fixedLit, hfl⟩ := Zip.Spec.DeflateStoredCorrect.fromLengths_fixedLit_ok
  exact Deflate.Correctness.fromLengths_valid fixedLitLengths 15 fixedLit hfl

private theorem fixedDistLengths_valid' :
    Huffman.Spec.ValidLengths (fixedDistLengths.toList.map UInt8.toNat) 15 := by
  obtain ⟨fixedDist, hfd⟩ := Zip.Spec.DeflateStoredCorrect.fromLengths_fixedDist_ok
  exact Deflate.Correctness.fromLengths_valid fixedDistLengths 15 fixedDist hfd

/-- The verified reference `inflateRawReference` is the fixed-tree-built block loop
    (the `fromLengths` of the fixed code lengths always succeeds, yielding the
    canonical trees). The concrete `fromLengthsTree` term stays opaque. -/
theorem inflateRawReference_eq_loop (data : ByteArray) (sp mo sh : Nat) :
    Inflate.inflateRawReference data sp mo sh
      = Inflate.inflateLoop { data, pos := sp, bitOff := 0 } (ByteArray.emptyWithCapacity sh)
          (HuffTree.fromLengthsTree fixedLitLengths 15) (HuffTree.fromLengthsTree fixedDistLengths 15)
          mo data.size := by
  rw [Inflate.inflateRawReference,
      HuffTree.fromLengths_ok_of_valid fixedLitLengths 15 fixedLitLengths_valid',
      HuffTree.fromLengths_ok_of_valid fixedDistLengths 15 fixedDistLengths_valid']
  rfl

/-- The production `inflateRaw` is the tree-free block loop. -/
theorem inflateRaw_eq_loop (data : ByteArray) (sp mo sh : Nat) :
    Inflate.inflateRaw data sp mo sh
      = Inflate.inflateLoopTreeFree { data, pos := sp, bitOff := 0 }
          (ByteArray.emptyWithCapacity sh) mo data.size := rfl

set_option maxRecDepth 4096 in
/-- **Top-level forward correctness.** Whenever the verified `Inflate.inflateReference`
    succeeds, the tree-free `Inflate.inflate` produces the same bytes — so
    the tree-free decoder (which never builds a Huffman tree at runtime) is a
    correct drop-in for the trusted decoder on every successful decode. The fixed
    Huffman trees exist only in the proof; `fromLengths fixedLitLengths` succeeding
    inside `inflateRaw` supplies their validity. -/
theorem inflate_of_inflateReference (data : ByteArray) (maxOut sizeHint : Nat) {out : ByteArray}
    (h : Inflate.inflateReference data maxOut sizeHint = .ok out) :
    Inflate.inflate data maxOut = .ok out := by
  rw [Inflate.inflateReference, Inflate.inflateRawReference] at h
  simp only [bind, Except.bind] at h
  obtain ⟨pr, hraw, hret⟩ := bindOk h; obtain ⟨output, restPos⟩ := pr
  simp only [pure, Except.pure, Except.ok.injEq] at hret; subst hret
  obtain ⟨fixedLit, hfl, hraw⟩ := bindOk hraw
  obtain ⟨fixedDist, hfd, hloop⟩ := bindOk hraw
  rw [show ByteArray.emptyWithCapacity sizeHint = ByteArray.empty from by
    simp [ByteArray.emptyWithCapacity, ByteArray.empty]] at hloop
  have hflv := Deflate.Correctness.fromLengths_valid fixedLitLengths 15 fixedLit hfl
  have hfdv := Deflate.Correctness.fromLengths_valid fixedDistLengths 15 fixedDist hfd
  have hfleq : fixedLit = HuffTree.fromLengthsTree fixedLitLengths 15 :=
    Except.ok.inj (hfl.symm.trans (HuffTree.fromLengths_ok_of_valid fixedLitLengths 15 hflv))
  have hfdeq : fixedDist = HuffTree.fromLengthsTree fixedDistLengths 15 :=
    Except.ok.inj (hfd.symm.trans (HuffTree.fromLengths_ok_of_valid fixedDistLengths 15 hfdv))
  have hbody := inflateLoopTreeFree_of_inflateLoop data hflv (by decide) hfdv (by decide) maxOut
    { data, pos := 0, bitOff := 0 } ByteArray.empty (Or.inl rfl) (Nat.zero_le _) rfl
    (output, restPos) (by rw [hfleq, hfdeq] at hloop; exact hloop)
  -- fold the tree-free loop result back through the production `inflateRaw`
  have hrawp : Inflate.inflateRaw data 0 maxOut 0 = .ok (output, restPos) := by
    rw [inflateRaw_eq_loop,
        show ByteArray.emptyWithCapacity 0 = ByteArray.empty from by
          simp [ByteArray.emptyWithCapacity, ByteArray.empty]]
    exact hbody
  rw [Inflate.inflate]
  simp only [hrawp, bind, Except.bind, pure, Except.pure]

set_option maxRecDepth 4096 in
/-- **Top-level backward correctness.** Whenever the tree-free decoder succeeds,
    the verified `Inflate.inflateReference` succeeds with the same bytes. With the validation
    gap closed this is the converse of `inflate_of_inflateReference`, so the two
    decoders accept exactly the same inputs (`native ⊆ FFI` is preserved). -/
theorem inflateReference_of_inflate (data : ByteArray) (maxOut : Nat) {out : ByteArray}
    (h : Inflate.inflate data maxOut = .ok out) :
    Inflate.inflateReference data maxOut = .ok out := by
  rw [Inflate.inflate] at h
  simp only [bind, Except.bind] at h
  obtain ⟨pr, hloop, hret⟩ := bindOk h; obtain ⟨output, restPos⟩ := pr
  simp only [pure, Except.pure, Except.ok.injEq] at hret; subst hret
  have hbody := inflateLoop_of_inflateLoopTreeFree data fixedLitLengths_valid' (by decide)
    fixedDistLengths_valid' (by decide) maxOut
    { data, pos := 0, bitOff := 0 } ByteArray.empty (Or.inl rfl) (Nat.zero_le _) rfl
    (output, restPos) hloop
  -- fold the verified-decoder result back through `inflateRaw` without evaluating
  -- the concrete fixed `fromLengthsTree` (kept opaque via `exact hbody`)
  have hraw : Inflate.inflateRawReference data 0 maxOut 0 = .ok (output, restPos) := by
    rw [inflateRawReference_eq_loop,
        show ByteArray.emptyWithCapacity 0 = ByteArray.empty from by
          simp [ByteArray.emptyWithCapacity, ByteArray.empty]]
    exact hbody
  rw [Inflate.inflateReference]
  simp only [hraw, bind, Except.bind, pure, Except.pure]

/-- **Top-level accept-set equality.** The production `inflate` and the verified
    reference `inflateReference` succeed on exactly the same inputs with the same
    output. This is the bridge every downstream theorem rides on: any property of
    the reference's success set transfers to the production tree-free decoder, and
    `native ⊆ FFI` is preserved. -/
theorem inflate_ok_iff_reference (data : ByteArray) (maxOut : Nat) (out : ByteArray) :
    Inflate.inflate data maxOut = .ok out ↔ Inflate.inflateReference data maxOut = .ok out :=
  ⟨inflateReference_of_inflate data maxOut,
   fun h => inflate_of_inflateReference data maxOut 0 h⟩

set_option maxRecDepth 4096 in
/-- **`inflateRaw` accept-set equality.** For an in-bounds start position the
    production `inflateRaw` and the verified reference `inflateRawReference` succeed
    on exactly the same inputs with the same output and end position. -/
theorem inflateRaw_ok_iff_reference (data : ByteArray) (sp mo sh : Nat)
    (hle : sp ≤ data.size) (p : ByteArray × Nat) :
    Inflate.inflateRaw data sp mo sh = .ok p ↔ Inflate.inflateRawReference data sp mo sh = .ok p := by
  rw [inflateRaw_eq_loop, inflateRawReference_eq_loop]
  exact inflateLoopTreeFree_ok_iff data fixedLitLengths_valid' (by decide)
    fixedDistLengths_valid' (by decide) mo
    { data, pos := sp, bitOff := 0 } (ByteArray.emptyWithCapacity sh) (Or.inl rfl) hle rfl p

end Zip.Native.Inflate
