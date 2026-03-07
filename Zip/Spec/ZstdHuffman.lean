import Zip.Native.ZstdHuffman
import Zip.Spec.Fse
import ZipForStd.Array

/-!
# Zstandard Huffman Weight Validity Predicates (RFC 8878 §4.2.1)

Formal specification of Zstd Huffman weight table validity and decoded
table structure.  Zstd Huffman coding uses a weight-based representation
where each symbol has a weight `W ≥ 0`; symbols with `W > 0` have code
length `maxBits + 1 - W`, and a weight of 0 means the symbol is not
present.  The last symbol's weight is implicit, determined by the Kraft
equality.

The specification is structured in layers:
1. **Weight validity**: non-empty, at least one non-zero, bounded weights
2. **Kraft completeness**: sum of `2^(W-1)` for positive weights, plus
   the implicit last symbol, equals exactly `2^maxBits`
3. **Table validity**: structural invariants on the flat lookup table
   produced by `buildZstdHuffmanTable`

All predicates have `Decidable` instances for use with `decide`.
-/

namespace Zstd.Spec.Huffman

open Zip.Native (HuffmanEntry ZstdHuffmanTable)

/-! ## Weight sum computation -/

/-- Compute the weight sum `∑ 2^(W-1)` for all positive weights in the array.
    This is the contribution of the explicitly listed symbols; the implicit
    last symbol fills the gap to `2^maxBits`. -/
def weightSum (weights : Array UInt8) : Nat :=
  weights.foldl (fun acc w =>
    if w.toNat > 0 then acc + (1 <<< (w.toNat - 1)) else acc) 0

/-! ## Weight validity predicates -/

/-- A Huffman weight array is valid when:
    (a) it is non-empty (`weights.size ≥ 1`),
    (b) at least one weight is non-zero,
    (c) no weight exceeds 13 (the practical maximum per RFC 8878 — codes
        longer than 13 bits are not useful for a 256-symbol alphabet). -/
def ValidWeights (weights : Array UInt8) : Prop :=
  weights.size ≥ 1 ∧
  (∃ i : Fin weights.size, weights[i].toNat > 0) ∧
  (∀ i : Fin weights.size, weights[i].toNat ≤ 13)

instance {weights : Array UInt8} : Decidable (ValidWeights weights) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-! ## Kraft completeness -/

/-- Check whether `n` is a power of 2 (i.e. `n = 2^k` for some `k`).
    Uses the standard bit-trick: `n > 0 ∧ n &&& (n - 1) = 0`. -/
def isPow2 (n : Nat) : Bool :=
  n > 0 && (n &&& (n - 1)) == 0

/-- Helper: for even n > 0, `n &&& (n - 1) = 2 * (n/2 &&& (n/2 - 1))`. -/
private theorem land_pred_even (n : Nat) (heven : n % 2 = 0) (hpos : n > 0) :
    n &&& (n - 1) = 2 * (n / 2 &&& (n / 2 - 1)) := by
  have hdiv : (n - 1) / 2 = n / 2 - 1 := by omega
  apply Nat.eq_of_testBit_eq
  intro i
  match i with
  | 0 =>
    rw [Nat.testBit_and]
    simp only [Nat.testBit_zero, heven, Nat.mul_mod_right,
      show (0 : Nat) ≠ 1 from by omega, decide_false, Bool.false_and]
  | i + 1 =>
    rw [Nat.testBit_and, Nat.testBit_succ, Nat.testBit_succ]
    rw [Nat.testBit_succ, Nat.mul_div_cancel_left _ (by omega : 0 < 2)]
    rw [Nat.testBit_and, hdiv]

/-- Helper: for odd n, `n &&& (n - 1) = 2 * (n / 2)`. -/
private theorem land_pred_odd (n : Nat) (hodd : n % 2 = 1) :
    n &&& (n - 1) = 2 * (n / 2) := by
  have hdiv : (n - 1) / 2 = n / 2 := by omega
  apply Nat.eq_of_testBit_eq
  intro i
  match i with
  | 0 =>
    have : (n - 1) % 2 = 0 := by omega
    rw [Nat.testBit_and]
    simp only [Nat.testBit_zero, hodd, this, Nat.mul_mod_right, decide_true, Bool.true_and]
  | i + 1 =>
    rw [Nat.testBit_and, Nat.testBit_succ, Nat.testBit_succ,
        hdiv, Bool.and_self,
        Nat.testBit_succ, Nat.mul_div_cancel_left _ (by omega : 0 < 2)]

/-- Strong induction helper: n > 0 ∧ n &&& (n-1) = 0 → ∃ k, 2^k = n. -/
private theorem land_pred_zero_imp_pow2 (n : Nat) (hpos : n > 0) (hand : n &&& (n - 1) = 0) :
    ∃ k : Nat, 2 ^ k = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
  rcases Nat.mod_two_eq_zero_or_one n with hmod | hmod
  · -- n is even: use land_pred_even to reduce to n/2
    have hge2 : n ≥ 2 := by omega
    have heven := land_pred_even n hmod hpos
    rw [hand] at heven
    -- heven : 0 = 2 * (n/2 &&& (n/2 - 1)), so n/2 &&& (n/2 - 1) = 0
    have hand2 : n / 2 &&& (n / 2 - 1) = 0 := by omega
    have hpos2 : n / 2 > 0 := by omega
    have hlt : n / 2 < n := by omega
    have ⟨j, hj⟩ := ih (n / 2) hlt hpos2 hand2
    exact ⟨j + 1, by rw [Nat.pow_succ, Nat.mul_comm]; omega⟩
  · -- n is odd: if n ≥ 3, then n &&& (n-1) > 0, contradiction
    -- So n must be 1
    have hodd := land_pred_odd n hmod
    rw [hand] at hodd
    -- hodd : 0 = 2 * (n / 2), so n / 2 = 0, so n = 1
    have : n / 2 = 0 := by omega
    have : n = 1 := by omega
    exact ⟨0, by omega⟩

/-- `isPow2` correctly characterizes powers of 2. -/
theorem isPow2_iff (n : Nat) : isPow2 n = true ↔ ∃ k : Nat, 1 <<< k = n := by
  simp only [isPow2, Nat.shiftLeft_eq, Nat.one_mul, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq]
  constructor
  · exact fun ⟨hpos, hand⟩ => land_pred_zero_imp_pow2 n hpos hand
  · intro ⟨k, hk⟩
    subst hk
    refine ⟨Nat.two_pow_pos k, ?_⟩
    -- 2^k &&& (2^k - 1) = 0 by induction using land_pred_even
    induction k with
    | zero => decide
    | succ k ih =>
      have hdiv : 2 ^ (k + 1) / 2 = 2 ^ k := by
        rw [Nat.pow_succ, Nat.mul_comm, Nat.mul_div_cancel_left _ (by omega : 0 < 2)]
      rw [land_pred_even (2 ^ (k + 1))
        (by rw [Nat.pow_succ, Nat.mul_comm]; exact Nat.mul_mod_right 2 _)
        (Nat.two_pow_pos _), hdiv, ih]

/-- The Kraft equality holds for `weights` and `maxBits` when the sum of
    `2^(W-1)` for all positive explicit weights, plus the implicit last
    symbol's contribution, equals exactly `2^maxBits`.  Equivalently:
    `weightSum weights < 2^maxBits` (the implicit symbol fills the gap),
    and the gap is itself a power of 2.

    This is the fundamental constraint from RFC 8878 §4.2.1.1: the total
    must be a complete prefix-free code. -/
def KraftComplete (weights : Array UInt8) (maxBits : Nat) : Prop :=
  let ws := weightSum weights
  ws > 0 ∧
  ws < 1 <<< maxBits ∧
  isPow2 ((1 <<< maxBits) - ws) = true

instance {weights : Array UInt8} {maxBits : Nat} :
    Decidable (KraftComplete weights maxBits) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-! ## Table validity predicates -/

/-- A flat Huffman decoding table satisfies structural invariants when:
    (a) `table.size = 1 << maxBits` (the table is fully populated),
    (b) all entries have `numBits ≤ maxBits`, and
    (c) all symbol indices are at most 255 (fit in UInt8, always true
        by construction but useful for downstream reasoning). -/
def ValidHuffmanTable (table : Array HuffmanEntry) (maxBits : Nat) : Prop :=
  table.size = 1 <<< maxBits ∧
  (∀ i : Fin table.size, table[i].numBits.toNat ≤ maxBits) ∧
  (∀ i : Fin table.size, table[i].symbol.toNat ≤ 255)

instance {table : Array HuffmanEntry} {maxBits : Nat} :
    Decidable (ValidHuffmanTable table maxBits) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-! ## Helper: forIn with pure yield reduces to foldl -/

/-- When the body of `forIn` over an `Array` in the `Except` monad always
    returns `Except.ok (ForInStep.yield ...)`, the result equals `Except.ok`
    of the corresponding `Array.foldl`.

    This is proved by converting through `Array.forIn_eq_foldlM` and
    `Array.foldlM_toList`, then inducting on `as.toList`. -/
private theorem forIn_pure_yield_eq_foldl {ε : Type} (as : Array α) (f : α → β → β) (init : β) :
    forIn as init (fun a b =>
      (Except.ok (ForInStep.yield (f a b)) : Except ε (ForInStep β))) =
    (Except.ok (as.foldl (fun b a => f a b) init) : Except ε β) := by
  rw [Array.forIn_eq_foldlM, ← Array.foldlM_toList, ← Array.foldl_toList]
  generalize as.toList = l
  revert init
  induction l with
  | nil => intro init; rfl
  | cons x l ih =>
    intro init
    simp only [List.foldlM, bind, Except.bind, List.foldl_cons]
    exact ih (f x init)

/-! ## Correctness theorems -/

open Zip.Native in
/-- The WF loop always returns at least its initial `maxBits` argument. -/
private theorem findMaxBitsWF_ge (ws maxBits power : Nat) (hp : power > 0) :
    findMaxBitsWF ws maxBits power hp ≥ maxBits := by
  unfold findMaxBitsWF
  split
  · have ih := findMaxBitsWF_ge ws (maxBits + 1) (power * 2) (by omega); omega
  · split <;> omega
termination_by ws - power

open Zip.Native in
/-- When `weightSum ≥ 1`, `findMaxBitsWF weightSum 0 1 _ ≥ 1`. -/
private theorem findMaxBitsWF_ge_one (ws : Nat) (hws : ws ≥ 1) :
    findMaxBitsWF ws 0 1 (by omega) ≥ 1 := by
  unfold findMaxBitsWF
  split
  · -- 1 < ws: recurse with maxBits=1, power=2
    exact Nat.le_trans (by omega : 1 ≤ 1) (findMaxBitsWF_ge ws 1 2 (by omega))
  · -- ¬(1 < ws), so ws ≤ 1, combined with ws ≥ 1 means ws = 1
    split <;> simp only [beq_iff_eq] at * <;> omega

open Zip.Native in
/-- When `weightsToMaxBits` succeeds, the result is at least 1.  The weight sum
    is ≥ 1 (the guard rejects zero), and `findMaxBitsWF` with initial power = 1
    always returns ≥ 1 when the weight sum is positive. -/
private theorem weightsToMaxBits_ge_one (weights : Array UInt8) (m : Nat)
    (h : weightsToMaxBits weights = .ok m) : m ≥ 1 := by
  simp only [weightsToMaxBits, bind, Except.bind] at h
  -- Layer 1: forIn weights (weightSum accumulation loop)
  split at h
  · exact nomatch h
  · rename_i ws _
    -- Layer 2: guard (weightSum == 0)
    split at h
    · exact nomatch h
    · -- guard passes, pure () reduces
      dsimp only [pure, Pure.pure, Except.pure] at h
      simp only [Except.ok.injEq] at h
      subst h
      exact findMaxBitsWF_ge_one ws (by simp only [beq_iff_eq] at *; omega)

open Zip.Native in
/-- The WF loop returns a value `m` such that `ws ≤ 2^m`, given the loop
    invariant `power = 2^maxBits`. -/
private theorem findMaxBitsWF_bound (ws maxBits power : Nat) (hp : power > 0)
    (hinv : power = 1 <<< maxBits) :
    ws ≤ 1 <<< (findMaxBitsWF ws maxBits power hp) := by
  unfold findMaxBitsWF
  split
  · -- power < ws: recurse with doubled power
    exact findMaxBitsWF_bound ws (maxBits + 1) (power * 2) (by omega)
      (by simp only [Nat.shiftLeft_eq, Nat.one_mul, Nat.pow_succ] at hinv ⊢; omega)
  · split
    · -- ws == power: return maxBits + 1
      rename_i _ h2; simp only [beq_iff_eq] at h2; subst h2
      simp only [hinv, Nat.shiftLeft_eq, Nat.one_mul, Nat.pow_succ]
      have := Nat.two_pow_pos maxBits; omega
    · -- power ≥ ws: return maxBits
      rename_i h1 _
      have := Nat.le_of_not_lt h1; rw [hinv] at this; exact this
termination_by ws - power

open Zip.Native in
/-- The inner fill loop preserves array size: each step either uses `set!`
    (which preserves size) or leaves the table unchanged. -/
private theorem fillHuffmanTableInnerWF_preserves_size
    (table : Array HuffmanEntry) (entry : HuffmanEntry)
    (code stride tableSize sym lastSymbol j : Nat)
    (result : Array HuffmanEntry)
    (h : fillHuffmanTableInnerWF table entry code stride tableSize sym lastSymbol j = .ok result) :
    result.size = table.size := by
  unfold fillHuffmanTableInnerWF at h
  split at h
  · -- j ≥ stride: result = table
    simp only [Except.ok.injEq] at h; subst h; rfl
  · -- j < stride: reduce `have idx := ...`
    dsimp only [] at h
    split at h
    · -- idx < tableSize: recurse with table.set!
      have ih := fillHuffmanTableInnerWF_preserves_size _ entry code stride tableSize
        sym lastSymbol (j + 1) result h
      rw [ih, Array.size_set!]
    · -- idx ≥ tableSize
      split at h
      · exact nomatch h  -- throw: contradiction
      · -- skip: recurse with table unchanged
        exact fillHuffmanTableInnerWF_preserves_size _ entry code stride tableSize
          sym lastSymbol (j + 1) result h
termination_by stride - j

open Zip.Native in
/-- The outer fill loop preserves array size. -/
private theorem fillHuffmanTableWF_preserves_size
    (table : Array HuffmanEntry) (allWeights : Array UInt8)
    (nextCode : Array Nat) (maxBits tableSize numSymbols lastSymbol sym : Nat)
    (resultTable : Array HuffmanEntry) (resultNextCode : Array Nat)
    (h : fillHuffmanTableWF table allWeights nextCode maxBits tableSize
      numSymbols lastSymbol sym = .ok (resultTable, resultNextCode)) :
    resultTable.size = table.size := by
  unfold fillHuffmanTableWF at h
  split at h
  · -- sym ≥ numSymbols: result = table
    simp only [Except.ok.injEq, Prod.mk.injEq] at h; rw [h.1]
  · -- sym < numSymbols: reduce `have w := ...`
    dsimp only [] at h
    split at h
    · -- w == 0: recurse unchanged
      exact fillHuffmanTableWF_preserves_size _ allWeights nextCode maxBits tableSize
        numSymbols lastSymbol (sym + 1) resultTable resultNextCode h
    · -- w ≠ 0: split on the inner match result
      split at h
      · -- inner succeeded with table'
        rename_i _ _ hinner
        have hsize := fillHuffmanTableInnerWF_preserves_size _ _ _ _ _ _ _ _ _ hinner
        have ih := fillHuffmanTableWF_preserves_size _ allWeights _ maxBits tableSize
          numSymbols lastSymbol _ resultTable resultNextCode h
        rw [ih, hsize]
      · exact nomatch h  -- inner threw: contradiction
termination_by numSymbols - sym

/-- Decompose a successful `buildZstdHuffmanTable` call: `weightsToMaxBits` succeeded
    with `result.maxBits`, and the table has size `1 <<< result.maxBits`.  This peels
    through the 7 monadic layers of the do-block once, deduplicating the shared work
    between `buildZstdHuffmanTable_tableSize` and `buildZstdHuffmanTable_maxBits_pos`. -/
private theorem buildZstdHuffmanTable_ok_elim (weights : Array UInt8)
    (result : ZstdHuffmanTable)
    (h : Zip.Native.buildZstdHuffmanTable weights = .ok result) :
    Zip.Native.weightsToMaxBits weights = .ok result.maxBits ∧
    result.table.size = 1 <<< result.maxBits := by
  open Zip.Native in
  simp only [buildZstdHuffmanTable, bind, Except.bind] at h
  cases hwm : weightsToMaxBits weights with
  | error e => simp only [hwm] at h; exact nomatch h
  | ok m =>
    rw [hwm] at h; dsimp only [Bind.bind, Except.bind] at h
    -- Peel through 7 monadic layers (forIn, guard, while, guard, weightCounts, nextCode, fill)
    split at h; · exact nomatch h
    · split at h; · exact nomatch h
      · dsimp only [pure, Pure.pure, Except.pure] at h
        split at h; · exact nomatch h
        · split at h; · exact nomatch h
          · split at h; · exact nomatch h
            · split at h; · exact nomatch h
              · split at h
                · exact nomatch h
                · rename_i _ v hfill
                  simp only [Except.ok.injEq] at h
                  constructor
                  · rw [← h]
                  · subst h
                    obtain ⟨filledTable, filledNextCode⟩ := v
                    simp only at hfill ⊢
                    have hpres := fillHuffmanTableWF_preserves_size _ _ _ _ _ _ _ _ _ _ hfill
                    rw [hpres, Array.size_replicate]

/-- When `buildZstdHuffmanTable` succeeds, the resulting table has size `1 <<< maxBits`. -/
theorem buildZstdHuffmanTable_tableSize (weights : Array UInt8)
    (result : ZstdHuffmanTable)
    (h : Zip.Native.buildZstdHuffmanTable weights = .ok result) :
    result.table.size = 1 <<< result.maxBits :=
  (buildZstdHuffmanTable_ok_elim weights result h).2

/-- When `buildZstdHuffmanTable` succeeds, `maxBits ≥ 1`. -/
theorem buildZstdHuffmanTable_maxBits_pos (weights : Array UInt8)
    (result : ZstdHuffmanTable)
    (h : Zip.Native.buildZstdHuffmanTable weights = .ok result) :
    result.maxBits ≥ 1 :=
  weightsToMaxBits_ge_one weights result.maxBits (buildZstdHuffmanTable_ok_elim weights result h).1

/-- When `weightsToMaxBits` succeeds with result `m`, the weight sum
    satisfies `0 < weightSum ≤ 2^m`. The function finds the smallest
    `k` with `2^k ≥ weightSum`, then bumps by 1 if equality holds
    (to accommodate the implicit last symbol).

    The original statement claimed `weightSum ≤ 2^(m-1)`, which is false:
    e.g. `weights = #[1, 2]` gives `weightSum = 3`, `m = 2`, but
    `3 > 2^(2-1) = 2`. The correct bound is `2^m`. -/
theorem weightsToMaxBits_valid (weights : Array UInt8)
    (m : Nat)
    (h : Zip.Native.weightsToMaxBits weights = .ok m) :
    weightSum weights > 0 ∧ weightSum weights ≤ 1 <<< m := by
  open Zip.Native in
  simp only [weightsToMaxBits, bind, Except.bind] at h
  split at h
  · exact nomatch h
  · rename_i ws heq_forIn
    split at h
    · exact nomatch h
    · dsimp only [pure, Pure.pure, Except.pure] at h
      simp only [Except.ok.injEq] at h
      subst h
      have hws : ws = weightSum weights := by
        -- Simplify match on pure PUnit.unit (do-notation desugaring artifact)
        simp only [pure, Pure.pure, Except.pure] at heq_forIn
        -- Pull Except.ok (ForInStep.yield ...) out of the if branches
        simp only [show ∀ (w : UInt8) (r : Nat),
            (if w.toNat > 0 then (Except.ok (ForInStep.yield (r + 1 <<< (w.toNat - 1))))
             else (Except.ok (ForInStep.yield r) : Except String (ForInStep Nat))) =
            Except.ok (ForInStep.yield (if w.toNat > 0 then r + 1 <<< (w.toNat - 1) else r))
          from fun w r => by split <;> rfl] at heq_forIn
        rw [forIn_pure_yield_eq_foldl] at heq_forIn
        exact (Except.ok.inj heq_forIn).symm
      rw [← hws]
      exact ⟨by simp only [beq_iff_eq] at *; omega,
             findMaxBitsWF_bound ws 0 1 (by omega) rfl⟩

/-- The `weightSum` function agrees with the inline computation in
    `weightsToMaxBits`: both compute `∑ 2^(W-1)` for positive weights. -/
theorem weightSum_eq_inline (weights : Array UInt8) :
    weightSum weights =
      weights.foldl (fun acc w =>
        if w.toNat > 0 then acc + (1 <<< (w.toNat - 1)) else acc) 0 := by
  rfl

/-- The weight fold step never decreases the accumulator. -/
private theorem weightStep_ge (acc : Nat) (w : UInt8) :
    acc ≤ (if w.toNat > 0 then acc + (1 <<< (w.toNat - 1)) else acc) := by
  split
  · exact Nat.le_add_right acc _
  · exact Nat.le_refl acc

/-- The weight fold is monotone in the initial accumulator. -/
private theorem weightFold_mono_init (l : List UInt8) (a b : Nat) (h : a ≤ b) :
    l.foldl (fun acc w =>
      if w.toNat > 0 then acc + (1 <<< (w.toNat - 1)) else acc) a ≤
    l.foldl (fun acc w =>
      if w.toNat > 0 then acc + (1 <<< (w.toNat - 1)) else acc) b := by
  induction l generalizing a b with
  | nil => exact h
  | cons x l ih =>
    simp only [List.foldl_cons]
    apply ih
    split <;> omega

/-- The weight fold over a list preserves a lower bound on the accumulator. -/
private theorem weightFold_ge_init (l : List UInt8) (acc : Nat) :
    acc ≤ l.foldl (fun acc w =>
      if w.toNat > 0 then acc + (1 <<< (w.toNat - 1)) else acc) acc := by
  induction l generalizing acc with
  | nil => exact Nat.le_refl _
  | cons x l ih =>
    simp only [List.foldl_cons]
    exact Nat.le_trans (weightStep_ge acc x) (ih _)

/-- A single non-zero weight gives a non-zero weight sum. -/
theorem weightSum_pos_of_exists_nonzero (weights : Array UInt8)
    (i : Fin weights.size) (hi : weights[i].toNat > 0) :
    weightSum weights > 0 := by
  unfold weightSum
  rw [← Array.foldl_toList]
  -- Split the list at index i
  rw [show weights.toList = weights.toList.take i.val ++ weights.toList.drop i.val
        from (List.take_append_drop i.val weights.toList).symm,
      List.foldl_append,
      show weights.toList.drop i.val =
        weights.toList[i.val] :: weights.toList.drop (i.val + 1)
        from List.drop_eq_getElem_cons (by simp only [Array.length_toList]; exact i.isLt),
      List.foldl_cons]
  -- After processing weights[i], the accumulator is ≥ 1
  apply Nat.lt_of_lt_of_le Nat.zero_lt_one
  apply Nat.le_trans _ (weightFold_ge_init _ _)
  split
  · -- 1 <<< k ≥ 1, so acc + (1 <<< k) ≥ 1
    exact Nat.le_trans
      (show 1 ≤ 1 <<< (weights.toList[↑i].toNat - 1) by
        simp only [Nat.shiftLeft_eq, Nat.one_mul]; exact Nat.two_pow_pos _)
      (Nat.le_add_left _ _)
  · -- Contradiction: weights.toList[↑i] = weights[i], whose toNat > 0
    next hc => exact absurd (by simpa only [Array.getElem_toList] using hi) hc

/-! ## Concrete validation examples -/

/-- The empty weight array has zero weight sum. -/
theorem weightSum_empty : weightSum #[] = 0 := by decide

/-- A single weight of 1 gives weight sum 1 (= 2^0). -/
theorem weightSum_singleton : weightSum #[1] = 1 := by decide

/-- Two weights of 1 gives weight sum 2 (= 1 + 1). -/
theorem weightSum_two_ones : weightSum #[1, 1] = 2 := by decide

/-- The weights `#[1, 1]` are valid: non-empty, at least one positive,
    all ≤ 13. -/
theorem validWeights_two_ones : ValidWeights #[1, 1] := by decide

/-- The weights `#[1, 1]` satisfy Kraft completeness with `maxBits = 2`:
    `weightSum = 2`, `2^2 = 4`, gap = 2 which is a power of 2. -/
theorem kraft_two_ones : KraftComplete #[1, 1] 2 := by decide

/-- A weight of 2 contributes 2 (= 2^1) to the sum. -/
theorem weightSum_weight2 : weightSum #[2] = 2 := by decide

/-- The weights `#[2, 1]` satisfy Kraft completeness with `maxBits = 2`:
    `weightSum = 2 + 1 = 3`, `2^2 = 4`, gap = 1 which is a power of 2. -/
theorem kraft_mixed : KraftComplete #[2, 1] 2 := by decide

/-! ## parseCompressedLiteralsHeader properties -/

open Zip.Native in
/-- `parseCompressedLiteralsHeader` always returns `headerBytes ≥ 3`. -/
private theorem parseCompressedLiteralsHeader_headerBytes_ge (data : ByteArray)
    (pos sizeFormat regen comp hdr : Nat) (fs : Bool)
    (h : parseCompressedLiteralsHeader data pos sizeFormat = .ok (regen, comp, hdr, fs)) :
    hdr ≥ 3 := by
  simp only [parseCompressedLiteralsHeader, bind, Except.bind, pure, Except.pure] at h
  split at h
  · split at h
    · exact nomatch h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h; omega
  · split at h
    · split at h
      · exact nomatch h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h; omega
    · split at h
      · exact nomatch h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h; omega

open Zip.Native in
/-- `parseCompressedLiteralsHeader` returns the correct `headerSize` for each `sizeFormat`:
    `sizeFormat ≤ 1 → 3`, `sizeFormat = 2 → 4`, `sizeFormat > 2 → 5`. -/
theorem parseCompressedLiteralsHeader_headerSize (data : ByteArray) (pos : Nat)
    (sizeFormat : Nat) (regen comp headerSize : Nat) (fourStreams : Bool)
    (h : parseCompressedLiteralsHeader data pos sizeFormat
         = .ok (regen, comp, headerSize, fourStreams)) :
    (sizeFormat ≤ 1 → headerSize = 3) ∧
    (sizeFormat = 2 → headerSize = 4) ∧
    (sizeFormat > 2 → headerSize = 5) := by
  simp only [parseCompressedLiteralsHeader, bind, Except.bind, pure, Except.pure] at h
  split at h
  · split at h
    · exact nomatch h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, -, hhdr, -⟩ := h
      exact ⟨fun _ => by omega, fun _ => by omega, fun _ => by omega⟩
  · split at h
    · split at h
      · exact nomatch h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        simp only [beq_iff_eq] at *
        obtain ⟨-, -, hhdr, -⟩ := h
        exact ⟨fun _ => by omega, fun _ => by omega, fun _ => by omega⟩
    · split at h
      · exact nomatch h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        simp only [beq_iff_eq] at *
        obtain ⟨-, -, hhdr, -⟩ := h
        exact ⟨fun _ => by omega, fun _ => by omega, fun _ => by omega⟩

open Zip.Native in
/-- `parseCompressedLiteralsHeader` returns the correct `fourStreams` value:
    `sizeFormat = 0 → false`, `sizeFormat ≥ 1 → true`. -/
theorem parseCompressedLiteralsHeader_fourStreams (data : ByteArray) (pos : Nat)
    (sizeFormat : Nat) (regen comp headerSize : Nat) (fourStreams : Bool)
    (h : parseCompressedLiteralsHeader data pos sizeFormat
         = .ok (regen, comp, headerSize, fourStreams)) :
    (sizeFormat = 0 → fourStreams = false) ∧
    (sizeFormat ≥ 1 → fourStreams = true) := by
  simp only [parseCompressedLiteralsHeader, bind, Except.bind, pure, Except.pure] at h
  split at h
  · split at h
    · exact nomatch h
    · rename_i hsf _
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, -, -, hfs⟩ := h
      -- hfs : (sizeFormat == 1) = fourStreams
      constructor
      · intro heq; subst heq; exact hfs.symm
      · intro hge
        simp only [show sizeFormat = 1 from by omega, beq_self_eq_true] at hfs
        exact hfs.symm
  · split at h
    · split at h
      · exact nomatch h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, -, -, hfs⟩ := h
        exact ⟨fun _ => by omega, fun _ => hfs.symm⟩
    · split at h
      · exact nomatch h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, -, -, hfs⟩ := h
        exact ⟨fun _ => by omega, fun _ => hfs.symm⟩

open Zip.Native in
/-- `parseCompressedLiteralsHeader` always returns `regen ≤ 0x3FFFF`.
    In all branches, `regen` is computed as `(raw >>> shift) &&& mask` where
    `mask ∈ {0x3FF, 0x3FFF, 0x3FFFF}`, and `x &&& mask ≤ mask ≤ 0x3FFFF`. -/
theorem parseCompressedLiteralsHeader_regen_bound (data : ByteArray) (pos : Nat)
    (sizeFormat : Nat) (regen comp headerSize : Nat) (fourStreams : Bool)
    (h : parseCompressedLiteralsHeader data pos sizeFormat
         = .ok (regen, comp, headerSize, fourStreams)) :
    regen ≤ 0x3FFFF := by
  simp only [parseCompressedLiteralsHeader, bind, Except.bind, pure, Except.pure] at h
  split at h
  · split at h
    · exact nomatch h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      rw [← h.1]; exact Nat.le_trans Nat.and_le_right (by omega)
  · split at h
    · split at h
      · exact nomatch h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        rw [← h.1]; exact Nat.le_trans Nat.and_le_right (by omega)
    · split at h
      · exact nomatch h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        rw [← h.1]; exact Nat.and_le_right

/-! ## parseLiteralsSection structural properties (raw/RLE) -/

open Zip.Native in
/-- For raw or RLE literals (types 0-1), the returned position is strictly
    greater than the input position, and the returned Huffman table is `none`. -/
private theorem parseLiteralsSection_simple_spec (data : ByteArray) (pos : Nat)
    (prevHuffTree : Option ZstdHuffmanTable)
    (literals : ByteArray) (pos' : Nat) (huffTable : Option ZstdHuffmanTable)
    (hlit : (data[pos]! &&& 3).toNat ≤ 1)
    (h : parseLiteralsSection data pos prevHuffTree = .ok (literals, pos', huffTable)) :
    pos' > pos ∧ huffTable = none := by
  simp only [parseLiteralsSection, bind, Except.bind, pure, Except.pure] at h
  split at h
  · exact nomatch h
  · -- data.size ≥ pos + 1, byte0 = data[pos]!
    -- litType > 3 guard
    split at h
    · exact nomatch h
    · -- litType ≤ 3; compressed/treeless check
      split at h
      · -- litType == 2 || litType == 3: contradicts hlit
        rename_i hle3 hcomp
        simp only [beq_iff_eq, Bool.or_eq_true] at hcomp
        have : (data[pos]! &&& 3).toNat = 2 ∨ (data[pos]! &&& 3).toNat = 3 := hcomp
        omega
      · -- Raw/RLE path: parse header
        -- sizeFormat dispatch
        split at h
        · -- sizeFormat == 0 || sizeFormat == 2: headerBytes = 1
          split at h
          · -- litType == 0: raw
            split at h
            · exact nomatch h
            · simp only [Except.ok.injEq, Prod.mk.injEq] at h
              exact ⟨by omega, h.2.2.symm⟩
          · -- litType == 1: RLE
            split at h
            · exact nomatch h
            · simp only [Except.ok.injEq, Prod.mk.injEq] at h
              exact ⟨by omega, h.2.2.symm⟩
        · split at h
          · -- sizeFormat == 1: headerBytes = 2
            split at h
            · exact nomatch h
            · split at h
              · -- litType == 0: raw
                split at h
                · exact nomatch h
                · simp only [Except.ok.injEq, Prod.mk.injEq] at h
                  exact ⟨by omega, h.2.2.symm⟩
              · -- litType == 1: RLE
                split at h
                · exact nomatch h
                · simp only [Except.ok.injEq, Prod.mk.injEq] at h
                  exact ⟨by omega, h.2.2.symm⟩
          · -- sizeFormat == 3: headerBytes = 3
            split at h
            · exact nomatch h
            · split at h
              · -- litType == 0: raw
                split at h
                · exact nomatch h
                · simp only [Except.ok.injEq, Prod.mk.injEq] at h
                  exact ⟨by omega, h.2.2.symm⟩
              · -- litType == 1: RLE
                split at h
                · exact nomatch h
                · simp only [Except.ok.injEq, Prod.mk.injEq] at h
                  exact ⟨by omega, h.2.2.symm⟩

open Zip.Native in
/-- For raw or RLE literals (types 0-1), the returned position advances. -/
theorem parseLiteralsSection_pos_gt_simple (data : ByteArray) (pos : Nat)
    (prevHuffTree : Option ZstdHuffmanTable)
    (literals : ByteArray) (pos' : Nat) (huffTable : Option ZstdHuffmanTable)
    (hlit : (data[pos]! &&& 3).toNat ≤ 1)
    (h : parseLiteralsSection data pos prevHuffTree = .ok (literals, pos', huffTable)) :
    pos' > pos :=
  (parseLiteralsSection_simple_spec data pos prevHuffTree literals pos' huffTable hlit h).1

open Zip.Native in
/-- For raw or RLE literals (types 0-1), no Huffman table is returned. -/
theorem parseLiteralsSection_huffTable_none_simple (data : ByteArray) (pos : Nat)
    (prevHuffTree : Option ZstdHuffmanTable)
    (literals : ByteArray) (pos' : Nat) (huffTable : Option ZstdHuffmanTable)
    (hlit : (data[pos]! &&& 3).toNat ≤ 1)
    (h : parseLiteralsSection data pos prevHuffTree = .ok (literals, pos', huffTable)) :
    huffTable = none :=
  (parseLiteralsSection_simple_spec data pos prevHuffTree literals pos' huffTable hlit h).2

open Zip.Native in
/-- For raw or RLE literals (types 0-1), the returned position stays within `data.size`. -/
theorem parseLiteralsSection_le_size_simple (data : ByteArray) (pos : Nat)
    (prevHuffTree : Option ZstdHuffmanTable)
    (literals : ByteArray) (pos' : Nat) (huffTable : Option ZstdHuffmanTable)
    (hlit : (data[pos]! &&& 3).toNat ≤ 1)
    (h : parseLiteralsSection data pos prevHuffTree = .ok (literals, pos', huffTable)) :
    pos' ≤ data.size := by
  simp only [parseLiteralsSection, bind, Except.bind, pure, Except.pure] at h
  split at h
  · exact nomatch h
  · -- data.size ≥ pos + 1
    split at h
    · exact nomatch h
    · -- litType ≤ 3; compressed/treeless check
      split at h
      · -- litType == 2 || litType == 3: contradicts hlit
        rename_i hle3 hcomp
        simp only [beq_iff_eq, Bool.or_eq_true] at hcomp
        have : (data[pos]! &&& 3).toNat = 2 ∨ (data[pos]! &&& 3).toNat = 3 := hcomp
        omega
      · -- Raw/RLE path: parse header
        -- sizeFormat dispatch
        split at h
        · -- sizeFormat == 0 || sizeFormat == 2: headerBytes = 1
          split at h
          · -- litType == 0: raw
            split at h
            · exact nomatch h
            · simp only [Except.ok.injEq, Prod.mk.injEq] at h
              omega
          · -- litType == 1: RLE
            split at h
            · exact nomatch h
            · simp only [Except.ok.injEq, Prod.mk.injEq] at h
              omega
        · split at h
          · -- sizeFormat == 1: headerBytes = 2
            split at h
            · exact nomatch h
            · split at h
              · -- litType == 0: raw
                split at h
                · exact nomatch h
                · simp only [Except.ok.injEq, Prod.mk.injEq] at h
                  omega
              · -- litType == 1: RLE
                split at h
                · exact nomatch h
                · simp only [Except.ok.injEq, Prod.mk.injEq] at h
                  omega
          · -- sizeFormat == 3: headerBytes = 3
            split at h
            · exact nomatch h
            · split at h
              · -- litType == 0: raw
                split at h
                · exact nomatch h
                · simp only [Except.ok.injEq, Prod.mk.injEq] at h
                  omega
              · -- litType == 1: RLE
                split at h
                · exact nomatch h
                · simp only [Except.ok.injEq, Prod.mk.injEq] at h
                  omega

open Zip.Native in
/-- For compressed or treeless literals (types 2-3), the returned position advances. -/
theorem parseLiteralsSection_pos_gt_compressed (data : ByteArray) (pos : Nat)
    (prevHuffTree : Option ZstdHuffmanTable)
    (literals : ByteArray) (pos' : Nat) (huffTable : Option ZstdHuffmanTable)
    (hlit : (data[pos]! &&& 3).toNat ≥ 2)
    (h : parseLiteralsSection data pos prevHuffTree = .ok (literals, pos', huffTable)) :
    pos' > pos := by
  simp only [parseLiteralsSection, bind, Except.bind, pure, Except.pure] at h
  split at h
  · exact nomatch h
  · -- data.size ≥ pos + 1
    split at h
    · exact nomatch h
    · -- litType ≤ 3
      split at h
      · -- Compressed/treeless path (litType == 2 || litType == 3)
        -- bind result of parseCompressedLiteralsHeader: error vs ok
        split at h
        · exact nomatch h
        · -- parseCompressedLiteralsHeader succeeded; headerBytes ≥ 3
          rename_i v heq
          obtain ⟨regen, comp, hdr, fs⟩ := v
          have hge := parseCompressedLiteralsHeader_headerBytes_ge data pos _ _ _ _ _ heq
          -- litType == 3 check
          split at h
          · -- treeless (type 3)
            split at h
            · -- prevHuffTree = some t
              split at h
              · exact nomatch h -- data too small
              · -- decodeHuffmanLiterals result
                split at h
                · exact nomatch h
                · simp only [Except.ok.injEq, Prod.mk.injEq] at h; omega
            · exact nomatch h -- no previous Huffman tree (prevHuffTree = none)
          · -- compressed (type 2)
            split at h
            · exact nomatch h -- data too small
            · -- parseHuffmanTreeDescriptor result via mapError
              split at h
              · exact nomatch h
              · -- treeSize check
                split at h
                · exact nomatch h
                · -- decodeHuffmanLiterals result via mapError
                  split at h
                  · exact nomatch h
                  · simp only [Except.ok.injEq, Prod.mk.injEq] at h; omega
      · -- Raw/RLE path: contradicts hlit
        rename_i hle3 hnotcomp
        simp only [beq_iff_eq, Bool.or_eq_true, not_or] at hnotcomp
        omega

open Zip.Native in
/-- For all literal types (0-3), the returned position advances. -/
theorem parseLiteralsSection_pos_gt (data : ByteArray) (pos : Nat)
    (prevHuffTree : Option ZstdHuffmanTable)
    (literals : ByteArray) (pos' : Nat) (huffTable : Option ZstdHuffmanTable)
    (h : parseLiteralsSection data pos prevHuffTree = .ok (literals, pos', huffTable)) :
    pos' > pos := by
  by_cases hlit : (data[pos]! &&& 3).toNat ≤ 1
  · exact parseLiteralsSection_pos_gt_simple data pos prevHuffTree literals pos' huffTable hlit h
  · exact parseLiteralsSection_pos_gt_compressed data pos prevHuffTree literals pos' huffTable
      (by omega) h

/-! ## parseLiteralsSection le_size properties -/

open Zip.Native in
/-- For compressed or treeless literals (types 2-3), the returned position stays within
    `data.size`. The bounds check `data.size < afterHeader + compSize → throw` ensures
    `pos' = afterHeader + compSize ≤ data.size` on success. -/
theorem parseLiteralsSection_le_size_compressed (data : ByteArray) (pos : Nat)
    (prevHuffTree : Option ZstdHuffmanTable)
    (literals : ByteArray) (pos' : Nat) (huffTable : Option ZstdHuffmanTable)
    (hlit : (data[pos]! &&& 3).toNat ≥ 2)
    (h : parseLiteralsSection data pos prevHuffTree = .ok (literals, pos', huffTable)) :
    pos' ≤ data.size := by
  simp only [parseLiteralsSection, bind, Except.bind, pure, Except.pure] at h
  split at h
  · exact nomatch h
  · -- data.size ≥ pos + 1
    split at h
    · exact nomatch h
    · -- litType ≤ 3
      split at h
      · -- Compressed/treeless path (litType == 2 || litType == 3)
        -- bind result of parseCompressedLiteralsHeader: error vs ok
        split at h
        · exact nomatch h
        · -- parseCompressedLiteralsHeader succeeded
          rename_i v heq
          obtain ⟨regen, comp, hdr, fs⟩ := v
          -- litType == 3 check
          split at h
          · -- treeless (type 3)
            split at h
            · -- prevHuffTree = some t
              split at h
              · exact nomatch h -- data too small
              · -- decodeHuffmanLiterals result
                split at h
                · exact nomatch h
                · simp only [Except.ok.injEq, Prod.mk.injEq] at h; omega
            · exact nomatch h -- no previous Huffman tree (prevHuffTree = none)
          · -- compressed (type 2)
            split at h
            · exact nomatch h -- data too small
            · -- parseHuffmanTreeDescriptor result via mapError
              split at h
              · exact nomatch h
              · -- treeSize check
                split at h
                · exact nomatch h
                · -- decodeHuffmanLiterals result via mapError
                  split at h
                  · exact nomatch h
                  · simp only [Except.ok.injEq, Prod.mk.injEq] at h; omega
      · -- Raw/RLE path: contradicts hlit
        rename_i hle3 hnotcomp
        simp only [beq_iff_eq, Bool.or_eq_true, not_or] at hnotcomp
        omega

open Zip.Native in
/-- For all literal types (0-3), the returned position stays within `data.size`. -/
theorem parseLiteralsSection_le_size (data : ByteArray) (pos : Nat)
    (prevHuffTree : Option ZstdHuffmanTable)
    (literals : ByteArray) (pos' : Nat) (huffTable : Option ZstdHuffmanTable)
    (h : parseLiteralsSection data pos prevHuffTree = .ok (literals, pos', huffTable)) :
    pos' ≤ data.size := by
  by_cases hlit : (data[pos]! &&& 3).toNat ≤ 1
  · exact parseLiteralsSection_le_size_simple data pos prevHuffTree literals pos' huffTable hlit h
  · exact parseLiteralsSection_le_size_compressed data pos prevHuffTree literals pos' huffTable
      (by omega) h

/-! ## parseHuffmanTreeDescriptor position properties -/

open Zip.Native in
/-- When `parseHuffmanWeightsDirect` succeeds, the returned position equals
    `pos + (numWeights + 1) / 2`. -/
private theorem parseHuffmanWeightsDirect_pos_eq (data : ByteArray) (pos numWeights : Nat)
    (weights : Array UInt8) (pos' : Nat)
    (h : parseHuffmanWeightsDirect data pos numWeights = .ok (weights, pos')) :
    pos' = pos + (numWeights + 1) / 2 := by
  simp only [parseHuffmanWeightsDirect, bind, Except.bind] at h
  split at h
  · exact nomatch h
  · split at h
    · exact nomatch h
    · simp only [pure, Pure.pure, Except.pure] at h
      split at h
      · exact nomatch h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        exact h.2.symm

open Zip.Native in
/-- When `parseHuffmanWeightsFse` succeeds, the returned position equals
    `pos + 1 + compressedSize`. -/
private theorem parseHuffmanWeightsFse_pos_eq (data : ByteArray) (pos compressedSize : Nat)
    (weights : Array UInt8) (pos' : Nat)
    (h : parseHuffmanWeightsFse data pos compressedSize = .ok (weights, pos')) :
    pos' = pos + 1 + compressedSize := by
  simp only [parseHuffmanWeightsFse, bind, Except.bind] at h
  split at h
  · exact nomatch h
  · -- decodeFseDistribution
    split at h
    · exact nomatch h
    · -- buildFseTable
      split at h
      · exact nomatch h
      · -- BackwardBitReader.init
        split at h
        · exact nomatch h
        · -- decodeFseSymbolsAll
          split at h
          · exact nomatch h
          · split at h
            · exact nomatch h
            · obtain ⟨-, rfl⟩ := h
              rfl

open Zip.Native in
/-- When `parseHuffmanWeightsDirect` succeeds, the returned position is within
    the data bounds: `pos' ≤ data.size`. -/
theorem parseHuffmanWeightsDirect_le_size (data : ByteArray) (pos numWeights : Nat)
    (weights : Array UInt8) (pos' : Nat)
    (h : parseHuffmanWeightsDirect data pos numWeights = .ok (weights, pos')) :
    pos' ≤ data.size := by
  have hpos := parseHuffmanWeightsDirect_pos_eq data pos numWeights weights pos' h
  simp only [parseHuffmanWeightsDirect, bind, Except.bind] at h
  split at h
  · exact nomatch h
  · rename_i hle
    rw [hpos]; omega

open Zip.Native in
/-- When `parseHuffmanWeightsFse` succeeds, the returned position is within
    the data bounds: `pos' ≤ data.size`. -/
private theorem parseHuffmanWeightsFse_le_size (data : ByteArray) (pos compressedSize : Nat)
    (weights : Array UInt8) (pos' : Nat)
    (h : parseHuffmanWeightsFse data pos compressedSize = .ok (weights, pos')) :
    pos' ≤ data.size := by
  have hpos := parseHuffmanWeightsFse_pos_eq data pos compressedSize weights pos' h
  simp only [parseHuffmanWeightsFse, bind, Except.bind] at h
  split at h
  · exact nomatch h
  · rename_i hle
    rw [hpos]; omega

open Zip.Native in
/-- When `parseHuffmanTreeDescriptor` succeeds, the returned position is at least
    `pos + 2` (1 header byte + at least 1 data byte). -/
theorem parseHuffmanTreeDescriptor_pos_ge_two (data : ByteArray) (pos : Nat)
    (table : ZstdHuffmanTable) (pos' : Nat)
    (h : parseHuffmanTreeDescriptor data pos = .ok (table, pos')) :
    pos' ≥ pos + 2 := by
  simp only [parseHuffmanTreeDescriptor, bind, Except.bind] at h
  -- Size guard
  by_cases h1 : data.size < pos + 1
  · simp [h1] at h
  · rw [if_neg h1] at h; simp only [pure, Pure.pure, Except.pure] at h
    -- headerByte >= 128 check
    by_cases h2 : data[pos]!.toNat ≥ 128
    · rw [if_pos h2] at h
      -- parseHuffmanWeightsDirect bind
      cases hwd : parseHuffmanWeightsDirect data (pos + 1) (data[pos]!.toNat - 127) with
      | error e => simp only [hwd] at h; exact nomatch h
      | ok v =>
        rw [hwd] at h; dsimp only [Bind.bind, Except.bind] at h
        cases hbt : buildZstdHuffmanTable v.fst with
        | error e => simp only [hbt] at h; exact nomatch h
        | ok t =>
          rw [hbt] at h; dsimp only [pure, Pure.pure, Except.pure] at h
          have hpos := parseHuffmanWeightsDirect_pos_eq data (pos + 1)
            (data[pos]!.toNat - 127) v.fst v.snd hwd
          obtain ⟨-, rfl⟩ := h
          rw [hpos]; omega
    · rw [if_neg (show ¬data[pos]!.toNat ≥ 128 from h2)] at h
      -- headerByte == 0 check
      by_cases h3 : (data[pos]!.toNat == 0) = true
      · simp [h3] at h
      · rw [if_neg h3] at h
        cases hfse : parseHuffmanWeightsFse data pos data[pos]!.toNat with
        | error e => simp only [hfse] at h; exact nomatch h
        | ok v =>
          rw [hfse] at h; dsimp only [Bind.bind, Except.bind] at h
          cases hbt : buildZstdHuffmanTable v.fst with
          | error e => simp only [hbt] at h; exact nomatch h
          | ok t =>
            rw [hbt] at h; dsimp only [pure, Pure.pure, Except.pure] at h
            have hpos := parseHuffmanWeightsFse_pos_eq data pos
              data[pos]!.toNat v.fst v.snd hfse
            obtain ⟨-, rfl⟩ := h
            rw [hpos]; simp only [beq_iff_eq] at h3; omega

open Zip.Native in
/-- When `parseHuffmanTreeDescriptor` succeeds, the returned position is strictly
    greater than the input position. -/
theorem parseHuffmanTreeDescriptor_pos_gt (data : ByteArray) (pos : Nat)
    (table : ZstdHuffmanTable) (pos' : Nat)
    (h : parseHuffmanTreeDescriptor data pos = .ok (table, pos')) :
    pos' > pos := by
  have := parseHuffmanTreeDescriptor_pos_ge_two data pos table pos' h
  omega

open Zip.Native in
/-- When `parseHuffmanTreeDescriptor` succeeds, the returned position is within
    the data bounds: `pos' ≤ data.size`. -/
theorem parseHuffmanTreeDescriptor_le_size (data : ByteArray) (pos : Nat)
    (table : ZstdHuffmanTable) (pos' : Nat)
    (h : parseHuffmanTreeDescriptor data pos = .ok (table, pos')) :
    pos' ≤ data.size := by
  simp only [parseHuffmanTreeDescriptor, bind, Except.bind] at h
  -- Size guard
  by_cases h1 : data.size < pos + 1
  · simp [h1] at h
  · rw [if_neg h1] at h; simp only [pure, Pure.pure, Except.pure] at h
    -- headerByte >= 128 check
    by_cases h2 : data[pos]!.toNat ≥ 128
    · rw [if_pos h2] at h
      -- parseHuffmanWeightsDirect bind
      cases hwd : parseHuffmanWeightsDirect data (pos + 1) (data[pos]!.toNat - 127) with
      | error e => simp only [hwd] at h; exact nomatch h
      | ok v =>
        rw [hwd] at h; dsimp only [Bind.bind, Except.bind] at h
        cases hbt : buildZstdHuffmanTable v.fst with
        | error e => simp only [hbt] at h; exact nomatch h
        | ok t =>
          rw [hbt] at h; dsimp only [pure, Pure.pure, Except.pure] at h
          obtain ⟨-, rfl⟩ := h
          exact parseHuffmanWeightsDirect_le_size data (pos + 1)
            (data[pos]!.toNat - 127) v.fst v.snd hwd
    · rw [if_neg (show ¬data[pos]!.toNat ≥ 128 from h2)] at h
      -- headerByte == 0 check
      by_cases h3 : (data[pos]!.toNat == 0) = true
      · simp [h3] at h
      · rw [if_neg h3] at h
        cases hfse : parseHuffmanWeightsFse data pos data[pos]!.toNat with
        | error e => simp only [hfse] at h; exact nomatch h
        | ok v =>
          rw [hfse] at h; dsimp only [Bind.bind, Except.bind] at h
          cases hbt : buildZstdHuffmanTable v.fst with
          | error e => simp only [hbt] at h; exact nomatch h
          | ok t =>
            rw [hbt] at h; dsimp only [pure, Pure.pure, Except.pure] at h
            obtain ⟨-, rfl⟩ := h
            exact parseHuffmanWeightsFse_le_size data pos
              data[pos]!.toNat v.fst v.snd hfse

/-! ## decodeHuffmanSymbol properties -/

open Zip.Native in
/-- When `decodeHuffmanSymbol` succeeds, the bit budget does not increase.
    This is the key monotonicity property for proving termination of
    Huffman stream decoding. -/
theorem decodeHuffmanSymbol_totalBitsRemaining_le
    (htable : ZstdHuffmanTable) (br : BackwardBitReader)
    (sym : UInt8) (br' : BackwardBitReader)
    (h : decodeHuffmanSymbol htable br = .ok (sym, br')) :
    br'.totalBitsRemaining ≤ br.totalBitsRemaining := by
  simp only [decodeHuffmanSymbol, bind, Except.bind] at h
  -- if peekBits == 0
  split at h; · exact nomatch h
  -- first readBits (peek): cases on result
  cases hrd1 : br.readBits (min htable.maxBits br.totalBitsRemaining) with
  | error => simp only [hrd1] at h; exact nomatch h
  | ok v1 =>
    obtain ⟨bits1, br1⟩ := v1
    rw [hrd1] at h
    simp only [pure, Pure.pure, Except.pure] at h
    -- if numBits > avail
    split at h; · exact nomatch h
    -- second readBits
    split at h; · exact nomatch h
    -- ok case: extract reader equation
    rename_i v2 hrd2
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    have := Zstd.Spec.Fse.readBits_totalBitsRemaining_sub br _ _ _ hrd2
    omega

open Zip.Native in
/-- The number of bits consumed is at most `maxBits`, given the table is
    well-formed (all entries have `numBits ≤ maxBits`). This bounds per-symbol
    cost and is needed for proving that stream decoding terminates within
    the available bit budget. -/
theorem decodeHuffmanSymbol_bits_le_maxBits
    (htable : ZstdHuffmanTable) (br : BackwardBitReader)
    (sym : UInt8) (br' : BackwardBitReader)
    (hvalid : ValidHuffmanTable htable.table htable.maxBits)
    (h : decodeHuffmanSymbol htable br = .ok (sym, br')) :
    br.totalBitsRemaining - br'.totalBitsRemaining ≤ htable.maxBits := by
  simp only [decodeHuffmanSymbol, bind, Except.bind] at h
  split at h; · exact nomatch h
  cases hrd1 : br.readBits (min htable.maxBits br.totalBitsRemaining) with
  | error => simp only [hrd1] at h; exact nomatch h
  | ok v1 =>
    obtain ⟨bits1, br1⟩ := v1
    rw [hrd1] at h
    simp only [pure, Pure.pure, Except.pure] at h
    split at h; · exact nomatch h
    split at h; · exact nomatch h
    rename_i v2 hrd2
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    have hsub := Zstd.Spec.Fse.readBits_totalBitsRemaining_sub br _ _ _ hrd2
    rw [hsub]
    -- Need: numBits ≤ maxBits from ValidHuffmanTable
    have h_nb_le : htable.table[bits1.toNat <<< (htable.maxBits - min htable.maxBits br.totalBitsRemaining)]!.numBits.toNat ≤ htable.maxBits := by
      let idx := bits1.toNat <<< (htable.maxBits - min htable.maxBits br.totalBitsRemaining)
      show htable.table[idx]!.numBits.toNat ≤ htable.maxBits
      simp only [getElem!_def]
      split
      · rename_i e he
        obtain ⟨hi, heq⟩ := Array.getElem?_eq_some_iff.mp he
        rw [← heq]
        exact hvalid.2.1 ⟨idx, hi⟩
      · have : (default : HuffmanEntry).numBits.toNat = 0 := by decide
        omega
    omega

open Zip.Native in
/-- If decoding succeeds, the input reader had bits remaining. This is the
    contrapositive of the `peekBits == 0` error check. -/
theorem decodeHuffmanSymbol_totalBitsRemaining_pos
    (htable : ZstdHuffmanTable) (br : BackwardBitReader)
    (sym : UInt8) (br' : BackwardBitReader)
    (h : decodeHuffmanSymbol htable br = .ok (sym, br')) :
    br.totalBitsRemaining > 0 := by
  simp only [decodeHuffmanSymbol, bind, Except.bind] at h
  split at h
  · exact nomatch h
  · rename_i hpb
    simp only [beq_iff_eq] at hpb
    omega

end Zstd.Spec.Huffman
