import Zip.Native.ZstdHuffman

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

/-! ## Correctness theorems -/

/-- When `buildZstdHuffmanTable` succeeds, the resulting table has size
    `1 << maxBits`.  This follows from the `Array.replicate tableSize default`
    initialization where `tableSize = 1 << maxBits`, and the subsequent
    `set!` operations preserve the array size. -/
theorem buildZstdHuffmanTable_tableSize (weights : Array UInt8)
    (result : ZstdHuffmanTable)
    (h : Zip.Native.buildZstdHuffmanTable weights = .ok result) :
    result.table.size = 1 <<< result.maxBits := by
  sorry

/-- When `buildZstdHuffmanTable` succeeds, `maxBits ≥ 1`.  This follows
    from `weightsToMaxBits` requiring at least one non-zero weight, so
    `weightSum ≥ 1`, meaning `maxBits ≥ 1`. -/
theorem buildZstdHuffmanTable_maxBits_pos (weights : Array UInt8)
    (result : ZstdHuffmanTable)
    (h : Zip.Native.buildZstdHuffmanTable weights = .ok result) :
    result.maxBits ≥ 1 := by
  sorry

/-- When `weightsToMaxBits` succeeds with result `m`, the weight sum
    satisfies `2^(m-1) < weightSum ≤ 2^m` (except when `weightSum` is
    exactly a power of 2, in which case `m` is bumped by 1).

    More precisely: `weightSum weights > 0 ∧ weightSum weights ≤ 2^(m-1)`,
    since `m` is chosen so that `2^(m-1)` is the first power ≥ `weightSum`,
    and if equality holds, `m` is incremented by 1 to accommodate the
    implicit last symbol. -/
theorem weightsToMaxBits_valid (weights : Array UInt8)
    (m : Nat)
    (h : Zip.Native.weightsToMaxBits weights = .ok m) :
    weightSum weights > 0 ∧ weightSum weights ≤ 1 <<< (m - 1) := by
  sorry

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

end Zstd.Spec.Huffman
