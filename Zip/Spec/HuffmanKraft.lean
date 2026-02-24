import Zip.Spec.Huffman
import ZipForStd.List

/-!
# Kraft Inequality Analysis for Canonical Huffman Codes

Infrastructure for the Kraft inequality proof: `kraftSumFrom`, `ncRec`
(the nextCodes recurrence), conservation laws, and the bound
`ncRec b + blCount[b]! ≤ 2^b`. These underpin the prefix-free and
injectivity theorems in `HuffmanTheorems.lean`.

Definitions and types are in `Zip.Spec.Huffman`.
-/

namespace Huffman.Spec

/-! ## Kraft inequality helper lemmas -/

/-- The Kraft sum over a list is at least the contribution from elements equal to `len`. -/
private theorem kraft_ge_count (ls : List Nat) (maxBits len : Nat) :
    (ls.filter (· == len)).length * 2 ^ (maxBits - len) ≤
    ls.foldl (fun acc l => acc + 2 ^ (maxBits - l)) 0 := by
  induction ls with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, Nat.zero_add]
    rw [List.foldl_add_init]
    simp only [List.filter_cons]
    cases hxl : x == len
    · exact Nat.le_trans ih (Nat.le_add_left _ _)
    · have hxeq : x = len := beq_iff_eq.mp hxl
      subst hxeq
      simp only [ite_true, List.length_cons, Nat.succ_mul]; omega

/-- Double filter: `(· != 0)` then `(· == len)` is the same as `(· == len)` when `len > 0`. -/
private theorem filter_ne_zero_filter_eq (ls : List Nat) (len : Nat) (hlen : len ≠ 0) :
    (ls.filter (· != 0)).filter (· == len) = ls.filter (· == len) := by
  rw [List.filter_filter]; congr 1; ext x
  by_cases h : x = len <;> simp [bne_iff_ne, beq_iff_eq, h, hlen]

/-- In a valid length assignment, the count of codes with a given non-zero length
    is at most `2^len`. -/
theorem count_le_pow_of_validLengths (lengths : List Nat) (maxBits len : Nat)
    (hv : ValidLengths lengths maxBits) (hlen : len ≠ 0) (hlen' : len ≤ maxBits) :
    (lengths.filter (· == len)).length ≤ 2 ^ len := by
  have hkraft := hv.2
  have hcount := kraft_ge_count (lengths.filter (· != 0)) maxBits len
  rw [filter_ne_zero_filter_eq lengths len hlen] at hcount
  have hle := Nat.le_trans hcount hkraft
  have hpow_eq : 2 ^ maxBits = 2 ^ len * 2 ^ (maxBits - len) := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [hpow_eq] at hle
  exact Nat.le_of_mul_le_mul_right hle (Nat.pow_pos (by omega))

/-! ## Helper definitions for nextCodes analysis -/

/-- Simple recursive definition of the nextCodes recurrence:
    `ncRec blCount 0 = 0`, `ncRec blCount (b+1) = (ncRec blCount b + blCount[b]!) * 2`.
    This matches what `nextCodes.go` computes at each step. -/
protected def ncRec (blCount : Array Nat) : Nat → Nat
  | 0 => 0
  | b + 1 => (Huffman.Spec.ncRec blCount b + blCount[b]!) * 2

/-- Partial Kraft sum from position `start` to `maxBits`:
    `∑_{i=start}^{maxBits} blCount[i]! * 2^(maxBits - i)`. -/
private def kraftSumFrom (blCount : Array Nat) (maxBits b : Nat) : Nat :=
  if b > maxBits then 0
  else blCount[b]! * 2 ^ (maxBits - b) + kraftSumFrom blCount maxBits (b + 1)
termination_by maxBits + 1 - b

/-! ## Conservation law: ncRec and kraftSumFrom -/

/-- Unfolding lemma for `kraftSumFrom` when `b ≤ maxBits`. -/
private theorem kraftSumFrom_unfold (blCount : Array Nat) (maxBits b : Nat) (hb : b ≤ maxBits) :
    kraftSumFrom blCount maxBits b =
      blCount[b]! * 2 ^ (maxBits - b) + kraftSumFrom blCount maxBits (b + 1) := by
  rw [kraftSumFrom.eq_1]; exact if_neg (by omega)

/-- `kraftSumFrom` past `maxBits` is zero. -/
private theorem kraftSumFrom_gt (blCount : Array Nat) (maxBits b : Nat) (hb : b > maxBits) :
    kraftSumFrom blCount maxBits b = 0 := by
  rw [kraftSumFrom.eq_1]; exact if_pos hb

/-- Conservation law: `ncRec b * 2^(maxBits-b) + kraftSumFrom b = kraftSumFrom 0`.
    The nextCodes recurrence preserves the total Kraft sum. -/
private theorem ncRec_kraft_conservation (blCount : Array Nat) (maxBits b : Nat)
    (hb : b ≤ maxBits) :
    Huffman.Spec.ncRec blCount b * 2 ^ (maxBits - b) + kraftSumFrom blCount maxBits b =
      kraftSumFrom blCount maxBits 0 := by
  induction b with
  | zero => simp [Huffman.Spec.ncRec]
  | succ n ih =>
    have ih' := ih (by omega)
    rw [kraftSumFrom_unfold blCount maxBits n (by omega)] at ih'
    show (Huffman.Spec.ncRec blCount n + blCount[n]!) * 2 * 2 ^ (maxBits - (n + 1)) +
      kraftSumFrom blCount maxBits (n + 1) = kraftSumFrom blCount maxBits 0
    have : 2 * 2 ^ (maxBits - (n + 1)) = 2 ^ (maxBits - n) := by
      rw [show maxBits - n = (maxBits - (n + 1)) + 1 from by omega, Nat.pow_succ, Nat.mul_comm]
    rw [Nat.mul_assoc, this, Nat.add_mul]
    omega

/-! ## Connecting kraftSumFrom to ValidLengths -/

/-- `Array.set!` at a different index doesn't affect the target index. -/
private theorem array_set_ne (arr : Array Nat) (i j v : Nat) (hij : i ≠ j) :
    (arr.set! i v)[j]! = arr[j]! := by
  simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
        Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne hij]

/-- `Array.set!` at the same index replaces the value. -/
private theorem array_set_self (arr : Array Nat) (i v : Nat) (hi : i < arr.size) :
    (arr.set! i v)[i]! = v := by
  simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
        Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt hi]

/-- `Array.set!` preserves the size. -/
private theorem array_set_size (arr : Array Nat) (i v : Nat) :
    (arr.set! i v).size = arr.size := by
  simp [Array.set!_eq_setIfInBounds]

/-- `countLengths[b]!` counts elements of `lengths` equal to `b`, for valid `b`. -/
protected theorem countLengths_eq (lengths : List Nat) (maxBits b : Nat)
    (hb : b ≠ 0) (hb' : b ≤ maxBits) :
    (countLengths lengths maxBits)[b]! =
      lengths.foldl (fun acc l => if (l == b) = true then acc + 1 else acc) 0 := by
  simp only [countLengths]
  suffices ∀ (acc : Array Nat), acc.size = maxBits + 1 →
      (lengths.foldl (fun acc len =>
        if len == 0 || len > maxBits then acc
        else acc.set! len (acc[len]! + 1)) acc)[b]! =
      acc[b]! + lengths.foldl (fun acc l => if (l == b) = true then acc + 1 else acc) 0 by
    rw [this _ (Array.size_replicate ..)]
    suffices h : (Array.replicate (maxBits + 1) 0)[b]! = 0 by omega
    simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
               Array.getElem?_replicate]; split <;> rfl
  intro acc hsize
  induction lengths generalizing acc with
  | nil => simp
  | cons l ls ih =>
    simp only [List.foldl_cons]
    split
    · rename_i hskip
      rw [ih acc hsize]; congr 1
      have hlb : (l == b) = false := by
        simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hskip
        cases hskip with
        | inl h => exact beq_eq_false_iff_ne.mpr (h ▸ Ne.symm hb)
        | inr h => exact beq_eq_false_iff_ne.mpr (fun heq => by rw [heq] at h; omega)
      simp [hlb]
    · rename_i hset
      simp only [Bool.or_eq_true, beq_iff_eq, not_or, decide_eq_true_eq] at hset
      have hl_ne : l ≠ 0 := hset.1
      have hl_le : l ≤ maxBits := by omega
      have hsize' : (acc.set! l (acc[l]! + 1)).size = maxBits + 1 := by
        rw [array_set_size]; exact hsize
      rw [ih _ hsize']
      cases Nat.decEq l b with
      | isTrue heq =>
        subst heq
        rw [array_set_self acc l _ (by omega)]
        simp only [beq_self_eq_true, ite_true, Nat.zero_add]
        rw [List.foldl_count_init l 1]; omega
      | isFalse hne =>
        rw [array_set_ne acc l b _ hne]
        simp only [beq_eq_false_iff_ne.mpr hne, ite_false, Bool.false_eq_true]

/-- `nextCodes.go` produces `ncRec` values: the `code` parameter at entry with
    `bits = b` becomes `ncRec blCount b` after the body executes. -/
private theorem nextCodes_go_eq_ncRec (blCount : Array Nat) (maxBits : Nat)
    (arr : Array Nat) (bits code : Nat)
    (hsize : arr.size = maxBits + 1)
    (hbits : 1 ≤ bits) (hbitsM : bits ≤ maxBits + 1)
    (hcode : code = Huffman.Spec.ncRec blCount (bits - 1))
    (hprev : ∀ b, 1 ≤ b → b < bits → arr[b]! = Huffman.Spec.ncRec blCount b)
    (b : Nat) (hb : 1 ≤ b) (hbM : b ≤ maxBits) :
    (nextCodes.go blCount maxBits arr bits code)[b]! = Huffman.Spec.ncRec blCount b := by
  unfold nextCodes.go
  split
  · exact hprev b hb (by omega)
  · rename_i hle
    have hle' : bits ≤ maxBits := by omega
    let code' := (code + blCount[bits - 1]!) * 2
    let arr' := arr.set! bits code'
    have hsize' : arr'.size = maxBits + 1 := by
      simp only [arr', array_set_size]; exact hsize
    have hcode' : code' = Huffman.Spec.ncRec blCount bits := by
      simp only [code', hcode]
      cases bits with
      | zero => omega
      | succ n => simp [Huffman.Spec.ncRec]
    have hprev' : ∀ b', 1 ≤ b' → b' < bits + 1 → arr'[b']! = Huffman.Spec.ncRec blCount b' := by
      intro b' hb' hb'lt
      cases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hb'lt) with
      | inl heq =>
        rw [heq]; simp only [arr']
        rw [array_set_self arr bits code' (by omega)]
        exact hcode'
      | inr hlt =>
        simp only [arr']
        rw [array_set_ne arr bits b' code' (by omega)]
        exact hprev b' hb' hlt
    exact nextCodes_go_eq_ncRec blCount maxBits arr' (bits + 1) code'
      hsize' (by omega) (by omega) hcode' hprev' b hb hbM

/-- The nextCodes array stores ncRec values at each position. -/
protected theorem nextCodes_eq_ncRec (blCount : Array Nat) (maxBits b : Nat)
    (hb : b ≠ 0) (hbM : b ≤ maxBits) :
    (nextCodes blCount maxBits)[b]! = Huffman.Spec.ncRec blCount b := by
  simp only [nextCodes]
  exact nextCodes_go_eq_ncRec blCount maxBits _ 1 0
    (Array.size_replicate ..) (by omega) (by omega) (by simp [Huffman.Spec.ncRec])
    (fun b' hb' hlt => by omega) b (by omega) hbM

/-- Incrementing one count at index `l` adds `2^(maxBits-l)` to the Kraft sum
    from positions ≤ l, and doesn't affect positions > l. -/
private theorem kraftSumFrom_incr (acc : Array Nat) (maxBits l b : Nat)
    (hl : l ≤ maxBits) (hsize : acc.size ≥ maxBits + 1) :
    kraftSumFrom (acc.set! l (acc[l]! + 1)) maxBits b =
      kraftSumFrom acc maxBits b + if b ≤ l then 2 ^ (maxBits - l) else 0 := by
  if hb : b > maxBits then
    simp [kraftSumFrom_gt _ _ _ hb, show ¬(b ≤ l) from by omega]
  else
    have hb' : b ≤ maxBits := by omega
    rw [kraftSumFrom_unfold _ _ _ hb', kraftSumFrom_unfold _ _ _ hb']
    if hbl : b = l then
      subst hbl
      rw [array_set_self acc b _ (by omega)]
      have ih := kraftSumFrom_incr acc maxBits b (b + 1) hl hsize
      simp only [show ¬(b + 1 ≤ b) from by omega, ite_false, Nat.add_zero] at ih
      rw [ih]; simp only [show b ≤ b from Nat.le_refl _, ite_true]
      rw [Nat.add_mul]; omega
    else
      rw [array_set_ne acc l b _ (by exact fun h => hbl h.symm)]
      have ih := kraftSumFrom_incr acc maxBits l (b + 1) hl hsize
      rw [ih]
      if hbl' : b ≤ l then
        simp only [hbl', show b + 1 ≤ l from by omega, ite_true]; omega
      else
        simp only [hbl', show ¬(b + 1 ≤ l) from by omega, ite_false, Nat.add_zero]
termination_by maxBits + 1 - b

/-- `kraftSumFrom` over an all-zeros array is 0. -/
private theorem kraftSumFrom_replicate (maxBits b : Nat) :
    kraftSumFrom (Array.replicate (maxBits + 1) 0) maxBits b = 0 := by
  if hb : b > maxBits then
    exact kraftSumFrom_gt _ _ _ hb
  else
    rw [kraftSumFrom_unfold _ _ _ (by omega)]
    have : (Array.replicate (maxBits + 1) 0)[b]! = 0 := by
      simp [show b < maxBits + 1 from by omega]
    rw [this, Nat.zero_mul, Nat.zero_add]
    exact kraftSumFrom_replicate maxBits (b + 1)
termination_by maxBits + 1 - b

/-- `ValidLengths` is preserved when removing the head element. -/
protected theorem validLengths_cons {l : Nat} {ls : List Nat} {maxBits : Nat}
    (hv : ValidLengths (l :: ls) maxBits) : ValidLengths ls maxBits := by
  constructor
  · exact fun x hx => hv.1 x (List.mem_cons_of_mem l hx)
  · have hf := hv.2
    simp only [List.filter_cons] at hf
    split at hf
    · simp only [List.foldl_cons, Nat.zero_add] at hf
      rw [List.foldl_add_init] at hf; exact Nat.le_trans (Nat.le_add_left _ _) hf
    · exact hf

/-- The full Kraft sum `kraftSumFrom 0` equals the Kraft sum in `ValidLengths`. -/
private theorem kraftSumFrom_eq_kraft_foldl (lengths : List Nat) (maxBits : Nat)
    (hv : ValidLengths lengths maxBits) :
    kraftSumFrom (countLengths lengths maxBits) maxBits 0 ≤ 2 ^ maxBits := by
  simp only [countLengths]
  suffices ∀ (acc : Array Nat), acc.size = maxBits + 1 →
      kraftSumFrom (lengths.foldl (fun acc len =>
        if len == 0 || len > maxBits then acc
        else acc.set! len (acc[len]! + 1)) acc) maxBits 0 =
      kraftSumFrom acc maxBits 0 +
      (lengths.filter (· != 0)).foldl (fun acc l => acc + 2 ^ (maxBits - l)) 0 by
    rw [this _ (Array.size_replicate ..)]
    rw [kraftSumFrom_replicate, Nat.zero_add]
    exact hv.2
  intro acc hsize
  induction lengths generalizing acc with
  | nil => simp
  | cons l ls ih =>
    have hv_ls := Huffman.Spec.validLengths_cons hv
    simp only [List.foldl_cons]
    split
    · rename_i hskip
      rw [ih hv_ls acc hsize]
      congr 1
      simp only [List.filter_cons]
      simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hskip
      cases hskip with
      | inl h => simp [h]
      | inr h => exfalso; exact Nat.not_lt.mpr (hv.1 l List.mem_cons_self) h
    · rename_i hset
      simp only [Bool.or_eq_true, beq_iff_eq, not_or, decide_eq_true_eq] at hset
      have hl_ne : l ≠ 0 := hset.1
      have hl_le : l ≤ maxBits := by omega
      have hsize' : (acc.set! l (acc[l]! + 1)).size = maxBits + 1 := by
        rw [array_set_size]; exact hsize
      rw [ih hv_ls (acc.set! l (acc[l]! + 1)) hsize']
      rw [kraftSumFrom_incr acc maxBits l 0 hl_le (by omega)]
      simp only [Nat.zero_le, ite_true]
      have hfilt : (l :: ls).filter (· != 0) = l :: ls.filter (· != 0) := by
        simp only [List.filter_cons]
        exact if_pos (bne_iff_ne.mpr hl_ne)
      rw [hfilt, List.foldl_cons, Nat.zero_add, Nat.add_assoc, ← List.foldl_add_init]

/-- The ncRec recurrence at higher bit lengths bounds from below by
    scaling the value at a lower length:
    `ncRec b₂ ≥ (ncRec b₁ + count[b₁]) * 2^(b₂ - b₁)`. -/
protected theorem ncRec_shift (blCount : Array Nat) (b₁ b₂ : Nat) (h : b₁ < b₂) :
    (Huffman.Spec.ncRec blCount b₁ + blCount[b₁]!) * 2 ^ (b₂ - b₁) ≤
      Huffman.Spec.ncRec blCount b₂ := by
  induction b₂ with
  | zero => omega
  | succ k ih =>
    simp only [Huffman.Spec.ncRec]
    cases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp h) with
    | inl hlt =>
      calc (Huffman.Spec.ncRec blCount b₁ + blCount[b₁]!) * 2 ^ (k + 1 - b₁)
          = ((Huffman.Spec.ncRec blCount b₁ + blCount[b₁]!) * 2 ^ (k - b₁)) * 2 := by
            rw [show k + 1 - b₁ = (k - b₁) + 1 from by omega, Nat.pow_succ, Nat.mul_assoc]
        _ ≤ Huffman.Spec.ncRec blCount k * 2 := Nat.mul_le_mul_right 2 (ih hlt)
        _ ≤ (Huffman.Spec.ncRec blCount k + blCount[k]!) * 2 :=
            Nat.mul_le_mul_right 2 (Nat.le_add_right _ _)
    | inr heq =>
      subst heq; simp

/-- The core ncRec bound: `ncRec blCount b + blCount[b]! ≤ 2^b` when the Kraft
    inequality holds for the full sum from 0. -/
private theorem ncRec_bound (blCount : Array Nat) (maxBits b : Nat)
    (hb : b ≤ maxBits)
    (hkraft : kraftSumFrom blCount maxBits 0 ≤ 2 ^ maxBits) :
    Huffman.Spec.ncRec blCount b + blCount[b]! ≤ 2 ^ b := by
  have hcons := ncRec_kraft_conservation blCount maxBits b hb
  rw [kraftSumFrom_unfold blCount maxBits b hb] at hcons
  have h1 : (Huffman.Spec.ncRec blCount b + blCount[b]!) * 2 ^ (maxBits - b) ≤ 2 ^ maxBits := by
    have : (Huffman.Spec.ncRec blCount b + blCount[b]!) * 2 ^ (maxBits - b) ≤
           kraftSumFrom blCount maxBits 0 := by rw [Nat.add_mul]; omega
    omega
  rw [show 2 ^ maxBits = 2 ^ b * 2 ^ (maxBits - b) from by
    rw [← Nat.pow_add]; congr 1; omega] at h1
  exact Nat.le_of_mul_le_mul_right h1 (Nat.pow_pos (by omega))

/-- The nextCodes construction ensures nc[b] + count[b] ≤ 2^b.
    This is the Kraft-based invariant of the canonical code construction:
    at each bit length b, the starting code plus the number of codes
    at that length doesn't exceed the code space. -/
protected theorem nextCodes_plus_count_le (lengths : List Nat) (maxBits b : Nat)
    (hv : ValidLengths lengths maxBits)
    (hb : b ≠ 0) (hb' : b ≤ maxBits) :
    (nextCodes (countLengths lengths maxBits) maxBits)[b]! +
      lengths.foldl (fun acc l => if (l == b) = true then acc + 1 else acc) 0 ≤ 2 ^ b := by
  let blCount := countLengths lengths maxBits
  have hNC := Huffman.Spec.nextCodes_eq_ncRec blCount maxBits b hb hb'
  have hCL : blCount[b]! =
      lengths.foldl (fun acc l => if (l == b) = true then acc + 1 else acc) 0 :=
    Huffman.Spec.countLengths_eq lengths maxBits b hb hb'
  have hKraft := kraftSumFrom_eq_kraft_foldl lengths maxBits hv
  rw [hNC, ← hCL]
  exact ncRec_bound blCount maxBits b hb' hKraft

end Huffman.Spec
