import Zip.Spec.Huffman

/-!
# Huffman Code Property Theorems

Property theorems for the canonical Huffman code construction:
Kraft inequality analysis, prefix-free proofs, injectivity,
and decode correctness.

Definitions and types are in `Zip.Spec.Huffman`.
-/

namespace Huffman.Spec

/-! ## natToBits prefix properties -/

/-- `natToBits val (w₁ + w₂)` splits into the high `w₁` bits
    (of `val / 2^w₂`) followed by the low `w₂` bits. -/
private theorem natToBits_append (val w₁ w₂ : Nat) :
    natToBits val (w₁ + w₂) = natToBits (val / 2 ^ w₂) w₁ ++ natToBits val w₂ := by
  induction w₁ with
  | zero => simp [natToBits]
  | succ n ih =>
    rw [Nat.add_right_comm]
    simp only [natToBits]
    rw [ih, List.cons_append, ← Nat.testBit_div_two_pow]

/-- If `natToBits a n` is a prefix of `natToBits b m` (`n ≤ m`, both values
    in range), then `b < (a + 1) * 2^(m - n)`.  This is the numerical
    consequence of one codeword being a prefix of another. -/
private theorem natToBits_prefix_lt (a b n m : Nat)
    (hnm : n ≤ m) (ha : a < 2 ^ n) (hb : b < 2 ^ m)
    (hpre : (natToBits a n).IsPrefix (natToBits b m)) :
    b < (a + 1) * 2 ^ (m - n) := by
  let d := m - n
  have hd_pos : 0 < 2 ^ d := Nat.two_pow_pos d
  have hm : m = n + d := by omega
  rw [hm, natToBits_append b n d] at hpre
  obtain ⟨t, ht⟩ := hpre
  have ⟨heq, _⟩ := List.append_inj ht (by simp [natToBits_length])
  have hdiv_bound : b / 2 ^ d < 2 ^ n := by
    rw [Nat.div_lt_iff_lt_mul hd_pos, ← Nat.pow_add]; rw [hm] at hb; exact hb
  have ha_eq : a = b / 2 ^ d := natToBits_injective a (b / 2 ^ d) n ha hdiv_bound heq
  have := Nat.lt_mul_div_succ b hd_pos
  rw [ha_eq, Nat.mul_comm]; exact this

/-! ## Prefix comparison lemmas -/

/-- Two prefixes of the same list are comparable: one is a prefix of the other. -/
private theorem IsPrefix_dichotomy {a b c : List Bool}
    (ha : a <+: b ++ c) : a <+: b ∨ b <+: a := by
  induction a generalizing b with
  | nil => left; exact List.nil_prefix
  | cons x xs ih =>
    cases b with
    | nil => right; exact List.nil_prefix
    | cons y ys =>
      obtain ⟨t, ht⟩ := ha
      have hxy : x = y := by simp [List.cons_append] at ht; exact ht.1
      have hrest : xs <+: ys ++ c :=
        ⟨t, by simp [List.cons_append] at ht; exact ht.2⟩
      cases ih hrest with
      | inl h =>
        left; obtain ⟨t', ht'⟩ := h
        exact ⟨t', by rw [hxy, List.cons_append, ht']⟩
      | inr h =>
        right; obtain ⟨t', ht'⟩ := h
        exact ⟨t', by rw [← hxy, List.cons_append, ht']⟩

/-- `isPrefixOf` returns true for a list prepended to any suffix. -/
private theorem isPrefixOf_self_append (cw rest : List Bool) :
    isPrefixOf cw (cw ++ rest) = true := by
  induction cw with
  | nil => simp [isPrefixOf]
  | cons x xs ih => simp [isPrefixOf, ih]

/-! ## Kraft inequality helper lemmas -/

private theorem foldl_add_init (f : Nat → Nat) (init : Nat) (ls : List Nat) :
    ls.foldl (fun acc l => acc + f l) init = init + ls.foldl (fun acc l => acc + f l) 0 := by
  induction ls generalizing init with
  | nil => simp
  | cons x xs ih => simp only [List.foldl_cons, Nat.zero_add]; rw [ih, ih (f x)]; omega

private theorem foldl_count_init (b : Nat) (init : Nat) (ls : List Nat) :
    ls.foldl (fun acc l => if (l == b) = true then acc + 1 else acc) init =
      init + ls.foldl (fun acc l => if (l == b) = true then acc + 1 else acc) 0 := by
  induction ls generalizing init with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, Nat.zero_add]
    split
    · rw [ih, ih 1]; omega
    · exact ih init

/-- The Kraft sum over a list is at least the contribution from elements equal to `len`. -/
private theorem kraft_ge_count (ls : List Nat) (maxBits len : Nat) :
    (ls.filter (· == len)).length * 2 ^ (maxBits - len) ≤
    ls.foldl (fun acc l => acc + 2 ^ (maxBits - l)) 0 := by
  induction ls with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, Nat.zero_add]
    rw [foldl_add_init]
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
private def ncRec (blCount : Array Nat) : Nat → Nat
  | 0 => 0
  | b + 1 => (ncRec blCount b + blCount[b]!) * 2

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
    ncRec blCount b * 2 ^ (maxBits - b) + kraftSumFrom blCount maxBits b =
      kraftSumFrom blCount maxBits 0 := by
  induction b with
  | zero => simp [ncRec]
  | succ n ih =>
    have ih' := ih (by omega)
    rw [kraftSumFrom_unfold blCount maxBits n (by omega)] at ih'
    show (ncRec blCount n + blCount[n]!) * 2 * 2 ^ (maxBits - (n + 1)) +
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
      -- l ≠ 0 and l ≤ maxBits: set acc[l] += 1
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
        rw [foldl_count_init l 1]; omega
      | isFalse hne =>
        rw [array_set_ne acc l b _ hne]
        simp only [beq_eq_false_iff_ne.mpr hne, ite_false, Bool.false_eq_true]

/-- `nextCodes.go` produces `ncRec` values: the `code` parameter at entry with
    `bits = b` becomes `ncRec blCount b` after the body executes. -/
private theorem nextCodes_go_eq_ncRec (blCount : Array Nat) (maxBits : Nat)
    (arr : Array Nat) (bits code : Nat)
    (hsize : arr.size = maxBits + 1)
    (hbits : 1 ≤ bits) (hbitsM : bits ≤ maxBits + 1)
    (hcode : code = ncRec blCount (bits - 1))
    (hprev : ∀ b, 1 ≤ b → b < bits → arr[b]! = ncRec blCount b)
    (b : Nat) (hb : 1 ≤ b) (hbM : b ≤ maxBits) :
    (nextCodes.go blCount maxBits arr bits code)[b]! = ncRec blCount b := by
  unfold nextCodes.go
  split
  · exact hprev b hb (by omega)
  · rename_i hle
    have hle' : bits ≤ maxBits := by omega
    let code' := (code + blCount[bits - 1]!) * 2
    let arr' := arr.set! bits code'
    have hsize' : arr'.size = maxBits + 1 := by
      simp only [arr', array_set_size]; exact hsize
    have hcode' : code' = ncRec blCount bits := by
      simp only [code', hcode]
      cases bits with
      | zero => omega
      | succ n => simp [ncRec]
    have hprev' : ∀ b', 1 ≤ b' → b' < bits + 1 → arr'[b']! = ncRec blCount b' := by
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
private theorem nextCodes_eq_ncRec (blCount : Array Nat) (maxBits b : Nat)
    (hb : b ≠ 0) (hbM : b ≤ maxBits) :
    (nextCodes blCount maxBits)[b]! = ncRec blCount b := by
  simp only [nextCodes]
  exact nextCodes_go_eq_ncRec blCount maxBits _ 1 0
    (Array.size_replicate ..) (by omega) (by omega) (by simp [ncRec])
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
private theorem validLengths_cons {l : Nat} {ls : List Nat} {maxBits : Nat}
    (hv : ValidLengths (l :: ls) maxBits) : ValidLengths ls maxBits := by
  constructor
  · exact fun x hx => hv.1 x (List.mem_cons_of_mem l hx)
  · have hf := hv.2
    simp only [List.filter_cons] at hf
    split at hf
    · -- l passes filter: l :: filter ls
      simp only [List.foldl_cons, Nat.zero_add] at hf
      rw [foldl_add_init] at hf; exact Nat.le_trans (Nat.le_add_left _ _) hf
    · -- l filtered out: filter ls
      exact hf

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
    have hv_ls := validLengths_cons hv
    simp only [List.foldl_cons]
    split
    · rename_i hskip
      rw [ih hv_ls acc hsize]
      congr 1
      simp only [List.filter_cons]
      simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hskip
      cases hskip with
      | inl h =>
        simp [h]
      | inr h =>
        exfalso; exact Nat.not_lt.mpr (hv.1 l List.mem_cons_self) h
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
      rw [hfilt, List.foldl_cons, Nat.zero_add, Nat.add_assoc, ← foldl_add_init]

/-- The ncRec recurrence at higher bit lengths bounds from below by
    scaling the value at a lower length:
    `ncRec b₂ ≥ (ncRec b₁ + count[b₁]) * 2^(b₂ - b₁)`. -/
private theorem ncRec_shift (blCount : Array Nat) (b₁ b₂ : Nat) (h : b₁ < b₂) :
    (ncRec blCount b₁ + blCount[b₁]!) * 2 ^ (b₂ - b₁) ≤ ncRec blCount b₂ := by
  induction b₂ with
  | zero => omega
  | succ k ih =>
    simp only [ncRec]
    cases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp h) with
    | inl hlt =>
      calc (ncRec blCount b₁ + blCount[b₁]!) * 2 ^ (k + 1 - b₁)
          = ((ncRec blCount b₁ + blCount[b₁]!) * 2 ^ (k - b₁)) * 2 := by
            rw [show k + 1 - b₁ = (k - b₁) + 1 from by omega, Nat.pow_succ, Nat.mul_assoc]
        _ ≤ ncRec blCount k * 2 := Nat.mul_le_mul_right 2 (ih hlt)
        _ ≤ (ncRec blCount k + blCount[k]!) * 2 :=
            Nat.mul_le_mul_right 2 (Nat.le_add_right _ _)
    | inr heq =>
      subst heq; simp

/-- The core ncRec bound: `ncRec blCount b + blCount[b]! ≤ 2^b` when the Kraft
    inequality holds for the full sum from 0. -/
private theorem ncRec_bound (blCount : Array Nat) (maxBits b : Nat)
    (hb : b ≤ maxBits)
    (hkraft : kraftSumFrom blCount maxBits 0 ≤ 2 ^ maxBits) :
    ncRec blCount b + blCount[b]! ≤ 2 ^ b := by
  have hcons := ncRec_kraft_conservation blCount maxBits b hb
  rw [kraftSumFrom_unfold blCount maxBits b hb] at hcons
  have h1 : (ncRec blCount b + blCount[b]!) * 2 ^ (maxBits - b) ≤ 2 ^ maxBits := by
    have : (ncRec blCount b + blCount[b]!) * 2 ^ (maxBits - b) ≤
           kraftSumFrom blCount maxBits 0 := by rw [Nat.add_mul]; omega
    omega
  rw [show 2 ^ maxBits = 2 ^ b * 2 ^ (maxBits - b) from by
    rw [← Nat.pow_add]; congr 1; omega] at h1
  exact Nat.le_of_mul_le_mul_right h1 (Nat.pow_pos (by omega))

/-! ## Helper lemmas for codeFor proofs -/

/-- The nextCodes construction ensures nc[b] + count[b] ≤ 2^b.
    This is the Kraft-based invariant of the canonical code construction:
    at each bit length b, the starting code plus the number of codes
    at that length doesn't exceed the code space.
    Proof requires analyzing the nextCodes.go recurrence and connecting
    it to the Kraft inequality in ValidLengths. -/
protected theorem nextCodes_plus_count_le (lengths : List Nat) (maxBits b : Nat)
    (hv : ValidLengths lengths maxBits)
    (hb : b ≠ 0) (hb' : b ≤ maxBits) :
    (nextCodes (countLengths lengths maxBits) maxBits)[b]! +
      lengths.foldl (fun acc l => if (l == b) = true then acc + 1 else acc) 0 ≤ 2 ^ b := by
  let blCount := countLengths lengths maxBits
  have hNC := nextCodes_eq_ncRec blCount maxBits b hb hb'
  have hCL : blCount[b]! =
      lengths.foldl (fun acc l => if (l == b) = true then acc + 1 else acc) 0 :=
    Huffman.Spec.countLengths_eq lengths maxBits b hb hb'
  have hKraft := kraftSumFrom_eq_kraft_foldl lengths maxBits hv
  rw [hNC, ← hCL]
  exact ncRec_bound blCount maxBits b hb' hKraft

/-- The counting foldl is monotone: the result is always ≥ the initial value. -/
protected theorem count_foldl_mono (len : Nat) (l : List Nat) (init : Nat) :
    init ≤ l.foldl (fun acc x => if (x == len) = true then acc + 1 else acc) init := by
  induction l generalizing init with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    cases hx : (x == len)
    · exact ih init
    · exact Nat.le_trans (by omega) (ih (init + 1))

/-- If s₁ < s₂ and lengths[s₁] = len, then the offset (count of same-length
    earlier symbols) for s₂ is strictly greater than for s₁, because
    lengths.take s₂ includes symbol s₁ (which has length len). -/
private theorem offset_of_lt (lengths : List Nat) (s₁ s₂ : Nat) (len : Nat)
    (hs₁ : s₁ < lengths.length)
    (hlen₁ : lengths[s₁] = len) (hlt : s₁ < s₂) (hs₂ : s₂ ≤ lengths.length) :
    List.foldl (fun acc l => if (l == len) = true then acc + 1 else acc)
      0 (List.take s₁ lengths) <
    List.foldl (fun acc l => if (l == len) = true then acc + 1 else acc)
      0 (List.take s₂ lengths) := by
  -- Generalize to arbitrary initial value for induction
  suffices ∀ (init : Nat),
      List.foldl (fun acc l => if (l == len) = true then acc + 1 else acc)
        init (List.take s₁ lengths) <
      List.foldl (fun acc l => if (l == len) = true then acc + 1 else acc)
        init (List.take s₂ lengths) from this 0
  induction lengths generalizing s₁ s₂ with
  | nil => simp at hs₁
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

/-- Extract `len ≠ 0 ∧ len ≤ maxBits` from the codeFor condition. -/
protected theorem codeFor_len_bounds {len maxBits : Nat}
    (h : ¬(len == 0 || decide (len > maxBits)) = true) : len ≠ 0 ∧ len ≤ maxBits := by
  simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, not_or] at h; omega

/-- The code value assigned by the canonical construction fits in `len` bits.
    This follows from the Kraft inequality: the nextCodes construction ensures
    nc[len] + count_at_len ≤ 2^len, and offset < count_at_len. -/
protected theorem code_value_bound (lengths : List Nat) (maxBits sym : Nat)
    (hv : ValidLengths lengths maxBits)
    (hs : sym < lengths.length)
    (hlen : ¬(lengths[sym] == 0 || decide (lengths[sym] > maxBits)) = true) :
    (nextCodes (countLengths lengths maxBits) maxBits)[lengths[sym]]! +
      List.foldl (fun acc l => if (l == lengths[sym]) = true then acc + 1 else acc)
        0 (List.take sym lengths) <
    2 ^ lengths[sym] := by
  have ⟨hlen0, hlenM⟩ := Huffman.Spec.codeFor_len_bounds hlen
  -- Key bound: nc[len] + totalCount ≤ 2^len
  have hncBound := Huffman.Spec.nextCodes_plus_count_le lengths maxBits lengths[sym] hv hlen0 hlenM
  -- Offset < totalCount: reuse offset_of_lt with s₂ = lengths.length
  have hOffsetLt : List.foldl (fun acc l => if (l == lengths[sym]) = true then acc + 1 else acc)
      0 (List.take sym lengths) <
    lengths.foldl (fun acc l => if (l == lengths[sym]) = true then acc + 1 else acc) 0 := by
    have h := offset_of_lt lengths sym lengths.length lengths[sym] hs rfl hs (by omega)
    rwa [List.take_length] at h
  omega

/-- Extract structural information from `codeFor` returning `some`. -/
protected theorem codeFor_spec {lengths : List Nat} {maxBits sym : Nat} {cw : Codeword}
    (h : codeFor lengths maxBits sym = some cw) :
    ∃ (hs : sym < lengths.length)
      (hlen : ¬(lengths[sym] == 0 || decide (lengths[sym] > maxBits)) = true),
      cw = natToBits
        ((nextCodes (countLengths lengths maxBits) maxBits)[lengths[sym]]! +
          List.foldl (fun acc l => if (l == lengths[sym]) = true then acc + 1 else acc)
            0 (List.take sym lengths))
        lengths[sym] := by
  unfold codeFor at h
  split at h
  · rename_i hs
    simp only [] at h
    split at h
    · simp at h
    · rename_i hlen
      exact ⟨hs, hlen, by simpa using h.symm⟩
  · simp at h

/-! ## Specification theorems -/

/-- `isPrefixOf` agrees with the `List.IsPrefix` proposition. -/
theorem isPrefixOf_iff (pre xs : List Bool) :
    isPrefixOf pre xs = true ↔ pre.IsPrefix xs := by
  induction pre generalizing xs with
  | nil => simp [isPrefixOf, List.IsPrefix]
  | cons a as ih =>
    cases xs with
    | nil => simp [isPrefixOf, List.IsPrefix]
    | cons b bs =>
      simp [isPrefixOf, Bool.and_eq_true, beq_iff_eq, ih]

/-- Decoding with a prefix-free code table is deterministic:
    if `decode` returns a result, it is the unique matching entry. -/
theorem decode_deterministic {α : Type} (table : List (Codeword × α))
    (bits : Codeword) (a b : α) (r₁ r₂ : Codeword) :
    decode table bits = some (a, r₁) →
    decode table bits = some (b, r₂) →
    a = b ∧ r₁ = r₂ := by
  intro h₁ h₂; simp_all

/-- The canonical code assigns distinct codewords to distinct symbols,
    provided the lengths are valid. -/
theorem codeFor_injective (lengths : List Nat) (maxBits : Nat)
    (hv : ValidLengths lengths maxBits)
    (s₁ s₂ : Nat) (cw : Codeword) :
    codeFor lengths maxBits s₁ = some cw →
    codeFor lengths maxBits s₂ = some cw →
    s₁ = s₂ := by
  intro h₁ h₂
  have ⟨hs₁, hlen₁, h₁⟩ := Huffman.Spec.codeFor_spec h₁
  have ⟨hs₂, hlen₂, h₂⟩ := Huffman.Spec.codeFor_spec h₂
  have heq := h₁.symm.trans h₂
  have hlen_eq : lengths[s₁] = lengths[s₂] := by
    have := congrArg List.length heq
    rwa [natToBits_length, natToBits_length] at this
  have hb₁ := Huffman.Spec.code_value_bound lengths maxBits s₁ hv hs₁ hlen₁
  rw [hlen_eq] at heq hb₁
  have hb₂ := Huffman.Spec.code_value_bound lengths maxBits s₂ hv hs₂ hlen₂
  have hcode := natToBits_injective _ _ _ hb₁ hb₂ heq
  by_cases heqs : s₁ = s₂
  · exact heqs
  · exfalso
    have : s₁ < s₂ ∨ s₂ < s₁ := by omega
    cases this with
    | inl hlt =>
      have := offset_of_lt lengths s₁ s₂ lengths[s₂] hs₁ hlen_eq hlt (Nat.le_of_lt hs₂)
      omega
    | inr hgt =>
      have := offset_of_lt lengths s₂ s₁ lengths[s₂] hs₂ rfl hgt (Nat.le_of_lt hs₁)
      omega

/-- The canonical code is prefix-free when lengths are valid. This is
    the key property ensuring unambiguous decoding. -/
theorem canonical_prefix_free (lengths : List Nat) (maxBits : Nat)
    (hv : ValidLengths lengths maxBits)
    (s₁ s₂ : Nat) (cw₁ cw₂ : Codeword) :
    codeFor lengths maxBits s₁ = some cw₁ →
    codeFor lengths maxBits s₂ = some cw₂ →
    s₁ ≠ s₂ →
    ¬cw₁.IsPrefix cw₂ := by
  intro h₁ h₂ hne hpre
  -- Extract structural info (all fields at once)
  have ⟨hs₁, hlen₁_cond, hcw₁⟩ := Huffman.Spec.codeFor_spec h₁
  have ⟨hs₂, hlen₂_cond, hcw₂⟩ := Huffman.Spec.codeFor_spec h₂
  have ⟨hlen₁_ne, hlen₁_le⟩ := Huffman.Spec.codeFor_len_bounds hlen₁_cond
  have ⟨hlen₂_ne, hlen₂_le⟩ := Huffman.Spec.codeFor_len_bounds hlen₂_cond
  have hlen₁ : cw₁.length = lengths[s₁] := by rw [hcw₁, natToBits_length]
  have hlen₂ : cw₂.length = lengths[s₂] := by rw [hcw₂, natToBits_length]
  -- Prefix implies cw₁.length ≤ cw₂.length
  obtain ⟨t, ht⟩ := hpre
  have htlen : cw₁.length + t.length = cw₂.length := by
    rw [← ht, List.length_append]
  by_cases heq : lengths[s₁] = lengths[s₂]
  · -- Same length: prefix of same-length list means equal
    have : t = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; simp at ht; subst ht
    exact hne (codeFor_injective lengths maxBits hv s₁ s₂ cw₁ h₁ h₂)
  · -- Different lengths: canonical codes at different lengths aren't prefixes.
    have hlt_len : lengths[s₁] < lengths[s₂] := by omega
    -- Code values fit in their bit lengths
    have hb₁ := Huffman.Spec.code_value_bound lengths maxBits s₁ hv hs₁ hlen₁_cond
    have hb₂ := Huffman.Spec.code_value_bound lengths maxBits s₂ hv hs₂ hlen₂_cond
    -- Prefix in natToBits form gives numerical upper bound
    have hupper := natToBits_prefix_lt _ _ _ _ (by omega) hb₁ hb₂ (hcw₁ ▸ hcw₂ ▸ ⟨t, ht⟩)
    -- Connect nextCodes array values to ncRec
    let blCount := countLengths lengths maxBits
    have hnc₁ := nextCodes_eq_ncRec blCount maxBits _ hlen₁_ne hlen₁_le
    have hnc₂ := nextCodes_eq_ncRec blCount maxBits _ hlen₂_ne hlen₂_le
    -- offset₁ < total count at length len₁
    have hoff_lt : List.foldl (fun acc l => if (l == lengths[s₁]) = true then acc + 1 else acc)
        0 (List.take s₁ lengths) < blCount[lengths[s₁]]! := by
      have h := offset_of_lt lengths s₁ lengths.length lengths[s₁] hs₁ rfl hs₁ (by omega)
      rw [List.take_length] at h
      rw [Huffman.Spec.countLengths_eq lengths maxBits lengths[s₁] hlen₁_ne hlen₁_le]; exact h
    -- Chain: code₂ < (code₁+1)*2^d ≤ (ncRec₁+count₁)*2^d ≤ ncRec₂ ≤ code₂
    exfalso
    rw [hnc₁, hnc₂] at hupper
    have hmul : (ncRec blCount lengths[s₁] +
        List.foldl (fun acc l => if (l == lengths[s₁]) = true then acc + 1 else acc) 0
          (List.take s₁ lengths) + 1) *
        2 ^ (lengths[s₂] - lengths[s₁]) ≤
        (ncRec blCount lengths[s₁] + blCount[lengths[s₁]]!) *
          2 ^ (lengths[s₂] - lengths[s₁]) :=
      Nat.mul_le_mul_right _ (by omega)
    have hshift := ncRec_shift blCount lengths[s₁] lengths[s₂] hlt_len
    omega

/-! ## Decode correctness -/

/-- `decode` on a prefix-free code table correctly finds the matching entry.
    If `(cw, sym)` is in the table and the codewords are pairwise
    non-prefix, then decoding `cw ++ rest` returns `(sym, rest)`. -/
theorem decode_prefix_free {α : Type} (table : List (Codeword × α))
    (cw : Codeword) (sym : α) (rest : Codeword)
    (hmem : (cw, sym) ∈ table)
    (hpf : ∀ cw₁ s₁ cw₂ s₂, (cw₁, s₁) ∈ table → (cw₂, s₂) ∈ table →
      (cw₁, s₁) ≠ (cw₂, s₂) → ¬cw₁.IsPrefix cw₂) :
    decode table (cw ++ rest) = some (sym, rest) := by
  induction table with
  | nil => simp at hmem
  | cons entry entries ih =>
    obtain ⟨cw', sym'⟩ := entry
    simp only [decode]
    cases hmem with
    | head =>
      simp [isPrefixOf_self_append, List.drop_append_of_le_length (Nat.le_refl _)]
    | tail _ htail =>
      by_cases heq : (cw', sym') = (cw, sym)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
        simp [isPrefixOf_self_append, List.drop_append_of_le_length (Nat.le_refl _)]
      · have hno : isPrefixOf cw' (cw ++ rest) = false := by
          cases hp : isPrefixOf cw' (cw ++ rest) with
          | false => rfl
          | true =>
            exfalso; rw [isPrefixOf_iff] at hp
            cases IsPrefix_dichotomy hp with
            | inl h =>
              exact hpf cw' sym' cw sym (List.mem_cons_self ..)
                (List.mem_cons_of_mem _ htail) heq h
            | inr h =>
              exact hpf cw sym cw' sym' (List.mem_cons_of_mem _ htail)
                (List.mem_cons_self ..) (Ne.symm heq) h
        simp only [hno]
        exact ih htail (fun cw₁ s₁ cw₂ s₂ h₁ h₂ hne =>
          hpf cw₁ s₁ cw₂ s₂ (List.mem_cons_of_mem _ h₁)
            (List.mem_cons_of_mem _ h₂) hne)

/-! ## Connecting canonical_prefix_free to allCodes -/

/-- Membership in `allCodes` is characterized by `codeFor`. -/
theorem allCodes_mem_iff (lengths : List Nat) (maxBits : Nat) (s : Nat) (cw : Codeword) :
    (s, cw) ∈ allCodes lengths maxBits ↔
      s < lengths.length ∧ codeFor lengths maxBits s = some cw := by
  simp only [allCodes, List.mem_filterMap, List.mem_range]
  constructor
  · rintro ⟨sym, hsym, h⟩
    cases hcf : codeFor lengths maxBits sym with
    | none => simp [hcf] at h
    | some cw' =>
      simp [hcf] at h
      exact ⟨h.1 ▸ hsym, h.1 ▸ h.2 ▸ hcf⟩
  · rintro ⟨hs, hcode⟩
    exact ⟨s, hs, by simp [hcode]⟩

/-- `allCodes` has no duplicate entries (each symbol appears at most once). -/
theorem allCodes_nodup (lengths : List Nat) (maxBits : Nat) :
    (allCodes lengths maxBits).Nodup := by
  simp only [allCodes, List.Nodup]
  apply List.Pairwise.filterMap (R := (· ≠ ·))
  · intro sym₁ sym₂ hne p₁ hp₁ p₂ hp₂
    cases hc₁ : codeFor lengths maxBits sym₁ with
    | none => simp [hc₁] at hp₁
    | some cw₁ =>
      cases hc₂ : codeFor lengths maxBits sym₂ with
      | none => simp [hc₂] at hp₂
      | some cw₂ =>
        simp [hc₁] at hp₁; simp [hc₂] at hp₂
        subst hp₁; subst hp₂
        exact fun h => hne (Prod.mk.inj h).1
  · exact List.nodup_range

/-- Codewords assigned to distinct symbols are not prefixes of each other.
    This is the membership-based version of `canonical_prefix_free`. -/
theorem allCodes_prefix_free_of_ne (lengths : List Nat) (maxBits : Nat)
    (hv : ValidLengths lengths maxBits)
    (s₁ s₂ : Nat) (cw₁ cw₂ : Codeword)
    (h₁ : (s₁, cw₁) ∈ allCodes lengths maxBits)
    (h₂ : (s₂, cw₂) ∈ allCodes lengths maxBits)
    (hne : s₁ ≠ s₂) :
    ¬cw₁.IsPrefix cw₂ := by
  rw [allCodes_mem_iff] at h₁ h₂
  exact canonical_prefix_free lengths maxBits hv s₁ s₂ cw₁ cw₂ h₁.2 h₂.2 hne

/-- The list of codewords produced by `allCodes` is prefix-free. -/
theorem allCodeWords_prefix_free (lengths : List Nat) (maxBits : Nat)
    (hv : ValidLengths lengths maxBits) :
    IsPrefixFree ((allCodes lengths maxBits).map Prod.snd) := by
  intro i j hi hj hij hpre
  simp only [List.length_map] at hi hj
  rw [List.getElem_map, List.getElem_map] at hpre
  have hmi := (allCodes_mem_iff ..).mp (List.getElem_mem (h := hi))
  have hmj := (allCodes_mem_iff ..).mp (List.getElem_mem (h := hj))
  have hne : (allCodes lengths maxBits)[i].1 ≠ (allCodes lengths maxBits)[j].1 := by
    intro heq
    have hcw_eq := Option.some.inj (hmi.2.symm.trans (heq ▸ hmj.2))
    have hentry_eq : (allCodes lengths maxBits)[i] = (allCodes lengths maxBits)[j] :=
      Prod.ext heq hcw_eq
    have hpw := List.pairwise_iff_getElem.mp (allCodes_nodup lengths maxBits)
    have : ¬(i < j) := fun h => hpw i j hi hj h hentry_eq
    have : ¬(j < i) := fun h => hpw j i hj hi h hentry_eq.symm
    omega
  exact canonical_prefix_free lengths maxBits hv _ _ _ _ hmi.2 hmj.2 hne hpre

end Huffman.Spec
