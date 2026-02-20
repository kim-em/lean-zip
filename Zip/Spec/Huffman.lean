/-!
# Prefix Codes and Canonical Huffman Construction

Formal specification of prefix-free binary codes and the canonical
Huffman code construction from RFC 1951 §3.2.2.

A prefix code is a set of binary codewords where no codeword is a proper
prefix of another. This guarantees unique, unambiguous decoding: given a
bit stream, there is at most one way to segment it into codewords.

The canonical Huffman construction assigns codewords to symbols based
solely on their code lengths, using a deterministic algorithm that ensures:
1. Shorter codes are numerically smaller
2. Codes of the same length are assigned in increasing symbol order
-/

namespace Huffman.Spec

/-! ## Codewords -/

/-- A codeword: a list of bits, MSB first (as read from a DEFLATE stream). -/
abbrev Codeword := List Bool

/-- Convert a natural number to an MSB-first bit list of the given width.
    Example: `natToBits 5 3 = [true, false, true]` (binary 101). -/
def natToBits (val : Nat) : Nat → Codeword
  | 0 => []
  | w + 1 => val.testBit w :: natToBits val w

/-! ## Properties of `natToBits` -/

/-- `natToBits` produces a list of the specified width. -/
theorem natToBits_length (val width : Nat) :
    (natToBits val width).length = width := by
  induction width with
  | zero => simp [natToBits]
  | succ n ih => simp [natToBits, ih]

/-- Two `natToBits` outputs of the same width are equal iff all testBit
    values agree on bit positions below the width. -/
theorem natToBits_eq_iff (v₁ v₂ w : Nat) :
    natToBits v₁ w = natToBits v₂ w ↔ ∀ i < w, v₁.testBit i = v₂.testBit i := by
  induction w with
  | zero => simp [natToBits]
  | succ n ih =>
    simp only [natToBits, List.cons.injEq]
    rw [ih]
    constructor
    · rintro ⟨hbit, htail⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
      · exact htail i h
      · exact h ▸ hbit
    · intro h
      exact ⟨h n (by omega), fun i hi => h i (by omega)⟩

/-- `natToBits` is injective for values below `2^w`. -/
theorem natToBits_injective (v₁ v₂ w : Nat) (h₁ : v₁ < 2 ^ w) (h₂ : v₂ < 2 ^ w)
    (heq : natToBits v₁ w = natToBits v₂ w) : v₁ = v₂ := by
  apply Nat.eq_of_testBit_eq; intro i
  by_cases hi : i < w
  · exact (natToBits_eq_iff v₁ v₂ w).mp heq i hi
  · have hiw : w ≤ i := Nat.le_of_not_lt hi
    have p₁ : v₁ < 2 ^ i := Nat.lt_of_lt_of_le h₁ (Nat.pow_le_pow_right (by omega) hiw)
    have p₂ : v₂ < 2 ^ i := Nat.lt_of_lt_of_le h₂ (Nat.pow_le_pow_right (by omega) hiw)
    rw [Nat.testBit_lt_two_pow p₁, Nat.testBit_lt_two_pow p₂]

/-! ## Canonical Huffman code construction (RFC 1951 §3.2.2) -/

/-- Count the number of codes of each length, producing an array indexed
    by length. Lengths exceeding `maxBits` are clamped. -/
def countLengths (lengths : List Nat) (maxBits : Nat) : Array Nat :=
  let init := Array.replicate (maxBits + 1) 0
  lengths.foldl (fun acc len =>
    if len == 0 || len > maxBits then acc
    else acc.set! len (acc[len]! + 1)) init

/-- Compute the first code value for each bit length.
    Implements: `next_code[bits] = (next_code[bits-1] + bl_count[bits-1]) << 1`
    from RFC 1951 §3.2.2 step 2. -/
def nextCodes (blCount : Array Nat) (maxBits : Nat) : Array Nat :=
  let init := Array.replicate (maxBits + 1) 0
  go init 1 0
where
  go (arr : Array Nat) (bits code : Nat) : Array Nat :=
    if h : bits > maxBits then arr
    else
      let code := (code + blCount[bits - 1]!) * 2
      go (arr.set! bits code) (bits + 1) code
  termination_by maxBits + 1 - bits
  decreasing_by omega

/-- Compute the canonical codeword for a given symbol.
    Returns `none` if the symbol's code length is 0 or exceeds `maxBits`. -/
def codeFor (lengths : List Nat) (maxBits : Nat := 15) (sym : Nat) :
    Option Codeword :=
  if h : sym < lengths.length then
    let len := lengths[sym]
    if len == 0 || len > maxBits then none
    else
      let blCount := countLengths lengths maxBits
      let nc := nextCodes blCount maxBits
      -- Count how many earlier symbols have the same length
      let offset := (lengths.take sym).foldl
        (fun acc l => if l == len then acc + 1 else acc) 0
      let code := nc[len]! + offset
      some (natToBits code len)
  else none

/-- All (symbol, codeword) pairs for symbols with non-zero code length.
    Symbols are listed in increasing order. -/
def allCodes (lengths : List Nat) (maxBits : Nat := 15) :
    List (Nat × Codeword) :=
  (List.range lengths.length).filterMap fun sym =>
    (codeFor lengths maxBits sym).map (sym, ·)

/-! ## Decoding -/

/-- Check whether `pre` is a prefix of `xs`. -/
def isPrefixOf : List Bool → List Bool → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => a == b && isPrefixOf as bs

/-- Decode one symbol from a bit stream using a code table.
    Returns the decoded symbol and remaining bits, or `none` if no
    codeword matches the beginning of the stream. -/
def decode (table : List (Codeword × α)) (bits : Codeword) :
    Option (α × Codeword) :=
  match table with
  | [] => none
  | (cw, sym) :: rest =>
    if isPrefixOf cw bits then some (sym, bits.drop cw.length)
    else decode rest bits

/-! ## Prefix-free property -/

/-- A list of codewords is prefix-free: no codeword is a prefix of
    another distinct codeword in the list. -/
def IsPrefixFree (words : List Codeword) : Prop :=
  ∀ (i j : Nat), (hi : i < words.length) → (hj : j < words.length) →
    i ≠ j → ¬words[i].IsPrefix words[j]

/-! ## Well-formedness -/

/-- A code length assignment is valid when:
    1. All lengths are ≤ maxBits
    2. The Kraft inequality is satisfied (not oversubscribed):
       `∑ 2^(maxBits - len) ≤ 2^maxBits` for non-zero lengths.
    This ensures the canonical construction produces a valid prefix code. -/
def ValidLengths (lengths : List Nat) (maxBits : Nat) : Prop :=
  (∀ l ∈ lengths, l ≤ maxBits) ∧
  (lengths.filter (· != 0)).foldl
    (fun acc l => acc + 2^(maxBits - l)) 0 ≤ 2^maxBits

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
    · simp only [ite_true, List.length_cons, Nat.succ_mul]
      have hxeq : x = len := beq_iff_eq.mp hxl
      rw [hxeq]; omega

/-- Double filter: `(· != 0)` then `(· == len)` is the same as `(· == len)` when `len > 0`. -/
private theorem filter_ne_zero_filter_eq (ls : List Nat) (len : Nat) (hlen : len ≠ 0) :
    (ls.filter (· != 0)).filter (· == len) = ls.filter (· == len) := by
  rw [List.filter_filter]
  congr 1; ext x
  match h : x == len with
  | true =>
    have : x = len := beq_iff_eq.mp h
    subst this; simp [bne_iff_ne, hlen]
  | false => simp

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
    -- ih': ncRec n * 2^(maxBits-n) + (blCount[n]! * 2^(maxBits-n) + kraftSumFrom (n+1)) = kraftSumFrom 0
    -- Unfold ncRec (n+1) = (ncRec n + blCount[n]!) * 2, targeted
    show (ncRec blCount n + blCount[n]!) * 2 * 2 ^ (maxBits - (n + 1)) +
      kraftSumFrom blCount maxBits (n + 1) = kraftSumFrom blCount maxBits 0
    rw [Nat.mul_assoc,
        show 2 * 2 ^ (maxBits - (n + 1)) = 2 ^ (maxBits - n) from by
          rw [show maxBits - n = maxBits - (n + 1) + 1 from by omega, Nat.pow_succ,
              Nat.mul_comm],
        Nat.add_mul]
    omega

/-! ## Connecting kraftSumFrom to ValidLengths -/

/-- `Array.set!` at a nonzero index doesn't affect index 0. -/
private theorem array_set_ne_zero (arr : Array Nat) (i v : Nat) (hi : i ≠ 0) :
    (arr.set! i v)[0]! = arr[0]! := by
  show (arr.setIfInBounds i v).get!Internal 0 = arr.get!Internal 0
  simp only [Array.get!Internal, Array.getD, Array.setIfInBounds]
  split
  · rename_i h
    simp only [Array.size_set]
    split
    · rename_i h₀
      have h₁ : 0 < (arr.set i v h).size := by rw [Array.size_set]; exact h₀
      exact show (arr.set i v h)[0]'h₁ = arr[0]'h₀ by rw [Array.getElem_set]; simp [hi]
    · rfl
  · rfl

/-- `Array.set!` at a different index doesn't affect the target index. -/
private theorem array_set_ne (arr : Array Nat) (i j v : Nat) (hij : i ≠ j) :
    (arr.set! i v)[j]! = arr[j]! := by
  show (arr.setIfInBounds i v).get!Internal j = arr.get!Internal j
  simp only [Array.get!Internal, Array.getD, Array.setIfInBounds]
  split
  · rename_i h
    simp only [Array.size_set]
    split
    · rename_i hj
      have hj' : j < (arr.set i v h).size := by rw [Array.size_set]; exact hj
      exact show (arr.set i v h)[j]'hj' = arr[j]'hj by rw [Array.getElem_set]; simp [hij]
    · rfl
  · rfl

/-- `Array.set!` at the same index replaces the value. -/
private theorem array_set_self (arr : Array Nat) (i v : Nat) (hi : i < arr.size) :
    (arr.set! i v)[i]! = v := by
  show (arr.setIfInBounds i v).get!Internal i = v
  unfold Array.setIfInBounds
  simp only [hi, dite_true]
  unfold Array.get!Internal Array.getD
  simp only [Array.size_set, hi, dite_true]
  have hi' : i < (arr.set i v hi).size := by rw [Array.size_set]; exact hi
  show (arr.set i v hi)[i]'hi' = v
  rw [Array.getElem_set, if_pos rfl]

/-- `Array.set!` preserves the size. -/
private theorem array_set_size (arr : Array Nat) (i v : Nat) :
    (arr.set! i v).size = arr.size := by
  simp only [Array.set!, Array.setIfInBounds]
  split
  · exact Array.size_set ..
  · rfl

/-- `countLengths` never modifies index 0. -/
private theorem countLengths_zero (lengths : List Nat) (maxBits : Nat) :
    (countLengths lengths maxBits)[0]! = 0 := by
  simp only [countLengths]
  suffices ∀ (acc : Array Nat), acc[0]! = 0 →
      (lengths.foldl (fun acc len =>
        if len == 0 || len > maxBits then acc
        else acc.set! len (acc[len]! + 1)) acc)[0]! = 0 from
    this _ (by
      show (Array.replicate (maxBits + 1) 0).get!Internal 0 = 0
      simp only [Array.get!Internal, Array.getD, Array.size_replicate]
      split
      · exact Array.getElem_replicate _
      · rfl)
  intro acc hacc
  induction lengths generalizing acc with
  | nil => exact hacc
  | cons l ls ih =>
    simp only [List.foldl_cons]
    split
    · exact ih acc hacc
    · rename_i h
      apply ih
      have hl : l ≠ 0 := by simp only [Bool.or_eq_true, beq_iff_eq] at h; omega
      rw [array_set_ne_zero acc l _ hl]; exact hacc

/-- `countLengths[b]!` counts elements of `lengths` equal to `b`, for valid `b`. -/
private theorem countLengths_eq (lengths : List Nat) (maxBits b : Nat)
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
    show (Array.replicate (maxBits + 1) 0).get!Internal b + _ = _
    simp only [Array.get!Internal, Array.getD, Array.size_replicate]
    split
    · simp [Array.getInternal]
    · simp
  intro acc hsize
  induction lengths generalizing acc with
  | nil => simp
  | cons l ls ih =>
    simp only [List.foldl_cons]
    split
    · rename_i hskip
      -- l == 0 || l > maxBits: skip, foldl for count also skips if l ≠ b
      rw [ih acc hsize]
      congr 1
      -- need: (l == b) = false when l = 0 or l > maxBits and b ≠ 0 and b ≤ maxBits
      simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hskip
      cases hskip with
      | inl h => simp [show (l == b) = false from beq_eq_false_iff_ne.mpr (h ▸ Ne.symm hb)]
      | inr h => simp [show (l == b) = false from
          beq_eq_false_iff_ne.mpr (fun heq => by rw [heq] at h; omega)]
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
        -- l = b: the set increments acc[b], and foldl counts this element
        subst heq
        rw [array_set_self acc l _ (by omega)]
        simp only [beq_self_eq_true, ite_true, Nat.zero_add]
        rw [foldl_count_init l 1]; omega
      | isFalse hne =>
        -- l ≠ b: the set doesn't affect acc[b], and foldl doesn't count this element
        rw [array_set_ne acc l b _ hne]
        have hlb : (l == b) = false := beq_eq_false_iff_ne.mpr hne
        simp only [hlb, ite_false, Bool.false_eq_true, ite_false]

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
  · -- bits > maxBits: function returns arr; b < bits so hprev applies
    rename_i hgt
    exact hprev b hb (by omega)
  · -- bits ≤ maxBits: recursive call
    rename_i hle
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
        -- b' = bits: was just set
        rw [heq]; simp only [arr']
        rw [array_set_self arr bits code' (by omega)]
        exact hcode'
      | inr hlt =>
        -- b' < bits: set at different index doesn't affect
        simp only [arr']
        rw [array_set_ne arr bits b' code' (by omega)]
        exact hprev b' hb' hlt
    exact nextCodes_go_eq_ncRec blCount maxBits arr' (bits + 1) code'
      hsize' (by omega) (by omega) hcode' hprev' b hb hbM

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
        have : b + 1 ≤ l := by omega
        simp only [hbl', this, ite_true]; omega
      else
        have : ¬(b + 1 ≤ l) := by omega
        simp only [hbl', this, ite_false, Nat.add_zero]
termination_by maxBits + 1 - b

/-- `kraftSumFrom` over an all-zeros array is 0. -/
private theorem kraftSumFrom_replicate (maxBits b : Nat) :
    kraftSumFrom (Array.replicate (maxBits + 1) 0) maxBits b = 0 := by
  if hb : b > maxBits then
    exact kraftSumFrom_gt _ _ _ hb
  else
    rw [kraftSumFrom_unfold _ _ _ (by omega)]
    have : (Array.replicate (maxBits + 1) 0)[b]! = 0 := by
      show (Array.replicate (maxBits + 1) 0).get!Internal b = 0
      simp only [Array.get!Internal, Array.getD, Array.size_replicate]
      split
      · exact Array.getElem_replicate _
      · rfl
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
      -- l = 0 or l > maxBits: skip, and filter also skips or l > maxBits is impossible
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
      -- l ≠ 0 and l ≤ maxBits: increment count
      simp only [Bool.or_eq_true, beq_iff_eq, not_or, decide_eq_true_eq] at hset
      have hl_ne : l ≠ 0 := hset.1
      have hl_le : l ≤ maxBits := by omega
      have hsize' : (acc.set! l (acc[l]! + 1)).size = maxBits + 1 := by
        rw [array_set_size]; exact hsize
      rw [ih hv_ls (acc.set! l (acc[l]! + 1)) hsize']
      rw [kraftSumFrom_incr acc maxBits l 0 hl_le (by omega)]
      simp only [Nat.zero_le, ite_true]
      -- Unfold filter on (l :: ls): l passes since l ≠ 0
      have hfilt : (l :: ls).filter (· != 0) = l :: ls.filter (· != 0) := by
        simp only [List.filter_cons]
        exact if_pos (bne_iff_ne.mpr hl_ne)
      rw [hfilt, List.foldl_cons, Nat.zero_add, Nat.add_assoc, ← foldl_add_init]

/-- The core ncRec bound: `ncRec blCount b + blCount[b]! ≤ 2^b` when the Kraft
    inequality holds for the full sum from 0. -/
private theorem ncRec_bound (blCount : Array Nat) (maxBits b : Nat)
    (hb : b ≤ maxBits)
    (hkraft : kraftSumFrom blCount maxBits 0 ≤ 2 ^ maxBits) :
    ncRec blCount b + blCount[b]! ≤ 2 ^ b := by
  have hcons := ncRec_kraft_conservation blCount maxBits b hb
  rw [kraftSumFrom_unfold blCount maxBits b hb] at hcons
  -- (ncRec b + blCount[b]!) * 2^(maxBits-b) ≤ kraftSumFrom 0 ≤ 2^maxBits
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
private theorem nextCodes_plus_count_le (lengths : List Nat) (maxBits b : Nat)
    (hv : ValidLengths lengths maxBits)
    (hb : b ≠ 0) (hb' : b ≤ maxBits) :
    (nextCodes (countLengths lengths maxBits) maxBits)[b]! +
      lengths.foldl (fun acc l => if (l == b) = true then acc + 1 else acc) 0 ≤ 2 ^ b := by
  let blCount := countLengths lengths maxBits
  -- Step 1: (nextCodes blCount maxBits)[b]! = ncRec blCount b
  have hNC : (nextCodes blCount maxBits)[b]! = ncRec blCount b := by
    simp only [nextCodes]
    exact nextCodes_go_eq_ncRec blCount maxBits _ 1 0
      (Array.size_replicate ..) (by omega) (by omega) (by simp [ncRec])
      (fun b' hb' hlt => by omega) b (by omega) hb'
  -- Step 2: blCount[b]! = count of b in lengths
  have hCL : blCount[b]! =
      lengths.foldl (fun acc l => if (l == b) = true then acc + 1 else acc) 0 :=
    countLengths_eq lengths maxBits b hb hb'
  -- Step 3: kraftSumFrom ≤ 2^maxBits (from ValidLengths)
  have hKraft := kraftSumFrom_eq_kraft_foldl lengths maxBits hv
  -- Step 4: ncRec bound
  have hBound := ncRec_bound blCount maxBits b hb' hKraft
  -- Combine: nc[b] + count = ncRec b + blCount[b]! ≤ 2^b
  rw [hNC, ← hCL]
  exact hBound

/-- The counting foldl is monotone: the result is always ≥ the initial value. -/
private theorem count_foldl_mono (len : Nat) (l : List Nat) (init : Nat) :
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
      -- s₁ = 0: take 0 = [], foldl = init
      simp only [List.take_zero, List.foldl_nil]
      -- s₂ ≥ 1: take s₂ (x :: xs) = x :: take (s₂ - 1) xs
      -- Since x = lengths[0] = len, the first step of foldl adds 1
      simp only [List.getElem_cons_zero] at hlen₁
      have hs₂' : 0 < s₂ := by omega
      rw [List.take_cons hs₂']
      simp only [List.foldl_cons, show (x == len) = true from beq_iff_eq.mpr hlen₁, ite_true]
      exact Nat.lt_of_lt_of_le (by omega) (count_foldl_mono len _ _)
    | succ n =>
      simp only [List.length_cons] at hs₁ hs₂
      have hs₂' : 0 < s₂ := by omega
      rw [List.take_cons (by omega : 0 < n + 1), List.take_cons hs₂']
      simp only [List.foldl_cons]
      have hlen₁' : xs[n] = len := by
        simp only [List.getElem_cons_succ] at hlen₁; exact hlen₁
      exact ih n (s₂ - 1) (by omega) hlen₁' (by omega) (by omega) _

/-- The code value assigned by the canonical construction fits in `len` bits.
    This follows from the Kraft inequality: the nextCodes construction ensures
    nc[len] + count_at_len ≤ 2^len, and offset < count_at_len. -/
private theorem code_value_bound (lengths : List Nat) (maxBits sym : Nat)
    (hv : ValidLengths lengths maxBits)
    (hs : sym < lengths.length)
    (hlen : ¬(lengths[sym] == 0 || decide (lengths[sym] > maxBits)) = true) :
    (nextCodes (countLengths lengths maxBits) maxBits)[lengths[sym]]! +
      List.foldl (fun acc l => if (l == lengths[sym]) = true then acc + 1 else acc)
        0 (List.take sym lengths) <
    2 ^ lengths[sym] := by
  have hlen0 : lengths[sym] ≠ 0 := by
    intro h; have : (lengths[sym] == 0 || decide (lengths[sym] > maxBits)) = true := by simp [h]
    exact hlen this
  have hlenM : lengths[sym] ≤ maxBits := by
    by_cases h : lengths[sym] > maxBits
    · exfalso; exact hlen (by simp [h])
    · omega
  -- Key bound: nc[len] + totalCount ≤ 2^len
  have hncBound := nextCodes_plus_count_le lengths maxBits lengths[sym] hv hlen0 hlenM
  -- Offset < totalCount: reuse offset_of_lt with s₂ = lengths.length
  have hOffsetLt : List.foldl (fun acc l => if (l == lengths[sym]) = true then acc + 1 else acc)
      0 (List.take sym lengths) <
    lengths.foldl (fun acc l => if (l == lengths[sym]) = true then acc + 1 else acc) 0 := by
    have h := offset_of_lt lengths sym lengths.length lengths[sym] hs rfl hs (by omega)
    rwa [List.take_length] at h
  omega

/-- Extract structural information from `codeFor` returning `some`. -/
private theorem codeFor_spec {lengths : List Nat} {maxBits sym : Nat} {cw : Codeword}
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
  -- Extract structural info from both codeFor calls
  have ⟨hs₁, hlen₁, h₁⟩ := codeFor_spec h₁
  have ⟨hs₂, hlen₂, h₂⟩ := codeFor_spec h₂
  -- h₁ : cw = natToBits code₁ lengths[s₁]
  -- h₂ : cw = natToBits code₂ lengths[s₂]
  -- Step 1: lengths must be equal
  have heq := h₁.symm.trans h₂
  have hlen_eq : lengths[s₁] = lengths[s₂] := by
    have := congrArg List.length heq
    rwa [natToBits_length, natToBits_length] at this
  -- Step 2: code values must be equal (by natToBits_injective)
  have hb₁ := code_value_bound lengths maxBits s₁ hv hs₁ hlen₁
  rw [hlen_eq] at heq hb₁
  have hb₂ := code_value_bound lengths maxBits s₂ hv hs₂ hlen₂
  have hcode := natToBits_injective _ _ _ hb₁ hb₂ heq
  -- hcode : nc[len] + offset₁ = nc[len] + offset₂, so offset₁ = offset₂
  -- Step 3: if s₁ ≠ s₂, offsets differ — contradiction
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
  -- Extract structural info
  have ⟨_, _, hcw₁⟩ := codeFor_spec h₁
  have ⟨_, _, hcw₂⟩ := codeFor_spec h₂
  have hlen₁ : cw₁.length = lengths[s₁] := by rw [hcw₁, natToBits_length]
  have hlen₂ : cw₂.length = lengths[s₂] := by rw [hcw₂, natToBits_length]
  -- Prefix implies cw₁.length ≤ cw₂.length
  obtain ⟨t, ht⟩ := hpre
  have htlen : cw₁.length + t.length = cw₂.length := by
    have := congrArg List.length ht; simp at this; omega
  by_cases heq : lengths[s₁] = lengths[s₂]
  · -- Same length: prefix of same-length list means equal
    have : t = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; simp at ht; subst ht
    exact hne (codeFor_injective lengths maxBits hv s₁ s₂ cw₁ h₁ h₂)
  · -- Different lengths: canonical codes at different lengths aren't prefixes.
    -- This requires showing nc[len₂] ≥ (nc[len₁] + count[len₁]) * 2^(len₂-len₁),
    -- i.e., the nextCodes recurrence leaves no room for prefix overlap.
    sorry

end Huffman.Spec
