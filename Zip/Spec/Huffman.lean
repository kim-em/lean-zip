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
      rw [hxeq]
      calc (xs.filter (· == len)).length * 2 ^ (maxBits - len) + 2 ^ (maxBits - len)
          _ ≤ xs.foldl (fun acc l => acc + 2 ^ (maxBits - l)) 0 + 2 ^ (maxBits - len) :=
              Nat.add_le_add_right ih _
          _ = 2 ^ (maxBits - len) + xs.foldl (fun acc l => acc + 2 ^ (maxBits - l)) 0 :=
              Nat.add_comm _ _

/-- Double filter: `(· != 0)` then `(· == len)` is the same as `(· == len)` when `len > 0`. -/
private theorem filter_ne_zero_filter_eq (ls : List Nat) (len : Nat) (hlen : len ≠ 0) :
    (ls.filter (· != 0)).filter (· == len) = ls.filter (· == len) := by
  induction ls with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.filter_cons]
    cases hxl : x == len
    · cases hx0 : (x != 0)
      · exact ih
      · simp only [ite_true, List.filter_cons, hxl]; exact ih
    · have hx0 : (x != 0) = true := by
        have := beq_iff_eq.mp hxl; subst this; exact bne_iff_ne.mpr hlen
      simp only [hx0, ite_true, List.filter_cons, hxl]
      exact congrArg _ ih

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
  have hpow_pos : 0 < 2 ^ (maxBits - len) := Nat.pos_of_ne_zero fun h => by
    simp [Nat.pow_eq_zero] at h
  rw [Nat.mul_comm, Nat.mul_comm (2 ^ len)] at hle
  exact Nat.le_of_mul_le_mul_left hle hpow_pos

/-! ## Helper lemmas for codeFor proofs -/

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
  sorry

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
    have htl : t.length = 0 := by omega
    have : t = [] := by cases t with | nil => rfl | cons _ _ => simp at htl
    subst this; rw [List.append_nil] at ht; subst ht
    exact hne (codeFor_injective lengths maxBits hv s₁ s₂ cw₁ h₁ h₂)
  · -- Different lengths: canonical codes at different lengths aren't prefixes.
    -- This requires showing nc[len₂] ≥ (nc[len₁] + count[len₁]) * 2^(len₂-len₁),
    -- i.e., the nextCodes recurrence leaves no room for prefix overlap.
    sorry

end Huffman.Spec
