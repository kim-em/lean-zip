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

Kraft inequality analysis is in `Zip.Spec.HuffmanKraft`.
Property theorems (prefix-free proofs, injectivity, decode correctness)
are in `Zip.Spec.HuffmanTheorems`.
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
  · have p₁ : v₁ < 2 ^ i := Nat.lt_of_lt_of_le h₁ (Nat.pow_le_pow_right (by omega) (by omega))
    have p₂ : v₂ < 2 ^ i := Nat.lt_of_lt_of_le h₂ (Nat.pow_le_pow_right (by omega) (by omega))
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

private theorem nextCodes_go_size (blCount : Array Nat) (maxBits : Nat)
    (arr : Array Nat) (bits code : Nat) (hsize : arr.size = maxBits + 1) :
    (nextCodes.go blCount maxBits arr bits code).size = maxBits + 1 := by
  unfold nextCodes.go
  split
  · exact hsize
  · exact nextCodes_go_size blCount maxBits _ _ _
      (by simp [Array.set!_eq_setIfInBounds, hsize])
  termination_by maxBits + 1 - bits

/-- `nextCodes` returns an array of size `maxBits + 1`. -/
protected theorem nextCodes_size (blCount : Array Nat) (maxBits : Nat) :
    (nextCodes blCount maxBits).size = maxBits + 1 :=
  nextCodes_go_size blCount maxBits _ 1 0 (Array.size_replicate ..)

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

instance : Decidable (ValidLengths lengths maxBits) :=
  inferInstanceAs (Decidable (_ ∧ _))

end Huffman.Spec
