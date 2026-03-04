import Zip.Native.ZstdFrame

/-!
# Zstd Huffman Weight Validity Predicates

Formal specification of Zstd Huffman weight table validity and table structure,
based on RFC 8878 §4.2.1.

Zstd uses a weight-based Huffman representation distinct from DEFLATE's
code-length approach. Each symbol has a weight `w ≥ 0`; weight 0 means
the symbol is not present. For present symbols, the code length is
`maxBits + 1 - w`, and each weight contributes `2^(w-1)` to the weight
sum. An implicit last symbol fills the gap to complete the prefix code.

Key invariants formalized here:
- `ValidWeights`: basic well-formedness of a weight array
- `KraftComplete`: the Kraft equality for Zstd's weight encoding
- `ValidHuffmanTable`: structural invariants of the flat lookup table

These predicates are prerequisites for future proof work:
- `buildZstdHuffmanTable` correctness: valid weights → valid table
- Huffman decode determinism: valid table + valid bitstream → unique symbol
- Literal section roundtrip: Huffman-encode then decode recovers original
- Prefix-freeness: the codes derived from valid weights form a prefix-free set
-/

namespace Zstd.Spec.Huffman

open Zip.Native

/-! ## Helper definitions -/

/-- Compute the weight sum: `∑ 2^(w-1)` for all weights `w > 0`.
    This is the core quantity in Zstd's Huffman weight scheme (RFC 8878 §4.2.1.1). -/
def weightSum (weights : Array UInt8) : Nat :=
  weights.foldl (fun acc w =>
    if w.toNat > 0 then acc + (1 <<< (w.toNat - 1)) else acc) 0

/-- A natural number is a positive power of two.
    Uses bit manipulation: a positive `n` is a power of 2 iff `n &&& (n-1) = 0`. -/
def IsPowerOfTwo (n : Nat) : Prop := n > 0 ∧ n &&& (n - 1) = 0

instance (n : Nat) : Decidable (IsPowerOfTwo n) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ## Validity predicates -/

/-- A weight array is valid when:
    (a) it has at least one entry,
    (b) at least one weight is non-zero (some symbol must be present),
    (c) no individual weight exceeds 13 (practical bound per RFC 8878). -/
def ValidWeights (weights : Array UInt8) : Prop :=
  weights.size ≥ 1 ∧
  (∃ w ∈ weights.toList, w ≠ (0 : UInt8)) ∧
  (∀ w ∈ weights.toList, w.toNat ≤ 13)

instance {weights : Array UInt8} : Decidable (ValidWeights weights) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The Kraft equality for Zstd's weight encoding (RFC 8878 §4.2.1.1).
    The sum of `2^(w_i - 1)` for all explicit positive weights must be:
    (a) positive (at least one symbol present),
    (b) strictly less than `2^maxBits` (room for the implicit last symbol), and
    (c) the remainder `2^maxBits - weightSum` must be a positive power of 2
        (ensuring the implicit last symbol has a valid integral weight).
    Additionally, `maxBits ≥ 1`. -/
def KraftComplete (weights : Array UInt8) (maxBits : Nat) : Prop :=
  maxBits ≥ 1 ∧
  weightSum weights > 0 ∧
  weightSum weights < 2 ^ maxBits ∧
  IsPowerOfTwo (2 ^ maxBits - weightSum weights)

instance {weights : Array UInt8} {maxBits : Nat} :
    Decidable (KraftComplete weights maxBits) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- A Zstd Huffman table is valid when:
    (a) `table.size = 1 <<< maxBits` (flat lookup table is correctly sized),
    (b) all entries have `numBits ≤ maxBits` (no code exceeds the table depth),
    (c) all symbol values are valid byte indices (`< 256`). -/
def ValidHuffmanTable (table : Array HuffmanEntry) (maxBits : Nat) : Prop :=
  table.size = 1 <<< maxBits ∧
  (∀ w ∈ table.toList, w.numBits.toNat ≤ maxBits) ∧
  (∀ w ∈ table.toList, w.symbol.toNat < 256)

instance {table : Array HuffmanEntry} {maxBits : Nat} :
    Decidable (ValidHuffmanTable table maxBits) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-! ## Basic properties -/

/-- `IsPowerOfTwo` holds for 1. -/
theorem isPowerOfTwo_one : IsPowerOfTwo 1 := by decide

/-- 0 is not a power of two. -/
theorem not_isPowerOfTwo_zero : ¬IsPowerOfTwo 0 := by decide

/-- `IsPowerOfTwo` holds for `2^k` when `k` is small. -/
theorem isPowerOfTwo_two : IsPowerOfTwo 2 := by decide
theorem isPowerOfTwo_four : IsPowerOfTwo 4 := by decide

/-! ## Correctness theorems for table construction -/

/-- When `buildZstdHuffmanTable` succeeds, the table has the correct size.
    Follows from the table being initialized via `Array.replicate (1 <<< maxBits)`
    and only modified by `Array.set!`, which preserves size. -/
theorem buildZstdHuffmanTable_tableSize (weights : Array UInt8)
    (ht : ZstdHuffmanTable) (h : buildZstdHuffmanTable weights = .ok ht) :
    ht.table.size = 1 <<< ht.maxBits := by
  sorry -- Requires unfolding monadic for-loops and showing Array.set! preserves size.

/-- When `buildZstdHuffmanTable` succeeds, `maxBits ≥ 1`.
    Follows from `weightsToMaxBits` requiring at least one non-zero weight
    (weight sum ≥ 1), which forces `maxBits ≥ 1`. -/
theorem buildZstdHuffmanTable_maxBits_pos (weights : Array UInt8)
    (ht : ZstdHuffmanTable) (h : buildZstdHuffmanTable weights = .ok ht) :
    ht.maxBits ≥ 1 := by
  sorry -- Requires unfolding weightsToMaxBits and its while loop.

/-- When `weightsToMaxBits` succeeds with result `m`, the weight sum satisfies
    `2^(m-1) ≤ weightSum weights` and `weightSum weights < 2^m`.
    The returned `m` is the smallest value such that `weightSum weights < 2^m`. -/
theorem weightsToMaxBits_bounds (weights : Array UInt8)
    (m : Nat) (h : weightsToMaxBits weights = .ok m) :
    2 ^ (m - 1) ≤ weightSum weights ∧ weightSum weights < 2 ^ m := by
  sorry -- Requires unfolding weightsToMaxBits, relating its internal weightSum
        -- computation to Zstd.Spec.Huffman.weightSum, and analyzing the while loop.

end Zstd.Spec.Huffman
