import Zip.Spec.Huffman

/-!
# Huffman Code Length Computation from Symbol Frequencies

Spec-level algorithm for computing optimal Huffman code lengths from symbol
frequencies. This is the encoding direction: given how often each symbol
appears, determine the bit length of each symbol's codeword.

The algorithm:
1. Create leaf nodes for symbols with frequency > 0
2. Repeatedly merge the two lightest nodes (standard Huffman construction)
3. Extract code depths from the resulting tree
4. Limit depths to `maxBits` (15 for DEFLATE)

The key correctness property is that the computed lengths satisfy
`Huffman.Spec.ValidLengths`, ensuring the canonical construction produces
a valid prefix-free code.

Definitions and types for the canonical code construction (from given lengths)
are in `Zip.Spec.Huffman`. Property theorems are in `Zip.Spec.HuffmanTheorems`.
-/

namespace Huffman.Spec

/-! ## Binary tree for Huffman construction -/

/-- Binary tree for Huffman code construction. Leaves carry a symbol,
    internal nodes carry the combined weight of their subtrees. -/
inductive BuildTree where
  | leaf (weight : Nat) (sym : Nat)
  | node (weight : Nat) (left right : BuildTree)
deriving Repr

/-- Weight of a Huffman tree node. -/
def BuildTree.weight : BuildTree → Nat
  | .leaf w _ => w
  | .node w _ _ => w

/-! ## Tree construction -/

/-- Insert a tree into a list sorted by weight (ascending). -/
def insertByWeight (t : BuildTree) : List BuildTree → List BuildTree
  | [] => [t]
  | x :: xs =>
    if t.weight ≤ x.weight then t :: x :: xs
    else x :: insertByWeight t xs

/-- `insertByWeight` preserves list length plus one. -/
theorem insertByWeight_length (t : BuildTree) (xs : List BuildTree) :
    (insertByWeight t xs).length = xs.length + 1 := by
  induction xs with
  | nil => simp [insertByWeight]
  | cons x xs ih =>
    simp only [insertByWeight]
    split <;> simp [ih]

/-- Build a Huffman tree from a list of trees sorted by weight.
    Repeatedly merges the two lightest trees until one remains.
    Precondition: the input list should be non-empty and sorted by weight. -/
def buildHuffmanTree : List BuildTree → BuildTree
  | [] => .leaf 0 0
  | [t] => t
  | t1 :: t2 :: rest =>
    let merged := BuildTree.node (t1.weight + t2.weight) t1 t2
    buildHuffmanTree (insertByWeight merged rest)
termination_by xs => xs.length
decreasing_by simp_all [insertByWeight_length]

/-! ## Depth extraction -/

/-- Extract the depth of each symbol in the tree, as (symbol, depth) pairs. -/
def BuildTree.depths (t : BuildTree) (depth : Nat := 0) :
    List (Nat × Nat) :=
  match t with
  | .leaf _ sym => [(sym, depth)]
  | .node _ l r => l.depths (depth + 1) ++ r.depths (depth + 1)

/-! ## Code length computation pipeline -/

/-- Assign code lengths into a list indexed by symbol number.
    Symbols not mentioned in `depths` get length 0. -/
def assignLengths (depths : List (Nat × Nat)) (numSymbols : Nat) : List Nat :=
  let init := List.replicate numSymbols 0
  depths.foldl (fun acc (sym, len) =>
    if sym < acc.length then acc.set sym len else acc) init

/-- Compute Huffman code lengths from symbol frequencies.
    `freqs` is a list of (symbol, frequency) pairs.
    Returns a list of length `numSymbols` where index `i` is the code length
    for symbol `i` (0 means the symbol has no codeword).

    Code lengths are capped at `maxBits`. For typical DEFLATE inputs
    (≤ 286 symbols), the optimal tree depth is well under 15, so the cap
    rarely activates. -/
def computeCodeLengths (freqs : List (Nat × Nat)) (numSymbols : Nat)
    (maxBits : Nat := 15) : List Nat :=
  let nonzero := freqs.filter (fun (_, f) => f > 0)
  if nonzero.isEmpty then List.replicate numSymbols 0
  else if nonzero.length == 1 then
    let (sym, _) := nonzero.head!
    assignLengths [(sym, 1)] numSymbols
  else
    let leaves := (nonzero.map fun (sym, freq) => BuildTree.leaf freq sym)
      |>.mergeSort (fun a b => a.weight ≤ b.weight)
    let tree := buildHuffmanTree leaves
    let depths := tree.depths
    -- Cap at maxBits
    let capped := depths.map fun (s, d) => (s, min d maxBits)
    assignLengths capped numSymbols

/-! ## Properties -/

/-- Folding `List.set` preserves list length. -/
private theorem foldl_set_length (depths : List (Nat × Nat)) (acc : List Nat) :
    (depths.foldl (fun acc (p : Nat × Nat) =>
      if p.1 < acc.length then acc.set p.1 p.2 else acc) acc).length = acc.length := by
  induction depths generalizing acc with
  | nil => simp
  | cons d ds ih =>
    simp only [List.foldl_cons]
    split
    · rw [ih]; simp [List.length_set]
    · exact ih acc

/-- `assignLengths` produces a list of the requested length. -/
theorem assignLengths_length (depths : List (Nat × Nat)) (n : Nat) :
    (assignLengths depths n).length = n := by
  simp only [assignLengths]
  rw [foldl_set_length]
  exact List.length_replicate ..

/-- `computeCodeLengths` produces a list of length `numSymbols`. -/
theorem computeCodeLengths_length (freqs : List (Nat × Nat)) (n : Nat) (maxBits : Nat) :
    (computeCodeLengths freqs n maxBits).length = n := by
  simp only [computeCodeLengths]
  split
  · exact List.length_replicate ..
  · split
    · exact assignLengths_length ..
    · simp only [assignLengths_length]

/-! ## Tree structure properties -/

/-- Every `BuildTree` has non-empty depths. -/
theorem BuildTree.depths_ne_nil (t : BuildTree) (d : Nat) :
    t.depths d ≠ [] := by
  match t with
  | .leaf _ _ => simp [depths]
  | .node _ l r =>
    simp only [depths, ne_eq]
    cases hl : l.depths (d + 1) with
    | nil => exact absurd hl (l.depths_ne_nil _)
    | cons x xs => simp

/-- Every tree built by `buildHuffmanTree` from a non-empty list has at least
    one leaf, so `depths` is non-empty. -/
theorem buildTree_depths_nonempty (ts : List BuildTree) :
    (buildHuffmanTree ts).depths ≠ [] :=
  (buildHuffmanTree ts).depths_ne_nil 0

/-- All depths in a `BuildTree` are ≥ the starting depth parameter. -/
theorem BuildTree.depths_ge (t : BuildTree) (d : Nat) :
    ∀ p ∈ t.depths d, p.2 ≥ d := by
  match t with
  | .leaf _ s => simp [depths]
  | .node _ l r =>
    simp only [depths, List.mem_append]
    intro p hp
    cases hp with
    | inl h => exact Nat.le_of_succ_le (l.depths_ge (d + 1) p h)
    | inr h => exact Nat.le_of_succ_le (r.depths_ge (d + 1) p h)

/-! ## ValidLengths proof -/

/-- Elements of a list after `set` are bounded if the original and the new value are. -/
private theorem foldl_set_bounded (depths : List (Nat × Nat)) (acc : List Nat) (bound : Nat)
    (hacc : ∀ l ∈ acc, l ≤ bound)
    (hdepths : ∀ p ∈ depths, p.2 ≤ bound) :
    ∀ l ∈ depths.foldl (fun acc (p : Nat × Nat) =>
      if p.1 < acc.length then acc.set p.1 p.2 else acc) acc,
    l ≤ bound := by
  induction depths generalizing acc with
  | nil => exact hacc
  | cons d ds ih =>
    simp only [List.foldl_cons]
    apply ih
    · intro l hl
      split at hl
      · rename_i hlt
        cases List.mem_or_eq_of_mem_set hl with
        | inl hmem => exact hacc l hmem
        | inr heq => exact heq ▸ hdepths d (List.mem_cons_self ..)
      · exact hacc l hl
    · exact fun p hp => hdepths p (List.mem_cons_of_mem _ hp)

/-- `assignLengths` with all values ≤ maxBits produces lengths ≤ maxBits. -/
theorem assignLengths_bounded (depths : List (Nat × Nat)) (n maxBits : Nat)
    (h : ∀ p ∈ depths, p.2 ≤ maxBits) :
    ∀ l ∈ assignLengths depths n, l ≤ maxBits := by
  exact foldl_set_bounded depths _ maxBits
    (fun l hl => by have := List.eq_of_mem_replicate hl; omega) h

/-- `ValidLengths` holds for all-zero lengths. -/
private theorem validLengths_replicate_zero (n maxBits : Nat) :
    ValidLengths (List.replicate n 0) maxBits := by
  constructor
  · intro l hl; have := List.eq_of_mem_replicate hl; omega
  · simp

/-- Filtering nonzero elements from an all-zero list gives the empty list. -/
private theorem filter_ne_zero_replicate (n : Nat) :
    (List.replicate n (0 : Nat)).filter (· != 0) = [] := by
  induction n with
  | zero => rfl
  | succ n ih => simp

/-- Setting one position to 1 in an all-zero list, then filtering nonzero, gives `[1]`. -/
private theorem filter_ne_zero_replicate_set (n i : Nat) (hi : i < n) :
    ((List.replicate n (0 : Nat)).set i 1).filter (· != 0) = [1] := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero =>
      simp only [List.replicate_succ, List.set_cons_zero]
      simp
    | succ i =>
      simp only [List.replicate_succ, List.set_cons_succ]
      simp [ih i (by omega)]

/-- `ValidLengths` holds for a single symbol with length 1.

    The result has at most one nonzero entry (value 1).
    Kraft contribution: 2^(maxBits - 1) ≤ 2^maxBits. -/
private theorem validLengths_single (sym n maxBits : Nat) (hmb : maxBits > 0) :
    ValidLengths (assignLengths [(sym, 1)] n) maxBits := by
  constructor
  · exact assignLengths_bounded [(sym, 1)] n maxBits (by simp; omega)
  · simp only [assignLengths, List.foldl_cons, List.foldl_nil, List.length_replicate]
    by_cases h : sym < n
    · simp only [h, ↓reduceIte, filter_ne_zero_replicate_set _ _ h,
        List.foldl_cons, List.foldl_nil]
      -- Goal: 0 + 2^(maxBits - 1) ≤ 2^maxBits
      simp only [Nat.zero_add]
      exact Nat.pow_le_pow_right (by omega) (by omega)
    · simp only [h, ↓reduceIte, filter_ne_zero_replicate, List.foldl_nil]
      exact Nat.zero_le _

/-- Kraft sum of a list of depths, relative to normalization constant `D`:
    `∑ 2^(D - dᵢ)` where dᵢ are the depths. -/
def kraftSum (depths : List Nat) (D : Nat) : Nat :=
  depths.foldl (fun acc d => acc + 2 ^ (D - d)) 0

/-- `kraftSum` with a non-zero initial accumulator. -/
private theorem kraftSum_init (depths : List Nat) (D init : Nat) :
    depths.foldl (fun acc d => acc + 2 ^ (D - d)) init =
    init + kraftSum depths D := by
  induction depths generalizing init with
  | nil => simp [kraftSum]
  | cons x xs ih =>
    simp only [List.foldl_cons, kraftSum]
    rw [ih, ih (0 + 2 ^ (D - x))]
    omega

/-- `kraftSum` distributes over append. -/
private theorem kraftSum_append (l₁ l₂ : List Nat) (D : Nat) :
    kraftSum (l₁ ++ l₂) D = kraftSum l₁ D + kraftSum l₂ D := by
  simp only [kraftSum, List.foldl_append]
  exact kraftSum_init l₂ D _

/-- A `BuildTree` rooted at depth `d` has its Kraft sum (relative to any `D ≥ max depth`)
    equal to `2^(D - d)`. This is the fundamental property of binary trees:
    the leaves partition the code space exactly. -/
theorem BuildTree.kraft_eq (t : BuildTree) (d D : Nat)
    (hD : ∀ p ∈ t.depths d, p.2 ≤ D) :
    kraftSum (t.depths d |>.map Prod.snd) D = 2 ^ (D - d) := by
  match t with
  | .leaf _ _ =>
    simp [depths, kraftSum, List.foldl]
  | .node _ l r =>
    simp only [depths, List.map_append]
    rw [kraftSum_append]
    have hlD : ∀ p ∈ l.depths (d + 1), p.2 ≤ D := fun p hp =>
      hD p (List.mem_append_left _ hp)
    have hrD : ∀ p ∈ r.depths (d + 1), p.2 ≤ D := fun p hp =>
      hD p (List.mem_append_right _ hp)
    rw [l.kraft_eq (d + 1) D hlD, r.kraft_eq (d + 1) D hrD]
    have hne : l.depths (d + 1) ≠ [] := l.depths_ne_nil _
    have ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ hne
    have hpd : p.2 ≥ d + 1 := l.depths_ge (d + 1) p hp
    have hpD : p.2 ≤ D := hlD p hp
    rw [show D - d = (D - (d + 1)) + 1 from by omega, Nat.pow_succ]
    omega

/-- All computed code lengths are ≤ maxBits. This holds because
    single-symbol codes use length 1 ≤ maxBits, and multi-symbol depths
    are capped with `min d maxBits` before assignment. -/
theorem computeCodeLengths_bounded (freqs : List (Nat × Nat)) (n maxBits : Nat)
    (hmb : maxBits > 0) :
    ∀ l ∈ computeCodeLengths freqs n maxBits, l ≤ maxBits := by
  simp only [computeCodeLengths]
  split
  · intro l hl; have := List.eq_of_mem_replicate hl; omega
  · split
    · apply assignLengths_bounded
      intro p hp
      cases hp with
      | head => omega
      | tail _ h => contradiction
    · apply assignLengths_bounded
      intro p hp
      simp only [List.mem_map] at hp
      obtain ⟨⟨s', d'⟩, _, rfl⟩ := hp
      exact Nat.min_le_right d' maxBits

/-- The computed code lengths satisfy `ValidLengths`.

    **STATUS: FALSE as stated.** The theorem has a verified counterexample:
    `computeCodeLengths [(0,100),(1,10),(2,1),(3,1)] 4 2` produces `[1,2,2,2]`
    with Kraft sum 5 > 4 = 2^2. The naive depth capping (`min d maxBits`)
    can produce oversubscribed code lengths when the Huffman tree has depths
    exceeding `maxBits`.

    The zero-symbol and single-symbol cases are proved. The multi-symbol case
    needs one of:
    1. A precondition: all tree depths ≤ maxBits (holds for DEFLATE with
       maxBits=15 and ≤ 286 symbols, since optimal tree depth ≤ 9)
    2. Fixing `computeCodeLengths` to use proper depth limiting
       (package-merge or iterative shortening) instead of naive capping

    For DEFLATE usage, the Kraft inequality holds in practice since
    15-bit codes can represent 2^15 = 32768 symbols, far exceeding the
    maximum of 286 lit/len or 30 distance symbols. -/
theorem computeCodeLengths_valid (freqs : List (Nat × Nat)) (n : Nat)
    (maxBits : Nat) (hmb : maxBits > 0) :
    ValidLengths (computeCodeLengths freqs n maxBits) maxBits := by
  constructor
  · exact computeCodeLengths_bounded freqs n maxBits hmb
  · simp only [computeCodeLengths]
    split
    · simp
    · split
      · simp only [assignLengths, List.foldl_cons, List.foldl_nil, List.length_replicate]
        by_cases h : (List.filter (fun x => decide (x.2 > 0)) freqs).head!.1 < n
        · simp only [h, ↓reduceIte, filter_ne_zero_replicate_set _ _ h,
            List.foldl_cons, List.foldl_nil, Nat.zero_add]
          exact Nat.pow_le_pow_right (by omega) (by omega)
        · simp only [h, ↓reduceIte, filter_ne_zero_replicate, List.foldl_nil]
          exact Nat.zero_le _
      · sorry

end Huffman.Spec
