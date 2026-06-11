import Zip.Spec.Huffman
import ZipForStd.List

/-!
# Huffman Code Length Computation from Symbol Frequencies

Spec-level algorithm for computing optimal Huffman code lengths from symbol
frequencies. This is the encoding direction: given how often each symbol
appears, determine the bit length of each symbol's codeword.

The algorithm:
1. Create leaf nodes for symbols with frequency > 0
2. Repeatedly merge the two lightest nodes (standard Huffman construction)
3. Extract code depths from the resulting tree
4. Limit depths to `maxBits` (15 for DEFLATE), with a Kraft inequality fixup

The key correctness property is that the computed lengths satisfy
`Huffman.Spec.ValidLengths`, ensuring the canonical construction produces
a valid prefix-free code.

Definitions and types for the canonical code construction (from given lengths)
are in `Zip.Spec.Huffman`. Kraft inequality analysis is in `Zip.Spec.HuffmanKraft`.
Property theorems are in `Zip.Spec.HuffmanTheorems`.
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
  | nil => simp only [insertByWeight, List.length_cons, List.length_nil]
  | cons x xs ih =>
    simp only [insertByWeight]
    split <;> simp only [List.length_cons, ih] <;> omega

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
decreasing_by simp only [insertByWeight_length, List.length_cons]; omega

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

/-- Kraft sum of a list of depths, relative to normalization constant `D`:
    `∑ 2^(D - dᵢ)` where dᵢ are the depths. -/
def kraftSum (depths : List Nat) (D : Nat) : Nat :=
  depths.foldl (fun acc d => acc + 2 ^ (D - d)) 0

/-- Fix code lengths to satisfy the Kraft inequality. If the Kraft sum
    exceeds `2^maxBits`, set all non-zero lengths to `maxBits`.
    This produces valid (though potentially suboptimal) codes. -/
def fixKraftList (lengths : List Nat) (maxBits : Nat) : List Nat :=
  if kraftSum (lengths.filter (· != 0)) maxBits ≤ 2 ^ maxBits then lengths
  else lengths.map fun l => if l == 0 then 0 else maxBits

/-! ## Proper length-limiting (zlib `gen_bitlen`, not the flat fallback)

The naive "cap each depth at `maxBits`, and if that breaks the Kraft inequality
flatten *every* code to `maxBits`" is catastrophic: a Huffman tree whose natural
depth exceeds the limit by even one bit collapses to a uniform `maxBits`-bit
code, which is worse than fixed Huffman — so the encoder silently falls back to a
fixed block, giving up 20–30% on every large file. Instead we redistribute the
overflow the way zlib's `gen_bitlen` does: cap, then repair the small Kraft
overflow by moving leaves through the `bl_count` histogram, and assign the
resulting lengths to symbols by decreasing frequency.

These functions are *heuristics* — they decide only how many codes get each
length. `fixKraftList` still wraps the result, so validity (`ValidLengths`) is
guaranteed regardless, and they carry no proof obligation; the only properties
the proofs use are structural (every produced length is in `[1, maxBits]`, and
every symbol receives one), which the `zip`+padding shape below makes immediate. -/

/-- Histogram of code lengths after capping each natural depth at `maxBits`. -/
def cappedBlCount (depths : List (Nat × Nat)) (maxBits : Nat) : Array Nat := Id.run do
  let mut bl : Array Nat := Array.replicate (maxBits + 2) 0
  for p in depths do
    let dc := min p.2 maxBits
    bl := bl.set! dc ((bl.getD dc 0) + 1)
  return bl

/-- Largest length `≤ start` with a positive count in `bl` (0 if none). -/
def findBelow (bl : Array Nat) (start : Nat) : Nat :=
  if start = 0 then 0
  else if bl.getD start 0 > 0 then start
  else findBelow bl (start - 1)
termination_by start

/-- Kraft sum of a `bl_count` histogram in units of `2^-maxBits`:
    `Σ_l bl[l]·2^(maxBits−l)` over `l ∈ [1, maxBits]`. A complete code sums to
    exactly `2^maxBits`; a capped histogram exceeds it by the overflow the
    repair must remove. -/
def blKraft (bl : Array Nat) (maxBits : Nat) : Nat :=
  (List.range maxBits).foldl (fun acc i => acc + bl.getD (i + 1) 0 * 2 ^ (maxBits - (i + 1))) 0

/-- Repair a capped `bl_count` so the code is complete (Kraft-exact) within
    `maxBits` (zlib `gen_bitlen`'s move): take the deepest depth `bits` below
    `maxBits` with a leaf, move that leaf to `bits+1` and pair it with an
    overflow leaf pulled up from `maxBits`. Each step lowers the Kraft sum by
    exactly 1 (in `2^-maxBits` units) and preserves the leaf count, so calling
    it with `excess = blKraft bl maxBits − 2^maxBits` lands exactly on a
    complete code. The updates must be sequential `set!`s on the current
    array: when `bits + 1 = maxBits` the `+2` and `−1` compose on the same
    entry (a chained read of the *original* array here used to overwrite the
    increment, silently dropping leaves and forcing the flat
    `fixKraftList` fallback — emitting incomplete codes that zlib's inflate
    rejects). Heuristic only. -/
def repairBl (bl : Array Nat) (excess maxBits : Nat) : Array Nat :=
  match excess with
  | 0 => bl
  | e + 1 =>
    let bits := findBelow bl (maxBits - 1)
    if bits == 0 then bl  -- defensive: unreachable while over-subscribed
    else
      let bl := bl.set! bits ((bl.getD bits 0) - 1)
      let bl := bl.set! (bits + 1) ((bl.getD (bits + 1) 0) + 2)
      let bl := bl.set! maxBits ((bl.getD maxBits 0) - 1)
      repairBl bl e maxBits

/-- The multiset of code lengths a `bl_count` histogram describes, ascending:
    `bl.getD l 0` copies of each `l ∈ [1, maxBits]`. Every element is in
    `[1, maxBits]` by construction (the only fact the proofs need). -/
def expandBl (bl : Array Nat) (maxBits : Nat) : List Nat :=
  (List.range maxBits).flatMap (fun i => List.replicate (bl.getD (i + 1) 0) (i + 1))

/-- Proper length-limited Huffman lengths as `(symbol, length)` pairs: build the
    tree, cap+repair its depths into a complete `≤ maxBits` code, and hand the
    lengths to symbols by decreasing frequency (most frequent → shortest). The
    `maxBits` padding guarantees every symbol gets a length even if the heuristic
    repair under-produces; on the common path only the real lengths are used. -/
def limitedPairs (nonzero : List (Nat × Nat)) (maxBits : Nat) : List (Nat × Nat) :=
  let leaves := (nonzero.map fun p => BuildTree.leaf p.2 p.1).mergeSort
                  (fun a b => a.weight ≤ b.weight)
  let depths := (buildHuffmanTree leaves).depths
  let capped := cappedBlCount depths maxBits
  let bl := repairBl capped (blKraft capped maxBits - 2 ^ maxBits) maxBits
  let symsByFreq := (nonzero.mergeSort (fun a b => b.2 ≤ a.2)).map (·.1)
  symsByFreq.zip (expandBl bl maxBits ++ List.replicate symsByFreq.length maxBits)

/-- Compute Huffman code lengths from symbol frequencies.
    `freqs` is a list of (symbol, frequency) pairs.
    Returns a list of length `numSymbols` where index `i` is the code length
    for symbol `i` (0 means the symbol has no codeword).

    Multi-symbol inputs use proper length-limiting (`limitedPairs`); the result
    is wrapped in `fixKraftList`, which guarantees the Kraft inequality (and hence
    `ValidLengths`) even if the heuristic repair ever leaves a residual overflow. -/
def computeCodeLengths (freqs : List (Nat × Nat)) (numSymbols : Nat)
    (maxBits : Nat := 15) : List Nat :=
  let nonzero := freqs.filter (fun (_, f) => f > 0)
  if nonzero.isEmpty then List.replicate numSymbols 0
  else if nonzero.length == 1 then
    let (sym, _) := nonzero.head!
    assignLengths [(sym, 1)] numSymbols
  else
    fixKraftList (assignLengths (limitedPairs nonzero maxBits) numSymbols) maxBits

/-! ## Properties -/

/-- Folding `List.set` preserves list length. -/
private theorem foldl_set_length (depths : List (Nat × Nat)) (acc : List Nat) :
    (depths.foldl (fun acc (p : Nat × Nat) =>
      if p.1 < acc.length then acc.set p.1 p.2 else acc) acc).length = acc.length := by
  induction depths generalizing acc with
  | nil => simp only [List.foldl_nil]
  | cons d ds ih =>
    simp only [List.foldl_cons]
    split
    · rw [ih, List.length_set]
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
    · simp only [fixKraftList]
      split
      · exact assignLengths_length ..
      · simp only [List.length_map]; exact assignLengths_length ..

/-! ## Tree structure properties -/

/-- Every `BuildTree` has non-empty depths. -/
theorem BuildTree.depths_ne_nil (t : BuildTree) (d : Nat) :
    t.depths d ≠ [] := by
  match t with
  | .leaf _ _ => simp only [depths, ne_eq, List.cons_ne_nil, not_false_eq_true]
  | .node _ l r =>
    simp only [depths, ne_eq]
    cases hl : l.depths (d + 1) with
    | nil => exact absurd hl (l.depths_ne_nil _)
    | cons x xs => simp only [List.append_ne_nil_of_left_ne_nil, ne_eq, List.cons_ne_nil,
        not_false_eq_true]

/-- Every tree built by `buildHuffmanTree` from a non-empty list has at least
    one leaf, so `depths` is non-empty. -/
theorem buildTree_depths_nonempty (ts : List BuildTree) :
    (buildHuffmanTree ts).depths ≠ [] :=
  (buildHuffmanTree ts).depths_ne_nil 0

/-- All depths in a `BuildTree` are ≥ the starting depth parameter. -/
theorem BuildTree.depths_ge (t : BuildTree) (d : Nat) :
    ∀ p ∈ t.depths d, p.2 ≥ d := by
  match t with
  | .leaf _ s => simp only [depths, List.mem_cons, List.mem_nil_iff, or_false, forall_eq,
      Nat.le_refl]
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
      · cases List.mem_or_eq_of_mem_set hl with
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

/-- Filtering nonzero elements from an all-zero list gives the empty list. -/
private theorem filter_ne_zero_replicate (n : Nat) :
    (List.replicate n (0 : Nat)).filter (· != 0) = [] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ, List.filter_cons, bne_self_eq_false,
      Bool.false_eq_true, ↓reduceIte, ih]

/-- Setting one position to 1 in an all-zero list, then filtering nonzero, gives `[1]`. -/
private theorem filter_ne_zero_replicate_set (n i : Nat) (hi : i < n) :
    ((List.replicate n (0 : Nat)).set i 1).filter (· != 0) = [1] := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero =>
      simp only [List.replicate_succ, List.set_cons_zero, List.filter_cons,
        filter_ne_zero_replicate]; rfl
    | succ i =>
      simp only [List.replicate_succ, List.set_cons_succ, List.filter_cons,
        bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, ih i (by omega)]

/-- `ValidLengths` holds for a single symbol with length 1.

    The result has at most one nonzero entry (value 1).
    Kraft contribution: 2^(maxBits - 1) ≤ 2^maxBits. -/
private theorem validLengths_single (sym n maxBits : Nat) (hmb : maxBits > 0) :
    ValidLengths (assignLengths [(sym, 1)] n) maxBits := by
  constructor
  · exact assignLengths_bounded [(sym, 1)] n maxBits (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp; subst hp; omega)
  · simp only [assignLengths, List.foldl_cons, List.foldl_nil, List.length_replicate]
    by_cases h : sym < n
    · simp only [h, ↓reduceIte, filter_ne_zero_replicate_set _ _ h,
        List.foldl_cons, List.foldl_nil]
      -- Goal: 0 + 2^(maxBits - 1) ≤ 2^maxBits
      simp only [Nat.zero_add]
      exact Nat.pow_le_pow_right (by omega) (by omega)
    · simp only [h, ↓reduceIte, filter_ne_zero_replicate, List.foldl_nil]
      exact Nat.zero_le _

/-- `kraftSum` with a non-zero initial accumulator. -/
private theorem kraftSum_init (depths : List Nat) (D init : Nat) :
    depths.foldl (fun acc d => acc + 2 ^ (D - d)) init =
    init + kraftSum depths D := by
  induction depths generalizing init with
  | nil => simp only [List.foldl_nil, kraftSum, Nat.add_zero]
  | cons x xs ih =>
    simp only [List.foldl_cons, kraftSum]
    rw [ih, ih (0 + 2 ^ (D - x))]
    omega

/-- `kraftSum` distributes over append. -/
private theorem kraftSum_append (l₁ l₂ : List Nat) (D : Nat) :
    kraftSum (l₁ ++ l₂) D = kraftSum l₁ D + kraftSum l₂ D := by
  simp only [kraftSum, List.foldl_append]
  exact kraftSum_init l₂ D _

/-- `kraftSum` of a cons: pull the head's contribution out front. -/
private theorem kraftSum_cons (a : Nat) (l : List Nat) (D : Nat) :
    kraftSum (a :: l) D = 2 ^ (D - a) + kraftSum l D := by
  simp only [kraftSum, List.foldl_cons, Nat.zero_add]
  exact kraftSum_init l D _

/-- `kraftSum` of a `replicate`: `k` copies of depth `v` contribute `k · 2^(D−v)`. -/
private theorem kraftSum_replicate (k v D : Nat) :
    kraftSum (List.replicate k v) D = k * 2 ^ (D - v) := by
  induction k with
  | zero => simp only [List.replicate_zero, kraftSum, List.foldl_nil, Nat.zero_mul]
  | succ k ih => rw [List.replicate_succ, kraftSum_cons, ih, Nat.succ_mul, Nat.add_comm]

/-- The Kraft sum of the histogram-expanded length list, taken over an arbitrary
    list of bit-lengths `is`, equals the per-length `bl[l]·2^(maxBits−l)` sum. The
    `blKraft`/`expandBl` correspondence below is the `is = List.range maxBits` case. -/
private theorem kraftSum_flatMap_replicate (bl : Array Nat) (maxBits : Nat) (is : List Nat) :
    kraftSum (is.flatMap (fun i => List.replicate (bl.getD (i + 1) 0) (i + 1))) maxBits
      = is.foldl (fun acc i => acc + bl.getD (i + 1) 0 * 2 ^ (maxBits - (i + 1))) 0 := by
  induction is with
  | nil => simp only [List.flatMap_nil, kraftSum, List.foldl_nil]
  | cons x xs ih =>
    rw [List.flatMap_cons, kraftSum_append, kraftSum_replicate, ih,
      List.foldl_cons, Nat.zero_add, ← List.foldl_add_init]

/-- `kraftSum` of `expandBl` equals the histogram Kraft sum `blKraft`. The expanded
    length multiset and the `bl_count` histogram describe the same code, so they have
    the same Kraft sum — this is the bridge that lets the histogram-level completeness
    of `repairBl` transfer to the length list `limitedPairs` hands out. -/
theorem expandBl_kraft (bl : Array Nat) (maxBits : Nat) :
    kraftSum (expandBl bl maxBits) maxBits = blKraft bl maxBits :=
  kraftSum_flatMap_replicate bl maxBits (List.range maxBits)

/-- A `BuildTree` rooted at depth `d` has its Kraft sum (relative to any `D ≥ max depth`)
    equal to `2^(D - d)`. This is the fundamental property of binary trees:
    the leaves partition the code space exactly. -/
theorem BuildTree.kraft_eq (t : BuildTree) (d D : Nat)
    (hD : ∀ p ∈ t.depths d, p.2 ≤ D) :
    kraftSum (t.depths d |>.map Prod.snd) D = 2 ^ (D - d) := by
  match t with
  | .leaf _ _ =>
    simp only [depths, List.map_cons, List.map_nil, kraftSum, List.foldl_cons, List.foldl_nil,
      Nat.zero_add]
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

/-! ## Kraft fixup properties -/

/-- `fixKraftList` preserves list length. -/
theorem fixKraftList_length (lengths : List Nat) (maxBits : Nat) :
    (fixKraftList lengths maxBits).length = lengths.length := by
  simp only [fixKraftList]
  split
  · rfl
  · exact List.length_map ..

/-- When all entries of a list equal `D`, `kraftSum l D = l.length`. -/
private theorem kraftSum_self (l : List Nat) (D : Nat) (h : ∀ x ∈ l, x = D) :
    kraftSum l D = l.length := by
  induction l with
  | nil => simp only [kraftSum, List.foldl_nil, List.length_nil]
  | cons x xs ih =>
    simp only [kraftSum, List.foldl_cons]
    rw [kraftSum_init]
    have hx : x = D := h x (List.mem_cons_self ..)
    subst hx
    simp only [Nat.sub_self, Nat.pow_zero, Nat.zero_add, List.length_cons]
    rw [ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]
    omega

/-- All non-zero entries produced by the fallback map are `maxBits`. -/
private theorem filter_map_eq_maxBits (l : List Nat) (maxBits : Nat) :
    ∀ x ∈ (l.map fun a => if a == 0 then 0 else maxBits).filter (· != 0),
    x = maxBits := by
  intro x hx
  simp only [List.mem_filter, List.mem_map] at hx
  obtain ⟨⟨a, _, rfl⟩, hne⟩ := hx
  split <;> rename_i ha
  · simp only [beq_iff_eq] at ha; subst ha
    simp only [beq_self_eq_true, ↓reduceIte, bne_self_eq_false, Bool.false_eq_true] at hne
  · rfl

/-- `fixKraftList` satisfies the Kraft inequality when the list length
    is at most `2^maxBits`. -/
theorem fixKraftList_kraft (lengths : List Nat) (maxBits : Nat)
    (hlen : lengths.length ≤ 2 ^ maxBits) :
    kraftSum ((fixKraftList lengths maxBits).filter (· != 0)) maxBits ≤ 2 ^ maxBits := by
  simp only [fixKraftList]
  split
  · assumption
  · rw [kraftSum_self _ _ (filter_map_eq_maxBits lengths maxBits)]
    have h1 := List.length_filter_le (fun (x : Nat) => x != 0)
      (lengths.map fun a => if a == 0 then 0 else maxBits)
    simp only [List.length_map] at h1
    omega

/-- All values in `fixKraftList` are bounded by `maxBits`. -/
theorem fixKraftList_bounded (lengths : List Nat) (maxBits : Nat)
    (h : ∀ l ∈ lengths, l ≤ maxBits) :
    ∀ l ∈ fixKraftList lengths maxBits, l ≤ maxBits := by
  simp only [fixKraftList]
  split
  · exact h
  · intro l hl
    simp only [List.mem_map] at hl
    obtain ⟨a, _, rfl⟩ := hl
    split <;> omega

/-! ## `limitedPairs` structural properties

Only two facts about `limitedPairs` reach the proofs, and both are independent of
the (heuristic) `bl_count` repair: every produced length lies in `[1, maxBits]`,
and every symbol of the (frequency-sorted) input receives a pair. They follow
from the `zip`-with-padded-`expandBl` shape. -/

/-- Every length `expandBl` produces is in `[1, maxBits]`. -/
theorem expandBl_mem_range (bl : Array Nat) (maxBits : Nat) :
    ∀ l ∈ expandBl bl maxBits, 1 ≤ l ∧ l ≤ maxBits := by
  intro l hl
  simp only [expandBl, List.mem_flatMap] at hl
  obtain ⟨i, hi, hl'⟩ := hl
  rw [List.mem_replicate] at hl'
  rw [List.mem_range] at hi
  omega

/-- Every length in a `limitedPairs` pair is in `[1, maxBits]`. -/
theorem limitedPairs_mem_range (nz : List (Nat × Nat)) (maxBits : Nat) (hmb : maxBits ≥ 1) :
    ∀ p ∈ limitedPairs nz maxBits, 1 ≤ p.2 ∧ p.2 ≤ maxBits := by
  intro p hp
  simp only [limitedPairs] at hp
  obtain ⟨_, h2⟩ := List.of_mem_zip hp
  rw [List.mem_append] at h2
  cases h2 with
  | inl h => exact expandBl_mem_range _ _ p.2 h
  | inr h => rw [List.mem_replicate] at h; omega

/-- The first components of `limitedPairs` are exactly the frequency-sorted
    symbols (the padding makes the right list long enough to cover them all). -/
theorem limitedPairs_map_fst (nz : List (Nat × Nat)) (maxBits : Nat) :
    (limitedPairs nz maxBits).map Prod.fst
      = (nz.mergeSort (fun a b => b.2 ≤ a.2)).map (·.1) := by
  simp only [limitedPairs]
  apply List.map_fst_zip
  rw [List.length_append, List.length_replicate]
  omega

/-- Every symbol with a nonzero frequency receives a pair in `limitedPairs`. -/
theorem limitedPairs_covers (nz : List (Nat × Nat)) (maxBits s : Nat)
    (hs : s ∈ nz.map (·.1)) : ∃ p ∈ limitedPairs nz maxBits, p.1 = s := by
  have hs' : s ∈ (limitedPairs nz maxBits).map Prod.fst := by
    rw [limitedPairs_map_fst]
    exact ((List.mergeSort_perm nz _).map (·.1)).mem_iff.mpr hs
  rw [List.mem_map] at hs'
  obtain ⟨p, hp, hps⟩ := hs'
  exact ⟨p, hp, hps⟩

/-! ## computeCodeLengths properties -/

/-- All computed code lengths are ≤ maxBits: single-symbol codes use length 1,
    and multi-symbol lengths come from `limitedPairs` (all in `[1, maxBits]`),
    then pass through `fixKraftList` (which preserves the ≤ `maxBits` bound). -/

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
    · apply fixKraftList_bounded
      apply assignLengths_bounded
      intro p hp
      exact (limitedPairs_mem_range _ maxBits hmb p hp).2

/-- The computed code lengths satisfy `ValidLengths`.

    The precondition `n ≤ 2^maxBits` ensures there are enough code points
    to represent all symbols. For DEFLATE (maxBits=15, n ≤ 286), this holds
    since 2^15 = 32768 >> 286. The `fixKraftList` fallback guarantees the
    Kraft inequality even when naive depth capping would oversubscribe. -/
theorem computeCodeLengths_valid (freqs : List (Nat × Nat)) (n : Nat)
    (maxBits : Nat) (hmb : maxBits > 0) (hn : n ≤ 2 ^ maxBits) :
    ValidLengths (computeCodeLengths freqs n maxBits) maxBits := by
  constructor
  · exact computeCodeLengths_bounded freqs n maxBits hmb
  · simp only [computeCodeLengths]
    split
    · simp only [filter_ne_zero_replicate, List.foldl_nil, Nat.zero_le]
    · split
      · exact (validLengths_single _ n maxBits hmb).2
      · -- Multi-symbol case: fixKraftList handles the Kraft inequality
        apply fixKraftList_kraft
        rw [assignLengths_length]
        exact hn

/-! ## computeCodeLengths nonzero property -/

/-- `fixKraftList` preserves nonzero entries: if `l[i]! ≠ 0` then
    `(fixKraftList l maxBits)[i]! ≠ 0` (assuming `maxBits > 0`). -/
theorem fixKraftList_nonzero (l : List Nat) (maxBits : Nat) (hmb : maxBits > 0)
    (i : Nat) (hi : i < l.length) (hne : l[i]! ≠ 0) :
    (fixKraftList l maxBits)[i]! ≠ 0 := by
  simp only [fixKraftList]
  split
  · exact hne
  · rw [getElem!_pos (l.map _) i (by simp only [List.length_map]; exact hi)]
    simp only [List.getElem_map]
    rw [show l[i] = l[i]! from by rw [getElem!_pos l i hi]]
    split
    · rename_i heq; simp only [beq_iff_eq] at heq; omega
    · omega


/-- Generalized: foldl set over an accumulator yields positive at position `s`
    when either the accumulator already has a positive value at `s`, or some entry
    for `s` exists with positive value. All entries for `s` must be positive. -/
private theorem foldl_set_pos_or_exists (depths : List (Nat × Nat)) (acc : List Nat)
    (s : Nat) (hs : s < acc.length)
    (hpos : ∀ p ∈ depths, p.1 = s → p.2 > 0)
    (hor : acc[s]! > 0 ∨ ∃ p ∈ depths, p.1 = s) :
    (depths.foldl (fun acc (p : Nat × Nat) =>
      if p.1 < acc.length then acc.set p.1 p.2 else acc) acc)[s]! > 0 := by
  induction depths generalizing acc with
  | nil =>
    cases hor with
    | inl h => exact h
    | inr h => exact absurd h (by simp only [List.not_mem_nil, false_and, not_exists,
        not_false_eq_true, implies_true])
  | cons d ds ih =>
    simp only [List.foldl_cons]
    have hs' : s < (if d.1 < acc.length then acc.set d.1 d.2 else acc).length := by
      split
      · rw [List.length_set]; exact hs
      · exact hs
    apply ih _ hs' (fun p hp => hpos p (List.mem_cons_of_mem _ hp))
    by_cases hds : d.1 = s
    · left; split
      · rw [hds, getElem!_pos _ s (by simp only [List.length_set]; exact hs)]
        simp only [List.getElem_set_self]
        exact hpos d (List.mem_cons_self ..) hds
      · omega
    ·
      cases hor with
      | inl h =>
        left; split
        · have hs_set : s < (acc.set d.1 d.2).length := by simp only [List.length_set]; exact hs
          rw [getElem!_pos _ s hs_set, List.getElem_set_ne hds hs_set,
              ← getElem!_pos acc s hs]; exact h
        · exact h
      | inr h =>
        obtain ⟨p, hp, hps⟩ := h
        cases hp with
        | head => exact absurd hps hds
        | tail _ hmem => exact Or.inr ⟨p, hmem, hps⟩

/-- If `(s, d)` appears in a list of depths, `d > 0`, and `s < n`, and all
    entries for `s` are positive, then `(assignLengths depths n)[s]! > 0`. -/
theorem assignLengths_pos (depths : List (Nat × Nat)) (n : Nat)
    (s : Nat) (hs : s < n)
    (hpos : ∀ p ∈ depths, p.1 = s → p.2 > 0) (hexists : ∃ p ∈ depths, p.1 = s) :
    (assignLengths depths n)[s]! > 0 := by
  simp only [assignLengths]
  apply foldl_set_pos_or_exists
  · simp only [List.length_replicate]; exact hs
  · exact hpos
  · exact Or.inr hexists

/-- `insertByWeight` preserves membership: elements of `xs` and the inserted `t`
    are all in the result. -/
private theorem insertByWeight_mem (t : BuildTree) (xs : List BuildTree) :
    ∀ x, x ∈ insertByWeight t xs ↔ x = t ∨ x ∈ xs := by
  intro x
  induction xs with
  | nil => simp only [insertByWeight, List.mem_cons, List.mem_nil_iff, or_false]
  | cons y ys ih =>
    simp only [insertByWeight]
    split
    · simp only [List.mem_cons]
    · simp only [List.mem_cons, ih]
      simp only [or_left_comm]

/-- Symbol `s` is a leaf symbol in tree `t`. -/
private inductive BuildTree.HasSym : BuildTree → Nat → Prop where
  | leaf (w s : Nat) : HasSym (.leaf w s) s
  | nodeLeft (w : Nat) (l r : BuildTree) (s : Nat) : l.HasSym s → (BuildTree.node w l r).HasSym s
  | nodeRight (w : Nat) (l r : BuildTree) (s : Nat) : r.HasSym s → (BuildTree.node w l r).HasSym s

/-- If `t.HasSym s`, then `s` appears in `t.depths d` for any `d`. -/
private theorem BuildTree.HasSym.in_depths {t : BuildTree} {s : Nat} (h : t.HasSym s) :
    ∀ d, ∃ d', (s, d') ∈ t.depths d := by
  induction h with
  | leaf w s =>
    intro d; exact ⟨d, by simp only [depths, List.mem_cons, List.mem_nil_iff, or_false]⟩
  | nodeLeft w l r s _ ih =>
    intro d
    obtain ⟨d', hd'⟩ := ih (d + 1)
    exact ⟨d', List.mem_append_left _ hd'⟩
  | nodeRight w l r s _ ih =>
    intro d
    obtain ⟨d', hd'⟩ := ih (d + 1)
    exact ⟨d', List.mem_append_right _ hd'⟩

/-- `insertByWeight` on a node preserves all symbols from that node. -/
private theorem buildHuffmanTree_HasSym_insertByWeight
    (merged : BuildTree) (rest : List BuildTree) (s : Nat)
    (h : ∃ t ∈ insertByWeight merged rest, t.HasSym s) :
    ∃ t ∈ merged :: rest, t.HasSym s := by
  obtain ⟨t, ht_mem, ht_sym⟩ := h
  rw [insertByWeight_mem] at ht_mem
  cases ht_mem with
  | inl heq =>
    refine ⟨merged, ?_, heq ▸ ht_sym⟩
    exact List.Mem.head _
  | inr hmem => exact ⟨t, List.Mem.tail _ hmem, ht_sym⟩

/-- `buildHuffmanTree` preserves all symbols from the input list:
    if some input tree has symbol `s`, then the output tree has symbol `s`. -/
private theorem buildHuffmanTree_HasSym (ts : List BuildTree) (s : Nat)
    (h : ∃ t ∈ ts, t.HasSym s) : (buildHuffmanTree ts).HasSym s := by
  match ts with
  | [] => obtain ⟨_, hmem, _⟩ := h; exact nomatch hmem
  | [t] =>
    obtain ⟨t', hmem, hsym⟩ := h
    simp only [buildHuffmanTree, List.mem_cons, List.mem_nil_iff, or_false] at hmem ⊢
    exact hmem ▸ hsym
  | t1 :: t2 :: rest =>
    simp only [buildHuffmanTree]
    have : (insertByWeight (BuildTree.node (t1.weight + t2.weight) t1 t2) rest).length < (t1 :: t2 :: rest).length := by
      simp only [insertByWeight_length, List.length_cons]; omega
    apply buildHuffmanTree_HasSym _ s
    obtain ⟨t', hmem, hsym⟩ := h
    simp only [List.mem_cons] at hmem
    cases hmem with
    | inl h =>
      exact ⟨_, (insertByWeight_mem _ _ _).mpr (Or.inl rfl), .nodeLeft _ _ _ _ (h ▸ hsym)⟩
    | inr h => cases h with
      | inl h =>
        exact ⟨_, (insertByWeight_mem _ _ _).mpr (Or.inl rfl), .nodeRight _ _ _ _ (h ▸ hsym)⟩
      | inr hmem =>
        exact ⟨t', (insertByWeight_mem _ _ _).mpr (Or.inr hmem), hsym⟩
termination_by ts.length

/-- `buildHuffmanTree` returns a node (not a leaf) when given ≥ 2 trees. -/
private theorem buildHuffmanTree_isNode (ts : List BuildTree) (h : ts.length ≥ 2) :
    ∃ w l r, buildHuffmanTree ts = BuildTree.node w l r := by
  match ts with
  | [] => simp only [List.length_nil] at h; omega
  | [_] => simp only [List.length_cons, List.length_nil] at h; omega
  | t1 :: t2 :: rest =>
    simp only [buildHuffmanTree]
    let merged := BuildTree.node (t1.weight + t2.weight) t1 t2
    by_cases hrest : rest = []
    · -- rest = [], so insertByWeight merged [] = [merged]
      subst hrest
      simp only [insertByWeight, buildHuffmanTree]
      exact ⟨_, _, _, rfl⟩
    · -- rest non-empty, insertByWeight has ≥ 2 elements, recurse
      have hge2 : (insertByWeight merged rest).length ≥ 2 := by
        rw [insertByWeight_length]
        cases rest with | nil => contradiction | cons _ _ => simp only [List.length_cons]; omega
      have : (insertByWeight merged rest).length < (t1 :: t2 :: rest).length := by
        simp only [insertByWeight_length, List.length_cons]; omega
      exact buildHuffmanTree_isNode _ hge2
termination_by ts.length

/-- All depths from `buildHuffmanTree` with ≥ 2 input trees are ≥ 1. -/
private theorem buildHuffmanTree_depths_ge_one (ts : List BuildTree) (h : ts.length ≥ 2)
    (p : Nat × Nat) (hp : p ∈ (buildHuffmanTree ts).depths 0) : p.2 ≥ 1 := by
  obtain ⟨w, l, r, htree⟩ := buildHuffmanTree_isNode ts h
  rw [htree, BuildTree.depths] at hp
  simp only [List.mem_append] at hp
  cases hp with
  | inl h => exact l.depths_ge 1 p h
  | inr h => exact r.depths_ge 1 p h

/-- If symbol `sym` appears as a leaf in any tree in `ts`, then `(sym, d)` appears
    in `(buildHuffmanTree ts).depths 0` for some `d`. -/
private theorem buildHuffmanTree_leaf_in_depths (ts : List BuildTree) (sym : Nat)
    (hmem : ∃ t ∈ ts, ∃ w, t = BuildTree.leaf w sym) :
    ∃ d, (sym, d) ∈ (buildHuffmanTree ts).depths 0 := by
  obtain ⟨t, ht_mem, w, ht_eq⟩ := hmem
  have hsym : t.HasSym sym := ht_eq ▸ .leaf w sym
  exact (buildHuffmanTree_HasSym ts sym ⟨t, ht_mem, hsym⟩).in_depths 0

/-- If symbol `s` appears with nonzero frequency in `freqs` and `s < numSymbols`,
    then `(computeCodeLengths freqs numSymbols maxBits)[s]! ≠ 0`.
    Requires `maxBits > 0`. -/
theorem computeCodeLengths_nonzero (freqs : List (Nat × Nat)) (numSymbols maxBits : Nat)
    (hmb : maxBits > 0) (s : Nat) (hs : s < numSymbols)
    (hfreq : ∃ p ∈ freqs, p.1 = s ∧ p.2 > 0) :
    (computeCodeLengths freqs numSymbols maxBits)[s]! ≠ 0 := by
  simp only [computeCodeLengths]
  obtain ⟨p, hp, hps, hpf⟩ := hfreq
  -- p has nonzero freq, so it passes the filter
  have hs_nz : p ∈ freqs.filter (fun x => decide (x.2 > 0)) := by
    simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨hp, hpf⟩
  -- Nonzero list is non-empty
  have hne : ¬(freqs.filter (fun x => decide (x.2 > 0))).isEmpty := by
    intro h; rw [List.isEmpty_iff_length_eq_zero] at h
    exact absurd (List.length_pos_of_mem hs_nz) (by omega)
  rw [if_neg hne]
  -- Abbreviate the nonzero list
  let nz := freqs.filter (fun x => decide (x.2 > 0))
  split
  · -- Single nonzero freq: must be symbol s
    rename_i hlen1
    have hs_nz' : p ∈ nz := hs_nz
    have hlen1' : nz.length = 1 := by rw [beq_iff_eq] at hlen1; exact hlen1
    have hhead : nz.head! = p := by
      have ⟨hd, tl, htl⟩ : ∃ hd tl, nz = hd :: tl := by
        cases hc : nz with
        | nil => rw [hc] at hs_nz'; exact nomatch hs_nz'
        | cons x xs => exact ⟨x, xs, rfl⟩
      have htl_nil : tl = [] := by
        rw [htl] at hlen1'; simp only [List.length_cons] at hlen1'
        exact List.eq_nil_of_length_eq_zero (by omega)
      rw [htl, htl_nil] at hs_nz'
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hs_nz'
      rw [htl, htl_nil]; simp only [List.head!]; exact hs_nz'.symm
    have hhead_fst : nz.head!.fst = s := by rw [hhead, hps]
    rw [show (nz.head!.fst, 1) = (s, 1) from by rw [hhead_fst]]
    have := assignLengths_pos [(s, 1)] numSymbols s hs
      (fun q hq _ => by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq; subst hq; omega)
      ⟨(s, 1), List.Mem.head _, rfl⟩
    omega
  · -- Multiple nonzero frequencies — proper length-limiting via `limitedPairs`.
    -- `fixKraftList` preserves nonzero, and `s` gets a pair (it is a nonzero
    -- symbol, hence in the frequency-sorted list) with a length ≥ 1 (every
    -- `limitedPairs` length is in `[1, maxBits]`).
    apply fixKraftList_nonzero _ _ hmb s
    · rw [assignLengths_length]; exact hs
    · have hpos := assignLengths_pos (limitedPairs nz maxBits) numSymbols s hs
        (fun q hq _ => by have := (limitedPairs_mem_range nz maxBits hmb q hq).1; omega)
        (limitedPairs_covers nz maxBits s (List.mem_map.mpr ⟨p, hs_nz, hps⟩))
      exact Nat.pos_iff_ne_zero.mp hpos

end Huffman.Spec
