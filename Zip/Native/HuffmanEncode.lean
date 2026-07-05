import Zip.Spec.HuffmanEncode

/-!
# Native array-based Huffman code-length construction

Array twins of the `List`-based code-length pipeline in
`Zip.Spec.HuffmanEncode`. The spec versions (`assignLengths`, `fixKraftList`,
`computeCodeLengths`) stay untouched as the reference; here we recompute the
same code lengths with `Array` accumulators so the hot `dynamicCodeLengths`
path (one build per split block per sizing candidate on large heterogeneous
members) no longer pays the `O(n²)` `List.set`/`List.length` churn that
`assignLengths` incurs, nor the allocator/reference-count traffic of the
`List Nat` result the emitters immediately `toArray` anyway.

The correspondence theorems (`computeCodeLengthsN_toList`,
`computeCodeLengthsN_toArray`) prove the array pipeline yields exactly the spec
`List`, so every downstream property of `computeCodeLengths` (length,
`ValidLengths`, completeness, nonzero) transfers verbatim and the compressed
output is byte-identical.

The tree build (`limitedPairs`) is reused unchanged: only the leaf-depth
histogram it feeds and the symbol→length assignment are array-native here. The
`O(n²)` cost lived in `assignLengths`, not the merge.
-/

namespace Huffman.Spec

/-! ## Array-based symbol→length assignment -/

/-- Array twin of `assignLengths`: assign code lengths into an array indexed by
    symbol number, symbols not mentioned getting length 0. `setIfInBounds`
    mirrors the `if sym < acc.length` guard of the `List` fold exactly, so an
    out-of-range symbol leaves the accumulator unchanged. -/
def assignLengthsN (depths : List (Nat × Nat)) (numSymbols : Nat) : Array Nat :=
  depths.foldl (fun acc (p : Nat × Nat) => acc.setIfInBounds p.1 p.2)
    (Array.replicate numSymbols 0)

/-- The array assignment, read back as a list, is the spec `List` assignment.
    Proved by an accumulator-generalized induction: `setIfInBounds`'s `toList`
    is `List.set`, and its size guard is the list-length guard. -/
theorem assignLengthsN_toList (depths : List (Nat × Nat)) (numSymbols : Nat) :
    (assignLengthsN depths numSymbols).toList = assignLengths depths numSymbols := by
  simp only [assignLengthsN, assignLengths]
  suffices h : ∀ (acc : Array Nat),
      (depths.foldl (fun acc (p : Nat × Nat) => acc.setIfInBounds p.1 p.2) acc).toList
        = depths.foldl (fun (acc : List Nat) (p : Nat × Nat) =>
            if p.1 < acc.length then acc.set p.1 p.2 else acc) acc.toList by
    have := h (Array.replicate numSymbols 0)
    simpa only [Array.toList_replicate] using this
  intro acc
  induction depths generalizing acc with
  | nil => simp only [List.foldl_nil]
  | cons d ds ih =>
    simp only [List.foldl_cons]
    rw [ih (acc.setIfInBounds d.1 d.2), Array.toList_setIfInBounds]
    by_cases h : d.1 < acc.toList.length
    · rw [if_pos h]
    · rw [if_neg h, List.set_eq_of_length_le (by omega)]

/-! ## Array-based Kraft fixup -/

/-- Array twin of `fixKraftList`. The Kraft-sum test is computed over the
    array's list view (an `O(n)` pass done once per call, not the `O(n²)`
    assignment it guards); on the common path the lengths pass through
    unchanged, and only the rare overflow branch rewrites via `Array.map`. -/
def fixKraftListN (lengths : Array Nat) (maxBits : Nat) : Array Nat :=
  if kraftSum (lengths.toList.filter (· != 0)) maxBits ≤ 2 ^ maxBits then lengths
  else lengths.map fun l => if l == 0 then 0 else maxBits

/-- The array Kraft fixup, read back as a list, is the spec `List` fixup. -/
theorem fixKraftListN_toList (lengths : Array Nat) (maxBits : Nat) :
    (fixKraftListN lengths maxBits).toList = fixKraftList lengths.toList maxBits := by
  simp only [fixKraftListN, fixKraftList]
  split
  · rfl
  · simp only [Array.toList_map]

/-! ## Array-based code-length pipeline -/

/-- Array twin of `computeCodeLengths`: same branch structure and same tree
    build (`limitedPairs`), but the symbol→length assignment and Kraft fixup are
    array-native. Returns the code lengths as an `Array Nat` directly, saving the
    emitters the `List Nat → Array` round-trip. -/
def computeCodeLengthsN (freqs : List (Nat × Nat)) (numSymbols : Nat)
    (maxBits : Nat := 15) : Array Nat :=
  let nonzero := freqs.filter (fun (_, f) => f > 0)
  if nonzero.isEmpty then Array.replicate numSymbols 0
  else if nonzero.length == 1 then
    let (sym, _) := nonzero.head!
    assignLengthsN [(sym, 1)] numSymbols
  else
    fixKraftListN (assignLengthsN (limitedPairs nonzero maxBits) numSymbols) maxBits

/-- **Correspondence.** The array pipeline read back as a list is exactly the
    spec `List` pipeline, so every property of `computeCodeLengths` transfers. -/
theorem computeCodeLengthsN_toList (freqs : List (Nat × Nat)) (numSymbols maxBits : Nat) :
    (computeCodeLengthsN freqs numSymbols maxBits).toList
      = computeCodeLengths freqs numSymbols maxBits := by
  simp only [computeCodeLengthsN, computeCodeLengths]
  split
  · exact Array.toList_replicate ..
  · split
    · exact assignLengthsN_toList ..
    · rw [fixKraftListN_toList, assignLengthsN_toList]

/-- The array pipeline is the `toArray` of the spec `List` pipeline: the form
    the emitters (which immediately `toArray`) consume. -/
theorem computeCodeLengthsN_toArray (freqs : List (Nat × Nat)) (numSymbols maxBits : Nat) :
    computeCodeLengthsN freqs numSymbols maxBits
      = (computeCodeLengths freqs numSymbols maxBits).toArray := by
  rw [← computeCodeLengthsN_toList, Array.toArray_toList]

/-- `computeCodeLengthsN` produces an array of size `numSymbols`. -/
theorem computeCodeLengthsN_size (freqs : List (Nat × Nat)) (numSymbols maxBits : Nat) :
    (computeCodeLengthsN freqs numSymbols maxBits).size = numSymbols := by
  rw [← Array.length_toList, computeCodeLengthsN_toList, computeCodeLengths_length]

end Huffman.Spec
