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

The array pipeline uses an array-native **two-queue (van Leeuwen) Huffman tree
build** (`huffTreeDepthsN`) in place of the spec's `List.mergeSort` +
`insertByWeight` construction. The spec built the tree with `O(n²)` boxed list
insertion and a `BuildTree` allocation per merge; on stat-shifting corpora the
observation-divergence splitter cuts each member into hundreds of blocks, each
paying two tree builds (~286-symbol lit + 30-symbol dist), so `insertByWeight`
was the top compress profile entry. The two-queue build is `O(n)` over a sorted
leaf array with no tree allocation: merged nodes are produced in non-decreasing
weight order, so a second array + two head indices suffice, and leaf depths are
recovered by a single reverse pass over parent pointers.

This is a **heuristic replacement** (route (b)): on weight ties the two-queue
tree can differ from the insertion tree, so the emitted code lengths — and hence
the compressed bytes — differ slightly from the spec pipeline, but only among
equally optimal codes. The spec `computeCodeLengths`/`limitedPairs` stay untouched
as the reference. What downstream consumers actually need — result size, every
length in `[1, maxBits]` (`bounded`), the Kraft inequality (`ValidLengths`), and
a nonzero length for every used symbol (`nonzero`) — depends only on the *shape*
of the output (`symsByFreq.zip (expandBl bl ++ padding)` wrapped in
`fixKraftList`), not on which histogram `bl` the build produces. So those
properties are re-proved here for the list twin `computeCodeLengthsListN` by
copying the spec proofs with `limitedPairs` swapped for `limitedPairsN`; the
`fixKraftList`/`expandBl`/`assignLengths` infrastructure is shared verbatim.

The capped-histogram Kraft repair (`cappedBlCount`/`repairBl`/`expandBl`) and the
array symbol→length assignment (`assignLengthsN`) and Kraft fixup
(`fixKraftListN`) are reused unchanged; only the tree build itself is new.
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
    · rw [ite_eq_left h]
    · rw [ite_eq_right h, List.set_eq_of_length_le (by omega)]

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

/-! ## Array-native two-queue Huffman tree build

`huffTreeDepthsN` replaces the spec's `mergeSort` + `insertByWeight` +
`BuildTree.depths` with the van Leeuwen two-queue method over flat arrays. Nodes
live in a single index space: leaves `0 .. n-1` (sorted ascending by weight),
internal nodes `n .. 2n-2` created in non-decreasing weight order. A merge always
combines the two smallest available among the leaf-queue front and the
merged-queue front, so two head indices suffice — no per-merge allocation. Parent
pointers always point to a *higher* index (the parent is created later), so a
single reverse pass computes every node's depth. Only the leaf depths feed the
shared `cappedBlCount`/`repairBl`/`expandBl` histogram pipeline.

No property of this build is proved: the downstream proofs need only the *shape*
of `limitedPairsN`'s output, which holds for any histogram (see the module
docstring). Correctness here is a *ratio* concern (the build must be an optimal
Huffman construction), validated by the corpus benchmark, not a *validity*
concern (guaranteed by `fixKraftList`). -/

/-- Select the smaller-weight node between the leaf-queue front (`leafHead`, valid
    while `< n`) and the merged-queue front (`intHead`, valid while `< next`),
    returning the chosen node index and the advanced head indices. Ties go to the
    merged node (mirrors `insertByWeight` placing a merged node before equal-weight
    leaves). The caller guarantees at least one queue is non-empty. -/
def popMinNode (weight : Array Nat) (n leafHead intHead next : Nat) : Nat × Nat × Nat :=
  if leafHead < n then
    if intHead < next then
      if weight[intHead]! ≤ weight[leafHead]! then (intHead, leafHead, intHead + 1)
      else (leafHead, leafHead + 1, intHead)
    else (leafHead, leafHead + 1, intHead)
  else (intHead, leafHead, intHead + 1)

/-- The merge loop: create internal node `next` (`n ≤ next ≤ 2n-2`) from the two
    smallest available nodes, record their parent, and recurse. Threads `weight`
    (destructively updated in place at RC 1) and `parent`; returns the completed
    parent array once every internal node exists. -/
def mergeLoopN (n : Nat) (weight parent : Array Nat) (leafHead intHead next : Nat) : Array Nat :=
  if _h : next < 2 * n - 1 then
    let (a, leafHead₁, intHead₁) := popMinNode weight n leafHead intHead next
    let (b, leafHead₂, intHead₂) := popMinNode weight n leafHead₁ intHead₁ next
    let weight := weight.set! next (weight[a]! + weight[b]!)
    let parent := (parent.set! a next).set! b next
    mergeLoopN n weight parent leafHead₂ intHead₂ (next + 1)
  else
    parent
termination_by 2 * n - 1 - next
decreasing_by omega

/-- Fill leaf/internal depths bottom-up: process indices `i` down from the node
    below the root, setting `depth[i] = depth[parent[i]] + 1`. Every non-root node
    has `parent[i] > i` and the root (index `2n-2`, depth 0) is left as the array's
    initial `0`, so each parent's depth is already set when its child is reached. -/
def depthLoopN (parent depth : Array Nat) (i : Nat) : Array Nat :=
  match i with
  | 0 => depth.set! 0 (depth[parent[0]!]! + 1)
  | i + 1 =>
    depthLoopN parent (depth.set! (i + 1) (depth[parent[i + 1]!]! + 1)) i

/-- Leaf depths of the two-queue Huffman tree over the nonzero `(symbol, freq)`
    pairs, as `(0, depth)` pairs (the symbol slot is a placeholder — only the depth
    multiset feeds `cappedBlCount`). Degenerate `≤ 1`-leaf inputs never reach here
    on the multi-symbol path; they return a harmless empty/zero list. -/
def huffTreeDepthsN (nz : List (Nat × Nat)) : List (Nat × Nat) :=
  let leafW := (nz.map (·.2)).toArray.qsort (· < ·)
  let n := leafW.size
  if n ≤ 1 then []
  else
    let weight := leafW ++ Array.replicate (n - 1) 0
    let parent := mergeLoopN n weight (Array.replicate (2 * n - 1) 0) 0 n n
    let depth := depthLoopN parent (Array.replicate (2 * n - 1) 0) (2 * n - 3)
    (List.range n).map (fun i => ((0 : Nat), depth[i]!))

/-! ## Array-native `limitedPairs` twin

`limitedPairsN` has the exact output shape of the spec `limitedPairs`
(`symsByFreq.zip (expandBl bl ++ padding)`); only the histogram `bl` comes from
the two-queue build instead of `buildHuffmanTree`. The shared `cappedBlCount` +
`repairBl` cap-and-repair keeps the code length-limited and complete. -/

/-- Array-native twin of `limitedPairs`: same frequency-sorted symbol list and
    same `expandBl`-plus-padding shape, but the depth histogram comes from the
    two-queue build (`huffTreeDepthsN`) rather than `buildHuffmanTree`. -/
def limitedPairsN (nz : List (Nat × Nat)) (maxBits : Nat) : List (Nat × Nat) :=
  let capped := cappedBlCount (huffTreeDepthsN nz) maxBits
  let bl := repairBl capped (blKraft capped maxBits - 2 ^ maxBits) maxBits
  let symsByFreq := (nz.mergeSort (fun a b => b.2 ≤ a.2)).map (·.1)
  symsByFreq.zip (expandBl bl maxBits ++ List.replicate symsByFreq.length maxBits)

/-- Every length in a `limitedPairsN` pair is in `[1, maxBits]` (shape fact, from
    the padded `expandBl`). Copy of `limitedPairs_mem_range` — the histogram is
    irrelevant. -/
theorem limitedPairsN_mem_range (nz : List (Nat × Nat)) (maxBits : Nat) (hmb : maxBits ≥ 1) :
    ∀ p ∈ limitedPairsN nz maxBits, 1 ≤ p.2 ∧ p.2 ≤ maxBits := by
  intro p hp
  simp only [limitedPairsN] at hp
  obtain ⟨_, h2⟩ := List.of_mem_zip hp
  rw [List.mem_append] at h2
  cases h2 with
  | inl h => exact expandBl_mem_range _ _ p.2 h
  | inr h => rw [List.mem_replicate] at h; omega

/-- The first components of `limitedPairsN` are exactly the frequency-sorted
    symbols. Copy of `limitedPairs_map_fst`. -/
theorem limitedPairsN_map_fst (nz : List (Nat × Nat)) (maxBits : Nat) :
    (limitedPairsN nz maxBits).map Prod.fst
      = (nz.mergeSort (fun a b => b.2 ≤ a.2)).map (·.1) := by
  simp only [limitedPairsN]
  apply List.map_fst_zip
  rw [List.length_append, List.length_replicate]
  omega

/-- Every symbol with a nonzero frequency receives a pair in `limitedPairsN`.
    Copy of `limitedPairs_covers`. -/
theorem limitedPairsN_covers (nz : List (Nat × Nat)) (maxBits s : Nat)
    (hs : s ∈ nz.map (·.1)) : ∃ p ∈ limitedPairsN nz maxBits, p.1 = s := by
  have hs' : s ∈ (limitedPairsN nz maxBits).map Prod.fst := by
    rw [limitedPairsN_map_fst]
    exact ((List.mergeSort_perm nz _).map (·.1)).mem_iff.mpr hs
  rw [List.mem_map] at hs'
  obtain ⟨p, hp, hps⟩ := hs'
  exact ⟨p, hp, hps⟩

/-! ## Array-based code-length pipeline -/

/-- Array twin of `computeCodeLengths`: same branch structure, but the tree build
    is the array-native two-queue (`limitedPairsN`) and the symbol→length
    assignment and Kraft fixup are array-native. Returns an `Array Nat` directly,
    saving the emitters the `List Nat → Array` round-trip. -/
def computeCodeLengthsN (freqs : List (Nat × Nat)) (numSymbols : Nat)
    (maxBits : Nat := 15) : Array Nat :=
  let nonzero := freqs.filter (fun (_, f) => f > 0)
  if nonzero.isEmpty then Array.replicate numSymbols 0
  else if nonzero.length == 1 then
    let (sym, _) := nonzero.head!
    assignLengthsN [(sym, 1)] numSymbols
  else
    fixKraftListN (assignLengthsN (limitedPairsN nonzero maxBits) numSymbols) maxBits

/-- List twin of `computeCodeLengthsN`: identical to the spec `computeCodeLengths`
    except the multi-symbol branch uses `limitedPairsN` (two-queue build). This is
    the value `(computeCodeLengthsN …).toList` reduces to; its properties are the
    spec ones with `limitedPairs` swapped for `limitedPairsN`. -/
def computeCodeLengthsListN (freqs : List (Nat × Nat)) (numSymbols : Nat)
    (maxBits : Nat := 15) : List Nat :=
  let nonzero := freqs.filter (fun (_, f) => f > 0)
  if nonzero.isEmpty then List.replicate numSymbols 0
  else if nonzero.length == 1 then
    let (sym, _) := nonzero.head!
    assignLengths [(sym, 1)] numSymbols
  else
    fixKraftList (assignLengths (limitedPairsN nonzero maxBits) numSymbols) maxBits

/-- **Correspondence.** The array pipeline read back as a list is the list twin
    `computeCodeLengthsListN` (the array-native assignment/fixup are `toList`-equal
    to the spec `List` ones; the two-queue build is shared verbatim). -/
theorem computeCodeLengthsN_toList (freqs : List (Nat × Nat)) (numSymbols maxBits : Nat) :
    (computeCodeLengthsN freqs numSymbols maxBits).toList
      = computeCodeLengthsListN freqs numSymbols maxBits := by
  simp only [computeCodeLengthsN, computeCodeLengthsListN]
  split
  · exact Array.toList_replicate ..
  · split
    · exact assignLengthsN_toList ..
    · rw [fixKraftListN_toList, assignLengthsN_toList]

/-- The array pipeline is the `toArray` of the list twin. -/
theorem computeCodeLengthsN_toArray (freqs : List (Nat × Nat)) (numSymbols maxBits : Nat) :
    computeCodeLengthsN freqs numSymbols maxBits
      = (computeCodeLengthsListN freqs numSymbols maxBits).toArray := by
  rw [← computeCodeLengthsN_toList, Array.toArray_toList]

/-- `computeCodeLengthsListN` produces a list of length `numSymbols`. Copy of
    `computeCodeLengths_length` (histogram-independent). -/
theorem computeCodeLengthsListN_length (freqs : List (Nat × Nat)) (n maxBits : Nat) :
    (computeCodeLengthsListN freqs n maxBits).length = n := by
  simp only [computeCodeLengthsListN]
  split
  · exact List.length_replicate ..
  · split
    · exact assignLengths_length ..
    · simp only [fixKraftList]
      split
      · exact assignLengths_length ..
      · simp only [List.length_map]; exact assignLengths_length ..

/-- `computeCodeLengthsN` produces an array of size `numSymbols`. -/
theorem computeCodeLengthsN_size (freqs : List (Nat × Nat)) (numSymbols maxBits : Nat) :
    (computeCodeLengthsN freqs numSymbols maxBits).size = numSymbols := by
  rw [← Array.length_toList, computeCodeLengthsN_toList, computeCodeLengthsListN_length]

/-! ## Properties of the list twin

The two-queue build only changes the *multi-symbol* branch (`limitedPairsN` vs
`limitedPairs`); the empty and single-symbol branches are byte-for-byte identical
to the spec `computeCodeLengths`. So each property is proved by delegating the
non-multi branches to the (public) spec lemma via `..._eq_of_small`, and proving
only the multi branch directly from the `limitedPairsN` shape facts
(`_mem_range`, `_covers`) — the same facts the spec proof uses. The tree-dependent
completeness (`computeCodeLengths_complete`) is *not* reproved: it is not consumed
downstream, and a heuristic build need not produce the same complete code. -/

/-- On non-multi inputs (`< 2` nonzero-frequency symbols) the two-queue twin is
    exactly the spec `computeCodeLengths`: the differing `limitedPairsN`/`limitedPairs`
    branch is unreachable, and the empty/single branches are identical. Used to
    delegate the empty/single-symbol `ValidLengths` to the spec (whose proof needs
    the file-private single-symbol Kraft lemmas). -/
theorem computeCodeLengthsListN_eq_of_small (freqs : List (Nat × Nat)) (n maxBits : Nat)
    (h : (freqs.filter (fun (_, f) => f > 0)).length < 2) :
    computeCodeLengthsListN freqs n maxBits = computeCodeLengths freqs n maxBits := by
  have h' : (freqs.filter (fun x => decide (x.2 > 0))).length < 2 := h
  simp only [computeCodeLengthsListN, computeCodeLengths]
  split
  · rfl
  · split
    · rfl
    · rename_i h1 h2
      simp only [List.isEmpty_iff_length_eq_zero] at h1
      simp only [beq_iff_eq] at h2
      omega

/-- On multi-symbol inputs (`≥ 2` nonzero-frequency symbols) the two-queue twin
    reduces to its `fixKraftList ∘ assignLengths ∘ limitedPairsN` form: the
    empty/single branches are excluded. Lets the shape-based property proofs work
    on the concrete `limitedPairsN` term. -/
theorem computeCodeLengthsListN_multi (freqs : List (Nat × Nat)) (n maxBits : Nat)
    (h : 2 ≤ (freqs.filter (fun (_, f) => f > 0)).length) :
    computeCodeLengthsListN freqs n maxBits
      = fixKraftList (assignLengths
          (limitedPairsN (freqs.filter (fun x => decide (x.2 > 0))) maxBits) n) maxBits := by
  have h' : 2 ≤ (freqs.filter (fun x => decide (x.2 > 0))).length := h
  simp only [computeCodeLengthsListN]
  split
  · rename_i he; simp only [List.isEmpty_iff_length_eq_zero] at he; omega
  · split
    · rename_i hs1; simp only [beq_iff_eq] at hs1; omega
    · rfl

/-- All lengths are `≤ maxBits`. Copy of `computeCodeLengths_bounded` with
    `limitedPairs → limitedPairsN` (uses only the shared shape lemma
    `limitedPairsN_mem_range`). -/
theorem computeCodeLengthsListN_bounded (freqs : List (Nat × Nat)) (n maxBits : Nat)
    (hmb : maxBits > 0) :
    ∀ l ∈ computeCodeLengthsListN freqs n maxBits, l ≤ maxBits := by
  simp only [computeCodeLengthsListN]
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
      exact (limitedPairsN_mem_range _ maxBits hmb p hp).2

/-- The lengths satisfy `ValidLengths`. The multi-symbol branch is proved directly
    from the shape (`fixKraftList_kraft` needs only `length ≤ 2^maxBits`); the
    empty/single branches delegate to `computeCodeLengths_valid` via
    `computeCodeLengthsListN_eq_of_small`. -/
theorem computeCodeLengthsListN_valid (freqs : List (Nat × Nat)) (n : Nat)
    (maxBits : Nat) (hmb : maxBits > 0) (hn : n ≤ 2 ^ maxBits) :
    ValidLengths (computeCodeLengthsListN freqs n maxBits) maxBits := by
  by_cases hmulti : 2 ≤ (freqs.filter (fun (_, f) => f > 0)).length
  · refine ⟨computeCodeLengthsListN_bounded freqs n maxBits hmb, ?_⟩
    rw [computeCodeLengthsListN_multi freqs n maxBits hmulti]
    apply fixKraftList_kraft
    rw [assignLengths_length]
    exact hn
  · rw [computeCodeLengthsListN_eq_of_small freqs n maxBits (by omega)]
    exact computeCodeLengths_valid freqs n maxBits hmb hn

/-- Every nonzero-frequency symbol `< numSymbols` gets a nonzero length. Copy of
    `computeCodeLengths_nonzero` with `limitedPairs → limitedPairsN` (uses only the
    shared shape lemmas `limitedPairsN_mem_range`/`limitedPairsN_covers`). -/
theorem computeCodeLengthsListN_nonzero (freqs : List (Nat × Nat)) (numSymbols maxBits : Nat)
    (hmb : maxBits > 0) (s : Nat) (hs : s < numSymbols)
    (hfreq : ∃ p ∈ freqs, p.1 = s ∧ p.2 > 0) :
    (computeCodeLengthsListN freqs numSymbols maxBits)[s]! ≠ 0 := by
  simp only [computeCodeLengthsListN]
  obtain ⟨p, hp, hps, hpf⟩ := hfreq
  have hs_nz : p ∈ freqs.filter (fun x => decide (x.2 > 0)) := by
    simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨hp, hpf⟩
  have hne : ¬(freqs.filter (fun x => decide (x.2 > 0))).isEmpty := by
    intro h; rw [List.isEmpty_iff_length_eq_zero] at h
    exact absurd (List.length_pos_of_mem hs_nz) (by omega)
  rw [ite_eq_right hne]
  let nz := freqs.filter (fun x => decide (x.2 > 0))
  split
  · rename_i hlen1
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
  · apply fixKraftList_nonzero _ _ hmb s
    · rw [assignLengths_length]; exact hs
    · have hpos := assignLengths_pos (limitedPairsN nz maxBits) numSymbols s hs
        (fun q hq _ => by have := (limitedPairsN_mem_range nz maxBits hmb q hq).1; omega)
        (limitedPairsN_covers nz maxBits s (List.mem_map.mpr ⟨p, hs_nz, hps⟩))
      exact Nat.pos_iff_ne_zero.mp hpos

end Huffman.Spec
