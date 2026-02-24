import Zip.Spec.HuffmanCorrect
import ZipForStd.Array

/-!
# Huffman fromLengths Loop Invariants

Proves that the `fromLengths` construction loop correctly builds a Huffman tree
whose leaves match the canonical code table (`allCodes`). Two main theorems:
- **`fromLengths_hasLeaf`**: every entry in `allCodes` becomes a leaf in the tree
- **`fromLengths_leaf_spec`**: every leaf in the tree corresponds to an `allCodes` entry
-/

namespace Deflate.Correctness

/-! ### Connecting fromLengths to allCodes -/

/-- When `fromLengths` succeeds, the tree is `fromLengthsTree`. -/
private theorem fromLengths_ok_eq (lengths : Array UInt8) (maxBits : Nat)
    (tree : Zip.Native.HuffTree)
    (htree : Zip.Native.HuffTree.fromLengths lengths maxBits = .ok tree) :
    tree = Zip.Native.HuffTree.fromLengthsTree lengths maxBits := by
  simp only [Zip.Native.HuffTree.fromLengths] at htree
  split at htree
  · simp at htree
  · split at htree
    · simp at htree
    · exact (Except.ok.inj htree).symm

/-- The count of elements equal to `b` in a prefix is at most the count in the full list. -/
theorem count_foldl_take_le (ls : List Nat) (b : Nat) (k : Nat) :
    (ls.take k).foldl (fun acc l => if (l == b) = true then acc + 1 else acc) 0 ≤
    ls.foldl (fun acc l => if (l == b) = true then acc + 1 else acc) 0 := by
  rw [show ls.foldl (fun acc l => if (l == b) = true then acc + 1 else acc) 0 =
    (ls.drop k).foldl (fun acc l => if (l == b) = true then acc + 1 else acc)
      ((ls.take k).foldl (fun acc l => if (l == b) = true then acc + 1 else acc) 0)
    from by rw [← List.foldl_append, List.take_append_drop]]
  exact Huffman.Spec.count_foldl_mono _ _ _

/-- `codeFor` returns `some` for symbols with valid nonzero length. -/
theorem codeFor_some (lsList : List Nat) (maxBits : Nat) (s : Nat)
    (hs : s < lsList.length) (hlen : lsList[s] ≠ 0) (hle : lsList[s] ≤ maxBits) :
    ∃ cw, Huffman.Spec.codeFor lsList maxBits s = some cw := by
  simp only [Huffman.Spec.codeFor, show s < lsList.length from hs, ↓reduceDIte]
  simp only [show (lsList[s] == 0 || decide (lsList[s] > maxBits)) = false from by
    simp [hlen]; omega]
  exact ⟨_, rfl⟩

/-- NC invariant update: after incrementing `nextCode[len]`, the NC invariant
    holds at `start + 1`. Shared by `insertLoop_forward` and `insertLoop_backward`. -/
private theorem nc_invariant_step
    (lengths : Array UInt8) (nextCode : Array UInt32) (start : Nat)
    (lsList : List Nat) (maxBits : Nat)
    (blCount : Array Nat) (hblCount : blCount = Huffman.Spec.countLengths lsList maxBits)
    (ncSpec : Array Nat) (hncSpec : ncSpec = Huffman.Spec.nextCodes blCount maxBits)
    (hv : Huffman.Spec.ValidLengths lsList maxBits) (hmb : maxBits < 32)
    (hncSize : nextCode.size ≥ maxBits + 1)
    (hstart : start < lengths.size)
    (hls_len : start < lsList.length)
    (hls_start : lsList[start] = lengths[start].toNat)
    (hlen_le : lengths[start].toNat ≤ maxBits)
    (hlen_pos_nat : 0 < lengths[start].toNat)
    (hnc : ∀ b, 1 ≤ b → b ≤ maxBits →
      nextCode[b]!.toNat = ncSpec[b]! +
        (lsList.take start).foldl (fun acc l => if l == b then acc + 1 else acc) 0)
    (b : Nat) (hb1 : 1 ≤ b) (hb15 : b ≤ maxBits) :
    (nextCode.set! lengths[start].toNat (nextCode[lengths[start].toNat]! + 1))[b]!.toNat =
      ncSpec[b]! +
        (lsList.take (start + 1)).foldl (fun acc l => if l == b then acc + 1 else acc) 0 := by
  rw [List.take_add_one]
  simp only [List.getElem?_eq_getElem hls_len, Option.toList,
             List.foldl_append, List.foldl_cons, List.foldl_nil, hls_start]
  by_cases hbeq : lengths[start].toNat = b
  · subst hbeq
    simp only [if_pos (beq_self_eq_true lengths[start].toNat)]
    rw [Array.getElem!_set!_self _ _ _ (by omega : lengths[start].toNat < nextCode.size)]
    have h_nc_val := hnc lengths[start].toNat (by omega) hlen_le
    have h_partial_le := count_foldl_take_le lsList lengths[start].toNat start
    have h_npc := Huffman.Spec.nextCodes_plus_count_le lsList maxBits
      lengths[start].toNat hv (by omega) hlen_le
    rw [← hblCount, ← hncSpec] at h_npc
    have h_pow := Nat.pow_le_pow_right (by omega : 0 < 2) (show lengths[start].toNat ≤ 31 from by omega)
    rw [UInt32.toNat_add, show (1 : UInt32).toNat = 1 from rfl,
        Nat.mod_eq_of_lt (by omega), h_nc_val]
    omega
  · have hf : ¬((lengths[start].toNat == b) = true) := by rw [beq_iff_eq]; exact hbeq
    simp only [if_neg hf]
    rw [Array.getElem!_set!_ne _ _ _ _ hbeq]
    exact hnc b hb1 hb15

/-- The tree produced by `insertLoop` has a leaf for every symbol with nonzero length,
    at the codeword given by `codeFor`. Proved by well-founded induction on `lengths.size - start`,
    maintaining the NC invariant, forward invariant, and NoLeafOnPath invariant. -/
private theorem insertLoop_forward
    (lengths : Array UInt8) (nextCode : Array UInt32)
    (start : Nat) (tree : Zip.Native.HuffTree)
    (lsList : List Nat) (hlsList : lsList = lengths.toList.map UInt8.toNat)
    (maxBits : Nat) (hmb : maxBits < 32)
    (blCount : Array Nat) (hblCount : blCount = Huffman.Spec.countLengths lsList maxBits)
    (ncSpec : Array Nat) (hncSpec : ncSpec = Huffman.Spec.nextCodes blCount maxBits)
    (hv : Huffman.Spec.ValidLengths lsList maxBits)
    (hncSize : nextCode.size ≥ maxBits + 1)
    -- NC invariant: nextCode tracks ncSpec + partial offset
    (hnc : ∀ b, 1 ≤ b → b ≤ maxBits →
      nextCode[b]!.toNat = ncSpec[b]! +
        (lsList.take start).foldl (fun acc l => if l == b then acc + 1 else acc) 0)
    -- Forward: tree has leaves for all k < start
    (hprev : ∀ k, k < start → (hk : k < lengths.size) → lengths[k] > 0 →
      ∀ cw, Huffman.Spec.codeFor lsList maxBits k = some cw →
        TreeHasLeaf tree cw k.toUInt16)
    -- NoLeafOnPath for all future codes
    (hnlop : ∀ k, start ≤ k → (hk : k < lengths.size) → lengths[k] > 0 →
      ∀ cw, Huffman.Spec.codeFor lsList maxBits k = some cw →
        NoLeafOnPath tree cw)
    -- Target symbol
    (j : Nat) (hjs : j < lengths.size) (hjlen : lengths[j] > 0)
    (cw : Huffman.Spec.Codeword) (hcf : Huffman.Spec.codeFor lsList maxBits j = some cw) :
    TreeHasLeaf (Zip.Native.HuffTree.insertLoop lengths nextCode start tree).1 cw j.toUInt16 := by
  unfold Zip.Native.HuffTree.insertLoop
  split
  · -- start < lengths.size
    rename_i hstart
    dsimp only []
    split
    · -- lengths[start] > 0: insert + recurse
      rename_i hlen_pos
      -- Common facts for insert case
      have hls_len : start < lsList.length := by simp [hlsList, hstart]
      have hls_start : lsList[start] = lengths[start].toNat := by
        simp only [hlsList, List.getElem_map, Array.getElem_toList]
      have hlen_le : lengths[start].toNat ≤ maxBits := by
        rw [← hls_start]; exact hv.1 _ (List.getElem_mem hls_len)
      have hlen_pos_nat : 0 < lengths[start].toNat := hlen_pos
      -- The codeword for symbol `start` matches the insert path
      obtain ⟨cw_s, hcf_s⟩ := codeFor_some lsList maxBits start hls_len
        (by rw [hls_start]; omega) (by rw [hls_start]; omega)
      have hcw_s : cw_s = Huffman.Spec.natToBits
          (nextCode[lengths[start].toNat]!).toNat lengths[start].toNat := by
        obtain ⟨_, _, hcw⟩ := Huffman.Spec.codeFor_spec hcf_s
        rw [hcw, hls_start]; congr 1
        rw [← hblCount, ← hncSpec]
        exact (hnc lengths[start].toNat (by omega) hlen_le).symm
      -- Prefix-freeness: insert path is not prefix of any other codeword
      have hpf : ∀ k, k ≠ start → ∀ cw', Huffman.Spec.codeFor lsList maxBits k = some cw' →
          ¬(Huffman.Spec.natToBits (nextCode[lengths[start].toNat]!).toNat
            lengths[start].toNat).IsPrefix cw' := by
        intro k hne cw' hcf_k
        have hcf_s' := hcw_s ▸ hcf_s
        exact Huffman.Spec.canonical_prefix_free lsList maxBits hv start k _ cw'
          hcf_s' hcf_k (by omega)
      exact insertLoop_forward lengths
        (nextCode.set! lengths[start].toNat (nextCode[lengths[start].toNat]! + 1))
        (start + 1)
        (tree.insert (nextCode[lengths[start].toNat]!) lengths[start].toNat start.toUInt16)
        lsList hlsList maxBits hmb blCount hblCount ncSpec hncSpec hv
        (by -- hncSize': set! preserves array size
          simp [Array.set!_eq_setIfInBounds, Array.setIfInBounds]
          split <;> simp_all)
        (nc_invariant_step lengths nextCode start lsList maxBits blCount hblCount
          ncSpec hncSpec hv hmb hncSize hstart hls_len hls_start hlen_le hlen_pos_nat hnc)
        (by -- hprev': forward invariant after insertion
          intro k hk hks hklen cw' hcf'
          by_cases hk_eq : k = start
          · -- k = start: newly inserted leaf
            have hcf_start : Huffman.Spec.codeFor lsList maxBits start = some cw' := by
              rw [← hk_eq]; exact hcf'
            have hcw_eq : cw_s = cw' := Option.some.inj (hcf_s.symm.trans hcf_start)
            subst hcw_eq; rw [hcw_s, hk_eq]
            have h_nlop : NoLeafOnPath tree cw_s :=
              hnlop start Nat.le.refl hstart hlen_pos cw_s hcf_s
            rw [hcw_s] at h_nlop
            exact insert_go_hasLeaf _ _ _ _ (by omega) h_nlop
          · -- k < start: leaf preserved by insert
            exact insert_go_preserves _ _ _ _ (by omega) cw' k.toUInt16
              (hprev k (by omega) hks hklen cw' hcf')
              (hpf k hk_eq cw' hcf'))
        (by -- hnlop': NoLeafOnPath preserved after insert
          intro k hk hks hklen cw' hcf'
          exact insert_go_noLeafOnPath _ _ _ _ (by omega) cw'
            (hnlop k (by omega) hks hklen cw' hcf')
            (hpf k (by omega) cw' hcf'))
        j hjs hjlen cw hcf
    · -- ¬(lengths[start] > 0): skip, recurse with same tree/nextCode
      rename_i hlen_zero
      have hls_len : start < lsList.length := by simp [hlsList, hstart]
      have hls_val : lsList[start] = 0 := by
        have : ¬(0 < lengths[start].toNat) := fun hp => hlen_zero hp
        simp [hlsList]; omega
      exact insertLoop_forward lengths nextCode (start + 1) tree
        lsList hlsList maxBits hmb blCount hblCount ncSpec hncSpec hv hncSize
        (by -- NC: lsList[start] = 0 doesn't change count for any b ≥ 1
          intro b hb1 hb15
          rw [hnc b hb1 hb15]; congr 1
          rw [List.take_add_one]
          simp [List.getElem?_eq_getElem hls_len, hls_val, List.foldl_append]
          omega)
        (by intro k hk hks hklen cw' hcf'
            have : k < start := by
              by_cases h : k = start
              · subst h; exact absurd hklen hlen_zero
              · omega
            exact hprev k this hks hklen cw' hcf')
        (by intro k hk hks hklen cw' hcf'; exact hnlop k (by omega) hks hklen cw' hcf')
        j hjs hjlen cw hcf
  · exact hprev j (by omega) hjs hjlen cw hcf
termination_by lengths.size - start

/-- Backward direction of `insertLoop_forward`: every leaf in the tree
    after `insertLoop` was either pre-existing or corresponds to a symbol
    with nonzero code length that was inserted during the loop. -/
private theorem insertLoop_backward
    (lengths : Array UInt8) (nextCode : Array UInt32)
    (start : Nat) (tree : Zip.Native.HuffTree)
    (lsList : List Nat) (hlsList : lsList = lengths.toList.map UInt8.toNat)
    (maxBits : Nat) (hmb : maxBits < 32)
    (blCount : Array Nat) (hblCount : blCount = Huffman.Spec.countLengths lsList maxBits)
    (ncSpec : Array Nat) (hncSpec : ncSpec = Huffman.Spec.nextCodes blCount maxBits)
    (hv : Huffman.Spec.ValidLengths lsList maxBits)
    (hncSize : nextCode.size ≥ maxBits + 1)
    (hnc : ∀ b, 1 ≤ b → b ≤ maxBits →
      nextCode[b]!.toNat = ncSpec[b]! +
        (lsList.take start).foldl (fun acc l => if l == b then acc + 1 else acc) 0)
    (cw : List Bool) (sym : UInt16)
    (h : TreeHasLeaf (Zip.Native.HuffTree.insertLoop lengths nextCode start tree).1 cw sym) :
    TreeHasLeaf tree cw sym ∨
    ∃ k, start ≤ k ∧ k < lsList.length ∧
      sym = k.toUInt16 ∧ Huffman.Spec.codeFor lsList maxBits k = some cw := by
  unfold Zip.Native.HuffTree.insertLoop at h
  split at h
  · -- start < lengths.size
    rename_i hstart
    dsimp only [] at h
    split at h
    · -- lengths[start] > 0: insert case
      rename_i hlen_pos
      have hls_len : start < lsList.length := by simp [hlsList, hstart]
      have hls_start : lsList[start] = lengths[start].toNat := by
        simp only [hlsList, List.getElem_map, Array.getElem_toList]
      have hlen_le : lengths[start].toNat ≤ maxBits := by
        rw [← hls_start]; exact hv.1 _ (List.getElem_mem hls_len)
      have hlen_pos_nat : 0 < lengths[start].toNat := hlen_pos
      -- The codeword for symbol `start`
      obtain ⟨cw_s, hcf_s⟩ := codeFor_some lsList maxBits start hls_len
        (by rw [hls_start]; omega) (by rw [hls_start]; omega)
      have hcw_s : cw_s = Huffman.Spec.natToBits
          (nextCode[lengths[start].toNat]!).toNat lengths[start].toNat := by
        obtain ⟨_, _, hcw⟩ := Huffman.Spec.codeFor_spec hcf_s
        rw [hcw, hls_start]; congr 1
        rw [← hblCount, ← hncSpec]
        exact (hnc lengths[start].toNat (by omega) hlen_le).symm
      -- Apply IH to the recursive call
      have ih := insertLoop_backward lengths
        (nextCode.set! lengths[start].toNat (nextCode[lengths[start].toNat]! + 1))
        (start + 1)
        (tree.insert (nextCode[lengths[start].toNat]!) lengths[start].toNat start.toUInt16)
        lsList hlsList maxBits hmb blCount hblCount ncSpec hncSpec hv
        (by simp [Array.set!_eq_setIfInBounds, Array.setIfInBounds]; split <;> simp_all)
        (nc_invariant_step lengths nextCode start lsList maxBits blCount hblCount
          ncSpec hncSpec hv hmb hncSize hstart hls_len hls_start hlen_le hlen_pos_nat hnc)
        cw sym h
      cases ih with
      | inl h_in_insert =>
        -- Leaf was in tree.insert: apply insert_go_complete'
        have ih2 := insert_go_complete' _ _ tree _ (by omega) cw sym h_in_insert
        cases ih2 with
        | inl h_in_tree => exact .inl h_in_tree
        | inr h_eq =>
          obtain ⟨hcw_eq, hsym_eq⟩ := h_eq
          exact .inr ⟨start, Nat.le.refl, hls_len, hsym_eq,
            by rw [hcw_eq, ← hcw_s]; exact hcf_s⟩
      | inr h_exists =>
        obtain ⟨k, hk_ge, hk_lt, hk_sym, hk_cf⟩ := h_exists
        exact .inr ⟨k, by omega, hk_lt, hk_sym, hk_cf⟩
    · -- lengths[start] = 0: skip case
      rename_i hlen_zero
      have hls_len : start < lsList.length := by simp [hlsList, hstart]
      have hls_val : lsList[start] = 0 := by
        have : ¬(0 < lengths[start].toNat) := fun hp => hlen_zero hp
        simp [hlsList]; omega
      have ih := insertLoop_backward lengths nextCode (start + 1) tree
        lsList hlsList maxBits hmb blCount hblCount ncSpec hncSpec hv hncSize
        (by intro b hb1 hb15; rw [hnc b hb1 hb15]; congr 1
            rw [List.take_add_one]
            simp [List.getElem?_eq_getElem hls_len, hls_val, List.foldl_append]; omega)
        cw sym h
      cases ih with
      | inl h_pre => exact .inl h_pre
      | inr h_exists =>
        obtain ⟨k, hk_ge, hk_lt, hk_sym, hk_cf⟩ := h_exists
        exact .inr ⟨k, by omega, hk_lt, hk_sym, hk_cf⟩
  · -- start ≥ lengths.size: base case (insertLoop returns tree unchanged)
    exact .inl h
termination_by lengths.size - start

/-- If `decode table bits = some (sym, rest)`, then there exists a matching
    codeword entry in the table with `bits = cw ++ rest`. -/
protected theorem decode_some_mem {α : Type} (table : List (Huffman.Spec.Codeword × α))
    (bits : List Bool) (sym : α) (rest : List Bool)
    (h : Huffman.Spec.decode table bits = some (sym, rest)) :
    ∃ cw, (cw, sym) ∈ table ∧ bits = cw ++ rest := by
  induction table with
  | nil => simp [Huffman.Spec.decode] at h
  | cons entry entries ih =>
    obtain ⟨cw', sym'⟩ := entry
    simp only [Huffman.Spec.decode] at h
    split at h
    · -- isPrefixOf true: match found
      rename_i hpre
      obtain ⟨rfl, rfl⟩ := Option.some.inj h
      rw [Huffman.Spec.isPrefixOf_iff] at hpre
      obtain ⟨t, rfl⟩ := hpre
      exact ⟨cw', List.mem_cons_self .., by simp⟩
    · -- isPrefixOf false: recurse
      obtain ⟨cw, hmem, hbits⟩ := ih h
      exact ⟨cw, List.mem_cons_of_mem _ hmem, hbits⟩

/-- The initial `nextCode` array (`ncSpec.map (·.toUInt32)`) satisfies the NC
    invariant at `start = 0`: each entry's `toNat` equals the spec value.
    Shared by `fromLengths_hasLeaf` and `fromLengths_leaf_spec`. -/
private theorem initial_nc_invariant (lengths : Array UInt8)
    (maxBits : Nat) (hmb : maxBits < 32)
    (hv : Huffman.Spec.ValidLengths (lengths.toList.map UInt8.toNat) maxBits)
    (b : Nat) (hb1 : 1 ≤ b) (hb15 : b ≤ maxBits) :
    ((Huffman.Spec.nextCodes (Huffman.Spec.countLengths
        (lengths.toList.map UInt8.toNat) maxBits) maxBits).map
      Nat.toUInt32)[b]!.toNat =
    (Huffman.Spec.nextCodes (Huffman.Spec.countLengths
        (lengths.toList.map UInt8.toNat) maxBits) maxBits)[b]! := by
  have hbs : b < (Huffman.Spec.nextCodes (Huffman.Spec.countLengths
      (List.map UInt8.toNat lengths.toList) maxBits) maxBits).size := by
    rw [Huffman.Spec.nextCodes_size]; omega
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
             Array.getElem?_map, Array.getElem?_eq_getElem hbs,
             Option.map_some, Option.getD_some]
  have h_npc := Huffman.Spec.nextCodes_plus_count_le
    (List.map UInt8.toNat lengths.toList) maxBits b hv (by omega) hb15
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
             Array.getElem?_eq_getElem hbs, Option.getD_some] at h_npc
  have h_pow := Nat.pow_le_pow_right (by omega : 0 < 2) (show b ≤ 31 from by omega)
  show (Huffman.Spec.nextCodes _ maxBits)[b].toUInt32.toNat =
       (Huffman.Spec.nextCodes _ maxBits)[b]
  rw [show ∀ n : Nat, n.toUInt32.toNat = n % 2 ^ 32 from fun _ => rfl,
      Nat.mod_eq_of_lt (by omega)]

/-- The tree built by `fromLengths` has a leaf for every canonical codeword.
    Requires `ValidLengths` to ensure no collisions during insertion. -/
protected theorem fromLengths_hasLeaf (lengths : Array UInt8)
    (maxBits : Nat) (hmb : maxBits < 32)
    (tree : Zip.Native.HuffTree)
    (htree : Zip.Native.HuffTree.fromLengths lengths maxBits = .ok tree)
    (hv : Huffman.Spec.ValidLengths (lengths.toList.map UInt8.toNat) maxBits)
    (s : Nat) (cw : Huffman.Spec.Codeword)
    (hmem : (s, cw) ∈ Huffman.Spec.allCodes (lengths.toList.map UInt8.toNat) maxBits) :
    TreeHasLeaf tree cw s.toUInt16 := by
  -- Extract facts from allCodes membership
  rw [Huffman.Spec.allCodes_mem_iff] at hmem
  obtain ⟨hs_len, hcf⟩ := hmem
  -- Get lengths[s] > 0 from codeFor returning some
  obtain ⟨_, hlen_cond, _⟩ := Huffman.Spec.codeFor_spec hcf
  have ⟨hlen_ne, _⟩ := Huffman.Spec.codeFor_len_bounds hlen_cond
  have hs : s < lengths.size := by simp at hs_len; omega
  have hjlen : lengths[s] > 0 := by
    have : (lengths.toList.map UInt8.toNat)[s] ≠ 0 := hlen_ne
    simp [List.getElem_map, Array.getElem_toList] at this
    exact Nat.pos_of_ne_zero this
  -- Rewrite tree to fromLengthsTree = (insertLoop ...).1
  rw [fromLengths_ok_eq lengths maxBits tree htree]
  -- fromLengthsTree unfolds to insertLoop with spec-derived nextCode
  show TreeHasLeaf (Zip.Native.HuffTree.fromLengthsTree lengths maxBits) cw s.toUInt16
  unfold Zip.Native.HuffTree.fromLengthsTree
  dsimp only []
  -- Apply insertLoop_forward with start = 0
  exact insertLoop_forward lengths _ 0 .empty _ rfl maxBits hmb _ rfl _ rfl hv
    (by simp [Array.size_map, Huffman.Spec.nextCodes_size])
    (by intro b hb1 hb15
        simp only [List.take_zero, List.foldl_nil, Nat.add_zero]
        exact initial_nc_invariant lengths maxBits hmb hv b hb1 hb15)
    (by intro k hk; omega)
    (by intro k _ _ _ cw' _; cases cw' <;> trivial)
    s hs hjlen cw hcf

/-- Every leaf in the tree built by `fromLengths` corresponds to an entry
    in `allCodes`. -/
protected theorem fromLengths_leaf_spec (lengths : Array UInt8)
    (maxBits : Nat) (hmb : maxBits < 32)
    (tree : Zip.Native.HuffTree)
    (htree : Zip.Native.HuffTree.fromLengths lengths maxBits = .ok tree)
    (hv : Huffman.Spec.ValidLengths (lengths.toList.map UInt8.toNat) maxBits)
    (hlen_bound : lengths.size ≤ UInt16.size)
    (cw : List Bool) (sym : UInt16)
    (h : TreeHasLeaf tree cw sym) :
    (sym.toNat, cw) ∈ Huffman.Spec.allCodes (lengths.toList.map UInt8.toNat) maxBits := by
  rw [fromLengths_ok_eq lengths maxBits tree htree] at h
  unfold Zip.Native.HuffTree.fromLengthsTree at h
  dsimp only [] at h
  have ih := insertLoop_backward lengths _ 0 .empty _ rfl maxBits hmb _ rfl _ rfl hv
    (by simp [Array.size_map, Huffman.Spec.nextCodes_size])
    (by intro b hb1 hb15
        simp only [List.take_zero, List.foldl_nil, Nat.add_zero]
        exact initial_nc_invariant lengths maxBits hmb hv b hb1 hb15)
    cw sym h
  cases ih with
  | inl h_empty => cases h_empty
  | inr h_exists =>
    obtain ⟨k, _, hk_len, rfl, hcf⟩ := h_exists
    have hk_small : k < UInt16.size := by simp at hk_len; omega
    have hk_toNat : k.toUInt16.toNat = k :=
      Nat.mod_eq_of_lt hk_small
    rw [Huffman.Spec.allCodes_mem_iff]
    exact ⟨by rw [hk_toNat]; exact hk_len, by rw [hk_toNat]; exact hcf⟩

end Deflate.Correctness
