import Zip.Spec.HuffmanCorrectLoop
import Zip.Native.Deflate

/-!
# Canonical Codes Encode Correctness

Proves that `canonicalCodes` (used by the native DEFLATE compressor) assigns
the same code values as `codeFor` (the spec's per-symbol code computation).
This bridges native encoding to spec decoding: the codes written by the
compressor correspond to leaves in the Huffman tree built by the decompressor.
-/

namespace Deflate.Correctness

/-! ### Size preservation -/

/-- `canonicalCodes.go` preserves the result array size. -/
protected theorem canonicalCodes_go_size (lengths : Array UInt8) (nextCode : Array UInt32)
    (i : Nat) (result : Array (UInt16 × UInt8)) :
    (Zip.Native.Deflate.canonicalCodes.go lengths nextCode i result).size = result.size := by
  unfold Zip.Native.Deflate.canonicalCodes.go
  split
  · dsimp only []
    split
    · rw [Deflate.Correctness.canonicalCodes_go_size]
      simp [Array.set!_eq_setIfInBounds, Array.setIfInBounds]; split <;> simp_all
    · exact Deflate.Correctness.canonicalCodes_go_size lengths nextCode (i + 1) result
  · rfl
termination_by lengths.size - i

/-! ### Main loop invariant -/

/-- Loop invariant for `canonicalCodes.go`. Given that:
    - The `nextCode` array tracks `ncSpec + partial offset` (NC invariant)
    - Entries at positions `< i` are already correct
    - Entries at positions `≥ i` are still `(0, 0)` (initial value)
    The final result has correct entries for all positions. -/
private theorem canonicalCodes_go_inv
    (lengths : Array UInt8) (nextCode : Array UInt32) (i : Nat)
    (result : Array (UInt16 × UInt8))
    (lsList : List Nat) (hlsList : lsList = lengths.toList.map UInt8.toNat)
    (maxBits : Nat) (hmb : maxBits < 16)
    (blCount : Array Nat) (hblCount : blCount = Huffman.Spec.countLengths lsList maxBits)
    (ncSpec : Array Nat) (hncSpec : ncSpec = Huffman.Spec.nextCodes blCount maxBits)
    (hv : Huffman.Spec.ValidLengths lsList maxBits)
    (hresSize : result.size = lengths.size)
    (hncSize : nextCode.size ≥ maxBits + 1)
    -- NC invariant
    (hnc : ∀ b, 1 ≤ b → b ≤ maxBits →
      nextCode[b]!.toNat = ncSpec[b]! +
        (lsList.take i).foldl (fun acc l => if (l == b) = true then acc + 1 else acc) 0)
    -- Result entries at positions < i are correct
    (hprev : ∀ j, j < i → (hjs : j < lengths.size) →
      if lengths[j] > 0 then
        result[j]!.2 = lengths[j] ∧
        result[j]!.1.toNat = ncSpec[lengths[j].toNat]! +
          (lsList.take j).foldl (fun acc l => if (l == lengths[j].toNat) = true then acc + 1 else acc) 0
      else result[j]! = (0, 0))
    -- Entries at positions ≥ i are (0, 0)
    (hfut : ∀ j, i ≤ j → j < lengths.size → result[j]! = (0, 0))
    -- Target
    (j : Nat) (hjs : j < lengths.size) :
    let final := Zip.Native.Deflate.canonicalCodes.go lengths nextCode i result
    if lengths[j] > 0 then
      final[j]!.2 = lengths[j] ∧
      final[j]!.1.toNat = ncSpec[lengths[j].toNat]! +
        (lsList.take j).foldl (fun acc l => if (l == lengths[j].toNat) = true then acc + 1 else acc) 0
    else final[j]! = (0, 0) := by
  unfold Zip.Native.Deflate.canonicalCodes.go
  split
  · -- i < lengths.size
    rename_i hi
    dsimp only []
    by_cases hlen_pos : lengths[i] > 0
    · -- lengths[i] > 0: insert case
      simp only [hlen_pos, ↓reduceIte]
      -- Bridge UInt8 comparison to Nat
      have hlen_pos_nat : 0 < lengths[i].toNat := hlen_pos
      -- Common setup
      have hls_len : i < lsList.length := by simp [hlsList, hi]
      have hls_i : lsList[i] = lengths[i].toNat := by
        simp only [hlsList, List.getElem_map, Array.getElem_toList]
      have hlen_le : lengths[i].toNat ≤ maxBits := by
        rw [← hls_i]; exact hv.1 _ (List.getElem_mem hls_len)
      -- Code value from NC invariant
      have hcode_val := hnc lengths[i].toNat (by omega) hlen_le
      have h_partial_le := count_foldl_take_le lsList lengths[i].toNat i
      -- Full bound: nc + total_count ≤ 2^len
      have h_npc := Huffman.Spec.nextCodes_plus_count_le lsList maxBits
        lengths[i].toNat hv (by omega) hlen_le
      rw [← hblCount, ← hncSpec] at h_npc
      have h_pow := Nat.pow_le_pow_right (by omega : 0 < 2)
        (show lengths[i].toNat ≤ 31 from by omega)
      -- Apply recursive case
      exact canonicalCodes_go_inv lengths
        (nextCode.set! lengths[i].toNat (nextCode[lengths[i].toNat]! + 1))
        (i + 1)
        (result.set! i ((nextCode[lengths[i].toNat]!).toUInt16, lengths[i]))
        lsList hlsList maxBits hmb blCount hblCount ncSpec hncSpec hv
        (by -- hresSize: set! preserves array size
          simp [Array.set!_eq_setIfInBounds, Array.setIfInBounds, hresSize]
          split <;> simp_all)
        (by -- hncSize: set! preserves array size
          simp only [Array.set!_eq_setIfInBounds, Array.setIfInBounds]
          split
          · simp_all
          · exact hncSize)
        (by -- hnc': NC invariant after increment
          intro b hb1 hb15
          rw [List.take_add_one]
          simp only [List.getElem?_eq_getElem hls_len, Option.toList,
                     List.foldl_append, List.foldl_cons, List.foldl_nil, hls_i]
          by_cases hbeq : lengths[i].toNat = b
          · -- b = len: both sides incremented
            subst hbeq
            simp only [beq_self_eq_true, ↓reduceIte]
            rw [Array.getElem!_set!_self _ _ _ (show lengths[i].toNat < nextCode.size from by omega)]
            rw [UInt32.toNat_add, show (1 : UInt32).toNat = 1 from rfl,
                Nat.mod_eq_of_lt (by omega), hcode_val]
            omega
          · -- b ≠ len: unchanged
            have hf : ¬((lengths[i].toNat == b) = true) := by
              rw [beq_iff_eq]; exact hbeq
            simp only [if_neg hf]
            rw [Array.getElem!_set!_ne _ _ _ _ hbeq]
            exact hnc b hb1 hb15)
        (by -- hprev': entries < i+1 are correct
          intro k hk hks
          by_cases hk_eq : k = i
          · -- k = i: newly set entry
            simp only [hk_eq]
            rw [Array.getElem!_set!_self result i _ (show i < result.size from by omega)]
            simp only [hlen_pos, ↓reduceIte]
            refine ⟨trivial, ?_⟩
            -- UInt32 → UInt16 → Nat faithfulness
            change (nextCode[lengths[i].toNat]!).toUInt16.toNat = _
            rw [show ∀ (x : UInt32), x.toUInt16.toNat = x.toNat % 65536 from fun _ => rfl,
                hcode_val, Nat.mod_eq_of_lt]
            -- ncSpec + partial count < 65536
            have : 2 ^ lengths[i].toNat ≤ 32768 :=
              Nat.pow_le_pow_right (by omega) (show lengths[i].toNat ≤ 15 from by omega)
            omega
          · -- k < i: preserved by set! at different index
            rw [Array.getElem!_set!_ne result i k _ (Ne.symm hk_eq)]
            exact hprev k (by omega) hks)
        (by -- hfut': entries at ≥ i+1 are still (0,0)
          intro k hk hks
          rw [Array.getElem!_set!_ne result i k _ (by omega)]
          exact hfut k (by omega) hks)
        j hjs
    · -- lengths[i] = 0: skip case
      simp only [hlen_pos, ↓reduceIte]
      have hlen_zero : lengths[i].toNat = 0 := Nat.eq_zero_of_not_pos hlen_pos
      have hls_len : i < lsList.length := by simp [hlsList, hi]
      have hls_val : lsList[i] = 0 := by
        simp only [hlsList, List.getElem_map, Array.getElem_toList, hlen_zero]
      exact canonicalCodes_go_inv lengths nextCode (i + 1) result
        lsList hlsList maxBits hmb blCount hblCount ncSpec hncSpec hv hresSize hncSize
        (by -- NC: lsList[i] = 0 doesn't change count for any b ≥ 1
          intro b hb1 hb15
          rw [hnc b hb1 hb15]; congr 1
          rw [List.take_add_one]
          simp only [List.getElem?_eq_getElem hls_len, Option.toList,
                     List.foldl_append, List.foldl_cons, List.foldl_nil, hls_val]
          have : ¬((0 == b) = true) := by rw [beq_iff_eq]; omega
          simp [this])
        (by -- hprev: extend to cover i (which has length 0)
          intro k hk hks
          by_cases hk_eq : k = i
          · simp only [hk_eq]
            have hfut_i := hfut i Nat.le.refl hi
            simp [hlen_pos, hfut_i]
          · exact hprev k (by omega) hks)
        (by -- hfut: positions ≥ i+1 still (0,0)
          intro k hk hks
          exact hfut k (by omega) hks)
        j hjs
  · -- i ≥ lengths.size: base case
    exact hprev j (by omega) hjs
termination_by lengths.size - i

/-! ### Initial NC invariant -/

/-- Prove the initial NC invariant for `nextCode = ncSpec.map (·.toUInt32)`. -/
private theorem initial_nc_invariant
    (lsList : List Nat) (maxBits : Nat) (hmb : maxBits < 32)
    (hv : Huffman.Spec.ValidLengths lsList maxBits)
    (ncSpec : Array Nat) (hncSpec : ncSpec = Huffman.Spec.nextCodes
      (Huffman.Spec.countLengths lsList maxBits) maxBits)
    (b : Nat) (hb1 : 1 ≤ b) (hb15 : b ≤ maxBits) :
    (ncSpec.map (fun (n : Nat) => n.toUInt32))[b]!.toNat = ncSpec[b]! := by
  have hbs : b < ncSpec.size := by
    rw [hncSpec, Huffman.Spec.nextCodes_size]; omega
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
  rw [Array.getElem?_map, Array.getElem?_eq_getElem hbs]
  simp only [Option.map_some, Option.getD_some]
  have h_npc := Huffman.Spec.nextCodes_plus_count_le lsList maxBits b hv (by omega) hb15
  rw [← hncSpec] at h_npc
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
             Array.getElem?_eq_getElem hbs, Option.getD_some] at h_npc
  have h_pow := Nat.pow_le_pow_right (by omega : 0 < 2) (show b ≤ 31 from by omega)
  show ncSpec[b].toUInt32.toNat = ncSpec[b]
  rw [show ∀ n : Nat, n.toUInt32.toNat = n % 2 ^ 32 from fun _ => rfl,
      Nat.mod_eq_of_lt (by omega)]

/-! ### Invariant instantiation at initial state -/

/-- Apply `canonicalCodes_go_inv` with the standard initial arguments (start index 0,
    initial `nextCode = ncSpec.map (·.toUInt32)`, result filled with `(0, 0)`). -/
private theorem canonicalCodes_inv_at (lengths : Array UInt8) (maxBits : Nat)
    (hv : Huffman.Spec.ValidLengths (lengths.toList.map UInt8.toNat) maxBits)
    (hmb : maxBits < 16) (i : Nat) (hi : i < lengths.size) :
    let lsList := lengths.toList.map UInt8.toNat
    let ncSpec := Huffman.Spec.nextCodes (Huffman.Spec.countLengths lsList maxBits) maxBits
    let final := Zip.Native.Deflate.canonicalCodes.go lengths
      (ncSpec.map fun n => n.toUInt32) 0 (Array.replicate lengths.size (0, 0))
    if lengths[i] > 0 then
      final[i]!.2 = lengths[i] ∧
      final[i]!.1.toNat = ncSpec[lengths[i].toNat]! +
        (lsList.take i).foldl (fun acc l => if (l == lengths[i].toNat) = true then acc + 1 else acc) 0
    else final[i]! = (0, 0) := by
  intro lsList ncSpec
  exact canonicalCodes_go_inv lengths
    (ncSpec.map fun n => n.toUInt32) 0 (Array.replicate lengths.size (0, 0))
    lsList rfl maxBits hmb _ rfl ncSpec rfl hv
    (Array.size_replicate ..)
    (by have : (ncSpec.map fun n => n.toUInt32).size = ncSpec.size := Array.size_map ..
        rw [this, show ncSpec = Huffman.Spec.nextCodes _ _ from rfl,
            Huffman.Spec.nextCodes_size]; omega)
    (by intro b hb1 hb15
        simp only [List.take_zero, List.foldl_nil, Nat.add_zero]
        exact initial_nc_invariant lsList maxBits (by omega) hv ncSpec rfl b hb1 hb15)
    (by intro k hk; omega)
    (by intro k _ hks; simp [show k < lengths.size from hks])
    i hi

/-! ### Top-level correspondence theorems -/

/-- For symbols with non-zero code length, `canonicalCodes` produces the same
    code value as spec's `codeFor`. The UInt16 stored by `canonicalCodes` equals
    the numeric code value, and `natToBits` of this value gives the spec codeword.
    Requires `maxBits < 16` for UInt16 faithfulness. -/
protected theorem canonicalCodes_correct_pos (lengths : Array UInt8) (maxBits : Nat)
    (hv : Huffman.Spec.ValidLengths (lengths.toList.map UInt8.toNat) maxBits)
    (hmb : maxBits < 16)
    (i : Nat) (hi : i < lengths.size) (hlen : lengths[i] > 0) :
    ∃ cw, Huffman.Spec.codeFor (lengths.toList.map UInt8.toNat) maxBits i = some cw ∧
      cw = Huffman.Spec.natToBits
        (Zip.Native.Deflate.canonicalCodes lengths maxBits)[i]!.1.toNat
        lengths[i].toNat ∧
      (Zip.Native.Deflate.canonicalCodes lengths maxBits)[i]!.2 = lengths[i] := by
  let lsList := lengths.toList.map UInt8.toNat
  have hlen_pos_nat : 0 < lengths[i].toNat := hlen
  have hls_len : i < lsList.length := by simp [lsList, hi]
  have hls_i : lsList[i] = lengths[i].toNat := by
    simp only [lsList, List.getElem_map, Array.getElem_toList]
  have hlen_le : lengths[i].toNat ≤ maxBits := by
    rw [← hls_i]; exact hv.1 _ (List.getElem_mem hls_len)
  obtain ⟨cw, hcf⟩ := codeFor_some lsList maxBits i hls_len (by rw [hls_i]; omega) (by rw [hls_i]; omega)
  -- Get the invariant result (once, for both code value and length)
  have hinv := canonicalCodes_inv_at lengths maxBits hv hmb i hi
  simp only [hlen, ↓reduceIte] at hinv
  refine ⟨cw, hcf, ?_, hinv.1⟩
  obtain ⟨_, _, hcw⟩ := Huffman.Spec.codeFor_spec hcf
  rw [hls_i] at hcw
  rw [hcw]; congr 1
  exact hinv.2.symm

/-- For symbols with zero code length, `canonicalCodes` stores `(0, 0)`. -/
protected theorem canonicalCodes_correct_zero (lengths : Array UInt8) (maxBits : Nat)
    (hv : Huffman.Spec.ValidLengths (lengths.toList.map UInt8.toNat) maxBits)
    (hmb : maxBits < 16)
    (i : Nat) (hi : i < lengths.size) (hlen : ¬(lengths[i] > 0)) :
    (Zip.Native.Deflate.canonicalCodes lengths maxBits)[i]! = (0, 0) := by
  have hinv := canonicalCodes_inv_at lengths maxBits hv hmb i hi
  simp only [hlen, ↓reduceIte] at hinv
  exact hinv

/-- Bridge theorem: the tree built by `fromLengths` has a leaf at the codeword
    stored by `canonicalCodes`, connecting the native encoder to the decoder. -/
protected theorem canonicalCodes_hasLeaf (lengths : Array UInt8)
    (maxBits : Nat) (hmb : maxBits < 16)
    (tree : Zip.Native.HuffTree)
    (htree : Zip.Native.HuffTree.fromLengths lengths maxBits = .ok tree)
    (hv : Huffman.Spec.ValidLengths (lengths.toList.map UInt8.toNat) maxBits)
    (i : Nat) (hi : i < lengths.size) (hlen : lengths[i] > 0) :
    let codes := Zip.Native.Deflate.canonicalCodes lengths maxBits
    TreeHasLeaf tree
      (Huffman.Spec.natToBits codes[i]!.1.toNat codes[i]!.2.toNat)
      i.toUInt16 := by
  intro codes
  let lsList := lengths.toList.map UInt8.toNat
  have hls_len : i < lsList.length := by simp [lsList, hi]
  obtain ⟨cw, hcf, hcw, hlen_eq⟩ :=
    Deflate.Correctness.canonicalCodes_correct_pos lengths maxBits hv hmb i hi hlen
  have hmem : (i, cw) ∈ Huffman.Spec.allCodes lsList maxBits := by
    rw [Huffman.Spec.allCodes_mem_iff]; exact ⟨hls_len, hcf⟩
  have hleaf := Deflate.Correctness.fromLengths_hasLeaf lengths maxBits (by omega) tree htree hv i cw hmem
  rw [hcw] at hleaf
  rw [hlen_eq]
  exact hleaf

end Deflate.Correctness
