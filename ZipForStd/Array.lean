import ZipForStd.List

/-!
# Array lemmas for the standard library

Generic lemmas about `Array.set!` and `getElem!` that are useful beyond the
Huffman module. Candidates for upstreaming to Lean's standard library.
-/

namespace Array

/-- `Array.set!` at a different index preserves the element. -/
theorem getElem!_set!_ne [Inhabited α] (arr : Array α) (i j : Nat) (v : α) (hij : i ≠ j) :
    (arr.set! i v)[j]! = arr[j]! := by
  simp [getElem!_eq_getD, getD_eq_getD_getElem?,
        set!_eq_setIfInBounds, getElem?_setIfInBounds_ne hij]

/-- `Array.set!` at the same index replaces the value. -/
theorem getElem!_set!_self [Inhabited α] (arr : Array α) (i : Nat) (v : α) (hi : i < arr.size) :
    (arr.set! i v)[i]! = v := by
  simp [getElem!_eq_getD, getD_eq_getD_getElem?,
        set!_eq_setIfInBounds, getElem?_setIfInBounds_self_of_lt hi]

/-- Incrementing `arr[k]!` preserves monotonicity: `arr[idx]! ≤ (arr.set! k (arr[k]! + 1))[idx]!`. -/
theorem getElem!_le_set!_incr (arr : Array Nat) (k idx : Nat) (hk : k < arr.size) :
    arr[idx]! ≤ (arr.set! k (arr[k]! + 1))[idx]! := by
  by_cases heq : k = idx
  · subst heq; rw [getElem!_set!_self arr _ _ hk]; omega
  · rw [getElem!_set!_ne arr _ _ _ heq]; omega

/-! ## extract/set decomposition -/

/-- `set!` at index `idx` followed by `extract 0 (idx+1)` gives
    the original prefix mapped to Nat, plus the new value's Nat. -/
theorem extract_set_map_append (arr : Array UInt8) (idx : Nat) (val : UInt8)
    (hidx : idx < arr.size) :
    ((arr.set! idx val).extract 0 (idx + 1)).toList.map UInt8.toNat =
    (arr.extract 0 idx).toList.map UInt8.toNat ++ [val.toNat] := by
  rw [Array.set!, Array.toList_extract, Array.toList_setIfInBounds, Array.toList_extract]
  simp only [List.extract, Nat.sub_zero, List.drop_zero]
  rw [List.take_set_succ _ _ _ (by rw [Array.length_toList]; exact hidx)]
  simp [List.map_append]

/-- The last element of a mapped extract equals the mapped array element. -/
theorem extract_map_getLast_eq (arr : Array UInt8) (idx : Nat)
    (hidx : 0 < idx) (hle : idx ≤ arr.size) :
    ((arr.extract 0 idx).toList.map UInt8.toNat).getLast! = arr[idx - 1]!.toNat := by
  simp only [Array.toList_extract, List.extract, Nat.sub_zero, List.drop_zero, List.map_take]
  have hlen : (List.take idx (List.map UInt8.toNat arr.toList)).length = idx := by
    simp [List.length_take, List.length_map, Array.length_toList, Nat.min_eq_left hle]
  rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_getElem?, hlen,
    List.getElem?_eq_getElem (by omega)]
  simp only [Option.getD_some]
  rw [getElem!_pos arr _ (by omega),
    @List.getElem_take _ (arr.toList.map UInt8.toNat) idx (idx - 1) (by rw [hlen]; omega)]
  simp [List.getElem_map]

end Array
