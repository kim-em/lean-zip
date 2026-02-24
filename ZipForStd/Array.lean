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

end Array
