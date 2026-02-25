import ZipForStd.Array

/-!
# ByteArray lemmas for the standard library

Generic lemmas about `ByteArray` indexing that bridge between
`ByteArray` get-element, `Array` get-element, and `List` get-element.
Candidates for upstreaming to Lean's standard library.
-/

namespace ByteArray

/-- `ByteArray` indexing agrees with `Array.toList` indexing. -/
theorem getElem_toList (data : ByteArray) (i : Nat) (h : i < data.size)
    (h' : i < data.data.toList.length := by simp [Array.length_toList]; exact h) :
    (data[i]'h : UInt8) = data.data.toList[i] := by
  show data.data[i] = data.data.toList[i]
  rw [← Array.getElem_toList]

/-- `ByteArray.getElem!` agrees with `Array.toList` indexing when in bounds. -/
theorem getElem!_toList (data : ByteArray) (i : Nat) (h : i < data.size) :
    data[i]! = data.data.toList[i]'(by simp [Array.length_toList]; exact h) := by
  rw [getElem!_pos data i h]
  exact getElem_toList data i h

/-- `ByteArray.data.toList.length` equals `ByteArray.size`. -/
theorem data_toList_length (data : ByteArray) :
    data.data.toList.length = data.size :=
  Array.length_toList

/-- Extract from `a ++ b` starting at or past `a.size` gives an extract of `b`. -/
theorem extract_append_ge (a b : ByteArray) (i j : Nat) (h : i ≥ a.size) :
    (a ++ b).extract i j = b.extract (i - a.size) (j - a.size) := by
  apply ByteArray.ext
  simp [ByteArray.data_extract, ByteArray.data_append, Array.extract_append]
  omega

/-- Extracting from 0 to `a.size` in `a ++ b` gives `a`. -/
theorem extract_append_left (a b : ByteArray) :
    (a ++ b).extract 0 a.size = a := by
  apply ByteArray.ext; simp

/-! ## `set!` interaction lemmas -/

/-- ByteArray.getElem! is the same as Array.getElem! on the underlying data. -/
private theorem getElem!_eq_data_getElem! (ba : ByteArray) (i : Nat) :
    ba[i]! = ba.data[i]! := by
  by_cases h : i < ba.size
  · rw [getElem!_pos ba i h, getElem!_pos ba.data i h]
    rfl
  · rw [getElem!_neg ba i h, getElem!_neg ba.data i h]

/-- `ByteArray.set!` preserves size. -/
theorem size_set! (data : ByteArray) (i : Nat) (v : UInt8) :
    (data.set! i v).size = data.size := by
  show (data.data.setIfInBounds i v).size = data.data.size
  exact Array.size_setIfInBounds ..

/-- Setting a byte and reading at the same index returns the written value. -/
theorem getElem!_set!_self (data : ByteArray) (i : Nat) (v : UInt8) (h : i < data.size) :
    (data.set! i v)[i]! = v := by
  rw [getElem!_eq_data_getElem!]
  show (data.data.set! i v)[i]! = v
  exact Array.getElem!_set!_self data.data i v h

/-- Setting a byte at index `i` doesn't affect reads at a different index `j`. -/
theorem getElem!_set!_ne (data : ByteArray) (i j : Nat) (v : UInt8) (hij : i ≠ j) :
    (data.set! i v)[j]! = data[j]! := by
  rw [getElem!_eq_data_getElem!, getElem!_eq_data_getElem!]
  show (data.data.set! i v)[j]! = data.data[j]!
  exact Array.getElem!_set!_ne data.data i j v hij

end ByteArray
