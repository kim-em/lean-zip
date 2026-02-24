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

end ByteArray
