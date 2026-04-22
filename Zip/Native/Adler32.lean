import Zip.Spec.Adler32

/-!
# Native Lean Adler-32 Implementation

Pure Lean implementation of Adler-32 (RFC 1950). Operates on `ByteArray`
for practical use; proved equivalent to the list-based specification.
-/

namespace Adler32.Native

/-- Process a `ByteArray`, updating the Adler-32 state. -/
def updateBytes (s : Spec.State) (data : ByteArray) : Spec.State :=
  data.data.foldl Spec.updateByte s

/-- Compute Adler-32 of an entire `ByteArray`. -/
def adler32 (init : UInt32 := 1) (data : ByteArray) : UInt32 :=
  let s := Spec.unpack init
  let s' := updateBytes s data
  Spec.pack s'

/-! ## Equivalence to spec -/

/-- `updateBytes` equals `Spec.updateList` on the underlying array data. -/
theorem updateBytes_eq_updateList (s : Spec.State) (data : ByteArray) :
    updateBytes s data = Spec.updateList s data.data.toList := by
  simp only [updateBytes, ByteArray.size_data, Spec.updateList, Array.foldl_toList]

/-- `updateBytes` preserves validity. -/
theorem updateBytes_valid (s : Spec.State) (hs : Spec.Valid s) (data : ByteArray) :
    Spec.Valid (updateBytes s data) := by
  rw [updateBytes_eq_updateList]
  exact Spec.updateList_valid s hs _

/-- Compositionality of incremental Adler-32 computation (native level,
see `PLAN.md:27-28`). Associativity of `adler32` over `ByteArray`
append — an incremental streaming pipeline over concatenated chunks
yields the same result as a whole-buffer computation. -/
theorem adler32_append (init : UInt32) (a b : ByteArray) :
    adler32 init (a ++ b) = adler32 (adler32 init a) b := by
  simp only [adler32, updateBytes_eq_updateList, ByteArray.data_append,
    Array.toList_append, Spec.updateList_append]
  -- Goal: pack (updateList (updateList (unpack init) A) B)
  --     = pack (updateList (unpack (pack (updateList (unpack init) A))) B)
  -- Case split on whether A = a.data.toList is empty; Valid applies only in the
  -- cons case. The nil case reduces via `pack_unpack`.
  generalize a.data.toList = A
  match A with
  | [] => rw [Spec.updateList_nil, Spec.pack_unpack]
  | x :: xs =>
    rw [Spec.unpack_pack_of_valid _ (Spec.updateList_cons .. ▸
      Spec.updateList_valid _ (Spec.updateByte_valid ..) _)]

end Adler32.Native
