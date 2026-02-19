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
  simp [updateBytes, Spec.updateList, Array.foldl_toList]

end Adler32.Native
