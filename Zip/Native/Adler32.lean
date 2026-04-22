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

/-- The Adler-32 of an empty input equals the supplied `init`.
The pack/unpack roundtrip is the identity on any `UInt32`, so feeding
no bytes leaves the state — and therefore the packed checksum —
unchanged. -/
@[simp] theorem adler32_empty (init : UInt32) :
    adler32 init ByteArray.empty = init := by
  simp only [adler32, updateBytes, ByteArray.data_empty, Array.foldl_empty]
  exact Spec.pack_unpack init

/-- Closed form for the Adler-32 of a single byte starting from the
default `init = 1`. Matches `Spec.checksum_singleton` after bridging
the pack/unpack on the initial state. -/
theorem adler32_singleton (b : UInt8) :
    adler32 1 (ByteArray.push ByteArray.empty b) =
    UInt32.ofNat ((1 + b.toNat) * 65537) := by
  have hdata : (ByteArray.push ByteArray.empty b).data.toList = [b] := rfl
  have hunpack : Spec.unpack 1 = Spec.init := by decide
  simp only [adler32, updateBytes_eq_updateList, hdata, hunpack]
  exact Spec.checksum_singleton b

/-- Closed form for the Adler-32 of a two-byte input starting from the
default `init = 1`. Matches `Spec.checksum_pair` after bridging the
pack/unpack on the initial state. -/
theorem adler32_pair (b₁ b₂ : UInt8) :
    adler32 1 ((ByteArray.empty.push b₁).push b₂) =
    UInt32.ofNat
      ((1 + b₁.toNat + b₂.toNat) +
       (2 + 2 * b₁.toNat + b₂.toNat) * 65536) := by
  have hdata : ((ByteArray.empty.push b₁).push b₂).data.toList = [b₁, b₂] := rfl
  have hunpack : Spec.unpack 1 = Spec.init := by decide
  simp only [adler32, updateBytes_eq_updateList, hdata, hunpack]
  exact Spec.checksum_pair b₁ b₂

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
