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

/-- Native Adler-32 of `n` zero bytes starting from the default
`init = 1`, closed form matching `Spec.checksum_replicate_zero`
after bridging the `ByteArray` to its underlying `List UInt8`. -/
theorem adler32_replicate_zero (n : Nat) (hn : n < 65521) :
    adler32 1 (ByteArray.mk (Array.replicate n 0)) =
      UInt32.ofNat (1 + n * 65536) := by
  have hunpack : Spec.unpack 1 = Spec.init := by decide
  simp only [adler32, updateBytes_eq_updateList, hunpack]
  exact Spec.checksum_replicate_zero n hn

/-- Native Adler-32 of `n` copies of byte `b` starting from the
default `init = 1`, closed form matching `Spec.checksum_replicate`
after bridging the `ByteArray` to its underlying `List UInt8`. -/
theorem adler32_replicate (n : Nat) (b : UInt8)
    (hA : 1 + n * b.toNat < 65521)
    (hB : n + (n * (n + 1) / 2) * b.toNat < 65521) :
    adler32 1 (ByteArray.mk (Array.replicate n b)) =
      UInt32.ofNat ((n + (n * (n + 1) / 2) * b.toNat) * 65536
                     + (1 + n * b.toNat)) := by
  have hunpack : Spec.unpack 1 = Spec.init := by decide
  simp only [adler32, updateBytes_eq_updateList, hunpack]
  exact Spec.checksum_replicate n b hA hB

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

/-- Combine two Adler-32 checksums of adjacent byte blocks into the
checksum of their concatenation, given the length of the second block.
Mirrors zlib's `adler32_combine` closed form — this is a characterizing
property of Adler-32 that makes parallel hashing possible. -/
def adler32_combine (a b : UInt32) (len2 : Nat) : UInt32 :=
  let ⟨a1, a2⟩ := Spec.unpack a
  let ⟨b1, b2⟩ := Spec.unpack b
  Spec.pack ((a1 + b1 + Spec.MOD_ADLER - 1) % Spec.MOD_ADLER,
             (a2 + len2 * a1 + b2 + len2 * Spec.MOD_ADLER - len2) % Spec.MOD_ADLER)

/-- Correctness of `adler32_combine` starting from the default `init = 1`:
combining the two block checksums produces the checksum of the
concatenation. Native-level counterpart of `Spec.checksum_combine`,
bridged through `updateBytes_eq_updateList`. -/
theorem adler32_combine_eq_concat (xs ys : ByteArray) :
    adler32_combine (adler32 1 xs) (adler32 1 ys) ys.size
      = adler32 1 (xs ++ ys) := by
  have hunpack : Spec.unpack 1 = Spec.init := by decide
  have ha_valid : Spec.Valid (Spec.updateList Spec.init xs.data.toList) :=
    Spec.updateList_valid Spec.init Spec.init_valid _
  have hb_valid : Spec.Valid (Spec.updateList Spec.init ys.data.toList) :=
    Spec.updateList_valid Spec.init Spec.init_valid _
  -- Unpack the packed intermediate results back to the running states.
  have hunpack_a :
      Spec.unpack (adler32 1 xs) = Spec.updateList Spec.init xs.data.toList := by
    simp only [adler32, updateBytes_eq_updateList, hunpack]
    exact Spec.unpack_pack_of_valid _ ha_valid
  have hunpack_b :
      Spec.unpack (adler32 1 ys) = Spec.updateList Spec.init ys.data.toList := by
    simp only [adler32, updateBytes_eq_updateList, hunpack]
    exact Spec.unpack_pack_of_valid _ hb_valid
  have hsize : ys.size = ys.data.toList.length := by
    simp only [ByteArray.size_data, Array.length_toList]
  -- Bridge `adler32 1 (xs ++ ys)` to the spec `checksum` formula.
  have hcat : adler32 1 (xs ++ ys) =
      Spec.checksum (xs.data.toList ++ ys.data.toList) := by
    simp only [adler32, updateBytes_eq_updateList, ByteArray.data_append,
      Array.toList_append, hunpack, Spec.checksum]
  have hcomb := Spec.checksum_combine xs.data.toList ys.data.toList
  simp only at hcomb
  unfold adler32_combine
  simp only [hunpack_a, hunpack_b, hsize]
  rw [hcat, hcomb]

end Adler32.Native
