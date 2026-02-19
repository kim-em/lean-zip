import Zip.Spec.Crc32
import Std.Tactic.BVDecide

/-!
# Native Lean CRC-32 Implementation

Pure Lean CRC-32 using a precomputed lookup table, with the key
linearity lemma proved and the full table equivalence pending.
-/

namespace Crc32.Native

/-- Precomputed CRC-32 lookup table (256 entries). -/
def table : Array UInt32 := Spec.mkTable

/-- Process a `ByteArray` using the table-driven algorithm. -/
def updateBytes (crc : UInt32) (data : ByteArray) : UInt32 :=
  data.data.foldl (Spec.crcByteTable table) crc

/-- Compute CRC-32 of a `ByteArray`.
    Matches the zlib API: `init = 0` starts a fresh checksum. -/
def crc32 (init : UInt32 := 0) (data : ByteArray) : UInt32 :=
  let raw := if init == 0 then 0xFFFFFFFF else init ^^^ 0xFFFFFFFF
  let result := updateBytes raw data
  result ^^^ 0xFFFFFFFF

/-! ## Proof infrastructure

The table-driven CRC uses the linearity of `crcBit` over XOR: when
the low bit of `a` is zero, `crcBit(a ^^^ b) = (a >>> 1) ^^^ crcBit(b)`.
Iterating 8 times gives the table identity. -/

/-- CRC linearity: `crcBit` distributes over XOR when the extra term has bit 0 = 0. -/
theorem crcBit_xor_high (a b : UInt32) (ha : a &&& 1 = 0) :
    Spec.crcBit (a ^^^ b) = (a >>> 1) ^^^ Spec.crcBit b := by
  simp only [Spec.crcBit, Spec.POLY]; bv_decide

theorem table_size : table.size = 256 := Array.size_ofFn ..

/-- Table-driven byte update equals bit-by-bit `Spec.crcByte`.
    Proof requires iterating `crcBit_xor_high` 8 times and connecting
    the table lookup to the bit-by-bit computation. -/
theorem crcByteTable_eq_crcByte (crc : UInt32) (byte : UInt8) :
    Spec.crcByteTable table crc byte = Spec.crcByte crc byte := by
  sorry

/-- `updateBytes` equals `Spec.updateList` on the underlying array data. -/
theorem updateBytes_eq_updateList (crc : UInt32) (data : ByteArray) :
    updateBytes crc data = Spec.updateList crc data.data.toList := by
  simp only [updateBytes, Spec.updateList, Array.foldl_toList]
  have : Spec.crcByteTable table = Spec.crcByte :=
    funext fun crc => funext fun byte => crcByteTable_eq_crcByte crc byte
  rw [this]

end Crc32.Native
