import Zip.Spec.Crc32

/-!
# Native Lean CRC-32 Implementation

Pure Lean CRC-32 using a precomputed lookup table.
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

/-! ## Equivalence to spec -/

theorem table_size : table.size = 256 := by native_decide

/-- Table-driven byte update equals bit-by-bit `Spec.crcByte`.
    The proof requires showing the CRC linearity property:
    iterating `crcBit` 8 times on `crc ^^^ byte` equals
    `(crc >>> 8) ^^^ table[(crc ^^^ byte) &&& 0xFF]`.
    This is a consequence of XOR distributivity over the CRC recurrence. -/
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
