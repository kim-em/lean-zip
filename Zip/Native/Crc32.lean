import Zip.Spec.Crc32
import Std.Tactic.BVDecide

/-!
# Native Lean CRC-32 Implementation

Pure Lean CRC-32 using a precomputed lookup table, proved equivalent
to the bit-by-bit specification.
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

/-! ## Proof infrastructure -/

theorem table_size : table.size = 256 := Array.size_ofFn ..

/-- CRC linearity: `crcBit` distributes over XOR when the extra term has bit 0 = 0. -/
theorem crcBit_xor_high (a b : UInt32) (ha : a &&& 1 = 0) :
    Spec.crcBit (a ^^^ b) = (a >>> 1) ^^^ Spec.crcBit b := by
  simp only [Spec.crcBit, Spec.POLY]; bv_decide

/-- `UInt32.ofNat byte.toNat` is a zero-extension from 8 to 32 bits. -/
private theorem UInt32_ofNat_UInt8_toNat (byte : UInt8) :
    UInt32.ofNat byte.toNat = ⟨byte.toBitVec.setWidth 32⟩ := by
  show UInt32.ofBitVec (BitVec.ofNat 32 byte.toBitVec.toNat) =
       UInt32.ofBitVec (byte.toBitVec.setWidth 32)
  congr 1; exact BitVec.ofNat_toNat 32 byte.toBitVec

/-- 8-fold `crcBit` splits: the high 24 bits shift right and XOR separately
    from the low 8 bits that go through the polynomial reduction. -/
private theorem crcBits8_split (v : UInt32) :
    Spec.crcBit (Spec.crcBit (Spec.crcBit (Spec.crcBit
      (Spec.crcBit (Spec.crcBit (Spec.crcBit (Spec.crcBit v))))))) =
    (v >>> 8) ^^^ Spec.crcBit (Spec.crcBit (Spec.crcBit (Spec.crcBit
      (Spec.crcBit (Spec.crcBit (Spec.crcBit (Spec.crcBit (v &&& 0xFF)))))))) := by
  simp only [Spec.crcBit, Spec.POLY]; bv_decide

/-- XOR with a zero-extended byte doesn't affect bits 8–31 after right shift. -/
private theorem xor_byte_shr8 (crc : UInt32) (byte : UInt8) :
    (crc ^^^ UInt32.ofNat byte.toNat) >>> 8 = crc >>> 8 := by
  rw [UInt32_ofNat_UInt8_toNat]
  show UInt32.ofBitVec ((crc.toBitVec ^^^ byte.toBitVec.setWidth 32) >>> 8) =
       UInt32.ofBitVec (crc.toBitVec >>> 8)
  congr 1; bv_decide

private theorem and_0xFF_toNat_lt (x : UInt32) : (x &&& 0xFF).toNat < 256 := by
  show (x.toBitVec &&& (255 : BitVec 32)).toNat < 256
  rw [BitVec.toNat_and]
  change x.toBitVec.toNat &&& 255 < 256
  exact Nat.and_lt_two_pow _ (by omega : (255 : Nat) < 2 ^ 8)

private theorem table_getElem (i : Nat) (h : i < table.size) :
    table[i] = Spec.crcBit (Spec.crcBit (Spec.crcBit (Spec.crcBit
      (Spec.crcBit (Spec.crcBit (Spec.crcBit (Spec.crcBit (UInt32.ofNat i)))))))) := by
  simp only [table, Spec.mkTable, Array.getElem_ofFn]

/-- Table-driven byte update equals bit-by-bit `Spec.crcByte`. -/
theorem crcByteTable_eq_crcByte (crc : UInt32) (byte : UInt8) :
    Spec.crcByteTable table crc byte = Spec.crcByte crc byte := by
  simp only [Spec.crcByteTable]
  have hlt : ((crc ^^^ UInt32.ofNat byte.toNat) &&& 0xFF).toNat < table.size := by
    rw [table_size]; exact and_0xFF_toNat_lt _
  rw [dif_pos hlt, table_getElem _ hlt, UInt32.ofNat_toNat]
  simp only [Spec.crcByte]
  rw [crcBits8_split (crc ^^^ UInt32.ofNat byte.toNat), xor_byte_shr8]

/-- `updateBytes` equals `Spec.updateList` on the underlying array data. -/
theorem updateBytes_eq_updateList (crc : UInt32) (data : ByteArray) :
    updateBytes crc data = Spec.updateList crc data.data.toList := by
  simp only [updateBytes, Spec.updateList, Array.foldl_toList]
  have : Spec.crcByteTable table = Spec.crcByte :=
    funext fun _ => funext fun _ => crcByteTable_eq_crcByte ..
  rw [this]

/-- The CRC-32 of an empty input equals the supplied `init` (with the
zlib convention that `init = 0` denotes a fresh checksum that still
ends up at `0`). -/
@[simp] theorem crc32_empty (init : UInt32) :
    crc32 init ByteArray.empty = init := by
  simp only [crc32, updateBytes, ByteArray.data_empty, Array.foldl_empty]
  bv_decide

/-- Closed form for the CRC-32 of a single byte starting from the
default `init = 0` (which the `crc32` wrapper rewrites to the internal
running state `0xFFFFFFFF`). Matches `Spec.checksum_singleton` via
`updateBytes_eq_updateList`. -/
theorem crc32_singleton (b : UInt8) :
    crc32 0 (ByteArray.mk #[b]) =
      0xFF000000 ^^^ Spec.mkTable[0xFF ^^^ b.toNat]'(by
        exact Spec.xor_ff_byte_lt_mkTable_size b) := by
  have hdata : (ByteArray.mk #[b]).data.toList = [b] := rfl
  simp only [crc32]
  show _ ^^^ (0xFFFFFFFF : UInt32) = _
  rw [show ((0 : UInt32) == 0) = true from rfl, if_pos rfl,
    updateBytes_eq_updateList, hdata]
  exact Spec.checksum_singleton b

/-- Closed form for the CRC-32 of a two-byte input starting from the
default `init = 0`. Matches `Spec.checksum_pair` via
`updateBytes_eq_updateList`. -/
theorem crc32_pair (b₁ b₂ : UInt8) :
    crc32 0 (ByteArray.mk #[b₁, b₂]) =
      (let s₁ : UInt32 :=
        0x00FFFFFF ^^^ Spec.mkTable[0xFF ^^^ b₁.toNat]'
          (by exact Spec.xor_ff_byte_lt_mkTable_size b₁)
       (s₁ >>> 8) ^^^
         Spec.mkTable[((s₁ ^^^ UInt32.ofNat b₂.toNat) &&& 0xFF).toNat]'(by
           rw [Spec.mkTable_size]; exact and_0xFF_toNat_lt _) ^^^ 0xFFFFFFFF) := by
  have hdata : (ByteArray.mk #[b₁, b₂]).data.toList = [b₁, b₂] := rfl
  simp only [crc32]
  show _ ^^^ (0xFFFFFFFF : UInt32) = _
  rw [show ((0 : UInt32) == 0) = true from rfl, if_pos rfl,
    updateBytes_eq_updateList, hdata]
  exact Spec.checksum_pair b₁ b₂

/-- Compositionality of incremental CRC-32 computation (native level,
see `PLAN.md:27-28`). Associativity of `crc32` over `ByteArray` append
— an incremental streaming pipeline over concatenated chunks yields
the same result as a whole-buffer computation. -/
theorem crc32_append (init : UInt32) (a b : ByteArray) :
    crc32 init (a ++ b) = crc32 (crc32 init a) b := by
  have raw_eq : ∀ x : UInt32,
      (if x == 0 then (0xFFFFFFFF : UInt32) else x ^^^ 0xFFFFFFFF) = x ^^^ 0xFFFFFFFF := by
    bv_decide
  simp only [crc32, raw_eq]
  simp only [UInt32.xor_assoc, UInt32.xor_self, UInt32.xor_zero,
    updateBytes_eq_updateList, ByteArray.data_append, Array.toList_append,
    Spec.updateList_append]

end Crc32.Native
