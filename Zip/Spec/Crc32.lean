import Std.Tactic.BVDecide

/-!
# CRC-32 Specification

CRC-32 as used in gzip, ZIP, PNG, etc. (ISO 3309 / ITU-T V.42).

The polynomial is 0xEDB88320 (bit-reversed representation of 0x04C11DB7).

The algorithm:
1. Initialize CRC to 0xFFFFFFFF
2. For each byte, XOR the byte into the low 8 bits of the CRC,
   then for each of the 8 bits, if the LSB is set, shift right and
   XOR with the polynomial; otherwise just shift right.
3. Final XOR with 0xFFFFFFFF (complement).

Characterizing property: compositionality of incremental computation
(see `PLAN.md:27-28`) — `checksum (xs ++ ys)` can be recovered from
`checksum xs` by decoding its running state, feeding more bytes, then
re-applying the final XOR. See `checksum_append` below.
-/

namespace Crc32.Spec

/-- The CRC-32 polynomial (bit-reversed). -/
def POLY : UInt32 := 0xEDB88320

/-- Process one bit of a CRC-32 computation.
    If the LSB is 1, shift right and XOR with the polynomial.
    Otherwise, just shift right. -/
def crcBit (crc : UInt32) : UInt32 :=
  if crc &&& 1 == 1 then
    (crc >>> 1) ^^^ POLY
  else
    crc >>> 1

/-- Process one byte by XORing it into the CRC and processing 8 bits. -/
def crcByte (crc : UInt32) (byte : UInt8) : UInt32 :=
  let crc := crc ^^^ UInt32.ofNat byte.toNat
  crcBit (crcBit (crcBit (crcBit (crcBit (crcBit (crcBit (crcBit crc)))))))

/-- Process a list of bytes. -/
def updateList (crc : UInt32) (data : List UInt8) : UInt32 :=
  data.foldl crcByte crc

/-- Compute CRC-32 of a byte list (with initial and final complement). -/
def checksum (data : List UInt8) : UInt32 :=
  (updateList 0xFFFFFFFF data) ^^^ 0xFFFFFFFF

/-! ## Specification theorems -/

/-- `updateList` over a concatenation equals sequential application. -/
theorem updateList_append (crc : UInt32) (xs ys : List UInt8) :
    updateList crc (xs ++ ys) = updateList (updateList crc xs) ys := by
  simp only [updateList, List.foldl_append]

/-- Empty input leaves the CRC unchanged. -/
theorem updateList_nil (crc : UInt32) : updateList crc [] = crc := rfl

/-- The CRC-32 checksum of the empty input is `0`. -/
@[simp] theorem checksum_empty : checksum [] = 0 := by
  simp only [checksum, updateList_nil]
  bv_decide

/-- Compositionality of incremental CRC-32 computation (spec level).
The running state after processing `xs` is `checksum xs ^^^ 0xFFFFFFFF`;
feeding `ys` into that state and re-applying the final XOR yields
`checksum (xs ++ ys)`. -/
theorem checksum_append (xs ys : List UInt8) :
    checksum (xs ++ ys) =
    updateList (checksum xs ^^^ 0xFFFFFFFF) ys ^^^ 0xFFFFFFFF := by
  unfold checksum
  rw [updateList_append]
  have xor_twice : ∀ x : UInt32, (x ^^^ 0xFFFFFFFF) ^^^ 0xFFFFFFFF = x := by
    intro x; bv_decide
  rw [xor_twice]

/-- The CRC-32 lookup table: precomputed CRC for each byte value 0..255. -/
def mkTable : Array UInt32 :=
  Array.ofFn fun (i : Fin 256) =>
    let crc := UInt32.ofNat i.val
    crcBit (crcBit (crcBit (crcBit (crcBit (crcBit (crcBit (crcBit crc)))))))

/-- Table-driven single-byte CRC update. -/
def crcByteTable (table : Array UInt32) (crc : UInt32) (byte : UInt8) : UInt32 :=
  let index := ((crc ^^^ UInt32.ofNat byte.toNat) &&& 0xFF).toNat
  if h : index < table.size then
    (crc >>> 8) ^^^ table[index]
  else
    crc -- unreachable for a 256-entry table

/-! ## Table-level closed form for a single byte

Helpers below are duplicated from `Zip/Native/Crc32.lean` so that the
Spec file does not depend on the Native implementation. The Native
side keeps its own copies as the build order is `Spec → Native`. -/

/-- The `mkTable` array has size 256. -/
theorem mkTable_size : mkTable.size = 256 := Array.size_ofFn ..

/-- For any byte `b`, `0xFF ^^^ b.toNat < mkTable.size`. Shared by
`checksum_singleton` and its native-side wrapper `crc32_singleton`. -/
theorem xor_ff_byte_lt_mkTable_size (b : UInt8) :
    0xFF ^^^ b.toNat < mkTable.size := by
  rw [mkTable_size]
  exact Nat.xor_lt_two_pow (by decide : (0xFF : Nat) < 2 ^ 8) b.toNat_lt

private theorem mkTable_getElem (i : Nat) (h : i < mkTable.size) :
    mkTable[i] = crcBit (crcBit (crcBit (crcBit
      (crcBit (crcBit (crcBit (crcBit (UInt32.ofNat i)))))))) := by
  simp only [mkTable, Array.getElem_ofFn]

/-- 8-fold `crcBit` splits: the high 24 bits shift right and XOR
separately from the low 8 bits that go through the polynomial
reduction. -/
private theorem crcBits8_split (v : UInt32) :
    crcBit (crcBit (crcBit (crcBit (crcBit (crcBit (crcBit (crcBit v))))))) =
    (v >>> 8) ^^^ crcBit (crcBit (crcBit (crcBit
      (crcBit (crcBit (crcBit (crcBit (v &&& 0xFF)))))))) := by
  simp only [crcBit, POLY]; bv_decide

private theorem UInt32_ofNat_UInt8_toNat (b : UInt8) :
    UInt32.ofNat b.toNat = ⟨b.toBitVec.setWidth 32⟩ := by
  show UInt32.ofBitVec (BitVec.ofNat 32 b.toBitVec.toNat) =
       UInt32.ofBitVec (b.toBitVec.setWidth 32)
  congr 1; exact BitVec.ofNat_toNat 32 b.toBitVec

private theorem and_0xFF_toNat_lt (x : UInt32) : (x &&& 0xFF).toNat < 256 := by
  show (x.toBitVec &&& (255 : BitVec 32)).toNat < 256
  rw [BitVec.toNat_and]
  change x.toBitVec.toNat &&& 255 < 256
  exact Nat.and_lt_two_pow _ (by omega : (255 : Nat) < 2 ^ 8)

private theorem xor_byte_shr8 (crc : UInt32) (byte : UInt8) :
    (crc ^^^ UInt32.ofNat byte.toNat) >>> 8 = crc >>> 8 := by
  rw [UInt32_ofNat_UInt8_toNat]
  show UInt32.ofBitVec ((crc.toBitVec ^^^ byte.toBitVec.setWidth 32) >>> 8) =
       UInt32.ofBitVec (crc.toBitVec >>> 8)
  congr 1; bv_decide

/-- Table-driven byte update equals bit-by-bit `crcByte`. Spec-level
restatement of the identity proven at the Native level; stated here so
downstream Spec-level closed-form theorems (like `checksum_singleton`)
do not have to pull in the Native implementation. -/
theorem crcByteTable_mkTable_eq_crcByte (crc : UInt32) (byte : UInt8) :
    crcByteTable mkTable crc byte = crcByte crc byte := by
  simp only [crcByteTable]
  have hlt : ((crc ^^^ UInt32.ofNat byte.toNat) &&& 0xFF).toNat < mkTable.size := by
    rw [mkTable_size]; exact and_0xFF_toNat_lt _
  rw [dif_pos hlt, mkTable_getElem _ hlt, UInt32.ofNat_toNat]
  simp only [crcByte]
  rw [crcBits8_split (crc ^^^ UInt32.ofNat byte.toNat), xor_byte_shr8]

/-- The CRC-32 checksum of a single byte has a closed form as a single
`mkTable` lookup. This is the `checksum_singleton` rung of the CRC-32
ladder, analogous to `Adler32.Spec.checksum_singleton`. The high byte
`0xFF000000` comes from `(0xFFFFFFFF >>> 8) ^^^ 0xFFFFFFFF`. -/
theorem checksum_singleton (b : UInt8) :
    checksum [b] =
      0xFF000000 ^^^ mkTable[0xFF ^^^ b.toNat]'(by exact xor_ff_byte_lt_mkTable_size b) := by
  -- Bridge via the table-driven byte update; `checksum [b]` is literally
  -- `crcByte 0xFFFFFFFF b ^^^ 0xFFFFFFFF` by unfolding `checksum`.
  show crcByte 0xFFFFFFFF b ^^^ 0xFFFFFFFF = _
  rw [← crcByteTable_mkTable_eq_crcByte]
  simp only [crcByteTable]
  have hb32 : b.toNat < UInt32.size := Nat.lt_trans b.toNat_lt (by decide)
  have hlt : ((((0xFFFFFFFF : UInt32) ^^^ UInt32.ofNat b.toNat) &&& 0xFF).toNat) <
      mkTable.size := by rw [mkTable_size]; exact and_0xFF_toNat_lt _
  rw [dif_pos hlt]
  -- The internal `crcByteTable` index equals the simpler `0xFF ^^^ b.toNat`.
  have hidx :
      (((0xFFFFFFFF : UInt32) ^^^ UInt32.ofNat b.toNat) &&& 0xFF).toNat =
      0xFF ^^^ b.toNat := by
    rw [UInt32.toNat_and, UInt32.toNat_xor, UInt32.toNat_ofNat_of_lt' hb32,
      show ((0xFFFFFFFF : UInt32).toNat) = 0xFFFFFFFF from rfl,
      show ((0xFF : UInt32).toNat) = 0xFF from rfl,
      Nat.and_xor_distrib_right,
      show (0xFFFFFFFF : Nat) &&& 0xFF = 0xFF from rfl,
      Nat.and_two_pow_sub_one_of_lt_two_pow (n := 8) b.toNat_lt]
  -- Unify the two `mkTable` accesses via index congruence + proof irrelevance.
  rw [getElem_congr_idx (c := mkTable) hidx]
  generalize mkTable[0xFF ^^^ b.toNat]'(hidx ▸ hlt) = t
  bv_decide

/-- The CRC-32 checksum of a two-byte input `[b₁, b₂]` has a closed
form as two `mkTable` lookups. The running state `s₁` after byte `b₁`
is `0x00FFFFFF ^^^ mkTable[0xFF ^^^ b₁.toNat]` (the `0x00FFFFFF` comes
from `0xFFFFFFFF >>> 8`); then the second table lookup is indexed by
the low byte of `s₁ ^^^ b₂`. The trailing `^^^ 0xFFFFFFFF` is the
final complement. -/
theorem checksum_pair (b₁ b₂ : UInt8) :
    checksum [b₁, b₂] =
      (let s₁ : UInt32 :=
        0x00FFFFFF ^^^ mkTable[0xFF ^^^ b₁.toNat]'
          (by exact xor_ff_byte_lt_mkTable_size b₁)
       (s₁ >>> 8) ^^^
         mkTable[((s₁ ^^^ UInt32.ofNat b₂.toNat) &&& 0xFF).toNat]'(by
           rw [mkTable_size]; exact and_0xFF_toNat_lt _) ^^^ 0xFFFFFFFF) := by
  -- Bridge the inner `crcByte` through the table.
  show crcByte (crcByte 0xFFFFFFFF b₁) b₂ ^^^ 0xFFFFFFFF = _
  rw [← crcByteTable_mkTable_eq_crcByte 0xFFFFFFFF b₁]
  simp only [crcByteTable]
  have hb1 : b₁.toNat < UInt32.size := Nat.lt_trans b₁.toNat_lt (by decide)
  have hlt₁ : ((((0xFFFFFFFF : UInt32) ^^^ UInt32.ofNat b₁.toNat) &&& 0xFF).toNat) <
      mkTable.size := by rw [mkTable_size]; exact and_0xFF_toNat_lt _
  rw [dif_pos hlt₁]
  -- Simplify the inner index to `0xFF ^^^ b₁.toNat`.
  have hidx₁ :
      (((0xFFFFFFFF : UInt32) ^^^ UInt32.ofNat b₁.toNat) &&& 0xFF).toNat =
      0xFF ^^^ b₁.toNat := by
    rw [UInt32.toNat_and, UInt32.toNat_xor, UInt32.toNat_ofNat_of_lt' hb1,
      show ((0xFFFFFFFF : UInt32).toNat) = 0xFFFFFFFF from rfl,
      show ((0xFF : UInt32).toNat) = 0xFF from rfl,
      Nat.and_xor_distrib_right,
      show (0xFFFFFFFF : Nat) &&& 0xFF = 0xFF from rfl,
      Nat.and_two_pow_sub_one_of_lt_two_pow (n := 8) b₁.toNat_lt]
  rw [getElem_congr_idx (c := mkTable) hidx₁]
  -- `0xFFFFFFFF >>> 8 = 0x00FFFFFF`, so the running state matches `s₁`.
  rw [show ((0xFFFFFFFF : UInt32) >>> 8) = 0x00FFFFFF from rfl]
  -- Bridge the outer `crcByte` through the table.
  rw [← crcByteTable_mkTable_eq_crcByte _ b₂]
  simp only [crcByteTable]
  have hlt₂ : ((((0x00FFFFFF : UInt32) ^^^
      mkTable[0xFF ^^^ b₁.toNat]'(by exact xor_ff_byte_lt_mkTable_size b₁) ^^^
      UInt32.ofNat b₂.toNat) &&& 0xFF).toNat) < mkTable.size := by
    rw [mkTable_size]; exact and_0xFF_toNat_lt _
  rw [dif_pos hlt₂]

end Crc32.Spec
