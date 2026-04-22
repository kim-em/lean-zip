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

end Crc32.Spec
