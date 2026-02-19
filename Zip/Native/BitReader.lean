/-
  Bit-level reader for DEFLATE streams.

  DEFLATE (RFC 1951) packs bits LSB-first within each byte.
  This module provides a stateful reader that tracks a byte position
  and a bit offset (0–7) within the current byte.
-/
namespace Zip.Native

structure BitReader where
  data : ByteArray
  pos : Nat       -- byte position
  bitOff : Nat    -- bit offset within current byte (0 = LSB)
namespace BitReader

def ofByteArray (data : ByteArray) : BitReader :=
  { data, pos := 0, bitOff := 0 }

def remaining (br : BitReader) : Nat :=
  if br.pos < br.data.size then
    (br.data.size - br.pos) * 8 - br.bitOff
  else
    0

def isEof (br : BitReader) : Bool :=
  br.pos ≥ br.data.size

/-- Read a single bit. Returns (bit, updatedReader). -/
def readBit (br : BitReader) : Except String (UInt32 × BitReader) :=
  if br.pos ≥ br.data.size then
    .error "BitReader: unexpected end of input"
  else
    let byte := br.data[br.pos]!
    let bit : UInt32 := ((byte.toUInt32 >>> br.bitOff.toUInt32) &&& 1)
    if br.bitOff + 1 ≥ 8 then
      .ok (bit, { br with pos := br.pos + 1, bitOff := 0 })
    else
      .ok (bit, { br with bitOff := br.bitOff + 1 })

/-- Read `n` bits (n ≤ 25), LSB first. Returns the value as UInt32. -/
def readBits (br : BitReader) (n : Nat) : Except String (UInt32 × BitReader) :=
  go br 0 0 n
where
  go (br : BitReader) (acc : UInt32) (shift : Nat) : Nat → Except String (UInt32 × BitReader)
    | 0 => .ok (acc, br)
    | k + 1 => do
      let (bit, br') ← br.readBit
      go br' (acc ||| (bit <<< shift.toUInt32)) (shift + 1) k

/-- Align to the next byte boundary. Discards remaining bits in the current byte. -/
def alignToByte (br : BitReader) : BitReader :=
  if br.bitOff == 0 then br
  else { br with pos := br.pos + 1, bitOff := 0 }

/-- Read a UInt16 in little-endian from the byte-aligned position. -/
def readUInt16LE (br : BitReader) : Except String (UInt16 × BitReader) :=
  let br := br.alignToByte
  if br.pos + 2 > br.data.size then
    .error "BitReader: unexpected end of input reading UInt16"
  else
    let lo := br.data[br.pos]!.toUInt16
    let hi := br.data[br.pos + 1]!.toUInt16
    .ok (lo ||| (hi <<< 8), { br with pos := br.pos + 2 })

/-- Read `n` bytes from byte-aligned position. -/
def readBytes (br : BitReader) (n : Nat) : Except String (ByteArray × BitReader) :=
  let br := br.alignToByte
  if br.pos + n > br.data.size then
    .error "BitReader: unexpected end of input reading bytes"
  else
    .ok (br.data.extract br.pos (br.pos + n), { br with pos := br.pos + n })

end BitReader
end Zip.Native
