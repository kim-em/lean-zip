/-
  LSB-first bit packer for DEFLATE streams.

  DEFLATE (RFC 1951) packs bits LSB-first within each byte.
  This module provides a stateful writer that accumulates bits
  into a partial byte, flushing complete bytes to a ByteArray.
-/
namespace Zip.Native

structure BitWriter where
  data : ByteArray
  bitBuf : UInt8    -- partial byte being assembled
  bitCount : UInt8  -- bits used in bitBuf (0-7)

namespace BitWriter

def empty : BitWriter := ⟨.empty, 0, 0⟩

/-- Write `n` bits (n ≤ 25) from `val`, LSB first.
    Fixed-width fields in DEFLATE are packed LSB-first. -/
def writeBits (bw : BitWriter) (n : Nat) (val : UInt32) : BitWriter :=
  go bw 0 n val
where
  go (bw : BitWriter) (i : Nat) (n : Nat) (val : UInt32) : BitWriter :=
    if i ≥ n then bw
    else
      let bit := ((val >>> i.toUInt32) &&& 1).toUInt8
      let bw' := { bw with bitBuf := bw.bitBuf ||| (bit <<< bw.bitCount) }
      if bw'.bitCount + 1 ≥ 8 then
        go { data := bw'.data.push bw'.bitBuf, bitBuf := 0, bitCount := 0 } (i + 1) n val
      else
        go { bw' with bitCount := bw'.bitCount + 1 } (i + 1) n val
  termination_by n - i

/-- Write a Huffman code of `len` bits. Huffman codes in DEFLATE are
    packed MSB-first (RFC 1951 §3.1.1), so we reverse the bit order. -/
def writeHuffCode (bw : BitWriter) (code : UInt16) (len : UInt8) : BitWriter :=
  go bw len.toNat code
where
  go (bw : BitWriter) : Nat → UInt16 → BitWriter
    | 0, _ => bw
    | n + 1, code =>
      let bit := ((code >>> n.toUInt16) &&& 1).toUInt8
      let bw' := { bw with bitBuf := bw.bitBuf ||| (bit <<< bw.bitCount) }
      if bw'.bitCount.toNat + 1 ≥ 8 then
        go { data := bw'.data.push bw'.bitBuf, bitBuf := 0, bitCount := 0 } n code
      else
        go { bw' with bitCount := bw'.bitCount + 1 } n code

/-- Flush any partial byte (pad with zeros). Returns the final ByteArray. -/
def flush (bw : BitWriter) : ByteArray :=
  if bw.bitCount > 0 then bw.data.push bw.bitBuf
  else bw.data

end BitWriter
end Zip.Native
