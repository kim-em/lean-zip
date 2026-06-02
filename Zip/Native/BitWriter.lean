/-!
  LSB-first bit packer for DEFLATE streams.

  DEFLATE (RFC 1951) packs bits LSB-first within each byte.
  This module provides a stateful writer that accumulates bits
  into a partial byte, flushing complete bytes to a ByteArray.

  Fields are packed in bulk: a whole `writeBits`/`writeHuffCode` field is
  merged into a wide (`UInt64`) accumulator in one shift/OR, then whole bytes
  are flushed in a short inner loop (`flushAcc`). This is byte-identical to a
  bit-by-bit packer but avoids one loop iteration and one `ByteArray.push` per
  bit — the dominant cost when emitting millions of literals.
-/
namespace Zip.Native

structure BitWriter where
  data : ByteArray
  bitBuf : UInt8    -- partial byte being assembled
  bitCount : UInt8  -- bits used in bitBuf (0-7)

namespace BitWriter

def empty : BitWriter := ⟨.empty, 0, 0⟩

/-- Flush whole bytes out of a wide accumulator `acc` holding `total` valid
    low bits, LSB-first. Pushes `total / 8` bytes to `data`; the remaining
    `total % 8` bits become the new partial byte. -/
/-- Total number of bits written so far: 8 per fully flushed byte in `data`
    plus the `bitCount` bits held in the partial byte. Used by the DEFLATE
    compressor to size a block (`⌈bitLength/8⌉` bytes after `flush`) without
    materialising it. -/
def bitLength (bw : BitWriter) : Nat := bw.data.size * 8 + bw.bitCount.toNat

def flushAcc (data : ByteArray) (acc : UInt64) : Nat → BitWriter
  | total =>
    if total ≥ 8 then
      flushAcc (data.push acc.toUInt8) (acc >>> 8) (total - 8)
    else
      ⟨data, acc.toUInt8, total.toUInt8⟩
  termination_by total => total

/-- Write `n` bits (n ≤ 25) from `val`, LSB first.
    Fixed-width fields in DEFLATE are packed LSB-first.

    The low `n` bits of `val` are masked, shifted above the `bitCount`
    bits already in `bitBuf`, OR-ed into a 64-bit accumulator, then whole
    bytes are flushed. -/
def writeBits (bw : BitWriter) (n : Nat) (val : UInt32) : BitWriter :=
  let masked : UInt64 := val.toUInt64 % (1 <<< n.toUInt64)
  let acc : UInt64 := bw.bitBuf.toUInt64 ||| (masked <<< bw.bitCount.toUInt64)
  flushAcc bw.data acc (bw.bitCount.toNat + n)

/-- Reverse all 16 bits of `x` (`bit i ↦ bit (15-i)`) with a branchless
    swap network — no per-bit loop. -/
def reverse16 (x : UInt16) : UInt16 :=
  let x := ((x &&& 0x5555) <<< 1) ||| ((x &&& 0xaaaa) >>> 1)
  let x := ((x &&& 0x3333) <<< 2) ||| ((x &&& 0xcccc) >>> 2)
  let x := ((x &&& 0x0f0f) <<< 4) ||| ((x &&& 0xf0f0) >>> 4)
  ((x &&& 0x00ff) <<< 8) ||| ((x &&& 0xff00) >>> 8)

/-- Write a Huffman code of `len` bits. Huffman codes in DEFLATE are
    packed MSB-first (RFC 1951 §3.1.1) but bytes are filled LSB-first, so the
    code's low `len` bits must be reversed before the LSB-first batch pack.

    The reversal is done in one shot: reverse all 16 bits, then shift the
    reversed code down by `16 - len` so its low `len` bits hold the code in
    packing order. (Widening to `UInt64` before the down-shift makes `len = 0`
    yield `0` correctly, since `>>> 16` clears a 16-bit value.) -/
def writeHuffCode (bw : BitWriter) (code : UInt16) (len : UInt8) : BitWriter :=
  let rev : UInt64 := (reverse16 code).toUInt64 >>> (16 - len.toUInt64)
  let acc : UInt64 := bw.bitBuf.toUInt64 ||| (rev <<< bw.bitCount.toUInt64)
  flushAcc bw.data acc (bw.bitCount.toNat + len.toNat)

/-- Flush any partial byte (pad with zeros). Returns the final ByteArray. -/
def flush (bw : BitWriter) : ByteArray :=
  if bw.bitCount > 0 then bw.data.push bw.bitBuf
  else bw.data

end BitWriter
end Zip.Native
