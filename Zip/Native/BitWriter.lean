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

/-- Total number of bits written so far: 8 per fully flushed byte in `data`
    plus the `bitCount` bits held in the partial byte. Used by the DEFLATE
    compressor to size a block (`⌈bitLength/8⌉` bytes after `flush`) without
    materialising it. -/
def bitLength (bw : BitWriter) : Nat := bw.data.size * 8 + bw.bitCount.toNat

/-- Flush whole bytes out of a wide accumulator `acc` holding `total` valid
    low bits, LSB-first. Pushes `total / 8` bytes to `data`; the remaining
    `total % 8` bits become the new partial byte.

    Reference form only: the production writers use the split
    `flushBytes`/`dropBytes` loops (equal by `flushAcc_eq`, which the
    `writeBits_def`/`writeHuffCode_def` equations build on) so the `BitWriter`
    cell is constructed in the caller, where the ctor-reuse optimization can
    recycle the input writer instead of allocating a fresh cell per field
    (measured at ~59%/~19% of `mi_malloc_small` calls on L1/L8 compress,
    #2739). -/
def flushAcc (data : ByteArray) (acc : UInt64) : Nat → BitWriter
  | total =>
    if total ≥ 8 then
      flushAcc (data.push acc.toUInt8) (acc >>> 8) (total - 8)
    else
      ⟨data, acc.toUInt8, total.toUInt8⟩
  termination_by total => total

/-- The byte-pushing half of `flushAcc`: push the low `k` whole bytes of
    `acc`, LSB-first. Returns only the grown `ByteArray` — the leftover
    partial-byte state is pure arithmetic (`dropBytes`), so the caller can
    build the result `BitWriter` itself and have ctor reuse recycle its
    input cell. -/
def flushBytes (data : ByteArray) (acc : UInt64) : Nat → ByteArray
  | 0 => data
  | k + 1 => flushBytes (data.push acc.toUInt8) (acc >>> 8) k

/-- The accumulator half of `flushAcc`: `acc` after `k` byte-sized right
    shifts (the value whose low bits become the new partial byte). Iterated
    `>>> 8` rather than `>>> (8*k)` so it agrees with `flushAcc` for *every*
    `k`, not just `8*k < 64`. -/
def dropBytes (acc : UInt64) : Nat → UInt64
  | 0 => acc
  | k + 1 => dropBytes (acc >>> 8) k

/-- `flushAcc` is the split pair `flushBytes`/`dropBytes`: the byte pushes
    and the leftover accumulator commute past each other. -/
theorem flushAcc_eq (data : ByteArray) (acc : UInt64) (total : Nat) :
    flushAcc data acc total =
      ⟨flushBytes data acc (total / 8), (dropBytes acc (total / 8)).toUInt8,
        (total % 8).toUInt8⟩ := by
  induction total using Nat.strongRecOn generalizing data acc with
  | _ total ih =>
    rw [flushAcc]
    by_cases hge : total ≥ 8
    · rw [if_pos hge, ih (total - 8) (by omega)]
      have hdiv : total / 8 = (total - 8) / 8 + 1 := by omega
      have hmod : (total - 8) % 8 = total % 8 := by omega
      rw [hdiv, hmod, flushBytes, dropBytes]
    · rw [if_neg hge]
      have h8 : total / 8 = 0 := by omega
      have hm : total % 8 = total := by omega
      rw [h8, hm, flushBytes, dropBytes]

/-- Write `n` bits (n ≤ 25) from `val`, LSB first.
    Fixed-width fields in DEFLATE are packed LSB-first.

    The low `n` bits of `val` are masked, shifted above the `bitCount`
    bits already in `bitBuf`, OR-ed into a 64-bit accumulator, then whole
    bytes are flushed. The result cell is constructed here (not in the
    flush loop) so ctor reuse updates `bw` in place — see `flushAcc`. -/
def writeBits (bw : BitWriter) (n : Nat) (val : UInt32) : BitWriter :=
  let masked : UInt64 := val.toUInt64 % (1 <<< n.toUInt64)
  let acc : UInt64 := bw.bitBuf.toUInt64 ||| (masked <<< bw.bitCount.toUInt64)
  let total := bw.bitCount.toNat + n
  ⟨flushBytes bw.data acc (total / 8), (dropBytes acc (total / 8)).toUInt8,
    (total % 8).toUInt8⟩

/-- `writeBits` is `flushAcc` of the merged accumulator — the pre-#2739
    defining equation, for the spec proofs. -/
theorem writeBits_def (bw : BitWriter) (n : Nat) (val : UInt32) :
    bw.writeBits n val =
      flushAcc bw.data
        (bw.bitBuf.toUInt64 ||| ((val.toUInt64 % (1 <<< n.toUInt64)) <<< bw.bitCount.toUInt64))
        (bw.bitCount.toNat + n) :=
  (flushAcc_eq ..).symm

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
  let total := bw.bitCount.toNat + len.toNat
  ⟨flushBytes bw.data acc (total / 8), (dropBytes acc (total / 8)).toUInt8,
    (total % 8).toUInt8⟩

/-- `writeHuffCode` is `flushAcc` of the merged accumulator — the pre-#2739
    defining equation, for the spec proofs. -/
theorem writeHuffCode_def (bw : BitWriter) (code : UInt16) (len : UInt8) :
    bw.writeHuffCode code len =
      flushAcc bw.data
        (bw.bitBuf.toUInt64 |||
          (((reverse16 code).toUInt64 >>> (16 - len.toUInt64)) <<< bw.bitCount.toUInt64))
        (bw.bitCount.toNat + len.toNat) :=
  (flushAcc_eq ..).symm

/-- Flush any partial byte (pad with zeros). Returns the final ByteArray. -/
def flush (bw : BitWriter) : ByteArray :=
  if bw.bitCount > 0 then bw.data.push bw.bitBuf
  else bw.data

end BitWriter
end Zip.Native
