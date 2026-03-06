import Zip.Binary

/-!
# Native Lean XXH64 Implementation

Pure Lean implementation of the XXH64 hash function (64-bit variant of xxHash
by Yann Collet). Used by Zstandard (RFC 8878) for optional content checksums:
the upper 32 bits of `xxHash64 data 0` are stored as a 32-bit checksum at the
end of each Zstd frame that has the `Content_Checksum` flag set.

Reference: https://github.com/Cyan4973/xxHash/blob/dev/doc/xxhash_spec.md
-/

namespace XxHash64

/-- XXH64 prime constants. -/
def PRIME64_1 : UInt64 := 0x9E3779B185EBCA87
def PRIME64_2 : UInt64 := 0xC2B2AE3D27D4EB4F
def PRIME64_3 : UInt64 := 0x165667B19E3779F9
def PRIME64_4 : UInt64 := 0x85EBCA77C2B2AE63
def PRIME64_5 : UInt64 := 0x27D4EB2F165667C5

/-- Rotate left for UInt64. -/
@[inline] def rotl (v : UInt64) (n : UInt64) : UInt64 :=
  (v <<< n) ||| (v >>> (64 - n))

/-- Single accumulator round: mix an 8-byte lane into an accumulator. -/
@[inline] def round (acc lane : UInt64) : UInt64 :=
  let acc := acc + lane * PRIME64_2
  let acc := rotl acc 31
  acc * PRIME64_1

/-- Merge an accumulator value into the convergence hash. -/
@[inline] def mergeAccumulator (acc accN : UInt64) : UInt64 :=
  let acc := acc ^^^ round 0 accN
  let acc := acc * PRIME64_1
  acc + PRIME64_4

/-- Read a little-endian UInt64 from a ByteArray at the given offset. -/
@[inline] def readU64LE (data : ByteArray) (off : Nat) : UInt64 :=
  Binary.readUInt64LE data off

/-- Read a little-endian UInt32 from a ByteArray at the given offset, as UInt64. -/
@[inline] def readU32LE (data : ByteArray) (off : Nat) : UInt64 :=
  (Binary.readUInt32LE data off).toUInt64

/-- Final avalanche mixing. -/
@[inline] def avalanche (h : UInt64) : UInt64 :=
  let h := h ^^^ (h >>> 33)
  let h := h * PRIME64_2
  let h := h ^^^ (h >>> 29)
  let h := h * PRIME64_3
  h ^^^ (h >>> 32)

/-- Process remaining 8-byte chunks. -/
def processRemaining8 (h : UInt64) (data : ByteArray) (pos endPos : Nat) : UInt64 × Nat :=
  if pos + 8 ≤ endPos then
    let lane := readU64LE data pos
    let h := h ^^^ round 0 lane
    let h := rotl h 27 * PRIME64_1 + PRIME64_4
    processRemaining8 h data (pos + 8) endPos
  else
    (h, pos)
termination_by endPos - pos

/-- Process remaining 1-byte chunks. -/
def processRemaining1 (h : UInt64) (data : ByteArray) (pos endPos : Nat) : UInt64 :=
  if pos < endPos then
    let lane := data[pos]!.toUInt64
    let h := h ^^^ (lane * PRIME64_5)
    let h := rotl h 11 * PRIME64_1
    processRemaining1 h data (pos + 1) endPos
  else
    h
termination_by endPos - pos

/-- Process remaining bytes after full 32-byte stripes.
    Handles 8-byte, 4-byte, and 1-byte chunks. -/
def processRemaining (acc : UInt64) (data : ByteArray) (off len : Nat) : UInt64 :=
  let endPos := off + len
  let (h, pos) := processRemaining8 acc data off endPos
  let (h, pos) :=
    if pos + 4 ≤ endPos then
      let lane := readU32LE data pos
      let h := h ^^^ (lane * PRIME64_1)
      let h := rotl h 23 * PRIME64_2 + PRIME64_3
      (h, pos + 4)
    else
      (h, pos)
  processRemaining1 h data pos endPos

/-- Compute XXH64 hash of a `ByteArray` with the given seed.
    Follows the xxHash specification exactly:
    1. Initialize accumulators (4 × 64-bit for inputs ≥ 32 bytes)
    2. Process 32-byte stripes
    3. Converge accumulators
    4. Add total length
    5. Process remaining bytes
    6. Final avalanche -/
def xxHash64 (data : ByteArray) (seed : UInt64 := 0) : UInt64 :=
  let len := data.size
  let h :=
    if len < 32 then
      seed + PRIME64_5
    else Id.run do
      let mut acc1 := seed + PRIME64_1 + PRIME64_2
      let mut acc2 := seed + PRIME64_2
      let mut acc3 := seed
      let mut acc4 := seed - PRIME64_1
      let stripeEnd := len / 32 * 32
      let mut pos := 0
      while pos < stripeEnd do
        acc1 := round acc1 (readU64LE data pos)
        acc2 := round acc2 (readU64LE data (pos + 8))
        acc3 := round acc3 (readU64LE data (pos + 16))
        acc4 := round acc4 (readU64LE data (pos + 24))
        pos := pos + 32
      let h := rotl acc1 1 + rotl acc2 7 + rotl acc3 12 + rotl acc4 18
      let h := mergeAccumulator h acc1
      let h := mergeAccumulator h acc2
      let h := mergeAccumulator h acc3
      return mergeAccumulator h acc4
  let h := h + len.toUInt64
  let remaining := len % 32
  let h := processRemaining h data (len - remaining) remaining
  avalanche h

/-- Compute the upper 32 bits of XXH64 with seed 0.
    This is the checksum format used by Zstandard (RFC 8878 §3.1.1). -/
def xxHash64Upper32 (data : ByteArray) : UInt32 :=
  (xxHash64 data 0 >>> 32).toUInt32

end XxHash64
