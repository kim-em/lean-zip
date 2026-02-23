/-
  Pure Lean DEFLATE compressor.

  Currently implements only Level 0 (stored blocks), which emits
  uncompressed data in DEFLATE-valid stored blocks (RFC 1951 §3.2.4).
-/

namespace Zip.Native.Deflate

/-- Maximum data bytes per stored block (2^16 - 1). -/
private def maxBlockSize : Nat := 65535

/-- Compress data into raw DEFLATE stored blocks (level 0).
    Splits into blocks of at most 65535 bytes. Each block has:
    - 1 byte: BFINAL (bit 0) | BTYPE=00 (bits 1-2), rest zero
    - 2 bytes LE: LEN (number of data bytes)
    - 2 bytes LE: NLEN (one's complement of LEN)
    - LEN bytes: raw data

    Empty input produces one final stored block with LEN=0. -/
def deflateStored (data : ByteArray) : ByteArray := Id.run do
  let mut result := ByteArray.empty
  if data.size == 0 then
    -- Empty: one final stored block with LEN=0
    result := result.push 0x01  -- BFINAL=1, BTYPE=00
    result := result.push 0x00  -- LEN low
    result := result.push 0x00  -- LEN high
    result := result.push 0xFF  -- NLEN low
    result := result.push 0xFF  -- NLEN high
    return result
  let mut pos := 0
  while pos < data.size do
    let remaining := data.size - pos
    let blockSize := min remaining maxBlockSize
    let isFinal := pos + blockSize >= data.size
    -- Header byte: BFINAL (bit 0), BTYPE=00 (bits 1-2)
    result := result.push (if isFinal then 0x01 else 0x00)
    -- LEN (16-bit LE)
    let len := blockSize.toUInt16
    result := result.push (len &&& 0xFF).toUInt8
    result := result.push ((len >>> 8) &&& 0xFF).toUInt8
    -- NLEN (one's complement of LEN, 16-bit LE)
    let nlen := len ^^^ 0xFFFF
    result := result.push (nlen &&& 0xFF).toUInt8
    result := result.push ((nlen >>> 8) &&& 0xFF).toUInt8
    -- Raw data
    result := result ++ data.extract pos (pos + blockSize)
    pos := pos + blockSize
  return result

end Zip.Native.Deflate
