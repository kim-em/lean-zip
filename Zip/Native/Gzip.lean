/-
  Pure Lean gzip (RFC 1952) and zlib (RFC 1950) compression and decompression.

  Compression wraps native DEFLATE output with gzip/zlib framing headers,
  trailers, and checksums. Decompression parses the framing, inflates the
  DEFLATE stream, and verifies checksums.
-/
import Zip.Native.Inflate
import Zip.Native.Deflate
import Zip.Native.Crc32
import Zip.Native.Adler32
import Zip.Binary

namespace Zip.Native

namespace GzipDecode

/-- Decompress a gzip stream (RFC 1952). Supports concatenated members.
    Returns the decompressed data. -/
def decompress (data : ByteArray) (maxOutputSize : Nat := 256 * 1024 * 1024) :
    Except String ByteArray := do
  if data.size < 10 then throw "Gzip: input too short for gzip header"
  let mut pos : Nat := 0
  let mut result : ByteArray := .empty
  -- Process concatenated gzip members
  for _ in [:1000] do
    if pos ≥ data.size then return result
    -- Parse header
    if pos + 10 > data.size then throw "Gzip: truncated header"
    let id1 := data[pos]!
    let id2 := data[pos + 1]!
    unless id1 == 0x1f && id2 == 0x8b do
      if pos == 0 then throw "Gzip: invalid magic bytes"
      -- End of concatenated stream
      return result
    let cm := data[pos + 2]!
    unless cm == 8 do throw "Gzip: unsupported compression method"
    let flg := data[pos + 3]!
    -- Skip MTIME (4), XFL (1), OS (1)
    pos := pos + 10
    -- FEXTRA
    if flg &&& 0x04 != 0 then
      if pos + 2 > data.size then throw "Gzip: truncated FEXTRA length"
      let xlen := (Binary.readUInt16LE data pos).toNat
      pos := pos + 2 + xlen
    -- FNAME (null-terminated)
    if flg &&& 0x08 != 0 then
      while pos < data.size && data[pos]! != 0 do pos := pos + 1
      pos := pos + 1 -- skip NUL
    -- FCOMMENT (null-terminated)
    if flg &&& 0x10 != 0 then
      while pos < data.size && data[pos]! != 0 do pos := pos + 1
      pos := pos + 1
    -- FHCRC (2-byte header CRC)
    if flg &&& 0x02 != 0 then pos := pos + 2
    if pos > data.size then throw "Gzip: header extends past end of input"
    -- Inflate (cap each member to remaining budget so total stays within maxOutputSize)
    let memberMax := maxOutputSize - result.size
    let (decompressed, endPos) ← Inflate.inflateRaw data pos memberMax
    pos := endPos
    -- Parse trailer: CRC32 (4 bytes LE) + ISIZE (4 bytes LE)
    if pos + 8 > data.size then throw "Gzip: truncated trailer"
    let expectedCrc := Binary.readUInt32LE data pos
    let expectedSize := Binary.readUInt32LE data (pos + 4)
    pos := pos + 8
    -- Verify CRC32
    let actualCrc := Crc32.Native.crc32 0 decompressed
    unless actualCrc == expectedCrc do
      throw s!"Gzip: CRC32 mismatch: expected {expectedCrc}, got {actualCrc}"
    -- Verify size (mod 2^32)
    let actualSize := decompressed.size.toUInt32
    unless actualSize == expectedSize do
      throw s!"Gzip: size mismatch: expected {expectedSize}, got {actualSize}"
    result := result ++ decompressed
    if result.size > maxOutputSize then
      throw "Gzip: total output exceeds maximum size"
  throw "Gzip: too many concatenated members"

end GzipDecode

namespace GzipEncode

/-- Compress data to gzip format (RFC 1952).
    Uses DEFLATE level 0 (stored), 1 (greedy LZ77), or 2+ (lazy LZ77). -/
def compress (data : ByteArray) (level : UInt8 := 1) : ByteArray :=
  let deflated := if level == 0 then
    Deflate.deflateStored data
  else if level == 1 then
    Deflate.deflateFixed data
  else
    Deflate.deflateLazy data
  -- Gzip header: ID1=0x1f, ID2=0x8b, CM=8, FLG=0, MTIME=0, XFL, OS=255
  let xfl : UInt8 := if level == 0 then 0x00 else 0x04
  let header := ByteArray.mk #[0x1f, 0x8b, 8, 0, 0, 0, 0, 0, xfl, 0xFF]
  -- CRC32 of uncompressed data (4 bytes LE)
  let crc := Crc32.Native.crc32 0 data
  -- ISIZE: original size mod 2^32 (4 bytes LE)
  let isize := data.size.toUInt32
  let trailer := ByteArray.mk #[
    (crc &&& 0xFF).toUInt8, ((crc >>> 8) &&& 0xFF).toUInt8,
    ((crc >>> 16) &&& 0xFF).toUInt8, ((crc >>> 24) &&& 0xFF).toUInt8,
    (isize &&& 0xFF).toUInt8, ((isize >>> 8) &&& 0xFF).toUInt8,
    ((isize >>> 16) &&& 0xFF).toUInt8, ((isize >>> 24) &&& 0xFF).toUInt8
  ]
  header ++ deflated ++ trailer

end GzipEncode

namespace ZlibDecode

/-- Decompress a zlib stream (RFC 1950).
    Returns the decompressed data. -/
def decompress (data : ByteArray) (maxOutputSize : Nat := 256 * 1024 * 1024) :
    Except String ByteArray := do
  if data.size < 6 then throw "Zlib: input too short"
  -- Parse header: CMF (1 byte) + FLG (1 byte)
  let cmf := data[0]!
  let flg := data[1]!
  -- Check header checksum
  let check := cmf.toUInt16 * 256 + flg.toUInt16
  unless check % 31 == 0 do throw "Zlib: header check failed"
  -- CM must be 8 (deflate)
  unless cmf &&& 0x0F == 8 do throw "Zlib: unsupported compression method"
  -- CINFO (window size) must be ≤ 7
  let cinfo := cmf >>> 4
  unless cinfo ≤ 7 do throw s!"Zlib: invalid window size {cinfo}"
  let mut pos : Nat := 2
  -- FDICT: preset dictionary (not supported)
  if flg &&& 0x20 != 0 then
    throw "Zlib: preset dictionaries not supported"
  -- Inflate
  let (decompressed, endPos) ← Inflate.inflateRaw data pos maxOutputSize
  pos := endPos
  -- Parse trailer: Adler32 (4 bytes big-endian)
  if pos + 4 > data.size then throw "Zlib: truncated trailer"
  let b0 := data[pos]!.toUInt32
  let b1 := data[pos + 1]!.toUInt32
  let b2 := data[pos + 2]!.toUInt32
  let b3 := data[pos + 3]!.toUInt32
  let expectedAdler := (b0 <<< 24) ||| (b1 <<< 16) ||| (b2 <<< 8) ||| b3
  -- Verify Adler32
  let actualAdler := Adler32.Native.adler32 1 decompressed
  unless actualAdler == expectedAdler do
    throw s!"Zlib: Adler32 mismatch: expected {expectedAdler}, got {actualAdler}"
  return decompressed

end ZlibDecode

namespace ZlibEncode

/-- Compress data to zlib format (RFC 1950).
    Uses DEFLATE level 0 (stored), 1 (greedy LZ77), or 2+ (lazy LZ77). -/
def compress (data : ByteArray) (level : UInt8 := 1) : ByteArray :=
  let deflated := if level == 0 then
    Deflate.deflateStored data
  else if level == 1 then
    Deflate.deflateFixed data
  else
    Deflate.deflateLazy data
  -- CMF: CM=8 (deflate), CINFO=7 (32K window)
  let cmf : UInt8 := 0x78
  -- FLG: FLEVEL (bits 6-7) + FCHECK (bits 0-4) such that (CMF*256 + FLG) % 31 == 0
  let flevel : UInt8 := if level == 0 then 0x00 else 0x40
  let fcheck := (31 - ((cmf.toNat * 256 + flevel.toNat) % 31)) % 31
  let flg := flevel ||| fcheck.toUInt8
  let header := ByteArray.mk #[cmf, flg]
  -- Adler32 of uncompressed data (4 bytes big-endian)
  let adler := Adler32.Native.adler32 1 data
  let trailer := ByteArray.mk #[
    ((adler >>> 24) &&& 0xFF).toUInt8, ((adler >>> 16) &&& 0xFF).toUInt8,
    ((adler >>> 8) &&& 0xFF).toUInt8, (adler &&& 0xFF).toUInt8
  ]
  header ++ deflated ++ trailer

end ZlibEncode

/-- Format detected from the first bytes of a compressed stream. -/
inductive CompressFormat where
  | gzip
  | zlib
  | rawDeflate

/-- Detect the compression format from the first bytes.
    - Gzip: starts with 0x1f 0x8b
    - Zlib: first byte has CM=8 (low nibble), and header check passes
    - Raw deflate: fallback -/
def detectFormat (data : ByteArray) : CompressFormat :=
  if data.size ≥ 2 && data[0]! == 0x1f && data[1]! == 0x8b then
    .gzip
  else if data.size ≥ 2 then
    let cmf := data[0]!
    let flg := data[1]!
    let check := cmf.toUInt16 * 256 + flg.toUInt16
    if cmf &&& 0x0F == 8 && check % 31 == 0 then .zlib
    else .rawDeflate
  else
    .rawDeflate

/-- Decompress data by auto-detecting the format (gzip, zlib, or raw deflate). -/
def decompressAuto (data : ByteArray) (maxOutputSize : Nat := 256 * 1024 * 1024) :
    Except String ByteArray :=
  match detectFormat data with
  | .gzip => GzipDecode.decompress data maxOutputSize
  | .zlib => ZlibDecode.decompress data maxOutputSize
  | .rawDeflate => Inflate.inflate data maxOutputSize

/-- Compress data with format selection.
    Default: gzip format, level 1 (fixed Huffman). -/
def compressAuto (data : ByteArray)
    (format : CompressFormat := .gzip) (level : UInt8 := 1) :
    ByteArray :=
  match format with
  | .gzip => GzipEncode.compress data level
  | .zlib => ZlibEncode.compress data level
  | .rawDeflate =>
    if level == 0 then Deflate.deflateStored data
    else if level == 1 then Deflate.deflateFixed data
    else Deflate.deflateLazy data

end Zip.Native
