import Zip.Binary

/-!
  Pure Lean parser for Zstandard frame headers (RFC 8878 §3.1.1).

  Parses the fixed-format header at the start of every Zstd frame:
  magic number, frame header descriptor (bit fields), optional window
  descriptor, optional dictionary ID, and optional frame content size.
  This is the foundation for native Zstd decompression.
-/

namespace Zip.Native

/-- Parsed Zstandard frame header. -/
structure ZstdFrameHeader where
  /-- Whether the frame includes a 32-bit content checksum at the end. -/
  contentChecksum : Bool
  /-- Whether the window descriptor is absent (content fits in one segment). -/
  singleSegment : Bool
  /-- Optional dictionary ID used for compression. -/
  dictionaryId : Option UInt32
  /-- Optional uncompressed content size in bytes. -/
  contentSize : Option UInt64
  /-- Window size in bytes (from window descriptor, or content size if single segment). -/
  windowSize : UInt64
  deriving Repr

/-- Zstd magic number: 0xFD2FB528 (little-endian). -/
def zstdMagic : UInt32 := 0xFD2FB528

/-- Compute window size from a Zstd window descriptor byte (RFC 8878 §3.1.1.1.2). -/
def windowSizeFromDescriptor (winDesc : UInt8) : UInt64 :=
  let exponent := (winDesc >>> 3).toNat   -- bits 7-3
  let mantissa := (winDesc &&& 7).toNat   -- bits 2-0
  let windowLog := 10 + exponent
  let windowBase : UInt64 := 1 <<< windowLog.toUInt64
  let windowAdd := (windowBase / 8) * mantissa.toUInt64
  windowBase + windowAdd

/-- Parse a Zstandard frame header starting at `pos` in `data`.
    Returns the parsed header and the position immediately after the header.
    Fails with a descriptive error message if the data is malformed or too short. -/
def parseFrameHeader (data : ByteArray) (pos : Nat) :
    Except String (ZstdFrameHeader × Nat) := do
  -- Magic number (4 bytes)
  if data.size < pos + 4 then
    throw "Zstd: not enough data for magic number"
  let magic := Binary.readUInt32LE data pos
  if magic != zstdMagic then
    throw s!"Zstd: invalid magic number 0x{String.ofList (Nat.toDigits 16 magic.toNat)} (expected 0xFD2FB528)"
  let mut off := pos + 4

  -- Frame_Header_Descriptor (1 byte)
  if data.size < off + 1 then
    throw "Zstd: not enough data for frame header descriptor"
  let desc := data[off]!
  off := off + 1

  let fcsFlag := (desc >>> 6).toNat       -- bits 7-6: Frame_Content_Size_Flag
  let singleSegment := (desc >>> 5) &&& 1 == 1  -- bit 5
  let contentChecksum := (desc >>> 2) &&& 1 == 1 -- bit 2
  let didFlag := (desc &&& 3).toNat       -- bits 1-0: Dictionary_ID_Flag

  -- Window_Descriptor (1 byte, absent if Single_Segment_Flag is set)
  let mut windowSize : UInt64 := 0
  if !singleSegment then
    if data.size < off + 1 then
      throw "Zstd: not enough data for window descriptor"
    windowSize := windowSizeFromDescriptor data[off]!
    off := off + 1

  -- Dictionary_ID (0/1/2/4 bytes)
  let didSize := match didFlag with
    | 1 => 1
    | 2 => 2
    | 3 => 4
    | _ => 0
  if data.size < off + didSize then
    throw "Zstd: not enough data for dictionary ID"
  let dictionaryId : Option UInt32 :=
    match didSize with
    | 1 => some data[off]!.toUInt32
    | 2 => some (Binary.readUInt16LE data off).toUInt32
    | 4 => some (Binary.readUInt32LE data off)
    | _ => none
  off := off + didSize

  -- Frame_Content_Size (0/1/2/4/8 bytes)
  let fcsSize := match fcsFlag with
    | 0 => if singleSegment then 1 else 0
    | 1 => 2
    | 2 => 4
    | _ => 8  -- fcsFlag == 3
  if data.size < off + fcsSize then
    throw "Zstd: not enough data for frame content size"
  let contentSize : Option UInt64 :=
    match fcsSize with
    | 1 => some data[off]!.toUInt64
    | 2 =>
      -- 2-byte FCS has a +256 offset (RFC 8878 §3.1.1.4)
      some ((Binary.readUInt16LE data off).toUInt64 + 256)
    | 4 => some (Binary.readUInt32LE data off).toUInt64
    | 8 => some (Binary.readUInt64LE data off)
    | _ => none
  off := off + fcsSize

  -- If single segment, window size equals content size
  if singleSegment then
    windowSize := contentSize.getD 0

  return ({
    contentChecksum
    singleSegment
    dictionaryId
    contentSize
    windowSize
  }, off)

end Zip.Native
