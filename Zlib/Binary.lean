namespace Binary

-- Little-endian integer read/write (used by ZIP)

def readUInt16LE (data : ByteArray) (offset : Nat) : UInt16 :=
  let b0 := data[offset]!
  let b1 := data[offset + 1]!
  b0.toUInt16 ||| (b1.toUInt16 <<< 8)

def readUInt32LE (data : ByteArray) (offset : Nat) : UInt32 :=
  let b0 := data[offset]!
  let b1 := data[offset + 1]!
  let b2 := data[offset + 2]!
  let b3 := data[offset + 3]!
  b0.toUInt32 ||| (b1.toUInt32 <<< 8) ||| (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24)

def writeUInt16LE (val : UInt16) : ByteArray :=
  .mk #[val.toUInt8, (val >>> 8).toUInt8]

def writeUInt32LE (val : UInt32) : ByteArray :=
  .mk #[val.toUInt8, (val >>> 8).toUInt8, (val >>> 16).toUInt8, (val >>> 24).toUInt8]

def readUInt64LE (data : ByteArray) (offset : Nat) : UInt64 :=
  let lo := (readUInt32LE data offset).toUInt64
  let hi := (readUInt32LE data (offset + 4)).toUInt64
  lo ||| (hi <<< 32)

def writeUInt64LE (val : UInt64) : ByteArray :=
  writeUInt32LE val.toUInt32 ++ writeUInt32LE (val >>> 32).toUInt32

-- Octal ASCII read/write (used by Tar)

/-- Write a number as NUL-terminated octal ASCII, right-aligned in a field of `width` bytes.
    E.g. `writeOctal 1234 12` produces `"00000002322\0"` (11 octal digits + NUL). -/
@[noinline] def writeOctal (val : UInt64) (width : Nat) : ByteArray := Id.run do
  let digits := width - 1  -- leave room for NUL terminator
  -- Extract octal digits (least significant first)
  let mut v := val.toNat
  let mut buf : Array UInt8 := #[]
  if v == 0 then
    buf := buf.push '0'.toNat.toUInt8
  else
    while v > 0 do
      buf := buf.push (('0'.toNat + v % 8).toUInt8)
      v := v / 8
  -- Truncate to fit field: if more digits than available, keep only the
  -- least significant `digits` octal digits (this prevents buffer overrun)
  if buf.size > digits then
    buf := buf.extract 0 digits
  -- Build result: leading '0's + digits in reverse + NUL
  let mut result := ByteArray.empty
  for _ in [:digits - buf.size] do
    result := result.push '0'.toNat.toUInt8
  for i in [:buf.size] do
    result := result.push buf[buf.size - 1 - i]!
  result := result.push 0
  return result

/-- Read an octal ASCII number from a byte array field. Stops at NUL or space. -/
@[noinline] def readOctal (data : ByteArray) (offset : Nat) (len : Nat) : UInt64 := Id.run do
  let mut result : UInt64 := 0
  for i in [:len] do
    let b := data[offset + i]!
    if b == 0 || b == ' '.toNat.toUInt8 then break
    if b >= '0'.toNat.toUInt8 && b <= '7'.toNat.toUInt8 then
      result := result * 8 + (b - '0'.toNat.toUInt8).toUInt64
  return result

-- NUL-padded string read/write (used by Tar)

/-- Write a string NUL-padded to exactly `width` bytes. -/
@[noinline] def writeString (s : String) (width : Nat) : ByteArray := Id.run do
  let utf8 := s.toUTF8
  let mut result := ByteArray.empty
  let toCopy := min utf8.size width
  for i in [:toCopy] do
    result := result.push utf8[i]!
  for _ in [:width - toCopy] do
    result := result.push 0
  return result

/-- Read a NUL-terminated string from a byte array field. -/
@[noinline] def readString (data : ByteArray) (offset : Nat) (len : Nat) : String := Id.run do
  let mut bytes := ByteArray.empty
  for i in [:len] do
    let b := data[offset + i]!
    if b == 0 then break
    bytes := bytes.push b
  return String.fromUTF8! bytes

/-- Create a ByteArray of `n` zero bytes. -/
@[noinline] def zeros (n : Nat) : ByteArray := Id.run do
  let mut result := ByteArray.empty
  for _ in [:n] do
    result := result.push 0
  return result

end Binary
