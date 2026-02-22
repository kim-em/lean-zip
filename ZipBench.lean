import Zip
/-! Benchmark driver for hyperfine.

Usage:
  lake exe bench <operation> <size> <pattern> [level]

Operations: inflate, gzip, zlib, crc32, adler32
Patterns:   constant, cyclic, prng
Level:      0-9 (default 6, only for inflate/gzip/zlib)

Examples:
  hyperfine 'lake exe bench inflate 1048576 prng 6'
  hyperfine 'lake exe bench crc32 1048576 constant'
  hyperfine --parameter-list size 1024,65536,1048576 \
            'lake exe bench inflate {size} prng 6'
-/

def mkConstantData (size : Nat) : ByteArray := Id.run do
  let mut result := ByteArray.empty
  for _ in [:size] do
    result := result.push 0x42
  return result

def mkCyclicData (size : Nat) : ByteArray := Id.run do
  let pattern : Array UInt8 := #[0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77,
                                   0x88, 0x99, 0xAA, 0xBB, 0xCC, 0xDD, 0xEE, 0xFF]
  let mut result := ByteArray.empty
  for i in [:size] do
    result := result.push pattern[i % 16]!
  return result

def mkPrngData (size : Nat) : ByteArray := Id.run do
  let mut state : UInt32 := 2463534242
  let mut result := ByteArray.empty
  for _ in [:size] do
    state := state ^^^ (state <<< 13)
    state := state ^^^ (state >>> 17)
    state := state ^^^ (state <<< 5)
    result := result.push (state &&& 0xFF).toUInt8
  return result

def generateData (pattern : String) (size : Nat) : IO ByteArray :=
  match pattern with
  | "constant" => pure (mkConstantData size)
  | "cyclic"   => pure (mkCyclicData size)
  | "prng"     => pure (mkPrngData size)
  | other      => throw (IO.userError s!"unknown pattern: {other}")

def main (args : List String) : IO Unit := do
  match args with
  | [op, sizeStr, pattern] => run op sizeStr pattern 6
  | [op, sizeStr, pattern, levelStr] =>
    match levelStr.toNat? with
    | some level => run op sizeStr pattern level
    | none => usage
  | _ => usage
where
  usage := throw (IO.userError
    "usage: bench <inflate|gzip|zlib|crc32|adler32> <size> <constant|cyclic|prng> [level]")
  run (op sizeStr pattern : String) (level : Nat) : IO Unit := do
    let some size := sizeStr.toNat? | usage
    let data ← generateData pattern size
    match op with
    | "inflate" =>
      let compressed ← RawDeflate.compress data level.toUInt8
      match Zip.Native.Inflate.inflate compressed with
      | .ok _ => pure ()
      | .error e => throw (IO.userError e)
    | "gzip" =>
      let compressed ← Gzip.compress data level.toUInt8
      match Zip.Native.GzipDecode.decompress compressed with
      | .ok _ => pure ()
      | .error e => throw (IO.userError e)
    | "zlib" =>
      let compressed ← Zlib.compress data level.toUInt8
      match Zip.Native.ZlibDecode.decompress compressed with
      | .ok _ => pure ()
      | .error e => throw (IO.userError e)
    | "crc32" =>
      let _ := Crc32.Native.crc32 0 data
      pure ()
    | "crc32-ffi" =>
      let _ := Checksum.crc32 0 data
      pure ()
    | "adler32" =>
      let _ := Adler32.Native.adler32 1 data
      pure ()
    | "adler32-ffi" =>
      let _ := Checksum.adler32 1 data
      pure ()
    | other => throw (IO.userError s!"unknown operation: {other}")
