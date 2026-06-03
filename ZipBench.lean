import Zip
import Zip.Native.InflateBuf
/-! Benchmark driver for hyperfine.

Usage:
  lake exe bench <operation> <size> <pattern> [level]

Operations:
  inflate        — native DEFLATE decompression
  inflate-ffi    — zlib FFI decompression
  inflate-miniz  — miniz_oxide (Rust) DEFLATE decompression (Track D)
  deflate        — native DEFLATE compression (fixed Huffman)
  deflate-lazy   — native DEFLATE compression (lazy matching)
  deflate-ffi    — zlib FFI compression
  compress-miniz — miniz_oxide (Rust) DEFLATE compression (Track D)
  gzip           — native gzip decompression
  gzip-ffi       — zlib FFI gzip decompression
  zlib           — native zlib decompression
  zlib-ffi       — zlib FFI zlib decompression
  crc32          — native CRC-32
  crc32-ffi      — zlib FFI CRC-32
  adler32        — native Adler-32
  adler32-ffi    — zlib FFI Adler-32

Patterns:   constant, cyclic, prng, text
Level:      0-9 (default 6, only for compression/inflate)

Examples:
  hyperfine 'lake exe bench inflate 1048576 prng 6'
  hyperfine '.lake/build/bin/bench inflate 10485760 prng 6' \
            '.lake/build/bin/bench inflate-ffi 10485760 prng 6'
  hyperfine --parameter-list size 1024,65536,1048576 \
            '.lake/build/bin/bench inflate {size} prng 6'
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

/-- Pseudo-text payload (cycled common English words wrapped to ~72 cols).
    Mirrors `ZipTest.Helpers.mkTextData` so bench measurements match the
    Track D ratio-vs-zopfli setup. -/
def mkTextData (size : Nat) : ByteArray := Id.run do
  let words := #["the", "of", "and", "to", "in", "a", "is", "that", "for", "it",
                  "was", "on", "are", "be", "with", "as", "at", "this", "have", "from",
                  "or", "by", "not", "but", "what", "all", "were", "when", "we", "there",
                  "can", "an", "your", "which", "their", "if", "do", "will", "each", "how"]
  let mut result := ByteArray.empty
  let mut col : Nat := 0
  let mut wi : Nat := 0
  while result.size < size do
    let word := words[wi % words.size]!
    wi := wi + 1
    if col > 0 then
      if col + 1 + word.length > 72 then
        result := result.push 0x0A  -- newline
        col := 0
      else
        result := result.push 0x20  -- space
        col := col + 1
    for c in word.toUTF8 do
      if result.size < size then
        result := result.push c
    col := col + word.length
  return result.extract 0 size

def generateData (pattern : String) (size : Nat) : IO ByteArray :=
  match pattern with
  | "constant" => pure (mkConstantData size)
  | "cyclic"   => pure (mkCyclicData size)
  | "prng"     => pure (mkPrngData size)
  | "text"     => pure (mkTextData size)
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
    "usage: bench <operation> <size> <constant|cyclic|prng|text> [level]")
  run (op sizeStr pattern : String) (level : Nat) : IO Unit := do
    let some size := sizeStr.toNat? | usage
    let data ← generateData pattern size
    match op with
    -- Decompression benchmarks (compress with FFI first, then decompress)
    | "inflate" =>
      let compressed ← RawDeflate.compress data level.toUInt8
      match Zip.Native.Inflate.inflate compressed with
      | .ok _ => pure ()
      | .error e => throw (IO.userError e)
    | "inflate-buf" =>
      let compressed ← RawDeflate.compress data level.toUInt8
      match Zip.Native.InflateBuf.inflate compressed with
      | .ok _ => pure ()
      | .error e => throw (IO.userError e)
    | "decode-ab" =>
      -- Build DISTINCT compressed inputs (perturb one byte per rep, on a COPY so
      -- shared `data` is never mutated) to defeat hoisting/memoisation.
      let nin := 16
      let mut inputs : Array ByteArray := #[]
      for i in [0:nin] do
        let d := if data.size == 0 then data else
          (data.extract 0 data.size).set! (i % data.size) (data[i % data.size]!.toNat.toUInt8 ^^^ 1)
        inputs := inputs.push (← RawDeflate.compress d level.toUInt8)
      let dec1 := Zip.Native.Inflate.inflate
      let dec2 := Zip.Native.InflateBuf.inflate
      let sink (acc : UInt64) (r : Except String ByteArray) : IO UInt64 :=
        match r with
        | .ok x => pure (acc + x.size.toUInt64 + (if x.size > 0 then x[0]!.toUInt64 else 0))
        | .error e => throw (IO.userError e)
      -- warm
      let mut w : UInt64 := 0
      for _ in [0:3] do for c in inputs do w ← sink w (dec1 c); w ← sink w (dec2 c)
      if w == 0xFFFFFFFFFFFFFFFF then IO.println "x"
      -- Interleave ref/buf at single-decode granularity, alternating order by round
      -- parity, summing each side's nanos. Fine-grained alternation cancels drift.
      let rounds := 80
      let mut refTot : Nat := 0
      let mut bufTot : Nat := 0
      let mut acc : UInt64 := 0
      for round in [0:rounds] do
        for c in inputs do
          if round % 2 == 0 then
            let a ← IO.monoNanosNow
            acc ← sink acc (dec1 c)
            let b ← IO.monoNanosNow
            acc ← sink acc (dec2 c)
            let e ← IO.monoNanosNow
            refTot := refTot + (b - a); bufTot := bufTot + (e - b)
          else
            let a ← IO.monoNanosNow
            acc ← sink acc (dec2 c)
            let b ← IO.monoNanosNow
            acc ← sink acc (dec1 c)
            let e ← IO.monoNanosNow
            bufTot := bufTot + (b - a); refTot := refTot + (e - b)
      if acc == 0xFFFFFFFFFFFFFFFF then IO.println "x"
      let n := (rounds * nin).toFloat
      let mbps (tot : Nat) : Float := (data.size.toFloat * n) / (tot.toFloat / 1.0e9) / 1.0e6
      IO.println s!"size={data.size} {pattern} lvl={level}: ref={mbps refTot |>.toString.take 7} MB/s  buf={mbps bufTot |>.toString.take 7} MB/s  speedup={(refTot.toFloat/bufTot.toFloat).toString.take 5}x"
    | "inflate-buf-check" =>
      let compressed ← RawDeflate.compress data level.toUInt8
      let a := Zip.Native.Inflate.inflate compressed
      let b := Zip.Native.InflateBuf.inflate compressed
      match a, b with
      | .ok x, .ok y =>
        if x == y && x == data then IO.println s!"OK size={data.size} lvl={level}"
        else throw (IO.userError s!"MISMATCH buf.size={y.size} ref.size={x.size} orig={data.size}")
      | .error e, _ => throw (IO.userError s!"ref inflate failed: {e}")
      | _, .error e => throw (IO.userError s!"buf inflate failed: {e}")
    | "inflate-ffi" =>
      let compressed ← RawDeflate.compress data level.toUInt8
      let _ ← RawDeflate.decompress compressed
      pure ()
    | "inflate-miniz" =>
      let compressed ← RawDeflate.compress data level.toUInt8
      let _ ← MinizOxide.decompress compressed
      pure ()
    | "gzip" =>
      let compressed ← Gzip.compress data level.toUInt8
      match Zip.Native.GzipDecode.decompress compressed with
      | .ok _ => pure ()
      | .error e => throw (IO.userError e)
    | "gzip-ffi" =>
      let compressed ← Gzip.compress data level.toUInt8
      let _ ← Gzip.decompress compressed
      pure ()
    | "zlib" =>
      let compressed ← Zlib.compress data level.toUInt8
      match Zip.Native.ZlibDecode.decompress compressed with
      | .ok _ => pure ()
      | .error e => throw (IO.userError e)
    | "zlib-ffi" =>
      let compressed ← Zlib.compress data level.toUInt8
      let _ ← Zlib.decompress compressed
      pure ()
    -- Compression benchmarks
    | "deflate" =>
      let _ := Zip.Native.Deflate.deflateFixed data
      pure ()
    | "deflate-lazy" =>
      let _ := Zip.Native.Deflate.deflateLazy data
      pure ()
    | "deflate-ffi" =>
      let _ ← RawDeflate.compress data level.toUInt8
      pure ()
    | "compress-miniz" =>
      let _ ← MinizOxide.compress data level.toUInt8
      pure ()
    -- Checksum benchmarks
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
