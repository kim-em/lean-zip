import Zip
import Zip.Native.InflateBuf
import Bench.MinizOxide
import Bench.Libdeflate
/-! Benchmark driver for hyperfine.

Usage:
  lake exe bench <operation> <size> <pattern> [level]

Operations:
  inflate        — native DEFLATE decompression
  inflate-ffi    — zlib FFI decompression
  inflate-miniz  — miniz_oxide (Rust) DEFLATE decompression (Track D)
  inflate-libdeflate — libdeflate (C) DEFLATE decompression (Track D)
  deflate        — native DEFLATE compression (fixed Huffman)
  deflate-lazy   — native DEFLATE compression (lazy matching)
  deflate-ffi    — zlib FFI compression
  compress-miniz — miniz_oxide (Rust) DEFLATE compression (Track D)
  compress-libdeflate — libdeflate (C) DEFLATE compression (Track D)
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
  -- "@<path>": read a real corpus file (size arg ignored). Synthetic generators
  -- (esp. `text`) are degenerate for matcher measurement — use real data here.
  | p          =>
    if p.startsWith "@" then IO.FS.readBinFile (p.drop 1).toString
    else throw (IO.userError s!"unknown pattern: {p}")

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
      -- The decompressed size is known here (we just compressed `data`), so pass it
      -- as `sizeHint` to pre-size the output buffer and skip the doubling reallocs.
      match Zip.Native.Inflate.inflate compressed (sizeHint := data.size) with
      | .ok _ => pure ()
      | .error e => throw (IO.userError e)
    | "inflate-buf" =>
      let compressed ← RawDeflate.compress data level.toUInt8
      match Zip.Native.InflateBuf.inflate compressed (sizeHint := data.size) with
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
      let dec1 := fun c => Zip.Native.Inflate.inflate c (sizeHint := data.size)
      let dec2 := fun c => Zip.Native.InflateBuf.inflate c (sizeHint := data.size)
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
    | "inflate-libdeflate" =>
      let compressed ← Libdeflate.compress data level.toUInt8
      let _ ← Libdeflate.decompress compressed
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
      -- Print the compressed size (mirrors the `csize` one-line format) so the
      -- whole-tar measurement (bench/whole_tar_l6.sh) can read miniz's output
      -- size while still timing this as a fresh single-shot process. This feeds
      -- the CODEC section of that measurement: run THROUGH this same lean `bench`
      -- harness, this path pays the identical `readBinFile` + big-ByteArray I/O
      -- tax that `csize` (native) pays, so that I/O cancels and the codec-CPU
      -- ratio is isolated. It is NOT the end-to-end `zip silesia.tar` wall — that
      -- is the separate `compress-file` / `miniz-compress-file` CLIs. The extra
      -- print is negligible next to compressing a 200 MB tar, so it does not
      -- perturb the cold timing the measurement records.
      let out ← MinizOxide.compress data level.toUInt8
      let ratio : Float := 100.0 * out.size.toFloat / data.size.toFloat
      IO.println s!"size={data.size} lvl={level}: out={out.size} ratio={ratio.toString.take 5}%"
    | "compress-libdeflate" =>
      let _ ← Libdeflate.compress data level.toUInt8
      pure ()
    -- One-shot native compressed size (deterministic; no timing loop). Used to
    -- sweep ratio-only knobs cheaply across a whole corpus without paying the
    -- `compress-pareto` warmup/rep cost. Prints `size out ratio%`.
    | "csize" =>
      let out := Zip.Native.Deflate.deflateRaw data level.toUInt8
      let ratio : Float := 100.0 * out.size.toFloat / data.size.toFloat
      IO.println s!"size={data.size} lvl={level}: out={out.size} ratio={ratio.toString.take 5}%"
    -- P0 diagnostic: separate the one-time dense-table CAF build (paid on the
    -- first distance lookup of the process) from steady-state per-call cost.
    -- Builds `nin` distinct inputs (perturb one byte) to defeat CSE/memoisation,
    -- times each `deflateRaw` at `level`, and reports first-call vs mean-of-rest.
    | "profile-raw" =>
      let nin := 64
      let reps := 60
      let mut inputs : Array ByteArray := #[]
      for i in [0:nin] do
        let d := if data.size == 0 then data else
          (data.extract 0 data.size).set! (i % data.size) (data[i % data.size]!.toNat.toUInt8 ^^^ 1)
        inputs := inputs.push d
      -- Force the result through IO so each compression is fully evaluated
      -- *between* the timestamps (a pure `let` would defer evaluation past `b`).
      let sink (x : ByteArray) : IO UInt64 :=
        pure (x.size.toUInt64 + (if x.size > 0 then x[0]!.toUInt64 else 0))
      let mut acc : UInt64 := 0
      let mut times : Array Nat := #[]
      for c in inputs do
        let a ← IO.monoNanosNow
        acc := acc + (← sink (Zip.Native.Deflate.deflateRaw c level.toUInt8))
        let b ← IO.monoNanosNow
        times := times.push (b - a)
      -- Extra unmeasured passes for profiler sample volume (steady state only).
      for _ in [0:reps] do
        for c in inputs do
          acc := acc + (← sink (Zip.Native.Deflate.deflateRaw c level.toUInt8))
      if acc == 0xFFFFFFFFFFFFFFFF then IO.println "x"
      let first := times[0]!
      let rest := times.toList.drop 1
      let restMean := (rest.foldl (· + ·) 0).toFloat / rest.length.toFloat
      IO.println s!"size={data.size} lvl={level}: first={first}ns restMean={restMean.toString.take 9}ns ratio={(first.toFloat/restMean).toString.take 5}x"
    -- Pareto measurement for matcher-policy experiments: steady-state compress
    -- throughput (MB/s) AND output size (compression ratio), both axes from one
    -- run. Builds distinct inputs (perturb one byte) to defeat CSE/memoisation.
    | "compress-pareto" =>
      let nin := 4
      let reps := 12
      let mut inputs : Array ByteArray := #[]
      for i in [0:nin] do
        let d := if data.size == 0 then data else
          (data.extract 0 data.size).set! (i % data.size) (data[i % data.size]!.toNat.toUInt8 ^^^ 1)
        inputs := inputs.push d
      let sink (x : ByteArray) : IO UInt64 :=
        pure (x.size.toUInt64 + (if x.size > 0 then x[0]!.toUInt64 else 0))
      let mut acc : UInt64 := 0
      -- warm
      for c in inputs do acc := acc + (← sink (Zip.Native.Deflate.deflateRaw c level.toUInt8))
      let outSize := (Zip.Native.Deflate.deflateRaw (inputs[0]!) level.toUInt8).size
      let mut tot : Nat := 0
      for _ in [0:reps] do
        for c in inputs do
          let a ← IO.monoNanosNow
          acc := acc + (← sink (Zip.Native.Deflate.deflateRaw c level.toUInt8))
          let b ← IO.monoNanosNow
          tot := tot + (b - a)
      if acc == 0xFFFFFFFFFFFFFFFF then IO.println "x"
      let n := (reps * nin).toFloat
      let mbps : Float := (data.size.toFloat * n) / (tot.toFloat / 1.0e9) / 1.0e6
      let ratio : Float := 100.0 * outSize.toFloat / data.size.toFloat
      IO.println s!"size={data.size} lvl={level}: {mbps.toString.take 7} MB/s  out={outSize} ratio={ratio.toString.take 5}%"
    -- P1 gate 2: match-length histogram of the packed matcher stream at `level`.
    -- A reference token has bit 31 set; length sits in bits 16..30. Reports the
    -- literal/reference split and how many references have ≥8 bytes of runway
    -- (the threshold below which word-at-a-time compare cannot pay).
    | "match-hist" =>
      -- `lzMatchP` now returns a packed `TokenArray` (no `ForIn`); this is a
      -- diagnostic histogram, not the hot path, so unpack to the `Array UInt32`
      -- model to iterate.
      let ptoks := (Zip.Native.Deflate.lzMatchP data level.toUInt8).toArray
      let mut lits : Nat := 0
      let mut refs : Nat := 0
      let mut totLen : Nat := 0
      let mut ge8 : Nat := 0
      let mut ge16 : Nat := 0
      let mut ge32 : Nat := 0
      let mut ge64 : Nat := 0
      let mut ge128 : Nat := 0
      let mut buckets : Array Nat := Array.replicate 9 0  -- len 3..10 then 11+
      for w in ptoks do
        if w &&& ((1 : UInt32) <<< 31) == 0 then
          lits := lits + 1
        else
          let len := ((w >>> 16) &&& 0x7FFF).toNat
          refs := refs + 1
          totLen := totLen + len
          if len ≥ 8 then ge8 := ge8 + 1
          if len ≥ 16 then ge16 := ge16 + 1
          if len ≥ 32 then ge32 := ge32 + 1
          if len ≥ 64 then ge64 := ge64 + 1
          if len ≥ 128 then ge128 := ge128 + 1
          let b := if len ≤ 10 then len - 3 else 8
          buckets := buckets.set! b (buckets[b]! + 1)
      let refsF := if refs == 0 then 1.0 else refs.toFloat
      let pct (n : Nat) := (100.0*n.toFloat/refsF).toString.take 4
      IO.println s!"size={data.size} lvl={level}: lits={lits} refs={refs} avgLen={(totLen.toFloat/refsF).toString.take 5} ge8={ge8}({pct ge8}%) ge16={ge16}({pct ge16}%)"
      IO.println s!"  nice-thresholds: ge32={ge32}({pct ge32}%) ge64={ge64}({pct ge64}%) ge128={ge128}({pct ge128}%)"
      IO.println s!"  len-buckets [3,4,5,6,7,8,9,10,11+]: {buckets.toList}"
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
