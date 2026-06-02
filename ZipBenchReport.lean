import Zip
/-! # Track D benchmark report (JSON emitter)

Runs the full compress/decompress matrix — native lean-zip vs each reference
implementation — across data patterns × sizes × levels, measuring **compression
ratio** (deterministic) and **throughput** (median-of-N MB/s), and emits a JSON
document consumed by `bench/plot.py` to render the log-scale SVG dashboard.

Usage:
  lake exe bench-report [output.json]      # default: bench/results/latest.json

This is the measurement half of the Track D dashboard; see `bench/run.sh` for
the one-command regenerate (report → plot) flow and `BENCH.md` for the rendered
dashboard. The data generators mirror `ZipBench.lean` (the hyperfine driver) so
the two measurement paths see identical inputs.
-/

/-! ## Data generators (mirror `ZipBench.lean`) -/

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
        result := result.push 0x0A
        col := 0
      else
        result := result.push 0x20
        col := col + 1
    for c in word.toUTF8 do
      if result.size < size then
        result := result.push c
    col := col + word.length
  return result.extract 0 size

def generateData (pattern : String) (size : Nat) : ByteArray :=
  match pattern with
  | "constant" => mkConstantData size
  | "cyclic"   => mkCyclicData size
  | "prng"     => mkPrngData size
  | "text"     => mkTextData size
  | _          => mkPrngData size

/-! ## Timing -/

/-- Force a `ByteArray` value and return a quantity derived from it, so the
    optimizer cannot eliminate the computation under test. -/
@[noinline] def sink (b : ByteArray) : IO Nat := pure b.size

/-- Median (lower-middle) of a list of nanosecond timings. -/
def median (xs : List Nat) : Nat :=
  let a := xs.toArray.qsort (· < ·)
  if a.size == 0 then 0 else a[a.size / 2]!

/-- Time `act` `iters` times, returning nanoseconds-per-op. `act` returns a
    nonzero quantity that is accumulated to keep the work observably live. -/
def timePerOp (iters : Nat) (act : IO Nat) : IO Nat := do
  let t0 ← IO.monoNanosNow
  let mut acc : Nat := 0
  for _ in [:iters] do
    acc := acc + (← act)
  let t1 ← IO.monoNanosNow
  -- Defeat dead-code elimination without affecting the timed region.
  if acc == 0 then IO.eprintln "unreachable"
  return (t1 - t0) / (max iters 1)

/-- Iteration count by data size — small inputs are looped more for stability. -/
def itersFor (size : Nat) : Nat :=
  if size ≤ 16384 then 50
  else if size ≤ 262144 then 10
  else if size ≤ 1048576 then 3
  else 1

/-- Median ns-per-op over `reps` repetitions of an `itersFor size`-long loop. -/
def measureNs (size reps : Nat) (act : IO Nat) : IO Nat := do
  let iters := itersFor size
  let mut ts : List Nat := []
  for _ in [:reps] do
    ts := (← timePerOp iters act) :: ts
  return median ts

/-! ## JSON helpers (hand-rolled to avoid pulling in `Lean.Data.Json`) -/

def round2 (f : Float) : Float := (f * 100.0).round / 100.0
def round4 (f : Float) : Float := (f * 10000.0).round / 10000.0

/-- MB/s from a per-op nanosecond figure; `none` if the timing was zero. -/
def mbps (bytes nsPerOp : Nat) : Option Float :=
  if nsPerOp == 0 then none
  else some (round2 ((bytes.toFloat / (1024.0 * 1024.0)) / (nsPerOp.toFloat / 1.0e9)))

def jNum? : Option Float → String
  | none => "null"
  | some f => toString f

/-- One result row. `decompressMBps`/`outSize` are optional (e.g. ratio-only
    compressors record no decompress timing). -/
structure Row where
  compressor : String
  pattern : String
  size : Nat
  level : Nat
  outSize : Nat
  ratio : Float
  compressMBps : Option Float
  decompressMBps : Option Float

def Row.toJson (r : Row) : String :=
  "    {" ++
  s!"\"compressor\": \"{r.compressor}\", \"pattern\": \"{r.pattern}\", " ++
  s!"\"size\": {r.size}, \"level\": {r.level}, \"out_size\": {r.outSize}, " ++
  s!"\"ratio\": {round4 r.ratio}, " ++
  s!"\"compress_mbps\": {jNum? r.compressMBps}, " ++
  s!"\"decompress_mbps\": {jNum? r.decompressMBps}" ++
  "}"

/-! ## Matrix -/

def patterns : List String := ["constant", "cyclic", "prng", "text"]
def sizes : List Nat := [1024, 4096, 16384, 65536, 262144, 1048576]
def levels : List Nat := [1, 6, 9]
def reps : Nat := 5

/-- Run one compressor over the whole pattern×size×level grid. `compress`
    returns the compressed bytes (for ratio); `decompress?` optionally times a
    decoder on a canonical raw-deflate stream. -/
def runCompressor
    (name : String)
    (compress : ByteArray → Nat → IO ByteArray)
    (decompress? : Option (ByteArray → IO ByteArray)) : IO (List Row) := do
  let mut rows : List Row := []
  for pat in patterns do
    for size in sizes do
      let data := generateData pat size
      for level in levels do
        let compressed ← compress data level
        let outSize := compressed.size
        let ratio := outSize.toFloat / (max size 1).toFloat
        let cNs ← measureNs size reps (compress data level >>= sink)
        -- Decompress timing uses a canonical zlib-FFI raw-deflate stream so all
        -- decoders are measured on identical, format-correct input.
        let dMBps ← match decompress? with
          | none => pure none
          | some dec => do
            let ref ← RawDeflate.compress data level.toUInt8
            let dNs ← measureNs size reps (dec ref >>= sink)
            pure (mbps size dNs)
        rows := { compressor := name, pattern := pat, size := size, level := level,
                  outSize := outSize, ratio := ratio,
                  compressMBps := mbps size cNs, decompressMBps := dMBps } :: rows
      IO.eprint "."  -- progress
  IO.eprintln s!" {name} done"
  return rows.reverse

/-! ## Compressor adapters -/

def nativeCompress (data : ByteArray) (level : Nat) : IO ByteArray :=
  pure (Zip.Native.Deflate.deflateRaw data level.toUInt8)

def nativeDecompress (data : ByteArray) : IO ByteArray :=
  match Zip.Native.Inflate.inflate data with
  | .ok b => pure b
  | .error e => throw (IO.userError e)

def zlibCompress (data : ByteArray) (level : Nat) : IO ByteArray :=
  RawDeflate.compress data level.toUInt8

def minizCompress (data : ByteArray) (level : Nat) : IO ByteArray :=
  MinizOxide.compress data level.toUInt8

/-! ## Meta + main -/

def shell (cmd : String) (args : List String) : IO String := do
  try
    let out ← IO.Process.run { cmd := cmd, args := args.toArray }
    pure (out.replace "\n" "")
  catch _ => pure "unknown"

def main (args : List String) : IO Unit := do
  let outPath := args.head?.getD "bench/results/latest.json"
  IO.eprintln "Running Track D benchmark matrix (native vs references)…"

  let nativeRows ← runCompressor "native" nativeCompress (some nativeDecompress)
  let zlibRows   ← runCompressor "zlib"   zlibCompress   (some RawDeflate.decompress)
  let minizRows  ← runCompressor "miniz_oxide" minizCompress (some MinizOxide.decompress)
  let rows := nativeRows ++ zlibRows ++ minizRows

  let date ← shell "date" ["-u", "+%Y-%m-%dT%H:%M:%SZ"]
  let machine ← shell "uname" ["-mns"]
  let commit ← shell "git" ["rev-parse", "--short", "HEAD"]
  let toolchain ← shell "cat" ["lean-toolchain"]

  let body := String.intercalate ",\n" (rows.map Row.toJson)
  let json :=
    "{\n" ++
    "  \"meta\": {\n" ++
    s!"    \"date\": \"{date}\",\n" ++
    s!"    \"machine\": \"{machine}\",\n" ++
    s!"    \"git_commit\": \"{commit}\",\n" ++
    s!"    \"toolchain\": \"{toolchain}\",\n" ++
    s!"    \"note\": \"compress_mbps/decompress_mbps are a median-of-{reps} snapshot on the machine above; ratio is deterministic\"\n" ++
    "  },\n" ++
    "  \"results\": [\n" ++ body ++ "\n  ]\n}\n"

  -- Ensure parent dir exists, then write.
  if let some parent := (System.FilePath.mk outPath).parent then
    IO.FS.createDirAll parent
  IO.FS.writeFile outPath json
  IO.eprintln s!"Wrote {rows.length} rows → {outPath}"
