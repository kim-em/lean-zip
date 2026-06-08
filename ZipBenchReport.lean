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

/-- Non-periodic English-like text: words drawn pseudo-randomly (not in fixed
    order like `mkTextData`). The fixed-order `text` pattern compresses into a
    few very long matches, so its decompression is dominated by the LZ77 copy
    loop and barely touches Huffman symbol decoding. Random word order produces
    many short, varied matches and frequent literals, so decompression is
    **Huffman-decode-bound** — the regime the fast-bits table decoder targets. -/
def mkWordsData (size : Nat) : ByteArray := Id.run do
  let words := #["the", "of", "and", "to", "in", "a", "is", "that", "for", "it",
                  "was", "on", "are", "be", "with", "as", "at", "this", "have", "from",
                  "or", "by", "not", "but", "what", "all", "were", "when", "we", "there",
                  "can", "an", "your", "which", "their", "if", "do", "will", "each", "how"]
  let mut result := ByteArray.empty
  let mut state : UInt64 := 0x9e3779b97f4a7c15
  while result.size < size do
    state := state ^^^ (state <<< 13)
    state := state ^^^ (state >>> 7)
    state := state ^^^ (state <<< 17)
    let word := words[state.toNat % words.size]!
    for c in word.toUTF8 do
      if result.size < size then
        result := result.push c
    if result.size < size then
      result := result.push 0x20
  return result.extract 0 size

def generateData (pattern : String) (size : Nat) : ByteArray :=
  match pattern with
  | "constant" => mkConstantData size
  | "cyclic"   => mkCyclicData size
  | "prng"     => mkPrngData size
  | "text"     => mkTextData size
  | "words"    => mkWordsData size
  | _          => mkPrngData size

/-! ## Real corpora (committed Canterbury cache)

The synthetic patterns isolate behaviours but are not representative of real
data (the pseudo-text pattern is pathologically compressible). The Canterbury
corpus (11 files, ~2.8 MB) is committed under `bench/corpora/canterbury/`
(materialized by `bench/fetch_corpora.sh`, verified against recorded SHA-256),
so it runs at every level on every regeneration with no network. Each file is a
single-size workload tagged `canterbury/<file>`. -/

def corporaDir : String := "bench/corpora"

/-- The standard Canterbury corpus files (in `cantrbry.tar.gz` order). -/
def canterburyFiles : List String :=
  ["alice29.txt", "asyoulik.txt", "cp.html", "fields.c", "grammar.lsp",
   "kennedy.xls", "lcet10.txt", "plrabn12.txt", "ptt5", "sum", "xargs.1"]

/-- Load a committed corpus as `(pattern, bytes)` workloads, where `pattern` is
    `"<corpus>/<file>"`. Files that are absent (cache not materialized) are
    skipped with a warning, so the dashboard degrades gracefully. -/
def loadCorpus (corpus : String) (files : List String) :
    IO (List (String × ByteArray)) := do
  let dir := System.FilePath.mk corporaDir / corpus
  let mut out : List (String × ByteArray) := []
  for f in files do
    let path := dir / f
    if ← path.pathExists then
      let bytes ← IO.FS.readBinFile path
      out := (s!"{corpus}/{f}", bytes) :: out
    else
      IO.eprintln s!"  corpus file missing (run bench/fetch_corpora.sh): {path}"
  return out.reverse

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

def patterns : List String := ["constant", "cyclic", "prng", "text", "words"]
def sizes : List Nat := [1024, 4096, 16384, 65536, 262144, 1048576]
def levels : List Nat := [1, 2, 3, 4, 5, 6, 7, 8, 9]
def reps : Nat := 5

/-- Run one compressor over a list of `(pattern, bytes)` workloads × levels,
    timing compress (and optionally decompress on a canonical raw-deflate
    stream). The size of each row is the workload's byte length — so this serves
    both the synthetic grid (`generateData`) and the real-corpus files. -/
def runWorkloads
    (name : String)
    (workloads : List (String × ByteArray))
    (compress : ByteArray → Nat → IO ByteArray)
    (decompress? : Option (ByteArray → IO ByteArray))
    (theLevels : List Nat := levels) (theReps : Nat := reps) : IO (List Row) := do
  let mut rows : List Row := []
  for (pat, data) in workloads do
    let size := data.size
    for level in theLevels do
      let compressed ← compress data level
      let outSize := compressed.size
      let ratio := outSize.toFloat / (max size 1).toFloat
      let cNs ← measureNs size theReps (compress data level >>= sink)
      -- Decompress timing uses a canonical zlib-FFI raw-deflate stream so all
      -- decoders are measured on identical, format-correct input.
      let dMBps ← match decompress? with
        | none => pure none
        | some dec => do
          let ref ← RawDeflate.compress data level.toUInt8
          let dNs ← measureNs size theReps (dec ref >>= sink)
          pure (mbps size dNs)
      rows := { compressor := name, pattern := pat, size := size, level := level,
                outSize := outSize, ratio := ratio,
                compressMBps := mbps size cNs, decompressMBps := dMBps } :: rows
    IO.eprint "."  -- progress
  IO.eprintln s!" {name} done"
  return rows.reverse

/-- Run one compressor over the synthetic pattern×size×level grid. `theSizes`/
    `theLevels`/`theReps` let slow ratio-ceiling compressors (zopfli) run a
    reduced grid. -/
def runCompressor
    (name : String)
    (compress : ByteArray → Nat → IO ByteArray)
    (decompress? : Option (ByteArray → IO ByteArray))
    (theSizes : List Nat := sizes) (theLevels : List Nat := levels)
    (theReps : Nat := reps) : IO (List Row) := do
  let workloads := patterns.flatMap fun pat =>
    theSizes.map fun size => (pat, generateData pat size)
  runWorkloads name workloads compress decompress? theLevels theReps

/-- Ratio-only rows (no timing) for a compressor across `theLevels` at one size —
    used to populate the ratio-vs-level plot densely (every DEFLATE level) without
    paying the median-of-N timing cost at every level. `levelSize` matches the
    plotter's `LEVEL_SIZE`. -/
def levelSize : Nat := 65536
def runRatioLevels (name : String) (compress : ByteArray → Nat → IO ByteArray)
    (theLevels : List Nat) : IO (List Row) := do
  let mut rows : List Row := []
  for pat in patterns do
    let data := generateData pat levelSize
    for level in theLevels do
      let compressed ← compress data level
      rows := { compressor := name, pattern := pat, size := levelSize, level := level,
                outSize := compressed.size,
                ratio := compressed.size.toFloat / (max levelSize 1).toFloat,
                compressMBps := none, decompressMBps := none } :: rows
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

def libdeflateCompress (data : ByteArray) (level : Nat) : IO ByteArray :=
  Libdeflate.compress data level.toUInt8

/-- zopfli is level-less; ignore the level and use its default iteration count. -/
def zopfliCompress (data : ByteArray) (_level : Nat) : IO ByteArray :=
  Zopfli.compress data 0

/-! ## Meta + main -/

def shell (cmd : String) (args : List String) : IO String := do
  try
    let out ← IO.Process.run { cmd := cmd, args := args.toArray }
    pure (out.replace "\n" "")
  catch _ => pure "unknown"

/-- Write the exact bytes of every `pattern × size` payload to
    `dir/<pattern>_<size>.bin`, so external-language comparators (Go, Zig, OCaml,
    JS) compress byte-identical input and their ratios line up with the native
    rows. Keeps the pattern generators in one place (here) rather than
    reimplemented per language. -/
def dumpPayloads (dir : String) : IO Unit := do
  IO.FS.createDirAll dir
  for pat in patterns do
    for size in sizes do
      let data := generateData pat size
      IO.FS.writeBinFile (System.FilePath.mk dir / s!"{pat}_{size}.bin") data
  IO.eprintln s!"Dumped {patterns.length * sizes.length} synthetic payloads → {dir}"
  -- Real-corpus payloads go in a per-corpus subdir as `<file>.bin`, so
  -- `run_external.py` reconstructs the `<corpus>/<file>` pattern from the path
  -- and feeds the comparators byte-identical corpus bytes.
  let corpus ← loadCorpus "canterbury" canterburyFiles
  unless corpus.isEmpty do
    let sub := System.FilePath.mk dir / "canterbury"
    IO.FS.createDirAll sub
    for (pat, data) in corpus do
      let file := pat.drop "canterbury/".length
      IO.FS.writeBinFile (sub / s!"{file}.bin") data
    IO.eprintln s!"Dumped {corpus.length} canterbury payloads → {sub}"

def runReport (outPath : String) : IO Unit := do
  IO.eprintln "Running Track D benchmark matrix (native vs references)…"

  let nativeRows ← runCompressor "native" nativeCompress (some nativeDecompress)
  let zlibRows   ← runCompressor "zlib"   zlibCompress   (some RawDeflate.decompress)
  let minizRows  ← runCompressor "miniz_oxide" minizCompress (some MinizOxide.decompress)
  let libdeflRows ← runCompressor "libdeflate" libdeflateCompress (some Libdeflate.decompress)
  -- zopfli is the ratio ceiling: compress-only, very slow, level-less. Run a
  -- reduced grid (one nominal level, capped size, single rep) so it appears on
  -- the ratio graphs without dominating wall-clock.
  let zopfliRows ← runCompressor "zopfli" zopfliCompress none
                     (theSizes := sizes.filter (· ≤ 262144)) (theLevels := [6]) (theReps := 1)
  -- The timed matrix now covers every DEFLATE level (1–9) at every size, so the
  -- ratio-by-level plot reads its dense per-level data straight from the timed
  -- rows — no separate ratio-only gap fill is needed. zopfli stays a single
  -- (level-less) point.
  let syntheticRows := nativeRows ++ zlibRows ++ minizRows ++ libdeflRows ++ zopfliRows

  -- Real-corpus rows: the same timing matrix over the committed Canterbury files
  -- (one single-size workload per file), so the dashboard rests on representative
  -- data, not only the synthetic patterns. Canterbury is small (~2.8 MB), so the
  -- C/Rust references and zopfli all run at every level alongside native.
  let corpus ← loadCorpus "canterbury" canterburyFiles
  let corpusRows ← if corpus.isEmpty then pure [] else do
    IO.eprintln s!"Running Canterbury corpus matrix ({corpus.length} files)…"
    let cn ← runWorkloads "native"      corpus nativeCompress     (some nativeDecompress)
    let cz ← runWorkloads "zlib"        corpus zlibCompress       (some RawDeflate.decompress)
    let cm ← runWorkloads "miniz_oxide" corpus minizCompress      (some MinizOxide.decompress)
    let cl ← runWorkloads "libdeflate"  corpus libdeflateCompress (some Libdeflate.decompress)
    let czo ← runWorkloads "zopfli"     corpus zopfliCompress     none (theLevels := [6]) (theReps := 1)
    pure (cn ++ cz ++ cm ++ cl ++ czo)

  let rows := syntheticRows ++ corpusRows

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

def main (args : List String) : IO Unit := do
  match args with
  | ["--dump-payloads", dir] => dumpPayloads dir
  | _ => runReport (args.head?.getD "bench/results/latest.json")
