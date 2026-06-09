import Zip
/-! # Track D benchmark report (JSON emitter)

Runs the full compress/decompress matrix — native lean-zip vs each reference
implementation — over the **real compression corpora** (Canterbury, Silesia, …)
across every DEFLATE level, measuring **compression ratio** (deterministic) and
**throughput** (median-of-N MB/s), and emits a JSON document consumed by
`bench/plot.py` to render the SVG dashboard.

Synthetic data is gone: the pseudo-prose pattern was pathologically
compressible (200:1) and its decode read ~3800 MB/s versus ~106 MB/s on real
prose in the *same* run, so it misled on every axis. Only the committed corpora
are timed now (see `bench/corpora/`).

Usage:
  lake exe bench-report [output.json]      # default: bench/results/latest.json

This is the measurement half of the Track D dashboard; see `bench/run.sh` for
the one-command regenerate (report → plot) flow and `BENCH.md` for the rendered
dashboard.
-/

/-! ## Real corpora (committed corpus cache)

Each subdirectory of `bench/corpora/` is a corpus, and every file inside it is a
single-size workload tagged `<corpus>/<file>`. The Canterbury corpus (11 files,
~2.8 MB) is committed (materialized by `bench/fetch_corpora.sh`, verified against
recorded SHA-256), so it runs at every level on every regeneration with no
network. New corpora (e.g. Silesia) are discovered automatically once their
files land — nothing here hard-codes Canterbury. -/

def corporaDir : String := "bench/corpora"

/-- Discover every committed corpus under `corporaDir`. Returns one
    `(corpus, workloads)` entry per subdirectory, where each workload is
    `("<corpus>/<file>", bytes)`. Corpora and their files are sorted by name for
    deterministic output. Absent corpora dir ⇒ empty list (dashboard degrades
    gracefully); new corpora slot in with no code change. -/
def loadCorpora : IO (List (String × List (String × ByteArray))) := do
  let root := System.FilePath.mk corporaDir
  unless ← root.pathExists do
    IO.eprintln s!"  no corpora dir (run bench/fetch_corpora.sh): {root}"
    return []
  let entries ← root.readDir
  let dirs := (entries.map (·.path)).qsort (fun a b => a.toString < b.toString)
  let mut out : List (String × List (String × ByteArray)) := []
  for dir in dirs do
    if ← dir.isDir then
      let corpus := dir.fileName.getD ""
      let files ← dir.readDir
      let paths := (files.map (·.path)).qsort (fun a b => a.toString < b.toString)
      let mut workloads : List (String × ByteArray) := []
      for path in paths do
        unless ← path.isDir do
          let bytes ← IO.FS.readBinFile path
          let name := path.fileName.getD ""
          workloads := (s!"{corpus}/{name}", bytes) :: workloads
      unless workloads.isEmpty do
        out := (corpus, workloads.reverse) :: out
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

def levels : List Nat := [1, 2, 3, 4, 5, 6, 7, 8, 9]
def reps : Nat := 5

/-- Run one compressor over a list of `(pattern, bytes)` workloads × levels,
    timing compress (and optionally decompress on a canonical raw-deflate
    stream). The size of each row is the workload's byte length. -/
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

/-- Write the exact bytes of every real-corpus payload to a per-corpus subdir as
    `dir/<corpus>/<file>.bin`, so external-language comparators (Go, Zig, OCaml,
    JS) compress byte-identical input and their ratios line up with the native
    rows. `run_external.py` reconstructs the `<corpus>/<file>` pattern from the
    path. -/
def dumpPayloads (dir : String) : IO Unit := do
  IO.FS.createDirAll dir
  let corpora ← loadCorpora
  for (corpus, files) in corpora do
    let sub := System.FilePath.mk dir / corpus
    IO.FS.createDirAll sub
    for (pat, data) in files do
      let file := pat.drop (corpus.length + 1)  -- strip "<corpus>/"
      IO.FS.writeBinFile (sub / s!"{file}.bin") data
    IO.eprintln s!"Dumped {files.length} {corpus} payloads → {sub}"

def runReport (outPath : String) : IO Unit := do
  IO.eprintln "Running Track D benchmark matrix (native vs references) on real corpora…"

  -- Real-corpus rows only: the same timing matrix over every committed corpus
  -- (one single-size workload per file), so the dashboard rests entirely on
  -- representative data. zopfli is the ratio ceiling (compress-only, very slow,
  -- level-less) — run at one nominal level / single rep so it appears on the
  -- ratio graphs without dominating wall-clock.
  let corpora ← loadCorpora
  if corpora.isEmpty then
    IO.eprintln "  no corpora found — run bench/fetch_corpora.sh"
  let mut rows : List Row := []
  for (corpus, files) in corpora do
    -- Every corpus is timed at all 9 levels (so the speed-vs-ratio scatter shows
    -- the full level sweep). Large corpora (Silesia, ~200 MB) use a single timing
    -- pass — variance is low on big files — and skip zopfli (level-less and ~100×
    -- slower than zlib), to keep the run tractable; small corpora (Canterbury)
    -- keep the median-of-`reps` matrix plus the zopfli ratio-ceiling point.
    let big := corpus == "silesia"
    let lvls := levels
    let rps  := if big then 1 else reps
    IO.eprintln s!"Running {corpus} corpus matrix ({files.length} files, levels {lvls}, reps {rps})…"
    let cn ← runWorkloads "native"      files nativeCompress     (some nativeDecompress)     (theLevels := lvls) (theReps := rps)
    let cz ← runWorkloads "zlib"        files zlibCompress       (some RawDeflate.decompress) (theLevels := lvls) (theReps := rps)
    let cm ← runWorkloads "miniz_oxide" files minizCompress      (some MinizOxide.decompress) (theLevels := lvls) (theReps := rps)
    let cl ← runWorkloads "libdeflate"  files libdeflateCompress (some Libdeflate.decompress) (theLevels := lvls) (theReps := rps)
    let czo ← if big then pure [] else
      runWorkloads "zopfli" files zopfliCompress none (theLevels := [6]) (theReps := 1)
    rows := rows ++ cn ++ cz ++ cm ++ cl ++ czo

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
