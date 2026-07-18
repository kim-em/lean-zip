import Zip
import Bench.MinizOxide
import Bench.Libdeflate
import Bench.Zopfli
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

/-- Level range for the FFI reference codecs (zlib, miniz_oxide), whose
    `deflateInit2` accepts only 0–9. -/
def levels : List Nat := [1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- Native lean-zip's level range. Wider than the zlib/miniz FFI cap of 9: since
    #2638, level 9 is the L9-fast approximate-optimal tier and **level 10 is the
    exact-DP crown** (the max-ratio ceiling). The dashboard must always sweep
    native through 10 so the crown stays on the Pareto — otherwise the headline
    graph loses our best-ratio point. `runWorkloads` already omits the decode
    timing for `level > 9` (no zlib-FFI raw-deflate reference exists there), so
    the extra native point is compress-only, exactly like libdeflate 10–12. -/
def nativeLevels : List Nat := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- libdeflate's full level range. It exposes 1–12, and its densest points
    (10–12) are exactly the ones the comparison Pareto needs from it — so it is
    swept to 12 here while the FFI references cap at 9 and native caps at 10. -/
def libdeflateLevels : List Nat := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
def reps : Nat := 5

/-- Run one compressor over a list of `(pattern, bytes)` workloads × levels,
    timing compress (and optionally decompress on a canonical raw-deflate
    stream). The size of each row is the workload's byte length. -/
def runWorkloads
    (name : String)
    (workloads : List (String × ByteArray))
    (compress : ByteArray → Nat → IO ByteArray)
    (decompress? : Option (ByteArray → Nat → IO ByteArray))
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
      -- decoders are measured on identical, format-correct input. That reference
      -- is built by the zlib FFI, whose `deflateInit2` accepts only levels 0–9,
      -- so a codec swept past 9 (libdeflate 10–12) has no faithful reference at
      -- its own level: decode timing is **omitted** there rather than measured on
      -- a mislabelled lower-level stream (and the dedicated decode-density
      -- experiment covers those levels on real libdeflate streams anyway). This
      -- also sidesteps the `deflateInit2: stream error` the extended levels raise.
      let dMBps ← match decompress? with
        | none => pure none
        | some dec =>
          if level > 9 then pure none
          else do
            let ref ← RawDeflate.compress data level.toUInt8
            -- The decompressed size is known here; pass it as the exact size so
            -- the native decoder runs its verified `uset` exact-size fastloop
            -- (`inflateSized … (exact := true)`), matching the production
            -- ZIP/gzip path where the uncompressed size comes from the archive
            -- metadata. The FFI reference decoders ignore it.
            let dNs ← measureNs size theReps (dec ref size >>= sink)
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

def nativeDecompress (data : ByteArray) (origSize : Nat) : IO ByteArray :=
  -- Route through `inflateSized … (exact := true)`: the decode-density scenario
  -- feeds the true `origSize`, so this engages the verified branch-free `uset`
  -- exact-size fastloop — exactly the production ZIP-extraction decode path
  -- (`Zip.Archive`), not the push decoder. `inflateSized_agrees` proves this is
  -- byte-identical to `inflate`; with the true non-zero corpus `origSize`,
  -- `exact := true` takes the fast path (a `0` size would fall back harmlessly).
  match Zip.Native.Inflate.inflateSized data (sizeHint := origSize) (exact := true) with
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

def runReport (outPath : String) (nativeOnly : Bool := false)
    (levelOverride : Option (List Nat) := none) : IO Unit := do
  IO.eprintln s!"Running Track D benchmark matrix ({if nativeOnly then "native ONLY" else "native vs references"}\
{match levelOverride with | some ls => s!", levels {ls}" | none => ""}) on real corpora…"

  -- Real-corpus rows only: the same timing matrix over every committed corpus
  -- (one single-size workload per file), so the dashboard rests entirely on
  -- representative data.
  let corpora ← loadCorpora
  if corpora.isEmpty then
    IO.eprintln "  no corpora found — run bench/fetch_corpora.sh"
  let mut rows : List Row := []
  for (corpus, files) in corpora do
    -- Every corpus is timed at all 9 levels (so the speed-vs-ratio scatter shows
    -- the full level sweep). Large corpora (Silesia, ~200 MB) use a single timing
    -- pass — variance is low on big files — to keep the run tractable; small
    -- corpora (Canterbury) keep the median-of-`reps` matrix.
    --
    -- zopfli is intentionally not benchmarked here: it is compress-only and
    -- ~100× slower than zlib (default iteration count), so even at one
    -- level/rep it dominated the wall-clock of the whole matrix. Its FFI binding
    -- (`zopfliCompress`) is kept for ad-hoc ratio-ceiling checks.
    let big := corpus == "silesia"
    -- Native sweeps 1–10 (incl. the level-10 crown, #2638); the FFI references
    -- (zlib/miniz) cap at 9. An explicit `levelOverride` (a native-only regen at
    -- a chosen level list) applies to whichever codecs run.
    let nlvls := levelOverride.getD nativeLevels
    let lvls := levelOverride.getD levels
    let rps  := if big then 1 else reps
    IO.eprintln s!"Running {corpus} corpus matrix ({files.length} files, native levels {nlvls}, reps {rps})…"
    let cn ← runWorkloads "native"      files nativeCompress     (some nativeDecompress)     (theLevels := nlvls) (theReps := rps)
    -- `--native-only`: skip the reference compressors. Their ratios are
    -- deterministic and their MB/s drift <~3% run-to-run (measured), so a Lean-only
    -- change reuses the prior dashboard's reference rows (spliced in post-hoc by
    -- bench/run.sh) instead of paying to re-measure them.
    if nativeOnly then
      rows := rows ++ cn
    else
      let cz ← runWorkloads "zlib"        files zlibCompress       (some fun d _ => RawDeflate.decompress d) (theLevels := lvls) (theReps := rps)
      let cm ← runWorkloads "miniz_oxide" files minizCompress      (some fun d _ => MinizOxide.decompress d) (theLevels := lvls) (theReps := rps)
      -- libdeflate sweeps 1–12 (its full range); the others cap at 9. A level
      -- override (the native-only dashboard regen) is for the Lean codec, so
      -- libdeflate keeps its own full list unless that override is in effect.
      let llvls := match levelOverride with | some ls => ls | none => libdeflateLevels
      let cl ← runWorkloads "libdeflate"  files libdeflateCompress (some fun d _ => Libdeflate.decompress d) (theLevels := llvls) (theReps := rps)
      rows := rows ++ cn ++ cz ++ cm ++ cl

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

/-- One-shot zopfli ratio-ceiling run over every corpus. zopfli is compress-only,
    level-less, and ~100× slower than zlib (default iteration count), so it is
    deliberately NOT part of the routine `runReport` matrix. This writes a FROZEN
    snapshot of the best-achievable ratio per file; the dashboard overlays it
    (see `bench/plot.py`) without ever recomputing it. Do not regenerate unless
    the corpora themselves change — see `bench/README.md`. -/
def runZopfliCeiling (outPath : String) : IO Unit := do
  IO.eprintln "Running ONE-TIME zopfli ratio ceiling over all corpora (slow — frozen artifact)…"
  let corpora ← loadCorpora
  if corpora.isEmpty then
    IO.eprintln "  no corpora found — run bench/fetch_corpora.sh"
  let mut rows : List Row := []
  for (corpus, files) in corpora do
    IO.eprintln s!"  zopfli {corpus} ({files.length} files)…"
    -- ratio only (zopfli is level-less; level 6 is nominal, single rep — the
    -- compress_mbps column is an artifact, not a benchmark).
    let cz ← runWorkloads "zopfli" files zopfliCompress none (theLevels := [6]) (theReps := 1)
    rows := rows ++ cz
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
    "    \"frozen\": true,\n" ++
    "    \"note\": \"FROZEN zopfli ratio ceiling — do NOT regenerate. zopfli is " ++
    "compress-only, level-less and ~100x slower than zlib; level=6 is nominal and " ++
    "compress_mbps is a single-rep artifact, not a benchmark. ratio/out_size are " ++
    "deterministic. Regenerate only if the corpora change: lake env " ++
    ".lake/build/bin/bench-report --zopfli-ceiling bench/results/zopfli-ceiling.json\"\n" ++
    "  },\n" ++
    "  \"results\": [\n" ++ body ++ "\n  ]\n}\n"
  if let some parent := (System.FilePath.mk outPath).parent then
    IO.FS.createDirAll parent
  IO.FS.writeFile outPath json
  IO.eprintln s!"Wrote {rows.length} zopfli rows → {outPath}"

/-- Decode `ref` through `inflateSized … (exact := true)`, optionally at exact
    size `hint` (`0` = no hint → push decoder; `> 0` → verified exact-size `uset`
    fastloop, the production ZIP-extraction path). `inflateSized_agrees` makes both
    arms byte-identical to `inflate`. `@[noinline]` keeps the pure decode call from
    being hoisted out of the timed loop (it is otherwise loop-invariant), so each
    timed call really decodes. -/
@[noinline] def decodeForAB (ref : ByteArray) (hint : Nat) : IO Nat := do
  match Zip.Native.Inflate.inflateSized ref (sizeHint := hint) (exact := true) with
  | .ok b => sink b
  | .error e => throw (IO.userError e)

/-- Paired, interleaved decode A/B: native decode WITH the exact output size vs
    WITHOUT it, measured back-to-back per file so machine-load common-mode noise
    cancels. Since both arms go through `inflateSized … (exact := true)`, the
    exact-size arm (`hint = size`) engages the verified `uset` fastloop while the
    no-hint arm (`hint = 0`) falls back to the push decoder — so this now measures
    the *fastloop* speedup, not merely output presizing. Reports per-corpus geomean
    speedup (no-hint time / exact-size time) with a 95% CI on the log-ratios. Robust
    on a busy shared machine; pin with `taskset -c`. This is a diagnostic, not part
    of the dashboard matrix. -/
def runPresizeAB (pairs : Nat := 12) : IO Unit := do
  let corpora ← loadCorpora
  IO.println s!"Paired decode A/B (push no-hint time / exact-size fastloop time), {pairs} pairs/file, level 6:"
  for (corpus, files) in corpora do
    let mut logs : List Float := []
    let mut noMBs : List Float := []
    let mut yesMBs : List Float := []
    for (_pat, data) in files do
      let size := data.size
      let ref ← RawDeflate.compress data 6
      let _ ← decodeForAB ref 0; let _ ← decodeForAB ref size  -- warm
      for p in [:pairs] do
        let (nNs, yNs) ←
          if p % 2 == 0 then
            let a ← timePerOp 1 (decodeForAB ref 0)
            let b ← timePerOp 1 (decodeForAB ref size)
            pure (a, b)
          else
            let b ← timePerOp 1 (decodeForAB ref size)
            let a ← timePerOp 1 (decodeForAB ref 0)
            pure (a, b)
        if nNs > 0 && yNs > 0 then
          logs := Float.log (nNs.toFloat / yNs.toFloat) :: logs
          let mb (ns : Nat) : Float := (size.toFloat / (1024.0 * 1024.0)) / (ns.toFloat / 1.0e9)
          noMBs := mb nNs :: noMBs
          yesMBs := mb yNs :: yesMBs
    let n := logs.length
    if n == 0 then
      IO.println s!"  {corpus}: no data"
    else
      let nf := n.toFloat
      let mean := (logs.foldl (· + ·) 0.0) / nf
      let var := (logs.foldl (fun a x => a + (x - mean) * (x - mean)) 0.0) / (max (nf - 1.0) 1.0)
      let std := Float.sqrt var
      let hw := 1.96 * std / Float.sqrt nf
      let sp := Float.exp mean
      let lo := Float.exp (mean - hw)
      let hi := Float.exp (mean + hw)
      let avg (xs : List Float) : Float := (xs.foldl (· + ·) 0.0) / xs.length.toFloat
      IO.println s!"  {corpus} (n={n}): speedup={round4 sp}x  95% CI [{round4 lo}, {round4 hi}]  \
nohint={round2 (avg noMBs)} MB/s  presize={round2 (avg yesMBs)} MB/s"

/-! ## Decode-density experiment

The compress dashboard's headline is a *speed-vs-ratio Pareto* because each codec
chooses its own ratio/speed tradeoff. Decompression has no such tradeoff: the
input density is exogenous (a property of the stream, not the decoder's choice).
The right decode chart is therefore **decode throughput vs input density**, with
every decoder measured on *byte-identical* input — only possible because DEFLATE
is one interoperable format. We fix the encoder to **libdeflate** (raw DEFLATE,
the densest realistic streams, level range 1–12) and decode the identical streams
with every decoder, plus a `memcpy` ceiling (the bandwidth bound on emitting the
output bytes). The in-process decoders (native/zlib/miniz/libdeflate) are timed
here; the external comparators decode the dumped streams via their `decode` mode
(see `bench/decode_density.py`). Output rows reuse the `Row` schema with
`compressor` holding the *decoder* name and `ratio` holding libdeflate's
compression ratio (the x-axis). -/

def decodeDensityLevels : List Nat := [1, 3, 6, 9, 12]

/-- Fixed-encoder streams for the decode-density experiment: libdeflate at each
    level in `decodeDensityLevels`, plus a single zopfli stream (the densest
    realistic raw DEFLATE). Each entry is `(fileTag, levelField, encode)` where
    `fileTag` names the on-disk stream (`<file>_<fileTag>.deflate`), `levelField`
    is recorded in the emitted Row (`0` = zopfli, a level-less sentinel), and
    `encode` produces the raw stream on a cache miss. Constructing the list does
    not run any encoder — the `IO` actions stay unforced until a stream is
    genuinely missing from the cache. -/
def decodeDensityEncodings (data : ByteArray) : List (String × Nat × IO ByteArray) :=
  decodeDensityLevels.map (fun l => (s!"L{l}", l, Libdeflate.compress data l.toUInt8))
    ++ [("zopfli", 0, Zopfli.compress data 0)]

/-- A memcpy of `data.size` bytes (a fresh full-range copy): the decode-speed
    ceiling — no decoder can emit output faster than memory bandwidth. -/
@[noinline] def memcpyBytes (data : ByteArray) : IO Nat :=
  pure (data.extract 0 data.size).size

def runDecodeDensity (outPath streamsDir : String) : IO Unit := do
  IO.eprintln "Running decode-density (fixed libdeflate input; native/zlib/miniz/libdeflate + memcpy) over silesia…"
  let corpora ← loadCorpora
  let mut rows : List Row := []
  for (corpus, files) in corpora do
    if corpus == "silesia" then
      IO.FS.createDirAll (System.FilePath.mk streamsDir / corpus)
      IO.eprintln s!"  silesia: {files.length} files × (libdeflate {decodeDensityLevels} + zopfli), streams cached under {streamsDir}"
      for (pat, data) in files do
        let size := data.size
        let file := pat.drop (corpus.length + 1)
        for (tag, level, enc) in decodeDensityEncodings data do
          -- Semi-permanent stream cache: reuse a dumped stream, but only if it
          -- still decodes to the exact current payload — a stale, truncated, or
          -- wrong-corpus file is treated as missing and re-encoded (zopfli
          -- especially is far too slow to recompress every run). On a genuine
          -- miss, encode once and persist. Only the optional zopfli encoder may be
          -- absent, in which case that one stream is skipped; a libdeflate encode
          -- failure or a cache-write failure is fatal, not silently swallowed.
          let streamPath := System.FilePath.mk streamsDir / corpus / s!"{file}_{tag}.deflate"
          let cached? ← do
            if ← streamPath.pathExists then
              let bytes ← IO.FS.readBinFile streamPath
              let valid ← try (do let dec ← RawDeflate.decompress bytes; pure (dec == data))
                          catch _ => pure false
              if valid then pure (some bytes)
              else
                IO.eprintln s!"\n  stale cache {file} {tag}: re-encoding"
                pure none
            else pure none
          let stream? ← match cached? with
            | some bytes => pure (some bytes)
            | none =>
              let encoded? ←
                try pure (some (← enc))
                catch e =>
                  if tag == "zopfli" then
                    IO.eprintln s!"\n  skip {file} zopfli (encoder unavailable): {toString e}"
                    pure none
                  else throw e
              match encoded? with
              | none => pure none
              | some s => IO.FS.writeBinFile streamPath s; pure (some s)
          let some stream := stream? | continue
          let outSize := stream.size
          let ratio := round4 (outSize.toFloat / (max size 1).toFloat)
          let mkRow (name : String) (d : Option Float) : Row :=
            { compressor := name, pattern := pat, size := size, level := level,
              outSize := outSize, ratio := ratio, compressMBps := none, decompressMBps := d }
          let dn ← measureNs size reps (nativeDecompress stream size >>= sink)
          let dz ← measureNs size reps (RawDeflate.decompress stream >>= sink)
          let dm ← measureNs size reps (MinizOxide.decompress stream >>= sink)
          let dl ← measureNs size reps (Libdeflate.decompress stream >>= sink)
          let dc ← measureNs size reps (memcpyBytes data)
          rows := rows ++
            [ mkRow "native" (mbps size dn), mkRow "zlib" (mbps size dz),
              mkRow "miniz_oxide" (mbps size dm), mkRow "libdeflate" (mbps size dl),
              mkRow "memcpy" (mbps size dc) ]
        IO.eprint "."
      IO.eprintln " silesia decode-density done"
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
    "    \"experiment\": \"decode-density: fixed encoder (libdeflate levels + zopfli, level 0 = zopfli), ratio = encoder compression ratio, " ++
    "decompress_mbps = each decoder on identical streams; compressor field holds the decoder name\"\n" ++
    "  },\n" ++
    "  \"results\": [\n" ++ body ++ "\n  ]\n}\n"
  if let some parent := (System.FilePath.mk outPath).parent then
    IO.FS.createDirAll parent
  IO.FS.writeFile outPath json
  IO.eprintln s!"Wrote {rows.length} decode-density rows → {outPath} (streams → {streamsDir})"

def main (args : List String) : IO Unit := do
  match args with
  | ["--presize-ab"] => runPresizeAB
  | ["--presize-ab", nStr] => runPresizeAB ((nStr.toNat?).getD 12)
  | ["--decode-density", out, streamsDir] => runDecodeDensity out streamsDir
  | ["--dump-payloads", dir] => dumpPayloads dir
  | ["--zopfli-ceiling", out] => runZopfliCeiling out
  | ["--native-only", out] => runReport out (nativeOnly := true)
  | ["--native-only", out, lvlCsv] =>
    -- e.g. "1,2,3,4,5,6,7,8" to skip the slow optimal-parse L9 when a Lean change
    -- does not touch the L9 path; the dashboard splice keeps the prior L9 + reference rows.
    let lvls := (lvlCsv.splitOn ",").filterMap (·.trim.toNat?)
    runReport out (nativeOnly := true) (levelOverride := some lvls)
  | _ => runReport (args.head?.getD "bench/results/latest.json")
