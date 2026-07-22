import Zip
/-! # Fast-L1 emit-cost attribution (issue #2726, Step 1)

A tokens-held-constant microbench on Silesia. With `ptokens := lzMatchP data 1`
fixed (matched *once*, outside every timed region), it times separately the
pieces of the level-1 emit path so the fast-L1 design can be chosen from the
attribution instead of assumed:

1. `tokenFreqsPTA ptokens`                        — the frequency walk
2. `tokenFreqsP` + `dynamicCodeLengths + dynHeaderCodes + dynBlockBytesWith`
                                                   — freqs + the dynamic sizing/tree
                                                     build (as `deflateRawBaseP`
                                                     runs it; contrast with row 1
                                                     to isolate the tree build)
3. `fixedBlockBytes` (over freshly walked freqs) — the fixed sizer
4. `deflateFixedBlockP data ptokens`              — fixed-only emit (token walk + BitWriter)
5. `deflateRawBaseP data ptokens`                 — the full base candidate

plus, per file, which block the current L1 dispatch actually emits
(stored / fixed / dynamic) and the resulting sizes.

Run: `lake exe l1-attrib [corpusDir]`   (default `bench/corpora/silesia`).
Emits a Markdown table on stdout (MB/s per stage, chosen branch) for the
issue's Step-1 attribution table.
-/

open Zip.Native.Deflate
open Zip.Spec.DeflateStoredCorrect (storedBlockBytes)

/-- Median (lower-middle) of nanosecond timings. -/
def medianNs (xs : List Nat) : Nat :=
  let a := xs.toArray.qsort (· < ·)
  if a.size == 0 then 0 else a[a.size / 2]!

/-- Iteration count by data size (mirrors `ZipBenchReport.itersFor`). -/
def itersFor (size : Nat) : Nat :=
  if size ≤ 16384 then 50
  else if size ≤ 262144 then 10
  else if size ≤ 1048576 then 3
  else 1

/-- Time `op` `iters` times; ns per op. `op` is a `Unit → Nat` **thunk**, not a
    pre-evaluated `IO Nat`: `pure expr` would force `expr` once at construction
    (Lean is strict), so the timed loop would measure nothing. A function body
    re-runs on every application, so `op ()` genuinely recomputes each iteration.
    `@[noinline]` keeps the optimizer from lifting the loop-invariant call out. -/
@[noinline] def timePerOp (iters : Nat) (op : Unit → Nat) : IO Nat := do
  let t0 ← IO.monoNanosNow
  let mut acc : Nat := 0
  for _ in [:iters] do
    acc := acc + op ()
  let t1 ← IO.monoNanosNow
  if acc == 0 then IO.eprintln "unreachable"
  return (t1 - t0) / (max iters 1)

/-- Median ns-per-op over `reps` timed loops. -/
def measureNs (size : Nat) (reps : Nat) (op : Unit → Nat) : IO Nat := do
  let iters := itersFor size
  let mut ts : List Nat := []
  for _ in [:reps] do
    ts := (← timePerOp iters op) :: ts
  return medianNs ts

/-- MB/s from a per-op nanosecond figure (throughput vs *uncompressed* bytes). -/
def mbps (bytes nsPerOp : Nat) : Float :=
  if nsPerOp == 0 then 0.0
  else (bytes.toFloat / (1024.0 * 1024.0)) / (nsPerOp.toFloat / 1.0e9)

def round1 (f : Float) : Float := (f * 10.0).round / 10.0

/-- Which base-candidate block `deflateRawBaseP` emits for these tokens. -/
inductive Branch | stored | fixed | dyn
def Branch.str : Branch → String
  | .stored => "stored" | .fixed => "fixed" | .dyn => "dynamic"

def reps : Nat := 5

structure FileResult where
  name : String
  size : Nat
  freqsMBps : Float
  dynSizeMBps : Float
  fixedSizeMBps : Float
  fixedEmitMBps : Float
  baseMBps : Float
  branch : Branch
  fixedBytes : Nat
  dynBytes : Nat
  storedBytes : Nat
  outBytes : Nat

def analyzeFile (name : String) (data : ByteArray) : IO FileResult := do
  let size := data.size
  -- Match once, outside every timed region: the emit cost is what we attribute.
  let ptokens := lzMatchP data 1
  let _ ← IO.println s!"  {name}: {size} bytes, {ptokens.size} tokens — timing…"

  -- (1) frequency walk. Sum the frequency arrays (not `.size`, which is the
  -- constant 286/30 and would let the walk be elided) to keep the fold live.
  let freqsNs ← measureNs size reps fun _ =>
    let f := tokenFreqsPTA ptokens
    f.1.foldl (· + ·) 0 + f.2.foldl (· + ·) 0
  -- (2) dynamic sizing/tree build (freqs → code lengths → header plan → dyn size)
  let dynSizeNs ← measureNs size reps fun _ =>
    let f := tokenFreqsPTA ptokens
    let lens := dynamicCodeLengths f.1 f.2
    let plan := dynHeaderCodes lens.1 lens.2
    have hcl : plan.clCodes.size ≥ 19 :=
      Nat.le_of_eq (dynHeaderCodes_clCodes_size lens.1 lens.2).symm
    dynBlockBytesWith f.1 f.2 lens.1 lens.2 plan hcl
  -- (3) fixed sizer
  let fixedSizeNs ← measureNs size reps fun _ =>
    let f := tokenFreqsPTA ptokens
    fixedBlockBytes f.1 f.2
  -- (4) fixed-only emit (token walk + BitWriter)
  let fixedEmitNs ← measureNs size reps fun _ =>
    (deflateFixedBlockP data ptokens).size
  -- (5) full base candidate
  let baseNs ← measureNs size reps fun _ =>
    (deflateRawBaseP data ptokens).size

  -- (6) which branch the base dispatch actually takes, and the sizes
  let f := tokenFreqsPTA ptokens
  let lens := dynamicCodeLengths f.1 f.2
  let plan := dynHeaderCodes lens.1 lens.2
  have hcl : plan.clCodes.size ≥ 19 :=
    Nat.le_of_eq (dynHeaderCodes_clCodes_size lens.1 lens.2).symm
  let fixedBytes := fixedBlockBytes f.1 f.2
  let dynBytes := dynBlockBytesWith f.1 f.2 lens.1 lens.2 plan hcl
  let storedBytes := storedBlockBytes data
  let branch : Branch :=
    if storedBytes < (if fixedBytes < dynBytes then fixedBytes else dynBytes) then .stored
    else if fixedBytes < dynBytes then .fixed else .dyn
  let outBytes := (deflateRawBaseP data ptokens).size

  return {
    name, size,
    freqsMBps := round1 (mbps size freqsNs),
    dynSizeMBps := round1 (mbps size dynSizeNs),
    fixedSizeMBps := round1 (mbps size fixedSizeNs),
    fixedEmitMBps := round1 (mbps size fixedEmitNs),
    baseMBps := round1 (mbps size baseNs),
    branch, fixedBytes, dynBytes, storedBytes, outBytes
  }

def main (args : List String) : IO Unit := do
  let dir := args.headD "bench/corpora/silesia"
  let root := System.FilePath.mk dir
  unless ← root.pathExists do
    IO.eprintln s!"corpus dir not found: {root}"
    return
  let entries ← root.readDir
  let paths := (entries.map (·.path)).qsort (fun a b => a.toString < b.toString)
  let mut acc : List FileResult := []
  for path in paths do
    unless ← path.isDir do
      let data ← IO.FS.readBinFile path
      let name := path.fileName.getD ""
      acc := (← analyzeFile name data) :: acc
  let results := acc.reverse

  -- Markdown attribution table
  IO.println ""
  IO.println "## Step-1 attribution (L1, tokens held constant, Silesia)"
  IO.println ""
  IO.println "MB/s vs uncompressed bytes; median-of-5. `(1)` freqs, `(2)` freqs+dyn sizing+tree,"
  IO.println "`(3)` fixed sizing, `(4)` fixed-only emit, `(5)` full base candidate."
  IO.println ""
  IO.println "| file | size | (1) freqs | (2) freqs+dynSize | (3) fixSize | (4) fixEmit | (5) base | branch | fixed B | dyn B |"
  IO.println "|------|------|-----------|-------------|-------------|-------------|----------|--------|---------|-------|"
  for r in results do
    IO.println s!"| {r.name} | {r.size} | {r.freqsMBps} | {r.dynSizeMBps} | {r.fixedSizeMBps} | {r.fixedEmitMBps} | {r.baseMBps} | {r.branch.str} | {r.fixedBytes} | {r.dynBytes} |"
  IO.println ""
  IO.println "Ratios of current L1 base output (out/size) and fixed-only give-up:"
  IO.println ""
  IO.println "| file | base ratio | fixed-only ratio | dyn wins by |"
  IO.println "|------|-----------|------------------|-------------|"
  for r in results do
    let baseRatio := round4 (r.outBytes.toFloat / (max r.size 1).toFloat)
    -- fixed-only block bytes ≈ fixedBytes (single fixed block, +header handled inside)
    let fixedRatio := round4 (r.fixedBytes.toFloat / (max r.size 1).toFloat)
    let dynWin := if r.fixedBytes ≥ r.dynBytes then
        round4 ((r.fixedBytes - r.dynBytes).toFloat / (max r.dynBytes 1).toFloat * 100.0)
      else 0.0
    IO.println s!"| {r.name} | {baseRatio} | {fixedRatio} | {dynWin}% |"
where
  round4 (f : Float) : Float := (f * 10000.0).round / 10000.0
