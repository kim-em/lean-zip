import Zip
/-! # Fast-L1 matcher-policy sweep (issue #2726, candidate A)

For each Silesia file and each `(chainDepth, insertCap)` config, measure the
*matcher* throughput (`lz77ChainIterP`, greedy — the level 1-3 `deflate_fast`
arm), the *true* end-to-end throughput (match + emit fused, directly timing
`deflateRawBaseP data (lz77ChainIterP ...)` so the token-count coupling is
captured, not estimated), and the resulting base ratio. The fast corner is read
off the end-to-end column directly.

Run: `lake exe l1-sweep [corpusDir]`.
-/

open Zip.Native.Deflate

def medianNs (xs : List Nat) : Nat :=
  let a := xs.toArray.qsort (· < ·)
  if a.size == 0 then 0 else a[a.size / 2]!

def itersFor (size : Nat) : Nat :=
  if size ≤ 16384 then 50 else if size ≤ 262144 then 10
  else if size ≤ 1048576 then 3 else 1

@[noinline] def timePerOp (iters : Nat) (op : Unit → Nat) : IO Nat := do
  let t0 ← IO.monoNanosNow
  let mut acc : Nat := 0
  for _ in [:iters] do
    acc := acc + op ()
  let t1 ← IO.monoNanosNow
  if acc == 0 then IO.eprintln "unreachable"
  return (t1 - t0) / (max iters 1)

def measureNs (size reps : Nat) (op : Unit → Nat) : IO Nat := do
  let iters := itersFor size
  let mut ts : List Nat := []
  for _ in [:reps] do ts := (← timePerOp iters op) :: ts
  return medianNs ts

def mbps (bytes nsPerOp : Nat) : Float :=
  if nsPerOp == 0 then 0.0
  else (bytes.toFloat / (1024.0 * 1024.0)) / (nsPerOp.toFloat / 1.0e9)

def round1 (f : Float) : Float := (f * 10.0).round / 10.0
def round4 (f : Float) : Float := (f * 10000.0).round / 10000.0
def reps : Nat := 5

/-- The `(chainDepth, insertCap)` configs to sweep. `(8,16)` is today's L1;
    `(4,·)` and `(2,·)` are the zlib `deflate_fast` neighbourhood; a raised
    `insertCap` (insert every interior position) trades speed for ratio;
    a lowered one defers more insertions (faster match, worse ratio). -/
def configs : List (Nat × Nat) :=
  [(8, 16), (4, 16), (8, 4), (4, 4), (4, 2), (2, 2)]

/-- Distinct symbol for the ratio path so CSE cannot merge it with the timed
    calls (which would make the work appear to run in ~0 ns). -/
@[noinline] def matchForRatio (data : ByteArray) (cd ic : Nat) : TokenArray :=
  lz77ChainIterP data cd 32768 ic

structure Cell where
  cd : Nat
  ic : Nat
  matchMBps : Float
  e2eMBps : Float
  ratio : Float

def analyzeFile (name : String) (data : ByteArray) : IO (List Cell) := do
  let size := data.size
  IO.println s!"  {name}: {size} bytes …"
  let mut cells : List Cell := []
  for (cd, ic) in configs do
    -- Matcher throughput alone.
    let matchNs ← measureNs size reps fun _ => (lz77ChainIterP data cd 32768 ic).size
    -- True base-path end-to-end throughput: match *and* emit fused, so the
    -- token-count coupling (a shallower match emits more tokens → slower emit)
    -- is captured, not estimated. This is `deflateRawBase data level` for the
    -- level whose knobs are `(cd, ic)` — i.e. `deflateRaw` minus the
    -- `incompressiblePrescan`/stored-shortcut gate, which does not fire on these
    -- (compressible) Silesia files.
    let e2eNs ← measureNs size reps fun _ =>
      (deflateRawBaseP data (lz77ChainIterP data cd 32768 ic)).size
    let out := (deflateRawBaseP data (matchForRatio data cd ic)).size
    let ratio := out.toFloat / (max size 1).toFloat
    cells := { cd, ic, matchMBps := round1 (mbps size matchNs),
               e2eMBps := round1 (mbps size e2eNs), ratio := round4 ratio } :: cells
  return cells.reverse

def geomean (xs : List Float) : Float :=
  if xs.isEmpty then 0.0
  else Float.exp ((xs.foldl (fun a x => a + Float.log x) 0.0) / xs.length.toFloat)

def main (args : List String) : IO Unit := do
  let dir := args.headD "bench/corpora/silesia"
  let root := System.FilePath.mk dir
  unless ← root.pathExists do IO.eprintln s!"no corpus dir: {root}"; return
  let entries ← root.readDir
  let paths := (entries.map (·.path)).qsort (fun a b => a.toString < b.toString)
  let mut acc : List (String × List Cell) := []
  for path in paths do
    unless ← path.isDir do
      let data ← IO.FS.readBinFile path
      let name := path.fileName.getD ""
      acc := (name, ← analyzeFile name data) :: acc
  let perFile := acc.reverse

  IO.println ""
  IO.println "## Candidate A: L1 matcher-policy sweep (Silesia)"
  IO.println ""
  for (cd, ic) in configs do
    let cells := perFile.filterMap fun (_, cs) => cs.find? (fun c => c.cd == cd && c.ic == ic)
    let gRatio := round4 (geomean (cells.map (·.ratio)))
    let gE2e := round1 (geomean (cells.map (·.e2eMBps)))
    let gMatch := round1 (geomean (cells.map (·.matchMBps)))
    let maxRatio := round4 (cells.map (·.ratio) |>.foldl (fun a x => if x > a then x else a) 0.0)
    let icS := if ic ≥ 1000000000 then "∞" else toString ic
    IO.println s!"- **cd={cd}, ic={icS}**: geomean ratio {gRatio}, max-file ratio {maxRatio}, match {gMatch} MB/s, **e2e {gE2e} MB/s**"
  IO.println ""
  IO.println "Per-file end-to-end MB/s (ratio) (rows=file, cols=config):"
  IO.print "| file |"
  for (cd, ic) in configs do
    let icS := if ic ≥ 1000000000 then "∞" else toString ic
    IO.print s!" cd{cd}/ic{icS} |"
  IO.println ""
  IO.print "|------|"
  for _ in configs do IO.print "------|"
  IO.println ""
  for (name, cs) in perFile do
    IO.print s!"| {name} |"
    for c in cs do IO.print s!" {c.e2eMBps} ({c.ratio}) |"
    IO.println ""
