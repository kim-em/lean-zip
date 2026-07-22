import Zip
/-! # Huffman code-length build microbench (issue #2761)

Times the per-block dynamic-Huffman code-length construction — the hot cluster
on heterogeneous, heavily-split members (mozilla L6) — comparing the spec
`List`-based `computeCodeLengths` against the array twin `computeCodeLengthsN`.

Tokens are matched once per file, split into fixed-size blocks (to mimic the
split-block regime), and each block's `(litFreqs, distFreqs)` is summarised
once. The timed region is only the code-length build over every block's
frequencies, so the measurement isolates exactly the cluster the issue targets.

Run: `lake exe huff-bench [corpusDir]`  (default `bench/corpora/canterbury`).
-/

open Zip.Native.Deflate

@[noinline] def timeNs (iters : Nat) (op : Unit → Nat) : IO Nat := do
  let t0 ← IO.monoNanosNow
  let mut acc : Nat := 0
  for _ in [:iters] do
    acc := acc + op ()
  let t1 ← IO.monoNanosNow
  if acc == 0 then IO.eprintln "unreachable"
  return (t1 - t0) / (max iters 1)

def medianNs (xs : List Nat) : Nat :=
  let a := xs.toArray.qsort (· < ·)
  if a.size == 0 then 0 else a[a.size / 2]!

/-- Per-block frequency summaries for a file: split the packed token stream into
    `blockToks`-sized blocks and summarise each. -/
def blockFreqs (ptokens : Array UInt32) (blockToks : Nat) : Array (Array Nat × Array Nat) := Id.run do
  let mut out : Array (Array Nat × Array Nat) := #[]
  let mut i := 0
  while i < ptokens.size do
    let j := min (i + blockToks) ptokens.size
    out := out.push (tokenFreqsP (ptokens.extract i j))
    i := j
  return out

/-- Sum of all built lengths (keeps the build live and unelided). `@[noinline]`
    and a per-call `bump` folded into `litFreqs[0]` so the timing loop cannot
    CSE the call across iterations/reps. -/
@[noinline] def sumListBuild (blocks : Array (Array Nat × Array Nat)) (bump : Nat) : Nat := Id.run do
  let mut acc := 0
  for (lf, df) in blocks do
    let lf := lf.set! 0 (lf.getD 0 0 + bump)
    acc := acc + (Huffman.Spec.computeCodeLengths (freqsToPairs lf) 286 15).foldl (· + ·) 0
    acc := acc + (Huffman.Spec.computeCodeLengths (freqsToPairs df) 30 15).foldl (· + ·) 0
  return acc

@[noinline] def sumArrBuild (blocks : Array (Array Nat × Array Nat)) (bump : Nat) : Nat := Id.run do
  let mut acc := 0
  for (lf, df) in blocks do
    let lf := lf.set! 0 (lf.getD 0 0 + bump)
    acc := acc + (Huffman.Spec.computeCodeLengthsN (freqsToPairs lf) 286 15).foldl (· + ·) 0
    acc := acc + (Huffman.Spec.computeCodeLengthsN (freqsToPairs df) 30 15).foldl (· + ·) 0
  return acc

def reps : Nat := 7

def analyzeFile (name : String) (data : ByteArray) (blockToks : Nat) : IO Unit := do
  let ptokens := (lzMatchP data 6).toArray
  let blocks := blockFreqs ptokens blockToks
  -- Replicate the file's blocks so a single build pass is milliseconds (the
  -- split-block regime of a large member), and time single passes (`iters = 1`)
  -- so nothing loop-invariant can be hoisted across iterations.
  let target := 4000
  let copies := max 1 ((target + blocks.size) / max 1 blocks.size)
  let big := (Array.replicate copies blocks).flatten
  let okList := sumListBuild big 7
  let okArr := sumArrBuild big 7
  let mut tl : List Nat := []
  let mut ta : List Nat := []
  for k in [:reps] do
    tl := (← timeNs 1 (fun _ => sumListBuild big (k + 1))) :: tl
    ta := (← timeNs 1 (fun _ => sumArrBuild big (k + 1))) :: ta
  let ml := medianNs tl
  let ma := medianNs ta
  let speedup := if ma == 0 then 0.0 else ml.toFloat / ma.toFloat
  let perBuildL := ml / (max 1 big.size)
  let perBuildA := ma / (max 1 big.size)
  let agree := if okList == okArr then "ok" else "MISMATCH"
  IO.println s!"| {name} | {data.size} | {big.size} | {ml/1000} | {ma/1000} | {perBuildL} | {perBuildA} | {(speedup * 100.0).round / 100.0}x | {agree} |"

def main (args : List String) : IO Unit := do
  let dir := args.headD "bench/corpora/canterbury"
  let blockToks := (args[1]?).bind (·.toNat?) |>.getD 2048
  let root := System.FilePath.mk dir
  unless ← root.pathExists do
    IO.eprintln s!"corpus dir not found: {root}"; return
  IO.println s!"## Huffman code-length build: List `computeCodeLengths` vs array `computeCodeLengthsN`"
  IO.println s!"(tokens matched once at L6, {blockToks} tokens/block; median-of-{reps} ns for the build over all blocks)"
  IO.println ""
  IO.println "| file | bytes | blocks | List µs | Array µs | List ns/blk | Array ns/blk | speedup | agree |"
  IO.println "|------|-------|--------|---------|----------|-------------|--------------|---------|-------|"
  let entries ← root.readDir
  let paths := (entries.map (·.path)).qsort (fun a b => a.toString < b.toString)
  for path in paths do
    unless ← path.isDir do
      let data ← IO.FS.readBinFile path
      analyzeFile (path.fileName.getD "") data blockToks
