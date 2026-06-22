import Zip.Native.InflateTreeFree
import Zip

/-!
# End-to-end tree-free decode: conformance + benchmark

Compresses each corpus file with the zlib FFI (a format-correct raw-deflate
stream), then decodes it two ways — the verified `Inflate.inflate` (tree + table)
and the prototype `Inflate.inflateTreeFree` (no Huffman tree) — asserts the two
outputs are byte-identical to the original (conformance), and times both with a
paired interleaved measurement (per-file geomean of after/before ratios), so
common-mode machine noise cancels.
-/

open Zip.Native

def corporaDir : System.FilePath := "bench/corpora"

def loadFiles : IO (Array (String × ByteArray)) := do
  let root := corporaDir
  unless ← root.pathExists do
    IO.eprintln s!"no corpora dir: {root}"; return #[]
  let mut out : Array (String × ByteArray) := #[]
  for corpusEntry in (← root.readDir) do
    if ← corpusEntry.path.isDir then
      let corpus := corpusEntry.path.fileName.getD ""
      let files := ((← corpusEntry.path.readDir).map (·.path)).qsort (·.toString < ·.toString)
      for path in files do
        unless ← path.isDir do
          out := out.push (s!"{corpus}/{path.fileName.getD ""}", ← IO.FS.readBinFile path)
  return out

@[noinline] def sink (n : Nat) : IO Nat := pure n

/-- Time one decode (returns output size to defeat DCE). -/
def timeDecode (decode : ByteArray → IO ByteArray) (input : ByteArray) : IO (Nat × Nat) := do
  let t0 ← IO.monoNanosNow
  let out ← decode input
  let t1 ← IO.monoNanosNow
  let _ ← sink out.size
  return (t1 - t0, out.size)

def baselineDecode (input : ByteArray) (origSize : Nat) : IO ByteArray :=
  match Inflate.inflate input (sizeHint := origSize) with
  | .ok b => pure b | .error e => throw (IO.userError s!"baseline: {e}")

def treeFreeDecode (input : ByteArray) : IO ByteArray :=
  match Inflate.inflateTreeFree input with
  | .ok b => pure b | .error e => throw (IO.userError s!"treefree: {e}")

/-- Geometric mean of a list of ratios (×1000 fixed-point for printing). -/
def geomeanX1000 (ratios : Array Float) : Nat :=
  if ratios.isEmpty then 1000
  else
    let logSum := ratios.foldl (fun acc r => acc + Float.log r) 0.0
    let g := Float.exp (logSum / ratios.size.toFloat)
    (g * 1000.0).toUInt64.toNat

/-- Format an ×1000 fixed-point ratio as "D.DDD". -/
def fmtX1000 (g : Nat) : String :=
  let whole := g / 1000
  let frac := g % 1000
  let f := if frac < 10 then s!"00{frac}" else if frac < 100 then s!"0{frac}" else toString frac
  s!"{whole}.{f}x"

def main : IO Unit := do
  let files ← loadFiles
  if files.isEmpty then IO.eprintln "no files"; return
  let level : UInt8 := 6
  let reps := 7
  IO.println s!"Tree-free end-to-end decode: conformance + paired timing (level {level}, {reps} pairs/file)"
  IO.println "  file | size | baseline ns | treefree ns | speedup"
  let mut allRatios : Array Float := #[]
  let mut canRatios : Array Float := #[]
  let mut silRatios : Array Float := #[]
  for (name, data) in files do
    -- format-correct raw-deflate stream via zlib FFI
    let deflated ← RawDeflate.compress data level
    -- conformance: both decoders reproduce the original
    let bOut ← baselineDecode deflated data.size
    let tOut ← treeFreeDecode deflated
    unless bOut == data do throw (IO.userError s!"[{name}] baseline output != original")
    unless tOut == data do throw (IO.userError s!"[{name}] tree-free output != original")
    -- paired interleaved timing
    let mut ratios : Array Float := #[]
    let mut bTotal := 0
    let mut tTotal := 0
    for _ in [:reps] do
      let (bNs, _) ← timeDecode (fun i => baselineDecode i data.size) deflated
      let (tNs, _) ← timeDecode treeFreeDecode deflated
      bTotal := bTotal + bNs
      tTotal := tTotal + tNs
      if tNs > 0 then ratios := ratios.push (bNs.toFloat / tNs.toFloat)
    let g := geomeanX1000 ratios
    allRatios := allRatios ++ ratios
    if name.startsWith "canterbury" then canRatios := canRatios ++ ratios
    if name.startsWith "silesia" then silRatios := silRatios ++ ratios
    IO.println s!"  {name} | {data.size} | {bTotal / reps} | {tTotal / reps} | {fmtX1000 g}"
  let gAll := geomeanX1000 allRatios
  let gCan := geomeanX1000 canRatios
  let gSil := geomeanX1000 silRatios
  IO.println s!"GEOMEAN speedup (treefree vs baseline):"
  IO.println s!"  canterbury: {fmtX1000 gCan}   silesia: {fmtX1000 gSil}   all: {fmtX1000 gAll}"
  IO.println "  (>1.0 = tree-free faster)"
