import Zip

/-! Wave-0 profiling driver (NOT committed): per-phase timing of `deflateRaw`
    at every level 1–9 plus decode, on real corpus files. Defeats Lean's
    laziness per the track-d-state methodology: the input is perturbed one
    byte per rep, and every phase result flows through an IO-sequenced sink. -/

open Zip.Native.Deflate Zip.Native

def mono : IO Nat := IO.monoNanosNow

/-- Time `reps` runs of `act` (each receives the rep index for perturbation);
    returns total ms. The returned Nat from `act` is accumulated into a sink
    printed at the end so nothing is dead code. -/
def timeIt (reps : Nat) (act : Nat → IO Nat) : IO Float := do
  let t0 ← mono
  let mut sink := 0
  for i in [0:reps] do
    sink := sink + (← act i)
  let t1 ← mono
  if sink == 42424242 then IO.println "(sink)"
  return (Float.ofNat (t1 - t0)) / 1e6 / (Float.ofNat reps)

def perturb (data : ByteArray) (i : Nat) : ByteArray :=
  let j := (i * 7919) % data.size
  data.set! j (data[j]! + 1)

def fmt (x : Float) : String :=
  let y := (x * 100).toUInt64.toNat
  s!"{y / 100}.{(y % 100) / 10}{y % 10}"

def profileFile (name : String) (path : String) (reps repsSlow : Nat) : IO Unit := do
  let data ← IO.FS.readBinFile path
  let mb := Float.ofNat data.size / 1e6
  IO.println s!"\n=== {name} ({data.size} bytes) — per-phase ms (and MB/s for full) ==="
  IO.println "lvl   match  freqs   lens   emit  | base SCsplit AtSplit optimal |  full  MB/s | decode MB/s"
  for lv in [1, 2, 3, 4, 5, 6, 7, 8, 9] do
    let level := UInt8.ofNat lv
    let r := if lv ≥ 7 then repsSlow else reps
    -- matcher
    let tMatch ← timeIt r fun i => do
      let d := perturb data i
      pure (lzMatch d level).size
    -- tokenFreqs (matcher recomputed inside but subtracted via tMatch)
    let toks := lzMatch data level
    let tFreqs ← timeIt r fun i => do
      pure ((tokenFreqs (toks.push (.literal (UInt8.ofNat i)))).1)[i % 286]!
    -- dynamicCodeLengths
    let f := tokenFreqs toks
    let tLens ← timeIt r fun i => do
      pure (dynamicCodeLengths (f.1.set! (i % 256) (f.1[i % 256]! + 1)) f.2).1.length
    -- single dynamic block emit (includes freqs+lens internally; report raw)
    let tEmit ← timeIt r fun i => do
      pure (deflateDynamicBlock data (toks.push (.literal (UInt8.ofNat i)))).size
    -- candidates (only meaningful at ≥7, but cheap enough to time at all levels)
    let tBase ← timeIt r fun i => do
      pure (deflateRawBase (perturb data i) level).size
    let mut tSC := 0.0
    let mut tAt := 0.0
    let mut tOpt := 0.0
    if lv ≥ 7 then
      tSC ← timeIt repsSlow fun i => do
        pure (deflateDynamicBlocksSC (perturb data i) splitChunkSize level).size
      tAt ← timeIt repsSlow fun i => do
        pure (deflateDynamicBlocksSharedAt (perturb data i) chooseSplitsArbitrated level).size
    if lv == 9 then
      tOpt ← timeIt repsSlow fun i => do
        pure (deflateDynamicBlocksOptimal (perturb data i) sharedTokChunk).size
    -- full
    let tFull ← timeIt r fun i => do
      pure (deflateRaw (perturb data i) level).size
    let out := deflateRaw data level
    let tDec ← timeIt reps fun _ => do
      match Inflate.inflate out (data.size + 1) with
      | .ok d => pure d.size
      | .error _ => pure 0
    let cMBs := mb / (tFull / 1000)
    let dMBs := mb / (tDec / 1000)
    IO.println s!"{lv}   {fmt tMatch}  {fmt tFreqs}  {fmt tLens}  {fmt tEmit}  | {fmt tBase} {fmt tSC} {fmt tAt} {fmt tOpt} |  {fmt tFull}  {fmt cMBs} | {fmt tDec} {fmt dMBs}"

def main (args : List String) : IO Unit := do
  let quick := args.contains "--quick"
  profileFile "alice29.txt" "bench/corpora/canterbury/alice29.txt" (if quick then 3 else 10) (if quick then 1 else 3)
  unless quick do
    profileFile "silesia/dickens" "bench/corpora/silesia/dickens" 2 1
