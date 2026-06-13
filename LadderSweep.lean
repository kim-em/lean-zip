import Zip

/-! #2541 ladder sweep (NOT committed): for each level 1–6, sweep
    `chainDepth`/`insertCap` candidates over corpus files, measuring emitted
    size (via the real `deflateRawBaseTokens` single-block dispatch — the path
    levels 1–6 actually take) and matcher+emit wall time. CSV:
    `<file>,<level>,<depth>,<cap>,<size>,<ms>` (no header). The input is
    perturbed per rep and results flow through a sink (laziness discipline
    per plans/track-d-state.md). -/

open Zip.Native.Deflate

def perturb (data : ByteArray) (i : Nat) : ByteArray :=
  let j := (i * 7919) % data.size
  data.set! j (data[j]! + 1)

/-- The deployed per-level matcher with knob overrides (mirrors `lzMatch`). -/
def matchWith (data : ByteArray) (level : UInt8) (depth cap : Nat) : Array LZ77Token :=
  if 4 ≤ level then lz77ChainLazyIter data depth 32768 cap
  else lz77ChainIter data depth 32768 cap

def grid (level : UInt8) : List (Nat × Nat) :=
  let d := chainDepth level
  let c := insertCap level
  let depths := [d / 4, d / 2, d, d * 2].filter (· ≥ 2) |>.eraseDups
  let caps := if level ≤ 3 then [c / 2, c, c * 2].filter (· ≥ 8) |>.eraseDups
              else [64, 256, c].eraseDups
  depths.flatMap fun dd => caps.map fun cc => (dd, cc)

def main (args : List String) : IO Unit := do
  let reps := 5
  for path in args do
    let data ← IO.FS.readBinFile path
    let name := (path.splitOn "/").getLast!
    for lv in [1, 2, 3, 4, 5, 6] do
      let level := UInt8.ofNat lv
      for (d, c) in grid level do
        let t0 ← IO.monoNanosNow
        let mut sink := 0
        let mut size := 0
        for i in [0:reps] do
          let pd := perturb data i
          let out := deflateRawBaseTokens pd (matchWith pd level d c)
          sink := sink + out.size
          size := out.size
        let t1 ← IO.monoNanosNow
        if sink == 1 then IO.println "(sink)"
        let ms := (t1 - t0) / 1000000 / reps
        IO.println s!"{name},{lv},{d},{c},{size},{ms}"
