import Conformance.Helpers
import Conformance.BenchHelpers
import Zip.Native.Parallel

/-! Throughput of the opt-in chunk-parallel encoder
    (`Zip.Native.Deflate.deflateDynamicBlocksSCParallel`) with threading off
    and on, over the patterns `NativeCompressBench` uses.  The two settings are
    proven to emit identical bytes (`deflateDynamicBlocksSCParallel_eq`); this
    checks that at runtime too.  It runs at whatever `LEAN_NUM_THREADS` the
    process was started with, so compare a `LEAN_NUM_THREADS=1` run with a
    `LEAN_NUM_THREADS=4` one to see the scaling. -/

namespace Conformance.ParallelBench

def tests : IO Unit := do
  IO.println "  ParallelBench tests..."
  IO.println "    --- chunk-parallel deflate (par=false vs par=true), lvl=6, 256KB chunks, best of 3 ---"
  let pats := #[("constant", mkConstantData), ("cyclic", mkCyclicData), ("prng", mkPrngData),
                 ("text", mkTextData)]
  let size := 8 * 1024 * 1024
  for (pname, pgen) in pats do
    let data := pgen size
    -- Best of three per setting: one sample on a busy machine can swing ±30%.
    let mut sElapsed := 0
    let mut pElapsed := 0
    for i in [0:3] do
      let s1 ← IO.monoNanosNow
      let seq ← forceEval (Zip.Native.Deflate.deflateDynamicBlocksSCParallel data 262144 6 false)
      let e1 ← IO.monoNanosNow
      let s2 ← IO.monoNanosNow
      let par ← forceEval (Zip.Native.Deflate.deflateDynamicBlocksSCParallel data 262144 6 true)
      let e2 ← IO.monoNanosNow
      unless seq == par do
        throw (IO.userError s!"parallel deflate differs from sequential: {sizeName size} {pname}")
      sElapsed := if i == 0 then e1 - s1 else min sElapsed (e1 - s1)
      pElapsed := if i == 0 then e2 - s2 else min pElapsed (e2 - s2)
    IO.println s!"      {pad (sizeName size) 6} {pad pname 9} seq={pad (fmtMs sElapsed ++ "ms") 10} ({fmtMBps size sElapsed} MB/s)  par={pad (fmtMs pElapsed ++ "ms") 10} ({fmtMBps size pElapsed} MB/s)  speedup={fmtRatio sElapsed pElapsed}x"
  IO.println "  ParallelBench tests passed."

end Conformance.ParallelBench
