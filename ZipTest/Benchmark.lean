import ZipTest.Helpers
import ZipTest.BenchHelpers
import Zip.Native.Inflate

/-! Decompression throughput benchmark: native Lean DEFLATE vs FFI zlib.

    This is the Track D1 baseline benchmark. It compresses representative
    inputs using FFI zlib, then measures wall-clock decompression time for
    native Lean inflate vs FFI zlib inflate over multiple iterations.
    Reports throughput in MB/s. -/

namespace ZipTest.Benchmark

/-- Run decompression `iters` times, return total elapsed nanoseconds. -/
private def benchNative (compressed : ByteArray) (iters : Nat) : IO Nat := do
  let start ← IO.monoNanosNow
  for _ in [:iters] do
    let _ ← forceEval (match Zip.Native.Inflate.inflate compressed with
      | .ok r => r | .error _ => ByteArray.empty)
  let stop ← IO.monoNanosNow
  return stop - start

/-- Run FFI decompression `iters` times, return total elapsed nanoseconds. -/
private def benchFFI (compressed : ByteArray) (iters : Nat) : IO Nat := do
  let start ← IO.monoNanosNow
  for _ in [:iters] do
    let _ ← forceEval (← RawDeflate.decompress compressed)
  let stop ← IO.monoNanosNow
  return stop - start

def tests : IO Unit := do
  IO.println "  Benchmark: DEFLATE decompression throughput (Track D1)..."

  -- Data patterns: text (compressible) and prng (less compressible)
  let pats := #[("text", mkTextData), ("prng", mkPrngData)]
  -- Sizes: 16KB, 64KB, 256KB
  let sizes := #[16384, 65536, 262144]
  -- Compression levels
  let levels : Array UInt8 := #[1, 6]
  -- Iterations for stable timing
  let iters := 5

  IO.println s!"    Iterations per measurement: {iters}"
  IO.println s!"    {pad "Size" 6} {pad "Pattern" 9} {pad "Level" 6} {pad "Ratio" 8} {pad "Native" 20} {pad "FFI" 20} {pad "Slowdown" 8}"

  for size in sizes do
    for (pname, pgen) in pats do
      let data := pgen size
      for level in levels do
        -- Compress with FFI
        let compressed ← RawDeflate.compress data level
        let ratio := if data.size == 0 then "N/A"
          else
            let r10 := compressed.size * 1000 / data.size
            let whole := r10 / 10
            let frac := r10 % 10
            s!"{whole}.{frac}%"

        -- Verify correctness before benchmarking
        match Zip.Native.Inflate.inflate compressed with
        | .ok r => unless r == data do
            throw (IO.userError s!"native inflate mismatch: {sizeName size} {pname} lvl={level}")
        | .error e => throw (IO.userError s!"native inflate error: {e}")
        let ffiResult ← RawDeflate.decompress compressed
        unless ffiResult == data do
          throw (IO.userError s!"ffi inflate mismatch: {sizeName size} {pname} lvl={level}")

        -- Benchmark: multiple iterations
        let nElapsed ← benchNative compressed iters
        let fElapsed ← benchFFI compressed iters

        -- Per-iteration averages
        let nAvg := nElapsed / iters
        let fAvg := fElapsed / iters

        -- Slowdown factor (native / FFI), with one decimal
        let slowdown := if fAvg == 0 then "∞"
          else
            let s10 := nAvg * 10 / fAvg
            let whole := s10 / 10
            let frac := s10 % 10
            s!"{whole}.{frac}x"

        IO.println s!"    {pad (sizeName size) 6} {pad pname 9} {pad s!"lvl={level}" 6} {pad ratio 8} native={pad (fmtMs nAvg ++ "ms") 10} ({fmtMBps size nAvg} MB/s)  ffi={pad (fmtMs fAvg ++ "ms") 10} ({fmtMBps size fAvg} MB/s)  {slowdown}"

  IO.println "  Benchmark tests passed."

end ZipTest.Benchmark
