import ZipTest.Helpers
import ZipTest.BenchHelpers
import Zip.Native.ZstdFrame

/-! Zstd decompression throughput benchmarks: FFI compress → native/FFI decompress.
    Covers 4 data patterns × 4 sizes (1KB–1MB) at compression levels 1, 3, 9, 19.
    Reports compression ratio, native decompress MB/s, and FFI decompress MB/s.
    Uses multi-iteration methodology with warm-up for stable measurements. -/

namespace ZipTest.ZstdDecompressBench

/-- Run native Zstd decompression `iters` times, return total elapsed nanoseconds. -/
private def benchNative (compressed : ByteArray) (iters : Nat) : IO Nat := do
  let start ← IO.monoNanosNow
  for _ in [:iters] do
    let _ ← forceEval (match Zip.Native.decompressZstd compressed with
      | .ok r => r | .error _ => ByteArray.empty)
  let stop ← IO.monoNanosNow
  return stop - start

/-- Run FFI Zstd decompression `iters` times, return total elapsed nanoseconds. -/
private def benchFFI (compressed : ByteArray) (iters : Nat) : IO Nat := do
  let start ← IO.monoNanosNow
  for _ in [:iters] do
    let _ ← forceEval (← Zstd.decompress compressed)
  let stop ← IO.monoNanosNow
  return stop - start

def tests : IO Unit := do
  IO.println "  ZstdDecompressBench tests..."

  let pats := #[("constant", mkConstantData), ("cyclic", mkCyclicData),
                ("prng", mkPrngData), ("text", mkTextData)]
  let sizes := #[1024, 16384, 131072, 1048576]
  let levels : Array UInt8 := #[1, 3, 9, 19]

  IO.println "    --- Zstd decompression throughput (native vs FFI, multi-iteration) ---"
  IO.println s!"      {pad "Size" 6} {pad "Pattern" 9} {pad "Level" 6} {pad "Ratio" 6} {pad "Iters" 6} {pad "Native" 16} {pad "FFI" 16}"
  for size in sizes do
    for (pname, pgen) in pats do
      let data := pgen size
      for level in levels do
        let compressed ← Zstd.compress data level
        let ratio := fmtRatio compressed.size data.size
        let iters := calibrateIters size

        -- Verify correctness before benchmarking
        let nd := match Zip.Native.decompressZstd compressed with
          | .ok r => r | .error _ => ByteArray.empty
        unless nd == data do
          IO.eprintln s!"      WARN: native content mismatch at {sizeName size} {pname} lvl={level} (got {nd.size} bytes, expected {data.size})"
        let fd ← Zstd.decompress compressed
        unless fd == data do
          throw (IO.userError s!"zstd FFI roundtrip: {sizeName size} {pname} lvl={level}")

        -- Warm-up iteration
        let _ ← benchNative compressed 1
        let _ ← benchFFI compressed 1

        -- Timed runs
        let nElapsed ← benchNative compressed iters
        let fElapsed ← benchFFI compressed iters

        -- Per-iteration averages
        let nAvg := nElapsed / iters
        let fAvg := fElapsed / iters

        IO.println s!"      {pad (sizeName size) 6} {pad pname 9} lvl={pad (toString level) 2}  {pad ratio 6} {pad (toString iters) 6} native={pad (fmtMs nAvg ++ "ms") 10} ({fmtMBps size nAvg} MB/s)  ffi={pad (fmtMs fAvg ++ "ms") 10} ({fmtMBps size fAvg} MB/s)"

  IO.println "  ZstdDecompressBench tests passed."

end ZipTest.ZstdDecompressBench
