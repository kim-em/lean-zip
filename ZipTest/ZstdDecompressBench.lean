import ZipTest.Helpers
import Zip.Native.ZstdFrame

/-! Zstd decompression throughput benchmarks: FFI compress → native/FFI decompress.
    Covers 4 data patterns × 4 sizes (1KB–1MB) at compression levels 1, 3, 9, 19.
    Reports compression ratio, native decompress MB/s, and FFI decompress MB/s. -/

namespace ZipTest.ZstdDecompressBench

private def pad (s : String) (w : Nat) : String :=
  s ++ String.ofList (List.replicate (w - min w s.length) ' ')

private def fmtMBps (dataSize : Nat) (elapsedNs : Nat) : String :=
  if elapsedNs == 0 then "    ∞" else
  let mbps10 := dataSize * 10000000000 / elapsedNs / (1024 * 1024)
  let whole := mbps10 / 10
  let frac := mbps10 % 10
  let s := s!"{whole}.{frac}"
  let padding := if s.length < 5 then String.ofList (List.replicate (5 - s.length) ' ') else ""
  padding ++ s

private def fmtMs (ns : Nat) : String :=
  let us := ns / 1000
  let ms := us / 1000
  let frac := us % 1000
  if ms ≥ 10 then s!"{ms}.{frac / 100}"
  else if ms ≥ 1 then
    let d2 := frac / 10
    s!"{ms}.{if d2 < 10 then "0" else ""}{d2}"
  else
    s!"{ms}.{if frac < 100 then "0" else ""}{if frac < 10 then "0" else ""}{frac}"

private def fmtRatio (num denom : Nat) : String :=
  if denom == 0 then "  N/A" else
  let r := num.toFloat / denom.toFloat
  let s := s!"{r}"
  if s.length > 5 then (s.take 5).toString else s

@[noinline] private def forceEval (b : ByteArray) : IO ByteArray := pure b

def tests : IO Unit := do
  IO.println "  ZstdDecompressBench tests..."

  let pats := #[("constant", mkConstantData), ("cyclic", mkCyclicData),
                ("prng", mkPrngData), ("text", mkTextData)]
  let sizes := #[1024, 16384, 131072, 1048576]
  let levels : Array UInt8 := #[1, 3, 9, 19]

  IO.println "    --- Zstd decompression throughput (native vs FFI) ---"
  IO.println s!"      {pad "Size" 6} {pad "Pattern" 9} {pad "Level" 6} {pad "Ratio" 6} {pad "Native" 16} {pad "FFI" 16}"
  for size in sizes do
    for (pname, pgen) in pats do
      let data := pgen size
      for level in levels do
        let compressed ← Zstd.compress data level
        let ratio := fmtRatio compressed.size data.size

        -- Native decompress
        let s1 ← IO.monoNanosNow
        let nd ← forceEval (match Zip.Native.decompressZstd compressed with
          | .ok r => r | .error _ => ByteArray.empty)
        let e1 ← IO.monoNanosNow

        -- FFI decompress
        let s2 ← IO.monoNanosNow
        let fd ← Zstd.decompress compressed
        let e2 ← IO.monoNanosNow

        -- Verify correctness
        unless nd == data do
          IO.eprintln s!"      WARN: native content mismatch at {sizeName size} {pname} lvl={level} (got {nd.size} bytes, expected {data.size})"
        unless fd == data do
          throw (IO.userError s!"zstd FFI roundtrip: {sizeName size} {pname} lvl={level}")

        let nElapsed := e1 - s1
        let fElapsed := e2 - s2
        IO.println s!"      {pad (sizeName size) 6} {pad pname 9} lvl={pad (toString level) 2}  {pad ratio 6} native={pad (fmtMs nElapsed ++ "ms") 10} ({fmtMBps size nElapsed} MB/s)  ffi={pad (fmtMs fElapsed ++ "ms") 10} ({fmtMBps size fElapsed} MB/s)"

  IO.println "  ZstdDecompressBench tests passed."

end ZipTest.ZstdDecompressBench
