import ZipTest.Helpers
import Zip.Native.Inflate
import Zip.Native.Gzip

/-! Compression throughput and ratio benchmarks: native Lean compressor vs FFI (zlib).
    Covers raw deflate, gzip, and zlib formats at levels 0, 1, and 6.

    Levels 0 (stored) and 1 (greedy) use iterative LZ77 and support large inputs.
    Levels 2+ (lazy/dynamic) still use non-tail-recursive LZ77 and are capped at
    32KB to avoid stack overflow. -/

namespace ZipTest.NativeCompressBench

private def pad (s : String) (w : Nat) : String :=
  s ++ String.ofList (List.replicate (w - min w s.length) ' ')

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

@[noinline] private def forceEval (b : ByteArray) : IO ByteArray := pure b

def tests : IO Unit := do
  IO.println "  NativeCompressBench tests..."
  let pats := #[("constant", mkConstantData), ("cyclic", mkCyclicData), ("prng", mkPrngData)]
  -- Small sizes: all levels (0, 1, 6). Large sizes: levels 0 and 1 only
  -- (lazy/dynamic LZ77 is still non-tail-recursive and overflows above ~50KB).
  let smallSizes := #[1024, 4096, 16384, 32768]
  let allLevels : Array UInt8 := #[0, 1, 6]
  let largeSizes := #[65536, 131072, 262144]
  let safeLevels : Array UInt8 := #[0, 1]

  -- Raw deflate
  IO.println "    --- raw deflate compression (native vs FFI) ---"
  for (sizes, levels) in [(smallSizes, allLevels), (largeSizes, safeLevels)] do
   for size in sizes do
    for (pname, pgen) in pats do
      let data := pgen size
      for level in levels do
        let s1 ← IO.monoNanosNow
        let nc ← forceEval (Zip.Native.Deflate.deflateRaw data level)
        let e1 ← IO.monoNanosNow
        let s2 ← IO.monoNanosNow
        let _fc ← RawDeflate.compress data level
        let e2 ← IO.monoNanosNow
        match Zip.Native.Inflate.inflate nc with
        | .ok r => unless r == data do
            throw (IO.userError s!"deflate roundtrip: {sizeName size} {pname} lvl={level}")
        | .error e => throw (IO.userError e)
        IO.println s!"      {pad (sizeName size) 6} {pad pname 9} lvl={level}  native={pad (fmtMs (e1 - s1) ++ "ms") 10} ffi={fmtMs (e2 - s2)}ms"

  -- Gzip
  IO.println "    --- gzip compression (native vs FFI) ---"
  for (sizes, levels) in [(smallSizes, allLevels), (largeSizes, safeLevels)] do
   for size in sizes do
    for (pname, pgen) in pats do
      let data := pgen size
      for level in levels do
        let s1 ← IO.monoNanosNow
        let nc ← forceEval (Zip.Native.GzipEncode.compress data level)
        let e1 ← IO.monoNanosNow
        let s2 ← IO.monoNanosNow
        let _fc ← Gzip.compress data level
        let e2 ← IO.monoNanosNow
        match Zip.Native.GzipDecode.decompress nc with
        | .ok r => unless r == data do
            throw (IO.userError s!"gzip roundtrip: {sizeName size} {pname} lvl={level}")
        | .error e => throw (IO.userError e)
        IO.println s!"      {pad (sizeName size) 6} {pad pname 9} lvl={level}  native={pad (fmtMs (e1 - s1) ++ "ms") 10} ffi={fmtMs (e2 - s2)}ms"

  -- Zlib
  IO.println "    --- zlib compression (native vs FFI) ---"
  for (sizes, levels) in [(smallSizes, allLevels), (largeSizes, safeLevels)] do
   for size in sizes do
    for (pname, pgen) in pats do
      let data := pgen size
      for level in levels do
        let s1 ← IO.monoNanosNow
        let nc ← forceEval (Zip.Native.ZlibEncode.compress data level)
        let e1 ← IO.monoNanosNow
        let s2 ← IO.monoNanosNow
        let _fc ← Zlib.compress data level
        let e2 ← IO.monoNanosNow
        match Zip.Native.ZlibDecode.decompress nc with
        | .ok r => unless r == data do
            throw (IO.userError s!"zlib roundtrip: {sizeName size} {pname} lvl={level}")
        | .error e => throw (IO.userError e)
        IO.println s!"      {pad (sizeName size) 6} {pad pname 9} lvl={level}  native={pad (fmtMs (e1 - s1) ++ "ms") 10} ffi={fmtMs (e2 - s2)}ms"

  -- Compression ratio (32KB all levels, 256KB levels 0-1)
  IO.println "    --- compression ratio (native/FFI) ---"
  IO.println s!"      {pad "Size" 6} {pad "Format" 8} {pad "Pattern" 9} {pad "Level" 6} {pad "Native" 10} {pad "FFI" 10} Ratio"
  for (ratioSize, ratioLevels) in [((32768 : Nat), allLevels), (262144, safeLevels)] do
   for (pname, pgen) in pats do
    let data := pgen ratioSize
    for level in ratioLevels do
      let ncR ← forceEval (Zip.Native.Deflate.deflateRaw data level)
      let fcR ← RawDeflate.compress data level
      let rR := if fcR.size == 0 then 0.0 else ncR.size.toFloat / fcR.size.toFloat
      let sR := let s := s!"{rR}"; if s.length > 6 then s.take 6 else s
      IO.println s!"      {pad (sizeName ratioSize) 6} {pad "raw" 8} {pad pname 9} {pad s!"lvl={level}" 6} {pad (toString ncR.size) 10} {pad (toString fcR.size) 10} {sR}"
      let ncG ← forceEval (Zip.Native.GzipEncode.compress data level)
      let fcG ← Gzip.compress data level
      let rG := if fcG.size == 0 then 0.0 else ncG.size.toFloat / fcG.size.toFloat
      let sG := let s := s!"{rG}"; if s.length > 6 then s.take 6 else s
      IO.println s!"      {pad (sizeName ratioSize) 6} {pad "gzip" 8} {pad pname 9} {pad s!"lvl={level}" 6} {pad (toString ncG.size) 10} {pad (toString fcG.size) 10} {sG}"
      let ncZ ← forceEval (Zip.Native.ZlibEncode.compress data level)
      let fcZ ← Zlib.compress data level
      let rZ := if fcZ.size == 0 then 0.0 else ncZ.size.toFloat / fcZ.size.toFloat
      let sZ := let s := s!"{rZ}"; if s.length > 6 then s.take 6 else s
      IO.println s!"      {pad (sizeName ratioSize) 6} {pad "zlib" 8} {pad pname 9} {pad s!"lvl={level}" 6} {pad (toString ncZ.size) 10} {pad (toString fcZ.size) 10} {sZ}"

  IO.println "  NativeCompressBench tests passed."

end ZipTest.NativeCompressBench
