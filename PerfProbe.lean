import Zip

/-! W5.P1 probe (NOT committed): run exactly ONE compressor on one input in a
    loop, so an external `perf record` captures a clean single-compressor
    window. Input perturbed per rep (laziness discipline); result sizes
    accumulated as the sink.

    Usage: perf-probe <native|zlib|miniz|libdeflate> <file> <level> <reps> -/

def perturb (data : ByteArray) (i : Nat) : ByteArray :=
  let j := (i * 7919) % data.size
  data.set! j (data[j]! + 1)

def main (args : List String) : IO Unit := do
  let [comp, path, levelS, repsS] := args
    | throw (IO.userError "usage: perf-probe <native|zlib|miniz|libdeflate> <file> <level> <reps>")
  let data ← IO.FS.readBinFile path
  let level := UInt8.ofNat levelS.toNat!
  let reps := repsS.toNat!
  let mut sink := 0
  for i in [0:reps] do
    let d := perturb data i
    let out ← match comp with
      | "native" => pure (Zip.Native.Deflate.deflateRaw d level)
      | "zlib" => RawDeflate.compress d level
      | "miniz" => MinizOxide.compress d level
      | "libdeflate" => Libdeflate.compress d level
      | _ => throw (IO.userError s!"unknown compressor {comp}")
    sink := sink + out.size
  IO.println s!"{comp} L{level} reps={reps} sink={sink}"
