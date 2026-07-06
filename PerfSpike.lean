import Zip.Native.DeflateDynamic

@[noinline] def compressOnce (data : ByteArray) (level : UInt8) : IO Nat := do
  let n := (Zip.Native.Deflate.deflateRaw data level).size
  if n == 0 then throw (IO.userError "empty output")
  return n

def mbps (size ns : Nat) : Float := (Float.ofNat size / 1e6) / (Float.ofNat ns / 1e9)

def main (args : List String) : IO Unit := do
  let path := args.headD "bench/corpora/silesia/dickens"
  let reps := (args.drop 1).head?.bind (·.toNat?) |>.getD 5
  let data ← IO.FS.readBinFile path
  IO.println s!"file={path} size={data.size} reps={reps}"
  for level in [4,5,6,7,8] do
    let mut best : Nat := 0
    let mut out : Nat := 0
    for _ in [0:reps] do
      let t0 ← IO.monoNanosNow
      let n ← compressOnce data level.toUInt8
      let t1 ← IO.monoNanosNow
      out := n
      let dt := t1 - t0
      if best == 0 || dt < best then best := dt
    IO.println s!"L{level}: {mbps data.size best} MB/s  {best/1000000}ms  out={out}"
