import Zip

/-! Scratch: deterministic `deflateRaw` output size + fold checksum over a file,
    for byte-identity comparison across branches (rung-4 #2837). Not committed. -/

open Zip.Native.Deflate

def foldck (a : ByteArray) : Nat :=
  a.foldl (fun acc b => (acc * 1000003 + b.toNat + 1) % (2^61 - 1)) a.size

def main (args : List String) : IO Unit := do
  match args with
  | path :: levels =>
    let data ← IO.FS.readBinFile path
    for ls in levels do
      let level := (ls.toNat?).getD 6
      let out := deflateRaw data level.toUInt8
      IO.println s!"{path},L{level},{out.size},{foldck out}"
  | _ => IO.println "usage: csize-file <path> <level>..."
