import Zip

/-! # `compress-file` — the honest lean side of the end-to-end CLI comparison

A minimal real compression tool: read a file, raw-DEFLATE compress it, report
the compressed size. This is exactly the shape of `zip silesia.tar` that Kim's
`hyperfine` headline benchmarks — read the file bytes → compress → report — so
it is the fair lean side to time head-to-head against a real rust CLI
(`miniz-compress-file`, the miniz_oxide crate's `[[bin]]`).

Unlike `bench csize` / `bench compress-miniz` (which BOTH run inside the same
`bench` process and so both pay lean's `readBinFile` + big-ByteArray-alloc I/O
tax, cancelling it out of the codec ratio), this exe pays that I/O tax on the
lean side ONLY — because the rust CLI has its own, faster read path. So this is
where lean's real file-read/alloc system time shows up against rust, which is
the end-to-end wall Kim actually measures.

Usage:  compress-file <path> [level=6]
-/

open Zip.Native.Deflate

def main (args : List String) : IO Unit := do
  let path :: rest := args
    | throw (IO.userError "usage: compress-file <path> [level=6]")
  let level : UInt8 := (rest.head?.bind (·.toNat?) |>.getD 6).toUInt8
  let data ← IO.FS.readBinFile path
  let out := deflateRaw data level
  IO.println out.size
