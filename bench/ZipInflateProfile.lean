import Zip
import Bench.Libdeflate

/-!
# Single-decoder inflate profiling driver

A deliberately tiny driver whose `decode` mode's steady-state loop calls **only**
the production native decoder `Zip.Native.Inflate.inflate` over one payload (plus
minimal loop/size bookkeeping), so a `perf record` / `perf stat` of that process
attributes cleanly to inflate. Unlike `bench-report --decode-density`
(`ZipBenchReport.lean`), which sweeps five decoders over all of Silesia, no other
decoder runs here. (The binary links `Bench.Libdeflate` for `compress` mode, but
that code never executes in a `decode` run, so it costs no samples.)

Two modes:

- `compress <file> <out> <level>` — dump a libdeflate raw-DEFLATE payload once
  (levels 1–12; libdeflate makes the densest realistic streams). Run this first
  to materialize the stream, then profile `decode` over it.
- `decode <payload> <origSize> <reps>` — read the dumped payload and call
  `Inflate.inflate` (`sizeHint := origSize`) `reps` times over the *same* bytes.
  `origSize` is the decompressed length (the pre-size hint); pass the original
  file's size. Lean is strict, so the `match` re-evaluates `inflate` on every
  iteration; the loop deliberately does **not** bind the result once outside the
  loop (which would compute a single decode and reuse it) and consumes each
  result via a running checksum (through the `noinline` `sink`), so no decode is
  dead-code eliminated. Wall-clock therefore scales linearly with `reps`.

See `bench/README.md` § *Profiling the decoder* for the `perf` recipe and the
same-worktree A/B rule.
-/

open Zip.Native

/-- A `noinline` consumer of the decode's realized size, so the compiler cannot
    prove each `inflate` result dead and drop it. -/
@[noinline] def sink (n : Nat) : IO Nat := pure n

/-- `decode` mode: run native inflate `reps` times over one payload, nothing else. -/
def runDecode (payloadPath : String) (origSize reps : Nat) : IO Unit := do
  let payload ← IO.FS.readBinFile payloadPath
  -- Sanity-check once (outside any timed region) that the stream decodes, and
  -- report the decompressed size so a caller can confirm origSize is right.
  match Zip.Native.Inflate.inflate payload (sizeHint := origSize) with
  | .error e => throw (IO.userError s!"inflate failed on {payloadPath}: {e}")
  | .ok first =>
    IO.eprintln s!"inflate-profile decode: {payload.size} → {first.size} bytes, \
                   sizeHint={origSize}, reps={reps}"
    let mut checksum := 0
    -- Strict eval re-runs `inflate` each iteration (no let-bound reuse); the
    -- running checksum through `sink` keeps every result live.
    for _ in [:reps] do
      match Zip.Native.Inflate.inflate payload (sizeHint := origSize) with
      | .ok b => checksum := checksum + (← sink b.size)
      | .error e => throw (IO.userError s!"inflate failed: {e}")
    IO.eprintln s!"done ({reps} reps, checksum={checksum})"

/-- `compress` mode: dump one libdeflate raw-DEFLATE payload for later profiling. -/
def runCompress (inPath outPath : String) (level : UInt8) : IO Unit := do
  let data ← IO.FS.readBinFile inPath
  let stream ← Libdeflate.compress data level
  IO.FS.writeBinFile outPath stream
  IO.eprintln s!"inflate-profile compress: {inPath} ({data.size} B) → {outPath} \
                 ({stream.size} B, level {level}); origSize for decode = {data.size}"

def usage : String :=
  "usage:\n" ++
  "  inflate-profile compress <file> <out> <level>        dump a libdeflate payload once\n" ++
  "  inflate-profile decode <payload> <origSize> <reps>   profile native inflate only"

def main (args : List String) : IO Unit := do
  match args with
  | ["compress", inPath, outPath, lvlStr] =>
    let some level := lvlStr.toNat? | throw (IO.userError s!"bad level: {lvlStr}")
    runCompress inPath outPath level.toUInt8
  | ["decode", payloadPath, sizeStr, repsStr] =>
    let some origSize := sizeStr.toNat? | throw (IO.userError s!"bad origSize: {sizeStr}")
    let some reps := repsStr.toNat? | throw (IO.userError s!"bad reps: {repsStr}")
    runDecode payloadPath origSize reps
  | _ => IO.eprintln usage; throw (IO.userError "bad arguments")
