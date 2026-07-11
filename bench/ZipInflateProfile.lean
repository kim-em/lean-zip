import Zip
import Zip.Native.InflateFast  -- #2799 spike (quarantined: not re-exported by `Zip`)
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

/-- Report absolute throughput from a timed loop. MB/s is over the *decompressed*
    bytes (`origSize`), the meaningful decode-rate denominator. -/
def reportMBps (label : String) (origSize reps ns checksum : Nat) : IO Unit := do
  let mbps := if ns == 0 then 0.0
    else (Float.ofNat (origSize * reps) * 1000.0) / Float.ofNat ns
  IO.eprintln s!"{label}: {reps} reps, {origSize * reps} B decompressed in \
                 {Float.ofNat ns / 1.0e6} ms → {mbps} MB/s (checksum={checksum})"

/-- `decode` mode: time native inflate `reps` times over one payload. The decode
    is inlined directly in the loop body (not behind an IO closure), so the pure
    `inflate payload` is re-run every iteration rather than hoisted out; each
    result size flows through the `noinline` `sink`, keeping it live. -/
def runDecode (payloadPath : String) (origSize reps : Nat) : IO Unit := do
  let payload ← IO.FS.readBinFile payloadPath
  -- Sanity-check once (outside the timed region) that the stream decodes.
  match Zip.Native.Inflate.inflate payload (sizeHint := origSize) with
  | .error e => throw (IO.userError s!"inflate failed on {payloadPath}: {e}")
  | .ok first =>
    IO.eprintln s!"inflate-profile decode: {payload.size} → {first.size} bytes, \
                   sizeHint={origSize}, reps={reps}"
    let mut checksum := 0
    let t0 ← IO.monoNanosNow
    for _ in [:reps] do
      match Zip.Native.Inflate.inflate payload (sizeHint := origSize) with
      | .ok b => checksum := checksum + (← sink b.size)
      | .error e => throw (IO.userError s!"inflate failed: {e}")
    let t1 ← IO.monoNanosNow
    reportMBps "decode" origSize reps (t1 - t0) checksum

/-- `decode-fast` mode (issue #2799 spike): like `decode`, but the steady-state
    loop calls the write-once-cursor `Inflate.inflateFast` instead of the
    production `Inflate.inflate`. A/B the two saved... no — A/B the two MODES of
    the *same* binary (`decode` vs `decode-fast`), which is even more
    code-layout-comparable than the two-worktree rule requires. The one-time
    sanity check asserts `inflateFast` output equals `inflate` output, so a
    correctness divergence aborts before any timing. -/
def runDecodeFast (payloadPath : String) (origSize reps : Nat) : IO Unit := do
  let payload ← IO.FS.readBinFile payloadPath
  let refOut ← match Zip.Native.Inflate.inflate payload (sizeHint := origSize) with
    | .error e => throw (IO.userError s!"reference inflate failed on {payloadPath}: {e}")
    | .ok b => pure b
  match Zip.Native.Inflate.inflateFast payload (sizeHint := origSize) with
  | .error e => throw (IO.userError s!"inflateFast failed on {payloadPath}: {e}")
  | .ok first =>
    unless first == refOut do
      throw (IO.userError s!"inflateFast output MISMATCH: {first.size} B vs reference {refOut.size} B")
    IO.eprintln s!"inflate-profile decode-fast: {payload.size} → {first.size} bytes \
                   (== reference), sizeHint={origSize}, reps={reps}"
    let mut checksum := 0
    let t0 ← IO.monoNanosNow
    for _ in [:reps] do
      match Zip.Native.Inflate.inflateFast payload (sizeHint := origSize) with
      | .ok b => checksum := checksum + (← sink b.size)
      | .error e => throw (IO.userError s!"inflateFast failed: {e}")
    let t1 ← IO.monoNanosNow
    reportMBps "decode-fast" origSize reps (t1 - t0) checksum

/-- `decode-fast-u` mode: like `decode-fast` but the branch-free `uset` fastloop
    (`Inflate.inflateFastU`). Asserts output equals the reference once, then loops. -/
def runDecodeFastU (payloadPath : String) (origSize reps : Nat) : IO Unit := do
  let payload ← IO.FS.readBinFile payloadPath
  let refOut ← match Zip.Native.Inflate.inflate payload (sizeHint := origSize) with
    | .error e => throw (IO.userError s!"reference inflate failed on {payloadPath}: {e}")
    | .ok b => pure b
  match Zip.Native.Inflate.inflateFastU payload (sizeHint := origSize) with
  | .error e => throw (IO.userError s!"inflateFastU failed on {payloadPath}: {e}")
  | .ok first =>
    unless first == refOut do
      throw (IO.userError s!"inflateFastU output MISMATCH: {first.size} B vs reference {refOut.size} B")
    IO.eprintln s!"inflate-profile decode-fast-u: {payload.size} → {first.size} bytes \
                   (== reference), sizeHint={origSize}, reps={reps}"
    let mut checksum := 0
    let t0 ← IO.monoNanosNow
    for _ in [:reps] do
      match Zip.Native.Inflate.inflateFastU payload (sizeHint := origSize) with
      | .ok b => checksum := checksum + (← sink b.size)
      | .error e => throw (IO.userError s!"inflateFastU failed: {e}")
    let t1 ← IO.monoNanosNow
    reportMBps "decode-fast-u" origSize reps (t1 - t0) checksum

/-- `decode-ld` mode: time libdeflate's own decompressor over the same payload,
    as the absolute "speed bar" in the same harness. -/
def runDecodeLd (payloadPath : String) (origSize reps : Nat) : IO Unit := do
  let payload ← IO.FS.readBinFile payloadPath
  let first ← Libdeflate.decompress payload origSize.toUInt64
  IO.eprintln s!"inflate-profile decode-ld: {payload.size} → {first.size} bytes, \
                 sizeHint={origSize}, reps={reps}"
  let mut checksum := 0
  let t0 ← IO.monoNanosNow
  for _ in [:reps] do
    let b ← Libdeflate.decompress payload origSize.toUInt64
    checksum := checksum + (← sink b.size)
  let t1 ← IO.monoNanosNow
  reportMBps "decode-ld" origSize reps (t1 - t0) checksum

/-- `compress` mode: dump one libdeflate raw-DEFLATE payload for later profiling. -/
def runCompress (inPath outPath : String) (level : UInt8) : IO Unit := do
  let data ← IO.FS.readBinFile inPath
  let stream ← Libdeflate.compress data level
  IO.FS.writeBinFile outPath stream
  IO.eprintln s!"inflate-profile compress: {inPath} ({data.size} B) → {outPath} \
                 ({stream.size} B, level {level}); origSize for decode = {data.size}"

def usage : String :=
  "usage:\n" ++
  "  inflate-profile compress <file> <out> <level>          dump a libdeflate payload once\n" ++
  "  inflate-profile decode <payload> <origSize> <reps>     profile native inflate only\n" ++
  "  inflate-profile decode-fast <payload> <origSize> <reps> profile the #2799 write-once-cursor spike"

def main (args : List String) : IO Unit := do
  match args with
  | ["compress", inPath, outPath, lvlStr] =>
    let some level := lvlStr.toNat? | throw (IO.userError s!"bad level: {lvlStr}")
    runCompress inPath outPath level.toUInt8
  | ["decode", payloadPath, sizeStr, repsStr] =>
    let some origSize := sizeStr.toNat? | throw (IO.userError s!"bad origSize: {sizeStr}")
    let some reps := repsStr.toNat? | throw (IO.userError s!"bad reps: {repsStr}")
    runDecode payloadPath origSize reps
  | ["decode-fast", payloadPath, sizeStr, repsStr] =>
    let some origSize := sizeStr.toNat? | throw (IO.userError s!"bad origSize: {sizeStr}")
    let some reps := repsStr.toNat? | throw (IO.userError s!"bad reps: {repsStr}")
    runDecodeFast payloadPath origSize reps
  | ["decode-fast-u", payloadPath, sizeStr, repsStr] =>
    let some origSize := sizeStr.toNat? | throw (IO.userError s!"bad origSize: {sizeStr}")
    let some reps := repsStr.toNat? | throw (IO.userError s!"bad reps: {repsStr}")
    runDecodeFastU payloadPath origSize reps
  | ["decode-ld", payloadPath, sizeStr, repsStr] =>
    let some origSize := sizeStr.toNat? | throw (IO.userError s!"bad origSize: {sizeStr}")
    let some reps := repsStr.toNat? | throw (IO.userError s!"bad reps: {repsStr}")
    runDecodeLd payloadPath origSize reps
  | _ => IO.eprintln usage; throw (IO.userError "bad arguments")
