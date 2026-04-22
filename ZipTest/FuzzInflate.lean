import Zip
import ZipTest.Helpers

/-! Deterministic randomized fuzz driver for inflate entry points.

Exercises every whole-buffer and streaming inflate surface — both the
FFI wrappers and the pure-Lean native decoders — with pseudo-randomly
generated `ByteArray` inputs. The goal is to catch unhandled
exceptions, panics, unbounded allocations, and (when run under
`scripts/sanitize-ffi.sh`) sanitizer-level memory errors that
hand-written regression fixtures miss.

The driver is intentionally deterministic: a fixed `(seed, iterations)`
pair produces the same exact inputs on every run. Any failure can be
reproduced by re-running with the same seed.

See `SECURITY_INVENTORY.md` *Fuzz coverage* and
`plans/track-e-current-audit-checklist.md` Priority 3 item 3. -/

namespace ZipTest.FuzzInflate

/-- Input size classes cycled through across fuzz iterations. Kept
    small (≤ 64 KiB) — this is a correctness harness, not a throughput
    test. -/
private def sizeClasses : Array Nat :=
  #[0, 1, 16, 512, 8192, 65536]

/-- Cap on whole-buffer decompressed output. 4 MiB is large enough
    that any legitimate small input won't be clipped, but small enough
    that an accidentally-valid bomb stops early. -/
private def defaultMaxOutput : Nat := 4 * 1024 * 1024

/-- Chunk sizes used by the streaming driver. Deliberately irregular
    so we stress cross-chunk state (`inflateReset`, `realloc` growth)
    with inputs that aren't block-aligned. -/
private def chunkSizes : Array Nat := #[1, 7, 31, 127]

/-- 64-bit xorshift PRNG. Inlined here so the fuzz driver has zero
    external randomness dependency — reproducibility is the point. -/
private def xorshift64 (s : UInt64) : UInt64 := Id.run do
  let mut x := s
  x := x ^^^ (x <<< 13)
  x := x ^^^ (x >>> 7)
  x := x ^^^ (x <<< 17)
  return x

/-- Generate `n` pseudo-random bytes starting from `state`. Returns
    the bytes and the updated PRNG state. -/
private def genBytes (state : UInt64) (n : Nat) : ByteArray × UInt64 := Id.run do
  let mut s := state
  let mut result := ByteArray.empty
  for _ in [:n] do
    s := xorshift64 s
    result := result.push (s &&& 0xFF).toUInt8
  return (result, s)

/-- Pick a value from `arr` by PRNG state. -/
private def pick [Inhabited α] (arr : Array α) (s : UInt64) : α :=
  arr[s.toNat % arr.size]!

/-- Split `data` into chunks using PRNG state to pick sizes from
    `chunkSizes`. Returns the chunks and updated state. -/
private def splitIntoChunks (data : ByteArray) (state : UInt64) :
    Array ByteArray × UInt64 := Id.run do
  let mut s := state
  let mut chunks : Array ByteArray := #[]
  let mut pos : Nat := 0
  while pos < data.size do
    s := xorshift64 s
    let size := pick chunkSizes s
    let stop := min data.size (pos + size)
    chunks := chunks.push (data.extract pos stop)
    pos := stop
  return (chunks, s)

/-- Run one FFI whole-buffer entry point. Any thrown `IO.userError`
    is swallowed (that is the handled case). Other exceptions (e.g.
    a panic leaking through) propagate and fail the fuzz run.

    `.userError` is the only `IO.Error` variant the zlib FFI emits
    (via `lean_mk_io_user_error` in `c/zlib_ffi.c`); any other variant
    reaching the catch is either an FFI contract regression or a
    runtime-level error that should surface loudly, so we re-raise. -/
private def tryFFI (label : String) (action : IO ByteArray) : IO Unit := do
  try
    let _ ← action
  catch e =>
    match e with
    | .userError _ =>
      let _ := s!"[fuzz {label}] {e}"
      pure ()
    | _ => throw e

/-- Run one native whole-buffer entry point. Returns `()` regardless
    of `Except` outcome — a parse failure is the expected common case. -/
private def tryNative (_label : String) (action : Except String ByteArray) : IO Unit := do
  match action with
  | .ok _ => pure ()
  | .error _ => pure ()

/-- Drive the streaming `lean_gzip_inflate_push` path with chunked
    input. Any caught exception is the handled case. -/
private def tryStreaming (chunks : Array ByteArray) : IO Unit := do
  try
    let state ← Gzip.InflateState.new
    for chunk in chunks do
      let _ ← state.push chunk
    let _ ← state.finish
  catch _ =>
    pure ()

/-- One fuzz iteration: generate a random input of some size and
    drive every inflate entry point on it. Updates and returns the
    PRNG state. -/
private def oneIteration (state : UInt64) : IO UInt64 := do
  -- Pick an input size.
  let s0 := xorshift64 state
  let size := pick sizeClasses s0
  let (input, s1) := genBytes s0 size
  -- Whole-buffer FFI paths.
  tryFFI "Zlib.decompress" (Zlib.decompress input defaultMaxOutput.toUInt64)
  tryFFI "Gzip.decompress" (Gzip.decompress input defaultMaxOutput.toUInt64)
  tryFFI "RawDeflate.decompress" (RawDeflate.decompress input defaultMaxOutput.toUInt64)
  -- Whole-buffer native paths.
  tryNative "Zip.Native.Inflate.inflate"
    (Zip.Native.Inflate.inflate input defaultMaxOutput)
  tryNative "Zip.Native.GzipDecode.decompress"
    (Zip.Native.GzipDecode.decompress input defaultMaxOutput)
  tryNative "Zip.Native.ZlibDecode.decompress"
    (Zip.Native.ZlibDecode.decompress input defaultMaxOutput)
  tryNative "Zip.Native.decompressAuto"
    (Zip.Native.decompressAuto input defaultMaxOutput)
  -- Streaming FFI path (the only streaming decoder we expose).
  let (chunks, s2) := splitIntoChunks input s1
  tryStreaming chunks
  return s2

/-- Run `iterations` fuzz iterations starting from `seed`. Every
    iteration drives every inflate entry point listed above on a
    freshly-generated random input. Returns normally on clean
    completion; any uncaught exception or process-level crash is the
    failure signal. -/
def runFuzz (seed : UInt64) (iterations : Nat) : IO Unit := do
  let mut state := if seed = 0 then 0xdeadbeefdeadbeef else seed
  for _ in [:iterations] do
    state ← oneIteration state

/-- Run fuzz iterations until `IO.monoMsNow` passes `deadlineMs`, or
    `maxIterations` is reached (whichever comes first). Returns the
    number of iterations performed. Used by
    `scripts/fuzz-inflate.sh` for wall-clock budgeted runs. -/
def runFuzzUntil (seed : UInt64) (deadlineMs : Nat)
    (maxIterations : Nat := 1_000_000) : IO Nat := do
  let mut state := if seed = 0 then 0xdeadbeefdeadbeef else seed
  let mut count : Nat := 0
  for _ in [:maxIterations] do
    if (← IO.monoMsNow) ≥ deadlineMs then break
    state ← oneIteration state
    count := count + 1
  return count

/-- Smoke test: fixed-seed 1000-iteration run invoked from `lake exe
    test`. Iteration count is bounded to keep CI runtime reasonable
    (~100 ms at ~100 μs/iteration). Prints the seed up front so a
    future CI failure log carries enough information to reproduce
    locally. -/
def tests : IO Unit := do
  let seed : UInt64 := 0xdeadbeef
  IO.println s!"  FuzzInflate tests (seed=0x{String.ofList (Nat.toDigits 16 seed.toNat)})..."
  runFuzz seed 1000
  IO.println "    1000 iterations completed"

end ZipTest.FuzzInflate
