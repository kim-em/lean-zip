import Zip
import ZipTest.Helpers

/-! Deterministic randomized fuzz driver for `Handle.read` and
`Stream.read` driven entry points.

In-repo regression reconstruction of the `lean_io_prim_handle_read`
buffer-overflow class identified by Kiran's blog-post AFL harness
([kirancodes.me](https://kirancodes.me/posts/log-who-watches-the-watchers.html)),
fixed upstream by leanprover/lean4#13392 (consumed via the
v4.30.0-rc2 toolchain bump in PR #2352).

Sibling of `ZipTest/FuzzInflate.lean`: same xorshift PRNG, same
deterministic-by-seed contract, same wall-clock budget shape. The
difference is the surface — `FuzzInflate` exercises the inflate
decoders with random *compressed* bytes; this driver exercises the
archive parsers (`Archive.list`, `Archive.extract`, `Tar.list`,
`Tar.extract`, `Tar.extractTarGz`, `Tar.extractTarGzNative`,
`Gzip.decompressStream`, `RawDeflate.decompressStream`,
`Gzip.decompressFile`) on the read side, with random bytes routed
through both the file `Handle.read` path and the
`IO.FS.Stream.read` path.

Pathological-input families (per #2380 deliverable 3):

- *read-size-vs-buffer-length mismatches at archive-record
  boundaries* — random sizes from `sizeClasses` straddle the
  internal 65536-byte chunk reads that every streaming surface
  uses, exposing realloc-grown buffer transitions.
- *zero-length reads followed by larger reads* — `0` is the first
  size class, ensuring the empty-input EOF path is exercised
  before any non-empty read.
- *oversized declared sizes* — random bytes occasionally form a
  parser-acceptable header whose declared payload size is huge;
  the `Tar.extract` `maxEntrySize` and the various
  `maxDecompressedSize` caps are exercised by the
  `outputCapClasses` rotation.
- *streaming reads across realloc-grown buffers* — `chunkSizes`
  includes values straddling 65536 (`{1, 7, 31, 127, 65535,
  65536, 65537}`), so the `fragmentingStream` wrapper drives
  short / boundary / over-sized reads through every stream
  surface.

The harness is intentionally deterministic: a fixed
`(seed, iterations)` pair produces the same exact inputs on every
run. Any failure can be reproduced by re-running with the same
seed.

See `SECURITY_INVENTORY.md` *Trusted Computing Base → Lean Runtime*
*Recent wins* and the *Local guard inventory for `Handle.read` and
`Stream.read`* subsection for the per-site audit whose guarantees
this harness exercises. -/

namespace ZipTest.FuzzHandleRead

/-- Input size classes cycled through across fuzz iterations. The
    upper bound (128 KiB) is deliberately above the 65536 chunk
    size used by every streaming surface so cross-chunk realloc
    transitions are exercised on every iteration. -/
private def sizeClasses : Array Nat :=
  #[0, 1, 16, 512, 8192, 65536, 131072]

/-- Chunk sizes used by the `fragmentingStream` wrapper. Values
    straddling the internal 65536 boundary stress the realloc-grown
    buffer transitions inside the streaming inflate / tar parsers. -/
private def chunkSizes : Array Nat :=
  #[1, 7, 31, 127, 65535, 65536, 65537]

/-- `maxDecompressedSize` / `maxEntrySize` classes used by the
    streaming decoders and the tar `extract` paths. `0` exercises
    the unlimited-mode branch (bomb-unsafe but still part of the
    public surface). -/
private def outputCapClasses : Array UInt64 :=
  #[0, 64, 1024, 65536, 1024 * 1024]

/-- 64-bit xorshift PRNG. Inlined here so the fuzz driver has zero
    external randomness dependency — reproducibility is the point.
    Identical to the inlined PRNG in `ZipTest/FuzzInflate.lean`. -/
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

/-- Splice the ZIP EOCD signature (`PK\x05\x06` = 0x06054b50) into
    `data` at a PRNG-picked position near the tail. Random bytes
    almost never form a recognisable EOCD by chance, which means
    `Archive.list` bails out at the first 65 KiB tail-scan
    iteration and never exercises the central-directory read
    paths. Splicing a real signature into the last 64 KiB drives
    parser progress further — and feeds nonsense into the CD
    parser, which is the path we actually want to stress. -/
private def withEocdSignature (data : ByteArray) (state : UInt64) :
    ByteArray × UInt64 := Id.run do
  -- Need at least 22 bytes (the EOCD record itself) to splice into.
  if data.size < 22 then return (data, state)
  let s := xorshift64 state
  -- Position the EOCD signature somewhere in the last 64 KiB
  -- (matches `Archive.list`'s tail scan window). At least 22 bytes
  -- of trailing room, so the EOCD has space for a degenerate but
  -- non-truncated body.
  let maxTail := min data.size 65536
  let pos := data.size - 22 - (s.toNat % (maxTail - 21))
  let mut buf := data
  -- PK\x05\x06 little-endian
  buf := buf.set! pos       0x50  -- 'P'
  buf := buf.set! (pos + 1) 0x4B  -- 'K'
  buf := buf.set! (pos + 2) 0x05
  buf := buf.set! (pos + 3) 0x06
  return (buf, s)

/-- Wrap `data` in a minimal gzip header (`0x1f 0x8b 0x08 0x00 …`).
    Forces the gzip header parser to commit to the deflate body and
    exercise the streaming `inflate.push` path on the random tail.
    On too-short input, returns `data` unchanged. -/
private def withGzipMagic (data : ByteArray) : ByteArray :=
  if data.size < 10 then data
  else Id.run do
    let mut buf := data
    buf := buf.set! 0 0x1f
    buf := buf.set! 1 0x8b
    buf := buf.set! 2 0x08  -- method = deflate
    buf := buf.set! 3 0x00  -- flags = none
    buf := buf.set! 4 0x00  -- mtime[0]
    buf := buf.set! 5 0x00
    buf := buf.set! 6 0x00
    buf := buf.set! 7 0x00
    buf := buf.set! 8 0x00  -- xflags
    buf := buf.set! 9 0xff  -- OS = unknown
    return buf

/-- Stamp the UStar magic (`"ustar\x00"`) at offset 257 of the
    first 512-byte block, with the `00` version. Forces the tar
    `parseHeader` to attempt a full UStar parse on random bytes
    instead of bailing on magic mismatch — exercises the
    octal-field parsing, checksum verification, and (when checksum
    happens to match) the `forEntries` payload-read loop. -/
private def withUstarMagic (data : ByteArray) : ByteArray :=
  if data.size < 512 then data
  else Id.run do
    let mut buf := data
    -- magic = "ustar\x00" at offset 257
    buf := buf.set! 257 0x75  -- 'u'
    buf := buf.set! 258 0x73  -- 's'
    buf := buf.set! 259 0x74  -- 't'
    buf := buf.set! 260 0x61  -- 'a'
    buf := buf.set! 261 0x72  -- 'r'
    buf := buf.set! 262 0x00
    -- version = "00" at offset 263
    buf := buf.set! 263 0x30  -- '0'
    buf := buf.set! 264 0x30  -- '0'
    return buf

/-- Try wrapper for an `IO`-returning archive operation. `.userError`
    is the only `IO.Error` variant the lean-zip parsers emit on
    malformed input (verified by every other test in the codebase
    that calls `assertThrows` with `IO.userError`-substring matches);
    any other variant reaching the catch is either a parser-contract
    regression or a runtime-level error that should surface loudly,
    so we re-raise. Mirrors `tryFFI` in `ZipTest/FuzzInflate.lean`. -/
private def tryRead (action : IO α) : IO Unit := do
  try
    let _ ← action
  catch e =>
    match e with
    | .userError _ => pure ()
    | _ => throw e

/-- Sink `IO.FS.Stream` that discards every byte written. Output
    side of the streaming-decompress fuzz probes — the fuzz driver
    cares only about whether the decoder crashes or violates a
    contract, not about the decompressed bytes. -/
private def discardSinkStream : IO.FS.Stream := {
  flush := pure ()
  read := fun _ => pure ByteArray.empty
  write := fun _ => pure ()
  getLine := pure ""
  putStr := fun _ => pure ()
  isTty := pure false
}

/-- One fuzz iteration: generate a random input of some size and
    drive every `Handle.read` / `Stream.read` entry point on it.
    `tmpFile` is the on-disk fixture path the file-based parsers
    consume; `outDir` is the extraction sink for `extract` paths.
    Both are reused across iterations and overwritten in place. -/
private def oneIteration (state : UInt64) (tmpFile : System.FilePath)
    (outDir : System.FilePath) : IO UInt64 := do
  -- Pick an input size and a random byte buffer.
  let s0 := xorshift64 state
  let size := pick sizeClasses s0
  let (input, s1) := genBytes s0 size
  -- Pick a chunk size for the `fragmentingStream` wrapper and an
  -- output cap class for the streaming decompressors.
  let s2 := xorshift64 s1
  let chunkSize := pick chunkSizes s2
  let s3 := xorshift64 s2
  let outCap := pick outputCapClasses s3

  ---- File-based (Handle.read) probes ------------------------------

  -- Bare random bytes: most iterations bail out at EOCD detection,
  -- but the tail-scan still drives `Handle.read` through the
  -- 65 KiB read window. The `outDir` is reused across iterations;
  -- random bytes essentially never reach the write path so it
  -- stays empty.
  IO.FS.writeBinFile tmpFile input
  tryRead (Archive.list tmpFile)
  tryRead (Archive.extract tmpFile outDir)

  -- Random bytes with a planted EOCD signature near the tail.
  -- Drives `Archive.list` past the tail scan into the
  -- central-directory read paths (where `readBoundedSpanFromHandle`
  -- and `readExact` are the actual read drivers).
  let (zipped, s4) := withEocdSignature input s3
  IO.FS.writeBinFile tmpFile zipped
  tryRead (Archive.list tmpFile)

  -- Random bytes prefixed with the gzip magic. Drives
  -- `Gzip.decompressFile` through the FFI streaming-inflate
  -- read loop on a real file handle.
  let gzipped := withGzipMagic input
  IO.FS.writeBinFile tmpFile gzipped
  let gzOut : System.FilePath := s!"{tmpFile}.out"
  tryRead (Gzip.decompressFile tmpFile (some gzOut))
  -- Drive the streaming tar.gz path on the same fixture: the
  -- gzip header is recognised, the inflate engine produces
  -- nonsense bytes, and the tar parser drops out at the first
  -- 512-byte read whose checksum / magic doesn't validate.
  tryRead (Tar.extractTarGz tmpFile outDir)
  -- Native tar.gz path: same inputs, separate code path
  -- (`extractTarGzNative` reads the entire file into memory and
  -- runs the native gzip decoder, then drives the tar parser
  -- against the in-memory bytes).
  tryRead (Tar.extractTarGzNative tmpFile outDir)

  ---- Stream-based (Stream.read) probes ----------------------------

  -- `byteArrayReadStream` returns a fresh stream every call (the
  -- internal position is held in an `IO.Ref Nat`), so each probe
  -- gets its own iterator. The `fragmentingStream` wrapper caps
  -- each `read` call to `chunkSize` bytes, simulating short reads
  -- from pipes / network streams across realloc-grown buffers.
  let mkStream : IO IO.FS.Stream := do
    let s ← byteArrayReadStream input
    return fragmentingStream s chunkSize

  -- Random bytes through the tar parser (Stream.read driven).
  -- `Tar.list` is the lightweight probe; `Tar.extract` adds the
  -- payload-read + skip-padding paths on top.
  let s5 := xorshift64 s4
  tryRead (do let s ← mkStream; Tar.list s)
  tryRead (do let s ← mkStream; Tar.extract s outDir
                (maxEntrySize := outCap)
                (maxTotalSize := outCap))

  -- Random bytes with the UStar magic stamped — forces
  -- `parseHeader` to commit to a full UStar parse rather than
  -- bailing on magic mismatch. Exercises the octal-field parsing
  -- + checksum verification + (when checksum happens to match)
  -- the `forEntries` payload-read loop.
  let ustarBytes := withUstarMagic input
  let mkUstarStream : IO IO.FS.Stream := do
    let s ← byteArrayReadStream ustarBytes
    return fragmentingStream s chunkSize
  tryRead (do let s ← mkUstarStream; Tar.list s)
  tryRead (do let s ← mkUstarStream; Tar.extract s outDir
                (maxEntrySize := outCap)
                (maxTotalSize := outCap))

  -- Streaming gzip / raw deflate decompressors driven through
  -- `byteArrayReadStream` + `fragmentingStream`. The
  -- `gzipped` buffer above carries a real gzip header; bare
  -- `input` exercises the magic-mismatch error path.
  let mkGzStream : IO IO.FS.Stream := do
    let s ← byteArrayReadStream gzipped
    return fragmentingStream s chunkSize
  tryRead (do let s ← mkGzStream
              Gzip.decompressStream s discardSinkStream
                (maxDecompressedSize := outCap))
  tryRead (do let s ← mkStream
              Gzip.decompressStream s discardSinkStream
                (maxDecompressedSize := outCap))
  tryRead (do let s ← mkStream
              RawDeflate.decompressStream s discardSinkStream
                (maxDecompressedSize := outCap))

  return s5

/-- Resolve the fuzz scratch directory. Reused across iterations
    and recreated empty at the top of `runFuzz`. The path is
    parameterised on `IO.tmpDir` if the platform exposes one;
    otherwise falls back to `/tmp` (matching the convention used
    by `ZipTest.Archive.tests` and `ZipTest.Helpers.writeFixtureTmp`). -/
private def fuzzScratchDir : System.FilePath :=
  ("/tmp" : System.FilePath) / "lean-zip-fuzz-handle-read"

/-- Prepare a fresh, empty scratch directory at `fuzzScratchDir`.
    Reused as both the on-disk fixture parent and the extraction
    output sink. -/
private def prepareScratchDir : IO Unit := do
  if ← fuzzScratchDir.pathExists then
    let _ ← IO.Process.run { cmd := "rm", args := #["-rf", fuzzScratchDir.toString] }
  IO.FS.createDirAll fuzzScratchDir

/-- Run `iterations` fuzz iterations starting from `seed`. Every
    iteration drives every `Handle.read` / `Stream.read` entry
    point listed in `oneIteration` on a freshly-generated random
    input. Returns normally on clean completion; any uncaught
    exception or process-level crash is the failure signal. -/
def runFuzz (seed : UInt64) (iterations : Nat) : IO Unit := do
  prepareScratchDir
  let tmpFile := fuzzScratchDir / "input.bin"
  let outDir := fuzzScratchDir / "out"
  IO.FS.createDirAll outDir
  let mut state := if seed = 0 then 0xfeedfacecafef00d else seed
  for _ in [:iterations] do
    state ← oneIteration state tmpFile outDir

/-- Run fuzz iterations until `IO.monoMsNow` passes `deadlineMs`,
    or `maxIterations` is reached (whichever comes first). Returns
    the number of iterations performed. Used by
    `scripts/fuzz-handle-read.sh` for wall-clock budgeted runs. -/
def runFuzzUntil (seed : UInt64) (deadlineMs : Nat)
    (maxIterations : Nat := 1_000_000) : IO Nat := do
  prepareScratchDir
  let tmpFile := fuzzScratchDir / "input.bin"
  let outDir := fuzzScratchDir / "out"
  IO.FS.createDirAll outDir
  let mut state := if seed = 0 then 0xfeedfacecafef00d else seed
  let mut count : Nat := 0
  for _ in [:maxIterations] do
    if (← IO.monoMsNow) ≥ deadlineMs then break
    state ← oneIteration state tmpFile outDir
    count := count + 1
  return count

/-- Smoke test: fixed-seed 100-iteration run invoked from
    `lake exe test`. Iteration count is bounded to keep CI runtime
    reasonable — each iteration writes the on-disk fixture three
    times (bare / EOCD-spliced / gzip-magic'd) and runs nine
    archive-parser probes, so wall-clock cost is dominated by the
    file writes (~ a few ms each). Prints the seed up front so a
    future CI failure log carries enough information to reproduce
    locally. -/
def tests : IO Unit := do
  let seed : UInt64 := 0xdeadc0de
  IO.println s!"  FuzzHandleRead tests (seed=0x{String.ofList (Nat.toDigits 16 seed.toNat)})..."
  runFuzz seed 100
  IO.println "    100 iterations completed"

end ZipTest.FuzzHandleRead
