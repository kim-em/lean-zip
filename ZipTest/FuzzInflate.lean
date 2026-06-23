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
    input. `.userError` is the only `IO.Error` variant the FFI emits
    (see `tryFFI` for rationale); any other variant reaching the catch
    is either an FFI contract regression or a runtime-level error that
    should surface loudly, so we re-raise. -/
private def tryStreaming (chunks : Array ByteArray) : IO Unit := do
  try
    let state ← Gzip.InflateState.new
    for chunk in chunks do
      let _ ← state.push chunk
    let _ ← state.finish
  catch e =>
    match e with
    | .userError _ => pure ()
    | _ => throw e

/-- `maxDecompressedSize` classes used by the high-level streaming
    fuzz probes. `0` opts into unlimited mode (the PR #1610
    pre-default / the opt-in for trusted input), so the "no-cap"
    code path is still exercised after PR #1631 flipped the default
    to 1 GiB. The finite entries stress the `IO.Ref UInt64` counter +
    guard at different "distance to cap" regimes. Bomb detection is
    out of scope — random bytes rarely decompress, and when they do
    the output is tiny — the value is cross-chunk counter
    soundness. See PR #1616 review F-c. -/
private def maxClasses : Array UInt64 :=
  #[0, 64, 1024, 65536]

/-- Sink `IO.FS.Stream` that discards every byte written. Used as
    the output side of the high-level streaming fuzz probes — the
    fuzz driver cares only about whether the decoder crashes or
    violates a contract, not about the decompressed bytes. -/
private def discardSinkStream : IO.FS.Stream := {
  flush := pure ()
  read := fun _ => pure ByteArray.empty
  write := fun _ => pure ()
  getLine := pure ""
  putStr := fun _ => pure ()
  isTty := pure false
}

/-- Readable `IO.FS.Stream` that yields the given `chunks` in order,
    one chunk per `read` call (capped to the requested byte count).
    Skips exhausted / empty chunks so the consumer sees an empty
    read only after every chunk is drained — critical because
    `decompressStream` treats the first empty read as EOF. -/
private def chunksReadStream (chunks : Array ByteArray) : IO IO.FS.Stream := do
  let idxRef ← IO.mkRef 0
  let offRef ← IO.mkRef 0
  return {
    flush := pure ()
    read := fun n => do
      let mut idx ← idxRef.get
      let mut off ← offRef.get
      -- Advance past already-drained chunks. At most `chunks.size`
      -- iterations; bounded `for` keeps this obviously terminating.
      for _ in [:chunks.size] do
        if idx ≥ chunks.size then break
        if off < chunks[idx]!.size then break
        idx := idx + 1
        off := 0
      if idx ≥ chunks.size then
        idxRef.set idx
        offRef.set 0
        return ByteArray.empty
      let chunk := chunks[idx]!
      let available := chunk.size - off
      let toRead := min n.toNat available
      let result := chunk.extract off (off + toRead)
      idxRef.set idx
      offRef.set (off + toRead)
      return result
    write := fun _ => throw (IO.userError "chunksReadStream: write not supported")
    getLine := pure ""
    putStr := fun _ => pure ()
    isTty := pure false
  }

/-- Drive the high-level `Gzip.decompressStream` path with the
    fuzz-generated `chunks` feeding an in-memory input stream and a
    PRNG-picked `maxDecompressedSize`. Exercises the Lean-side
    `IO.Ref UInt64` counter at `Zip/Gzip.lean:89-97` that the
    low-level `InflateState.push/finish` surface does not see.
    Catch is narrowed to `.userError` (matches `tryFFI`); other
    `IO.Error` variants propagate to fail the fuzz run loudly. -/
private def tryStreamingGzip (chunks : Array ByteArray)
    (maxCap : UInt64) : IO Unit := do
  try
    let inStream ← chunksReadStream chunks
    Gzip.decompressStream inStream discardSinkStream
      (maxDecompressedSize := maxCap)
  catch e =>
    match e with
    | .userError _ => pure ()
    | _ => throw e

/-- Drive the high-level `RawDeflate.decompressStream` path with the
    fuzz-generated `chunks` and a PRNG-picked `maxDecompressedSize`.
    Same counter pattern as `tryStreamingGzip`, on the raw-deflate
    wrapper at `Zip/RawDeflate.lean:59-69`. Same `.userError`-only
    narrowing for symmetry with `tryFFI`. -/
private def tryStreamingRawDeflate (chunks : Array ByteArray)
    (maxCap : UInt64) : IO Unit := do
  try
    let inStream ← chunksReadStream chunks
    RawDeflate.decompressStream inStream discardSinkStream
      (maxDecompressedSize := maxCap)
  catch e =>
    match e with
    | .userError _ => pure ()
    | _ => throw e

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
  tryNative "Zip.Native.Inflate.inflateTreeFree"
    (Zip.Native.Inflate.inflateTreeFree input defaultMaxOutput)
  tryNative "Zip.Native.GzipDecode.decompress"
    (Zip.Native.GzipDecode.decompress input defaultMaxOutput)
  tryNative "Zip.Native.ZlibDecode.decompress"
    (Zip.Native.ZlibDecode.decompress input defaultMaxOutput)
  tryNative "Zip.Native.decompressAuto"
    (Zip.Native.decompressAuto input defaultMaxOutput)
  -- Streaming FFI paths: the low-level `InflateState.push/finish`
  -- surface and the high-level `decompressStream` wrappers. The
  -- high-level probes share one PRNG-picked `maxDecompressedSize`
  -- across the gzip + raw-deflate calls — fewer xorshift advances
  -- per iteration keeps the PRNG state-space simple.
  let (chunks, s2) := splitIntoChunks input s1
  tryStreaming chunks
  let s3 := xorshift64 s2
  let maxCap := pick maxClasses s3
  tryStreamingGzip chunks maxCap
  tryStreamingRawDeflate chunks maxCap
  return s3

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

/-! ## Encoder-side conformance fuzz

The inflate fuzz above only ever round-trips the native decoder against
itself or feeds random bytes to the FFI. Neither can see an *encoder*
bug where native `deflateRaw` emits a stream the native inflate happily
accepts but zlib rejects — the `repairBl` length-limiter regression was
exactly this shape (incomplete CL / lit-len code sets that native
inflate tolerates and zlib does not). The two entries below close that
gap: a compress→FFI-decompress round-trip, and a differential
strictness census over bit-flipped dynamic-block headers. -/

/-- Input size classes for the encoder-side fuzz. Capped well below the
    inflate harness's 64 KiB because every payload is compressed at a
    sampled level (including the optimal-parse level 9), which is far
    costlier than a decode. -/
private def compressSizeClasses : Array Nat :=
  #[0, 1, 13, 200, 2048, 16384]

/-- Levels sampled by the compress→FFI fuzz. Spans stored (0), the fast
    greedy/lazy band, and the optimal parser (9) — the riskiest emit
    path and the one the upcoming matcher surgery will churn. -/
private def compressLevels : Array UInt8 :=
  #[0, 1, 4, 6, 7, 8, 9]

/-- Generate a fuzz payload of compressibility `cls` (`0`: random /
    incompressible — the encoder falls back to a stored block; `1`: small
    alphabet; `2`: long runs; `3`: repeated motif + sparse noise). Classes
    1–3 deliberately carry structure the encoder turns into fixed/dynamic
    Huffman blocks, so the header-emit logic — the surface the `repairBl`
    bug lived on — actually runs. Returns the payload and updated PRNG
    state. -/
private def genPayloadCls (state : UInt64) (n : Nat) (cls : Nat) :
    ByteArray × UInt64 := Id.run do
  let mut s := xorshift64 state
  let alpha := 3 + (s >>> 16).toNat % 12     -- 3..14 distinct values (class 1)
  let motifLen := 3 + (s >>> 24).toNat % 24  -- 3..26 byte motif (class 3)
  let mut out := ByteArray.empty
  for i in [:n] do
    s := xorshift64 s
    let b : UInt8 :=
      match cls % 4 with
      | 0 => (s &&& 0xFF).toUInt8                  -- random / incompressible
      | 1 => (s.toNat % alpha).toUInt8            -- small alphabet → dynamic Huffman
      | 2 => ((i / 31 + s.toNat % 3) % 11).toUInt8 -- long runs → RLE-friendly
      | _ =>                                      -- repeated motif + sparse noise
        if s.toNat % 16 == 0 then (s &&& 0xFF).toUInt8
        else ((i % motifLen) * 31 % 256).toUInt8
    out := out.push b
  return (out, s)

/-- Generate a fuzz payload whose compressibility class is PRNG-picked
    across all four classes. Used by the compress→FFI fuzz, which wants
    the stored-fallback path exercised alongside the Huffman paths. -/
private def genPayload (state : UInt64) (n : Nat) : ByteArray × UInt64 :=
  genPayloadCls state n (xorshift64 state).toNat

/-- One compress→FFI-decompress iteration: build a payload, compress it
    with native `deflateRaw` at a sampled level, decompress through the
    zlib FFI, and assert byte equality. A mismatch means the native
    encoder produced a stream zlib decodes differently (or rejects) — the
    cross-implementation bug class native-only round-trips can't see. -/
private def oneCompressIter (state : UInt64) : IO UInt64 := do
  let s0 := xorshift64 state
  let size := pick compressSizeClasses s0
  let (payload, s1) := genPayload s0 size
  let s2 := xorshift64 s1
  let level := pick compressLevels s2
  let compressed := Zip.Native.Deflate.deflateRaw payload level
  let decompressed ← RawDeflate.decompress compressed defaultMaxOutput.toUInt64
  unless decompressed == payload do
    throw (IO.userError
      s!"[compress-fuzz] level={level} size={size}: FFI decode mismatch \
         (got {decompressed.size}B, want {size}B)")
  return s2

/-- Run `iterations` compress→FFI-decompress fuzz iterations from `seed`. -/
def runCompressFuzz (seed : UInt64) (iterations : Nat) : IO Unit := do
  let mut state := if seed = 0 then 0x5eed1234abcd1234 else seed
  for _ in [:iterations] do
    state ← oneCompressIter state

/-! ### Differential strictness census

Take a *valid* dynamic-block stream the native encoder produced (so it
round-trips through both decoders by construction), flip one bit inside
its header region (BTYPE intact; HLIT/HDIST/HCLEN/CL-code-lengths and the
start of the lit-len length sequence), then ask both decoders to decode
the mutation. The verdicts are tallied into four buckets. The only
*failure* is a both-accept-but-disagree result (silent corruption);
native-accepts/FFI-rejects is the known strictness gap and is recorded,
not failed, so the count can inform whether tightening native inflate is
worth a follow-up. -/

/-- Header-region width (bytes from the block start) the differential
    fuzz flips bits within. ~12 bytes covers the 3-bit block header, the
    HLIT/HDIST/HCLEN fields, the up-to-19 3-bit CL code lengths, and the
    first few CL-encoded lit-len lengths. -/
private def diffHeaderBytes : Nat := 12

/-- Size classes for the differential fuzz. Biased upward — tiny inputs
    compress to a fixed-Huffman or stored block (the encoder's
    `pickSmaller` picks the smallest), so the base stream has to be large
    enough that a *dynamic* block wins and there is a header to mutate. -/
private def diffSizeClasses : Array Nat :=
  #[300, 800, 2000, 4096, 9000]

/-- Running tally of native-vs-FFI verdicts over mutated streams. -/
private structure Census where
  nativeAcceptFFIReject : Nat := 0
  nativeRejectFFIAccept : Nat := 0
  bothAccept : Nat := 0
  bothReject : Nat := 0
  mutated : Nat := 0
  skipped : Nat := 0   -- payload didn't compress to a dynamic block
deriving Inhabited

/-- Flip bit `bitIndex` (LSB-first within each byte, matching DEFLATE's
    bit order) of `data`. Out-of-range indices return `data` unchanged. -/
private def flipBit (data : ByteArray) (bitIndex : Nat) : ByteArray :=
  let byteIdx := bitIndex / 8
  if byteIdx < data.size then
    let mask : UInt8 := (1 : UInt8) <<< (UInt8.ofNat (bitIndex % 8))
    data.set! byteIdx (data[byteIdx]! ^^^ mask)
  else data

/-- Decode `data` through the zlib FFI, mapping the `userError` the FFI
    raises on a malformed stream into an `Except` so the caller can
    compare verdicts uniformly. Non-`userError` exceptions re-raise (see
    `tryFFI`). -/
private def ffiVerdict (data : ByteArray) : IO (Except Unit ByteArray) := do
  try
    let b ← RawDeflate.decompress data defaultMaxOutput.toUInt64
    return .ok b
  catch e =>
    match e with
    | .userError _ => return .error ()
    | _ => throw e

/-- One differential iteration. Builds a guaranteed-valid dynamic block
    via `deflateRaw … 9`, skips inputs that compressed to a non-dynamic
    block (BTYPE ≠ 2), mutates one header bit, and folds the verdict into
    `c`. Returns the updated PRNG state and census. -/
private def oneDiffIter (state : UInt64) (c : Census) : IO (UInt64 × Census) := do
  let s0 := xorshift64 state
  let size := pick diffSizeClasses s0
  -- Compressible payload (classes 1–3 only): force structure so level 9
  -- emits a dynamic block rather than a stored/fixed fallback.
  let cls := 1 + s0.toNat % 3
  let (payload, s1) := genPayloadCls s0 size cls
  let stream := Zip.Native.Deflate.deflateRaw payload 9
  -- BTYPE lives in bits 1–2 of the first byte (LSB-first); 2 == dynamic.
  let isDynamic := stream.size > 0 && ((stream[0]! >>> 1) &&& 3) == 2
  if !isDynamic then
    return (s1, { c with skipped := c.skipped + 1 })
  -- The base stream is the verified encoder's output, so it must
  -- round-trip through both decoders — assert it as extra conformance.
  match Zip.Native.Inflate.inflateTreeFree stream defaultMaxOutput with
  | .error e => throw (IO.userError s!"[diff-fuzz] base native inflate failed: {e}")
  | .ok r =>
    unless r == payload do
      throw (IO.userError "[diff-fuzz] base native round-trip mismatch")
  let baseFFI ← RawDeflate.decompress stream defaultMaxOutput.toUInt64
  unless baseFFI == payload do
    throw (IO.userError "[diff-fuzz] base FFI round-trip mismatch")
  -- Flip one bit in the header region, leaving BFINAL/BTYPE (bits 0–2)
  -- intact so the mutation stays a dynamic-header mutation.
  let s2 := xorshift64 s1
  let span := min (diffHeaderBytes * 8) (stream.size * 8)
  if span ≤ 3 then
    return (s2, { c with skipped := c.skipped + 1 })
  let bitIdx := 3 + s2.toNat % (span - 3)
  let mutated := flipBit stream bitIdx
  let nativeRes := Zip.Native.Inflate.inflateTreeFree mutated defaultMaxOutput
  let ffiRes ← ffiVerdict mutated
  let c := { c with mutated := c.mutated + 1 }
  match nativeRes, ffiRes with
  | .ok nb, .ok fb =>
    unless nb == fb do
      throw (IO.userError
        s!"[diff-fuzz] CORRUPTION: native and FFI both accept the mutated \
           stream but disagree (bit {bitIdx}, native {nb.size}B vs FFI {fb.size}B)")
    return (s2, { c with bothAccept := c.bothAccept + 1 })
  | .ok _, .error _ =>
    return (s2, { c with nativeAcceptFFIReject := c.nativeAcceptFFIReject + 1 })
  | .error _, .ok _ =>
    return (s2, { c with nativeRejectFFIAccept := c.nativeRejectFFIAccept + 1 })
  | .error _, .error _ =>
    return (s2, { c with bothReject := c.bothReject + 1 })

/-- Run `iterations` differential header-mutation iterations from `seed`,
    returning the accumulated census. -/
def runDiffFuzz (seed : UInt64) (iterations : Nat) : IO Census := do
  let mut state := if seed = 0 then 0xd1ff5eed0badf00d else seed
  let mut c : Census := {}
  for _ in [:iterations] do
    let (s, c') ← oneDiffIter state c
    state := s
    c := c'
  return c

/-! ### Structural-garbage decode census

A second decode-side census, complementary to `runDiffFuzz`. Where
`runDiffFuzz` perturbs a *single bit of a valid dynamic header*, this
target feeds inputs that are not mutations of a valid block at all:
truncated streams, concatenated gzip members (with a possibly-truncated
final member), and uniformly-random byte streams. For each input both
the native decoder and the zlib FFI are asked to decode, and the
verdicts are tallied into a `DecodeCensus`.

The contract mirrors `runDiffFuzz`: the only *failure* is silent
corruption (both decoders accept but return different bytes); a
native-accept/FFI-reject is recorded, not failed (it is the standing
strictness gap, narrowed — never widened — by the decode-strictness
work). The harness never panics and never loops past `maxOutputSize`
because every native entry point is total and budget-capped. -/

/-- Running tally of native-vs-FFI verdicts over structural-garbage
    inputs. Same four verdict buckets as `Census`, without the
    header-mutation-specific `mutated`/`skipped` counters. -/
private structure DecodeCensus where
  nativeAcceptFFIReject : Nat := 0
  nativeRejectFFIAccept : Nat := 0
  bothAccept : Nat := 0
  bothReject : Nat := 0
  total : Nat := 0
deriving Inhabited

/-- One-line tally summary for the test log / PR description. -/
private def DecodeCensus.summary (c : DecodeCensus) : String :=
  s!"both-accept {c.bothAccept}, both-reject {c.bothReject}, \
     native-accept/FFI-reject {c.nativeAcceptFFIReject}, \
     native-reject/FFI-accept {c.nativeRejectFFIAccept} (of {c.total})"

/-- Decode `data` through the zlib gzip FFI, mapping the malformed-stream
    `userError` into an `Except` (mirrors `ffiVerdict`, which targets the
    raw-deflate FFI). Non-`userError` exceptions re-raise. -/
private def gzipFFIVerdict (data : ByteArray) : IO (Except Unit ByteArray) := do
  try
    let b ← Gzip.decompress data defaultMaxOutput.toUInt64
    return .ok b
  catch e =>
    match e with
    | .userError _ => return .error ()
    | _ => throw e

/-- Fold one (native, FFI) verdict pair into `c`. The single failure mode
    is silent corruption — both decoders accept but disagree byte-for-byte;
    every other combination is a recorded census bucket. `label` and the
    running `total` identify the offending iteration in a failure log. -/
private def foldVerdict (label : String) (native : Except String ByteArray)
    (ffi : Except Unit ByteArray) (c : DecodeCensus) : IO DecodeCensus := do
  let c := { c with total := c.total + 1 }
  match native, ffi with
  | .ok nb, .ok fb =>
    unless nb == fb do
      throw (IO.userError
        s!"[{label}] CORRUPTION: native and FFI both accept (iter {c.total}) but \
           disagree (native {nb.size}B vs FFI {fb.size}B)")
    return { c with bothAccept := c.bothAccept + 1 }
  | .ok _, .error _ =>
    return { c with nativeAcceptFFIReject := c.nativeAcceptFFIReject + 1 }
  | .error _, .ok _ =>
    return { c with nativeRejectFFIAccept := c.nativeRejectFFIAccept + 1 }
  | .error _, .error _ =>
    return { c with bothReject := c.bothReject + 1 }

/-- Payload sizes for the structural-garbage classes. Kept modest (≤ 2 KiB)
    so that even level-9 optimal-parse compression of every base stream
    stays cheap across the iteration budget. -/
private def decodeSizeClasses : Array Nat :=
  #[64, 200, 800, 2048]

/-- One truncated-stream iteration. Compresses a structured payload to a
    valid raw-DEFLATE stream, then cuts it at a uniformly-random byte
    offset in `[0, size)` (always strictly shorter; because DEFLATE blocks
    are bit-packed, a byte cut lands mid-block, exercising bit-granular
    truncation too). Native inflate must return an `Except` — never panic,
    never run past `maxOutputSize`. -/
private def oneTruncIter (state : UInt64) (c : DecodeCensus) :
    IO (UInt64 × DecodeCensus) := do
  let s0 := xorshift64 state
  let size := pick decodeSizeClasses s0
  -- classes 1–3 carry structure → a real Huffman block to truncate.
  let cls := 1 + s0.toNat % 3
  let (payload, s1) := genPayloadCls s0 size cls
  let s2 := xorshift64 s1
  let level := pick compressLevels s2
  let stream := Zip.Native.Deflate.deflateRaw payload level
  let s3 := xorshift64 s2
  if stream.size == 0 then
    return (s3, c)
  let cut := s3.toNat % stream.size
  let truncated := stream.extract 0 cut
  let native := Zip.Native.Inflate.inflateTreeFree truncated defaultMaxOutput
  let ffi ← ffiVerdict truncated
  let c ← foldVerdict "trunc-deflate" native ffi c
  return (s3, c)

/-- One concatenated-gzip-member iteration. Builds `1..4` back-to-back
    gzip members (each an FFI-compressed structured payload), then with
    probability ½ truncates the concatenation at a random offset. When
    untruncated, both decoders must accept and reproduce the concatenated
    payloads (native gzip's documented multi-member behaviour); when
    truncated, the verdict is folded into the census (native ⊆ FFI, no
    silent corruption). -/
private def oneConcatIter (state : UInt64) (c : DecodeCensus) :
    IO (UInt64 × DecodeCensus) := do
  let s0 := xorshift64 state
  let nMembers := 1 + s0.toNat % 4
  let mut s := s0
  let mut concat := ByteArray.empty
  let mut expected := ByteArray.empty
  for _ in [:nMembers] do
    s := xorshift64 s
    let size := pick decodeSizeClasses s
    let cls := s.toNat % 4
    let (payload, s') := genPayloadCls s size cls
    s := xorshift64 s'
    let level := pick compressLevels s
    let member ← Gzip.compress payload level
    concat := concat ++ member
    expected := expected ++ payload
  let s1 := xorshift64 s
  let doTruncate := s1.toNat % 2 == 0 && concat.size > 0
  if !doTruncate then
    -- Valid concatenated stream: both decoders must round-trip it.
    match Zip.Native.GzipDecode.decompress concat defaultMaxOutput with
    | .error e => throw (IO.userError s!"[concat-gzip] native rejected a valid \
        {nMembers}-member stream: {e}")
    | .ok nb =>
      unless nb == expected do
        throw (IO.userError "[concat-gzip] native multi-member round-trip mismatch")
    let fb ← Gzip.decompress concat defaultMaxOutput.toUInt64
    unless fb == expected do
      throw (IO.userError "[concat-gzip] FFI multi-member round-trip mismatch")
    return (s1, { c with total := c.total + 1, bothAccept := c.bothAccept + 1 })
  let stream := concat.extract 0 (s1.toNat % concat.size)
  let native := Zip.Native.GzipDecode.decompress stream defaultMaxOutput
  let ffi ← gzipFFIVerdict stream
  let c ← foldVerdict "concat-gzip-trunc" native ffi c
  return (s1, c)

/-- One uniformly-random-byte-stream iteration. Feeds pure noise to native
    raw inflate as a smoke layer: it must terminate with an error (or, on
    the rare valid stored-block prefix, agree with the FFI byte-for-byte) —
    never panic, never disagree silently. -/
private def oneRandomIter (state : UInt64) (c : DecodeCensus) :
    IO (UInt64 × DecodeCensus) := do
  let s0 := xorshift64 state
  let size := pick decodeSizeClasses s0
  let (data, s1) := genBytes s0 size
  let native := Zip.Native.Inflate.inflateTreeFree data defaultMaxOutput
  let ffi ← ffiVerdict data
  let c ← foldVerdict "random-deflate" native ffi c
  return (s1, c)

/-- Run `iterations` of each structural-garbage class (truncated raw
    DEFLATE, concatenated gzip members, random byte streams) from
    independent sub-seeds derived from `seed`, printing a per-class tally.
    Deterministic: a fixed `(seed, iterations)` reproduces every input and
    every census exactly. -/
def runDecodeFuzz (seed : UInt64) (iterations : Nat) : IO Unit := do
  let base := if seed = 0 then 0x0dec0de0fab1e5 else seed
  let runClass (start : UInt64)
      (step : UInt64 → DecodeCensus → IO (UInt64 × DecodeCensus)) :
      IO DecodeCensus := do
    let mut state := start
    let mut c : DecodeCensus := {}
    for _ in [:iterations] do
      let (s, c') ← step state c
      state := s
      c := c'
    return c
  let cTrunc ← runClass base oneTruncIter
  let cConcat ← runClass (xorshift64 base) oneConcatIter
  let cRandom ← runClass (xorshift64 (xorshift64 base)) oneRandomIter
  IO.println s!"    decode-fuzz truncated:     {cTrunc.summary}"
  IO.println s!"    decode-fuzz concat-gzip:   {cConcat.summary}"
  IO.println s!"    decode-fuzz random-stream: {cRandom.summary}"

/-- Smoke test: fixed-seed 1000-iteration run invoked from `lake exe
    test`. Iteration count is bounded to keep CI runtime reasonable
    (~100 ms at ~100 μs/iteration). Prints the seed up front so a
    future CI failure log carries enough information to reproduce
    locally.

    Also drives the two encoder-side fuzz entries (compress→FFI
    round-trip and the differential header-mutation census), each ≥ 256
    iterations, and prints the native-vs-FFI verdict census so a CI log
    (and the PR description) carries the strictness-gap count. -/
def tests : IO Unit := do
  let seed : UInt64 := 0xdeadbeef
  IO.println s!"  FuzzInflate tests (seed=0x{String.ofList (Nat.toDigits 16 seed.toNat)})..."
  runFuzz seed 1000
  IO.println "    1000 iterations completed"
  runCompressFuzz 0xc0ffee 256
  IO.println "    256 compress→FFI iterations completed"
  let census ← runDiffFuzz 0xfeedface 256
  IO.println s!"    256 differential header-mutation iterations completed \
    ({census.mutated} mutated, {census.skipped} skipped non-dynamic)"
  IO.println s!"    census: both-accept {census.bothAccept}, both-reject \
    {census.bothReject}, native-accept/FFI-reject {census.nativeAcceptFFIReject}, \
    native-reject/FFI-accept {census.nativeRejectFFIAccept}"
  runDecodeFuzz 0xc0deba5e 256
  IO.println "    256×3 structural-garbage decode iterations completed"

end ZipTest.FuzzInflate
