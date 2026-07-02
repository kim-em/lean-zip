import Zip
import ZipTest.Helpers

/-! Deterministic **cross-engine interop** fuzz for the encoder: does our
raw-DEFLATE output actually interoperate with the rest of the ecosystem,
across the whole level ladder × a diverse input-shape generator?

### What this is *not* for

Native encode → native decode being the identity is already a **theorem**:
`Deflate.inflate_deflateRaw` (`Zip/Spec/DeflateRoundtrip.lean`) proves
`inflate (deflateRaw data level) = .ok data`, sorry-free, for *every*
input and *every* level (its proof branches through level-0 stored, the
L1/respread band, the #2638 L9-fast parse, and the level-10 crown), and it
transfers to the production `inflate` via the `inflate ↔ inflateReference`
equivalence. Totality likewise makes "native encode/decode never panics" a
proof obligation, not a test one. So this driver does **not** exist to
re-check the self-roundtrip — over the Lean model that is redundant.

### What this *is* for

The roundtrip proof shows we agree with *ourselves*; it says nothing about
whether the rest of the ecosystem agrees with us. zlib, libdeflate, and
miniz_oxide are opaque external C/Rust — Lean has no model of them, so
their acceptance of our output is not a theorem and cannot be one. This
driver checks that empirically. For a seeded, deterministic spread of
input shapes and **every level 0-9**:

1. **Interop out** (load-bearing) — `{zlib, libdeflate, miniz_oxide}
   .decompress (deflateRaw input level) == input`: our output is raw
   DEFLATE that *stricter* reference decoders accept, not just our own
   lenient one. This is the real payload. The bug class it catches: an
   encoder that emits a stream our own proven-correct decoder happily
   round-trips (so `inflate_deflateRaw` still holds) but that a conforming
   decoder rejects — e.g. the `repairBl` regression's incomplete Huffman
   code sets, which native inflate tolerated and zlib rejected. A roundtrip
   proof is blind to that by construction.
2. **Interop in** (load-bearing) — `Inflate.inflate ({zlib, libdeflate}
   .compress input level) == input`: our decoder accepts a *different*
   encoder's conforming output. This exercises decoder **completeness**
   against a real-world stream distribution — a direction the roundtrip
   theorem does not cover (it only proves we decode *our own* output).
3. **Self-roundtrip / no-panic** (free cross-check) — we do also assert
   `inflate (deflateRaw input level) == input` and that nothing panics.
   These are covered by the theorems above; we keep them only because they
   ride for free alongside the interop decode calls and cheaply cross-check
   the compiled binary against the proven model (a Lean codegen / FFI-glue
   miscompilation gap). They are not the coverage this file adds.

So the one-line justification is: the guard against a ladder-redesign or
fast-emit regression producing output that round-trips through *our*
decoder but that zlib/libdeflate/miniz reject (or vice versa) — the one
failure mode the encoder proofs cannot see.

The driver is deterministic: the shape × size × level matrix is a fixed
enumeration and the PRNG-filled payloads derive from a fixed seed, so a
failure reproduces exactly. Reference engines absent at build time
(libdeflate, miniz_oxide) skip cleanly, as elsewhere.

Distinct from — cite, don't duplicate:
* **#2575** owns the window / 64 KiB-stored-block *boundary* roundtrip
  specifics; this is the broader level×shape×engine matrix.
* **#2591** owns the RLE/overlap period sweep on the decode side.
* **#2582-2585** are decode-direction malformed-reject fuzz (opposite
  property).
-/

namespace ZipTest.FuzzCompress

/-! ## PRNG -/

/-- 64-bit xorshift PRNG. Inlined so the driver has zero external
    randomness dependency — reproducibility is the point. -/
private def xorshift64 (s : UInt64) : UInt64 := Id.run do
  let mut x := s
  x := x ^^^ (x <<< 13)
  x := x ^^^ (x >>> 7)
  x := x ^^^ (x <<< 17)
  return x

/-! ## Shape generators

Each generator maps a target `size` (and a PRNG `seed` where the content
is randomized) to a `ByteArray`. Together they cover the content classes
that stress different encoder paths. `size = 0` yields the empty array
from every generator (the degenerate case). -/

/-- All-identical bytes: maximally compressible, exercises the RLE /
    overlap-copy match path (one long back-reference). -/
private def genConstant (size : Nat) (seed : UInt64) : ByteArray := Id.run do
  let b := (seed &&& 0xFF).toUInt8
  let mut out := ByteArray.emptyWithCapacity size
  for _ in [:size] do
    out := out.push b
  return out

/-- Pseudo-random / incompressible bytes: the encoder must fall back to a
    stored block (or a fixed block barely larger than stored) at every
    level. Exercises the stored-fallback `pickSmaller` decision. -/
private def genIncompressible (size : Nat) (seed : UInt64) : ByteArray := Id.run do
  let mut s := if seed == 0 then 0x9e3779b97f4a7c15 else seed
  let mut out := ByteArray.emptyWithCapacity size
  for _ in [:size] do
    s := xorshift64 s
    out := out.push (s &&& 0xFF).toUInt8
  return out

/-- Low-entropy text-like content: a small word alphabet with spaces and
    newlines (repeats + literals). Compresses to dynamic-Huffman blocks,
    exercising the header-emit logic. Reuses `mkTextData`. -/
private def genText (size : Nat) (_seed : UInt64) : ByteArray :=
  mkTextData size

/-- Periodic / structured content: a PRNG-seeded motif tiled to fill
    `size`. The fixed period produces long matches at a constant distance,
    exercising the long-match and distance-code paths. Motif length varies
    with the seed (3..66) so different distance codes get hit. -/
private def genPeriodic (size : Nat) (seed : UInt64) : ByteArray := Id.run do
  let motifLen := 3 + (seed >>> 8).toNat % 64
  let mut s := if seed == 0 then 0xd1ce5eed0badf00d else seed
  let mut motif := ByteArray.emptyWithCapacity motifLen
  for _ in [:motifLen] do
    s := xorshift64 s
    motif := motif.push (s &&& 0xFF).toUInt8
  let mut out := ByteArray.emptyWithCapacity size
  for i in [:size] do
    out := out.push motif[i % motifLen]!
  return out

/-- Already-compressed content (near-1.0 ratio): text run through
    `deflateRaw`, truncated to exactly `size` bytes. This is a *native
    DEFLATE byte stream* used as an incompressible-but-non-uniform corpus —
    re-compressing it forces the stored fallback while looking nothing like
    uniform PRNG noise. (It is not an independent oracle; the point is the
    input shape, and any bytes are valid encoder input.) -/
private def genAlreadyCompressed (size : Nat) (seed : UInt64) : ByteArray :=
  if size == 0 then ByteArray.empty else
  let src := genText (size * 2 + 128) seed
  let comp := Zip.Native.Deflate.deflateRaw src 6
  -- If the compressed text is somehow shorter than `size`, pad with PRNG
  -- bytes so the payload is exactly `size` and still incompressible.
  if comp.size ≥ size then comp.extract 0 size
  else comp ++ genIncompressible (size - comp.size) seed

/-- A named shape generator. -/
private structure Shape where
  name : String
  gen : Nat → UInt64 → ByteArray
deriving Inhabited

/-- The content shape classes (excluding the size-driven empty / single-byte
    degenerate cases, which every generator covers via `size ∈ {0,1}`). -/
private def shapes : Array Shape := #[
  { name := "constant",   gen := genConstant },
  { name := "incompress", gen := genIncompressible },
  { name := "text",       gen := genText },
  { name := "periodic",   gen := genPeriodic },
  { name := "precomp",    gen := genAlreadyCompressed }
]

/-! ## Size classes -/

/-- Small + medium sizes, run at **every** level 0-9. Covers the empty /
    single-byte / min-match degenerate cases, the 258/259 max-match
    boundary, the ~32 KiB window, and the 64 KiB stored-block boundary
    (#2575 owns the boundary specifics in depth; here they are one axis of
    the broader matrix). -/
private def denseSizes : Array Nat :=
  #[0, 1, 2, 3, 258, 259, 32768, 65534, 65535, 65536]

/-- MB-scale multi-window sizes, run at **fewer** levels (`sparseLevels`)
    to keep CI time bounded — the optimal parser at level 9 on a megabyte
    is the single costliest cell in the matrix. -/
private def sparseSizes : Array Nat :=
  #[1048576, 2097152]

/-- Every level. Applied to `denseSizes`. -/
private def allLevels : Array UInt8 :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- Levels sampled for the MB-scale inputs: stored (0), the fast L1, the
    dynamic middle (6), and the optimal parser (9) — one representative per
    band, skipping the redundant respread rungs. -/
private def sparseLevels : Array UInt8 :=
  #[0, 1, 6, 9]

/-! ## Optional-engine availability

libdeflate and miniz_oxide are optional comparators; on a minimal
toolchain their FFI raises an `IO.userError` carrying a build-disabled
marker. We probe each once up front, then only call the ones that are
present — cheaper and cleaner than a per-iteration try/catch. -/

private def libdeflateMarker : String := "libdeflate: not built with"
private def minizMarker : String := "miniz_oxide: not built with Rust support"

/-- Run `action`; return `true` if it succeeds, `false` if it fails with
    `marker` (the build-disabled skip), re-raise anything else. -/
private def probe (action : IO α) (marker : String) : IO Bool := do
  match (← action.toBaseIO) with
  | .ok _ => return true
  | .error e =>
    if (toString e).contains marker then return false else throw e

/-- Which optional decode/encode engines are built in this configuration. -/
private structure Engines where
  libdeflate : Bool
  miniz : Bool

private def detectEngines : IO Engines := do
  let libdeflate ← probe (Libdeflate.compress ByteArray.empty) libdeflateMarker
  let miniz ← probe (MinizOxide.compress ByteArray.empty) minizMarker
  return { libdeflate, miniz }

/-! ## Assertions -/

/-- Assert `got == want`, throwing a reproduction-carrying error otherwise. -/
private def assertEq (ctx : String) (got want : ByteArray) : IO Unit :=
  unless got.beq want do
    throw (IO.userError
      s!"[fuzz-compress] {ctx}: mismatch (got {got.size}B, want {want.size}B)")

/-- Cap for every decode. Generous: the largest legitimate output is the
    2 MiB MB-scale payload, so 8 MiB never clips a valid stream while still
    bounding a hypothetical runaway. -/
private def maxOut : Nat := 8 * 1024 * 1024

/-- Run an FFI action, re-raising any error tagged with the cell context and
    `phase` so a comparator rejection still names the shape/size/level that
    triggered it (FFI errors carry only the library's own message). -/
private def tagged (ctx phase : String) (action : IO α) : IO α := do
  match (← action.toBaseIO) with
  | .ok x => return x
  | .error e => throw (IO.userError s!"[fuzz-compress] {ctx} {phase}: {e}")

/-- One matrix cell: compress `input` at `level`, then check interop-out
    (every present decoder reads our output), interop-in (we read the
    reference encoders' output), and the free self-roundtrip cross-check.
    Only interop is load-bearing; the self-roundtrip is a theorem (see the
    module docstring). `ctx` identifies the cell in any failure message. -/
private def checkCell (eng : Engines) (ctx : String)
    (input : ByteArray) (level : UInt8) : IO Unit := do
  -- Interop out (+ the free self-roundtrip cross-check): native encode,
  -- then decode through every engine. The native-inflate leg is the
  -- theorem-covered cross-check; the FFI legs are the load-bearing interop.
  let compressed := Zip.Native.Deflate.deflateRaw input level
  match Zip.Native.Inflate.inflate compressed maxOut with
  | .ok out => assertEq s!"{ctx} self-roundtrip" out input
  | .error e => throw (IO.userError s!"[fuzz-compress] {ctx}: native inflate rejected \
      native deflateRaw output: {e}")
  assertEq s!"{ctx} interop-out zlib"
    (← tagged ctx "interop-out zlib" (RawDeflate.decompress compressed maxOut.toUInt64)) input
  if eng.libdeflate then
    assertEq s!"{ctx} interop-out libdeflate"
      (← tagged ctx "interop-out libdeflate"
        (Libdeflate.decompress compressed maxOut.toUInt64)) input
  if eng.miniz then
    assertEq s!"{ctx} interop-out miniz_oxide"
      (← tagged ctx "interop-out miniz_oxide"
        (MinizOxide.decompress compressed maxOut.toUInt64)) input
  -- Interop in: native decode accepts the reference engines' output —
  -- decoder completeness against a real encoder's stream distribution.
  let zc ← tagged ctx "interop-in zlib compress" (RawDeflate.compress input level)
  match Zip.Native.Inflate.inflate zc maxOut with
  | .ok out => assertEq s!"{ctx} interop-in zlib" out input
  | .error e => throw (IO.userError s!"[fuzz-compress] {ctx}: native inflate rejected \
      zlib output: {e}")
  if eng.libdeflate then
    -- `Libdeflate.compress` clamps level 0 up to libdeflate's minimum (1), so
    -- this cell exercises libdeflate-level-1 interop-in at the `level=0` row;
    -- the round-trip property is level-agnostic, so that is harmless.
    let lc ← tagged ctx "interop-in libdeflate compress" (Libdeflate.compress input level)
    match Zip.Native.Inflate.inflate lc maxOut with
    | .ok out => assertEq s!"{ctx} interop-in libdeflate" out input
    | .error e => throw (IO.userError s!"[fuzz-compress] {ctx}: native inflate rejected \
        libdeflate output: {e}")

/-! ## Matrix driver -/

/-- Base seed feeding the shape generators. Each cell derives its own seed
    by mixing in the shape index, size, and level, so seed-sensitive shapes
    (incompressible, periodic, constant-byte, precomp) vary per cell while
    the whole run stays deterministic. The `text` shape ignores its seed, so
    same-size text cells share bytes across levels — intentional: it isolates
    the level axis on a fixed structured payload. -/
private def baseSeed : UInt64 := 0xc0117e55c0117e55

private def cellSeed (shapeIdx size : Nat) (level : UInt8) : UInt64 :=
  xorshift64 (baseSeed ^^^ (UInt64.ofNat shapeIdx <<< 40)
    ^^^ (UInt64.ofNat size <<< 8) ^^^ UInt64.ofNat level.toNat)

/-- Run the full shape × size × level matrix for one size/level list pair.
    Returns the number of cells checked. -/
private def runMatrix (eng : Engines) (sizes : Array Nat)
    (levels : Array UInt8) : IO Nat := do
  let mut count := 0
  for shapeIdx in [:shapes.size] do
    let shape := shapes[shapeIdx]!
    for size in sizes do
      for level in levels do
        let seed := cellSeed shapeIdx size level
        let input := shape.gen size seed
        let ctx := s!"shape={shape.name} size={size} level={level}"
        checkCell eng ctx input level
        count := count + 1
  return count

/-! ## Broken-encoder sanity check

A meta-test on the harness itself: if the encoder emitted a corrupt
stream, `checkCell`'s decode assertions must fire. We simulate a broken
encoder by flipping one output byte *after* compression and confirm that
the corruption is caught by **both** load-bearing decoders — native
inflate (the self-roundtrip assertion) *and* the mandatory zlib comparator
(the interop-out assertion). Requiring both guards against either assertion
being silently removed, and against a native-encode/native-decode pair that
shares a blind spot the reference engine would not. A byte flip is "caught"
by a decoder when it rejects the stream or decodes it to bytes ≠ the
original; we scan every byte position and require at least one flip caught
by each decoder, failing only if the whole stream tolerates corruption —
which would mean the property is not load-bearing. -/

/-- Does the mutated stream fail to reproduce `input` under native inflate?
    Either an error verdict or a differing payload counts as "caught". -/
private def nativeCatches (mutated input : ByteArray) : Bool :=
  match Zip.Native.Inflate.inflate mutated maxOut with
  | .ok out => !out.beq input
  | .error _ => true

/-- Same verdict via the mandatory zlib comparator (the interop-out path). -/
private def zlibCatches (mutated input : ByteArray) : IO Bool := do
  match (← (RawDeflate.decompress mutated maxOut.toUInt64).toBaseIO) with
  | .ok out => return !out.beq input
  | .error _ => return true

/-- Assert the harness catches a deliberately-broken encoder: compress a
    compressible payload, then flip each output byte in turn and require that
    both native inflate and the zlib comparator catch at least one flip.
    Fails if *no* single-byte corruption is detectable by a decoder — which
    would mean that decoder's assertion in `checkCell` is not load-bearing. -/
private def sanityCheckBrokenEncoder : IO Unit := do
  let input := genPeriodic 4096 0xbadc0de
  let compressed := Zip.Native.Deflate.deflateRaw input 6
  -- Sanity: the un-mutated stream must round-trip through both decoders
  -- (guards the premise that we start from a valid, interoperable stream).
  match Zip.Native.Inflate.inflate compressed maxOut with
  | .ok out => assertEq "sanity base native-roundtrip" out input
  | .error e => throw (IO.userError s!"[fuzz-compress] sanity base stream rejected \
      by native inflate: {e}")
  assertEq "sanity base zlib-roundtrip"
    (← tagged "sanity" "base zlib-roundtrip" (RawDeflate.decompress compressed maxOut.toUInt64))
    input
  let mut caughtNative := false
  let mut caughtZlib := false
  for i in [:compressed.size] do
    let mutated := compressed.set! i (compressed[i]! ^^^ 0xFF)
    if !caughtNative && nativeCatches mutated input then
      caughtNative := true
    unless caughtZlib do
      if ← zlibCatches mutated input then
        caughtZlib := true
  unless caughtNative do
    throw (IO.userError "[fuzz-compress] sanity check failed: no single-byte \
      corruption was caught by native inflate — the self-roundtrip assertion \
      is not load-bearing")
  unless caughtZlib do
    throw (IO.userError "[fuzz-compress] sanity check failed: no single-byte \
      corruption was caught by the zlib comparator — the interop-out assertion \
      is not load-bearing")

/-! ## Entry point -/

/-- Run the compress-matrix fuzz: the dense size × all-levels matrix, the
    MB-scale × sampled-levels matrix, and the broken-encoder sanity check.
    Prints which optional engines participated so a CI log records the
    coverage actually exercised. Deterministic and CI-bounded. -/
def tests : IO Unit := do
  IO.println "  FuzzCompress tests..."
  let eng ← detectEngines
  IO.println s!"    engines: zlib=yes libdeflate={eng.libdeflate} miniz_oxide={eng.miniz}"
  sanityCheckBrokenEncoder
  IO.println "    broken-encoder sanity check: caught"
  let dense ← runMatrix eng denseSizes allLevels
  IO.println s!"    dense matrix ({dense} cells: {shapes.size} shapes × \
    {denseSizes.size} sizes × {allLevels.size} levels) OK"
  let sparse ← runMatrix eng sparseSizes sparseLevels
  IO.println s!"    MB-scale matrix ({sparse} cells: {shapes.size} shapes × \
    {sparseSizes.size} sizes × {sparseLevels.size} levels) OK"
  IO.println "FuzzCompress tests: OK"

end ZipTest.FuzzCompress
