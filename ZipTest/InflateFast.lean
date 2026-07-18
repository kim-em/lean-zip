import ZipTest.Helpers
import Zip.Native.InflateFast

/-! Conformance tests for the write-once cursor decode (issue #2799).

    `Inflate.inflateFast` (`set!` cursor) and `Inflate.inflateFastU` (branch-free
    `uset` fastloop) produce byte-identical output to the production
    `Inflate.inflate` on the **exact-size path** — the caller passes the true
    decompressed length as `sizeHint`. Both are proven equal to `inflate`
    (`Zip.Spec.InflateFastCorrect.inflateFast_eq` / `inflateFastU_eq`); this test
    is the runtime cross-check across corpora, block types, and edge cases. It
    also exercises the production dispatch `Inflate.inflateSized`, including the
    fallback taken on a wrong size hint. -/

open Zip.Native

/-! ### Direct FFI conformance: `presize` and `copyWithinAt`

    Validate each `@[extern]` against an **independent** reference (not its own
    reference body), so the C is checked to agree with the trusted model on every
    input — including the degenerate / OOB cases where the C returns `a`
    unchanged, which the Lean body must match for the extern-with-reference-body
    pattern to hold. -/

/-- Independent reference for `ByteArray.presize`: `n` zero bytes built by push. -/
def ZipTest.InflateFast.refPresize (n : Nat) : ByteArray :=
  (List.range n).foldl (fun acc _ => acc.push 0) ByteArray.empty

/-- Independent reference for `ByteArray.copyWithinAt`: the same degenerate guard
    as the C (`distance = 0`, window underflow, or write past the end → no-op),
    then write byte `destOff + k = a[destOff - distance + k % distance]` reading
    the **original** window (never a freshly-written byte, since every read index
    is `< destOff`). -/
def ZipTest.InflateFast.refCopyWithinAt (a : ByteArray) (destOff distance len : Nat) :
    ByteArray :=
  if distance = 0 ∨ distance > destOff ∨ destOff + len > a.size then a
  else (List.range len).foldl
    (fun acc k => acc.set! (destOff + k) (a.get! (destOff - distance + k % distance))) a

/-- Extern vs reference for one `(destOff, distance, len)`, plus a copy-on-write
    check that a shared input array is left unchanged. -/
def ZipTest.InflateFast.checkCopyWithinAt (a : ByteArray) (destOff distance len : Nat) :
    IO Unit := do
  let snapshot := a.extract 0 a.size
  let got := a.copyWithinAt destOff distance len
  let want := ZipTest.InflateFast.refCopyWithinAt a destOff distance len
  unless got == want do
    throw (IO.userError
      s!"copyWithinAt mismatch at destOff {destOff}, distance {distance}, len {len}: \
         got {got.toList}, want {want.toList}")
  unless snapshot == a do
    throw (IO.userError s!"copyWithinAt mutated a shared array at destOff {destOff}")

/-- Sweep `presize` and `copyWithinAt` over small sizes, all in-bounds
    `(destOff, distance, len)`, and the degenerate / OOB edges. -/
def ZipTest.InflateFast.ffiConformance : IO Unit := do
  -- presize: size and all-zero, including n = 0.
  for n in [0, 1, 2, 7, 8, 9, 64, 257, 300] do
    let p := ByteArray.presize n
    unless p == ZipTest.InflateFast.refPresize n do
      throw (IO.userError s!"presize {n} mismatch")
    unless p.size == n do throw (IO.userError s!"presize {n} wrong size {p.size}")
  -- copyWithinAt: a base buffer with a known window prefix, room to write ahead.
  let base := ByteArray.mk ((Array.range 400).map (fun i => (i % 13 + 1).toUInt8))
  for destOff in [0, 1, 13, 50, 200, 399, 400] do
    for distance in [0, 1, 2, 3, 5, 13, 64, 201] do
      for len in [0, 1, 2, 3, 7, 8, 16, 100, 258] do
        ZipTest.InflateFast.checkCopyWithinAt base destOff distance len
  -- Explicit degenerate cases (each must be a no-op equal to the input):
  ZipTest.InflateFast.checkCopyWithinAt base 10 0 5        -- distance = 0
  ZipTest.InflateFast.checkCopyWithinAt base 5 10 3        -- distance > destOff (underflow)
  ZipTest.InflateFast.checkCopyWithinAt base 399 5 100     -- write past a.size
  ZipTest.InflateFast.checkCopyWithinAt base 50 5 0        -- len = 0
  -- RLE (distance = 1) and overlapping smear (len > distance):
  ZipTest.InflateFast.checkCopyWithinAt base 200 1 100
  ZipTest.InflateFast.checkCopyWithinAt base 200 3 100

/-- Compress `data` (raw DEFLATE at `level`), then assert both cursor spikes
    decode it — with `sizeHint := data.size` — to exactly `data` and to the same
    bytes as the reference `Inflate.inflate`. -/
def ZipTest.InflateFast.checkOne (label : String) (data : ByteArray) (level : UInt8 := 6) :
    IO Unit := do
  let compressed ← RawDeflate.compress data level
  let refOut ← match Inflate.inflate compressed with
    | .ok b => pure b
    | .error e => throw (IO.userError s!"reference inflate failed on {label}: {e}")
  assert! refOut == data
  match Inflate.inflateFast compressed (sizeHint := data.size) with
  | .ok b =>
    assert! b == data
    assert! b == refOut
  | .error e => throw (IO.userError s!"inflateFast failed on {label} (level {level}): {e}")
  match Inflate.inflateFastU compressed (sizeHint := data.size) with
  | .ok b =>
    assert! b == data
    assert! b == refOut
  | .error e => throw (IO.userError s!"inflateFastU failed on {label} (level {level}): {e}")
  -- Production dispatch `inflateSized`: the exact-size fast path, the inert
  -- fallback (`exact := false`), and wrong hints (oversized and undersized) that
  -- must reject in the fastloop and fall back to the push-based decoder — all
  -- give `refOut` (the reverse-soundness / `inflateSized_agrees` guarantee).
  for (tag, hint, exact) in
      [("exact", data.size, true), ("inexact", data.size, false),
       ("wrong-hint-over", data.size + 7, true), ("wrong-hint-under", data.size / 2, true),
       ("exact-inert", data.size, false)] do
    match Inflate.inflateSized compressed (sizeHint := hint) (exact := exact) with
    | .ok b => assert! b == refOut
    | .error e => throw (IO.userError s!"inflateSized {tag} failed on {label} (level {level}): {e}")

def ZipTest.InflateFast.tests : IO Unit := do
  IO.println "  InflateFast (write-once cursor spike, #2799) tests..."
  ZipTest.InflateFast.ffiConformance
  let big ← mkTestData
  let hello := "Hello, world!".toUTF8
  -- Edge cases: empty, single byte, tiny.
  ZipTest.InflateFast.checkOne "empty" ByteArray.empty
  ZipTest.InflateFast.checkOne "single" (ByteArray.mk #[42])
  ZipTest.InflateFast.checkOne "hello" hello
  -- Block types across levels: stored (0), fixed/dynamic (1, 6, 9).
  for lvl in [0, 1, 6, 9] do
    ZipTest.InflateFast.checkOne s!"hello@L{lvl}" hello lvl.toUInt8
    ZipTest.InflateFast.checkOne s!"big@L{lvl}" big lvl.toUInt8
  -- Highly repetitive data (exercises overlapping / RLE back-references, the
  -- `copyWithinAt` doubling smear path).
  let rle := ByteArray.mk (Array.replicate 5000 0x41)
  ZipTest.InflateFast.checkOne "rle" rle
  -- Longer varied buffer (multiple dynamic blocks, long matches).
  let varied := ByteArray.mk (Array.ofFn (n := 40000) (fun i => (i.val % 251).toUInt8))
  ZipTest.InflateFast.checkOne "varied" varied
  -- Margin-boundary sizes: the `uset` fastloop's per-symbol `outPos + 299 ≤
  -- output.size` guard transitions here between the hot margin body and the
  -- `< 299`-byte tail delegation to `goCur`. Sweep both sides across levels.
  for n in [1, 2, 297, 298, 299, 300, 301, 557, 598, 599, 600, 601] do
    let d := ByteArray.mk (Array.ofFn (n := n) (fun i => (i.val * 7 % 251).toUInt8))
    for lvl in [0, 6, 9] do
      ZipTest.InflateFast.checkOne s!"margin{n}@L{lvl}" d lvl.toUInt8
