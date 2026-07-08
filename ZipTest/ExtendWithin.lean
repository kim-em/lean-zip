import ZipTest.Helpers
import Zip.Native.ExtendWithin

/-! Conformance tests for the overlapping-match copy `@[extern]`
    `ByteArray.extendWithin` (which runs the C in `c/extend_within_ffi.c`).

    Each test compares the compiled extern against an **independent** per-byte
    reference `refExtend` — not the extern's own `fillDouble`-based reference
    body — so the comparison validates the C (and, transitively, that the C
    agrees with the trusted body). We sweep every in-bounds `(srcOff, distance,
    length)`, including the `distance = 1` RLE `memset` path, the doubling
    smear (`distance < length`, non-power-of-2 `length` to hit the clamped final
    chunk), the `length ≤ distance` short case, and the empty-window edges
    (`distance = 0`, `srcOff ≥ size`, `length = 0`). Copy-on-write is checked
    against an independent byte snapshot; a separate chained sweep exercises the
    in-place (exclusive-array) growth path the decoders actually take. -/

namespace ZipTest.ExtendWithin

/-- Independent per-byte reference for `ByteArray.extendWithin` (no `@[extern]`,
    no `fillDouble`): append `length` bytes, byte `i` being `a[srcOff + i % p]`
    where `p` is the effective period `min distance (a.size - srcOff)` — the
    clamped window `extract` produces — with an empty window appending nothing. -/
def refExtend (a : ByteArray) (srcOff distance length : Nat) : ByteArray :=
  let period := if srcOff < a.size then min distance (a.size - srcOff) else 0
  if period = 0 then a
  else (List.range length).foldl (fun acc i => acc.push a[srcOff + i % period]!) a

/-- Compare extern vs reference for one `(srcOff, distance, length)`, and (with
    a shared input) verify copy-on-write against an independent snapshot. -/
def checkOne (a : ByteArray) (srcOff distance length : Nat) : IO Unit := do
  let snapshot := a.extract 0 a.size  -- independent copy of the bytes
  let got := ByteArray.extendWithin a srcOff distance length
  let want := refExtend a srcOff distance length
  unless got == want do
    throw (IO.userError
      s!"extendWithin mismatch at srcOff {srcOff}, distance {distance}, length {length}: \
         got {got.toList}, want {want.toList}")
  unless snapshot == a do
    throw (IO.userError
      s!"extendWithin mutated a shared array at srcOff {srcOff}, distance {distance}")

/-- A spread of `length`s: `0`, powers of two and their neighbours (to hit both
    the exact-doubling and clamped-final-chunk paths), and a large value. -/
def lengths : List Nat := [0, 1, 2, 3, 7, 8, 9, 15, 16, 17, 31, 63, 100]

/-- Sweep every decoder-shaped call on `a`: `srcOff = a.size - distance` (the
    back-reference window ending at the tail) and `srcOff = 0`, over every
    `distance` from `1` to `a.size`, and every `length`. -/
def sweep (a : ByteArray) : IO Unit := do
  for distance in List.range (a.size + 1) do
    if distance ≥ 1 ∧ distance ≤ a.size then
      for length in lengths do
        checkOne a (a.size - distance) distance length
        checkOne a 0 distance length

/-- Byte patterns: constant (RLE), ascending, high-bit, and a mixed run. -/
def patterns : List ByteArray :=
  [ ByteArray.mk (Array.replicate 12 0xAB),
    ByteArray.mk (Array.range 12 |>.map (·.toUInt8)),
    ByteArray.mk (Array.range 12 |>.map (fun i => (0x80 ||| i).toUInt8)),
    ByteArray.mk #[0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07],
    ByteArray.mk #[0xFF] ]

/-- Exercise the in-place growth path: repeatedly append the tail-`distance`
    window (as a real overlapping back-reference does), chaining the extern on an
    unshared array and the reference on an independently built one. -/
partial def chain (distance step : Nat) (steps : Nat)
    (got want : ByteArray) : IO Unit := do
  if steps = 0 then pure ()
  else
    let srcOff := got.size - distance
    let got' := ByteArray.extendWithin got srcOff distance step
    let want' := refExtend want srcOff distance step
    unless got' == want' do
      throw (IO.userError s!"extendWithin chain mismatch (distance {distance}, \
        remaining {steps}): got {got'.toList}, want {want'.toList}")
    chain distance step (steps - 1) got' want'

def tests : IO Unit := do
  for a in patterns do
    sweep a
  -- Empty-window edges: distance 0, and srcOff at/over the end → append nothing.
  let a := patterns.head!
  checkOne a 0 0 8            -- distance 0
  checkOne a a.size 3 8      -- srcOff = size
  checkOne a (a.size + 5) 3 8 -- srcOff past end
  -- In-place growth chains: distance 1 (RLE / memset) and a small window that
  -- must smear forward across several appends.
  chain 1 5 6 (ByteArray.mk #[0x5A]) (ByteArray.mk #[0x5A])
  chain 3 7 5 (ByteArray.mk #[0x01, 0x02, 0x03]) (ByteArray.mk #[0x01, 0x02, 0x03])
  -- Direct spot-check of the RLE broadcast (distance 1) and a period-3 fill.
  let rle := ByteArray.extendWithin (ByteArray.mk #[0x42]) 0 1 5
  unless rle == ByteArray.mk #[0x42, 0x42, 0x42, 0x42, 0x42, 0x42] do
    throw (IO.userError "extendWithin RLE spot-check failed")
  let per3 := ByteArray.extendWithin (ByteArray.mk #[0x0A, 0x0B, 0x0C]) 0 3 7
  unless per3 == ByteArray.mk #[0x0A, 0x0B, 0x0C, 0x0A, 0x0B, 0x0C, 0x0A, 0x0B, 0x0C, 0x0A] do
    throw (IO.userError "extendWithin period-3 spot-check failed")
  IO.println "ExtendWithin conformance tests: OK"

end ZipTest.ExtendWithin
