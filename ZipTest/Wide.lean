import ZipTest.Helpers

/-! Conformance tests for the word-sized `@[extern]` ByteArray readers
    (`ByteArray.ugetUInt32LE` / `ugetUInt64LE`).

    Each test compares the compiled `@[extern]` result (which runs the C in
    `c/bytearray_wide_ffi.c`) against a pure-Lean reference recombination of the
    same bytes — i.e. the `@[extern]`'s own reference body, but evaluated without
    the extern so the comparison validates the C against the model. We sweep all
    in-bounds offsets (including the `off + W/8 == size` boundary) over several
    byte patterns. -/

namespace ZipTest.Wide

/-- Pure-Lean reference for the little-endian `UInt32` load (no `@[extern]`). -/
def refU32LE (a : ByteArray) (off : Nat) : UInt32 :=
  a[off]!.toUInt32 |||
  (a[off + 1]!.toUInt32 <<< 8) |||
  (a[off + 2]!.toUInt32 <<< 16) |||
  (a[off + 3]!.toUInt32 <<< 24)

/-- Pure-Lean reference for the little-endian `UInt64` load (no `@[extern]`). -/
def refU64LE (a : ByteArray) (off : Nat) : UInt64 :=
  a[off]!.toUInt64 |||
  (a[off + 1]!.toUInt64 <<< 8) |||
  (a[off + 2]!.toUInt64 <<< 16) |||
  (a[off + 3]!.toUInt64 <<< 24) |||
  (a[off + 4]!.toUInt64 <<< 32) |||
  (a[off + 5]!.toUInt64 <<< 40) |||
  (a[off + 6]!.toUInt64 <<< 48) |||
  (a[off + 7]!.toUInt64 <<< 56)

/-- Check every in-bounds 4-byte offset of `a`, extern vs reference. The `USize`
    index is passed straight to the extern, so its bound `off.toNat + 4 ≤ size`
    is exactly the dif-condition. -/
partial def checkU32 (a : ByteArray) (off : USize := 0) : IO Unit := do
  if h : off.toNat + 4 ≤ a.size then
    let got := ByteArray.ugetUInt32LE a off h
    let want := refU32LE a off.toNat
    unless got == want do
      throw (IO.userError s!"ugetUInt32LE mismatch at off {off.toNat}: got {got}, want {want}")
    checkU32 a (off + 1)

/-- Check every in-bounds 8-byte offset of `a`, extern vs reference. -/
partial def checkU64 (a : ByteArray) (off : USize := 0) : IO Unit := do
  if h : off.toNat + 8 ≤ a.size then
    let got := ByteArray.ugetUInt64LE a off h
    let want := refU64LE a off.toNat
    unless got == want do
      throw (IO.userError s!"ugetUInt64LE mismatch at off {off.toNat}: got {got}, want {want}")
    checkU64 a (off + 1)

/-- A spread of byte patterns: zeros, max bytes, ascending, descending, and a
    high-bit-set pattern (to catch sign-extension bugs in the recombination). -/
def patterns : List ByteArray :=
  [ ByteArray.mk (Array.replicate 20 0),
    ByteArray.mk (Array.replicate 20 0xFF),
    ByteArray.mk (Array.range 20 |>.map (·.toUInt8)),
    ByteArray.mk (Array.range 20 |>.map (fun i => (19 - i).toUInt8)),
    ByteArray.mk (Array.range 20 |>.map (fun i => (0x80 ||| i).toUInt8)),
    -- Exactly word-sized: hits only the `off + W/8 == size` boundary.
    ByteArray.mk #[0xDE, 0xAD, 0xBE, 0xEF, 0xCA, 0xFE, 0xBA, 0xBE] ]

def tests : IO Unit := do
  for a in patterns do
    checkU32 a
    checkU64 a
  -- A direct spot-check of a known little-endian value.
  let a := ByteArray.mk #[0x78, 0x56, 0x34, 0x12, 0xF0, 0xDE, 0xBC, 0x9A]
  unless ByteArray.ugetUInt32LE a 0 (by decide) == 0x12345678 do
    throw (IO.userError "ugetUInt32LE spot-check failed")
  unless ByteArray.ugetUInt64LE a 0 (by decide) == 0x9ABCDEF012345678 do
    throw (IO.userError "ugetUInt64LE spot-check failed")
  IO.println "Wide reader conformance tests: OK"

end ZipTest.Wide
