import ZipTest.Helpers

/-! Conformance tests for the word-sized `@[extern]` ByteArray readers
    (`ByteArray.ugetUInt32LE`, `ByteArray.ugetUInt64LE`) and writers
    (`ByteArray.usetUInt64LE`, `ByteArray.pushUInt64LE`).

    Each test compares the compiled `@[extern]` result (which runs the C in
    `c/bytearray_wide_ffi.c`) against a pure-Lean reference recombination of the
    same bytes — i.e. the `@[extern]`'s own reference body, but evaluated without
    the extern so the comparison validates the C against the model. We sweep all
    in-bounds offsets (including the `off + N == size` boundary) over several
    byte patterns. The writers additionally check copy-on-write semantics (a
    shared input array is left unchanged) and, for `pushUInt64LE`, both C paths:
    the wide-store fast path (exclusive array with capacity slack) and the
    byte-push fallback (shared arrays, capacity-tight arrays). -/

namespace ZipTest.Wide

/-- Pure-Lean reference for the little-endian `UInt32` load (no `@[extern]`). -/
def refU32LE (a : ByteArray) (off : Nat) : UInt32 :=
  a[off]!.toUInt32 |||
  (a[off + 1]!.toUInt32 <<< 8) |||
  (a[off + 2]!.toUInt32 <<< 16) |||
  (a[off + 3]!.toUInt32 <<< 24)

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
    -- Exactly word-sized: hits only the `off + 4 == size` boundary.
    ByteArray.mk #[0xDE, 0xAD, 0xBE, 0xEF] ]

/-- Byte patterns at least 8 wide, for the 64-bit reader (includes an exactly
    8-byte array to hit the `off + 8 == size` boundary). -/
def patterns64 : List ByteArray :=
  [ ByteArray.mk (Array.replicate 20 0),
    ByteArray.mk (Array.replicate 20 0xFF),
    ByteArray.mk (Array.range 20 |>.map (·.toUInt8)),
    ByteArray.mk (Array.range 20 |>.map (fun i => (19 - i).toUInt8)),
    ByteArray.mk (Array.range 20 |>.map (fun i => (0x80 ||| i).toUInt8)),
    ByteArray.mk #[0xEF, 0xCD, 0xAB, 0x89, 0x67, 0x45, 0x23, 0x01] ]

/-- Pure-Lean reference for the little-endian `UInt64` store (no `@[extern]`):
    the eight byte writes of `usetUInt64LE`'s reference body, via `set!`. -/
def refUset64LE (a : ByteArray) (off : Nat) (v : UInt64) : ByteArray :=
  (((((((a.set! off v.toUInt8).set!
    (off + 1) (v >>> 8).toUInt8).set!
    (off + 2) (v >>> 16).toUInt8).set!
    (off + 3) (v >>> 24).toUInt8).set!
    (off + 4) (v >>> 32).toUInt8).set!
    (off + 5) (v >>> 40).toUInt8).set!
    (off + 6) (v >>> 48).toUInt8).set!
    (off + 7) (v >>> 56).toUInt8

/-- Test values with distinct bytes, high bits set, zeros, and all-ones. -/
def storeValues : List UInt64 :=
  [0x0123456789ABCDEF, 0xFEDCBA9876543210, 0, 0xFFFFFFFFFFFFFFFF, 0x80]

/-- A `Nat` `k ≤ 8` survives the `toUSize` round-trip below 8 — discharges
    `pushUInt64LE`'s `k ≤ 8` side condition for a small loop counter. -/
private theorem toUSize_toNat_le_8 {k : Nat} (h : k ≤ 8) : k.toUSize.toNat ≤ 8 := by
  rw [Nat.toUSize_eq,
    USize.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt h (by cases USize.size_eq <;> omega))]
  exact h

/-- Check every in-bounds 8-byte offset of `a`: extern store vs reference,
    plus copy-on-write (the shared input must be unchanged afterwards —
    compared against an independent byte snapshot, since an alias would
    still compare equal after a wrongful in-place mutation). -/
partial def checkUset64 (a : ByteArray) (off : USize := 0) : IO Unit := do
  if h : off.toNat + 8 ≤ a.size then
    let snapshot := a.extract 0 a.size  -- independent copy of the bytes
    for v in storeValues do
      let got := ByteArray.usetUInt64LE a off v h
      let want := refUset64LE a off.toNat v
      unless got == want do
        throw (IO.userError
          s!"usetUInt64LE mismatch at off {off.toNat}, v {v}: got {got}, want {want}")
      unless snapshot == a do
        throw (IO.userError s!"usetUInt64LE mutated a shared array at off {off.toNat}")
    checkUset64 a (off + 1)

/-- Exercise the in-place (exclusive-array) path of `usetUInt64LE`: a chain
    of stores at successive offsets on an unshared array, checked against the
    same chain of reference stores. -/
partial def checkUset64Exclusive (off : USize := 0)
    (got : ByteArray := ByteArray.mk (Array.replicate 20 0x55))
    (want : ByteArray := ByteArray.mk (Array.replicate 20 0x55))
    (v : UInt64 := 0x0123456789ABCDEF) : IO Unit := do
  if h : off.toNat + 8 ≤ got.size then
    let got' := ByteArray.usetUInt64LE got off v h
    let want' := refUset64LE want off.toNat v
    unless got' == want' do
      throw (IO.userError s!"usetUInt64LE exclusive-chain mismatch at off {off.toNat}")
    checkUset64Exclusive (off + 1) got' want'
      (v * 6364136223846793005 + 1442695040888963407)

/-- Pure-Lean reference for the wide append (no `@[extern]`): push the low
    `k` bytes of `v`, LSB-first — `pushUInt64LE`'s reference body. -/
def refPush64LE (a : ByteArray) (v : UInt64) : Nat → ByteArray
  | 0 => a
  | k + 1 => refPush64LE (a.push v.toUInt8) (v >>> 8) k

/-- Check `pushUInt64LE` against the reference for every `k ≤ 8` on `a`,
    plus copy-on-write of the shared input (snapshot comparison as above). -/
partial def checkPush64 (a : ByteArray) (k : Nat := 0) : IO Unit := do
  if h : k ≤ 8 then
    let snapshot := a.extract 0 a.size
    for v in storeValues do
      let got := ByteArray.pushUInt64LE a v k.toUSize (toUSize_toNat_le_8 h)
      let want := refPush64LE a v k
      unless got == want do
        throw (IO.userError
          s!"pushUInt64LE mismatch at k {k}, v {v}: got {got}, want {want}")
      unless snapshot == a do
        throw (IO.userError s!"pushUInt64LE mutated a shared array at k {k}")
    checkPush64 a (k + 1)

/-- Exercise the exclusive-array paths of `pushUInt64LE`: a chain of pushes
    onto an unshared array (byte-push fallback while capacity is tight, wide
    fast path once push-doubling leaves ≥ 8 bytes of slack), checked against
    the same chain of reference pushes. -/
partial def checkPush64Exclusive (k : Nat := 0)
    (got : ByteArray := ByteArray.mk #[0xAA])  -- ByteArray.mk: capacity = size
    (want : ByteArray := ByteArray.mk #[0xAA])
    (v : UInt64 := 0x0123456789ABCDEF) : IO Unit := do
  if h : k ≤ 8 then
    let got' := ByteArray.pushUInt64LE got v k.toUSize (toUSize_toNat_le_8 h)
    let want' := refPush64LE want v k
    unless got' == want' do
      throw (IO.userError s!"pushUInt64LE exclusive-chain mismatch at k {k}")
    checkPush64Exclusive (k + 1) got' want'
      (v * 6364136223846793005 + 1442695040888963407)

def tests : IO Unit := do
  for a in patterns do
    checkU32 a
  for a in patterns64 do
    checkU64 a
  for a in patterns64 do
    checkUset64 a
  checkUset64Exclusive
  for a in [ByteArray.empty] ++ patterns64 do
    checkPush64 a
  checkPush64Exclusive
  -- Direct spot-checks of known little-endian byte placement.
  let z := ByteArray.mk #[0, 0, 0, 0, 0, 0, 0, 0, 0xAA]
  let stored := ByteArray.usetUInt64LE z 0 0x0123456789ABCDEF (by decide)
  unless stored == ByteArray.mk #[0xEF, 0xCD, 0xAB, 0x89, 0x67, 0x45, 0x23, 0x01, 0xAA] do
    throw (IO.userError "usetUInt64LE spot-check failed")
  let pushed := ByteArray.pushUInt64LE (ByteArray.mk #[0x77]) 0x0123456789ABCDEF
    (3 : Nat).toUSize (toUSize_toNat_le_8 (by omega))
  unless pushed == ByteArray.mk #[0x77, 0xEF, 0xCD, 0xAB] do
    throw (IO.userError "pushUInt64LE spot-check failed")
  -- Direct spot-checks of known little-endian values.
  let a := ByteArray.mk #[0x78, 0x56, 0x34, 0x12]
  unless ByteArray.ugetUInt32LE a 0 (by decide) == 0x12345678 do
    throw (IO.userError "ugetUInt32LE spot-check failed")
  let b := ByteArray.mk #[0xEF, 0xCD, 0xAB, 0x89, 0x67, 0x45, 0x23, 0x01]
  unless ByteArray.ugetUInt64LE b 0 (by decide) == 0x0123456789ABCDEF do
    throw (IO.userError "ugetUInt64LE spot-check failed")
  IO.println "Wide reader conformance tests: OK"

end ZipTest.Wide
