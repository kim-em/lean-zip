/-!
  Word-sized little-endian `ByteArray` loads for the DEFLATE hot loops.

  `ByteArray.ugetUInt32LE a off` and `ByteArray.ugetUInt64LE a off` read a 4- or
  8-byte little-endian word starting at byte `off` of `a`. The reference body —
  and the trusted specification of the `@[extern]` — is literally the
  byte-recombination expression the hot paths assemble today:

      a[off] ||| a[off+1] <<< 8 ||| a[off+2] <<< 16 ||| a[off+3] <<< 24     (u32)
      a[off] ||| a[off+1] <<< 8 ||| ... ||| a[off+7] <<< 56                 (u64)

  so swapping the inline byte assembly for one of these is definitional modulo
  the offset's `Nat`/`USize` round-trip; `@[extern]` only changes the compiled
  implementation (`c/bytearray_wide_ffi.c`) to a single wide load.

  The offset is a `USize`, so a hot loop's index arithmetic stays unboxed (the
  point of mirroring lean#14053's `uget*` readers rather than lean#8165's
  `Nat`-indexed `getUIntN`). The in-bounds hypothesis `off.toNat + W/8 ≤ a.size`
  is discharged by the caller's existing guards and means the C does no bounds
  check.

  This is a project-local stopgap mirroring the readers of lean#14053 (`wide
  fixed-width load/store`). The C symbols are namespaced `lean_zip_*` so they do
  not clash with core after the toolchain bump. Migration once lean#14053 lands:
  delete this file and `c/bytearray_wide_ffi.c`, and use core's `uget*`
  primitives (their reference bodies are identical, so callers and proofs are
  unchanged).
-/

namespace ByteArray

/-- Load the little-endian `UInt32` at byte offset `off`. The reference body
    `a[off] ||| a[off+1] <<< 8 ||| a[off+2] <<< 16 ||| a[off+3] <<< 24` is the
    trusted specification of the `@[extern]`; the C reads it in one wide load. -/
@[extern "lean_zip_uget_u32le"]
def ugetUInt32LE (a : @& ByteArray) (off : USize)
    (h : off.toNat + 4 ≤ a.size := by get_elem_tactic) : UInt32 :=
  (a[off.toNat]'(by omega)).toUInt32 |||
  ((a[off.toNat + 1]'(by omega)).toUInt32 <<< 8) |||
  ((a[off.toNat + 2]'(by omega)).toUInt32 <<< 16) |||
  ((a[off.toNat + 3]'(by omega)).toUInt32 <<< 24)

/-- Load the little-endian `UInt64` at byte offset `off`. The reference body
    `a[off] ||| a[off+1] <<< 8 ||| ... ||| a[off+7] <<< 56` is the trusted
    specification of the `@[extern]`; the C reads it in one wide load. -/
@[extern "lean_zip_uget_u64le"]
def ugetUInt64LE (a : @& ByteArray) (off : USize)
    (h : off.toNat + 8 ≤ a.size := by get_elem_tactic) : UInt64 :=
  (a[off.toNat]'(by omega)).toUInt64 |||
  ((a[off.toNat + 1]'(by omega)).toUInt64 <<< 8) |||
  ((a[off.toNat + 2]'(by omega)).toUInt64 <<< 16) |||
  ((a[off.toNat + 3]'(by omega)).toUInt64 <<< 24) |||
  ((a[off.toNat + 4]'(by omega)).toUInt64 <<< 32) |||
  ((a[off.toNat + 5]'(by omega)).toUInt64 <<< 40) |||
  ((a[off.toNat + 6]'(by omega)).toUInt64 <<< 48) |||
  ((a[off.toNat + 7]'(by omega)).toUInt64 <<< 56)

end ByteArray
