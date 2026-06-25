/-!
  Word-sized little-endian `ByteArray` load for the DEFLATE hash hot loop.

  `ByteArray.ugetUInt32LE a off` reads a 4-byte little-endian word starting at
  byte `off` of `a`. The reference body — and the trusted specification of the
  `@[extern]` — is literally the byte-recombination expression the hot path
  assembles today:

      a[off] ||| a[off+1] <<< 8 ||| a[off+2] <<< 16 ||| a[off+3] <<< 24

  so swapping the inline byte assembly for it is definitional modulo the offset's
  `Nat`/`USize` round-trip; `@[extern]` only changes the compiled implementation
  (`c/bytearray_wide_ffi.c`) to a single wide load. Replacing `hash3`'s four
  bounds-checked byte reads (four `uget` calls) with one `ugetUInt32LE` call is a
  measured ~+3.4% compress win (#2707) — the win is the call-count reduction, and
  it pays because the read is a *fixed* 4 bytes. (The 8-byte `ugetUInt64LE`
  reader was removed: its only intended consumer, the decode refill, tops up ~1
  byte at a time, so the wide load was measured neutral there — #2630.)

  The offset is a `USize`, so a hot loop's index arithmetic stays unboxed (the
  point of mirroring lean#14053's `uget*` readers rather than lean#8165's
  `Nat`-indexed `getUIntN`). The in-bounds hypothesis `off.toNat + 4 ≤ a.size`
  is discharged by the caller's existing guards and means the C does no bounds
  check.

  This is a project-local stopgap mirroring the reader of lean#14053 (`wide
  fixed-width load/store`). The C symbol is namespaced `lean_zip_*` so it does
  not clash with core after the toolchain bump. Migration once lean#14053 lands:
  delete this file and `c/bytearray_wide_ffi.c`, and use core's `uget*`
  primitive (its reference body is identical, so callers and proofs are
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

end ByteArray
