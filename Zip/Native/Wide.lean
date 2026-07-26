import Std.Tactic.BVDecide

/-!
  Word-sized little-endian `ByteArray` loads and stores for the DEFLATE
  hot loops.

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
  it pays because the read is a *fixed* 4 bytes. The 8-byte `ugetUInt64LE`
  reader (below) is the same scheme over eight bytes; it was once removed as
  measured-neutral for the decode refill, which tops up ~1 byte at a time
  (#2630), but the match-extension loop (`lz77Greedy.countMatch`, #2736) is a
  different consumer: it reads runs of many bytes and compares eight per
  iteration, so the wide load pays there.

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

/-- Load the little-endian `UInt64` at byte offset `off`. The reference body is
    the eight-byte analog of `ugetUInt32LE`
    `a[off] ||| a[off+1] <<< 8 ||| … ||| a[off+7] <<< 56`; it is the trusted
    specification of the `@[extern]`, which the C reads in one wide load. The
    match-extension loop compares two of these words per iteration. -/
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

/-- `set` preserves size (missing from core for `ByteArray`; used for the
    chained in-bounds proofs of `usetUInt64LE`'s reference body). -/
protected theorem size_set (a : ByteArray) (i : Nat) (v : UInt8) (h : i < a.size) :
    (a.set i v h).size = a.size := by
  simp only [← ByteArray.size_data, ByteArray.data_set, Array.size_set]

/-- Store the little-endian `UInt64` `v` at byte offset `off`. The reference
    body — the chain of eight `a.set` writes assembling the store byte by
    byte — is the trusted specification of the `@[extern]`; the C
    (`lean_zip_uset_u64le`) performs it as one wide store, in place when the
    array is exclusive. Writer analog of `ugetUInt64LE` (issue #2631); the
    caller's in-bounds proof means the C does no bounds check. Production decode
    uses it for `InflateBuf.goCurU`'s inline short-match copies; the deferred-
    accumulator writer designs also use it in bench variants C/D of
    `ZipWideStoreBench` (the measured 2.5× follow-up ceiling), while the
    production writer flush still uses `pushUInt64LE`. -/
@[extern "lean_zip_uset_u64le"]
def usetUInt64LE (a : ByteArray) (off : USize) (v : UInt64)
    (h : off.toNat + 8 ≤ a.size := by get_elem_tactic) : ByteArray :=
  ((((((((a.set off.toNat v.toUInt8 (by omega)).set
    (off.toNat + 1) (v >>> 8).toUInt8 (by simp only [ByteArray.size_set]; omega)).set
    (off.toNat + 2) (v >>> 16).toUInt8 (by simp only [ByteArray.size_set]; omega)).set
    (off.toNat + 3) (v >>> 24).toUInt8 (by simp only [ByteArray.size_set]; omega)).set
    (off.toNat + 4) (v >>> 32).toUInt8 (by simp only [ByteArray.size_set]; omega)).set
    (off.toNat + 5) (v >>> 40).toUInt8 (by simp only [ByteArray.size_set]; omega)).set
    (off.toNat + 6) (v >>> 48).toUInt8 (by simp only [ByteArray.size_set]; omega)).set
    (off.toNat + 7) (v >>> 56).toUInt8 (by simp only [ByteArray.size_set]; omega))

/-- Reference model for `pushUInt64LE`: push the low `k` bytes of `v`,
    LSB-first. This is exactly the shape of the BitWriter's byte-flush loop
    (`BitWriter.flushBytes`), so wiring the wide store into the writer is a
    definitional step. -/
def pushLEBytes (a : ByteArray) (v : UInt64) : Nat → ByteArray
  | 0 => a
  | k + 1 => pushLEBytes (a.push v.toUInt8) (v >>> 8) k

/-- Append the low `k` bytes (`k ≤ 8`) of `v`, LSB-first — the wide-store form
    of the BitWriter's per-byte flush loop. The reference body `pushLEBytes`
    is the trusted specification of the `@[extern]`; the C
    (`lean_zip_push_u64le`) appends them as one unconditional 8-byte store
    into capacity slack plus a size bump of `k` when the array is exclusive
    with room, falling back to the model's byte pushes otherwise. The `k ≤ 8`
    proof is what makes the single 8-byte store cover every appended byte. -/
@[extern "lean_zip_push_u64le"]
def pushUInt64LE (a : ByteArray) (v : UInt64) (k : USize)
    (h : k.toNat ≤ 8) : ByteArray :=
  pushLEBytes a v k.toNat

end ByteArray

/-- Count trailing zero bits of a `UInt64` (zero case defined as 64). This is the
    pure logical *specification* — its body is `BitVec.ctz`, kept for the
    match-extension proofs (`ctz (w1 ^^^ w2) >>> 3` is the little-endian byte
    index of the first differing byte between two 8-byte words). It carries no
    `@[extern]`: the runtime is supplied by `UInt64.ctzFast` via the `@[csimp]`
    bridge below, so every compiled call to `UInt64.ctz` becomes a call to
    `UInt64.ctzFast` — whose C `@[extern]` compiles to a single `tzcnt`/`bsf`. -/
def UInt64.ctz (x : UInt64) : UInt64 := ⟨BitVec.ctz x.toBitVec⟩

/-- The runtime implementation of counting trailing zeros: a branchy binary
    search over native `UInt64` ops only (`&&&`, `>>>`, `==`, `+`). The C
    `@[extern]` (`lean_zip_ctz64`) compiles it to one `tzcnt`/`bsf`; this fast
    pure-Lean body — proven equal to `UInt64.ctz` (= `BitVec.ctz`) by the
    `@[csimp]` lemma below — is the trusted specification of that extern *and* the
    compiled fallback when the C symbol is unavailable (the interpreter, or a
    platform without the shim), so the fallback runs within ~1% of `tzcnt`, not
    the ~64× slower `BitVec.ctz`. Nested-`if` form (no `do`-notation) so
    `bv_decide` reduces it cleanly. -/
@[extern "lean_zip_ctz64"]
def UInt64.ctzFast (x : UInt64) : UInt64 :=
  if x == 0 then 64 else
    let s5 : UInt64 := if x &&& 0xFFFFFFFF == 0 then 32 else 0
    let x5 := x >>> s5
    let s4 : UInt64 := if x5 &&& 0xFFFF == 0 then 16 else 0
    let x4 := x5 >>> s4
    let s3 : UInt64 := if x4 &&& 0xFF == 0 then 8 else 0
    let x3 := x4 >>> s3
    let s2 : UInt64 := if x3 &&& 0xF == 0 then 4 else 0
    let x2 := x3 >>> s2
    let s1 : UInt64 := if x2 &&& 0x3 == 0 then 2 else 0
    let x1 := x2 >>> s1
    let s0 : UInt64 := if x1 &&& 0x1 == 0 then 1 else 0
    s5 + s4 + s3 + s2 + s1 + s0

/-- `UInt64.ctz` (the `BitVec.ctz` spec) computes exactly `UInt64.ctzFast` (the
    fast binary search). Registered `@[csimp]`, so every compiled call to
    `UInt64.ctz` is replaced by `UInt64.ctzFast` — which is `@[extern]`, hence the
    production path is the C `tzcnt` (measured 0% cost) while the fallback stays
    the fast pure-Lean search. -/
@[csimp] theorem UInt64.ctz_eq_ctzFast : UInt64.ctz = UInt64.ctzFast := by
  funext x
  unfold UInt64.ctz UInt64.ctzFast
  bv_decide
