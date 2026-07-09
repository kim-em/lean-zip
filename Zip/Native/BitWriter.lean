import Std.Tactic.BVDecide
import Zip.Native.Wide

/-!
  LSB-first bit packer for DEFLATE streams.

  DEFLATE (RFC 1951) packs bits LSB-first within each byte.
  This module provides a stateful writer that accumulates bits
  into a wide pending buffer, flushing complete bytes to a ByteArray.

  Fields are packed in bulk: a whole `writeBits`/`writeHuffCode` field is
  merged into the 64-bit pending accumulator (`bitBuf`) in one shift/OR. Rather
  than flush every completed byte immediately (one `pushUInt64LE` FFI store per
  field — the dominant emit cost once the per-bit loop was removed, #2631), the
  writer **holds up to 31 pending bits** and flushes whole bytes only when the
  pending count reaches `flushThreshold` (32). One store then drains 4–7 bytes
  at once, cutting the FFI store count on a literal-heavy stream ~4× (measured
  ~+22-29% on the dynamic emit walk, ~+7-8% on full L1 — #2734). This is
  byte-identical to flushing every field: `toBits` (hence `bitLength` and the
  final `flush` output) depends only on the total bit sequence, not on when
  whole bytes are drained to `data`.
-/
namespace Zip.Native

/-- Pending-bit count at or above which whole bytes are drained to `data`.
    Below it, bits stay in the `bitBuf` accumulator (batched). At most one field
    (`≤ 25` bits) is added before the check, and the pre-check count is `< 32`,
    so the accumulator never exceeds `31 + 25 = 56 < 64` bits. -/
def flushThreshold : Nat := 32

structure BitWriter where
  data : ByteArray
  bitBuf : UInt64   -- pending bits, LSB-first (0 ≤ bitCount valid low bits)
  bitCount : UInt8  -- number of valid pending bits in bitBuf (0-31)

namespace BitWriter

def empty : BitWriter := ⟨.empty, 0, 0⟩

/-- Total number of bits written so far: 8 per fully flushed byte in `data`
    plus the `bitCount` bits held in the partial byte. Used by the DEFLATE
    compressor to size a block (`⌈bitLength/8⌉` bytes after `flush`) without
    materialising it. -/
def bitLength (bw : BitWriter) : Nat := bw.data.size * 8 + bw.bitCount.toNat

/-- Flush whole bytes out of a wide accumulator `acc` holding `total` valid
    low bits, LSB-first. Pushes `total / 8` bytes to `data`; the remaining
    `total % 8` bits become the new partial byte.

    Reference form only: the production writers use the split
    `flushBytes`/`dropBytes` loops (equal by `flushAcc_eq`, which the
    `writeBits_def`/`writeHuffCode_def` equations build on) so the `BitWriter`
    cell is constructed in the caller, where the ctor-reuse optimization can
    recycle the input writer instead of allocating a fresh cell per field
    (measured at ~59%/~19% of `mi_malloc_small` calls on L1/L8 compress,
    #2739). -/
def flushAcc (data : ByteArray) (acc : UInt64) : Nat → BitWriter
  | total =>
    if total ≥ 8 then
      flushAcc (data.push acc.toUInt8) (acc >>> 8) (total - 8)
    else
      ⟨data, acc, total.toUInt8⟩
  termination_by total => total

/-- The byte-pushing half of `flushAcc`: push the low `k` whole bytes of
    `acc`, LSB-first. Returns only the grown `ByteArray` — the leftover
    partial-byte state is pure arithmetic (`dropBytes`), so the caller can
    build the result `BitWriter` itself and have ctor reuse recycle its
    input cell. -/
def flushBytes (data : ByteArray) (acc : UInt64) : Nat → ByteArray
  | 0 => data
  | k + 1 => flushBytes (data.push acc.toUInt8) (acc >>> 8) k

/-- The accumulator half of `flushAcc`: `acc` after `k` byte-sized right
    shifts (the value whose low bits become the new partial byte). Iterated
    `>>> 8` rather than `>>> (8*k)` so it agrees with `flushAcc` for *every*
    `k`, not just `8*k < 64`. -/
def dropBytes (acc : UInt64) : Nat → UInt64
  | 0 => acc
  | k + 1 => dropBytes (acc >>> 8) k

/-- A `Nat` `≤ 8` survives the `toUSize` round-trip on every platform —
    discharges `pushUInt64LE`'s `k ≤ 8` side condition in `flushBytesWide`
    and its correctness proof. -/
private theorem toUSize_toNat_of_le_8 {k : Nat} (h : k ≤ 8) : k.toUSize.toNat = k := by
  rw [Nat.toUSize_eq]
  exact USize.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt h (by cases USize.size_eq <;> omega))

/-- `flushBytes` through the wide store: one `pushUInt64LE` call (an 8-byte
    store into capacity slack plus a size bump, `c/bytearray_wide_ffi.c`)
    replaces the `k`-iteration per-byte push loop. The writers always take
    the wide branch — under batching the pending count is `< flushThreshold = 32`
    before a field, so `k = total / 8 ≤ (31 + 25) / 8 = 7 ≤ 8` — but the guard
    keeps the function total on all inputs, falling back to the push loop.
    Kernel-measured 1.4× over the push loop on a synthetic L1-like field
    trace (`lake exe wide-store-bench`, issue #2631 step 0). -/
@[inline] def flushBytesWide (data : ByteArray) (acc : UInt64) (k : Nat) : ByteArray :=
  if h : k ≤ 8 then
    data.pushUInt64LE acc k.toUSize (by rw [toUSize_toNat_of_le_8 h]; exact h)
  else
    flushBytes data acc k

/-- The wide-store reference model unrolls to exactly the per-byte push
    loop (they are the same recursion). -/
theorem pushLEBytes_eq_flushBytes (data : ByteArray) (acc : UInt64) (k : Nat) :
    ByteArray.pushLEBytes data acc k = flushBytes data acc k := by
  induction k generalizing data acc with
  | zero => rfl
  | succ k ih => rw [ByteArray.pushLEBytes, flushBytes, ih]

/-- `flushBytesWide` is `flushBytes`: the wide branch is the model's push
    loop by `pushLEBytes_eq_flushBytes`, the fallback is definitional. -/
theorem flushBytesWide_eq (data : ByteArray) (acc : UInt64) (k : Nat) :
    flushBytesWide data acc k = flushBytes data acc k := by
  unfold flushBytesWide
  split
  next h =>
    rw [ByteArray.pushUInt64LE, pushLEBytes_eq_flushBytes]
    congr 1
    exact toUSize_toNat_of_le_8 h
  next => rfl

/-- `flushAcc` is the split pair `flushBytes`/`dropBytes`: the byte pushes
    and the leftover accumulator commute past each other. -/
theorem flushAcc_eq (data : ByteArray) (acc : UInt64) (total : Nat) :
    flushAcc data acc total =
      ⟨flushBytes data acc (total / 8), dropBytes acc (total / 8),
        (total % 8).toUInt8⟩ := by
  induction total using Nat.strongRecOn generalizing data acc with
  | _ total ih =>
    rw [flushAcc]
    by_cases hge : total ≥ 8
    · rw [if_pos hge, ih (total - 8) (by omega)]
      have hdiv : total / 8 = (total - 8) / 8 + 1 := by omega
      have hmod : (total - 8) % 8 = total % 8 := by omega
      rw [hdiv, hmod, flushBytes, dropBytes]
    · rw [if_neg hge]
      have h8 : total / 8 = 0 := by omega
      have hm : total % 8 = total := by omega
      rw [h8, hm, flushBytes, dropBytes]

/-- Batched flush: drain whole bytes only when the pending count reaches
    `flushThreshold`, else keep every bit in the accumulator. Reference form of
    the flush cadence the production `writeBits`/`writeHuffCode` use (they call
    the scalar `flushBatchedU`, equal by `flushBatchedU_eq`; the ctor is built
    in the writer after inlining, so ctor reuse still recycles the input cell).
    Byte-identical to `flushAcc` in output bits — only the split between `data`
    and the pending accumulator differs. -/
def flushBatched (data : ByteArray) (acc : UInt64) (total : Nat) : BitWriter :=
  if total ≥ flushThreshold then flushAcc data acc total
  else ⟨data, acc, total.toUInt8⟩

/-! ### Scalar-arithmetic flush kernel (#2827)

The writers run once per DEFLATE field — the hottest call sites in compress
(11–17% of L1 between `writeHuffCode`/`writeBits` self time). The reference
forms above do the per-field bookkeeping in `Nat` (`total`, `total / 8`,
`total % 8`, the `dropBytes` recursion), which the compiler emits as tagged
`lean_nat_*` calls plus an out-of-line `dropBytes` loop on every flush. The
`*U` forms below do the same arithmetic in `UInt32`/`UInt64` registers —
`total` fits `UInt32` exactly (`bitCount, len < 256`, so `total < 512`),
`/ 8` is `>>> 3`, `% 8` is `&&& 7`, and `dropBytes` collapses to one shift
(`dropBytesU_eq`). Each is proven equal to its reference form, so
`writeBits_def`/`writeHuffCode_def` (the equations all spec proofs anchor on)
keep their exact statements. -/

/-- `dropBytes` as a single shift: `k` byte-shifts of a 64-bit accumulator is
    `>>> 8k` for `k < 8` and `0` once every byte has been shifted out
    (`dropBytesU_eq`). Deliberately *not* `@[inline]`: inlining its branch
    into the writers' flush arm makes the ctor-reuse pass pick the flush-arm
    join as the sole reuse site, demoting the hot no-flush arm to
    free-then-alloc (measured −13% on dickens L1). As an out-call (like the
    old `dropBytes`) both writer arms keep in-place reuse. -/
def dropBytesU (acc : UInt64) (k : UInt32) : UInt64 :=
  if k < 8 then acc >>> (k.toUInt64 <<< 3) else 0

/-- `dropBytes` shifts by whole bytes: below 8 iterations it is one `>>> 8k`. -/
private theorem dropBytes_of_lt_8 (acc : UInt64) (k : Nat) (h : k < 8) :
    dropBytes acc k = acc >>> (8 * k).toUInt64 := by
  match k, h with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    apply UInt64.toNat_inj.mp
    simp only [dropBytes, UInt64.toNat_shiftRight, Nat.reduceMul, Nat.toUInt64_eq,
      UInt64.toNat_ofNat', UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow,
      Nat.reducePow, Nat.div_div_eq_div_mul]
    all_goals omega
  | n + 8, h => omega

/-- After eight byte-shifts nothing of a 64-bit accumulator remains. -/
private theorem dropBytes_eight (acc : UInt64) : dropBytes acc 8 = 0 := by
  simp only [dropBytes]
  bv_decide

/-- `dropBytes` splits over addition of iteration counts. -/
private theorem dropBytes_add (acc : UInt64) (a b : Nat) :
    dropBytes acc (a + b) = dropBytes (dropBytes acc a) b := by
  induction a generalizing acc with
  | zero => rw [Nat.zero_add]; rfl
  | succ a ih =>
    rw [Nat.add_right_comm]
    show dropBytes (acc >>> 8) (a + b) = dropBytes (dropBytes (acc >>> 8) a) b
    exact ih (acc >>> 8)

/-- Shifting nothing yields nothing, for any iteration count. -/
private theorem dropBytes_zero (k : Nat) : dropBytes 0 k = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [dropBytes]; simpa using ih

/-- The scalar `dropBytesU` is `dropBytes` at the `Nat` view of `k`. -/
theorem dropBytesU_eq (acc : UInt64) (k : UInt32) :
    dropBytesU acc k = dropBytes acc k.toNat := by
  unfold dropBytesU
  split
  next h =>
    have hk : k.toNat < 8 := by
      have := UInt32.lt_iff_toNat_lt.mp h
      simpa using this
    rw [dropBytes_of_lt_8 acc k.toNat hk]
    congr 1
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_shiftLeft, UInt32.toNat_toUInt64, Nat.toUInt64_eq, UInt64.toNat_ofNat']
    have h3 : (3 : UInt64).toNat = 3 := rfl
    rw [h3, Nat.mod_eq_of_lt (by omega : (3:Nat) < 64), Nat.shiftLeft_eq]
    omega
  next h =>
    have hk : 8 ≤ k.toNat :=
      Nat.le_of_not_lt fun hh => h (UInt32.lt_iff_toNat_lt.mpr (by simpa using hh))
    rw [(by omega : k.toNat = 8 + (k.toNat - 8)), dropBytes_add, dropBytes_eight,
      dropBytes_zero]

/-- `flushBytesWide` with a `UInt32` byte count: the `k ≤ 8` guard is a
    register compare and the `USize` cast is free (`flushBytesWideU_eq`). -/
@[inline] def flushBytesWideU (data : ByteArray) (acc : UInt64) (k : UInt32) : ByteArray :=
  if h : k ≤ 8 then
    data.pushUInt64LE acc k.toUSize (by
      simpa using UInt32.le_iff_toNat_le.mp h)
  else
    flushBytes data acc k.toNat

/-- The scalar `flushBytesWideU` is `flushBytes` at the `Nat` view of `k`. -/
theorem flushBytesWideU_eq (data : ByteArray) (acc : UInt64) (k : UInt32) :
    flushBytesWideU data acc k = flushBytes data acc k.toNat := by
  unfold flushBytesWideU
  split
  next h =>
    rw [ByteArray.pushUInt64LE, pushLEBytes_eq_flushBytes]
    simp
  next => rfl

/-- `flushBatched` in scalar arithmetic: the pending total in `UInt32`
    (exact — both summands are below 256), `/ 8` as `>>> 3`, `% 8` as
    `&&& 7`, `dropBytes` as one shift. Equal to `flushBatched` at the `Nat`
    view of `total` (`flushBatchedU_eq`); `@[inline]` so the result cell is
    constructed in the calling writer, where ctor reuse recycles the input
    `BitWriter` cell (#2739). -/
@[inline] def flushBatchedU (data : ByteArray) (acc : UInt64) (totalU : UInt32) : BitWriter :=
  if totalU ≥ 32 then
    ⟨flushBytesWideU data acc (totalU >>> 3), dropBytesU acc (totalU >>> 3),
      (totalU &&& 7).toUInt8⟩
  else
    ⟨data, acc, totalU.toUInt8⟩

/-- The scalar `flushBatchedU` is `flushBatched` at the `Nat` view of the
    pending total. -/
theorem flushBatchedU_eq (data : ByteArray) (acc : UInt64) (totalU : UInt32) :
    flushBatchedU data acc totalU = flushBatched data acc totalU.toNat := by
  unfold flushBatchedU flushBatched
  have hshift : (totalU >>> 3).toNat = totalU.toNat / 8 := by
    rw [UInt32.toNat_shiftRight]
    have h3 : (3 : UInt32).toNat = 3 := rfl
    rw [h3, Nat.mod_eq_of_lt (by omega : (3:Nat) < 32), Nat.shiftRight_eq_div_pow]
  by_cases h : (32 : UInt32) ≤ totalU
  · have hn : flushThreshold ≤ totalU.toNat := by
      have := UInt32.le_iff_toNat_le.mp h
      simpa [flushThreshold] using this
    rw [if_pos h, if_pos hn, flushAcc_eq, flushBytesWideU_eq, dropBytesU_eq, hshift]
    congr 1
    apply UInt8.toNat_inj.mp
    rw [UInt32.toNat_toUInt8, UInt32.toNat_and]
    have h7 : (7 : UInt32).toNat = 7 := rfl
    have hand : totalU.toNat &&& 7 = totalU.toNat % 8 := by
      simpa using Nat.and_two_pow_sub_one_eq_mod totalU.toNat 3
    rw [h7, hand, Nat.toUInt8_eq, UInt8.toNat_ofNat']
  · have hn : ¬ flushThreshold ≤ totalU.toNat := fun hh =>
      h (UInt32.le_iff_toNat_le.mpr (by simpa [flushThreshold] using hh))
    rw [if_neg h, if_neg hn]
    congr 1

/-- Write `n` bits (n ≤ 25) from `val`, LSB first.
    Fixed-width fields in DEFLATE are packed LSB-first.

    The low `n` bits of `val` are masked, shifted above the `bitCount`
    bits already in `bitBuf`, OR-ed into a 64-bit accumulator, then whole
    bytes are flushed via the scalar `flushBatchedU` (the `n ≤ 25` guard
    keeps the `UInt32` total exact; larger `n` — never produced by DEFLATE
    fields — takes the `Nat` reference path). -/
def writeBits (bw : BitWriter) (n : Nat) (val : UInt32) : BitWriter :=
  let masked : UInt64 := val.toUInt64 % (1 <<< n.toUInt64)
  let acc : UInt64 := bw.bitBuf ||| (masked <<< bw.bitCount.toUInt64)
  if n ≤ 25 then
    -- `flushBatchedU bw.data acc totalU`, hand-inlined so the result cell is a
    -- literal ctor in each branch and reuse recycles `bw` on both paths.
    let totalU : UInt32 := bw.bitCount.toUInt32 + n.toUInt32
    if totalU ≥ 32 then
      ⟨flushBytesWideU bw.data acc (totalU >>> 3), dropBytesU acc (totalU >>> 3),
        (totalU &&& 7).toUInt8⟩
    else
      ⟨bw.data, acc, totalU.toUInt8⟩
  else
    flushBatched bw.data acc (bw.bitCount.toNat + n)

/-- `writeBits` is `flushBatched` of the merged accumulator — the defining
    equation the spec proofs unfold to. -/
theorem writeBits_def (bw : BitWriter) (n : Nat) (val : UInt32) :
    bw.writeBits n val =
      flushBatched bw.data
        (bw.bitBuf ||| ((val.toUInt64 % (1 <<< n.toUInt64)) <<< bw.bitCount.toUInt64))
        (bw.bitCount.toNat + n) := by
  rw [writeBits]
  split
  next h =>
    refine (flushBatchedU_eq bw.data _ (bw.bitCount.toUInt32 + n.toUInt32)).trans ?_
    congr 1
    rw [UInt32.toNat_add, UInt8.toNat_toUInt32, Nat.toUInt32_eq, UInt32.toNat_ofNat']
    have hb := UInt8.toNat_lt bw.bitCount
    omega
  next => rfl

/-- Reverse all 16 bits of `x` (`bit i ↦ bit (15-i)`) with a branchless
    swap network — no per-bit loop. -/
def reverse16 (x : UInt16) : UInt16 :=
  let x := ((x &&& 0x5555) <<< 1) ||| ((x &&& 0xaaaa) >>> 1)
  let x := ((x &&& 0x3333) <<< 2) ||| ((x &&& 0xcccc) >>> 2)
  let x := ((x &&& 0x0f0f) <<< 4) ||| ((x &&& 0xf0f0) >>> 4)
  ((x &&& 0x00ff) <<< 8) ||| ((x &&& 0xff00) >>> 8)

/-- Write a Huffman code of `len` bits. Huffman codes in DEFLATE are
    packed MSB-first (RFC 1951 §3.1.1) but bytes are filled LSB-first, so the
    code's low `len` bits must be reversed before the LSB-first batch pack.

    The reversal is done in one shot: reverse all 16 bits, then shift the
    reversed code down by `16 - len` so its low `len` bits hold the code in
    packing order. (Widening to `UInt64` before the down-shift makes `len = 0`
    yield `0` correctly, since `>>> 16` clears a 16-bit value.)

    The flush bookkeeping runs through the scalar `flushBatchedU` — the
    `UInt32` total is exact for every input (`bitCount, len < 256`). -/
def writeHuffCode (bw : BitWriter) (code : UInt16) (len : UInt8) : BitWriter :=
  let rev : UInt64 := (reverse16 code).toUInt64 >>> (16 - len.toUInt64)
  let acc : UInt64 := bw.bitBuf ||| (rev <<< bw.bitCount.toUInt64)
  -- `flushBatchedU bw.data acc totalU`, hand-inlined so the result cell is a
  -- literal ctor in each branch and reuse recycles `bw` on both paths.
  let totalU : UInt32 := bw.bitCount.toUInt32 + len.toUInt32
  if totalU ≥ 32 then
    ⟨flushBytesWideU bw.data acc (totalU >>> 3), dropBytesU acc (totalU >>> 3),
      (totalU &&& 7).toUInt8⟩
  else
    ⟨bw.data, acc, totalU.toUInt8⟩

/-- `writeHuffCode` is `flushBatched` of the merged accumulator — the defining
    equation the spec proofs unfold to. -/
theorem writeHuffCode_def (bw : BitWriter) (code : UInt16) (len : UInt8) :
    bw.writeHuffCode code len =
      flushBatched bw.data
        (bw.bitBuf |||
          (((reverse16 code).toUInt64 >>> (16 - len.toUInt64)) <<< bw.bitCount.toUInt64))
        (bw.bitCount.toNat + len.toNat) := by
  rw [writeHuffCode]
  refine (flushBatchedU_eq bw.data _ (bw.bitCount.toUInt32 + len.toUInt32)).trans ?_
  congr 1
  rw [UInt32.toNat_add, UInt8.toNat_toUInt32, UInt8.toNat_toUInt32]
  have hb := UInt8.toNat_lt bw.bitCount
  have hl := UInt8.toNat_lt len
  omega

/-- Flush all pending bits, padding the final partial byte with zeros. Drains
    every whole pending byte (`bitCount` may hold up to 31 bits under batching),
    then the final partial byte. Returns the final ByteArray. -/
def flush (bw : BitWriter) : ByteArray :=
  let r := flushAcc bw.data bw.bitBuf bw.bitCount.toNat
  if r.bitCount > 0 then r.data.push r.bitBuf.toUInt8
  else r.data

end BitWriter
end Zip.Native
