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
    `flushBytesWide`/`dropBytes` directly for ctor reuse; equal by
    `writeBits_def`/`writeHuffCode_def`). Byte-identical to `flushAcc` in output
    bits — only the split between `data` and the pending accumulator differs. -/
def flushBatched (data : ByteArray) (acc : UInt64) (total : Nat) : BitWriter :=
  if total ≥ flushThreshold then flushAcc data acc total
  else ⟨data, acc, total.toUInt8⟩

/-- Write `n` bits (n ≤ 25) from `val`, LSB first.
    Fixed-width fields in DEFLATE are packed LSB-first.

    The low `n` bits of `val` are masked, shifted above the `bitCount`
    bits already in `bitBuf`, OR-ed into a 64-bit accumulator, then whole
    bytes are flushed. The result cell is constructed here (not in the
    flush loop) so ctor reuse updates `bw` in place — see `flushAcc`. -/
def writeBits (bw : BitWriter) (n : Nat) (val : UInt32) : BitWriter :=
  let masked : UInt64 := val.toUInt64 % (1 <<< n.toUInt64)
  let acc : UInt64 := bw.bitBuf ||| (masked <<< bw.bitCount.toUInt64)
  let total := bw.bitCount.toNat + n
  if total ≥ flushThreshold then
    ⟨flushBytesWide bw.data acc (total / 8), dropBytes acc (total / 8), (total % 8).toUInt8⟩
  else
    ⟨bw.data, acc, total.toUInt8⟩

/-- `writeBits` is `flushBatched` of the merged accumulator — the defining
    equation the spec proofs unfold to. -/
theorem writeBits_def (bw : BitWriter) (n : Nat) (val : UInt32) :
    bw.writeBits n val =
      flushBatched bw.data
        (bw.bitBuf ||| ((val.toUInt64 % (1 <<< n.toUInt64)) <<< bw.bitCount.toUInt64))
        (bw.bitCount.toNat + n) := by
  rw [writeBits, flushBatched]
  split
  · rw [flushBytesWide_eq, flushAcc_eq]
  · rfl

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
    yield `0` correctly, since `>>> 16` clears a 16-bit value.) -/
def writeHuffCode (bw : BitWriter) (code : UInt16) (len : UInt8) : BitWriter :=
  let rev : UInt64 := (reverse16 code).toUInt64 >>> (16 - len.toUInt64)
  let acc : UInt64 := bw.bitBuf ||| (rev <<< bw.bitCount.toUInt64)
  let total := bw.bitCount.toNat + len.toNat
  if total ≥ flushThreshold then
    ⟨flushBytesWide bw.data acc (total / 8), dropBytes acc (total / 8), (total % 8).toUInt8⟩
  else
    ⟨bw.data, acc, total.toUInt8⟩

/-- `writeHuffCode` is `flushBatched` of the merged accumulator — the defining
    equation the spec proofs unfold to. -/
theorem writeHuffCode_def (bw : BitWriter) (code : UInt16) (len : UInt8) :
    bw.writeHuffCode code len =
      flushBatched bw.data
        (bw.bitBuf |||
          (((reverse16 code).toUInt64 >>> (16 - len.toUInt64)) <<< bw.bitCount.toUInt64))
        (bw.bitCount.toNat + len.toNat) := by
  rw [writeHuffCode, flushBatched]
  split
  · rw [flushBytesWide_eq, flushAcc_eq]
  · rfl

/-- Write two Huffman codes in one merged accumulator operation — a single
    shift/OR field and a single flush check for a pair of literals, the way
    libdeflate writes its flush groups.

    When the first code would not trigger an intermediate flush (`bitCount +
    len1 < flushThreshold`, the common case right after a flush leaves few
    pending bits), both reversed codes are merged into one 64-bit accumulator:
    `code1` shifted above the pending bits, `code2` shifted above that, then the
    combined field is flushed once. The guard's `else` branch (rare: `bitCount +
    len1 ≥ 32`) falls back to the two sequential `writeHuffCode` calls.

    `writeHuffCode2_eq` proves the result **byte-identical to the two sequential
    `writeHuffCode` calls for every input** — no length precondition, because
    the merge and the sequential second write use the same (modular) `UInt64`
    shift/OR arithmetic: under the guard the first field never flushes, so
    merging the second above it lands the exact same bits with the exact same
    single flush the sequential pair would perform on its second call.

    That the merged field does not lose bits off the top of the 64-bit
    accumulator (i.e. that the output is well-formed DEFLATE, not merely equal to
    the sequential writer) is a **caller invariant**: DEFLATE literal/length
    Huffman codes have `len ≤ 15`, so with the guard `bitCount + len1 < 32` the
    top bit position `bitCount + len1 + len2 < 47` sits well inside 64. This is
    the same `len ≤ 15` invariant the emit specs already carry
    (`ValidLengths … 15`); it is not needed for `writeHuffCode2_eq`. -/
def writeHuffCode2 (bw : BitWriter) (code1 : UInt16) (len1 : UInt8)
    (code2 : UInt16) (len2 : UInt8) : BitWriter :=
  if bw.bitCount.toNat + len1.toNat < flushThreshold then
    let rev1 : UInt64 := (reverse16 code1).toUInt64 >>> (16 - len1.toUInt64)
    let rev2 : UInt64 := (reverse16 code2).toUInt64 >>> (16 - len2.toUInt64)
    let acc : UInt64 :=
      bw.bitBuf ||| (rev1 <<< bw.bitCount.toUInt64)
        ||| (rev2 <<< (bw.bitCount.toUInt64 + len1.toUInt64))
    let total := bw.bitCount.toNat + len1.toNat + len2.toNat
    if total ≥ flushThreshold then
      ⟨flushBytesWide bw.data acc (total / 8), dropBytes acc (total / 8), (total % 8).toUInt8⟩
    else
      ⟨bw.data, acc, total.toUInt8⟩
  else
    (bw.writeHuffCode code1 len1).writeHuffCode code2 len2

/-- The explicit ctor-reuse flush form (`flushBytesWide`/`dropBytes`) the
    production writers construct equals the `flushBatched` reference form —
    exactly the bridge inside `writeBits_def`/`writeHuffCode_def`, factored out
    so `writeHuffCode2_eq` can rewrite the batched fast path. -/
private theorem flushExplicit_eq_flushBatched (data : ByteArray) (acc : UInt64) (total : Nat) :
    (if total ≥ flushThreshold then
      (⟨flushBytesWide data acc (total / 8), dropBytes acc (total / 8),
        (total % 8).toUInt8⟩ : BitWriter)
     else ⟨data, acc, total.toUInt8⟩) = flushBatched data acc total := by
  unfold flushBatched
  split
  · rw [flushBytesWide_eq, flushAcc_eq]
  · rfl

/-- `writeHuffCode2` is byte-identical to the two sequential `writeHuffCode`
    calls it batches, as a `BitWriter` value (not merely at the `toBits` level).
    Under the guard the first field does not flush, so its merged accumulator is
    exactly the pending state the second `writeHuffCode` reads; OR is
    associative, so shifting `code2` above `code1` lands the same bits, and the
    single flush check on `bitCount + len1 + len2` is the one the sequential
    pair performs on its second call. -/
theorem writeHuffCode2_eq (bw : BitWriter) (code1 : UInt16) (len1 : UInt8)
    (code2 : UInt16) (len2 : UInt8) :
    bw.writeHuffCode2 code1 len1 code2 len2 =
      (bw.writeHuffCode code1 len1).writeHuffCode code2 len2 := by
  unfold writeHuffCode2
  split
  · rename_i hg
    have hg' : bw.bitCount.toNat + len1.toNat < 256 := by
      simp only [flushThreshold] at hg; omega
    -- The first field does not flush: it yields this explicit cell.
    have hX : bw.writeHuffCode code1 len1 =
        ⟨bw.data, bw.bitBuf ||| ((reverse16 code1).toUInt64 >>> (16 - len1.toUInt64))
          <<< bw.bitCount.toUInt64, (bw.bitCount.toNat + len1.toNat).toUInt8⟩ := by
      rw [writeHuffCode_def, flushBatched, if_neg (Nat.not_le.mpr hg)]
    -- The pending count after the first field, as Nat and as the shift amount.
    have htt1 : ((bw.bitCount.toNat + len1.toNat).toUInt8).toNat
        = bw.bitCount.toNat + len1.toNat := by
      simp only [Nat.toUInt8, UInt8.toNat_ofNat']
      rw [show (2 : Nat) ^ 8 = 256 from rfl]; omega
    have hshift : ((bw.bitCount.toNat + len1.toNat).toUInt8).toUInt64
        = bw.bitCount.toUInt64 + len1.toUInt64 := by
      apply UInt64.toNat_inj.mp
      rw [UInt8.toNat_toUInt64, htt1, UInt64.toNat_add, UInt8.toNat_toUInt64,
        UInt8.toNat_toUInt64, Nat.mod_eq_of_lt (by omega)]
    -- Both sides collapse to the same `flushBatched`.
    rw [flushExplicit_eq_flushBatched, writeHuffCode_def, hX, htt1, hshift, Nat.add_assoc]
  · rfl

/-- Flush all pending bits, padding the final partial byte with zeros. Drains
    every whole pending byte (`bitCount` may hold up to 31 bits under batching),
    then the final partial byte. Returns the final ByteArray. -/
def flush (bw : BitWriter) : ByteArray :=
  let r := flushAcc bw.data bw.bitBuf bw.bitCount.toNat
  if r.bitCount > 0 then r.data.push r.bitBuf.toUInt8
  else r.data

end BitWriter
end Zip.Native
