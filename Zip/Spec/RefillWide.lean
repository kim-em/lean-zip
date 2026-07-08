import Std.Tactic.BVDecide
import Zip.Native.Inflate
import Zip.Native.Wide

/-!
# Wide bit-refill: one `ugetUInt64LE` load replaces the per-byte refill loop

`InflateBuf.refill` tops up the bit buffer one byte at a time. When at least
eight bytes remain (`pos + 8 ≤ data.size`) and the buffer holds `cnt ≤ 56` bits,
the loop loads exactly `k = (56 - cnt)/8 + 1` whole bytes (bringing the count to
`cnt + 8k ∈ (56, 64]`). This file proves that those `k` byte-loads equal a single
little-endian eight-byte load (`ByteArray.ugetUInt64LE`) whose top `8 - k` bytes
are cleared (via a `<<< s >>> s` shift pair, `s = 64 - 8k`) and shifted into place
at bit `cnt`.

The masked wide step is **state-equal** to the byte loop: `refill_eq_wide` shows
`refill` itself produces exactly that `(pos, bitBuf, cnt)`. It is the single fact
the wide-refill production loops (`goTreeFreeUWide`, `goFusedPUWide`) are proven
equal through — their equivalence proofs reuse the existing `*_absorb_refill`
machinery untouched.
-/

namespace Zip.Native.InflateBuf

/-- The OR of the `j` bytes `data[pos], data[pos+1], …, data[pos+j-1]` shifted to
    bit positions `cnt, cnt+8, …` — the accumulator the byte-refill loop builds
    across `j` iterations starting from an empty buffer. -/
def chainOR (data : ByteArray) (pos cnt : Nat) : Nat → UInt64
  | 0 => 0
  | j + 1 => (data[pos]!.toUInt64 <<< cnt.toUInt64) ||| chainOR data (pos + 1) (cnt + 8) j

/-- **`refill` runs exactly `k` byte-loads.** When each of the first `k` steps
    fires (`cnt + 8i ≤ 56`, `pos + i` in range) and the `k`-th brings the count
    past 56, `refill` advances the cursor by `k`, ORs the `k` bytes into the
    buffer (`chainOR`), and raises the count by `8k`. -/
theorem refill_chain (data : ByteArray) :
    ∀ (k pos : Nat) (bb : UInt64) (cnt : Nat),
    (∀ i, i < k → cnt + 8 * i ≤ 56 ∧ pos + i < data.size) →
    56 < cnt + 8 * k →
    refill data pos bb cnt = (pos + k, bb ||| chainOR data pos cnt k, cnt + 8 * k) := by
  intro k
  induction k with
  | zero =>
    intro pos bb cnt _ hgt
    have hc : ¬ (cnt ≤ 56 ∧ pos < data.size) := by
      rintro ⟨h, _⟩; omega
    rw [refill, dif_neg hc]
    simp [chainOR]
  | succ k ih =>
    intro pos bb cnt hfire hgt
    obtain ⟨hcnt, hpos⟩ := hfire 0 (by omega)
    simp only [Nat.mul_zero, Nat.add_zero] at hcnt hpos
    rw [refill, dif_pos ⟨hcnt, hpos⟩, ← getElem!_pos data pos hpos]
    rw [ih (pos + 1) (bb ||| (data[pos]!.toUInt64 <<< cnt.toUInt64)) (cnt + 8)
        (by
          intro i hi
          obtain ⟨h1, h2⟩ := hfire (i + 1) (by omega)
          constructor <;> omega)
        (by omega)]
    have hpk : pos + 1 + k = pos + (k + 1) := by omega
    have hck : cnt + 8 + 8 * k = cnt + 8 * (k + 1) := by omega
    have hor : (bb ||| (data[pos]!.toUInt64 <<< cnt.toUInt64)) ||| chainOR data (pos + 1) (cnt + 8) k
        = bb ||| chainOR data pos cnt (k + 1) := by
      rw [chainOR, UInt64.or_assoc]
    rw [hpk, hck, hor]

/-- `Nat.toUInt64` is additive (both sides reduce mod `2^64`). -/
private theorem natAdd_toUInt64 (a b : Nat) : (a + b).toUInt64 = a.toUInt64 + b.toUInt64 := by
  apply UInt64.toNat_inj.mp
  simp only [Nat.toUInt64, UInt64.toNat_add, UInt64.toNat_ofNat']
  omega

private theorem tu0  : Nat.toUInt64 0  = 0  := rfl
private theorem tu8  : Nat.toUInt64 8  = 8  := rfl
private theorem tu16 : Nat.toUInt64 16 = 16 := rfl
private theorem tu24 : Nat.toUInt64 24 = 24 := rfl
private theorem tu32 : Nat.toUInt64 32 = 32 := rfl
private theorem tu40 : Nat.toUInt64 40 = 40 := rfl
private theorem tu48 : Nat.toUInt64 48 = 48 := rfl
private theorem tu56 : Nat.toUInt64 56 = 56 := rfl

set_option maxHeartbeats 2000000 in
/-- **The `k`-byte OR chain is the masked wide load.** The bytes the byte loop ORs
    in at `cnt, cnt+8, …` are exactly the low `k` bytes of the eight-byte
    little-endian word at `pos`, cleared above bit `8k` (by `<<< s >>> s`,
    `s = 64 - 8k`) and shifted to bit `cnt`. `cnt + 8k ≤ 64` keeps every shift
    below 64 (no wraparound). Proved per `k ∈ {1,…,8}` by `bv_decide`. -/
theorem chainOR_eq_recomb (data : ByteArray) (pos cnt k : Nat)
    (hk1 : 1 ≤ k) (hk8 : k ≤ 8) (hck : cnt + 8 * k ≤ 64) :
    chainOR data pos cnt k
      = (((data[pos]!.toUInt64 ||| data[pos+1]!.toUInt64 <<< 8 ||| data[pos+2]!.toUInt64 <<< 16
          ||| data[pos+3]!.toUInt64 <<< 24 ||| data[pos+4]!.toUInt64 <<< 32
          ||| data[pos+5]!.toUInt64 <<< 40 ||| data[pos+6]!.toUInt64 <<< 48
          ||| data[pos+7]!.toUInt64 <<< 56)
          <<< (64 - 8 * k : Nat).toUInt64) >>> (64 - 8 * k : Nat).toUInt64) <<< cnt.toUInt64 := by
  have hcU : cnt.toUInt64 ≤ (64 - 8 * k : Nat).toUInt64 := by
    apply UInt64.le_iff_toNat_le.mpr
    simp only [Nat.toUInt64, UInt64.toNat_ofNat']
    omega
  have hcases : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 := by omega
  rcases hcases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp only [chainOR, Nat.add_assoc, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub,
               natAdd_toUInt64, tu0, tu8, tu16, tu24, tu32, tu40, tu48, tu56,
               UInt64.or_zero] at hcU ⊢ <;>
    bv_decide

/-- **`ugetUInt64LE` is the eight-byte little-endian recombination.** Its trusted
    reference body, with the `USize` offset's `toNat` round-trip discharged and
    the bounds-checked `getElem` reads normalised to `getElem!`. -/
theorem ugetUInt64LE_recomb (data : ByteArray) (pos : Nat)
    (hpos : pos + 8 ≤ data.size) (hp : pos < USize.size) :
    data.ugetUInt64LE pos.toUSize (by rw [toUSize_toNat_of_lt hp]; omega)
      = data[pos]!.toUInt64 ||| data[pos+1]!.toUInt64 <<< 8 ||| data[pos+2]!.toUInt64 <<< 16
        ||| data[pos+3]!.toUInt64 <<< 24 ||| data[pos+4]!.toUInt64 <<< 32
        ||| data[pos+5]!.toUInt64 <<< 40 ||| data[pos+6]!.toUInt64 <<< 48
        ||| data[pos+7]!.toUInt64 <<< 56 := by
  rw [ByteArray.ugetUInt64LE]
  simp only [toUSize_toNat_of_lt hp]
  rw [getElem!_pos data pos (by omega), getElem!_pos data (pos+1) (by omega),
      getElem!_pos data (pos+2) (by omega), getElem!_pos data (pos+3) (by omega),
      getElem!_pos data (pos+4) (by omega), getElem!_pos data (pos+5) (by omega),
      getElem!_pos data (pos+6) (by omega), getElem!_pos data (pos+7) (by omega)]

/-- **The byte-refill loop equals one masked wide load.** From `cnt ≤ 56` with at
    least eight bytes remaining, `refill` advances to the same `(pos, bitBuf, cnt)`
    a single `ugetUInt64LE` load produces: the low `k = (56-cnt)/8 + 1` bytes of the
    word, cleared above bit `8k` and shifted to bit `cnt`, ORed into the buffer.
    The wide-refill loops are proven equal to their byte-refill twins through this
    one equation. -/
theorem refill_eq_wide (data : ByteArray) (pos : Nat) (bb : UInt64) (cnt : Nat)
    (hcnt : cnt ≤ 56) (hpos : pos + 8 ≤ data.size) (hp : pos < USize.size) :
    refill data pos bb cnt
      = (pos + ((56 - cnt) / 8 + 1),
         bb ||| (((data.ugetUInt64LE pos.toUSize (by rw [toUSize_toNat_of_lt hp]; omega))
                    <<< (64 - 8 * ((56 - cnt) / 8 + 1) : Nat).toUInt64
                    >>> (64 - 8 * ((56 - cnt) / 8 + 1) : Nat).toUInt64)
                  <<< cnt.toUInt64),
         cnt + 8 * ((56 - cnt) / 8 + 1)) := by
  have hk1 : 1 ≤ (56 - cnt) / 8 + 1 := by omega
  have hk8 : (56 - cnt) / 8 + 1 ≤ 8 := by omega
  have hck : cnt + 8 * ((56 - cnt) / 8 + 1) ≤ 64 := by omega
  have hgt : 56 < cnt + 8 * ((56 - cnt) / 8 + 1) := by omega
  rw [refill_chain data ((56 - cnt) / 8 + 1) pos bb cnt (fun i hi => ⟨by omega, by omega⟩) hgt,
      chainOR_eq_recomb data pos cnt ((56 - cnt) / 8 + 1) hk1 hk8 hck,
      ugetUInt64LE_recomb data pos hpos hp]

end Zip.Native.InflateBuf
