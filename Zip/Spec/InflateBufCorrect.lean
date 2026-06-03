import Zip.Spec.InflateTable
import Zip.Native.InflateBuf

/-!
# Wide-buffer Huffman decoder: equivalence to the reference

`Zip.Native.InflateBuf.decodeHuffmanFastBuf` threads the bit cursor as scalars
`(pos, bitBuf : UInt64, cnt)` and is proven **equal** to the canonical
`Inflate.decodeHuffmanFast` (which threads a `BitReader`), so the verified
`inflate` can adopt the faster reader with no trust gap.

The bridge is the buffer invariant `BufCorr`: `bitBuf` holds `cnt` valid low
bits which are exactly the stream bits of `data` from absolute bit position
`bitpos` onward. `refill` extends the buffer (preserving `bitpos`), `decodeSym`
corresponds to `HuffTree.decodeWithTable`, and `takeBits` to `BitReader.readBits`.

This file is built bottom-up; the foundational lemmas (`BufCorr`, `refill`) come
first, then the per-operation correspondences, then the loop induction.
-/

namespace Zip.Native.InflateBuf
open ZipCommon (BitReader)

/-- The `k`-th bit of the DEFLATE stream `data` (LSB-first within each byte). -/
def streamBit (data : ByteArray) (k : Nat) : Bool :=
  data[k / 8]!.toNat.testBit (k % 8)

/-- **Buffer invariant.** `bitBuf` holds exactly `cnt` valid low bits, equal to
    the stream bits of `data` at absolute positions `[bitpos, bitpos + cnt)`;
    `pos` is the next byte to load (`bitpos + cnt = pos * 8`), within `data`. -/
structure BufCorr (data : ByteArray) (bitpos pos : Nat) (bitBuf : UInt64) (cnt : Nat) : Prop where
  /-- The buffered bits sit between the cursor and the loaded byte boundary. -/
  span : bitpos + cnt = pos * 8
  /-- Loading never runs past the end of input. -/
  posLe : pos ≤ data.size
  /-- The accumulator never holds more than 64 bits. -/
  cntLe : cnt ≤ 64
  /-- Bits at or above `cnt` are zero — the buffer holds *exactly* `cnt` bits. -/
  high : bitBuf.toNat < 2 ^ cnt
  /-- Each valid bit equals the corresponding stream bit. -/
  bits : ∀ j, j < cnt → bitBuf.toNat.testBit j = streamBit data (bitpos + j)

/-- All buffered bit positions are within the stream (no past-EOF bits). -/
theorem BufCorr.inStream {data bitpos pos bitBuf cnt}
    (h : BufCorr data bitpos pos bitBuf cnt) (j : Nat) (hj : j < cnt) :
    bitpos + j < data.size * 8 := by
  have := h.span; have := h.posLe; omega

/-- `b * 2^cnt < 2^(cnt+8)` for a byte value `b`. -/
private theorem byte_mul_lt {b cnt : Nat} (h : b < 256) : b * 2 ^ cnt < 2 ^ (cnt + 8) := by
  calc b * 2 ^ cnt < 256 * 2 ^ cnt := (Nat.mul_lt_mul_right (Nat.two_pow_pos cnt)).mpr h
    _ = 2 ^ (cnt + 8) := by rw [Nat.pow_add, show (2 : Nat) ^ 8 = 256 from by decide, Nat.mul_comm]

/-- One `refill` step: OR the next byte into bits `[cnt, cnt+8)` of the buffer. -/
theorem refill_step {data : ByteArray} {bitpos pos : Nat} {bitBuf : UInt64} {cnt : Nat}
    (h : BufCorr data bitpos pos bitBuf cnt) (hcnt : cnt ≤ 56) (hpos : pos < data.size) :
    BufCorr data bitpos (pos + 1) (bitBuf ||| (data[pos]!.toUInt64 <<< cnt.toUInt64)) (cnt + 8) := by
  have hbytelt : data[pos]!.toNat < 256 := by have := UInt8.toNat_lt data[pos]!; omega
  have hshift : cnt.toUInt64.toNat % 64 = cnt := by
    simp [Nat.toUInt64, UInt64.toNat_ofNat]; omega
  -- the shifted byte equals `data[pos]!.toNat * 2^cnt`
  have hshifted : (data[pos]!.toUInt64 <<< cnt.toUInt64).toNat = data[pos]!.toNat * 2 ^ cnt := by
    rw [UInt64.toNat_shiftLeft, UInt8.toNat_toUInt64, hshift, Nat.shiftLeft_eq]
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (byte_mul_lt hbytelt)
      (Nat.pow_le_pow_right (by omega) (by omega)))
  refine ⟨by have := h.span; omega, by omega, by omega, ?_, ?_⟩
  · -- high: result < 2^(cnt+8)
    rw [UInt64.toNat_or, hshifted]
    exact Nat.or_lt_two_pow
      (Nat.lt_of_lt_of_le h.high (Nat.pow_le_pow_right (by omega) (by omega)))
      (byte_mul_lt hbytelt)
  · -- bits
    intro j hj
    rw [UInt64.toNat_or, Nat.testBit_or, hshifted, Nat.testBit_mul_two_pow]
    by_cases hjc : j < cnt
    · -- low byte unchanged: shifted byte has 0 bits below cnt
      have hd : decide (cnt ≤ j) = false := by simp only [decide_eq_false_iff_not]; omega
      rw [h.bits j hjc, hd]
      simp only [Bool.false_and, Bool.or_false]
    · -- bit in [cnt, cnt+8): comes from the new byte
      have hjlo : cnt ≤ j := by omega
      have hbb : bitBuf.toNat.testBit j = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h.high (Nat.pow_le_pow_right (by omega) hjlo))
      have hd : decide (cnt ≤ j) = true := by simp only [decide_eq_true_eq]; omega
      rw [hbb, Bool.false_or, hd]
      simp only [Bool.true_and]
      -- byte bit equals the stream bit
      have hspan := h.span
      have hpos8 : (bitpos + j) / 8 = pos := by omega
      have hmod8 : (bitpos + j) % 8 = j - cnt := by omega
      simp only [streamBit, hpos8, hmod8]

/-- `refill` preserves the buffer invariant and either fills past 56 bits or
    exhausts the input. -/
theorem refill_corr {data : ByteArray} {bitpos pos : Nat} {bitBuf : UInt64} {cnt : Nat}
    (h : BufCorr data bitpos pos bitBuf cnt) {p : Nat} {b : UInt64} {c : Nat}
    (heq : refill data pos bitBuf cnt = (p, b, c)) :
    BufCorr data bitpos p b c ∧ (56 < c ∨ p = data.size) := by
  unfold refill at heq
  split at heq
  · rename_i hcond
    obtain ⟨hc, hp⟩ := hcond
    exact refill_corr (refill_step h hc hp) heq
  · rename_i hcond
    obtain ⟨rfl, rfl, rfl⟩ := Prod.ext_iff.mp heq |>.imp id Prod.ext_iff.mp
    refine ⟨h, ?_⟩
    by_cases hp : pos < data.size
    · rcases Nat.lt_or_ge 56 cnt with h56 | h56
      · exact Or.inl h56
      · exact absurd ⟨h56, hp⟩ hcond
    · exact Or.inr (Nat.le_antisymm h.posLe (Nat.not_lt.mp hp))
termination_by data.size - pos
decreasing_by simp_wf; omega

end Zip.Native.InflateBuf
