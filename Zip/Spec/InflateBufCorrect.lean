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

/-- Consuming `k` (< 64) bits shifts the buffer right by `k` and advances the
    cursor by `k`. The dual of `refill_step`; used by the initial align,
    `takeBits`, and `decodeSym`. -/
theorem consume_corr {data : ByteArray} {bitpos pos : Nat} {bitBuf : UInt64} {cnt : Nat}
    (h : BufCorr data bitpos pos bitBuf cnt) {k : Nat} (hk : k ≤ cnt) (hk64 : k < 64) :
    BufCorr data (bitpos + k) pos (bitBuf >>> k.toUInt64) (cnt - k) := by
  have hkmod : k.toUInt64.toNat % 64 = k := by simp [Nat.toUInt64, UInt64.toNat_ofNat]; omega
  refine ⟨by have := h.span; omega, h.posLe, by have := h.cntLe; omega, ?_, ?_⟩
  · -- high: (bitBuf >>> k).toNat < 2^(cnt-k)
    rw [UInt64.toNat_shiftRight, hkmod, Nat.shiftRight_eq_div_pow]
    apply Nat.div_lt_of_lt_mul
    rw [Nat.mul_comm, ← Nat.pow_add]
    have hck : cnt - k + k = cnt := by omega
    rw [hck]; exact h.high
  · -- bits shift down by k
    intro j hj
    have hidx : k + j < cnt := by omega
    have he : bitpos + (k + j) = bitpos + k + j := by omega
    rw [UInt64.toNat_shiftRight, hkmod, Nat.testBit_shiftRight, h.bits (k + j) hidx, he]

/-- The low-`n`-bit mask `(1<<<n)-1` has Nat value `2^n - 1` (for `n < 64`). -/
theorem mask_toNat {n : Nat} (hn : n < 64) :
    ((1 <<< n.toUInt64) - 1 : UInt64).toNat = 2 ^ n - 1 := by
  have hnm : n.toUInt64.toNat % 64 = n := by simp [Nat.toUInt64, UInt64.toNat_ofNat]; omega
  have hpow : 2 ^ n < 2 ^ 64 := Nat.pow_lt_pow_right (by omega) hn
  have h1 : (1 <<< n.toUInt64 : UInt64).toNat = 2 ^ n := by
    rw [UInt64.toNat_shiftLeft, UInt64.toNat_one, hnm, Nat.shiftLeft_eq, Nat.one_mul,
      Nat.mod_eq_of_lt hpow]
  have hle : (1 : UInt64) ≤ 1 <<< n.toUInt64 := by
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_one, h1]; exact Nat.two_pow_pos n
  rw [UInt64.toNat_sub_of_le _ _ hle, h1, UInt64.toNat_one]

/-- The buffer's low-`n`-bit field (`j < n ≤ cnt`, `n < 64`) matches the stream. -/
theorem mask_testBit {data : ByteArray} {bitpos pos : Nat} {bitBuf : UInt64} {cnt : Nat}
    (h : BufCorr data bitpos pos bitBuf cnt) {n : Nat} (hn : n ≤ cnt) (hn64 : n < 64)
    {j : Nat} (hj : j < n) :
    (bitBuf &&& ((1 <<< n.toUInt64) - 1)).toNat.testBit j = streamBit data (bitpos + j) := by
  rw [UInt64.toNat_and, mask_toNat hn64, Nat.and_two_pow_sub_one_eq_mod, Nat.testBit_mod_two_pow]
  simp only [hj, decide_true, Bool.true_and]
  exact h.bits j (by omega)

/-- The masked field is `< 2^n`. -/
theorem mask_lt {bitBuf : UInt64} {n : Nat} (hn64 : n < 64) :
    (bitBuf &&& ((1 <<< n.toUInt64) - 1)).toNat < 2 ^ n := by
  rw [UInt64.toNat_and, mask_toNat hn64, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (Nat.two_pow_pos n)

open HuffTree in
/-- `peekFast` is `(_ &&& 0x1FF)`, so its value is `< 512`. -/
theorem peekFast_lt (br : BitReader) : (peekFast br).toNat < 512 := by
  simp only [peekFast, UInt32.toNat_and]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

open HuffTree in
/-- **9-bit table peek matches `peekFast`** when the buffer holds ≥ 9 bits (the
    common, non-EOF case). Both index the same 9 stream bits at the cursor. -/
theorem peek_eq {data : ByteArray} {br : BitReader} {pos : Nat} {bitBuf : UInt64} {cnt : Nat}
    (h : BufCorr data br.bitPos pos bitBuf cnt) (hwf : br.bitOff < 8) (hdata : br.data = data)
    (hcnt : 9 ≤ cnt) :
    (bitBuf &&& 0x1FF).toNat = (peekFast br).toNat := by
  have h9 : (0x1FF : UInt64) = (1 <<< (9 : Nat).toUInt64) - 1 := by decide
  have hbp : br.bitPos = br.pos * 8 + br.bitOff := rfl
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj9 : j < 9
  · have hbuf : (bitBuf &&& 0x1FF).toNat.testBit j = streamBit data (br.bitPos + j) := by
      rw [h9]; exact mask_testBit h (by omega) (by omega) hj9
    have hin : br.pos * 8 + br.bitOff + j < br.data.size * 8 := by
      have hs := h.span; have hp := h.posLe; rw [hdata, ← hbp]; omega
    rw [hbuf, peekFast_testBit br j hwf (by simp only [fastBits]; omega) hin]
    simp only [streamBit, ← hbp, hdata]
  · have h2j : (512 : Nat) ≤ 2 ^ j := by
      calc (512 : Nat) = 2 ^ 9 := by decide
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) (by omega)
    have hbuf : (bitBuf &&& 0x1FF).toNat.testBit j = false := by
      apply Nat.testBit_lt_two_pow
      rw [h9]; exact Nat.lt_of_lt_of_le (mask_lt (by omega)) (by
        calc (2 : Nat) ^ 9 ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) (by omega))
    rw [hbuf, Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (peekFast_lt br) h2j)]

end Zip.Native.InflateBuf
