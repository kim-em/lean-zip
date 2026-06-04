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

/-- A `BitReader`'s bit-list view is the stream from its cursor. -/
theorem toBits_getElem? {br : BitReader} {i : Nat} (hi : br.bitPos + i < br.data.size * 8) :
    br.toBits[i]? = some (streamBit br.data (br.bitPos + i)) := by
  rw [BitReader.toBits, List.getElem?_drop,
    HuffTree.bytesToBits_getElem? br.data (br.pos * 8 + br.bitOff + i) hi]
  simp only [streamBit, BitReader.bitPos]

/-- **`takeBits` value = `readBits` value.** The wide-buffer low-`n`-bit field
    equals the value the spec reader reads. -/
theorem takeBits_value {data : ByteArray} {br : BitReader} {pos : Nat} {bitBuf : UInt64} {cnt : Nat}
    (h : BufCorr data br.bitPos pos bitBuf cnt) (hwf : br.bitOff < 8) (hdata : br.data = data)
    {n : Nat} (hn : n ≤ cnt) (hn32 : n ≤ 32) (hn64 : n < 64)
    {val : UInt32} {br' : BitReader} (hread : br.readBits n = .ok (val, br')) :
    val.toNat = (takeBits bitBuf cnt n).1 := by
  have hmlt0 : (bitBuf &&& ((1 <<< n.toUInt64) - 1)).toNat < 2 ^ n := mask_lt hn64
  have hmb0 : ∀ i, i < n →
      (bitBuf &&& ((1 <<< n.toUInt64) - 1)).toNat.testBit i = streamBit data (br.bitPos + i) :=
    fun i hi => mask_testBit h hn hn64 hi
  show val.toNat = (bitBuf &&& ((1 <<< n.toUInt64) - 1)).toNat
  generalize hm : (bitBuf &&& ((1 <<< n.toUInt64) - 1)).toNat = m at hmlt0 hmb0 ⊢
  have hbound : br.bitPos + n ≤ data.size * 8 := by
    have := h.span; have := h.posLe; omega
  have hlen : br.toBits.length = br.data.size * 8 - br.bitPos := by
    rw [BitReader.toBits, List.length_drop, Deflate.Spec.bytesToBits_length]; rfl
  -- the first n bits of `br.toBits` are the bits of `m`
  have htake : br.toBits.take n = List.ofFn (fun i : Fin n => m.testBit i.val) := by
    apply List.ext_getElem
    · rw [List.length_take, List.length_ofFn, hlen, hdata]; omega
    · intro i h1 h2
      rw [List.length_take] at h1
      rw [List.getElem_take, List.getElem_ofFn]
      have hi : br.bitPos + i < br.data.size * 8 := by rw [hdata]; omega
      have hgi := toBits_getElem? (br := br) (i := i) hi
      rw [List.getElem?_eq_getElem (by omega)] at hgi
      rw [Option.some_inj.mp hgi, hdata]
      exact (hmb0 i (by omega)).symm
  have hsplit : br.toBits = List.ofFn (fun i : Fin n => m.testBit i.val) ++ br.toBits.drop n := by
    rw [← htake, List.take_append_drop]
  have hlsb : Deflate.Spec.readBitsLSB n br.toBits = some (m, br.toBits.drop n) := by
    have h0 := Deflate.Correctness.readBitsLSB_testBit m n hmlt0 (br.toBits.drop n)
    rw [← hsplit] at h0; exact h0
  obtain ⟨rest, htb, _⟩ := Deflate.Correctness.readBits_toBits br n val br' hwf hn32 hread
  rw [hlsb] at htb
  exact (congrArg Prod.fst (Option.some_inj.mp htb)).symm

/-- `readBits.go` preserves `bitOff < 8`. -/
theorem readBits_go_bitOff_lt (br br' : BitReader) (acc : UInt32) (shift n : Nat) (val : UInt32)
    (hwf : br.bitOff < 8)
    (h : BitReader.readBits.go br acc shift n = .ok (val, br')) : br'.bitOff < 8 := by
  induction n generalizing br acc shift with
  | zero => simp only [BitReader.readBits.go] at h; obtain ⟨_, rfl⟩ := h; exact hwf
  | succ n ih =>
    simp only [BitReader.readBits.go, bind, Except.bind] at h
    cases hrb : br.readBit with
    | error e => simp only [hrb] at h; exact nomatch h
    | ok p =>
      obtain ⟨bit, br₁⟩ := p
      simp only [hrb] at h
      exact ih br₁ _ _ (ZipCommon.readBit_bitOff_lt br br₁ bit hrb) h

/-- `readBits` preserves `bitOff < 8`. -/
theorem readBits_bitOff_lt {br br' : BitReader} {n : Nat} {val : UInt32}
    (h : br.readBits n = .ok (val, br')) (hwf : br.bitOff < 8) : br'.bitOff < 8 := by
  unfold BitReader.readBits at h
  exact readBits_go_bitOff_lt br br' 0 0 n val hwf h

/-- **`takeBits` corresponds to `readBits`.** Same value, and the resulting buffer
    corresponds to the advanced reader (which stays well-formed). -/
theorem takeBits_corr {data : ByteArray} {br : BitReader} {pos : Nat} {bitBuf : UInt64} {cnt : Nat}
    (h : BufCorr data br.bitPos pos bitBuf cnt) (hwf : br.bitOff < 8) (hdata : br.data = data)
    {n : Nat} (hn : n ≤ cnt) (hn32 : n ≤ 32) (hn64 : n < 64)
    {val : UInt32} {br' : BitReader} (hread : br.readBits n = .ok (val, br')) :
    val.toNat = (takeBits bitBuf cnt n).1
    ∧ BufCorr data br'.bitPos pos (takeBits bitBuf cnt n).2.1 (takeBits bitBuf cnt n).2.2
    ∧ br'.data = data ∧ br'.bitOff < 8 := by
  refine ⟨takeBits_value h hwf hdata hn hn32 hn64 hread, ?_, ?_, readBits_bitOff_lt hread hwf⟩
  · have hbp : br'.bitPos = br.bitPos + n := ZipCommon.readBits_bitPos_eq br br' n val hread hwf
    show BufCorr data br'.bitPos pos (bitBuf >>> n.toUInt64) (cnt - n)
    rw [hbp]; exact consume_corr h hn hn64
  · exact (ZipCommon.readBits_data_eq br br' n val hread).trans hdata

/-- The buffer's 9-bit table index, bit by bit: the stream bit while `j < cnt`,
    else 0 (works for any `cnt`, unlike `mask_testBit`). -/
theorem peek9_buf_testBit {data : ByteArray} {bitpos pos : Nat} {bitBuf : UInt64} {cnt : Nat}
    (h : BufCorr data bitpos pos bitBuf cnt) (j : Nat) (hj : j < 9) :
    (bitBuf &&& 0x1FF).toNat.testBit j = if j < cnt then streamBit data (bitpos + j) else false := by
  rw [UInt64.toNat_and, show (0x1FF : UInt64).toNat = 2 ^ 9 - 1 from by decide,
    Nat.and_two_pow_sub_one_eq_mod, Nat.testBit_mod_two_pow]
  simp only [hj, decide_true, Bool.true_and]
  split
  · exact h.bits j ‹_›
  · exact Nat.testBit_lt_two_pow
      (Nat.lt_of_lt_of_le h.high (Nat.pow_le_pow_right (by omega) (by omega)))

open HuffTree in
/-- **`peekFast` past end-of-stream reads 0.** The mirror of `peekFast_testBit`
    for bit positions at or beyond `data.size * 8`: the contributing byte is out
    of range, so the bit is 0. -/
theorem peekFast_testBit_eof (br : BitReader) (j : Nat) (hwf : br.bitOff < 8) (hj : j < 9)
    (hge : br.data.size * 8 ≤ br.pos * 8 + br.bitOff + j) :
    (peekFast br).toNat.testBit j = false := by
  have hmask : (0x1FF : UInt32).toNat.testBit j = true := by
    rw [show (0x1FF : UInt32).toNat = 2 ^ 9 - 1 from by decide, Nat.testBit_two_pow_sub_one]
    simp only [decide_eq_true_eq]; omega
  have hshift : br.bitOff.toUInt32.toNat % 32 = br.bitOff := by
    simp only [Nat.toUInt32, UInt32.ofNat, UInt32.toNat, BitVec.toNat_ofNat, Nat.reducePow]; omega
  have hb0eq : (if br.pos < br.data.size then br.data[br.pos]!.toUInt32 else (0 : UInt32)).toNat
      = (if br.pos < br.data.size then br.data[br.pos]!.toNat else 0) := by
    split
    · rw [UInt8.toNat_toUInt32]
    · rfl
  have hb1eq : (if br.pos + 1 < br.data.size then br.data[br.pos + 1]!.toUInt32 else (0 : UInt32)).toNat
      = (if br.pos + 1 < br.data.size then br.data[br.pos + 1]!.toNat else 0) := by
    split
    · rw [UInt8.toNat_toUInt32]
    · rfl
  have hb1lt : (if br.pos + 1 < br.data.size then br.data[br.pos + 1]!.toNat else 0) < 256 := by
    split
    · have := UInt8.toNat_lt br.data[br.pos + 1]!; omega
    · decide
  have hb0lt : (if br.pos < br.data.size then br.data[br.pos]!.toNat else 0) < 256 := by
    split
    · have := UInt8.toNat_lt br.data[br.pos]!; omega
    · decide
  -- byte-out-of-range facts, derived while the context still has plain `br.bitOff`
  have hbyte : (br.bitOff + j < 8 → br.data.size ≤ br.pos)
      ∧ (8 ≤ br.bitOff + j → br.data.size ≤ br.pos + 1) := by
    constructor <;> intro h8 <;> omega
  unfold peekFast
  rw [UInt32.toNat_and, Nat.testBit_and, UInt32.toNat_shiftRight, Nat.testBit_shiftRight,
    hmask, Bool.and_true, hshift, UInt32.toNat_or, Nat.testBit_or, hb0eq,
    UInt32.toNat_shiftLeft, show (8 : UInt32).toNat % 32 = 8 from by decide, hb1eq,
    Nat.mod_eq_of_lt (by rw [Nat.shiftLeft_eq, show (2 : Nat) ^ 8 = 256 from by decide,
      show (2 : Nat) ^ 32 = 4294967296 from by decide]; omega),
    Nat.testBit_shiftLeft]
  by_cases hlo : br.bitOff + j < 8
  · -- byte `pos` holds the bit, but it is out of range (pos ≥ size); `b1<<8` vanishes
    rw [if_neg (Nat.not_lt.mpr (hbyte.1 hlo)),
      show decide (br.bitOff + j ≥ 8) = false from by
        simp only [decide_eq_false_iff_not]; exact Nat.not_le.mpr hlo]
    simp
  · -- `b0`'s bit is past its 8-bit width (false); byte `pos+1` is out of range
    have h8 : 8 ≤ br.bitOff + j := Nat.not_lt.mp hlo
    have h256 : (256 : Nat) ≤ 2 ^ (br.bitOff + j) := by
      calc (256 : Nat) = 2 ^ 8 := by decide
        _ ≤ 2 ^ (br.bitOff + j) := Nat.pow_le_pow_right (by omega) h8
    rw [show (if br.pos < br.data.size then br.data[br.pos]!.toNat else 0).testBit (br.bitOff + j) = false from
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb0lt h256),
      if_neg (Nat.not_lt.mpr (hbyte.2 h8))]
    simp

open HuffTree in
/-- **9-bit table peek = `peekFast`, including end-of-stream.** Under the
    post-`refill` condition (`56 < cnt`, i.e. ≥ 9 bits, or input exhausted),
    the wide-buffer index equals `peekFast`'s — matching even the zero-padded
    high bits past the end of the stream. -/
theorem peek_eq_refilled {data : ByteArray} {br : BitReader} {pos : Nat} {bitBuf : UInt64} {cnt : Nat}
    (h : BufCorr data br.bitPos pos bitBuf cnt) (hwf : br.bitOff < 8) (hdata : br.data = data)
    (hr : 56 < cnt ∨ pos = data.size) :
    (bitBuf &&& 0x1FF).toNat = (peekFast br).toNat := by
  rcases hr with hc | hpos
  · exact peek_eq h hwf hdata (by omega)
  · have hbp : br.bitPos = br.pos * 8 + br.bitOff := rfl
    have hds : br.data.size = data.size := by rw [hdata]
    have hsp := h.span
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases hj9 : j < 9
    · rw [peek9_buf_testBit h j hj9]
      split
      · rename_i hjc
        have hin : br.pos * 8 + br.bitOff + j < br.data.size * 8 := by omega
        rw [peekFast_testBit br j hwf (by simp only [fastBits]; omega) hin]
        simp only [streamBit, ← hbp, hdata]
      · rename_i hjc
        have hge : br.data.size * 8 ≤ br.pos * 8 + br.bitOff + j := by omega
        rw [peekFast_testBit_eof br j hwf hj9 hge]
    · have h2j : (512 : Nat) ≤ 2 ^ j := by
        calc (512 : Nat) = 2 ^ 9 := by decide
          _ ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) (by omega)
      have hb : (bitBuf &&& 0x1FF).toNat.testBit j = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le
          (by rw [UInt64.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)) h2j)
      rw [hb, Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (peekFast_lt br) h2j)]

/-- The low buffer bit, as a `Bool` test, is the negation of the stream bit. -/
theorem low_bit_eq {data : ByteArray} {bitpos pos : Nat} {bitBuf : UInt64} {cnt : Nat}
    (h : BufCorr data bitpos pos bitBuf cnt) (hcnt : 0 < cnt) :
    (bitBuf &&& 1 == 0) = !streamBit data bitpos := by
  have hbit := h.bits 0 hcnt
  rw [Nat.add_zero, Nat.testBit_zero] at hbit
  have hand : (bitBuf &&& 1).toNat = bitBuf.toNat % 2 := by
    rw [UInt64.toNat_and, show (1 : UInt64).toNat = 1 from rfl, Nat.and_one_is_mod]
  have hlt : bitBuf.toNat % 2 < 2 := Nat.mod_lt _ (by decide)
  rcases hs : streamBit data bitpos with _ | _ <;> rw [hs] at hbit <;> simp only [decide_eq_true_eq,
      decide_eq_false_iff_not] at hbit
  · have hm : bitBuf.toNat % 2 = 0 := by omega
    have h0 : bitBuf &&& 1 = 0 := by
      have : (bitBuf &&& 1).toNat = (0 : UInt64).toNat := by rw [hand, hm]; rfl
      exact UInt64.toNat_inj.mp this
    simp [h0]
  · have h1 : bitBuf &&& 1 = 1 := by
      have : (bitBuf &&& 1).toNat = (1 : UInt64).toNat := by rw [hand, hbit]; rfl
      exact UInt64.toNat_inj.mp this
    simp [h1]

/-- **`walkTree` corresponds to `decode.go`.** Under the buffer invariant and the
    maintainable side condition `pos = data.size ∨ 21 < depth + cnt` (either the
    input is exhausted — so the buffer's `cnt = 0` coincides with reader EOF — or
    there are enough buffered bits to outrun the depth-20 guard), the wide-buffer
    tree walk and the reader's tree walk agree: same symbol/error, and on success
    the resulting buffer corresponds to the advanced reader. -/
theorem walkTree_corr (t : HuffTree) {data : ByteArray} :
    ∀ {br : BitReader} {pos : Nat} {bitBuf : UInt64} {cnt depth : Nat},
    BufCorr data br.bitPos pos bitBuf cnt → br.bitOff < 8 → br.data = data →
    (pos = data.size ∨ 21 < depth + cnt) →
    (∀ s br', HuffTree.decode.go t br depth = .ok (s, br') →
        ∃ bb c used, walkTree t bitBuf cnt depth = .ok (s, bb, c, used)
          ∧ BufCorr data br'.bitPos pos bb c ∧ br'.data = data ∧ br'.bitOff < 8)
    ∧ (∀ e, HuffTree.decode.go t br depth = .error e → walkTree t bitBuf cnt depth = .error e) := by
  induction t with
  | leaf s =>
    intro br pos bitBuf cnt depth h hwf hdata _
    refine ⟨?_, ?_⟩
    · intro s' br' hgo
      simp only [HuffTree.decode.go, Except.ok.injEq, Prod.mk.injEq] at hgo
      obtain ⟨rfl, rfl⟩ := hgo
      exact ⟨bitBuf, cnt, 0, by simp only [walkTree], h, hdata, hwf⟩
    · intro e hgo; simp [HuffTree.decode.go] at hgo
  | empty =>
    intro br pos bitBuf cnt depth _ _ _ _
    refine ⟨?_, ?_⟩
    · intro s' br' hgo; simp [HuffTree.decode.go] at hgo
    · intro e hgo
      simp only [HuffTree.decode.go, Except.error.injEq] at hgo
      simp only [walkTree, ← hgo]
  | node z o ihz iho =>
    intro br pos bitBuf cnt depth h hwf hdata hinv
    by_cases hd : depth > 20
    · refine ⟨fun s' br' hgo => by simp [HuffTree.decode.go, hd] at hgo, ?_⟩
      intro e hgo
      simp only [HuffTree.decode.go, hd, if_true, Except.error.injEq] at hgo
      simp only [walkTree, hd, if_true, ← hgo]
    · by_cases hcnt : 0 < cnt
      · -- read one bit; both follow the same stream bit
        have hbp : br.bitPos < data.size * 8 := by have := h.span; have := h.posLe; omega
        have htb : br.toBits = streamBit data br.bitPos :: br.toBits.tail := by
          have h0 := toBits_getElem? (br := br) (i := 0) (by rw [hdata]; simpa using hbp)
          rw [hdata] at h0
          cases hbl : br.toBits with
          | nil => rw [hbl] at h0; simp at h0
          | cons a l =>
            rw [hbl] at h0
            simp only [List.getElem?_cons_zero, Option.some_inj, Nat.add_zero] at h0
            simp only [List.tail_cons]; rw [h0]
        obtain ⟨br', hrb, _, hwf', _⟩ :=
          Deflate.Correctness.readBit_complete br (streamBit data br.bitPos) br.toBits.tail hwf htb
        have hbpe : br'.bitPos = br.bitPos + 1 :=
          ZipCommon.readBit_bitPos_eq br br' _ hrb hwf
        have hbdata : br'.data = data := (ZipCommon.readBit_data_eq br br' _ hrb).trans hdata
        -- buffer after consuming 1 bit corresponds to br'
        have hcc : BufCorr data br'.bitPos pos (bitBuf >>> 1) (cnt - 1) := by
          rw [hbpe, show (bitBuf >>> 1 : UInt64) = bitBuf >>> (1 : Nat).toUInt64 from by rfl]
          exact consume_corr h hcnt (by decide)
        have hsubinv : pos = data.size ∨ 21 < (depth + 1) + (cnt - 1) := by
          rcases hinv with h' | h'
          · exact Or.inl h'
          · exact Or.inr (by omega)
        -- the chosen subtree is the same on both sides
        have hbranch : (bitBuf &&& 1 == 0) = !streamBit data br.bitPos := low_bit_eq h hcnt
        have hcne : ¬ cnt = 0 := by omega
        rcases hs : streamBit data br.bitPos with _ | _
        · -- stream bit 0: both descend into `z`
          have hgs : HuffTree.decode.go (HuffTree.node z o) br depth
              = HuffTree.decode.go z br' (depth + 1) := by
            rw [HuffTree.decode.go, if_neg hd, hrb]; simp [bind, Except.bind, hs]
          have hsub : (if bitBuf &&& 1 == 0 then z else o) = z := by
            simp [show (bitBuf &&& 1 == 0) = true from by simp [hbranch, hs]]
          refine ⟨fun s' br'' hgo => ?_, fun e hgo => ?_⟩
          · rw [hgs] at hgo
            obtain ⟨bb2, c2, u2, hwt, hbc, hd2, ho2⟩ := (ihz hcc hwf' hbdata hsubinv).1 s' br'' hgo
            refine ⟨bb2, c2, u2 + 1, ?_, hbc, hd2, ho2⟩
            rw [walkTree, if_neg hd, if_neg hcne, hsub]; simp [hwt]
          · rw [hgs] at hgo
            rw [walkTree, if_neg hd, if_neg hcne, hsub]
            simp [(ihz hcc hwf' hbdata hsubinv).2 e hgo]
        · -- stream bit 1: both descend into `o`
          have hgs : HuffTree.decode.go (HuffTree.node z o) br depth
              = HuffTree.decode.go o br' (depth + 1) := by
            rw [HuffTree.decode.go, if_neg hd, hrb]; simp [bind, Except.bind, hs]
          have hsub : (if bitBuf &&& 1 == 0 then z else o) = o := by
            simp [show (bitBuf &&& 1 == 0) = false from by simp [hbranch, hs]]
          refine ⟨fun s' br'' hgo => ?_, fun e hgo => ?_⟩
          · rw [hgs] at hgo
            obtain ⟨bb2, c2, u2, hwt, hbc, hd2, ho2⟩ := (iho hcc hwf' hbdata hsubinv).1 s' br'' hgo
            refine ⟨bb2, c2, u2 + 1, ?_, hbc, hd2, ho2⟩
            rw [walkTree, if_neg hd, if_neg hcne, hsub]; simp [hwt]
          · rw [hgs] at hgo
            rw [walkTree, if_neg hd, if_neg hcne, hsub]
            simp [(iho hcc hwf' hbdata hsubinv).2 e hgo]
      · -- cnt = 0 → end of input (the EOF disjunct of the invariant must hold)
        have hc0 : cnt = 0 := by omega
        have hpos : pos = data.size := by
          rcases hinv with h' | h'
          · exact h'
          · omega
        have hge : br.data.size ≤ br.pos := by
          have hsp := h.span; have hb : br.bitPos = br.pos * 8 + br.bitOff := rfl
          rw [hdata]; omega
        have hrbe : br.readBit = .error "BitReader: unexpected end of input" := by
          simp only [ZipCommon.BitReader.readBit, show br.pos ≥ br.data.size from hge, if_true]
        refine ⟨?_, ?_⟩
        · intro s' br' hgo
          rw [HuffTree.decode.go, if_neg hd, hrbe] at hgo
          simp [bind, Except.bind] at hgo
        · intro e hgo
          rw [HuffTree.decode.go, if_neg hd, hrbe] at hgo
          simp only [bind, Except.bind] at hgo
          have he : "BitReader: unexpected end of input" = e := by injection hgo
          rw [walkTree, if_neg hd, if_pos hc0, he]

open HuffTree in
/-- **`decodeSym` corresponds to `HuffTree.decodeWithTable`.** Same symbol/error,
    and on success the resulting buffer corresponds to the advanced reader. The
    table code length is bounded by `fastBits` (true for `buildTable`). -/
theorem decodeSym_corr (tree : HuffTree) (table : Array (UInt16 × UInt8))
    {data : ByteArray} {br : BitReader} {pos : Nat} {bitBuf : UInt64} {cnt : Nat}
    (h : BufCorr data br.bitPos pos bitBuf cnt) (hwf : br.bitOff < 8) (hdata : br.data = data)
    (hr : 56 < cnt ∨ pos = data.size)
    (hlen : (table[(bitBuf &&& 0x1FF).toNat]!).2.toNat ≤ 9) :
    match HuffTree.decodeWithTable tree table br, decodeSym tree table bitBuf cnt with
    | .error e1, .error e2 => e1 = e2
    | .ok (s1, br'), .ok (s2, bb, c, used) =>
        s1 = s2 ∧ BufCorr data br'.bitPos pos bb c ∧ br'.data = data ∧ br'.bitOff < 8
    | _, _ => False := by
  have hbp : br.bitPos = br.pos * 8 + br.bitOff := rfl
  have hsp := h.span; have hple := h.posLe
  have hds : br.data.size = data.size := by rw [hdata]
  -- `cnt ≤ bitsAvail`, with equality when the input is exhausted
  have hav : cnt ≤ HuffTree.bitsAvail br ∧ (pos = data.size → cnt = HuffTree.bitsAvail br) := by
    unfold HuffTree.bitsAvail
    by_cases hpe : br.pos ≥ br.data.size
    · rw [if_pos hpe]; exact ⟨by omega, fun _ => by omega⟩
    · rw [if_neg hpe]; exact ⟨by omega, fun hh => by subst hh; omega⟩
  have hidx : (bitBuf &&& 0x1FF).toNat = (peekFast br).toNat := peek_eq_refilled h hwf hdata hr
  rw [hidx] at hlen
  unfold HuffTree.decodeWithTable decodeSym
  rw [if_neg (show ¬ br.bitOff ≥ 8 from by omega), hidx]
  simp only []
  generalize hentry : table[(peekFast br).toNat]! = entry at hlen ⊢
  -- the two guards have the same truth value (cnt vs bitsAvail, with len ≤ 9)
  have hgd : (entry.2.toNat == 0 || decide (entry.2.toNat > HuffTree.bitsAvail br))
           = (entry.2.toNat == 0 || decide (entry.2.toNat > cnt)) := by
    rcases hr with hc | hpe
    · have h1 : ¬ entry.2.toNat > HuffTree.bitsAvail br := by have := hav.1; omega
      have h2 : ¬ entry.2.toNat > cnt := by omega
      simp [h1, h2]
    · rw [hav.2 hpe]
  by_cases hg : (entry.2.toNat == 0 || decide (entry.2.toNat > cnt)) = true
  · -- fallback: walkTree ↔ decode
    rw [if_pos (hgd.trans hg), if_pos hg, HuffTree.decode]
    have hwc := walkTree_corr (depth := 0) tree h hwf hdata (by
      rcases hr with hc | hpe
      · exact Or.inr (by omega)
      · exact Or.inl hpe)
    rcases hgo : HuffTree.decode.go tree br 0 with _ | ⟨s1, br'⟩
    · rw [hwc.2 _ hgo]
    · obtain ⟨bb, c, used, hwt, hbc, hbd, hbo⟩ := hwc.1 s1 br' hgo
      rw [hwt]; exact ⟨rfl, hbc, hbd, hbo⟩
  · -- table hit
    rw [if_neg (by rw [hgd]; exact hg), if_neg hg]
    simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, not_or, Nat.not_lt] at hg
    obtain ⟨hne, hle⟩ := hg
    have hcc := consume_corr h hle (show entry.2.toNat < 64 from by omega)
    have hbpe : ({ br with pos := br.pos + (br.bitOff + entry.2.toNat) / 8, bitOff := (br.bitOff + entry.2.toNat) % 8 } : BitReader).bitPos = br.bitPos + entry.2.toNat := by simp only [BitReader.bitPos]; omega
    exact ⟨rfl, hbpe.symm ▸ hcc, hdata, Nat.mod_lt _ (by decide)⟩

/-- Every `buildTable` entry's code length is at most `fastBits = 9`
    (the table walk stops at `fastBits`, or returns the `0` sentinel). -/
theorem buildTable_codeLen_le (tree : HuffTree) (idx : Nat) (hidx : idx < 2 ^ HuffTree.fastBits) :
    (tree.buildTable[idx]!).2.toNat ≤ 9 := by
  have htab : tree.buildTable[idx]! = HuffTree.tableEntry tree idx := by
    simp only [HuffTree.buildTable]
    rw [getElem!_pos _ _ (by rw [Array.size_ofFn]; exact hidx), Array.getElem_ofFn]
  rw [htab, HuffTree.tableEntry]
  rcases hg : HuffTree.tableEntry.go tree idx 0 with ⟨sym, lenB⟩
  show lenB.toNat ≤ 9
  by_cases hp : 0 < lenB.toNat
  · have := HuffTree.tableEntry_go_len_le tree idx 0 sym lenB hg (by simp [HuffTree.fastBits]) hp
    simp only [HuffTree.fastBits] at this; omega
  · omega

/-- The 9-bit buffer index is `< 2^fastBits`. -/
theorem buf_idx_lt (bitBuf : UInt64) : (bitBuf &&& 0x1FF).toNat < 2 ^ HuffTree.fastBits := by
  simp only [HuffTree.fastBits]
  rw [UInt64.toNat_and]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

end Zip.Native.InflateBuf
