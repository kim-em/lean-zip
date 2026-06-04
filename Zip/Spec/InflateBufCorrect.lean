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
    val.toNat = (bitBuf &&& ((1 <<< n.toUInt64) - 1)).toNat := by
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

/-- A single `readBit` succeeds while in bounds, advancing the bit position by 1. -/
theorem readBit_ok_of_inbounds (br : BitReader) (hwf : br.bitOff < 8) (hin : br.pos < br.data.size) :
    ∃ bit br', br.readBit = .ok (bit, br') ∧ br'.bitPos = br.bitPos + 1
      ∧ br'.bitOff < 8 ∧ br'.data = br.data := by
  have hb : br.bitPos = br.pos * 8 + br.bitOff := rfl
  unfold BitReader.readBit
  rw [if_neg (by omega)]
  by_cases ho : br.bitOff + 1 ≥ 8
  · rw [if_pos ho]
    refine ⟨_, _, rfl, ?_, by show (0 : Nat) < 8; decide, rfl⟩
    show (br.pos + 1) * 8 + 0 = br.bitPos + 1
    omega
  · rw [if_neg ho]
    refine ⟨_, _, rfl, ?_, by show br.bitOff + 1 < 8; omega, rfl⟩
    show br.pos * 8 + (br.bitOff + 1) = br.bitPos + 1
    omega

/-- `readBits.go` succeeds when the reader has at least `k` bits left. -/
theorem readBits_go_avail : ∀ (k : Nat) (br : BitReader) (acc : UInt32) (shift : Nat), br.bitOff < 8 →
    br.bitPos + k ≤ br.data.size * 8 → ∃ val br', BitReader.readBits.go br acc shift k = .ok (val, br') := by
  intro k
  induction k with
  | zero => intro br acc shift _ _; exact ⟨acc, br, rfl⟩
  | succ k ih =>
    intro br acc shift hwf hb
    have hin : br.pos < br.data.size := by
      have : br.bitPos = br.pos * 8 + br.bitOff := rfl; omega
    obtain ⟨bit, br1, hrb1, hbp1, hwf1, hdata1⟩ := readBit_ok_of_inbounds br hwf hin
    simp only [BitReader.readBits.go, bind, Except.bind, hrb1]
    exact ih br1 _ _ hwf1 (by rw [hbp1, hdata1]; omega)

/-- `readBits.go` errors (with the standard message) when fewer than `k` bits remain. -/
theorem readBits_go_error : ∀ (k : Nat) (br : BitReader) (acc : UInt32) (shift : Nat), br.bitOff < 8 →
    br.bitPos ≤ br.data.size * 8 → br.data.size * 8 < br.bitPos + k →
    BitReader.readBits.go br acc shift k = .error "BitReader: unexpected end of input" := by
  intro k
  induction k with
  | zero => intro br acc shift _ hle hlt; omega
  | succ k ih =>
    intro br acc shift hwf hle hlt
    simp only [BitReader.readBits.go, bind, Except.bind]
    by_cases hpos : br.pos ≥ br.data.size
    · rw [show br.readBit = .error "BitReader: unexpected end of input" from by
        unfold BitReader.readBit; rw [if_pos hpos]]
    · obtain ⟨bit, br1, hrb1, hbp1, hwf1, hdata1⟩ := readBit_ok_of_inbounds br hwf (by omega)
      rw [hrb1]; simp only []
      exact ih br1 _ _ hwf1 (by rw [hbp1, hdata1]; have : br.bitPos = br.pos*8+br.bitOff := rfl; omega)
        (by rw [hbp1, hdata1]; omega)

/-- **`takeBits` corresponds to `readBits`, totally.** On a successful read the value
    and advanced state match; an end-of-input error transfers — given either enough
    buffered bits or true EOF (so the buffer's `cnt` equals the reader's available bits).
    Stated as two implications (like `walkTree_corr`) so it composes with `cases` on the
    read result without a match-motive rewrite. -/
theorem takeBits_corr {data : ByteArray} {br : BitReader} {pos : Nat} {bitBuf : UInt64} {cnt : Nat}
    (h : BufCorr data br.bitPos pos bitBuf cnt) (hwf : br.bitOff < 8) (hdata : br.data = data)
    {n : Nat} (hr : n ≤ cnt ∨ pos = data.size) (hn32 : n ≤ 32) (hn64 : n < 64) :
    (∀ val br', br.readBits n = .ok (val, br') →
        ∃ v bb c', takeBits bitBuf cnt n = .ok (v, bb, c') ∧ val.toNat = v
          ∧ BufCorr data br'.bitPos pos bb c' ∧ br'.data = data ∧ br'.bitOff < 8 ∧ c' = cnt - n)
    ∧ (∀ e, br.readBits n = .error e → takeBits bitBuf cnt n = .error e) := by
  have hsp := h.span; have hple := h.posLe
  have hbp : br.bitPos = br.pos * 8 + br.bitOff := rfl
  have hds : br.data.size = data.size := by rw [hdata]
  have hle : br.bitPos ≤ data.size * 8 := by omega
  by_cases hnc : n > cnt
  · -- EOF (else `hr` gives n ≤ cnt): both sides hit end of input
    have hpos : pos = data.size := hr.resolve_left (by omega)
    subst hpos
    have herr : br.readBits n = .error "BitReader: unexpected end of input" := by
      rw [BitReader.readBits]
      exact readBits_go_error n br 0 0 hwf (by rw [hds]; omega) (by rw [hds]; omega)
    have htk : takeBits bitBuf cnt n = .error "BitReader: unexpected end of input" := by
      unfold takeBits; rw [if_pos hnc]
    refine ⟨fun val br' h' => by rw [herr] at h'; exact absurd h' (by simp), fun e h' => ?_⟩
    rw [herr] at h'
    have he : "BitReader: unexpected end of input" = e := by injection h'
    rw [htk, he]
  · -- enough bits: both succeed
    have hn : n ≤ cnt := by omega
    have htk : takeBits bitBuf cnt n
        = .ok ((bitBuf &&& ((1 <<< n.toUInt64) - 1)).toNat, bitBuf >>> n.toUInt64, cnt - n) := by
      unfold takeBits; rw [if_neg hnc]
    refine ⟨fun val br' h' => ?_, fun e h' => ?_⟩
    · refine ⟨_, _, _, htk, takeBits_value h hwf hdata hn hn32 hn64 h', ?_, ?_,
        readBits_bitOff_lt h' hwf, rfl⟩
      · have hbpe : br'.bitPos = br.bitPos + n := ZipCommon.readBits_bitPos_eq br br' n val h' hwf
        rw [hbpe]; exact consume_corr h hn hn64
      · exact (ZipCommon.readBits_data_eq br br' n val h').trans hdata
    · obtain ⟨val, br', hok⟩ := readBits_go_avail n br 0 0 hwf (by rw [hds]; omega)
      rw [show br.readBits n = BitReader.readBits.go br 0 0 n from rfl, hok] at h'
      exact absurd h' (by simp)

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
    (hr : 8 < cnt ∨ pos = data.size) :
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

/-- All of `t`'s leaves lie at depth ≤ `d`, so a bit-walk reaches a leaf (or the
    `empty` sentinel) within `d` steps. Trees from `fromLengths` with valid
    DEFLATE code lengths (≤ 15) satisfy `treeDepthLE t 15`. -/
def treeDepthLE : HuffTree → Nat → Prop
  | .leaf _, _ => True
  | .empty, _ => True
  | .node _ _, 0 => False
  | .node z o, d + 1 => treeDepthLE z d ∧ treeDepthLE o d

/-- A successful `walkTree` consumes exactly `used` of the buffer's `cnt` bits. -/
theorem walkTree_consumed (t : HuffTree) :
    ∀ {bitBuf : UInt64} {cnt depth : Nat} {s bb c used},
    walkTree t bitBuf cnt depth = .ok (s, bb, c, used) → c + used = cnt := by
  induction t with
  | leaf s' =>
    intro bitBuf cnt depth s bb c used h
    simp only [walkTree, Except.ok.injEq, Prod.mk.injEq] at h; omega
  | empty => intro bitBuf cnt depth s bb c used h; simp only [walkTree] at h; exact absurd h (by simp)
  | node z o ihz iho =>
    intro bitBuf cnt depth s bb c used h
    rw [walkTree] at h
    by_cases hd : depth > 20
    · rw [if_pos hd] at h; exact absurd h (by simp)
    · rw [if_neg hd] at h
      by_cases hc0 : cnt = 0
      · rw [if_pos hc0] at h; exact absurd h (by simp)
      · rw [if_neg hc0] at h
        cases hrec : walkTree (if bitBuf &&& 1 == 0 then z else o) (bitBuf >>> 1) (cnt - 1) (depth + 1) with
        | error e => rw [hrec] at h; exact absurd h (by simp)
        | ok p =>
          obtain ⟨s', b', c', u'⟩ := p
          rw [hrec] at h
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨_, _, hc, hused⟩ := h
          subst hc; subst hused
          have hrc : c' + u' = cnt - 1 := by
            by_cases hbit : (bitBuf &&& 1 == 0) = true
            · rw [if_pos hbit] at hrec; exact ihz hrec
            · rw [if_neg hbit] at hrec; exact iho hrec
          omega

/-- A successful `walkTree` on a depth-≤`D` tree consumes at most `D` bits. -/
theorem walkTree_used_le (t : HuffTree) :
    ∀ {bitBuf : UInt64} {cnt depth D : Nat} {s bb c used},
    walkTree t bitBuf cnt depth = .ok (s, bb, c, used) → treeDepthLE t D → used ≤ D := by
  induction t with
  | leaf s' =>
    intro bitBuf cnt depth D s bb c used h _
    simp only [walkTree, Except.ok.injEq, Prod.mk.injEq] at h; omega
  | empty => intro bitBuf cnt depth D s bb c used h _; simp only [walkTree] at h; exact absurd h (by simp)
  | node z o ihz iho =>
    intro bitBuf cnt depth D s bb c used h hD
    rw [walkTree] at h
    by_cases hd : depth > 20
    · rw [if_pos hd] at h; exact absurd h (by simp)
    · rw [if_neg hd] at h
      by_cases hc0 : cnt = 0
      · rw [if_pos hc0] at h; exact absurd h (by simp)
      · rw [if_neg hc0] at h
        cases hrec : walkTree (if bitBuf &&& 1 == 0 then z else o) (bitBuf >>> 1) (cnt - 1) (depth + 1) with
        | error e => rw [hrec] at h; exact absurd h (by simp)
        | ok p =>
          obtain ⟨s', b', c', u'⟩ := p
          rw [hrec] at h
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨_, _, _, hused⟩ := h
          subst hused
          -- depth-≤D node: D = D'+1 with both subtrees depth ≤ D'
          match D, hD with
          | D' + 1, ⟨hz, ho⟩ =>
            have hu' : u' ≤ D' := by
              by_cases hbit : (bitBuf &&& 1 == 0) = true
              · rw [if_pos hbit] at hrec; exact ihz hrec hz
              · rw [if_neg hbit] at hrec; exact iho hrec ho
            omega

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
          ∧ BufCorr data br'.bitPos pos bb c ∧ br'.data = data ∧ br'.bitOff < 8 ∧ c ≤ cnt)
    ∧ (∀ e, HuffTree.decode.go t br depth = .error e → walkTree t bitBuf cnt depth = .error e) := by
  induction t with
  | leaf s =>
    intro br pos bitBuf cnt depth h hwf hdata _
    refine ⟨?_, ?_⟩
    · intro s' br' hgo
      simp only [HuffTree.decode.go, Except.ok.injEq, Prod.mk.injEq] at hgo
      obtain ⟨rfl, rfl⟩ := hgo
      exact ⟨bitBuf, cnt, 0, by simp only [walkTree], h, hdata, hwf, Nat.le_refl cnt⟩
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
            obtain ⟨bb2, c2, u2, hwt, hbc, hd2, ho2, hle2⟩ := (ihz hcc hwf' hbdata hsubinv).1 s' br'' hgo
            refine ⟨bb2, c2, u2 + 1, ?_, hbc, hd2, ho2, by omega⟩
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
            obtain ⟨bb2, c2, u2, hwt, hbc, hd2, ho2, hle2⟩ := (iho hcc hwf' hbdata hsubinv).1 s' br'' hgo
            refine ⟨bb2, c2, u2 + 1, ?_, hbc, hd2, ho2, by omega⟩
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
    (hr : 21 < cnt ∨ pos = data.size)
    (hlen : (table[(bitBuf &&& 0x1FF).toNat]!).2.toNat ≤ 9) (hdep : treeDepthLE tree 15) :
    match HuffTree.decodeWithTable tree table br, decodeSym tree table bitBuf cnt with
    | .error e1, .error e2 => e1 = e2
    | .ok (s1, br'), .ok (s2, bb, c, used) =>
        s1 = s2 ∧ BufCorr data br'.bitPos pos bb c ∧ br'.data = data ∧ br'.bitOff < 8
          ∧ c ≤ cnt ∧ cnt - c ≤ 15
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
  have hidx : (bitBuf &&& 0x1FF).toNat = (peekFast br).toNat :=
    peek_eq_refilled h hwf hdata (hr.imp (fun hc => by omega) id)
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
    · obtain ⟨bb, c, used, hwt, hbc, hbd, hbo, hle⟩ := hwc.1 s1 br' hgo
      have hcons := walkTree_consumed tree hwt
      have huse := walkTree_used_le tree hwt hdep
      rw [hwt]; exact ⟨rfl, hbc, hbd, hbo, hle, by omega⟩
  · -- table hit
    rw [if_neg (by rw [hgd]; exact hg), if_neg hg]
    simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, not_or, Nat.not_lt] at hg
    obtain ⟨hne, hle⟩ := hg
    have hcc := consume_corr h hle (show entry.2.toNat < 64 from by omega)
    have hbpe : ({ br with pos := br.pos + (br.bitOff + entry.2.toNat) / 8, bitOff := (br.bitOff + entry.2.toNat) % 8 } : BitReader).bitPos = br.bitPos + entry.2.toNat := by simp only [BitReader.bitPos]; omega
    exact ⟨rfl, hbpe.symm ▸ hcc, hdata, Nat.mod_lt _ (by decide), Nat.sub_le cnt _, by omega⟩

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

/-- `decodeSym_corr` specialized to a `buildTable` (discharges `hlen`). -/
theorem decodeSym_corr' (tree : HuffTree)
    {data : ByteArray} {br : BitReader} {pos : Nat} {bitBuf : UInt64} {cnt : Nat}
    (h : BufCorr data br.bitPos pos bitBuf cnt) (hwf : br.bitOff < 8) (hdata : br.data = data)
    (hr : 21 < cnt ∨ pos = data.size) (hdep : treeDepthLE tree 15) :
    match HuffTree.decodeWithTable tree tree.buildTable br, decodeSym tree tree.buildTable bitBuf cnt with
    | .error e1, .error e2 => e1 = e2
    | .ok (s1, br'), .ok (s2, bb, c, used) =>
        s1 = s2 ∧ BufCorr data br'.bitPos pos bb c ∧ br'.data = data ∧ br'.bitOff < 8
          ∧ c ≤ cnt ∧ cnt - c ≤ 15
    | _, _ => False :=
  decodeSym_corr tree tree.buildTable h hwf hdata hr (buildTable_codeLen_le tree _ (buf_idx_lt bitBuf)) hdep

set_option maxRecDepth 4000 in
open HuffTree in
/-- **The block loop corresponds.** The wide-buffer Huffman symbol loop `go`
    equals `Inflate.decodeHuffmanFast.go`: same output/error, and on success the
    final buffer corresponds to the final reader. `go` refills internally, so the
    only precondition is the buffer invariant. -/
theorem go_corr (litTree distTree : HuffTree) (maxOut dataSize : Nat) {data : ByteArray}
    (hldep : treeDepthLE litTree 15) (hddep : treeDepthLE distTree 15) :
    ∀ (br : BitReader) (output : ByteArray) (pos : Nat) (bitBuf : UInt64) (cnt : Nat),
    BufCorr data br.bitPos pos bitBuf cnt → br.bitOff < 8 → br.data = data →
    match Inflate.decodeHuffmanFast.go litTree distTree maxOut litTree.buildTable distTree.buildTable
            dataSize br output,
          go litTree.buildTable distTree.buildTable data litTree distTree maxOut dataSize pos bitBuf cnt
            br.bitPos output with
    | .error e1, .error e2 => e1 = e2
    | .ok (out1, br'), .ok (out2, _pos', bitBuf', cnt', bitpos') =>
        out1 = out2 ∧ BufCorr data br'.bitPos _pos' bitBuf' cnt' ∧ br'.data = data ∧ br'.bitOff < 8
          ∧ bitpos' = br'.bitPos
    | _, _ => False := by
  intro br output
  induction br, output using Inflate.decodeHuffmanFast.go.induct
      (maxOutputSize := maxOut) (dataSize := dataSize) with
  | _ br output ih_lit ih_ld =>
    intro pos bitBuf cnt hbc hwf hdata
    -- refill (`InflateBuf.go` refills internally; relate it to the buffer invariant)
    rcases hrf : refill data pos bitBuf cnt with ⟨pos1, bitBuf1, cnt1⟩
    obtain ⟨hbc1, hr1⟩ := refill_corr hbc hrf
    -- decodeSym ↔ decodeWithTable (literal symbol)
    have hsy := decodeSym_corr' litTree hbc1 hwf hdata (hr1.imp (fun h => by omega) id) hldep
    -- Split on the symbol decode BEFORE unfolding the loop bodies: while `go` is
    -- still an opaque application the goal contains no `decodeWithTable`/`decodeSym`
    -- subterm, so the `cases` does no `kabstract` over the giant inlined body. We
    -- unfold and reduce with targeted `rw` inside each branch instead.
    cases hdwt : litTree.decodeWithTable litTree.buildTable br with
    | error e1 =>
      cases hds2 : decodeSym litTree litTree.buildTable bitBuf1 cnt1 with
      | error e2 =>
        rw [hdwt, hds2] at hsy
        rw [Inflate.decodeHuffmanFast.go, InflateBuf.go, hrf]
        dsimp only []
        rw [hdwt, hds2]
        dsimp only [bind, Except.bind]
        exact hsy
      | ok p2 => rw [hdwt, hds2] at hsy; simp at hsy
    | ok p1 =>
      obtain ⟨sym, br₁⟩ := p1
      cases hds2 : decodeSym litTree litTree.buildTable bitBuf1 cnt1 with
      | error e2 => rw [hdwt, hds2] at hsy; simp at hsy
      | ok p2 =>
        obtain ⟨symB, bb, c, used⟩ := p2
        rw [hdwt, hds2] at hsy
        obtain ⟨hsym, hbc2, hbd2, hbo2, hcle, hcons⟩ := hsy
        -- Unify A's `sym` with B's `sym` here, while the goal is still opaque (so
        -- `subst` is cheap and there are no proof-carrying `arr[sym]'h` to break).
        -- Each leaf unfolds the bodies only after all its inner `cases` are done.
        subst hsym
        have hkey : br.bitPos + (cnt1 - c) = br₁.bitPos := by
          have := hbc1.span; have := hbc2.span; omega
        by_cases hlt : sym < 256
        · -- literal
          rw [Inflate.decodeHuffmanFast.go, InflateBuf.go, hrf]
          dsimp only []; rw [hdwt, hds2]; dsimp only [bind, Except.bind]
          rw [if_pos hlt, if_pos hlt, hkey]
          by_cases hmax : output.size ≥ maxOut
          · rw [if_pos hmax, if_pos hmax]
          · rw [if_neg hmax, if_neg hmax]
            by_cases hp1 : br₁.bitPos ≤ br.bitPos
            · rw [dif_pos hp1, dif_pos hp1]
            · rw [dif_neg hp1, dif_neg hp1]
              by_cases hp2 : dataSize * 8 < br₁.bitPos
              · rw [dif_pos hp2, dif_pos hp2]
              · rw [dif_neg hp2, dif_neg hp2]
                exact ih_lit sym br₁ hp1 hp2 pos1 bb c hbc2 hbo2 hbd2
        · by_cases hs256 : (sym == 256) = true
          · -- end of block: both return the current state
            rw [Inflate.decodeHuffmanFast.go, InflateBuf.go, hrf]
            dsimp only []; rw [hdwt, hds2]; dsimp only [bind, Except.bind]
            rw [if_neg hlt, if_neg hlt, if_pos hs256, if_pos hs256, hkey]
            exact ⟨rfl, hbc2, hbd2, hbo2, rfl⟩
          · by_cases hidx : sym.toNat - 257 ≥ Inflate.lengthBase.size
            · -- invalid length code: both throw the same message
              rw [Inflate.decodeHuffmanFast.go, InflateBuf.go, hrf]
              dsimp only []; rw [hdwt, hds2]; dsimp only [bind, Except.bind]
              rw [if_neg hlt, if_neg hlt, if_neg hs256, if_neg hs256, dif_pos hidx, dif_pos hidx]
            · -- valid length/distance back-reference
              have hN1 : sym.toNat - 257 < Inflate.lengthExtra.size := by
                rw [Inflate.lengthExtra_size]; simp only [Inflate.lengthBase_size] at hidx; omega
              have hext5 : (Inflate.lengthExtra[sym.toNat - 257]'hN1).toNat ≤ 5 := by
                have hb : ∀ i : Fin 29, (Inflate.lengthExtra[i.val]!).toNat ≤ 5 := by decide
                have hh := hb ⟨sym.toNat - 257, by rw [← Inflate.lengthExtra_size]; exact hN1⟩
                rwa [getElem!_pos] at hh
              have hbud_e : (Inflate.lengthExtra[sym.toNat - 257]'hN1).toNat ≤ c ∨ pos1 = data.size := by
                rcases hr1 with h56 | hp
                · exact Or.inl (by omega)
                · exact Or.inr hp
              have htc_e := takeBits_corr hbc2 hbo2 hbd2 hbud_e (by omega) (by omega)
              cases hXe : br₁.readBits (Inflate.lengthExtra[sym.toNat - 257]'hN1).toNat with
              | error e1 =>
                have hYe := htc_e.2 e1 hXe
                rw [Inflate.decodeHuffmanFast.go, InflateBuf.go, hrf]
                dsimp only []; rw [hdwt, hds2]; dsimp only [bind, Except.bind]
                rw [if_neg hlt, if_neg hlt, if_neg hs256, if_neg hs256, dif_neg hidx, dif_neg hidx,
                  readBitsFast_eq br₁, hXe, hYe]
              | ok pe =>
                obtain ⟨extraBits, br₂⟩ := pe
                obtain ⟨eb, bb2, c2, hYe, hval_e, hbc3, hbd3, hbo3, hc2eq⟩ := htc_e.1 extraBits br₂ hXe
                subst hval_e
                -- distance symbol decode (enough bits left after lit+lenExtra, or EOF)
                have hbud_d : 21 < c2 ∨ pos1 = data.size := by
                  rcases hr1 with h56 | hp
                  · exact Or.inl (by omega)
                  · exact Or.inr hp
                have htd := decodeSym_corr' distTree hbc3 hbo3 hbd3 hbud_d hddep
                cases hXd : distTree.decodeWithTable distTree.buildTable br₂ with
                | error e1 =>
                  cases hYd : decodeSym distTree distTree.buildTable bb2 c2 with
                  | error e2 =>
                    rw [hXd, hYd] at htd
                    rw [Inflate.decodeHuffmanFast.go, InflateBuf.go, hrf]
                    dsimp only []; rw [hdwt, hds2]; dsimp only [bind, Except.bind]
                    rw [if_neg hlt, if_neg hlt, if_neg hs256, if_neg hs256, dif_neg hidx, dif_neg hidx,
                      readBitsFast_eq br₁, hXe, hYe]
                    dsimp only [bind, Except.bind]
                    rw [hXd, hYd]
                    exact htd
                  | ok q => rw [hXd, hYd] at htd; exact absurd htd (by simp)
                | ok pd =>
                  obtain ⟨distSym, br₃⟩ := pd
                  cases hYd : decodeSym distTree distTree.buildTable bb2 c2 with
                  | error e2 => rw [hXd, hYd] at htd; exact absurd htd (by simp)
                  | ok q =>
                    obtain ⟨dsymB, bb3, c3, dused⟩ := q
                    rw [hXd, hYd] at htd
                    obtain ⟨hdsym, hbc4, hbd4, hbo4, hc3le, hc3cons⟩ := htd
                    subst hdsym
                    by_cases hdidx : distSym.toNat ≥ Inflate.distBase.size
                    · -- invalid distance code: both throw the same message
                      rw [Inflate.decodeHuffmanFast.go, InflateBuf.go, hrf]
                      dsimp only []; rw [hdwt, hds2]; dsimp only [bind, Except.bind]
                      rw [if_neg hlt, if_neg hlt, if_neg hs256, if_neg hs256, dif_neg hidx, dif_neg hidx,
                        readBitsFast_eq br₁, hXe, hYe]
                      dsimp only [bind, Except.bind]; rw [hXd, hYd]; dsimp only [bind, Except.bind]
                      rw [dif_pos hdidx, dif_pos hdidx]
                    · -- valid distance: read distance-extra bits
                      have hdN3 : distSym.toNat < Inflate.distExtra.size := by
                        rw [Inflate.distExtra_size]; simp only [Inflate.distBase_size] at hdidx; omega
                      have hde13 : (Inflate.distExtra[distSym.toNat]'hdN3).toNat ≤ 13 := by
                        have hb : ∀ i : Fin 30, (Inflate.distExtra[i.val]!).toNat ≤ 13 := by decide
                        have hh := hb ⟨distSym.toNat, by rw [← Inflate.distExtra_size]; exact hdN3⟩
                        rwa [getElem!_pos] at hh
                      have hbud_de : (Inflate.distExtra[distSym.toNat]'hdN3).toNat ≤ c3 ∨ pos1 = data.size := by
                        rcases hr1 with h56 | hp
                        · exact Or.inl (by omega)
                        · exact Or.inr hp
                      have htc_de := takeBits_corr hbc4 hbo4 hbd4 hbud_de (by omega) (by omega)
                      cases hXde : br₃.readBits (Inflate.distExtra[distSym.toNat]'hdN3).toNat with
                      | error e1 =>
                        have hYde := htc_de.2 e1 hXde
                        rw [Inflate.decodeHuffmanFast.go, InflateBuf.go, hrf]
                        dsimp only []; rw [hdwt, hds2]; dsimp only [bind, Except.bind]
                        rw [if_neg hlt, if_neg hlt, if_neg hs256, if_neg hs256, dif_neg hidx, dif_neg hidx,
                          readBitsFast_eq br₁, hXe, hYe]
                        dsimp only [bind, Except.bind]; rw [hXd, hYd]; dsimp only [bind, Except.bind]
                        rw [dif_neg hdidx, dif_neg hdidx, readBitsFast_eq br₃, hXde, hYde]
                      | ok pde =>
                        obtain ⟨dExtraBits, br₄⟩ := pde
                        obtain ⟨deb, bb4, c4, hYde, hval_de, hbc5, hbd5, hbo5, hc4eq⟩ :=
                          htc_de.1 dExtraBits br₄ hXde
                        subst hval_de
                        -- final reader position after the whole back-reference
                        have hkey4 : br.bitPos + (cnt1 - c4) = br₄.bitPos := by
                          have := hbc1.span; have := hbc5.span; omega
                        rw [Inflate.decodeHuffmanFast.go, InflateBuf.go, hrf]
                        dsimp only []; rw [hdwt, hds2]; dsimp only [bind, Except.bind]
                        rw [if_neg hlt, if_neg hlt, if_neg hs256, if_neg hs256, dif_neg hidx, dif_neg hidx,
                          readBitsFast_eq br₁, hXe, hYe]
                        dsimp only [bind, Except.bind]; rw [hXd, hYd]; dsimp only [bind, Except.bind]
                        rw [dif_neg hdidx, dif_neg hdidx, readBitsFast_eq br₃, hXde, hYde]
                        dsimp only [bind, Except.bind]
                        -- distance/length now share the same expression on both sides
                        by_cases hd0 : (Inflate.distBase[distSym.toNat]'(Nat.not_le.mp hdidx)).toNat + dExtraBits.toNat = 0
                        · rw [dif_pos hd0, dif_pos hd0]
                        · rw [dif_neg hd0, dif_neg hd0]
                          by_cases hds : (Inflate.distBase[distSym.toNat]'(Nat.not_le.mp hdidx)).toNat + dExtraBits.toNat > output.size
                          · rw [dif_pos hds, dif_pos hds]
                          · rw [dif_neg hds, dif_neg hds]
                            by_cases hmax2 : output.size + ((Inflate.lengthBase[sym.toNat - 257]'(Nat.not_le.mp hidx)).toNat + extraBits.toNat) > maxOut
                            · rw [if_pos hmax2, if_pos hmax2]
                            · rw [if_neg hmax2, if_neg hmax2]
                              -- progress guards: A uses br₄.bitPos, B uses the tracked bitpos (= it by hkey4)
                              by_cases hp1 : br₄.bitPos ≤ br.bitPos
                              · rw [dif_pos hp1,
                                  dif_pos (show br.bitPos + (cnt1 - c4) ≤ br.bitPos from by rw [hkey4]; exact hp1)]
                              · rw [dif_neg hp1,
                                  dif_neg (show ¬ br.bitPos + (cnt1 - c4) ≤ br.bitPos from by rw [hkey4]; exact hp1)]
                                by_cases hp2 : dataSize * 8 < br₄.bitPos
                                · rw [dif_pos hp2,
                                    dif_pos (show dataSize * 8 < br.bitPos + (cnt1 - c4) from by rw [hkey4]; exact hp2)]
                                · rw [dif_neg hp2,
                                    dif_neg (show ¬ dataSize * 8 < br.bitPos + (cnt1 - c4) from by rw [hkey4]; exact hp2)]
                                  simp only [hkey4]
                                  exact ih_ld sym hidx extraBits distSym hdidx dExtraBits br₄
                                    hd0 hds hp1 hp2 pos1 bb4 c4 hbc5 hbo5 hbd5


/-! ## Tree-depth bound from `fromLengths` -/

/-- `insert.go` keeps every leaf within depth `D` when the code length `n ≤ D`. -/
theorem insert_go_depthLE (code : UInt32) (symbol : UInt16) :
    ∀ (n D : Nat) (t : HuffTree), treeDepthLE t D → n ≤ D →
      treeDepthLE (HuffTree.insert.go code symbol t n) D := by
  intro n
  induction n with
  | zero => intro D t _ _; exact True.intro
  | succ n ih =>
    intro D t hT hn
    obtain ⟨D', rfl⟩ : ∃ D', D = D' + 1 := ⟨D - 1, by omega⟩
    cases t with
    | leaf s => exact True.intro
    | empty =>
      change treeDepthLE (if ((code >>> n.toUInt32) &&& 1) == 0
        then .node (HuffTree.insert.go code symbol .empty n) .empty
        else .node .empty (HuffTree.insert.go code symbol .empty n)) (D' + 1)
      by_cases hbit : ((code >>> n.toUInt32) &&& 1) == 0
      · rw [if_pos hbit]; exact ⟨ih D' .empty True.intro (by omega), True.intro⟩
      · rw [if_neg hbit]; exact ⟨True.intro, ih D' .empty True.intro (by omega)⟩
    | node z o =>
      obtain ⟨hz, ho⟩ := hT
      change treeDepthLE (if ((code >>> n.toUInt32) &&& 1) == 0
        then .node (HuffTree.insert.go code symbol z n) o
        else .node z (HuffTree.insert.go code symbol o n)) (D' + 1)
      by_cases hbit : ((code >>> n.toUInt32) &&& 1) == 0
      · rw [if_pos hbit]; exact ⟨ih D' z hz (by omega), ho⟩
      · rw [if_neg hbit]; exact ⟨hz, ih D' o ho (by omega)⟩

/-- `insert` keeps every leaf within depth `D` (code length `len ≤ D`). -/
theorem insert_depthLE {t : HuffTree} {D : Nat} (code : UInt32) (len : Nat) (symbol : UInt16)
    (hT : treeDepthLE t D) (hlen : len ≤ D) : treeDepthLE (t.insert code len symbol) D :=
  insert_go_depthLE code symbol len D t hT hlen

/-- `insertLoop` preserves the depth bound when every code length is `≤ maxBits`. -/
theorem insertLoop_depthLE (lengths : Array UInt8) (maxBits : Nat)
    (hlen : ∀ i (h : i < lengths.size), (lengths[i]'h).toNat ≤ maxBits) :
    ∀ (nextCode : Array UInt32) (start : Nat) (tree : HuffTree), treeDepthLE tree maxBits →
      treeDepthLE (HuffTree.insertLoop lengths nextCode start tree).1 maxBits := by
  intro nextCode start tree
  induction nextCode, start, tree using HuffTree.insertLoop.induct (lengths := lengths) with
  | case1 nextCode start tree h len hpos hsz c tree' nextCode' ih =>
    intro hT
    rw [HuffTree.insertLoop, dif_pos h, if_pos hpos, dif_pos hsz]
    exact ih (insert_depthLE _ _ _ hT (hlen start h))
  | case2 nextCode start tree h len hpos hsz ih =>
    intro hT
    rw [HuffTree.insertLoop, dif_pos h, if_pos hpos, dif_neg hsz]
    exact ih hT
  | case3 nextCode start tree h len hpos ih =>
    intro hT
    rw [HuffTree.insertLoop, dif_pos h, if_neg hpos]
    exact ih hT
  | case4 nextCode start tree h =>
    intro hT
    rw [HuffTree.insertLoop, dif_neg h]
    exact hT

/-- The canonical tree built from `≤ maxBits` code lengths has depth `≤ maxBits`. -/
theorem fromLengthsTree_depthLE (lengths : Array UInt8) (maxBits : Nat)
    (hlen : ∀ i (h : i < lengths.size), (lengths[i]'h).toNat ≤ maxBits) :
    treeDepthLE (HuffTree.fromLengthsTree lengths maxBits) maxBits := by
  unfold HuffTree.fromLengthsTree
  exact insertLoop_depthLE lengths maxBits hlen _ 0 .empty True.intro

/-- A validated `fromLengths` tree has depth `≤ maxBits`. -/
theorem fromLengths_depthLE {lengths : Array UInt8} {maxBits : Nat} {tree : HuffTree}
    (h : HuffTree.fromLengths lengths maxBits = .ok tree) : treeDepthLE tree maxBits := by
  unfold HuffTree.fromLengths at h
  simp only [] at h
  split at h
  · exact absurd h (by simp)
  · rename_i hany
    split at h
    · exact absurd h (by simp)
    · simp only [Except.ok.injEq] at h
      subst h
      refine fromLengthsTree_depthLE lengths maxBits (fun i hi => ?_)
      have hf : lengths.any (fun l => decide (l.toNat > maxBits)) = false := by simpa using hany
      have hi2 := (Array.any_eq_false.mp hf) i hi
      simp only [decide_eq_true_eq, gt_iff_lt, Nat.not_lt] at hi2
      exact hi2

/-! ## The wide-buffer decoder equals the reference -/

open Inflate in
/-- **`decodeHuffmanFastBuf` = `decodeHuffmanFast`** for depth-≤15 trees and a
    well-formed reader (`bitOff < 8`, not past end of input). -/
theorem decodeHuffmanFastBuf_eq (br : BitReader) (output : ByteArray)
    (litTree distTree : HuffTree) (maxOut : Nat)
    (hldep : treeDepthLE litTree 15) (hddep : treeDepthLE distTree 15)
    (hwf : br.bitOff < 8) (hbp : br.bitPos ≤ br.data.size * 8) :
    InflateBuf.decodeHuffmanFastBuf br output litTree distTree maxOut
      = Inflate.decodeHuffmanFast br output litTree distTree maxOut := by
  have hbpe : br.bitPos = br.pos * 8 + br.bitOff := rfl
  have hposle : br.pos ≤ br.data.size := by omega
  have hbc0 : BufCorr br.data (br.pos * 8) br.pos 0 0 :=
    ⟨by omega, hposle, by omega, by simp, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  rcases hrf : refill br.data br.pos 0 0 with ⟨pos0, bitBuf0, cnt0⟩
  obtain ⟨hbc1, hr1⟩ := refill_corr hbc0 hrf
  have hboff : br.bitOff ≤ cnt0 := by
    rcases hr1 with h56 | hpe
    · omega
    · have hs := hbc1.span; rw [hpe] at hs; omega
  have hbc2 : BufCorr br.data br.bitPos pos0 (bitBuf0 >>> br.bitOff.toUInt64) (cnt0 - br.bitOff) :=
    consume_corr hbc1 hboff (by omega)
  have hco := go_corr litTree distTree maxOut br.data.size hldep hddep br output pos0
    (bitBuf0 >>> br.bitOff.toUInt64) (cnt0 - br.bitOff) hbc2 hwf rfl
  unfold InflateBuf.decodeHuffmanFastBuf Inflate.decodeHuffmanFast
  rw [hrf]
  dsimp only []
  simp only [BitReader.bitPos] at hco
  cases hgoB : InflateBuf.go litTree.buildTable distTree.buildTable br.data litTree distTree maxOut
      br.data.size pos0 (bitBuf0 >>> br.bitOff.toUInt64) (cnt0 - br.bitOff) (br.pos * 8 + br.bitOff) output with
  | error eB =>
    cases hgoA : Inflate.decodeHuffmanFast.go litTree distTree maxOut litTree.buildTable
        distTree.buildTable br.data.size br output with
    | error eA =>
      rw [hgoA, hgoB] at hco; simp only [bind, Except.bind]; exact congrArg Except.error hco.symm
    | ok pA => rw [hgoA, hgoB] at hco; exact absurd hco (by simp)
  | ok pB =>
    obtain ⟨out2, pos', bitBuf', cnt', bitpos'⟩ := pB
    cases hgoA : Inflate.decodeHuffmanFast.go litTree distTree maxOut litTree.buildTable
        distTree.buildTable br.data.size br output with
    | error eA => rw [hgoA, hgoB] at hco; exact absurd hco (by simp)
    | ok pA =>
      obtain ⟨out1, br'⟩ := pA
      rw [hgoA, hgoB] at hco
      obtain ⟨hout, hbc', hbd', hbo', hbpos'⟩ := hco
      simp only [bind, Except.bind, Except.ok.injEq, Prod.mk.injEq]
      refine ⟨hout.symm, ?_⟩
      -- the reconstructed reader equals br' (endbit = br'.bitPos, then byte/bit split)
      have hspan := hbc'.span
      have hend : pos' * 8 - cnt' = br'.bitPos := by simp only [BitReader.bitPos] at hspan ⊢; omega
      have hp : (pos' * 8 - cnt') / 8 = br'.pos := by
        rw [hend]; show (br'.pos * 8 + br'.bitOff) / 8 = br'.pos; omega
      have ho : (pos' * 8 - cnt') % 8 = br'.bitOff := by
        rw [hend]; show (br'.pos * 8 + br'.bitOff) % 8 = br'.bitOff; omega
      rw [hbd'.symm, hp, ho]

/-- The trees from `decodeDynamicTrees` have depth ≤ 15 (built by `fromLengths 15`). -/
theorem decodeDynamicTrees_depthLE {br : BitReader} {litTree distTree : HuffTree} {br' : BitReader}
    (h : Inflate.decodeDynamicTrees br = .ok (litTree, distTree, br')) :
    treeDepthLE litTree 15 ∧ treeDepthLE distTree 15 := by
  have bind_ok : ∀ {α β : Type} (e : Except String α) (f : α → Except String β) (r : β),
      (e >>= f) = .ok r → ∃ a, e = .ok a ∧ f a = .ok r := by
    intro α β e f r he
    cases e with
    | error e => simp [bind, Except.bind] at he
    | ok a => exact ⟨a, rfl, by simpa only [bind, Except.bind] using he⟩
  unfold Inflate.decodeDynamicTrees at h
  obtain ⟨_, _, h⟩ := bind_ok _ _ _ h
  obtain ⟨_, _, h⟩ := bind_ok _ _ _ h
  obtain ⟨_, _, h⟩ := bind_ok _ _ _ h
  obtain ⟨_, _, h⟩ := bind_ok _ _ _ h
  obtain ⟨_, _, h⟩ := bind_ok _ _ _ h
  obtain ⟨_, _, h⟩ := bind_ok _ _ _ h
  obtain ⟨litT, hlit, h⟩ := bind_ok _ _ _ h
  obtain ⟨distT, hdist, h⟩ := bind_ok _ _ _ h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, _⟩ := h
  exact ⟨fromLengths_depthLE hlit, fromLengths_depthLE hdist⟩

/-! ## The block loop and `inflate` equal the reference -/

/-- Any successful read of `≥ 1` bit leaves the reader byte-aligned-or-less
    (`bitOff < 8`), regardless of the starting offset. -/
theorem readBits_go_bitOff_lt_pos : ∀ (n : Nat) (br : BitReader) (acc : UInt32) (shift : Nat)
    (v : UInt32) (br' : BitReader),
    BitReader.readBits.go br acc shift (n + 1) = .ok (v, br') → br'.bitOff < 8 := by
  intro n
  induction n with
  | zero =>
    intro br acc shift v br' h
    simp only [BitReader.readBits.go, bind, Except.bind] at h
    cases hrb : br.readBit with
    | error e => rw [hrb] at h; simp at h
    | ok p =>
      obtain ⟨bit, br1⟩ := p
      rw [hrb] at h
      simp only [BitReader.readBits.go, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h
      exact ZipCommon.readBit_bitOff_lt br br1 bit hrb
  | succ n ih =>
    intro br acc shift v br' h
    simp only [BitReader.readBits.go, bind, Except.bind] at h
    cases hrb : br.readBit with
    | error e => rw [hrb] at h; simp at h
    | ok p =>
      obtain ⟨bit, br1⟩ := p
      rw [hrb] at h
      exact ih br1 _ _ v br' h

theorem readBits_bitOff_lt_pos {br br' : BitReader} {n : Nat} {v : UInt32} (hn : 0 < n)
    (h : br.readBits n = .ok (v, br')) : br'.bitOff < 8 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact readBits_go_bitOff_lt_pos m br 0 0 v br' h

/-- `HuffTree.decode.go` preserves `bitOff < 8`. -/
theorem decode_go_bitOff_pres : ∀ (t : HuffTree) (br : BitReader) (depth : Nat) (s : UInt16) (br' : BitReader),
    br.bitOff < 8 → HuffTree.decode.go t br depth = .ok (s, br') → br'.bitOff < 8 := by
  intro t
  induction t with
  | leaf s =>
    intro br depth s' br' hbo h
    simp only [HuffTree.decode.go, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h; exact hbo
  | empty => intro br depth s' br' hbo h; simp [HuffTree.decode.go] at h
  | node z o ihz iho =>
    intro br depth s' br' hbo h
    rw [HuffTree.decode.go] at h
    by_cases hd : depth > 20
    · rw [if_pos hd] at h; simp at h
    · rw [if_neg hd] at h
      cases hrb : br.readBit with
      | error e => rw [hrb] at h; simp [bind, Except.bind] at h
      | ok p =>
        obtain ⟨bit, br1⟩ := p
        rw [hrb] at h
        simp only [bind, Except.bind] at h
        have hbo1 : br1.bitOff < 8 := ZipCommon.readBit_bitOff_lt br br1 bit hrb
        by_cases hbit : (bit == 0) = true
        · rw [if_pos hbit] at h; exact ihz br1 _ s' br' hbo1 h
        · rw [if_neg hbit] at h; exact iho br1 _ s' br' hbo1 h

theorem decode_bitOff_pres {tree : HuffTree} {br br' : BitReader} {s : UInt16}
    (hbo : br.bitOff < 8) (h : tree.decode br = .ok (s, br')) : br'.bitOff < 8 :=
  decode_go_bitOff_pres tree br 0 s br' hbo h

/-- `readCLCodeLengths` preserves `bitOff < 8`. -/
theorem readCLCodeLengths_bitOff_pres (numCodeLen : Nat) :
    ∀ (br : BitReader) (cl : Array UInt8) (i : Nat) (cl' : Array UInt8) (br' : BitReader),
      br.bitOff < 8 → Inflate.readCLCodeLengths br cl i numCodeLen = .ok (cl', br') → br'.bitOff < 8 := by
  intro br cl i
  induction br, cl, i using Inflate.readCLCodeLengths.induct (numCodeLen := numCodeLen) with
  | case1 br cl i hlt h_i ih =>
    intro cl' br' hbo h
    rw [Inflate.readCLCodeLengths, if_pos hlt, dif_pos h_i] at h
    simp only [bind, Except.bind] at h
    cases hrb : br.readBits 3 with
    | error e => rw [hrb] at h; simp at h
    | ok p =>
      obtain ⟨v, br1⟩ := p
      rw [hrb] at h; simp only [] at h
      exact ih v br1 cl' br' (readBits_bitOff_lt_pos (by omega) hrb) h
  | case2 br cl i hlt h_ni =>
    intro cl' br' hbo h
    rw [Inflate.readCLCodeLengths, if_pos hlt, dif_neg h_ni] at h; simp at h
  | case3 br cl i hni =>
    intro cl' br' hbo h
    rw [Inflate.readCLCodeLengths, if_neg hni, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h; exact hbo

/-- `decodeCLSymbols` preserves `bitOff < 8`. -/
theorem decodeCLSymbols_bitOff_pres (clTree : HuffTree) (totalCodes : Nat) :
    ∀ (br : BitReader) (cl : Array UInt8) (idx : Nat) (cl' : Array UInt8) (br' : BitReader),
      br.bitOff < 8 → Inflate.decodeCLSymbols clTree br cl idx totalCodes = .ok (cl', br') →
      br'.bitOff < 8 := by
  intro br cl idx
  induction br, cl, idx using Inflate.decodeCLSymbols.induct (totalCodes := totalCodes) with
  | case1 br cl idx hge =>
    intro cl' br' hbo h
    rw [Inflate.decodeCLSymbols, if_pos hge, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h; exact hbo
  | case2 br cl idx hge ih_set ih16 ih17 ih18 =>
    intro cl' br' hbo h
    rw [Inflate.decodeCLSymbols, if_neg hge] at h
    simp only [bind, Except.bind] at h
    cases hdec : clTree.decode br with
    | error e => rw [hdec] at h; simp at h
    | ok p =>
      obtain ⟨sym, br1⟩ := p
      rw [hdec] at h; simp only [] at h
      have hbo1 : br1.bitOff < 8 := decode_bitOff_pres hbo hdec
      by_cases hs16 : sym < 16
      · rw [if_pos hs16] at h; exact ih_set sym br1 cl' br' hbo1 h
      · rw [if_neg hs16] at h
        by_cases he16 : (sym == 16) = true
        · rw [if_pos he16] at h
          by_cases hi0 : (idx == 0) = true
          · rw [if_pos hi0] at h; simp [bind, Except.bind] at h
          · rw [if_neg hi0] at h; simp only [bind, Except.bind, pure, Except.pure] at h
            by_cases hcl : idx - 1 < cl.size
            · rw [dif_pos hcl] at h
              cases hrb : br1.readBits 2 with
              | error e => rw [hrb] at h; simp at h
              | ok q =>
                obtain ⟨rep, br2⟩ := q; rw [hrb] at h; simp only [] at h
                split at h
                · simp at h
                · exact ih16 hcl rep br2 cl' br' (readBits_bitOff_lt_pos (by omega) hrb) h
            · rw [dif_neg hcl] at h; simp at h
        · rw [if_neg he16] at h
          by_cases he17 : (sym == 17) = true
          · rw [if_pos he17] at h
            cases hrb : br1.readBits 3 with
            | error e => rw [hrb] at h; simp at h
            | ok q =>
              obtain ⟨rep, br2⟩ := q; rw [hrb] at h; simp only [] at h
              split at h
              · simp at h
              · exact ih17 rep br2 cl' br' (readBits_bitOff_lt_pos (by omega) hrb) h
          · rw [if_neg he17] at h
            by_cases he18 : (sym == 18) = true
            · rw [if_pos he18] at h
              cases hrb : br1.readBits 7 with
              | error e => rw [hrb] at h; simp at h
              | ok q =>
                obtain ⟨rep, br2⟩ := q; rw [hrb] at h; simp only [] at h
                split at h
                · simp at h
                · exact ih18 rep br2 cl' br' (readBits_bitOff_lt_pos (by omega) hrb) h
            · rw [if_neg he18] at h; simp at h

/-- `decodeDynamicTrees` preserves `bitOff < 8`. -/
theorem decodeDynamicTrees_bitOff_pres {br : BitReader} {litTree distTree : HuffTree} {br' : BitReader}
    (hbo : br.bitOff < 8) (h : Inflate.decodeDynamicTrees br = .ok (litTree, distTree, br')) :
    br'.bitOff < 8 := by
  have bind_ok : ∀ {α β : Type} (e : Except String α) (f : α → Except String β) (r : β),
      (e >>= f) = .ok r → ∃ a, e = .ok a ∧ f a = .ok r := by
    intro α β e f r he
    cases e with
    | error e => simp [bind, Except.bind] at he
    | ok a => exact ⟨a, rfl, by simpa only [bind, Except.bind] using he⟩
  unfold Inflate.decodeDynamicTrees at h
  obtain ⟨⟨_, br1⟩, h1, h⟩ := bind_ok _ _ _ h
  obtain ⟨⟨_, br2⟩, h2, h⟩ := bind_ok _ _ _ h
  obtain ⟨⟨_, br3⟩, h3, h⟩ := bind_ok _ _ _ h
  obtain ⟨⟨_, br4⟩, h4, h⟩ := bind_ok _ _ _ h
  obtain ⟨clTree, _, h⟩ := bind_ok _ _ _ h
  obtain ⟨⟨_, br5⟩, h6, h⟩ := bind_ok _ _ _ h
  obtain ⟨_, _, h⟩ := bind_ok _ _ _ h
  obtain ⟨_, _, h⟩ := bind_ok _ _ _ h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨_, _, rfl⟩ := h
  have hb3 := readBits_bitOff_lt_pos (by omega) h3
  have hb4 := readCLCodeLengths_bitOff_pres _ br3 _ _ _ _ hb3 h4
  exact decodeCLSymbols_bitOff_pres clTree _ br4 _ _ _ _ hb4 h6
