import Zip.Spec.InflateBufCorrect
import Zip.Native.InflateFast

/-!
# Correctness infrastructure for the speculative wide decoder refill

The libdeflate refill keeps real future stream bits above the logical bit count.
`LowEq` records the observational fact used by the decoder: two words agree in
their first `n` bits. `trimBits` is the proof-side canonical representative.
-/

namespace Zip.Native.InflateBuf

private theorem byte_mul_lt_wide {b cnt : Nat} (h : b < 256) :
    b * 2 ^ cnt < 2 ^ (cnt + 8) := by
  calc
    b * 2 ^ cnt < 256 * 2 ^ cnt := (Nat.mul_lt_mul_right (Nat.two_pow_pos cnt)).mpr h
    _ = 2 ^ (cnt + 8) := by
      rw [Nat.pow_add, show (2 : Nat) ^ 8 = 256 from by decide, Nat.mul_comm]

private theorem byteShift_testBit (b : UInt8) (s j : Nat) (hs : s ≤ 56) :
    (b.toUInt64 <<< s.toUInt64).toNat.testBit j =
      if s ≤ j ∧ j < s + 8 then b.toNat.testBit (j - s) else false := by
  have hb : b.toNat < 256 := UInt8.toNat_lt b
  have hsmod : s.toUInt64.toNat % 64 = s := by simp [Nat.toUInt64]; omega
  have hshift : (b.toUInt64 <<< s.toUInt64).toNat = b.toNat * 2 ^ s := by
    rw [UInt64.toNat_shiftLeft, UInt8.toNat_toUInt64, hsmod, Nat.shiftLeft_eq]
    apply Nat.mod_eq_of_lt
    exact Nat.lt_of_lt_of_le (byte_mul_lt_wide hb)
      (Nat.pow_le_pow_right (by omega) (by omega))
  rw [hshift, Nat.testBit_mul_two_pow]
  by_cases hsj : s ≤ j
  · simp only [hsj, decide_true, Bool.true_and]
    by_cases hj : j < s + 8
    · simp only [hj, and_self, if_true]
    · simp only [hj, and_false, if_false]
      apply Nat.testBit_lt_two_pow
      exact Nat.lt_of_lt_of_le hb (show 2 ^ 8 ≤ 2 ^ (j - s) from
        Nat.pow_le_pow_right (by omega) (by omega))
  · simp [hsj]

private theorem toU64_8 : Nat.toUInt64 8 = 8 := rfl
private theorem toU64_16 : Nat.toUInt64 16 = 16 := rfl
private theorem toU64_24 : Nat.toUInt64 24 = 24 := rfl
private theorem toU64_32 : Nat.toUInt64 32 = 32 := rfl
private theorem toU64_40 : Nat.toUInt64 40 = 40 := rfl
private theorem toU64_48 : Nat.toUInt64 48 = 48 := rfl
private theorem toU64_56 : Nat.toUInt64 56 = 56 := rfl

private theorem byteShift8 (b : UInt8) (j : Nat) :
    (b.toUInt64 <<< 8).toNat.testBit j =
      if 8 ≤ j ∧ j < 16 then b.toNat.testBit (j - 8) else false := by
  simpa only [toU64_8] using byteShift_testBit b 8 j (by omega)

private theorem byteShift16 (b : UInt8) (j : Nat) :
    (b.toUInt64 <<< 16).toNat.testBit j =
      if 16 ≤ j ∧ j < 24 then b.toNat.testBit (j - 16) else false := by
  simpa only [toU64_16] using byteShift_testBit b 16 j (by omega)

private theorem byteShift24 (b : UInt8) (j : Nat) :
    (b.toUInt64 <<< 24).toNat.testBit j =
      if 24 ≤ j ∧ j < 32 then b.toNat.testBit (j - 24) else false := by
  simpa only [toU64_24] using byteShift_testBit b 24 j (by omega)

private theorem byteShift32 (b : UInt8) (j : Nat) :
    (b.toUInt64 <<< 32).toNat.testBit j =
      if 32 ≤ j ∧ j < 40 then b.toNat.testBit (j - 32) else false := by
  simpa only [toU64_32] using byteShift_testBit b 32 j (by omega)

private theorem byteShift40 (b : UInt8) (j : Nat) :
    (b.toUInt64 <<< 40).toNat.testBit j =
      if 40 ≤ j ∧ j < 48 then b.toNat.testBit (j - 40) else false := by
  simpa only [toU64_40] using byteShift_testBit b 40 j (by omega)

private theorem byteShift48 (b : UInt8) (j : Nat) :
    (b.toUInt64 <<< 48).toNat.testBit j =
      if 48 ≤ j ∧ j < 56 then b.toNat.testBit (j - 48) else false := by
  simpa only [toU64_48] using byteShift_testBit b 48 j (by omega)

private theorem byteShift56 (b : UInt8) (j : Nat) :
    (b.toUInt64 <<< 56).toNat.testBit j =
      if 56 ≤ j ∧ j < 64 then b.toNat.testBit (j - 56) else false := by
  simpa only [toU64_56] using byteShift_testBit b 56 j (by omega)

private theorem byte_testBit_high (b : UInt8) {j : Nat} (hj : 8 ≤ j) :
    b.toNat.testBit j = false := by
  apply Nat.testBit_lt_two_pow
  exact Nat.lt_of_lt_of_le (UInt8.toNat_lt b)
    (show 2 ^ 8 ≤ 2 ^ j from Nat.pow_le_pow_right (by omega) hj)

private theorem byteInterval_iff (j k : Nat) :
    k * 8 ≤ j ∧ j < (k + 1) * 8 ↔ j / 8 = k := by
  constructor
  · intro h
    apply Nat.le_antisymm
    · have := (Nat.div_lt_iff_lt_mul (k := 8) (x := j) (y := k + 1) (by omega)).mpr h.2
      omega
    · exact (Nat.le_div_iff_mul_le (k := 8) (x := k) (y := j) (by omega)).mpr h.1
  · intro h
    constructor
    · apply (Nat.le_div_iff_mul_le (k := 8) (x := k) (y := j) (by omega)).mp
      omega
    · apply (Nat.div_lt_iff_lt_mul (k := 8) (x := j) (y := k + 1) (by omega)).mp
      omega

/-- Two words agree on every bit below `n`. -/
def LowEq (a b : UInt64) (n : Nat) : Prop :=
  ∀ j, j < n → a.toNat.testBit j = b.toNat.testBit j

theorem LowEq.symm {a b : UInt64} {n : Nat} (h : LowEq a b n) : LowEq b a n := by
  intro j hj
  exact (h j hj).symm

/-- Consuming `k` bits preserves equality on the remaining low window. -/
theorem LowEq.shiftRight {a b : UInt64} {n k : Nat} (h : LowEq a b n)
    (hk : k ≤ n) (hk64 : k < 64) :
    LowEq (a >>> k.toUInt64) (b >>> k.toUInt64) (n - k) := by
  intro j hj
  have hkmod : k.toUInt64.toNat % 64 = k := by
    simp [Nat.toUInt64]
    omega
  rw [UInt64.toNat_shiftRight, UInt64.toNat_shiftRight, hkmod, Nat.testBit_shiftRight,
    Nat.testBit_shiftRight]
  exact h (k + j) (by omega)

/-- AND with a mask confined to the observed window turns low equality into
    ordinary word equality. -/
theorem LowEq.and_eq {a b mask : UInt64} {n : Nat} (h : LowEq a b n)
    (hm : mask.toNat < 2 ^ n) : a &&& mask = b &&& mask := by
  apply UInt64.toNat_inj.mp
  apply Nat.eq_of_testBit_eq
  intro j
  rw [UInt64.toNat_and, UInt64.toNat_and, Nat.testBit_and, Nat.testBit_and]
  by_cases hj : j < n
  · rw [h j hj]
  · have hz : mask.toNat.testBit j = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hm
        (Nat.pow_le_pow_right (by omega) (by omega)))
    rw [hz, Bool.and_false, Bool.and_false]

/-- Proof-side canonical buffer: discard every bit at or above `n`. -/
def trimBits (bitBuf : UInt64) (n : Nat) : UInt64 :=
  (bitBuf.toNat % 2 ^ n).toUInt64

theorem trimBits_toNat {bitBuf : UInt64} {n : Nat} (hn : n ≤ 64) :
    (trimBits bitBuf n).toNat = bitBuf.toNat % 2 ^ n := by
  simp only [trimBits, Nat.toUInt64, UInt64.toNat_ofNat']
  apply Nat.mod_eq_of_lt
  exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos n))
    (Nat.pow_le_pow_right (by omega) hn)

theorem lowEq_trimBits (bitBuf : UInt64) {n : Nat} (hn : n ≤ 64) :
    LowEq bitBuf (trimBits bitBuf n) n := by
  intro j hj
  rw [trimBits_toNat hn, Nat.testBit_mod_two_pow]
  simp only [decide_eq_true_eq.mpr hj, Bool.true_and]

/-- Trimming commutes with consuming counted bits. -/
theorem trimBits_shiftRight (bitBuf : UInt64) {n k : Nat} (hn : n ≤ 64)
    (hk : k ≤ n) (hk64 : k < 64) :
    trimBits bitBuf n >>> k.toUInt64 = trimBits (bitBuf >>> k.toUInt64) (n - k) := by
  apply UInt64.toNat_inj.mp
  apply Nat.eq_of_testBit_eq
  intro j
  have hkmod : k.toUInt64.toNat % 64 = k := by simp [Nat.toUInt64]; omega
  rw [UInt64.toNat_shiftRight, hkmod, Nat.testBit_shiftRight]
  by_cases hj : j < n - k
  · rw [trimBits_toNat hn, Nat.testBit_mod_two_pow]
    simp only [show k + j < n by omega, decide_true, Bool.true_and]
    rw [trimBits_toNat (by omega), Nat.testBit_mod_two_pow]
    simp only [hj, decide_true, Bool.true_and, UInt64.toNat_shiftRight, hkmod,
      Nat.testBit_shiftRight]
  · have hl : (trimBits bitBuf n).toNat.testBit (k + j) = false := by
      apply Nat.testBit_lt_two_pow
      exact Nat.lt_of_lt_of_le (by rw [trimBits_toNat hn]; exact Nat.mod_lt _ (Nat.two_pow_pos n))
        (Nat.pow_le_pow_right (by omega) (by omega))
    rw [hl]
    apply Eq.symm
    apply Nat.testBit_lt_two_pow
    rw [trimBits_toNat (by omega)]
    exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos (n - k)))
      (Nat.pow_le_pow_right (by omega) (by omega))

/-- Trimming an already exact buffer is a no-op. -/
theorem trimBits_eq_self {bitBuf : UInt64} {n : Nat} (hn : n ≤ 64)
    (hhigh : bitBuf.toNat < 2 ^ n) : trimBits bitBuf n = bitBuf := by
  apply UInt64.toNat_inj.mp
  rw [trimBits_toNat hn, Nat.mod_eq_of_lt hhigh]

@[simp] theorem trimBits_idem (bitBuf : UInt64) {n : Nat} (hn : n ≤ 64) :
    trimBits (trimBits bitBuf n) n = trimBits bitBuf n := by
  apply trimBits_eq_self hn
  rw [trimBits_toNat hn]
  exact Nat.mod_lt _ (Nat.two_pow_pos n)

theorem trimBits_shiftRight_congr (bitBuf : UInt64) {n k : Nat} (hn : n ≤ 64)
    (hk : k ≤ n) :
    trimBits (trimBits bitBuf n >>> k.toUInt64) (n - k) =
      trimBits (bitBuf >>> k.toUInt64) (n - k) := by
  by_cases hk64 : k < 64
  · rw [trimBits_shiftRight bitBuf hn hk hk64, trimBits_idem _ (by omega)]
  · have hn64 : n = 64 := by omega
    have hk' : k = 64 := by omega
    subst n
    subst k
    rw [trimBits_eq_self (n := 64) (by omega) (UInt64.toNat_lt _)]

/-- A speculative buffer has `cnt` logically consumed-aligned bits and `avail`
    physically loaded bits. Every loaded bit is a genuine stream bit. -/
structure WideBufCorr (data : ByteArray) (bitpos pos : Nat) (bitBuf : UInt64)
    (cnt avail : Nat) : Prop where
  span : bitpos + cnt = pos * 8
  posLe : pos ≤ data.size
  cntLe : cnt ≤ avail
  aheadLe : avail ≤ cnt + 8
  availLe : avail ≤ 64
  inStream : bitpos + avail ≤ data.size * 8
  high : bitBuf.toNat < 2 ^ avail
  bits : ∀ j, j < avail → bitBuf.toNat.testBit j = streamBit data (bitpos + j)

/-- An exact buffer is a speculative buffer with no look-ahead. -/
theorem BufCorr.toWide {data bitpos pos bitBuf cnt}
    (h : BufCorr data bitpos pos bitBuf cnt) :
    WideBufCorr data bitpos pos bitBuf cnt cnt := by
  refine ⟨h.span, h.posLe, Nat.le_refl _, by omega, h.cntLe, ?_, h.high, h.bits⟩
  have := h.span
  have := h.posLe
  omega

/-- Discarding look-ahead recovers an ordinary exact `BufCorr`. -/
theorem WideBufCorr.trim {data bitpos pos bitBuf cnt avail}
    (h : WideBufCorr data bitpos pos bitBuf cnt avail) :
    BufCorr data bitpos pos (trimBits bitBuf cnt) cnt := by
  have hcnt64 : cnt ≤ 64 := Nat.le_trans h.cntLe h.availLe
  refine ⟨h.span, h.posLe, hcnt64, ?_, ?_⟩
  · rw [trimBits_toNat hcnt64]
    exact Nat.mod_lt _ (Nat.two_pow_pos cnt)
  · intro j hj
    rw [trimBits_toNat hcnt64, Nat.testBit_mod_two_pow]
    simp only [decide_eq_true_eq.mpr hj, Bool.true_and]
    exact h.bits j (Nat.lt_of_lt_of_le hj h.cntLe)

/-- Consuming counted bits shifts both the logical count and the loaded extent. -/
theorem WideBufCorr.consume {data bitpos pos bitBuf cnt avail}
    (h : WideBufCorr data bitpos pos bitBuf cnt avail) {k : Nat}
    (hk : k ≤ cnt) (hk64 : k < 64) :
    WideBufCorr data (bitpos + k) pos (bitBuf >>> k.toUInt64) (cnt - k) (avail - k) := by
  have hkavail : k ≤ avail := Nat.le_trans hk h.cntLe
  refine ⟨by have := h.span; omega, h.posLe, Nat.sub_le_sub_right h.cntLe k,
    ?_, Nat.le_trans (Nat.sub_le avail k) h.availLe, ?_, ?_, ?_⟩
  · rw [← show cnt + 8 - k = cnt - k + 8 by omega]
    exact Nat.sub_le_sub_right h.aheadLe k
  · calc
      bitpos + k + (avail - k) = bitpos + avail := by omega
      _ ≤ data.size * 8 := h.inStream
  · have hkmod : k.toUInt64.toNat % 64 = k := by simp [Nat.toUInt64]; omega
    rw [UInt64.toNat_shiftRight, hkmod, Nat.shiftRight_eq_div_pow]
    apply Nat.div_lt_of_lt_mul
    rw [Nat.mul_comm, ← Nat.pow_add]
    have hak : avail - k + k = avail := by omega
    rw [hak]
    exact h.high
  · intro j hj
    have hkmod : k.toUInt64.toNat % 64 = k := by simp [Nat.toUInt64]; omega
    have hidx : k + j < avail := by omega
    have he : bitpos + (k + j) = bitpos + k + j := by omega
    rw [UInt64.toNat_shiftRight, hkmod, Nat.testBit_shiftRight, h.bits (k + j) hidx, he]

/-- The byte tail closes any at-most-one-byte look-ahead window: after ORing the
    next logical byte, the buffer is exact again. -/
theorem WideBufCorr.refillByte {data bitpos pos bitBuf cnt avail}
    (h : WideBufCorr data bitpos pos bitBuf cnt avail)
    (hcnt : cnt ≤ 56) (hpos : pos < data.size) :
    BufCorr data bitpos (pos + 1)
      (bitBuf ||| (data[pos]!.toUInt64 <<< cnt.toUInt64)) (cnt + 8) := by
  have hcnt64 : cnt ≤ 64 := Nat.le_trans h.cntLe h.availLe
  have hexact := refill_step h.trim hcnt hpos
  have heq : bitBuf ||| (data[pos]!.toUInt64 <<< cnt.toUInt64) =
      trimBits bitBuf cnt ||| (data[pos]!.toUInt64 <<< cnt.toUInt64) := by
    apply UInt64.toNat_inj.mp
    apply Nat.eq_of_testBit_eq
    intro j
    rw [UInt64.toNat_or, UInt64.toNat_or, Nat.testBit_or, Nat.testBit_or]
    by_cases hjn : j < cnt
    · rw [(lowEq_trimBits bitBuf hcnt64) j hjn]
    · have hz : (trimBits bitBuf cnt).toNat.testBit j = false := by
        apply Nat.testBit_lt_two_pow
        rw [trimBits_toNat hcnt64]
        exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos cnt))
          (Nat.pow_le_pow_right (by omega) (by omega))
      rw [hz, Bool.false_or]
      by_cases hjc : j < avail
      · have hj : j < cnt + 8 := Nat.lt_of_lt_of_le hjc h.aheadLe
        have he := hexact.bits j hj
        rw [UInt64.toNat_or, Nat.testBit_or, hz, Bool.false_or] at he
        rw [h.bits j hjc, he, Bool.or_self]
      · have hz' : bitBuf.toNat.testBit j = false :=
          Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h.high
            (Nat.pow_le_pow_right (by omega) (by omega)))
        rw [hz', Bool.false_or]
  rw [heq]
  exact hexact

/-- At end of input a speculative buffer cannot actually have look-ahead: the
    stream bound and the cursor equation force `avail = cnt`. -/
theorem WideBufCorr.trim_eq_of_pos_eq {data bitpos pos bitBuf cnt avail}
    (h : WideBufCorr data bitpos pos bitBuf cnt avail) (hp : pos = data.size) :
    trimBits bitBuf cnt = bitBuf := by
  subst pos
  apply trimBits_eq_self (Nat.le_trans h.cntLe h.availLe)
  have ha : avail = cnt := by
    apply Nat.le_antisymm
    · have hs := h.span
      have hi := h.inStream
      omega
    · exact h.cntLe
  simpa [ha] using h.high

/-- A full speculative state and its trimmed representative have the same
    11-bit root-table window. -/
theorem WideBufCorr.trim_and_0x7FF {data bitpos pos bitBuf cnt avail}
    (h : WideBufCorr data bitpos pos bitBuf cnt avail)
    (hfull : 56 < cnt ∨ pos = data.size) :
    trimBits bitBuf cnt &&& 0x7FF = bitBuf &&& 0x7FF := by
  rcases hfull with hc | hp
  · apply LowEq.and_eq (n := cnt)
      ((lowEq_trimBits bitBuf (Nat.le_trans h.cntLe h.availLe)).symm)
    have hm : (0x7FF : UInt64).toNat = 2047 := rfl
    rw [hm]
    exact Nat.lt_of_lt_of_le (by decide : 2047 < 2 ^ 11)
      (Nat.pow_le_pow_right (by omega) (by omega))
  · rw [h.trim_eq_of_pos_eq hp]

theorem refill_eq_self_of_full (data : ByteArray) (pos : Nat) (bitBuf : UInt64)
    (cnt : Nat) (hfull : 56 < cnt ∨ pos = data.size) :
    refill data pos bitBuf cnt = (pos, bitBuf, cnt) := by
  rw [refill]
  apply dif_neg
  intro h
  rcases hfull with hc | hp
  · omega
  · omega

theorem refillGuard_usize_false_of_full (data : ByteArray) (pos cnt : USize)
    (hsz : data.size < USize.size) (hfull : 56 < cnt.toNat ∨ pos.toNat = data.size) :
    ¬(cnt ≤ 56 ∧ pos < data.size.toUSize) := by
  intro hg
  have hgn := (refillGuard_usize data pos cnt hsz).mp hg
  rcases hfull with hc | hp <;> omega

/-- Any exact full state corresponding to a speculative state is the canonical
    result of refilling the latter's trimmed input state. -/
theorem refill_eq_trimmed_full {data : ByteArray} {bitpos p0 p1 : Nat}
    {b0 b1 : UInt64} {c0 c1 a0 a1 : Nat}
    (h0 : WideBufCorr data bitpos p0 b0 c0 a0)
    (h1 : WideBufCorr data bitpos p1 b1 c1 a1)
    (hfull : 56 < c1 ∨ p1 = data.size) :
    refill data p0 (trimBits b0 c0) c0 = (p1, trimBits b1 c1, c1) := by
  calc
    refill data p0 (trimBits b0 c0) c0 =
        refill data p1 (trimBits b1 c1) c1 := refill_canonical h0.trim h1.trim
    _ = (p1, trimBits b1 c1, c1) := refill_eq_self_of_full data p1 _ c1 hfull

/-- A wide little-endian load is exactly the next 64 LSB-first stream bits. -/
theorem ugetUInt64LE_testBit (data : ByteArray) (pos : USize)
    (hpos : pos.toNat + 8 ≤ data.size) (j : Nat) (hj : j < 64) :
    (data.ugetUInt64LE pos hpos).toNat.testBit j =
      streamBit data (pos.toNat * 8 + j) := by
  rw [ByteArray.ugetUInt64LE]
  simp only [UInt64.toNat_or, Nat.testBit_or, UInt8.toNat_toUInt64]
  rw [byteShift56, byteShift48, byteShift40, byteShift32, byteShift24, byteShift16,
    byteShift8]
  simp only [show (8 ≤ j ∧ j < 16) ↔ j / 8 = 1 by simpa using byteInterval_iff j 1,
    show (16 ≤ j ∧ j < 24) ↔ j / 8 = 2 by simpa using byteInterval_iff j 2,
    show (24 ≤ j ∧ j < 32) ↔ j / 8 = 3 by simpa using byteInterval_iff j 3,
    show (32 ≤ j ∧ j < 40) ↔ j / 8 = 4 by simpa using byteInterval_iff j 4,
    show (40 ≤ j ∧ j < 48) ↔ j / 8 = 5 by simpa using byteInterval_iff j 5,
    show (48 ≤ j ∧ j < 56) ↔ j / 8 = 6 by simpa using byteInterval_iff j 6,
    show (56 ≤ j ∧ j < 64) ↔ j / 8 = 7 by simpa using byteInterval_iff j 7]
  have hcases : j < 8 ∨ (8 ≤ j ∧ j < 16) ∨ (16 ≤ j ∧ j < 24) ∨
      (24 ≤ j ∧ j < 32) ∨ (32 ≤ j ∧ j < 40) ∨ (40 ≤ j ∧ j < 48) ∨
      (48 ≤ j ∧ j < 56) ∨ (56 ≤ j ∧ j < 64) := by omega
  rcases hcases with h | h | h | h | h | h | h | h
  all_goals
    simp only [streamBit]
    have hdiv : (pos.toNat * 8 + j) / 8 = pos.toNat + j / 8 := by omega
    have hmod : (pos.toNat * 8 + j) % 8 = j % 8 := by omega
    rw [hdiv, hmod]
  · have hj0 : j / 8 = 0 := by omega
    have hjm : j % 8 = j := Nat.mod_eq_of_lt h
    simp only [hj0, hjm, Nat.add_zero]
    rw [getElem!_pos data pos.toNat (by omega)]
    simp [hj0]
  · have hj0 : j / 8 = 1 := by omega
    have hjm : j % 8 = j - 8 := by omega
    simp only [hj0, hjm]
    rw [getElem!_pos data (pos.toNat + 1) (by omega), byte_testBit_high _ (by omega)]
    simp [hj0]
  · have hj0 : j / 8 = 2 := by omega
    have hjm : j % 8 = j - 16 := by omega
    simp only [hj0, hjm]
    rw [getElem!_pos data (pos.toNat + 2) (by omega), byte_testBit_high _ (by omega)]
    simp [hj0]
  · have hj0 : j / 8 = 3 := by omega
    have hjm : j % 8 = j - 24 := by omega
    simp only [hj0, hjm]
    rw [getElem!_pos data (pos.toNat + 3) (by omega), byte_testBit_high _ (by omega)]
    simp [hj0]
  · have hj0 : j / 8 = 4 := by omega
    have hjm : j % 8 = j - 32 := by omega
    simp only [hj0, hjm]
    rw [getElem!_pos data (pos.toNat + 4) (by omega), byte_testBit_high _ (by omega)]
    simp [hj0]
  · have hj0 : j / 8 = 5 := by omega
    have hjm : j % 8 = j - 40 := by omega
    simp only [hj0, hjm]
    rw [getElem!_pos data (pos.toNat + 5) (by omega), byte_testBit_high _ (by omega)]
    simp [hj0]
  · have hj0 : j / 8 = 6 := by omega
    have hjm : j % 8 = j - 48 := by omega
    simp only [hj0, hjm]
    rw [getElem!_pos data (pos.toNat + 6) (by omega), byte_testBit_high _ (by omega)]
    simp [hj0]
  · have hj0 : j / 8 = 7 := by omega
    have hjm : j % 8 = j - 56 := by omega
    simp only [hj0, hjm]
    rw [getElem!_pos data (pos.toNat + 7) (by omega), byte_testBit_high _ (by omega)]
    simp [hj0]

private theorem shiftLeft_testBit (word : UInt64) {cnt j : Nat} (hcnt : cnt < 64)
    (hj : j < 64) :
    (word <<< cnt.toUInt64).toNat.testBit j =
      if cnt ≤ j then word.toNat.testBit (j - cnt) else false := by
  have hcmod : cnt.toUInt64.toNat % 64 = cnt := by simp [Nat.toUInt64]; omega
  rw [UInt64.toNat_shiftLeft, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft, hcmod]
  simp only [hj, decide_true, Bool.true_and]
  by_cases h : cnt ≤ j <;> simp [h]

/-- A wide load establishes a 64-bit speculative buffer while advancing the
    logical input cursor by only the whole bytes newly counted. -/
theorem wideLoad_corr {data : ByteArray} {bitpos avail : Nat} (pos : USize)
    {bitBuf : UInt64} {cnt : Nat} (h : WideBufCorr data bitpos pos.toNat bitBuf cnt avail)
    (hcnt : cnt < 64) (hpos : pos.toNat + 8 ≤ data.size) :
    WideBufCorr data bitpos
      (pos.toNat + (64 - cnt) / 8)
      (bitBuf ||| (data.ugetUInt64LE pos hpos <<< cnt.toUInt64))
      (cnt + 8 * ((64 - cnt) / 8)) 64 := by
  have hk : 8 * ((64 - cnt) / 8) ≤ 64 - cnt := by omega
  have hrem : 64 - cnt < 8 * ((64 - cnt) / 8) + 8 := by omega
  refine ⟨by have := h.span; omega, by omega, by omega, by omega, by omega,
    by have := h.span; omega, UInt64.toNat_lt _, ?_⟩
  intro j hj
  rw [UInt64.toNat_or, Nat.testBit_or, shiftLeft_testBit _ hcnt hj]
  by_cases hjc : j < cnt
  · rw [if_neg (by omega), Bool.or_false, h.bits j (Nat.lt_of_lt_of_le hjc h.cntLe)]
  · rw [if_pos (by omega), ugetUInt64LE_testBit data pos hpos (j - cnt) (by omega)]
    have heq : pos.toNat * 8 + (j - cnt) = bitpos + j := by
      have := h.span
      omega
    rw [heq]
    by_cases hja : j < avail
    · rw [h.bits j hja, Bool.or_self]
    · have hz : bitBuf.toNat.testBit j = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h.high
          (Nat.pow_le_pow_right (by omega) (by omega)))
      rw [hz, Bool.false_or]

/-- `wideRefillU` preserves the speculative-buffer invariant. -/
theorem wideRefillU_corr {data : ByteArray} {bitpos avail : Nat} (pos : USize)
    {bitBuf : UInt64} (cnt : USize) (hsz : data.size < USize.size)
    (h : WideBufCorr data bitpos pos.toNat bitBuf cnt.toNat avail) :
    ∃ avail', WideBufCorr data bitpos
      (wideRefillU data pos bitBuf cnt hsz).pos.toNat
      (wideRefillU data pos bitBuf cnt hsz).bitBuf
      (wideRefillU data pos bitBuf cnt hsz).cnt.toNat avail' := by
  simp only [wideRefillU]
  split
  · rename_i hw
    have hg := (refillGuardWide_usize data pos cnt hsz).mp hw
    have hk := wideRefillK_toNat cnt hg.1
    have hc := wideRefillCnt_toNat cnt hg.1
    have hp : (pos + ((64 - cnt) >>> 3)).toNat =
        pos.toNat + (64 - cnt.toNat) / 8 := by
      rw [USize.toNat_add, hk]
      apply Nat.mod_eq_of_lt
      rw [← USize.size_eq_two_pow]
      omega
    refine ⟨64, ?_⟩
    simp only [hp, hc]
    rw [usize_toUInt64_toNat]
    exact wideLoad_corr pos h (by omega) hg.2
  · exact ⟨avail, h⟩

/-- Once the byte-tail guard is false, the post-wide-refill state is full in
    exactly the sense used by the canonical refill proof. -/
theorem wideRefillU_full_of_no_tail {data : ByteArray} {bitpos avail : Nat}
    (pos : USize) {bitBuf : UInt64} (cnt : USize) (hsz : data.size < USize.size)
    (h : WideBufCorr data bitpos pos.toNat bitBuf cnt.toNat avail)
    (hn : ¬((wideRefillU data pos bitBuf cnt hsz).didWide = false ∧
      (wideRefillU data pos bitBuf cnt hsz).cnt ≤ 56 ∧
      (wideRefillU data pos bitBuf cnt hsz).pos < data.size.toUSize)) :
    ∃ avail', WideBufCorr data bitpos
        (wideRefillU data pos bitBuf cnt hsz).pos.toNat
        (wideRefillU data pos bitBuf cnt hsz).bitBuf
        (wideRefillU data pos bitBuf cnt hsz).cnt.toNat avail' ∧
      (56 < (wideRefillU data pos bitBuf cnt hsz).cnt.toNat ∨
        (wideRefillU data pos bitBuf cnt hsz).pos.toNat = data.size) := by
  obtain ⟨avail', hw⟩ := wideRefillU_corr pos cnt hsz h
  refine ⟨avail', hw, ?_⟩
  by_cases hd : (wideRefillU data pos bitBuf cnt hsz).didWide = false
  · by_cases hc : (wideRefillU data pos bitBuf cnt hsz).cnt ≤ 56
    · have hp : ¬ (wideRefillU data pos bitBuf cnt hsz).pos < data.size.toUSize := by
        intro hp
        exact hn ⟨hd, hc, hp⟩
      right
      have hs : data.size.toUSize.toNat = data.size := toUSize_toNat_of_lt hsz
      have hpn : ¬ (wideRefillU data pos bitBuf cnt hsz).pos.toNat < data.size := by
        intro hlt
        apply hp
        apply USize.lt_iff_toNat_lt.mpr
        rwa [hs]
      have hple := hw.posLe
      omega
    · left
      have h56 : (56 : USize).toNat = 56 :=
        USize.toNat_ofNat_of_lt (Nat.lt_of_lt_of_le (by decide) USize.le_size)
      rw [USize.le_iff_toNat_le, h56] at hc
      omega
  · simp only [wideRefillU] at hd
    split at hd
    · rename_i hg
      left
      have hc := wideRefillCnt_toNat cnt ((refillGuardWide_usize data pos cnt hsz).mp hg).1
      simp only [wideRefillU, dif_pos hg]
      omega
    · exact (hd rfl).elim

/-- The runtime cold-tail mask is the proof-side canonical buffer. -/
theorem trimBitBufU_eq_trimBits (bitBuf : UInt64) (cnt : USize) (hcnt : cnt.toNat ≤ 64) :
    trimBitBufU bitBuf cnt = trimBits bitBuf cnt.toNat := by
  unfold trimBitBufU
  split
  · rename_i h
    simp only [beq_iff_eq] at h
    have h64 : (64 : USize).toNat = 64 :=
      USize.toNat_ofNat_of_lt (Nat.lt_of_lt_of_le (by decide) USize.le_size)
    have hc : cnt.toNat = 64 := by rw [h, h64]
    rw [hc, trimBits_eq_self (by omega) (UInt64.toNat_lt _)]
  · rename_i h
    have hc : cnt.toNat < 64 := by
      simp only [beq_iff_eq, not_false_eq_true] at h
      have h64 : (64 : USize).toNat = 64 :=
        USize.toNat_ofNat_of_lt (Nat.lt_of_lt_of_le (by decide) USize.le_size)
      have : cnt.toNat ≠ 64 := by intro he; apply h; apply USize.toNat_inj.mp; rw [h64, he]
      omega
    apply UInt64.toNat_inj.mp
    rw [usize_toUInt64_toNat]
    rw [UInt64.toNat_and, mask_toNat hc, Nat.and_two_pow_sub_one_eq_mod,
      trimBits_toNat (by omega)]

/-- Canonicalize only the returned buffer of a symbol-decode result. -/
private def trimDecodeResult (r : UInt16 × UInt64 × Nat × Nat) :
    UInt16 × UInt64 × Nat × Nat :=
  (r.1, trimBits r.2.1 r.2.2.1, r.2.2.1, r.2.2.2)

/-- With the production 15-bit tables and a full buffer, speculative bits above
    `cnt` cannot affect symbol selection. They only survive above the returned
    count, where `trimDecodeResult` removes them. -/
theorem decodeSymCanon_trim (ld : HuffTree.LongDecode) (table : HuffTree.DecodeTable)
    (bitBuf : UInt64) (cnt : Nat) (hcnt : 15 ≤ cnt) (hcnt64 : cnt ≤ 64) :
    (HuffTree.decodeSymCanon ld table 15 (trimBits bitBuf cnt) cnt).map trimDecodeResult =
      (HuffTree.decodeSymCanon ld table 15 bitBuf cnt).map trimDecodeResult := by
  have hlow : LowEq (trimBits bitBuf cnt) bitBuf cnt :=
    (lowEq_trimBits bitBuf hcnt64).symm
  have hroot : trimBits bitBuf cnt &&& 0x7FF = bitBuf &&& 0x7FF := by
    apply hlow.and_eq
    have : (0x7FF : UInt64).toNat = 2047 := rfl
    rw [this]
    exact Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (by omega) hcnt)
  have hshift := hlow.shiftRight (k := 11) (by omega) (by omega)
  have hsub :
      (trimBits bitBuf cnt >>> (HuffTree.fastBits : Nat).toUInt64) &&&
          (2 ^ (15 - HuffTree.fastBits) - 1 : Nat).toUInt64 =
        (bitBuf >>> (HuffTree.fastBits : Nat).toUInt64) &&&
          (2 ^ (15 - HuffTree.fastBits) - 1 : Nat).toUInt64 := by
    apply LowEq.and_eq (n := cnt - 11) hshift
    simp only [HuffTree.fastBits]
    have hm : ((2 ^ (15 - 11) - 1 : Nat).toUInt64).toNat = 15 := by decide
    rw [hm]
    calc
      15 < 2 ^ 4 := by decide
      _ ≤ 2 ^ (cnt - 11) := Nat.pow_le_pow_right (by omega) (by omega)
  simp only [HuffTree.decodeSymCanon]
  rw [hroot]
  split
  · simp only [HuffTree.subLookup, hroot, hsub]
    split
    · rfl
    · split
      · rfl
      · split
        · rfl
        · split
          · rfl
          · simp only [Except.map, trimDecodeResult]
            rw [trimBits_shiftRight_congr bitBuf hcnt64 (by omega)]
  · simp only [Except.map, trimDecodeResult]
    simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, not_or] at ‹¬ _›
    rw [trimBits_shiftRight_congr bitBuf hcnt64 (by omega)]

theorem WideBufCorr.decodeSymCanon_map_trim (h : WideBufCorr data bitpos pos bitBuf cnt avail)
    (hready : 15 ≤ cnt ∨ pos = data.size)
    (ld : HuffTree.LongDecode) (table : HuffTree.DecodeTable) :
    (HuffTree.decodeSymCanon ld table 15 (trimBits bitBuf cnt) cnt).map trimDecodeResult =
      (HuffTree.decodeSymCanon ld table 15 bitBuf cnt).map trimDecodeResult := by
  rcases hready with hc | hp
  · exact decodeSymCanon_trim ld table bitBuf cnt hc
      (Nat.le_trans h.cntLe h.availLe)
  · rw [h.trim_eq_of_pos_eq hp]

/-- A successful canonical-table decode consumes exactly its reported number
    of bits. This structural fact does not require the table to be valid. -/
theorem decodeSymCanon_ok_spec (ld : HuffTree.LongDecode) (table : HuffTree.DecodeTable)
    (maxBits : Nat) (bitBuf : UInt64) (cnt : Nat) {sym : UInt16} {bb : UInt64}
    {c used : Nat}
    (h : HuffTree.decodeSymCanon ld table maxBits bitBuf cnt = .ok (sym, bb, c, used)) :
    bb = bitBuf >>> used.toUInt64 ∧ c = cnt - used ∧ used ≤ cnt := by
  simp only [HuffTree.decodeSymCanon] at h
  split at h
  · simp only [HuffTree.subLookup] at h
    split at h
    · contradiction
    · split at h
      · contradiction
      · split at h
        · contradiction
        · split at h
          · contradiction
          · rename_i hlen
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl, rfl⟩ := h
            exact ⟨rfl, rfl, Nat.not_lt.mp hlen⟩
  · rename_i hguard
    simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, not_or] at hguard
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    exact ⟨rfl, rfl, Nat.not_lt.mp hguard.2⟩

theorem WideBufCorr.decodeSymCanon_trim_ok
    (h : WideBufCorr data bitpos pos bitBuf cnt avail)
    (hready : 15 ≤ cnt ∨ pos = data.size)
    (ld : HuffTree.LongDecode) (table : HuffTree.DecodeTable)
    {sym : UInt16} {bb : UInt64} {c used : Nat} (hused64 : used < 64)
    (hde : HuffTree.decodeSymCanon ld table 15 bitBuf cnt = .ok (sym, bb, c, used)) :
    HuffTree.decodeSymCanon ld table 15 (trimBits bitBuf cnt) cnt =
      .ok (sym, trimBits bb c, c, used) := by
  have hm := h.decodeSymCanon_map_trim hready ld table
  rw [hde] at hm
  cases hx : HuffTree.decodeSymCanon ld table 15 (trimBits bitBuf cnt) cnt with
  | error e => rw [hx] at hm; contradiction
  | ok x =>
    obtain ⟨xs, xbb, xc, xu⟩ := x
    rw [hx] at hm
    simp only [Except.map, trimDecodeResult, Except.ok.injEq, Prod.mk.injEq] at hm
    obtain ⟨rfl, htrim, rfl, rfl⟩ := hm
    obtain ⟨hcanon, _, _⟩ := decodeSymCanon_ok_spec ld table 15
      (trimBits bitBuf cnt) cnt hx
    obtain ⟨hraw, hc, hu⟩ := decodeSymCanon_ok_spec ld table 15 bitBuf cnt hde
    rw [hcanon, hraw, hc]
    congr 2
    congr 2
    exact trimBits_shiftRight bitBuf (Nat.le_trans h.cntLe h.availLe) hu hused64

private def trimTakeResult (r : Nat × UInt64 × Nat) : Nat × UInt64 × Nat :=
  (r.1, trimBits r.2.1 r.2.2, r.2.2)

/-- Speculative bits above the count cannot affect a bounded `takeBits`. -/
theorem takeBits_trim (bitBuf : UInt64) (cnt n : Nat) (hn : n ≤ cnt)
    (hn64 : n < 64) (hcnt64 : cnt ≤ 64) :
    (takeBits (trimBits bitBuf cnt) cnt n).map trimTakeResult =
      (takeBits bitBuf cnt n).map trimTakeResult := by
  have hfield :
      trimBits bitBuf cnt &&& (((1 : UInt64) <<< n.toUInt64) - 1) =
        bitBuf &&& (((1 : UInt64) <<< n.toUInt64) - 1) := by
    apply ((lowEq_trimBits bitBuf hcnt64).symm).and_eq
    rw [mask_toNat hn64]
    exact Nat.lt_of_lt_of_le
      (Nat.sub_lt (n := 2 ^ n) (m := 1) (Nat.two_pow_pos n) (by omega))
      (Nat.pow_le_pow_right (by omega) hn)
  have hnot : ¬n > cnt := by omega
  simp only [takeBits, if_neg hnot, Except.map, trimTakeResult]
  rw [hfield]
  rw [trimBits_shiftRight_congr bitBuf hcnt64 hn]

theorem takeBits_ok_spec (bitBuf : UInt64) (cnt n : Nat) {v : Nat} {bb : UInt64} {c : Nat}
    (h : takeBits bitBuf cnt n = .ok (v, bb, c)) :
    n ≤ cnt ∧ bb = bitBuf >>> n.toUInt64 ∧ c = cnt - n := by
  simp only [takeBits] at h
  split at h
  · contradiction
  · rename_i hn
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨Nat.not_lt.mp hn, rfl, rfl⟩

theorem takeBits_trim_ok (bitBuf : UInt64) (cnt n : Nat) (hn : n ≤ cnt)
    (hn64 : n < 64) (hcnt64 : cnt ≤ 64) {v : Nat} {bb : UInt64} {c : Nat}
    (h : takeBits bitBuf cnt n = .ok (v, bb, c)) :
    takeBits (trimBits bitBuf cnt) cnt n = .ok (v, trimBits bb c, c) := by
  have hm := takeBits_trim bitBuf cnt n hn hn64 hcnt64
  rw [h] at hm
  cases hx : takeBits (trimBits bitBuf cnt) cnt n with
  | error e => rw [hx] at hm; contradiction
  | ok x =>
    obtain ⟨xv, xbb, xc⟩ := x
    rw [hx] at hm
    simp only [Except.map, trimTakeResult, Except.ok.injEq, Prod.mk.injEq] at hm
    obtain ⟨rfl, htrim, rfl⟩ := hm
    obtain ⟨_, hcanon, _⟩ := takeBits_ok_spec (trimBits bitBuf cnt) cnt n hx
    obtain ⟨_, hraw, hc⟩ := takeBits_ok_spec bitBuf cnt n h
    rw [hcanon, hraw, hc]
    congr 2
    congr 2
    exact trimBits_shiftRight bitBuf hcnt64 hn hn64

theorem takeBits_trim_error (bitBuf : UInt64) (cnt n : Nat) {e : String}
    (h : takeBits bitBuf cnt n = .error e) :
    takeBits (trimBits bitBuf cnt) cnt n = .error e := by
  unfold takeBits at h ⊢
  by_cases hn : n > cnt
  · simp only [if_pos hn] at h ⊢
    exact h
  · simp only [if_neg hn] at h ⊢
    contradiction

end Zip.Native.InflateBuf
