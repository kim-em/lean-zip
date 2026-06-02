import Zip.Native.BitWriter
import Zip.Spec.Deflate
import Zip.Spec.Huffman

/-!
# BitWriter ↔ spec bitstream correspondence

Connects the native `BitWriter` (used by the DEFLATE compressor) to the
spec-level bitstream functions (`writeBitsLSB`, `bytesToBits`, `natToBits`).
-/

namespace Zip.Native.BitWriter

/-- The logical bit sequence represented by a BitWriter. -/
def toBits (bw : BitWriter) : List Bool :=
  bw.data.data.toList.flatMap Deflate.Spec.bytesToBits.byteToBits ++
  (List.range bw.bitCount.toNat).map (fun i => bw.bitBuf.toNat.testBit i)

/-- Well-formedness: bitCount < 8, no stale bits above bitCount. -/
def wf (bw : BitWriter) : Prop :=
  bw.bitCount.toNat < 8 ∧ bw.bitBuf.toNat < 2 ^ bw.bitCount.toNat

theorem empty_wf : empty.wf := by
  constructor <;> simp only [empty, UInt8.toNat_zero, Nat.zero_lt_succ, Nat.pow_zero, Nat.lt_add_one]

theorem empty_toBits : empty.toBits = [] := by
  simp only [toBits, empty, ByteArray.data_empty, Array.toList_empty, List.flatMap_nil,
    UInt8.toNat_zero, Nat.zero_testBit, List.range_zero, List.map_nil, List.append_nil]

/-! ## Helper lemmas -/

private theorem flatMap_byteToBits_push (data : ByteArray) (b : UInt8) :
    (data.push b).data.toList.flatMap Deflate.Spec.bytesToBits.byteToBits =
    data.data.toList.flatMap Deflate.Spec.bytesToBits.byteToBits ++
    Deflate.Spec.bytesToBits.byteToBits b := by
  simp only [ByteArray.push, Array.toList_push, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]

/-- byteToBits splits at bit boundary k when upper bits are zero. -/
private theorem byteToBits_split (b : UInt8) (k : Nat) (hk : k ≤ 8)
    (hb : b.toNat < 2 ^ k) :
    Deflate.Spec.bytesToBits.byteToBits b =
    (List.range k).map (fun i => b.toNat.testBit i) ++
    List.replicate (8 - k) false := by
  simp only [Deflate.Spec.bytesToBits.byteToBits]
  apply List.ext_getElem
  · simp only [List.ofFn_succ, Fin.isValue, Fin.val_zero, Nat.testBit_zero, Fin.val_succ,
      Nat.zero_add, Nat.reduceAdd, Fin.val_eq_zero, List.ofFn_zero, List.length_cons,
      List.length_nil, List.length_append, List.length_map, List.length_range,
      List.length_replicate]; omega
  · intro i h1 h2
    simp only [List.length_ofFn] at h1
    simp only [List.getElem_ofFn]
    by_cases hik : i < k
    · rw [List.getElem_append_left (by simp only [List.length_map, List.length_range]; omega)]
      simp only [List.getElem_map, List.getElem_range]
    · rw [List.getElem_append_right (by simp only [List.length_map, List.length_range]; omega)]
      simp only [List.length_map, List.length_range, List.getElem_replicate]
      exact Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by omega) (by omega)))

/-! ## Nat-level bit manipulation -/

/-- testBit below the shift position sees only the original value. -/
private theorem testBit_or_shiftLeft_below (a b k j : Nat) (hj : j < k) :
    (a ||| (b <<< k)).testBit j = a.testBit j := by
  rw [Nat.testBit_or, Nat.testBit_shiftLeft]
  simp only [ge_iff_le, show ¬(k ≤ j) from by omega, decide_false, Bool.false_and, Bool.or_false]

/-- `decide (x % 2 = 1) = (x % 2 != 0)` — common tail for the LSB extraction. -/
private theorem decide_mod2_eq_bne (x : Nat) :
    decide (x % 2 = 1) = (x % 2 != 0) := by
  cases h : x % 2 with
  | zero => simp only [Nat.zero_ne_one, decide_false, bne_self_eq_false]
  | succ n =>
    have : n = 0 := by omega
    subst this; simp only [Nat.zero_add, decide_true, Nat.reduceBNe]

/-- `(x % 2 == 1) = (x % 2 != 0)` — BEq variant for writeBits proofs. -/
private theorem beq_mod2_eq_bne (x : Nat) :
    (x % 2 == 1) = (x % 2 != 0) := decide_mod2_eq_bne x

/-! ## Batched bit-packing correspondence

The implementation merges a whole field into a 64-bit accumulator and flushes
whole bytes (`flushAcc`); these lemmas show that this matches the spec-level
bit lists, by characterizing `flushAcc` via `testBit` of the accumulator. -/

/-- `writeBitsLSB n v` is the low `n` bits of `v`, LSB first. -/
private theorem writeBitsLSB_eq_map (n v : Nat) :
    Deflate.Spec.writeBitsLSB n v = (List.range n).map (fun i => v.testBit i) := by
  induction n generalizing v with
  | zero => simp only [Deflate.Spec.writeBitsLSB, List.range_zero, List.map_nil]
  | succ k ih =>
    rw [Deflate.Spec.writeBitsLSB, ih (v / 2), List.range_succ_eq_map, List.map_cons,
      List.map_map]
    congr 1
    · simp only [Nat.testBit, Nat.shiftRight_zero, Nat.one_and_eq_mod_two]
      exact (beq_mod2_eq_bne v)
    · apply List.map_congr_left
      intro i _
      simp only [Function.comp_apply, Nat.testBit_succ]

/-- Split a `range`-map at position `m`. -/
private theorem range_map_split (f : Nat → Bool) (m total : Nat) (h : m ≤ total) :
    (List.range total).map f =
    (List.range m).map f ++ (List.range (total - m)).map (fun i => f (i + m)) := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, List.length_append]; omega
  · intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    by_cases hi : i < m
    · rw [List.getElem_append_left (by simp only [List.length_map, List.length_range]; omega)]
      simp only [List.getElem_map, List.getElem_range]
    · rw [List.getElem_append_right (by simp only [List.length_map, List.length_range]; omega)]
      simp only [List.getElem_map, List.getElem_range, List.length_map, List.length_range]
      congr 1
      omega

/-- testBit at or above the shift position sees the shifted value. -/
private theorem testBit_or_shiftLeft_above (a b k j : Nat) (ha : a < 2 ^ k) :
    (a ||| (b <<< k)).testBit (k + j) = b.testBit j := by
  rw [Nat.testBit_or, Nat.testBit_shiftLeft,
    Nat.testBit_lt_two_pow
      (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega) (Nat.le_add_right k j)))]
  simp only [ge_iff_le, Nat.le_add_right, decide_true, Nat.add_sub_cancel_left, Bool.true_and,
    Bool.false_or]

/-- OR of a bounded value with a shifted bounded value is bounded. -/
private theorem or_shiftLeft_lt (a m k p : Nat) (ha : a < 2 ^ k) (hm : m < 2 ^ p) :
    a ||| (m <<< k) < 2 ^ (k + p) := by
  have hshift : m <<< k < 2 ^ (k + p) := by
    rw [Nat.shiftLeft_eq, Nat.pow_add, Nat.mul_comm (2 ^ k) (2 ^ p)]
    exact Nat.mul_lt_mul_of_pos_right hm (Nat.two_pow_pos _)
  exact Nat.or_lt_two_pow
    (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega) (by omega))) hshift

/-- `byteToBits` of a byte is the 8-bit `testBit` list. -/
private theorem byteToBits_eq_range8 (b : UInt8) :
    Deflate.Spec.bytesToBits.byteToBits b =
    (List.range 8).map (fun i => b.toNat.testBit i) := by
  rw [byteToBits_split b 8 (by omega) (by simpa using b.toNat_lt)]
  simp only [Nat.sub_self, List.replicate_zero, List.append_nil]

/-- Core: flushing a 64-bit accumulator holding `total` valid low bits produces
    exactly those bits (`testBit acc`), preserving well-formedness. -/
private theorem flushAcc_spec (data : ByteArray) (acc : UInt64) (total : Nat)
    (hacc : acc.toNat < 2 ^ total) :
    (flushAcc data acc total).toBits =
      data.data.toList.flatMap Deflate.Spec.bytesToBits.byteToBits ++
      (List.range total).map (fun i => acc.toNat.testBit i) ∧
    (flushAcc data acc total).wf := by
  induction total using Nat.strongRecOn generalizing data acc with
  | ind total ih =>
    rw [flushAcc]
    by_cases hge : total ≥ 8
    · rw [if_pos hge]
      have hsr : (acc >>> 8).toNat = acc.toNat / 2 ^ 8 := by
        rw [UInt64.toNat_shiftRight, show (8 : UInt64).toNat % 64 = 8 from by decide,
          Nat.shiftRight_eq_div_pow]
      have hacc' : (acc >>> 8).toNat < 2 ^ (total - 8) := by
        rw [hsr]
        apply Nat.div_lt_of_lt_mul
        rw [← Nat.pow_add, show 8 + (total - 8) = total from by omega]
        exact hacc
      obtain ⟨ihb, ihw⟩ := ih (total - 8) (by omega) (data.push acc.toUInt8) (acc >>> 8) hacc'
      refine ⟨?_, ihw⟩
      rw [ihb, flatMap_byteToBits_push, List.append_assoc]
      congr 1
      rw [byteToBits_eq_range8, range_map_split (fun i => acc.toNat.testBit i) 8 total hge]
      congr 1
      · apply List.map_congr_left
        intro i hi
        simp only [List.mem_range] at hi
        rw [UInt64.toNat_toUInt8, Nat.testBit_mod_two_pow]
        simp only [hi, decide_true, Bool.true_and]
      · apply List.map_congr_left
        intro i _
        rw [hsr, Nat.testBit_div_two_pow, Nat.add_comm]
    · rw [if_neg hge]
      have htot : total < 8 := by omega
      have htu : total.toUInt8.toNat = total := by
        simp only [Nat.toUInt8, UInt8.toNat_ofNat']
        rw [show (2 : Nat) ^ 8 = 256 from rfl]; omega
      have hau : acc.toUInt8.toNat = acc.toNat := by
        rw [UInt64.toNat_toUInt8]
        exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hacc
          (Nat.pow_le_pow_right (by omega) (by omega)))
      refine ⟨?_, ?_, ?_⟩
      · simp only [toBits, htu]
        congr 1
        apply List.map_congr_left
        intro i _
        rw [hau]
      · show total.toUInt8.toNat < 8
        rw [htu]; exact htot
      · show acc.toUInt8.toNat < 2 ^ total.toUInt8.toNat
        rw [hau, htu]; exact hacc

/-! ## writeBits correspondence -/

private theorem writeBits_spec (bw : BitWriter) (n : Nat) (val : UInt32)
    (hwf : bw.wf) (hn : n ≤ 25) :
    (bw.writeBits n val).toBits =
      bw.toBits ++ Deflate.Spec.writeBitsLSB n val.toNat ∧
    (bw.writeBits n val).wf := by
  obtain ⟨hbc, hbuf⟩ := hwf
  have hmask : (val.toUInt64 % (1 <<< n.toUInt64)).toNat = val.toNat % 2 ^ n := by
    rw [UInt64.toNat_mod, UInt32.toNat_toUInt64, UInt64.toNat_shiftLeft]
    have h1 : (1 : UInt64).toNat = 1 := rfl
    have hn2lt : (2 : Nat) ^ n < 2 ^ 64 :=
      Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by omega) hn)
        (Nat.pow_lt_pow_right (by omega) (by omega))
    have hnlt : n < 2 ^ 64 := Nat.lt_of_le_of_lt hn (by decide)
    have hn64 : n.toUInt64.toNat % 64 = n := by
      have he : n.toUInt64.toNat = n := by
        simp only [Nat.toUInt64, UInt64.toNat_ofNat']
        exact Nat.mod_eq_of_lt hnlt
      rw [he]; omega
    rw [h1, hn64, Nat.one_shiftLeft, Nat.mod_eq_of_lt hn2lt]
  have hbc64 : bw.bitCount.toUInt64.toNat % 64 = bw.bitCount.toNat := by
    simp only [UInt8.toNat_toUInt64]; omega
  have hmlt : val.toNat % 2 ^ n < 2 ^ n := Nat.mod_lt _ (Nat.two_pow_pos _)
  -- the accumulator as a Nat
  have hacc_nat :
      (bw.bitBuf.toUInt64 ||| ((val.toUInt64 % (1 <<< n.toUInt64)) <<< bw.bitCount.toUInt64)).toNat
      = bw.bitBuf.toNat ||| ((val.toNat % 2 ^ n) <<< bw.bitCount.toNat) := by
    rw [UInt64.toNat_or, UInt8.toNat_toUInt64, UInt64.toNat_shiftLeft, hmask, hbc64]
    congr 1
    apply Nat.mod_eq_of_lt
    rw [Nat.shiftLeft_eq]
    calc (val.toNat % 2 ^ n) * 2 ^ bw.bitCount.toNat
        < 2 ^ n * 2 ^ bw.bitCount.toNat :=
          Nat.mul_lt_mul_of_pos_right hmlt (Nat.two_pow_pos _)
      _ = 2 ^ (n + bw.bitCount.toNat) := (Nat.pow_add 2 n _).symm
      _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) (by omega)
  have haccbound :
      (bw.bitBuf.toUInt64 ||| ((val.toUInt64 % (1 <<< n.toUInt64)) <<< bw.bitCount.toUInt64)).toNat
      < 2 ^ (bw.bitCount.toNat + n) := by
    rw [hacc_nat]
    exact or_shiftLeft_lt bw.bitBuf.toNat (val.toNat % 2 ^ n) bw.bitCount.toNat n hbuf hmlt
  obtain ⟨hb, hw⟩ := flushAcc_spec bw.data _ (bw.bitCount.toNat + n) haccbound
  refine ⟨?_, ?_⟩
  · -- toBits
    simp only [writeBits]
    rw [hb, hacc_nat]
    simp only [toBits, List.append_assoc]
    congr 1
    rw [writeBitsLSB_eq_map,
      range_map_split (fun i => (bw.bitBuf.toNat ||| (val.toNat % 2 ^ n) <<< bw.bitCount.toNat).testBit i)
        bw.bitCount.toNat (bw.bitCount.toNat + n) (Nat.le_add_right _ _),
      show bw.bitCount.toNat + n - bw.bitCount.toNat = n from by omega]
    congr 1
    · apply List.map_congr_left
      intro i hi
      simp only [List.mem_range] at hi
      exact testBit_or_shiftLeft_below _ _ _ _ hi
    · apply List.map_congr_left
      intro i hi
      simp only [List.mem_range] at hi
      rw [Nat.add_comm i bw.bitCount.toNat,
        testBit_or_shiftLeft_above _ _ _ _ hbuf, Nat.testBit_mod_two_pow]
      simp only [hi, decide_true, Bool.true_and]
  · simp only [writeBits]; exact hw

theorem writeBits_toBits (bw : BitWriter) (n : Nat) (val : UInt32)
    (hwf : bw.wf) (hn : n ≤ 25) :
    (bw.writeBits n val).toBits =
    bw.toBits ++ Deflate.Spec.writeBitsLSB n val.toNat :=
  (writeBits_spec bw n val hwf hn).1

theorem writeBits_wf (bw : BitWriter) (n : Nat) (val : UInt32)
    (hwf : bw.wf) (hn : n ≤ 25) :
    (bw.writeBits n val).wf :=
  (writeBits_spec bw n val hwf hn).2

/-! ## writeHuffCode correspondence -/

/-- The branchless 16-bit reversal flips bit `j` to bit `15 - j`. -/
private theorem reverse16_testBit (x : UInt16) (j : Nat) (hj : j < 16) :
    (reverse16 x).toNat.testBit j = x.toNat.testBit (15 - j) := by
  rw [show (reverse16 x).toNat = (reverse16 x).toBitVec.toNat from rfl,
    show x.toNat = x.toBitVec.toNat from rfl, BitVec.testBit_toNat, BitVec.testBit_toNat]
  simp only [reverse16]
  match j, hj with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _
  | 8, _ | 9, _ | 10, _ | 11, _ | 12, _ | 13, _ | 14, _ | 15, _ => bv_decide
  | _ + 16, h => omega

/-- `natToBits` (MSB first) as a `range`-map. -/
private theorem natToBits_eq_map (v w : Nat) :
    Huffman.Spec.natToBits v w = (List.range w).map (fun i => v.testBit (w - 1 - i)) := by
  induction w with
  | zero => simp only [Huffman.Spec.natToBits, List.range_zero, List.map_nil]
  | succ k ih =>
    rw [Huffman.Spec.natToBits, ih, List.range_succ_eq_map, List.map_cons, List.map_map]
    refine List.cons_eq_cons.mpr ⟨?_, ?_⟩
    · congr 1 <;> omega
    · apply List.map_congr_left
      intro i _
      simp only [Function.comp_apply]
      congr 1 <;> omega

private theorem writeHuffCode_spec (bw : BitWriter) (code : UInt16) (len : UInt8)
    (hwf : bw.wf) (hlen : len.toNat ≤ 15) :
    (bw.writeHuffCode code len).toBits =
      bw.toBits ++ Huffman.Spec.natToBits code.toNat len.toNat ∧
    (bw.writeHuffCode code len).wf := by
  obtain ⟨hbc, hbuf⟩ := hwf
  -- the reversed code, shifted into packing position, as a Nat
  have hle : len.toUInt64 ≤ (16 : UInt64) := by
    rw [UInt64.le_iff_toNat_le, UInt8.toNat_toUInt64]
    exact Nat.le_trans hlen (by decide)
  have hsub : (16 - len.toUInt64).toNat = 16 - len.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ hle, UInt8.toNat_toUInt64,
      show (16 : UInt64).toNat = 16 from by decide]
  have hrev_nat : ((reverse16 code).toUInt64 >>> (16 - len.toUInt64)).toNat
      = (reverse16 code).toNat / 2 ^ (16 - len.toNat) := by
    rw [UInt64.toNat_shiftRight, UInt16.toNat_toUInt64, hsub,
      show (16 - len.toNat) % 64 = 16 - len.toNat from by omega, Nat.shiftRight_eq_div_pow]
  have hrevlt16 : (reverse16 code).toNat < 2 ^ 16 := by
    have := (reverse16 code).toNat_lt; simpa only [UInt16.size] using this
  have hrev_lt : ((reverse16 code).toUInt64 >>> (16 - len.toUInt64)).toNat < 2 ^ len.toNat := by
    rw [hrev_nat]
    apply Nat.div_lt_of_lt_mul
    rw [← Nat.pow_add, show (16 - len.toNat) + len.toNat = 16 from by omega]
    exact hrevlt16
  have hrev_bit : ∀ i, i < len.toNat →
      ((reverse16 code).toUInt64 >>> (16 - len.toUInt64)).toNat.testBit i
        = code.toNat.testBit (len.toNat - 1 - i) := by
    intro i hi
    rw [hrev_nat, Nat.testBit_div_two_pow, reverse16_testBit code (i + (16 - len.toNat)) (by omega)]
    congr 1; omega
  have hbc64 : bw.bitCount.toUInt64.toNat % 64 = bw.bitCount.toNat := by
    simp only [UInt8.toNat_toUInt64]; omega
  -- the accumulator as a Nat
  have hacc_nat :
      (bw.bitBuf.toUInt64 |||
        (((reverse16 code).toUInt64 >>> (16 - len.toUInt64)) <<< bw.bitCount.toUInt64)).toNat
      = bw.bitBuf.toNat |||
        (((reverse16 code).toUInt64 >>> (16 - len.toUInt64)).toNat <<< bw.bitCount.toNat) := by
    rw [UInt64.toNat_or, UInt8.toNat_toUInt64, UInt64.toNat_shiftLeft, hbc64]
    congr 1
    apply Nat.mod_eq_of_lt
    rw [Nat.shiftLeft_eq]
    calc ((reverse16 code).toUInt64 >>> (16 - len.toUInt64)).toNat * 2 ^ bw.bitCount.toNat
        < 2 ^ len.toNat * 2 ^ bw.bitCount.toNat :=
          Nat.mul_lt_mul_of_pos_right hrev_lt (Nat.two_pow_pos _)
      _ = 2 ^ (len.toNat + bw.bitCount.toNat) := (Nat.pow_add 2 _ _).symm
      _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) (by omega)
  have haccbound :
      (bw.bitBuf.toUInt64 |||
        (((reverse16 code).toUInt64 >>> (16 - len.toUInt64)) <<< bw.bitCount.toUInt64)).toNat
      < 2 ^ (bw.bitCount.toNat + len.toNat) := by
    rw [hacc_nat]
    exact or_shiftLeft_lt bw.bitBuf.toNat _ bw.bitCount.toNat len.toNat hbuf hrev_lt
  obtain ⟨hb, hw⟩ := flushAcc_spec bw.data _ (bw.bitCount.toNat + len.toNat) haccbound
  refine ⟨?_, ?_⟩
  · simp only [writeHuffCode]
    rw [hb, hacc_nat]
    simp only [toBits, List.append_assoc]
    congr 1
    rw [natToBits_eq_map,
      range_map_split (fun i => (bw.bitBuf.toNat |||
          ((reverse16 code).toUInt64 >>> (16 - len.toUInt64)).toNat <<< bw.bitCount.toNat).testBit i)
        bw.bitCount.toNat (bw.bitCount.toNat + len.toNat) (Nat.le_add_right _ _),
      show bw.bitCount.toNat + len.toNat - bw.bitCount.toNat = len.toNat from by omega]
    congr 1
    · apply List.map_congr_left
      intro i hi
      simp only [List.mem_range] at hi
      exact testBit_or_shiftLeft_below _ _ _ _ hi
    · apply List.map_congr_left
      intro i hi
      simp only [List.mem_range] at hi
      rw [Nat.add_comm i bw.bitCount.toNat, testBit_or_shiftLeft_above _ _ _ _ hbuf,
        hrev_bit i hi]
  · simp only [writeHuffCode]; exact hw

theorem writeHuffCode_toBits (bw : BitWriter) (code : UInt16) (len : UInt8)
    (hwf : bw.wf) (hlen : len.toNat ≤ 15) :
    (bw.writeHuffCode code len).toBits =
    bw.toBits ++ Huffman.Spec.natToBits code.toNat len.toNat :=
  (writeHuffCode_spec bw code len hwf hlen).1

theorem writeHuffCode_wf (bw : BitWriter) (code : UInt16) (len : UInt8)
    (hwf : bw.wf) (hlen : len.toNat ≤ 15) :
    (bw.writeHuffCode code len).wf :=
  (writeHuffCode_spec bw code len hwf hlen).2

/-! ## flush correspondence -/

theorem flush_toBits (bw : BitWriter) (hwf : bw.wf) :
    Deflate.Spec.bytesToBits bw.flush =
    bw.toBits ++ List.replicate ((8 - bw.bitCount.toNat % 8) % 8) false := by
  obtain ⟨hbc_lt, hbuf_lt⟩ := hwf
  unfold flush
  by_cases hbc0 : bw.bitCount.toNat = 0
  · -- bitCount = 0: no flush needed
    have hcond : ¬(bw.bitCount > 0) := by show ¬(0 < bw.bitCount.toNat); omega
    rw [if_neg hcond]
    simp only [hbc0, toBits, Deflate.Spec.bytesToBits, List.range_zero, List.map_nil,
      List.append_nil, Nat.zero_mod, Nat.sub_zero, Nat.mod_self, List.replicate_zero]
  · -- bitCount > 0: flush pushes bitBuf
    have hcond : bw.bitCount > 0 := by show 0 < bw.bitCount.toNat; omega
    rw [if_pos hcond]
    simp only [Deflate.Spec.bytesToBits]
    rw [flatMap_byteToBits_push]
    simp only [toBits, List.append_assoc]
    congr 1
    rw [byteToBits_split bw.bitBuf bw.bitCount.toNat (by omega) hbuf_lt]
    congr 1
    rw [Nat.mod_eq_of_lt hbc_lt,
        Nat.mod_eq_of_lt (show 8 - bw.bitCount.toNat < 8 from by omega)]

end Zip.Native.BitWriter
