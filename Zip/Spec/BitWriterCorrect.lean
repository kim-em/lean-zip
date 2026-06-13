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

/-! ## writeFour correspondence (Wave 6.1 reference-token fusion)

`writeFour` packs a reference token's four fields (length code, length extra
bits, distance code, distance extra bits) into one `UInt64` and drains once.
The key lemma `flushAcc_or` shows that draining a prefix of the accumulator and
then OR-ing the next field above the resulting partial byte equals draining the
combined word — i.e. `flushAcc` composes, because it emits whole LSB-first
bytes and keeps the `<8` remainder. Composed four times this gives
`writeFour_eq`, a BitWriter *value* equality with the four-call chain, so every
downstream proof and the emitted bytes are unchanged. -/

/-- `(a ||| (b <<< total)) % 2^8 = a % 2^8` for `total ≥ 8`: the shifted field
    sits entirely at or above bit 8, so it leaves the low byte untouched. -/
private theorem or_shiftLeft_mod_two_pow_eight (a b total : Nat) (hge : 8 ≤ total) :
    (a ||| (b <<< total)) % 2 ^ 8 = a % 2 ^ 8 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases hj : j < 8
  · simp only [hj, decide_true, Bool.true_and, ge_iff_le,
      show ¬(total ≤ j) from by omega, decide_false, Bool.false_and, Bool.or_false]
  · simp only [hj, decide_false, Bool.false_and]

/-- `(a ||| (b <<< total)) / 2^8 = (a / 2^8) ||| (b <<< (total - 8))` for
    `total ≥ 8`: dividing the combined word by a byte shifts both summands down
    by 8 (the field's bits all sit at ≥ `total ≥ 8`). -/
private theorem or_shiftLeft_div_two_pow_eight (a b total : Nat) (hge : 8 ≤ total) :
    (a ||| (b <<< total)) / 2 ^ 8 = (a / 2 ^ 8) ||| (b <<< (total - 8)) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_div_two_pow, Nat.testBit_or, Nat.testBit_or, Nat.testBit_div_two_pow,
    Nat.testBit_shiftLeft, Nat.testBit_shiftLeft]
  simp only [ge_iff_le]
  congr 1
  by_cases hcase : total ≤ j + 8
  · rw [show (decide (total - 8 ≤ j)) = true from by simp only [decide_eq_true_eq]; omega,
      show (decide (total ≤ j + 8)) = true from by simp only [decide_eq_true_eq]; omega]
    simp only [Bool.true_and]
    congr 1
    omega
  · rw [show (decide (total - 8 ≤ j)) = false from by simp only [decide_eq_false_iff_not]; omega,
      show (decide (total ≤ j + 8)) = false from by simp only [decide_eq_false_iff_not]; omega]
    simp only [Bool.false_and]

/-- `(y <<< s).toNat = y.toNat <<< k` when `s` carries `k`, the low `p` bits of
    `y` are valid and `k + p ≤ 64`. Handles the `% 64` on the shift amount and
    the `% 2^64` on the result; the `k = 64` corner (forced `p = 0`, `y = 0`)
    falls out because the shifted value is `0` on both sides. -/
private theorem uint64_shiftLeft_toNat (y s : UInt64) (k p : Nat)
    (hs : s.toNat = k) (hy : y.toNat < 2 ^ p) (hkp : k + p ≤ 64) :
    (y <<< s).toNat = y.toNat <<< k := by
  rw [UInt64.toNat_shiftLeft, hs]
  by_cases hk : k < 64
  · rw [show k % 64 = k from by omega]
    apply Nat.mod_eq_of_lt
    rw [Nat.shiftLeft_eq]
    calc y.toNat * 2 ^ k
        < 2 ^ p * 2 ^ k := Nat.mul_lt_mul_of_pos_right hy (Nat.two_pow_pos _)
      _ = 2 ^ (p + k) := (Nat.pow_add 2 p k).symm
      _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) (by omega)
  · -- k = 64, so p = 0 and y = 0
    have hp0 : p = 0 := by omega
    have hy0 : y.toNat = 0 := by rw [hp0] at hy; omega
    rw [hy0]; simp only [Nat.zero_shiftLeft]

/-- `UInt64` OR-of-shift bound: `(x ||| (y <<< s)).toNat < 2^(k+p)` when the low
    `k` bits of `x` and low `p` bits of `y` are valid, the shift `s` is `k`, and
    the result fits in 64 bits. Bridges the `% 64`/`% 2^64` of UInt64 shifts to
    the clean Nat `or_shiftLeft_lt`. -/
private theorem uint64_or_shiftLeft_lt (x y s : UInt64) (k p : Nat)
    (hs : s.toNat = k) (hx : x.toNat < 2 ^ k) (hy : y.toNat < 2 ^ p) (hkp : k + p ≤ 64) :
    (x ||| (y <<< s)).toNat < 2 ^ (k + p) := by
  rw [UInt64.toNat_or, uint64_shiftLeft_toNat y s k p hs hy hkp]
  exact or_shiftLeft_lt x.toNat y.toNat k p hx hy

/-- Draining `acc` (its low `total` bits valid) and then OR-ing a further field
    `more` (its low `k` bits valid) above the resulting partial byte equals
    draining the single combined word `acc ||| (more <<< total)`. The shift
    amount `s` carries `total` as a `UInt64`. -/
private theorem flushAcc_or (data : ByteArray) (acc more : UInt64) (s : UInt64)
    (total k : Nat) (hs : s.toNat = total)
    (hacc : acc.toNat < 2 ^ total) (hmore : more.toNat < 2 ^ k)
    (hsum : total + k ≤ 64) :
    flushAcc data (acc ||| (more <<< s)) (total + k) =
      let bw := flushAcc data acc total
      flushAcc bw.data (bw.bitBuf.toUInt64 ||| (more <<< bw.bitCount.toUInt64))
        (bw.bitCount.toNat + k) := by
  induction total using Nat.strongRecOn generalizing data acc s with
  | ind total ih =>
    -- The combined word as a Nat (no wraparound: total + k ≤ 64).
    have hcomb_nat : (acc ||| (more <<< s)).toNat = acc.toNat ||| (more.toNat <<< total) := by
      rw [UInt64.toNat_or, uint64_shiftLeft_toNat more s total k hs hmore (by omega)]
    have hcomb_lt : (acc ||| (more <<< s)).toNat < 2 ^ (total + k) := by
      rw [hcomb_nat, Nat.add_comm total k]
      exact or_shiftLeft_lt acc.toNat more.toNat total k hacc hmore
    by_cases hge : total ≥ 8
    · -- Both the combined drain and the prefix drain push a byte; recurse.
      -- low byte unaffected by `more` (which sits at position `total ≥ 8`)
      have hlow : (acc ||| (more <<< s)).toUInt8 = acc.toUInt8 := by
        apply UInt8.toNat_inj.mp
        rw [UInt64.toNat_toUInt8, UInt64.toNat_toUInt8, hcomb_nat,
          show (2 ^ 8 : Nat) = 2 ^ 8 from rfl,
          or_shiftLeft_mod_two_pow_eight acc.toNat more.toNat total hge]
      have hsm : (s - 8).toNat = total - 8 := by
        rw [UInt64.toNat_sub_of_le, hs, show (8 : UInt64).toNat = 8 from by decide]
        rw [UInt64.le_iff_toNat_le, show (8 : UInt64).toNat = 8 from by decide, hs]; omega
      -- the shifted-down combined word still equals acc-shifted OR more-shifted
      have hshift : (acc ||| (more <<< s)) >>> 8 = (acc >>> 8) ||| (more <<< (s - 8)) := by
        apply UInt64.toNat_inj.mp
        -- LHS numerator
        rw [UInt64.toNat_shiftRight, hcomb_nat,
          show (8 : UInt64).toNat % 64 = 8 from by decide, Nat.shiftRight_eq_div_pow,
          or_shiftLeft_div_two_pow_eight acc.toNat more.toNat total hge]
        -- RHS numerator
        rw [UInt64.toNat_or, UInt64.toNat_shiftRight,
          show (8 : UInt64).toNat % 64 = 8 from by decide, Nat.shiftRight_eq_div_pow,
          uint64_shiftLeft_toNat more (s - 8) (total - 8) k hsm hmore (by omega)]
      have hacc' : (acc >>> 8).toNat < 2 ^ (total - 8) := by
        rw [UInt64.toNat_shiftRight, show (8 : UInt64).toNat % 64 = 8 from by decide,
          Nat.shiftRight_eq_div_pow]
        apply Nat.div_lt_of_lt_mul
        rw [← Nat.pow_add, show 8 + (total - 8) = total from by omega]; exact hacc
      -- reduce the prefix drain (RHS let) by one byte
      have hrhs : flushAcc data acc total
          = flushAcc (data.push acc.toUInt8) (acc >>> 8) (total - 8) := by
        conv_lhs => rw [flushAcc]
        rw [if_pos hge]
      -- reduce the combined drain (LHS) by one byte, then apply IH
      conv_lhs => rw [flushAcc]
      rw [if_pos (show total + k ≥ 8 from by omega), hlow, hshift, hrhs,
        show total + k - 8 = (total - 8) + k from by omega]
      exact ih (total - 8) (by omega) (data.push acc.toUInt8) (acc >>> 8) (s - 8) hsm
        hacc' hmore (by omega)
    · -- prefix drain finishes: flushAcc data acc total = ⟨data, acc.toUInt8, total⟩
      have htu : total.toUInt8.toNat = total := by
        simp only [Nat.toUInt8, UInt8.toNat_ofNat']
        rw [show (2 : Nat) ^ 8 = 256 from rfl]; omega
      have hau : acc.toUInt8.toNat = acc.toNat := by
        rw [UInt64.toNat_toUInt8]
        exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hacc
          (Nat.pow_le_pow_right (by omega) (by omega)))
      have hrhs : flushAcc data acc total = ⟨data, acc.toUInt8, total.toUInt8⟩ := by
        conv_lhs => rw [flushAcc]
        rw [if_neg hge]
      rw [hrhs]
      -- RHS now: flushAcc data (acc.toUInt8.toUInt64 ||| (more <<< total.toUInt8.toUInt64)) (total + k)
      show flushAcc data (acc ||| (more <<< s)) (total + k)
        = flushAcc data (acc.toUInt8.toUInt64 |||
            (more <<< total.toUInt8.toUInt64)) (total.toUInt8.toNat + k)
      -- the two accumulators and the two counts agree
      have hcount : total.toUInt8.toNat + k = total + k := by rw [htu]
      have hacc_eq : (acc.toUInt8.toUInt64 ||| (more <<< total.toUInt8.toUInt64))
          = (acc ||| (more <<< s)) := by
        apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_or, UInt64.toNat_or, UInt64.toNat_shiftLeft,
          UInt64.toNat_shiftLeft, UInt8.toNat_toUInt64, htu, hs,
          show acc.toUInt8.toUInt64.toNat = acc.toNat from by rw [UInt64.toNat_toUInt8, hau]]
      rw [hcount, hacc_eq]

/-- The reversed Huffman code `(reverse16 c).toUInt64 >>> (16 - len)` has its
    low `len` bits valid. -/
private theorem rev_lt (c : UInt16) (len : UInt8) (hlen : len.toNat ≤ 15) :
    ((reverse16 c).toUInt64 >>> (16 - len.toUInt64)).toNat < 2 ^ len.toNat := by
  have hle : len.toUInt64 ≤ (16 : UInt64) := by
    rw [UInt64.le_iff_toNat_le, UInt8.toNat_toUInt64]; exact Nat.le_trans hlen (by decide)
  have hsub : (16 - len.toUInt64).toNat = 16 - len.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ hle, UInt8.toNat_toUInt64,
      show (16 : UInt64).toNat = 16 from by decide]
  rw [UInt64.toNat_shiftRight, UInt16.toNat_toUInt64, hsub,
    show (16 - len.toNat) % 64 = 16 - len.toNat from by omega, Nat.shiftRight_eq_div_pow]
  apply Nat.div_lt_of_lt_mul
  rw [← Nat.pow_add, show (16 - len.toNat) + len.toNat = 16 from by omega]
  have := (reverse16 c).toNat_lt; simpa only [UInt16.size] using this

/-- The masked extra-bits field `v % (1 <<< n)` has its low `n` bits valid. -/
private theorem mask_lt (v : UInt32) (n : Nat) (hn : n ≤ 25) :
    (v.toUInt64 % (1 <<< n.toUInt64)).toNat < 2 ^ n := by
  have hnlt : n < 2 ^ 64 := Nat.lt_of_le_of_lt hn (by decide)
  have hn2lt : (2 : Nat) ^ n < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by omega) hn)
      (Nat.pow_lt_pow_right (by omega) (by omega))
  have hn64 : n.toUInt64.toNat % 64 = n := by
    have he : n.toUInt64.toNat = n := by
      simp only [Nat.toUInt64, UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt hnlt
    rw [he]; omega
  rw [UInt64.toNat_mod, UInt64.toNat_shiftLeft, show (1 : UInt64).toNat = 1 from rfl, hn64,
    Nat.one_shiftLeft, Nat.mod_eq_of_lt hn2lt]
  exact Nat.mod_lt _ (Nat.two_pow_pos _)

/-- `(bw.bitCount.toUInt64 + δ).toNat = bw.bitCount.toNat + δ.toNat` when both fit
    in a byte's worth of width — used to align `writeFour`'s wide-shift positions
    with the per-field `flushAcc_or` shift amounts. -/
private theorem addUInt64_toNat_of_lt (a b : UInt64) (h : a.toNat + b.toNat < 2 ^ 64) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt h

/-- **Route A core result.** `writeFour` packs the four reference-token fields
    into one wide word and drains once; this equals the four-call
    `writeHuffCode`/`writeBits` chain *as BitWriter values*, so the fused emit
    is byte-identical and every downstream `toBits`/`wf` proof is unchanged.
    The width bounds are RFC 1951: Huffman code lengths `l1, l3 ≤ 15`, length
    extra `n2 ≤ 5`, distance extra `n4 ≤ 13`. -/
theorem writeFour_eq (bw : BitWriter) (c1 : UInt16) (l1 : UInt8) (n2 : Nat) (v2 : UInt32)
    (c3 : UInt16) (l3 : UInt8) (n4 : Nat) (v4 : UInt32)
    (hwf : bw.wf) (hl1 : l1.toNat ≤ 15) (hn2 : n2 ≤ 5) (hl3 : l3.toNat ≤ 15) (hn4 : n4 ≤ 13) :
    bw.writeFour c1 l1 n2 v2 c3 l3 n4 v4 =
      (((bw.writeHuffCode c1 l1).writeBits n2 v2).writeHuffCode c3 l3).writeBits n4 v4 := by
  obtain ⟨hbc, hbuf⟩ := hwf
  -- abbreviations for the four packed fields (LSB extra bits / reversed codes)
  let bc : UInt64 := bw.bitCount.toUInt64
  let rev1 : UInt64 := (reverse16 c1).toUInt64 >>> (16 - l1.toUInt64)
  let mask2 : UInt64 := v2.toUInt64 % (1 <<< n2.toUInt64)
  let rev3 : UInt64 := (reverse16 c3).toUInt64 >>> (16 - l3.toUInt64)
  let mask4 : UInt64 := v4.toUInt64 % (1 <<< n4.toUInt64)
  let A1 : UInt64 := bw.bitBuf.toUInt64 ||| (rev1 <<< bc)
  let A2 : UInt64 := A1 ||| (mask2 <<< (bc + l1.toUInt64))
  let A3 : UInt64 := A2 ||| (rev3 <<< (bc + l1.toUInt64 + n2.toUInt64))
  -- field width facts
  have hrev1 : rev1.toNat < 2 ^ l1.toNat := rev_lt c1 l1 hl1
  have hmask2v : mask2.toNat < 2 ^ n2 := mask_lt v2 n2 (by omega)
  have hrev3 : rev3.toNat < 2 ^ l3.toNat := rev_lt c3 l3 hl3
  have hmask4v : mask4.toNat < 2 ^ n4 := mask_lt v4 n4 (by omega)
  have hbcn : bc.toNat = bw.bitCount.toNat := UInt8.toNat_toUInt64 _
  -- shift positions as Nats (no UInt64 wraparound, all ≤ 55)
  have hl1n : l1.toUInt64.toNat = l1.toNat := UInt8.toNat_toUInt64 l1
  have hl3n : l3.toUInt64.toNat = l3.toNat := UInt8.toNat_toUInt64 l3
  have hn2n : n2.toUInt64.toNat = n2 := by
    simp only [Nat.toUInt64, UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  have hp1 : (bc + l1.toUInt64).toNat = bw.bitCount.toNat + l1.toNat := by
    rw [addUInt64_toNat_of_lt _ _ (by rw [hbcn, hl1n]; omega), hbcn, hl1n]
  have hp2 : (bc + l1.toUInt64 + n2.toUInt64).toNat = bw.bitCount.toNat + l1.toNat + n2 := by
    rw [addUInt64_toNat_of_lt _ _ (by rw [hp1, hn2n]; omega), hp1, hn2n]
  have hp3 : (bc + l1.toUInt64 + n2.toUInt64 + l3.toUInt64).toNat
      = bw.bitCount.toNat + l1.toNat + n2 + l3.toNat := by
    rw [addUInt64_toNat_of_lt _ _ (by rw [hp2, hl3n]; omega), hp2, hl3n]
  -- bitBuf fits in `bitCount` bits (from `wf`)
  have hbufN : bw.bitBuf.toUInt64.toNat < 2 ^ bw.bitCount.toNat := by
    rwa [UInt8.toNat_toUInt64]
  -- accumulator bounds (partial sums of width), via the UInt64 OR-shift bound
  have hA1lt : A1.toNat < 2 ^ (bw.bitCount.toNat + l1.toNat) :=
    uint64_or_shiftLeft_lt _ rev1 bc bw.bitCount.toNat l1.toNat hbcn hbufN hrev1 (by omega)
  have hA2lt : A2.toNat < 2 ^ (bw.bitCount.toNat + l1.toNat + n2) :=
    uint64_or_shiftLeft_lt _ mask2 (bc + l1.toUInt64) (bw.bitCount.toNat + l1.toNat) n2
      hp1 hA1lt hmask2v (by omega)
  have hA3lt : A3.toNat < 2 ^ (bw.bitCount.toNat + l1.toNat + n2 + l3.toNat) :=
    uint64_or_shiftLeft_lt _ rev3 (bc + l1.toUInt64 + n2.toUInt64)
      (bw.bitCount.toNat + l1.toNat + n2) l3.toNat hp2 hA2lt hrev3 (by omega)
  -- `writeHuffCode c1 l1 = flushAcc bw.data A1 (bc+l1)` (definitional)
  have hstep1 : bw.writeHuffCode c1 l1 = flushAcc bw.data A1 (bw.bitCount.toNat + l1.toNat) := rfl
  -- peel field 2 via flushAcc_or
  have hor2 := flushAcc_or bw.data A1 mask2 (bc + l1.toUInt64)
    (bw.bitCount.toNat + l1.toNat) n2 hp1 hA1lt
    (Nat.lt_of_le_of_lt (Nat.mod_le _ _) hmask2v) (by omega)
  have hstep2 : (bw.writeHuffCode c1 l1).writeBits n2 v2
      = flushAcc bw.data A2 (bw.bitCount.toNat + l1.toNat + n2) := by
    show (flushAcc bw.data A1 (bw.bitCount.toNat + l1.toNat)).writeBits n2 v2 = _
    rw [writeBits]; exact (hor2).symm
  -- peel field 3 via flushAcc_or
  have hor3 := flushAcc_or bw.data A2 rev3 (bc + l1.toUInt64 + n2.toUInt64)
    (bw.bitCount.toNat + l1.toNat + n2) l3.toNat hp2 hA2lt hrev3 (by omega)
  have hstep3 : (((bw.writeHuffCode c1 l1).writeBits n2 v2).writeHuffCode c3 l3)
      = flushAcc bw.data A3 (bw.bitCount.toNat + l1.toNat + n2 + l3.toNat) := by
    rw [hstep2]
    show (flushAcc bw.data A2 (bw.bitCount.toNat + l1.toNat + n2)).writeHuffCode c3 l3 = _
    rw [writeHuffCode]; exact (hor3).symm
  -- peel field 4 via flushAcc_or
  have hor4 := flushAcc_or bw.data A3 mask4 (bc + l1.toUInt64 + n2.toUInt64 + l3.toUInt64)
    (bw.bitCount.toNat + l1.toNat + n2 + l3.toNat) n4 hp3 hA3lt
    (Nat.lt_of_le_of_lt (Nat.mod_le _ _) hmask4v) (by omega)
  have hstep4 : ((((bw.writeHuffCode c1 l1).writeBits n2 v2).writeHuffCode c3 l3).writeBits n4 v4)
      = flushAcc bw.data (A3 ||| (mask4 <<< (bc + l1.toUInt64 + n2.toUInt64 + l3.toUInt64)))
          (bw.bitCount.toNat + l1.toNat + n2 + l3.toNat + n4) := by
    rw [hstep3]
    show (flushAcc bw.data A3 (bw.bitCount.toNat + l1.toNat + n2 + l3.toNat)).writeBits n4 v4 = _
    rw [writeBits]; exact (hor4).symm
  -- writeFour's accumulator is exactly `A3 ||| (mask4 << ...)`, same total width
  rw [hstep4]
  rfl

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
