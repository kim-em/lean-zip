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
  constructor <;> simp [empty]

theorem empty_toBits : empty.toBits = [] := by
  simp [toBits, empty]

/-! ## Helper lemmas -/

private theorem flatMap_byteToBits_push (data : ByteArray) (b : UInt8) :
    (data.push b).data.toList.flatMap Deflate.Spec.bytesToBits.byteToBits =
    data.data.toList.flatMap Deflate.Spec.bytesToBits.byteToBits ++
    Deflate.Spec.bytesToBits.byteToBits b := by
  simp [ByteArray.push, Array.toList_push]

/-- byteToBits splits at bit boundary k when upper bits are zero. -/
private theorem byteToBits_split (b : UInt8) (k : Nat) (hk : k ≤ 8)
    (hb : b.toNat < 2 ^ k) :
    Deflate.Spec.bytesToBits.byteToBits b =
    (List.range k).map (fun i => b.toNat.testBit i) ++
    List.replicate (8 - k) false := by
  simp only [Deflate.Spec.bytesToBits.byteToBits]
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp only [List.length_ofFn] at h1
    simp only [List.getElem_ofFn]
    by_cases hik : i < k
    · rw [List.getElem_append_left (by simp; omega)]
      simp
    · rw [List.getElem_append_right (by simp; omega)]
      simp only [List.length_map, List.length_range, List.getElem_replicate]
      exact Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by omega) (by omega)))

/-! ## Nat-level bit manipulation -/

/-- testBit below the shift position sees only the original value. -/
private theorem testBit_or_shiftLeft_below (a b k j : Nat) (hj : j < k) :
    (a ||| (b <<< k)).testBit j = a.testBit j := by
  rw [Nat.testBit_or, Nat.testBit_shiftLeft]
  simp [show ¬(k ≤ j) from by omega]

/-- testBit at the shift position sees the shifted bit. -/
private theorem testBit_or_shiftLeft_at (a b k : Nat) (ha : a < 2 ^ k) :
    (a ||| (b <<< k)).testBit k = b.testBit 0 := by
  rw [Nat.testBit_or, Nat.testBit_lt_two_pow ha, Bool.false_or,
      Nat.testBit_shiftLeft]
  simp

/-- testBit 0 of a value ≤ 1 equals decide (val = 1). -/
private theorem testBit_zero_of_le_one (b : Nat) (hb : b ≤ 1) :
    b.testBit 0 = decide (b = 1) := by
  cases b with
  | zero => simp [Nat.testBit]
  | succ n =>
    have : n = 0 := by omega
    subst this; simp [Nat.testBit]

/-- For small OR-shift on UInt8, toNat distributes. Key bridging lemma from
    UInt8 bit operations to Nat-level reasoning. -/
private theorem uint8_or_shiftLeft_toNat (buf bit k : UInt8)
    (hk : k.toNat < 8) (hbit : bit.toNat ≤ 1) :
    (buf ||| (bit <<< k)).toNat = buf.toNat ||| (bit.toNat <<< k.toNat) := by
  simp only [UInt8.toNat_or]
  congr 1
  show (bit <<< k).toNat = bit.toNat <<< k.toNat
  simp only [UInt8.toNat_shiftLeft]
  rw [Nat.mod_eq_of_lt hk]
  apply Nat.mod_eq_of_lt
  rw [Nat.shiftLeft_eq]
  calc bit.toNat * 2 ^ k.toNat
      ≤ 1 * 2 ^ k.toNat := Nat.mul_le_mul_right _ hbit
    _ = 2 ^ k.toNat := Nat.one_mul _
    _ ≤ 2 ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
    _ < 2 ^ 8 := by omega

/-- OR of a small value with a shifted single bit is bounded. Used by both addBit_toBits and addBit_wf. -/
private theorem or_shiftLeft_lt_two_pow (buf bit k : Nat)
    (hbuf : buf < 2 ^ k) (hbit : bit ≤ 1) :
    buf ||| (bit <<< k) < 2 ^ (k + 1) := by
  have hshift : bit <<< k < 2 ^ (k + 1) := by
    rw [Nat.shiftLeft_eq]
    calc bit * 2 ^ k ≤ 1 * 2 ^ k := Nat.mul_le_mul_right _ hbit
      _ = 2 ^ k := Nat.one_mul _
      _ < 2 ^ (k + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
  exact Nat.or_lt_two_pow
    (Nat.lt_of_lt_of_le hbuf (Nat.pow_le_pow_right (by omega) (by omega)))
    hshift

/-! ## Core addBit lemma -/

/-- Range map extension: extending range by 1 where the new element equals
    testBit_or_shiftLeft_at. -/
private theorem range_map_extend (buf : Nat) (bit : Nat) (k : Nat)
    (hbuf : buf < 2 ^ k) (_hbit : bit ≤ 1) :
    (List.range (k + 1)).map (fun i => (buf ||| (bit <<< k)).testBit i) =
    (List.range k).map (fun i => buf.testBit i) ++ [bit.testBit 0] := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    by_cases hik : i < k
    · rw [List.getElem_append_left (by simp; omega)]
      simp only [List.getElem_map, List.getElem_range]
      exact testBit_or_shiftLeft_below buf bit k i hik
    · have hieq : i = k := by omega
      subst hieq
      rw [List.getElem_append_right (by simp)]
      simp only [List.getElem_map, List.getElem_range, List.length_map,
        List.length_range, Nat.sub_self, List.getElem_cons_zero]
      exact testBit_or_shiftLeft_at buf bit i hbuf

/-- Adding one bit to a well-formed BitWriter extends toBits by that bit. -/
private theorem addBit_toBits (bw : BitWriter) (bit : UInt8) (bval : Bool)
    (hwf : bw.wf) (hbit_le : bit.toNat ≤ 1)
    (hbit_val : bval = decide (bit.toNat = 1)) :
    let newBuf := bw.bitBuf ||| (bit <<< bw.bitCount)
    let k := bw.bitCount.toNat
    (if k + 1 ≥ 8 then
      (⟨bw.data.push newBuf, (0 : UInt8), (0 : UInt8)⟩ : BitWriter)
    else
      (⟨bw.data, newBuf, bw.bitCount + 1⟩ : BitWriter)).toBits =
    bw.toBits ++ [bval] := by
  obtain ⟨hbc_lt, hbuf_lt⟩ := hwf
  simp only
  have hbridge := uint8_or_shiftLeft_toNat bw.bitBuf bit bw.bitCount hbc_lt hbit_le
  by_cases hflush : bw.bitCount.toNat + 1 ≥ 8
  · -- Case: k + 1 ≥ 8, i.e. k = 7 (flush)
    have hk7 : bw.bitCount.toNat = 7 := by omega
    rw [if_pos (show bw.bitCount.toNat + 1 ≥ 8 from hflush)]
    -- Simplify toBits of the flushed writer
    have htb : (⟨bw.data.push (bw.bitBuf ||| (bit <<< bw.bitCount)),
        (0 : UInt8), (0 : UInt8)⟩ : BitWriter).toBits =
        (bw.data.push (bw.bitBuf ||| (bit <<< bw.bitCount))).data.toList.flatMap
          Deflate.Spec.bytesToBits.byteToBits := by
      simp [toBits]
    rw [htb, flatMap_byteToBits_push]
    simp only [toBits, List.append_assoc]
    congr 1
    -- byteToBits (newBuf) = (range k).map (testBit bitBuf) ++ [bval]
    have hk8 : 8 - (bw.bitCount.toNat + 1) = 0 := by omega
    rw [byteToBits_split (bw.bitBuf ||| (bit <<< bw.bitCount)) (bw.bitCount.toNat + 1) (by omega)]
    · -- replicate 0 false = []
      rw [hk8, List.replicate_zero, List.append_nil]
      rw [hbridge]
      rw [range_map_extend bw.bitBuf.toNat bit.toNat bw.bitCount.toNat hbuf_lt hbit_le]
      congr 1; congr 1
      rw [hbit_val, testBit_zero_of_le_one bit.toNat hbit_le]
    · rw [hbridge]; exact or_shiftLeft_lt_two_pow _ _ _ hbuf_lt hbit_le
  · -- Case: k + 1 < 8 (no flush)
    rw [if_neg (show ¬(bw.bitCount.toNat + 1 ≥ 8) from hflush)]
    simp only [toBits]
    -- bitCount of new writer = bw.bitCount + 1
    have hbc_add : (bw.bitCount + 1).toNat = bw.bitCount.toNat + 1 := by
      show (bw.bitCount.toNat + 1) % 256 = bw.bitCount.toNat + 1
      apply Nat.mod_eq_of_lt; omega
    rw [hbc_add]
    simp only [List.append_assoc]
    congr 1
    rw [hbridge]
    rw [range_map_extend bw.bitBuf.toNat bit.toNat bw.bitCount.toNat hbuf_lt hbit_le]
    congr 1; congr 1
    rw [hbit_val, testBit_zero_of_le_one bit.toNat hbit_le]

/-- Adding one bit preserves well-formedness. -/
private theorem addBit_wf (bw : BitWriter) (bit : UInt8)
    (hwf : bw.wf) (hbit_le : bit.toNat ≤ 1) :
    let newBuf := bw.bitBuf ||| (bit <<< bw.bitCount)
    let k := bw.bitCount.toNat
    (if k + 1 ≥ 8 then
      (⟨bw.data.push newBuf, (0 : UInt8), (0 : UInt8)⟩ : BitWriter)
    else
      (⟨bw.data, newBuf, bw.bitCount + 1⟩ : BitWriter)).wf := by
  obtain ⟨hbc_lt, hbuf_lt⟩ := hwf
  simp only
  have hbridge := uint8_or_shiftLeft_toNat bw.bitBuf bit bw.bitCount hbc_lt hbit_le
  by_cases hflush : bw.bitCount.toNat + 1 ≥ 8
  · -- Flush case: new BitWriter is ⟨_, 0, 0⟩, same as empty_wf
    rw [if_pos (show bw.bitCount.toNat + 1 ≥ 8 from hflush)]
    show (0 : UInt8).toNat < 8 ∧ (0 : UInt8).toNat < 2 ^ (0 : UInt8).toNat
    simp
  · -- No flush: bitCount goes to k+1, newBuf < 2^(k+1)
    rw [if_neg (show ¬(bw.bitCount.toNat + 1 ≥ 8) from hflush)]
    constructor
    · -- (bw.bitCount + 1).toNat < 8
      show (bw.bitCount.toNat + 1) % 256 < 8
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    · show (bw.bitBuf ||| bit <<< bw.bitCount).toNat <
          2 ^ ((bw.bitCount.toNat + 1) % 256)
      rw [Nat.mod_eq_of_lt (by omega), hbridge]
      exact or_shiftLeft_lt_two_pow _ _ _ hbuf_lt hbit_le

/-- Extracting bit k from a UInt16 code: ((code >>> k) &&& 1).toUInt8 has toNat ≤ 1
    and equals testBit. -/
private theorem uint16_extract_bit (code : UInt16) (k : Nat) (hk : k < 16) :
    let bit := ((code >>> k.toUInt16) &&& 1).toUInt8
    bit.toNat ≤ 1 ∧ (decide (bit.toNat = 1) = code.toNat.testBit k) := by
  simp only
  have hand_le : (code >>> k.toUInt16).toNat &&& 1 ≤ 1 := Nat.and_le_right
  constructor
  · show (((code >>> k.toUInt16) &&& 1).toUInt8).toNat ≤ 1
    simp only [UInt16.toNat_toUInt8, UInt16.toNat_and, UInt16.toNat_one]
    rw [Nat.mod_eq_of_lt (by omega)]; exact hand_le
  · show decide ((((code >>> k.toUInt16) &&& 1).toUInt8).toNat = 1) = code.toNat.testBit k
    simp only [UInt16.toNat_toUInt8, UInt16.toNat_and, UInt16.toNat_one]
    rw [Nat.mod_eq_of_lt (by omega)]
    simp only [UInt16.toNat_shiftRight]
    rw [show k.toUInt16.toNat % 16 = k from by
      show k % UInt16.size % 16 = k
      simp only [UInt16.size]; omega]
    simp only [Nat.testBit]
    rw [Nat.and_comm, Nat.one_and_eq_mod_two]
    -- Goal: decide (x % 2 = 1) = (x % 2 != 0)
    cases h : _ % 2 with
    | zero => simp
    | succ n =>
      have : n = 0 := by omega
      subst this; simp

/-- Extracting bit i from a UInt32 value: ((val >>> i) &&& 1).toUInt8 has toNat ≤ 1
    and equals testBit. -/
private theorem uint32_extract_bit (val : UInt32) (i : Nat) (hi : i ≤ 25) :
    let bit := ((val >>> i.toUInt32) &&& 1).toUInt8
    bit.toNat ≤ 1 ∧ (decide (bit.toNat = 1) = val.toNat.testBit i) := by
  simp only
  have hand_le : (val >>> i.toUInt32).toNat &&& 1 ≤ 1 := Nat.and_le_right
  constructor
  · show (((val >>> i.toUInt32) &&& 1).toUInt8).toNat ≤ 1
    simp only [UInt32.toNat_toUInt8, UInt32.toNat_and, UInt32.toNat_one]
    rw [Nat.mod_eq_of_lt (by omega)]; exact hand_le
  · show decide ((((val >>> i.toUInt32) &&& 1).toUInt8).toNat = 1) = val.toNat.testBit i
    simp only [UInt32.toNat_toUInt8, UInt32.toNat_and, UInt32.toNat_one]
    rw [Nat.mod_eq_of_lt (by omega)]
    simp only [UInt32.toNat_shiftRight]
    rw [show i.toUInt32.toNat % 32 = i from by
      show i % UInt32.size % 32 = i
      simp only [UInt32.size]; omega]
    simp only [Nat.testBit]
    rw [Nat.and_comm, Nat.one_and_eq_mod_two]
    -- Goal: decide (x % 2 = 1) = (x % 2 != 0)
    cases h : _ % 2 with
    | zero => simp
    | succ n =>
      have : n = 0 := by omega
      subst this; simp

/-! ## writeHuffCode correspondence -/

private theorem writeHuffCode_go_spec (bw : BitWriter) (n : Nat) (code : UInt16)
    (hwf : bw.wf) (hn : n ≤ 15) :
    (writeHuffCode.go bw n code).toBits =
    bw.toBits ++ Huffman.Spec.natToBits code.toNat n ∧
    (writeHuffCode.go bw n code).wf := by
  induction n generalizing bw with
  | zero =>
    simp [writeHuffCode.go, Huffman.Spec.natToBits, hwf]
  | succ k ih =>
    simp only [writeHuffCode.go, Huffman.Spec.natToBits]
    obtain ⟨hbit_le, hbit_val⟩ := uint16_extract_bit code k (by omega)
    have hab := addBit_toBits bw _ (code.toNat.testBit k) hwf hbit_le hbit_val.symm
    have hawf := addBit_wf bw _ hwf hbit_le
    simp only at hab hawf
    by_cases hflush : bw.bitCount.toNat + 1 ≥ 8 <;>
    · first | rw [if_pos hflush] at hab hawf ⊢ | rw [if_neg hflush] at hab hawf ⊢
      have hih := ih _ hawf (by omega)
      exact ⟨by rw [hih.1, hab, List.append_assoc]; rfl, hih.2⟩

theorem writeHuffCode_toBits (bw : BitWriter) (code : UInt16) (len : UInt8)
    (hwf : bw.wf) (hlen : len.toNat ≤ 15) :
    (bw.writeHuffCode code len).toBits =
    bw.toBits ++ Huffman.Spec.natToBits code.toNat len.toNat := by
  exact (writeHuffCode_go_spec bw len.toNat code hwf hlen).1

theorem writeHuffCode_wf (bw : BitWriter) (code : UInt16) (len : UInt8)
    (hwf : bw.wf) (hlen : len.toNat ≤ 15) :
    (bw.writeHuffCode code len).wf := by
  exact (writeHuffCode_go_spec bw len.toNat code hwf hlen).2

/-! ## writeBits correspondence -/

/-- UInt8 flush condition ↔ Nat condition, for well-formed bitCount. -/
private theorem flush_iff_nat (bc : UInt8) (hbc : bc.toNat < 8) :
    (bc + 1 ≥ (8 : UInt8)) ↔ (bc.toNat + 1 ≥ 8) := by
  constructor
  · intro h
    have := UInt8.le_iff_toNat_le.mp h
    simp only [UInt8.toNat_ofNat, UInt8.toNat_add] at this
    omega
  · intro h
    apply UInt8.le_iff_toNat_le.mpr
    simp only [UInt8.toNat_ofNat, UInt8.toNat_add]
    omega

private theorem writeBits_go_spec (bw : BitWriter) (i n : Nat) (val : UInt32)
    (hwf : bw.wf) (hi : i ≤ n) (hn : n ≤ 25) :
    (writeBits.go bw i n val).toBits =
    bw.toBits ++ Deflate.Spec.writeBitsLSB (n - i) (val.toNat / 2 ^ i) ∧
    (writeBits.go bw i n val).wf := by
  -- Induction on the measure n - i
  suffices ∀ k, k = n - i → (writeBits.go bw i n val).toBits =
      bw.toBits ++ Deflate.Spec.writeBitsLSB k (val.toNat / 2 ^ i) ∧
      (writeBits.go bw i n val).wf by exact this _ rfl
  intro k
  induction k generalizing bw i with
  | zero =>
    intro heq
    have hieq : i = n := by omega
    subst hieq
    simp [writeBits.go, Deflate.Spec.writeBitsLSB, hwf]
  | succ m ihm =>
    intro heq
    have hin : i < n := by omega
    rw [writeBits.go, if_neg (show ¬(i ≥ n) from by omega)]
    obtain ⟨hbit_le, hbit_val⟩ := uint32_extract_bit val i (by omega)
    have hab := addBit_toBits bw _ (val.toNat.testBit i) hwf hbit_le hbit_val.symm
    have hawf := addBit_wf bw _ hwf hbit_le
    simp only at hab hawf
    -- The goal's if uses UInt8 condition; hab/hawf use Nat condition.
    -- Bridge via flush_iff_nat, then the two branches are identical.
    have hbc_lt := hwf.1
    have hhead : (val.toNat / 2 ^ i % 2 == 1) = val.toNat.testBit i := by
      simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.one_and_eq_mod_two]
      cases h : val.toNat / 2 ^ i % 2 with
      | zero => simp
      | succ j =>
        have : j = 0 := by omega
        subst this; simp
    have htail : val.toNat / 2 ^ i / 2 = val.toNat / 2 ^ (i + 1) := by
      rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
    by_cases hflush_nat : bw.bitCount.toNat + 1 ≥ 8 <;> {
      first | rw [if_pos hflush_nat] at hab hawf | rw [if_neg hflush_nat] at hab hawf
      first
        | rw [if_pos ((flush_iff_nat bw.bitCount hbc_lt).mpr hflush_nat)]
        | rw [if_neg (mt (flush_iff_nat bw.bitCount hbc_lt).mp hflush_nat)]
      simp only [Deflate.Spec.writeBitsLSB]; rw [hhead, htail]
      have hih := ihm _ (i + 1) hawf (by omega) (by omega)
      exact ⟨by rw [hih.1, hab, List.append_assoc]; rfl, hih.2⟩ }

theorem writeBits_toBits (bw : BitWriter) (n : Nat) (val : UInt32)
    (hwf : bw.wf) (hn : n ≤ 25) :
    (bw.writeBits n val).toBits =
    bw.toBits ++ Deflate.Spec.writeBitsLSB n val.toNat := by
  have h := (writeBits_go_spec bw 0 n val hwf (by omega) hn).1
  simp at h; exact h

theorem writeBits_wf (bw : BitWriter) (n : Nat) (val : UInt32)
    (hwf : bw.wf) (hn : n ≤ 25) :
    (bw.writeBits n val).wf := by
  exact (writeBits_go_spec bw 0 n val hwf (by omega) hn).2

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
    simp only [hbc0, toBits, Deflate.Spec.bytesToBits]; simp
  · -- bitCount > 0: flush pushes bitBuf
    have hcond : bw.bitCount > 0 := by show 0 < bw.bitCount.toNat; omega
    rw [if_pos hcond]
    simp only [Deflate.Spec.bytesToBits]
    rw [flatMap_byteToBits_push]
    simp only [toBits, List.append_assoc]
    congr 1
    rw [byteToBits_split bw.bitBuf bw.bitCount.toNat (by omega) hbuf_lt]
    congr 1
    have hbc_pos : bw.bitCount.toNat > 0 := by omega
    rw [Nat.mod_eq_of_lt hbc_lt,
        Nat.mod_eq_of_lt (show 8 - bw.bitCount.toNat < 8 from by omega)]

end Zip.Native.BitWriter
