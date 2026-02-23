import Zip.Spec.Deflate
import Zip.Native.Inflate
import ZipForStd.Nat

/-!
# Bitstream Correspondence

Establishes the correspondence between `BitReader` operations (byte-level,
imperative) and spec-level bit lists (`bytesToBits` + `readBitsLSB`).

A `BitReader` at position `(pos, bitOff)` in a `ByteArray` corresponds
to the bit list `(bytesToBits data).drop (pos * 8 + bitOff)`.
-/

/-- The spec-level bit list corresponding to a `BitReader`'s current position. -/
def Zip.Native.BitReader.toBits (br : Zip.Native.BitReader) : List Bool :=
  (Deflate.Spec.bytesToBits br.data).drop (br.pos * 8 + br.bitOff)

namespace Deflate.Correctness

/-! ### Helper lemmas for flatMap with uniform-length functions -/

/-- Dropping `n * k` elements from a flatMap with uniform-length-`k` outputs
    skips exactly `n` segments. -/
private theorem flatMap_drop_mul {α β : Type} (l : List α) (f : α → List β)
    (k n : Nat) (hk : ∀ a, (f a).length = k) :
    (l.flatMap f).drop (n * k) = (l.drop n).flatMap f := by
  induction n generalizing l with
  | zero => simp
  | succ m ih =>
    cases l with
    | nil => simp
    | cons a rest =>
      simp only [List.flatMap_cons, List.drop_succ_cons]
      have hk_eq : (m + 1) * k = (f a).length + m * k := by
        rw [Nat.succ_mul, hk a, Nat.add_comm]
      rw [hk_eq, ← List.drop_drop, List.drop_left]
      exact ih rest

/-- Dropping within the first segment of a flatMap. -/
private theorem flatMap_cons_drop {α β : Type} (a : α) (rest : List α)
    (f : α → List β) (off : Nat) (hoff : off ≤ (f a).length) :
    ((a :: rest).flatMap f).drop off = (f a).drop off ++ rest.flatMap f :=
  List.drop_append_of_le_length hoff

/-- Dropping `off` elements from `List.ofFn (n := n) f` gives a list
    headed by `f ⟨off, _⟩` when `off < n`. -/
private theorem ofFn_drop_head {n : Nat} {f : Fin n → β} {off : Nat}
    (hoff : off < n) :
    ∃ rest, (List.ofFn f).drop off = f ⟨off, hoff⟩ :: rest := by
  have hlen : off < (List.ofFn f).length := by simp; exact hoff
  rw [List.drop_eq_getElem_cons hlen, List.getElem_ofFn]
  exact ⟨_, rfl⟩

/-- `byteToBits` dropped by `off < 8` starts with `testBit off`. -/
private theorem byteToBits_drop_head (b : UInt8) (off : Nat) (hoff : off < 8) :
    ∃ rest, (Deflate.Spec.bytesToBits.byteToBits b).drop off =
      b.toNat.testBit off :: rest := by
  exact ofFn_drop_head hoff

/-- The key structural lemma: `bytesToBits data` dropped by `pos * 8 + off`
    starts with `data[pos].toNat.testBit off`. -/
private theorem bytesToBits_drop_testBit (data : ByteArray) (pos off : Nat)
    (hpos : pos < data.size) (hoff : off < 8) :
    ∃ rest, (Deflate.Spec.bytesToBits data).drop (pos * 8 + off) =
      data[pos].toNat.testBit off :: rest := by
  simp only [Deflate.Spec.bytesToBits]
  -- Step 1: split drop (pos * 8 + off) into drop off ∘ drop (pos * 8)
  rw [← List.drop_drop]
  -- Step 2: drop (pos * 8) skips pos complete 8-bit segments
  rw [flatMap_drop_mul data.data.toList _ 8 pos
    Deflate.Spec.bytesToBits.byteToBits_length]
  -- Step 3: data.data.toList.drop pos = data[pos] :: tail
  have hlen : pos < data.data.toList.length := by
    rw [Array.length_toList]; exact hpos
  rw [List.drop_eq_getElem_cons hlen]
  -- Step 4: drop off within first segment
  rw [flatMap_cons_drop _ _ _ off
    (by rw [Deflate.Spec.bytesToBits.byteToBits_length]; omega)]
  -- Step 5: head of (byteToBits data[pos]).drop off is testBit off
  have heq : data.data.toList[pos] = data[pos] := by
    simp [Array.getElem_toList]; rfl
  obtain ⟨tail, htail⟩ := byteToBits_drop_head (data.data.toList[pos]) off hoff
  rw [htail, heq]; exact ⟨_, rfl⟩

/-! ### Bit-value correspondence -/

private theorem shift_and_one_eq_testBit (n i : Nat) :
    (n >>> i) &&& 1 = if n.testBit i then 1 else 0 := by
  simp only [Nat.testBit, Nat.and_comm (n >>> i) 1, Nat.one_and_eq_mod_two, bne_iff_ne]
  split <;> omega

/-- The bit extracted at position `n` from a UInt32 corresponds to `testBit`. -/
theorem uint32_testBit (code : UInt32) (n : Nat) (hn : n < 32) :
    ((code >>> n.toUInt32) &&& 1) =
      if code.toNat.testBit n then 1 else 0 := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_and, UInt32.toNat_shiftRight]
  have hn_eq : n.toUInt32.toNat % 32 = n := by simp [Nat.toUInt32]; omega
  rw [hn_eq, UInt32.toNat_one, shift_and_one_eq_testBit]
  split <;> simp

/-- `uint32_testBit` specialized to UInt8 input. -/
private theorem uint32_bit_eq_testBit (byte : UInt8) (off : Nat) (hoff : off < 8) :
    ((byte.toUInt32 >>> off.toUInt32) &&& 1) =
      if byte.toNat.testBit off then 1 else 0 := by
  have := uint32_testBit byte.toUInt32 off (by omega)
  rwa [UInt8.toNat_toUInt32] at this

private theorem list_drop_cons_tail {l : List α} {a : α} {rest : List α} {n : Nat}
    (h : l.drop n = a :: rest) : rest = l.drop (n + 1) := by
  have : l.drop (n + 1) = (l.drop n).drop 1 := by rw [List.drop_drop, Nat.add_comm]
  rw [this, h, List.drop_one, List.tail_cons]

/-- `readBit` preserves the well-formedness invariant `bitOff < 8`. -/
theorem readBit_wf (br : Zip.Native.BitReader) (bit : UInt32)
    (br' : Zip.Native.BitReader) (hwf : br.bitOff < 8)
    (h : br.readBit = .ok (bit, br')) : br'.bitOff < 8 := by
  simp only [Zip.Native.BitReader.readBit] at h
  split at h
  · simp at h
  · split at h <;> simp only [Except.ok.injEq, Prod.mk.injEq] at h
    · obtain ⟨_, rfl⟩ := h; simp
    · obtain ⟨_, rfl⟩ := h; simp; omega

/-! ### readBit correspondence -/

/-- Reading a single bit from the `BitReader` corresponds to consuming
    the head of the corresponding bit list. Requires `bitOff < 8`. -/
theorem readBit_toBits (br : Zip.Native.BitReader)
    (bit : UInt32) (br' : Zip.Native.BitReader)
    (hwf : br.bitOff < 8)
    (h : br.readBit = .ok (bit, br')) :
    ∃ b rest,
      br.toBits = b :: rest ∧
      br'.toBits = rest ∧
      bit = if b then 1 else 0 := by
  -- Unfold readBit; the error case is impossible since h says it succeeded
  simp only [Zip.Native.BitReader.readBit] at h
  split at h
  · simp at h
  · rename_i hpos
    -- hpos : ¬(br.pos ≥ br.data.size), so br.pos < br.data.size
    have hpos' : br.pos < br.data.size := by omega
    -- Get the bit list structure from bytesToBits_drop_testBit
    obtain ⟨rest, hrest⟩ := bytesToBits_drop_testBit br.data br.pos br.bitOff hpos' hwf
    have hrest_eq : rest =
        (Deflate.Spec.bytesToBits br.data).drop (br.pos * 8 + br.bitOff + 1) :=
      list_drop_cons_tail hrest
    -- The bit read by readBit matches data[pos]! which equals data[pos]
    have hget : br.data[br.pos]! = br.data[br.pos] := by simp [hpos']
    refine ⟨br.data[br.pos].toNat.testBit br.bitOff, rest, hrest, ?_, ?_⟩
    · -- br'.toBits = rest
      split at h <;> simp only [Except.ok.injEq, Prod.mk.injEq] at h
      · obtain ⟨_, rfl⟩ := h
        simp only [Zip.Native.BitReader.toBits, hrest_eq]; congr 1; omega
      · obtain ⟨_, rfl⟩ := h
        simp only [Zip.Native.BitReader.toBits, hrest_eq]; congr 1
    · -- bit = if testBit then 1 else 0 (same in both bitOff cases)
      split at h <;> simp only [Except.ok.injEq, Prod.mk.injEq] at h
      all_goals (obtain ⟨rfl, _⟩ := h; rw [hget];
                 exact uint32_bit_eq_testBit br.data[br.pos] br.bitOff hwf)

/-! ### UInt32 accumulator arithmetic

Helper lemmas for the `readBits.go` loop invariant. The loop accumulates
bits via `acc ||| (bit <<< shift.toUInt32)`. When the bits don't overlap
(ensured by `acc.toNat < 2^shift`), this OR equals addition. -/

private theorem shift_toUInt32_mod32 {shift : Nat} (hshift : shift < 32) :
    shift.toUInt32.toNat % 32 = shift := by
  simp [Nat.toUInt32]; omega

private theorem acc_or_shift_toNat (acc bit : UInt32) (shift : Nat)
    (hacc : acc.toNat < 2 ^ shift) (hbit : bit = 0 ∨ bit = 1) (hshift : shift < 32) :
    (acc ||| (bit <<< shift.toUInt32)).toNat = acc.toNat + bit.toNat * 2 ^ shift := by
  rcases hbit with rfl | rfl
  · simp [UInt32.toNat_zero]
  · rw [UInt32.toNat_or, UInt32.toNat_shiftLeft, shift_toUInt32_mod32 hshift,
        UInt32.toNat_one, Nat.shiftLeft_eq, Nat.one_mul,
        Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) hshift),
        Nat.or_two_pow_eq_add hacc]

private theorem acc_or_shift_bound (acc bit : UInt32) (shift : Nat)
    (hacc : acc.toNat < 2 ^ shift) (hbit : bit = 0 ∨ bit = 1) (hshift : shift < 32) :
    (acc ||| (bit <<< shift.toUInt32)).toNat < 2 ^ (shift + 1) := by
  rw [acc_or_shift_toNat acc bit shift hacc hbit hshift, Nat.pow_succ]
  rcases hbit with rfl | rfl <;> simp <;> omega

/-! ### Generalized readBits.go invariant -/

/-- Generalized loop invariant for `readBits.go`: the spec-level
    `readBitsLSB k` on the corresponding bit list produces a value `specVal`
    such that `val.toNat = acc.toNat + specVal * 2^shift`. -/
private theorem readBits_go_spec (br : Zip.Native.BitReader) (acc : UInt32)
    (shift k : Nat) (val : UInt32) (br' : Zip.Native.BitReader)
    (hwf : br.bitOff < 8) (hsk : shift + k ≤ 32) (hacc : acc.toNat < 2 ^ shift)
    (h : Zip.Native.BitReader.readBits.go br acc shift k = .ok (val, br')) :
    ∃ specVal rest,
      Deflate.Spec.readBitsLSB k br.toBits = some (specVal, rest) ∧
      br'.toBits = rest ∧
      val.toNat = acc.toNat + specVal * 2 ^ shift ∧
      br'.bitOff < 8 := by
  induction k generalizing br acc shift with
  | zero =>
    simp only [Zip.Native.BitReader.readBits.go] at h
    obtain ⟨rfl, rfl⟩ := Except.ok.inj h
    exact ⟨0, br'.toBits, by simp [Deflate.Spec.readBitsLSB], rfl, by simp, hwf⟩
  | succ k ih =>
    -- Case split on whether readBit succeeds
    cases hrd : br.readBit with
    | error e =>
      -- readBit failed → readBits.go (k+1) fails, contradicting h
      simp only [Zip.Native.BitReader.readBits.go, bind, Except.bind, hrd] at h
      simp at h
    | ok p =>
      obtain ⟨bit, br₁⟩ := p
      -- readBit succeeded, unfold readBits.go using hrd
      simp only [Zip.Native.BitReader.readBits.go, bind, Except.bind, hrd] at h
      -- h : readBits.go br₁ (acc ||| (bit <<< shift.toUInt32)) (shift + 1) k = .ok (val, br')
      -- Extract bit correspondence from readBit_toBits
      obtain ⟨b, rest₁, hbr_bits, hbr1_bits, hbit_val⟩ :=
        readBit_toBits br bit br₁ hwf hrd
      have hwf₁ := readBit_wf br bit br₁ hwf hrd
      -- bit is 0 or 1
      have hbit01 : bit = 0 ∨ bit = 1 := by
        cases b <;> simp_all
      -- New accumulator bounds
      have hshift : shift < 32 := by omega
      have hacc' := acc_or_shift_bound acc bit shift hacc hbit01 hshift
      -- Apply IH to the recursive call (val, br' not generalized — don't pass them)
      obtain ⟨specVal', rest', hspec', hbr', hval', hwf'⟩ :=
        ih br₁ (acc ||| (bit <<< shift.toUInt32)) (shift + 1)
          hwf₁ (by omega) hacc' h
      -- Connect readBitsLSB (k+1) to the IH result
      rw [hbr1_bits] at hspec'
      refine ⟨(if b then 1 else 0) + specVal' * 2, rest', ?_, hbr', ?_, hwf'⟩
      · -- readBitsLSB (k+1) br.toBits = some (...)
        simp [Deflate.Spec.readBitsLSB, hbr_bits, hspec']
      · -- val.toNat = acc.toNat + ((if b then 1 else 0) + specVal' * 2) * 2^shift
        rw [hval', acc_or_shift_toNat acc bit shift hacc hbit01 hshift, Nat.pow_succ]
        cases b <;> simp_all [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm] <;> omega

/-! ### readBits correspondence -/

/-- Reading `n` bits via `BitReader.readBits` corresponds to
    `readBitsLSB n` on the spec bit list.
    Requires `bitOff < 8` (well-formedness) and `n ≤ 32` (UInt32 shift
    correctness — native `readBits.go` uses `bit <<< shift.toUInt32`
    where `UInt32.shiftLeft` reduces shift mod 32). -/
theorem readBits_toBits (br : Zip.Native.BitReader)
    (n : Nat) (val : UInt32) (br' : Zip.Native.BitReader)
    (hwf : br.bitOff < 8) (hn : n ≤ 32)
    (h : br.readBits n = .ok (val, br')) :
    ∃ rest,
      Deflate.Spec.readBitsLSB n br.toBits = some (val.toNat, rest) ∧
      br'.toBits = rest := by
  -- readBits = readBits.go br 0 0 n
  simp only [Zip.Native.BitReader.readBits] at h
  obtain ⟨specVal, rest, hspec, hrest, hval, _⟩ :=
    readBits_go_spec br 0 0 n val br' hwf (by omega) (by simp) h
  simp at hval
  -- hval : val.toNat = specVal, need to rewrite specVal → val.toNat in hspec
  rw [← hval] at hspec
  exact ⟨rest, hspec, hrest⟩

/-! ### alignToByte correspondence -/

/-- `toBits` length is a multiple of 8 minus `bitOff`. -/
private theorem toBits_length (br : Zip.Native.BitReader) :
    br.toBits.length = br.data.size * 8 - (br.pos * 8 + br.bitOff) := by
  simp [Zip.Native.BitReader.toBits, List.length_drop, Deflate.Spec.bytesToBits_length]

/-- When `bitOff = 0`, `toBits` has length divisible by 8. -/
private theorem toBits_length_mod8_zero (br : Zip.Native.BitReader) (h : br.bitOff = 0) :
    br.toBits.length % 8 = 0 := by
  rw [toBits_length, h, Nat.add_zero]
  omega

/-- When `0 < bitOff < 8` and the BitReader is within bounds, `toBits.length % 8 = 8 - bitOff`. -/
private theorem toBits_length_mod8_pos (br : Zip.Native.BitReader)
    (hwf : br.bitOff < 8) (hoff : br.bitOff ≠ 0) (hpos : br.pos < br.data.size) :
    br.toBits.length % 8 = 8 - br.bitOff := by
  rw [toBits_length]
  have : br.pos * 8 + br.bitOff < br.data.size * 8 := by omega
  omega

/-- Native `alignToByte` corresponds to spec `alignToByte` on the bit list.
    Requires `bitOff < 8` and that the BitReader is within bounds when `bitOff > 0`. -/
theorem alignToByte_toBits (br : Zip.Native.BitReader)
    (hwf : br.bitOff < 8)
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size) :
    br.alignToByte.toBits = Deflate.Spec.alignToByte br.toBits := by
  simp only [Zip.Native.BitReader.alignToByte, Deflate.Spec.alignToByte]
  by_cases hoff : br.bitOff = 0
  · -- bitOff = 0: native is identity, spec drops 0
    simp [hoff, toBits_length_mod8_zero br hoff]
  · -- bitOff > 0: native advances to next byte, spec drops (8 - bitOff) bits
    have hpos' : br.pos < br.data.size := hpos.resolve_left hoff
    have hoff_ne : (br.bitOff == 0) = false := by simp [hoff]
    simp only [hoff_ne, Bool.false_eq_true, ↓reduceIte]
    rw [toBits_length_mod8_pos br hwf hoff hpos']
    simp only [Zip.Native.BitReader.toBits, Nat.add_zero]
    rw [List.drop_drop]
    have hle : br.bitOff ≤ 8 := by omega
    congr 1
    rw [Nat.add_assoc, Nat.add_sub_cancel' hle]
    omega

/-! ### Byte-level read correspondence -/

/-- Reading `n` bits from `testBit` values (LSB first) reconstructs the
    original value. Key building block for byte-level read correspondence. -/
private theorem readBitsLSB_testBit (m n : Nat) (hm : m < 2 ^ n) (rest : List Bool) :
    Deflate.Spec.readBitsLSB n
      ((List.ofFn (n := n) fun (i : Fin n) => m.testBit i.val) ++ rest) =
      some (m, rest) := by
  induction n generalizing m with
  | zero => simp [Deflate.Spec.readBitsLSB]; omega
  | succ k ih =>
    simp only [List.ofFn_succ, List.cons_append]
    simp only [Deflate.Spec.readBitsLSB]
    -- Rewrite tail: m.testBit (i+1) = (m/2).testBit i
    have htb : (fun (i : Fin k) => m.testBit (Fin.succ i).val) =
               (fun (i : Fin k) => (m / 2).testBit i.val) := by
      ext i; simp [Fin.val_succ, ← Nat.testBit_div_two]
    rw [htb]
    -- Apply IH with m/2
    rw [ih (m / 2) (by omega)]
    simp
    -- (if m % 2 = 1 then 1 else 0) + m / 2 * 2 = m
    have := Nat.mod_add_div m 2; split <;> omega

/-- Splitting `readBitsLSB`: reading `m + n` bits is reading `m` then `n` bits,
    with the second value shifted left by `m`. -/
private theorem readBitsLSB_split (m n : Nat) (bits : List Bool) :
    Deflate.Spec.readBitsLSB (m + n) bits =
      (Deflate.Spec.readBitsLSB m bits).bind fun (v1, bits') =>
        (Deflate.Spec.readBitsLSB n bits').bind fun (v2, bits'') =>
          some (v1 + v2 * 2 ^ m, bits'') := by
  induction m generalizing bits with
  | zero =>
    simp only [Deflate.Spec.readBitsLSB, Nat.zero_add, Option.bind]
    cases Deflate.Spec.readBitsLSB n bits with
    | none => rfl
    | some p => simp
  | succ k ih =>
    -- Rewrite (k + 1) + n = (k + n) + 1 so readBitsLSB can unfold
    rw [show k + 1 + n = (k + n) + 1 from by omega]
    cases bits with
    | nil => simp [Deflate.Spec.readBitsLSB]
    | cons b rest =>
      -- Unfold one step of readBitsLSB on LHS
      simp only [Deflate.Spec.readBitsLSB]
      -- Apply IH to readBitsLSB (k + n) rest in the LHS
      rw [ih rest]
      -- Both sides now match on readBitsLSB k rest
      cases hk : Deflate.Spec.readBitsLSB k rest with
      | none => simp [bind, Option.bind]
      | some p =>
        obtain ⟨v1, rest'⟩ := p
        simp only [bind, Option.bind]
        cases hn : Deflate.Spec.readBitsLSB n rest' with
        | none => simp
        | some q =>
          obtain ⟨v2, rest''⟩ := q
          simp only []
          congr 1; ext1
          · rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.add_mul]; split <;> omega
          · rfl

/-- Reading 8 bits from a byte's bit representation recovers the byte value. -/
private theorem readBitsLSB_byteToBits (b : UInt8) (rest : List Bool) :
    Deflate.Spec.readBitsLSB 8 (Deflate.Spec.bytesToBits.byteToBits b ++ rest) =
      some (b.toNat, rest) := by
  exact readBitsLSB_testBit b.toNat 8 b.toBitVec.isLt rest

/-! ### Byte indexing into bytesToBits -/

/-- Helper: dropping past a prefix of known length. -/
private theorem drop_append_left' {l₁ l₂ : List α} {k : Nat}
    (h : l₁.length = k) (n : Nat) :
    (l₁ ++ l₂).drop (k + n) = l₂.drop n := by
  rw [← List.drop_drop, List.drop_left' h]

/-- Dropping `i * k` elements from a flatMap with uniform-length output
    gives the `i`-th element's image followed by the rest. -/
private theorem flatMap_uniform_drop {f : α → List β} (hf : ∀ a, (f a).length = k)
    (l : List α) (i : Nat) (hi : i < l.length) :
    (l.flatMap f).drop (i * k) = f l[i] ++ (l.flatMap f).drop ((i + 1) * k) := by
  induction l generalizing i with
  | nil => simp at hi
  | cons b rest ih =>
    cases i with
    | zero =>
      simp only [List.flatMap_cons, Nat.zero_mul, List.drop_zero, List.getElem_cons_zero,
        Nat.zero_add, Nat.one_mul]
      rw [List.drop_left' (hf b)]
    | succ j =>
      simp only [List.flatMap_cons, List.getElem_cons_succ]
      rw [show (j + 1) * k = k + j * k from by rw [Nat.succ_mul, Nat.add_comm],
          drop_append_left' (hf b),
          show (j + 2) * k = k + (j + 1) * k from by rw [show j + 2 = (j + 1) + 1 from rfl,
            Nat.succ_mul, Nat.add_comm],
          drop_append_left' (hf b)]
      exact ih j (by simpa using hi)

/-- At byte position `pos`, `bytesToBits` gives `byteToBits data[pos]` followed by the rest. -/
private theorem bytesToBits_getElem (data : ByteArray) (pos : Nat) (hpos : pos < data.size) :
    (Deflate.Spec.bytesToBits data).drop (pos * 8) =
      Deflate.Spec.bytesToBits.byteToBits data[pos] ++
        (Deflate.Spec.bytesToBits data).drop ((pos + 1) * 8) := by
  simp only [Deflate.Spec.bytesToBits, ByteArray.size] at *
  have hlen := Deflate.Spec.bytesToBits.byteToBits_length
  rw [flatMap_uniform_drop (fun b => hlen b) data.data.toList pos (by simpa using hpos)]
  simp only [Array.getElem_toList]; rfl

/-- From a byte-aligned reader, `readBitsLSB 8` produces the next byte value. -/
theorem toBits_readBitsLSB_byte (br : Zip.Native.BitReader)
    (hoff : br.bitOff = 0) (hpos : br.pos < br.data.size) :
    Deflate.Spec.readBitsLSB 8 br.toBits =
      some (br.data[br.pos].toNat,
            { br with pos := br.pos + 1, bitOff := 0 : Zip.Native.BitReader }.toBits) := by
  simp only [Zip.Native.BitReader.toBits, hoff, Nat.add_zero]
  rw [bytesToBits_getElem br.data br.pos hpos]
  rw [readBitsLSB_byteToBits]
  done

/-- `alignToByte` produces a byte-aligned BitReader. -/
theorem alignToByte_wf (br : Zip.Native.BitReader) :
    br.alignToByte.bitOff = 0 := by
  simp [Zip.Native.BitReader.alignToByte]
  split <;> simp_all

/-- `alignToByte` preserves the data field. -/
theorem alignToByte_data (br : Zip.Native.BitReader) :
    br.alignToByte.data = br.data := by
  simp [Zip.Native.BitReader.alignToByte]
  split <;> simp_all

/-! ### readUInt16LE correspondence -/

/-- Native `readUInt16LE` corresponds to spec `readBitsLSB 16` after alignment.
    The native reader aligns to a byte boundary, reads two bytes as LE uint16.
    The spec aligns and reads 16 bits LSB-first, giving the same value. -/
theorem readUInt16LE_toBits (br : Zip.Native.BitReader)
    (val : UInt16) (br' : Zip.Native.BitReader)
    (hwf : br.bitOff < 8)
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (h : br.readUInt16LE = .ok (val, br')) :
    ∃ rest,
      Deflate.Spec.readBitsLSB 16 (Deflate.Spec.alignToByte br.toBits) =
        some (val.toNat, rest) ∧
      br'.toBits = rest := by
  -- Unfold readUInt16LE: aligns, bounds check, reads two bytes
  simp only [Zip.Native.BitReader.readUInt16LE] at h
  split at h
  · simp at h -- bounds check failed → contradiction with h : error = ok
  · -- bounds check passed
    rename_i hbound
    -- h : .ok (lo ||| (hi <<< 8), { ... pos + 2 ... }) = .ok (val, br')
    -- hbound : ¬(br.alignToByte.pos + 2 > br.alignToByte.data.size)
    have hle : br.alignToByte.pos + 2 ≤ br.alignToByte.data.size := by omega
    -- Extract value and reader from h
    have hval : val = br.alignToByte.data[br.alignToByte.pos]!.toUInt16 |||
        (br.alignToByte.data[br.alignToByte.pos + 1]!.toUInt16 <<< 8) := by
      cases h; rfl
    have hbr' : br' = { br.alignToByte with pos := br.alignToByte.pos + 2 } := by
      cases h; rfl
    -- Alignment properties
    have hoff : br.alignToByte.bitOff = 0 := alignToByte_wf br
    have halign : br.alignToByte.toBits = Deflate.Spec.alignToByte br.toBits :=
      alignToByte_toBits br hwf hpos
    -- Split 16-bit read into two 8-bit reads
    rw [← halign, show (16 : Nat) = 8 + 8 from rfl, readBitsLSB_split]
    -- First byte
    have hpos0 : br.alignToByte.pos < br.alignToByte.data.size := by omega
    rw [toBits_readBitsLSB_byte br.alignToByte hoff hpos0]
    simp only [Option.bind]
    -- Second byte
    have hpos1 : br.alignToByte.pos + 1 < br.alignToByte.data.size := by omega
    rw [toBits_readBitsLSB_byte ⟨br.alignToByte.data, br.alignToByte.pos + 1, 0⟩ rfl hpos1]
    -- Goal: ∃ rest, some (lo + hi * 256, bits') = some (val.toNat, rest) ∧ br'.toBits = rest
    constructor
    constructor
    · -- some equality: values match
      simp only [Option.some.injEq, Prod.mk.injEq]
      constructor
      · -- Arithmetic: data[pos].toNat + data[pos+1].toNat * 256 = val.toNat
        rw [hval]; simp [hpos0, hpos1]
        -- Goal: lo.toNat + hi.toNat * 256 = lo.toNat ||| (hi.toNat <<< 8 % 65536)
        have hlo : br.alignToByte.data[br.alignToByte.pos].toNat < 2 ^ 8 :=
          br.alignToByte.data[br.alignToByte.pos].toBitVec.isLt
        have hhi : br.alignToByte.data[br.alignToByte.pos + 1].toNat < 2 ^ 8 :=
          br.alignToByte.data[br.alignToByte.pos + 1].toBitVec.isLt
        rw [Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega),
            show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.shiftLeft_eq,
            Nat.add_comm, Nat.shiftLeft_add_eq_or_of_lt hlo, Nat.or_comm]
      · rfl
    · -- br'.toBits = bits'
      rw [hbr']
      simp only [Zip.Native.BitReader.toBits, hoff]
      done

/-! ### readBytes correspondence -/

/-- Spec-level `readNBytes` on byte-aligned bits reads the expected bytes.
    Generalized over accumulator for the inductive proof. -/
private theorem readNBytes_aligned (data : ByteArray) (pos n : Nat)
    (hle : pos + n ≤ data.size) (acc : List UInt8) :
    Deflate.Spec.decodeStored.readNBytes n
      ((Deflate.Spec.bytesToBits data).drop (pos * 8)) acc =
      some (acc ++ (data.data.toList.extract pos (pos + n)),
            (Deflate.Spec.bytesToBits data).drop ((pos + n) * 8)) := by
  induction n generalizing pos acc with
  | zero =>
    simp [Deflate.Spec.decodeStored.readNBytes]
    done
  | succ k ih =>
    -- Unfold one step of readNBytes
    simp only [Deflate.Spec.decodeStored.readNBytes]
    -- Evaluate readBitsLSB 8 at byte-aligned position pos
    have hpos : pos < data.size := by omega
    rw [bytesToBits_getElem data pos hpos, readBitsLSB_byteToBits]
    simp only [bind, Option.bind, UInt8.ofNat_toNat]
    -- Apply IH with pos+1
    rw [ih (pos + 1) (by omega) (acc ++ [data[pos]])]
    -- Goal: some (acc ++ [data[pos]] ++ extract(pos+1, pos+1+k), ...) =
    --       some (acc ++ extract(pos, pos+k+1), ...)
    congr 1; ext1
    · -- List equality
      rw [List.append_assoc]
      congr 1
      -- [data[pos]] ++ extract(pos+1, pos+1+k) = extract(pos, pos+k+1)
      simp only [List.extract, show pos + (k + 1) - pos = k + 1 from by omega,
        show pos + 1 + k - (pos + 1) = k from by omega]
      have hlen : pos < data.data.toList.length := by simp [Array.length_toList]; exact hpos
      rw [List.drop_eq_getElem_cons hlen, List.take_succ_cons]
      congr 1
      congr 1; omega
    · -- bits equality: (pos+1+k)*8 = (pos+k+1)*8
      show List.drop ((pos + 1 + k) * 8) _ = List.drop ((pos + (k + 1)) * 8) _
      congr 1; omega

/-- `readUInt16LE` preserves well-formedness: output reader has `bitOff = 0`. -/
theorem readUInt16LE_wf (br : Zip.Native.BitReader)
    (val : UInt16) (br' : Zip.Native.BitReader)
    (h : br.readUInt16LE = .ok (val, br')) : br'.bitOff = 0 := by
  simp only [Zip.Native.BitReader.readUInt16LE] at h
  split at h
  · simp at h
  · have : br' = { br.alignToByte with pos := br.alignToByte.pos + 2 } := by cases h; rfl
    rw [this]; exact alignToByte_wf br

/-- `readUInt16LE` preserves the data field. -/
theorem readUInt16LE_data (br : Zip.Native.BitReader)
    (val : UInt16) (br' : Zip.Native.BitReader)
    (h : br.readUInt16LE = .ok (val, br')) : br'.data = br.data := by
  simp only [Zip.Native.BitReader.readUInt16LE] at h
  split at h
  · simp at h
  · have : br' = { br.alignToByte with pos := br.alignToByte.pos + 2 } := by cases h; rfl
    rw [this]; exact alignToByte_data br

/-- `readBytes` preserves well-formedness: output reader has `bitOff = 0`. -/
theorem readBytes_wf (br : Zip.Native.BitReader)
    (n : Nat) (bytes : ByteArray) (br' : Zip.Native.BitReader)
    (h : br.readBytes n = .ok (bytes, br')) : br'.bitOff = 0 := by
  simp only [Zip.Native.BitReader.readBytes] at h
  split at h
  · simp at h
  · have : br' = { br.alignToByte with pos := br.alignToByte.pos + n } := by cases h; rfl
    rw [this]; exact alignToByte_wf br

/-- For byte-aligned reader, `alignToByte` on the spec side is identity. -/
theorem alignToByte_id_of_aligned (br : Zip.Native.BitReader)
    (hoff : br.bitOff = 0) :
    Deflate.Spec.alignToByte br.toBits = br.toBits := by
  have : br.alignToByte = br := by
    simp [Zip.Native.BitReader.alignToByte, hoff]
  rw [← alignToByte_toBits br (by omega) (Or.inl hoff), this]

/-- Native `readBytes` corresponds to spec `readNBytes` after alignment.
    The native reader aligns to a byte boundary and reads `n` contiguous bytes.
    The spec reads `n` bytes one at a time via `readBitsLSB 8`. -/
theorem readBytes_toBits (br : Zip.Native.BitReader)
    (n : Nat) (bytes : ByteArray) (br' : Zip.Native.BitReader)
    (hwf : br.bitOff < 8)
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (h : br.readBytes n = .ok (bytes, br')) :
    ∃ rest,
      Deflate.Spec.decodeStored.readNBytes n (Deflate.Spec.alignToByte br.toBits) [] =
        some (bytes.data.toList, rest) ∧
      br'.toBits = rest := by
  -- Unfold readBytes: aligns, bounds check, extracts slice
  simp only [Zip.Native.BitReader.readBytes] at h
  split at h
  · simp at h
  · rename_i hbound
    -- Extract bytes and reader from h
    have hbytes : bytes = br.alignToByte.data.extract br.alignToByte.pos (br.alignToByte.pos + n) := by
      cases h; rfl
    have hbr' : br' = { br.alignToByte with pos := br.alignToByte.pos + n } := by
      cases h; rfl
    -- Alignment properties
    have hoff : br.alignToByte.bitOff = 0 := alignToByte_wf br
    have halign : br.alignToByte.toBits = Deflate.Spec.alignToByte br.toBits :=
      alignToByte_toBits br hwf hpos
    have hle : br.alignToByte.pos + n ≤ br.alignToByte.data.size := by omega
    -- Use readNBytes_aligned
    rw [← halign]
    simp only [Zip.Native.BitReader.toBits, hoff, Nat.add_zero]
    rw [readNBytes_aligned br.alignToByte.data br.alignToByte.pos n hle []]
    simp only [List.nil_append]
    -- bytes and remaining bits
    constructor; constructor
    · -- bytes equality
      congr 1
      rw [hbytes, ByteArray.data_extract, Array.toList_extract]
    · -- remaining bits equality
      rw [hbr']
      simp only [hoff, Nat.add_zero]

/-! ### writeBitsLSB properties -/

/-- `writeBitsLSB` produces exactly `n` bits. -/
theorem writeBitsLSB_length (n val : Nat) :
    (Deflate.Spec.writeBitsLSB n val).length = n := by
  induction n generalizing val with
  | zero => simp [Deflate.Spec.writeBitsLSB]
  | succ k ih => simp [Deflate.Spec.writeBitsLSB, ih]

/-- Reading back a written value recovers the original. -/
theorem readBitsLSB_writeBitsLSB (n val : Nat) (rest : List Bool)
    (h : val < 2 ^ n) :
    Deflate.Spec.readBitsLSB n (Deflate.Spec.writeBitsLSB n val ++ rest) =
      some (val, rest) := by
  induction n generalizing val with
  | zero => simp [Deflate.Spec.readBitsLSB, Deflate.Spec.writeBitsLSB]; omega
  | succ k ih =>
    simp only [Deflate.Spec.writeBitsLSB, List.cons_append, Deflate.Spec.readBitsLSB]
    have hlt : val / 2 < 2 ^ k := by
      rw [Nat.div_lt_iff_lt_mul (by omega : 0 < 2)]
      calc val < 2 ^ (k + 1) := h
           _ = 2 ^ k * 2 := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [ih (val / 2) hlt]
    simp only [bind, Option.bind]
    congr 1; ext1
    · -- (if val % 2 == 1 then 1 else 0) + val / 2 * 2 = val
      have := Nat.div_add_mod val 2
      split <;> simp_all [beq_iff_eq] <;> omega
    · rfl

end Deflate.Correctness
