import Zip.Spec.Deflate

/-!
# Bitstream Write Correspondence

Properties of bit-packing functions: `bitsToNat`, `bitsToByte`, `writeBitsLSB`,
and `bitsToBytes`. Establishes roundtrip properties with `bytesToBits` and
`readBitsLSB`.
-/

namespace Deflate.Correctness

/-! ### bitsToNat / bitsToByte properties -/

/-- `bitsToNat n` on `testBit` values recovers the original number. -/
private theorem bitsToNat_testBit (m n : Nat) (hm : m < 2 ^ n) :
    Deflate.Spec.bitsToNat n (List.ofFn (n := n) fun (i : Fin n) => m.testBit i.val) = m := by
  induction n generalizing m with
  | zero => simp at hm; simp [Deflate.Spec.bitsToNat]; omega
  | succ k ih =>
    simp only [List.ofFn_succ, Deflate.Spec.bitsToNat]
    have htb : (fun (i : Fin k) => m.testBit (Fin.succ i).val) =
               (fun (i : Fin k) => (m / 2).testBit i.val) := by
      ext i; simp [Fin.val_succ, ← Nat.testBit_div_two]
    have hdiv : m / 2 < 2 ^ k := by
      rw [Nat.div_lt_iff_lt_mul (by omega : 0 < 2)]; rw [Nat.pow_succ] at hm; omega
    rw [htb, ih (m / 2) hdiv]
    simp only [Nat.testBit, Nat.one_and_eq_mod_two]
    have := Nat.div_add_mod m 2
    by_cases hmod : m % 2 = 0 <;> simp_all <;> omega

/-- `bitsToNat n` produces values less than `2^n`. -/
private theorem bitsToNat_bound (n : Nat) (bits : List Bool) :
    Deflate.Spec.bitsToNat n bits < 2 ^ n := by
  induction n generalizing bits with
  | zero => simp [Deflate.Spec.bitsToNat]
  | succ k ih =>
    cases bits with
    | nil => simp [Deflate.Spec.bitsToNat]; exact Nat.pos_of_ne_zero (by simp [Nat.pow_eq_zero])
    | cons b rest =>
      simp only [Deflate.Spec.bitsToNat]
      have := ih rest; rw [Nat.pow_succ]; split <;> omega

/-- `testBit i` on `bitsToNat n bits` recovers `bits[i]` for `i < n` and `i < bits.length`. -/
private theorem testBit_bitsToNat (bits : List Bool) (n i : Nat)
    (hi : i < n) (hlen : i < bits.length) :
    (Deflate.Spec.bitsToNat n bits).testBit i = bits[i] := by
  induction n generalizing bits i with
  | zero => omega
  | succ k ih =>
    cases bits with
    | nil => simp at hlen
    | cons b rest =>
      simp only [Deflate.Spec.bitsToNat]
      cases i with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.testBit_zero]
        cases b <;> simp <;> omega
      | succ j =>
        simp only [List.getElem_cons_succ]
        rw [← Nat.testBit_div_two]
        have hdiv : ((if b then 1 else 0) + 2 * Deflate.Spec.bitsToNat k rest) / 2 =
            Deflate.Spec.bitsToNat k rest := by split <;> omega
        rw [hdiv]
        exact ih rest j (by omega) (by simp at hlen; omega)

/-- `testBit i` on `bitsToNat n bits` is `false` for `i ≥ n`. -/
private theorem testBit_bitsToNat_ge (bits : List Bool) (n i : Nat)
    (hi : i ≥ n) :
    (Deflate.Spec.bitsToNat n bits).testBit i = false := by
  have hlt := bitsToNat_bound n bits
  have hle : 2 ^ n ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) hi
  exact Nat.testBit_lt_two_pow (by omega)

/-- `testBit i` on `bitsToNat n bits` is `false` for `i ≥ bits.length` (within `n`). -/
private theorem testBit_bitsToNat_ge_length (bits : List Bool) (n i : Nat)
    (hi : i < n) (hlen : i ≥ bits.length) :
    (Deflate.Spec.bitsToNat n bits).testBit i = false := by
  induction n generalizing bits i with
  | zero => omega
  | succ k ih =>
    cases bits with
    | nil => simp [Deflate.Spec.bitsToNat]
    | cons b rest =>
      simp only [Deflate.Spec.bitsToNat]
      cases i with
      | zero => simp at hlen
      | succ j =>
        rw [← Nat.testBit_div_two]
        have hdiv : ((if b then 1 else 0) + 2 * Deflate.Spec.bitsToNat k rest) / 2 =
            Deflate.Spec.bitsToNat k rest := by split <;> omega
        rw [hdiv]
        exact ih rest j (by omega) (by simp at hlen; omega)

/-- `byteToBits (bitsToByte bits) = bits.take 8 ++ List.replicate (8 - min 8 bits.length) false`
    when `bits.length ≤ 8`. In particular, for length-8 lists this is the identity. -/
private theorem byteToBits_bitsToByte_take8 (bits : List Bool) :
    Deflate.Spec.bytesToBits.byteToBits (Deflate.Spec.bitsToByte bits) =
      List.ofFn fun (i : Fin 8) =>
        if h : i.val < bits.length then bits[i.val] else false := by
  simp only [Deflate.Spec.bitsToByte, Deflate.Spec.bytesToBits.byteToBits]
  congr 1; ext ⟨i, hi⟩
  have hbound := bitsToNat_bound 8 bits
  show (Deflate.Spec.bitsToNat 8 bits).toUInt8.toNat.testBit i =
    if h : i < bits.length then bits[i] else false
  rw [show (Deflate.Spec.bitsToNat 8 bits).toUInt8 =
    ⟨BitVec.ofNat 8 (Deflate.Spec.bitsToNat 8 bits)⟩ from rfl]
  simp only [UInt8.toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbound]
  by_cases hlen : i < bits.length
  · rw [testBit_bitsToNat bits 8 i (by omega) hlen]; simp [hlen]
  · rw [testBit_bitsToNat_ge_length bits 8 i (by omega) (by omega)]; simp [hlen]

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
      rw [Nat.div_lt_iff_lt_mul (by omega : 0 < 2)]; rw [Nat.pow_succ] at h; omega
    rw [ih (val / 2) hlt]
    simp only [bind, Option.bind]
    congr 1; ext1
    · have := Nat.div_add_mod val 2
      split <;> simp_all [beq_iff_eq] <;> omega
    · rfl

/-! ### bitsToBytes / bytesToBits roundtrip -/

/-- `bytesToBits.byteToBits` on length-8 bits recovers the original list. -/
private theorem byteToBits_bitsToByte_eq (bits : List Bool) (h : bits.length = 8) :
    Deflate.Spec.bytesToBits.byteToBits (Deflate.Spec.bitsToByte bits) = bits := by
  have := byteToBits_bitsToByte_take8 bits
  rw [this]
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp only [List.getElem_ofFn]
    simp [show i < bits.length from by omega]

/-- `bitsToBytes.go` with accumulator appends to the accumulator. -/
private theorem bitsToBytes_go_eq (bits : List Bool) (acc : ByteArray) :
    (Deflate.Spec.bitsToBytes.go bits acc).data.toList =
      acc.data.toList ++ (Deflate.Spec.bitsToBytes.go bits ByteArray.empty).data.toList := by
  suffices ∀ (bits : List Bool) (acc : ByteArray),
      (Deflate.Spec.bitsToBytes.go bits acc).data.toList =
        acc.data.toList ++ (Deflate.Spec.bitsToBytes.go bits ByteArray.empty).data.toList by
    exact this bits acc
  intro bits
  induction h : bits.length using Nat.strongRecOn generalizing bits with
  | _ n ih =>
    intro acc
    cases bits with
    | nil => simp [Deflate.Spec.bitsToBytes.go]
    | cons b rest =>
      unfold Deflate.Spec.bitsToBytes.go
      have hlen : ((b :: rest).drop 8).length < (b :: rest).length := by
        simp [List.length_drop]; omega
      subst h
      rw [ih _ hlen _ rfl (acc.push (Deflate.Spec.bitsToByte (b :: rest)))]
      rw [ih _ hlen _ rfl (ByteArray.empty.push (Deflate.Spec.bitsToByte (b :: rest)))]
      simp [ByteArray.push, Array.toList_push, List.append_assoc]

/-- `bitsToBytes` of empty is empty. -/
private theorem bitsToBytes_nil :
    Deflate.Spec.bitsToBytes [] = ByteArray.empty := by
  simp [Deflate.Spec.bitsToBytes, Deflate.Spec.bitsToBytes.go]

/-- `bitsToBytes` of non-empty list prepends one byte then recurses. -/
private theorem bitsToBytes_cons (b : Bool) (rest : List Bool) :
    (Deflate.Spec.bitsToBytes (b :: rest)).data.toList =
      [Deflate.Spec.bitsToByte (b :: rest)] ++
        (Deflate.Spec.bitsToBytes ((b :: rest).drop 8)).data.toList := by
  simp only [Deflate.Spec.bitsToBytes, Deflate.Spec.bitsToBytes.go]
  rw [bitsToBytes_go_eq]
  simp [ByteArray.push]

/-- `byteToBits_bitsToByte_take8` specialized: when `bits.length ≥ 8`,
    the output equals `bits.take 8`. -/
private theorem byteToBits_bitsToByte_take (bits : List Bool) (h : bits.length ≥ 8) :
    Deflate.Spec.bytesToBits.byteToBits (Deflate.Spec.bitsToByte bits) = bits.take 8 := by
  rw [byteToBits_bitsToByte_take8]
  apply List.ext_getElem
  · simp [List.length_take]; omega
  · intro i h1 h2
    simp only [List.length_ofFn] at h1
    simp only [List.getElem_ofFn, show i < bits.length from by omega, ↓reduceDIte,
      List.getElem_take]

/-- `bytesToBits` unfolds through the byte list via flatMap. -/
private theorem bytesToBits_data (ba : ByteArray) :
    Deflate.Spec.bytesToBits ba = ba.data.toList.flatMap Deflate.Spec.bytesToBits.byteToBits := by
  rfl

/-- Packing then unpacking recovers the original bits (byte-aligned). -/
theorem bytesToBits_bitsToBytes_aligned (bits : List Bool)
    (h : bits.length % 8 = 0) :
    Deflate.Spec.bytesToBits (Deflate.Spec.bitsToBytes bits) = bits := by
  induction h' : bits.length using Nat.strongRecOn generalizing bits with
  | _ n ih =>
    cases bits with
    | nil => simp [bitsToBytes_nil, Deflate.Spec.bytesToBits]
    | cons b rest =>
      have hlen : (b :: rest).length ≥ 8 := by simp at h ⊢; omega
      rw [bytesToBits_data, bitsToBytes_cons]
      simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [byteToBits_bitsToByte_take _ hlen]
      have hdrop_len : ((b :: rest).drop 8).length < (b :: rest).length := by
        simp [List.length_drop]; omega
      have hdrop_mod : ((b :: rest).drop 8).length % 8 = 0 := by
        simp only [List.length_drop, List.length_cons] at h ⊢; omega
      rw [← bytesToBits_data, ih _ (by omega) _ hdrop_mod rfl]
      exact List.take_append_drop 8 (b :: rest)

/-- The output of `bytesToBits ∘ bitsToBytes` is at least as long as the input. -/
private theorem bytesToBits_bitsToBytes_length_ge (bits : List Bool) :
    (Deflate.Spec.bytesToBits (Deflate.Spec.bitsToBytes bits)).length ≥ bits.length := by
  induction h' : bits.length using Nat.strongRecOn generalizing bits with
  | _ n ih =>
    subst h'
    cases bits with
    | nil => simp [bitsToBytes_nil, Deflate.Spec.bytesToBits]
    | cons b rest =>
      rw [bytesToBits_data, bitsToBytes_cons]
      simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.length_append, Deflate.Spec.bytesToBits.byteToBits_length]
      have hdrop_len : ((b :: rest).drop 8).length < (b :: rest).length := by
        simp [List.length_drop]; omega
      have hih := ih _ hdrop_len ((b :: rest).drop 8) rfl
      rw [bytesToBits_data] at hih
      simp only [List.length_flatMap, Deflate.Spec.bytesToBits.byteToBits_length,
        List.length_drop] at hih ⊢
      omega

/-- Packing then unpacking recovers the original bits up to padding. -/
theorem bytesToBits_bitsToBytes_take (bits : List Bool) :
    (Deflate.Spec.bytesToBits (Deflate.Spec.bitsToBytes bits)).take bits.length = bits := by
  induction h' : bits.length using Nat.strongRecOn generalizing bits with
  | _ n ih =>
    subst h'
    cases bits with
    | nil => simp [bitsToBytes_nil, Deflate.Spec.bytesToBits]
    | cons b rest =>
      rw [bytesToBits_data, bitsToBytes_cons]
      simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [byteToBits_bitsToByte_take8]
      have hdrop_len : ((b :: rest).drop 8).length < (b :: rest).length := by
        simp [List.length_drop]; omega
      have hlen_ge := bytesToBits_bitsToBytes_length_ge ((b :: rest).drop 8)
      rw [bytesToBits_data] at hlen_ge
      apply List.ext_getElem
      · simp only [List.length_take, List.length_append, List.length_ofFn, List.length_cons,
          List.length_drop] at hlen_ge ⊢
        omega
      · intro i h1 h2
        simp only [List.length_cons] at h2
        simp only [List.length_take, List.length_append, List.length_ofFn] at h1
        simp only [List.getElem_take]
        by_cases hi8 : i < 8
        · rw [List.getElem_append_left (by simp; exact hi8)]
          simp only [List.getElem_ofFn, show i < (b :: rest).length from by omega, ↓reduceDIte]
          rfl
        · have hi8' : i ≥ 8 := by omega
          rw [List.getElem_append_right (by simp; omega)]
          simp only [List.length_ofFn]
          have hih := ih _ hdrop_len ((b :: rest).drop 8) rfl
          rw [bytesToBits_data] at hih
          have hidx : i - 8 < ((b :: rest).drop 8).length := by
            simp [List.length_drop]; omega
          have hbound : i - 8 < (List.take ((b :: rest).drop 8).length
            (List.flatMap Deflate.Spec.bytesToBits.byteToBits
              (Deflate.Spec.bitsToBytes ((b :: rest).drop 8)).data.toList)).length := by
            rw [congrArg List.length hih]; exact hidx
          have helem := List.getElem_of_eq hih hbound
          simp only [List.getElem_take] at helem
          rw [helem]
          simp only [List.getElem_drop]
          congr 1; omega

end Deflate.Correctness
