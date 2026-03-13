import Zip.Native.Fse
import Zip.Spec.BitReaderInvariant

/-!
# FSE Distribution and Table Validity Predicates

Formal specification of FSE (Finite State Entropy) distribution validity
and table structure for Zstandard compressed blocks (RFC 8878 §4.1).

This module defines predicates characterizing:
- `ValidAccuracyLog`: accuracy log in the range [5, 9] per RFC 8878 §4.1
- `ValidDistribution`: probability distribution satisfying RFC constraints
- `ValidFseTable`: structural invariants of a decoded FSE table

These predicates formalize the validity checks performed by
`Zip.Native.decodeFseDistribution` and the structural properties
guaranteed by `Zip.Native.buildFseTable`. All predicates have `Decidable`
instances for use with `decide`.
-/

namespace Zstd.Spec.Fse

open Zip.Native (FseCell)

/-- The accuracy log for an FSE table is valid per RFC 8878 §4.1 when it
    falls in the range [5, 9]. This is the range for sequence-level FSE
    tables (literal lengths, match lengths, offsets). Huffman weight tables
    use a wider range but this captures the common case. -/
def ValidAccuracyLog (al : Nat) : Prop :=
  5 ≤ al ∧ al ≤ 9

instance {al : Nat} : Decidable (ValidAccuracyLog al) :=
  inferInstanceAs (Decidable (5 ≤ al ∧ al ≤ 9))

/-- Compute the total cell count from a probability distribution.
    Positive probabilities contribute their value; -1 probabilities
    (indicating "less than 1") each contribute 1 cell. Zero entries
    contribute nothing. This matches the counting logic in
    `decodeFseDistribution` where `remaining` starts at `1 << accuracyLog`
    and is decremented by each positive probability or by 1 for each
    -1 probability. -/
def cellCount (dist : Array Int32) : Nat :=
  dist.foldl (fun acc p =>
    if p.toInt > 0 then acc + p.toInt.toNat
    else if p == -1 then acc + 1
    else acc) 0

/-- A probability distribution is valid for a given accuracy log when:
    (a) all probabilities are ≥ -1,
    (b) the total cell count (positive probs summed + count of -1 entries)
        equals the table size `1 << accuracyLog`, and
    (c) at least one symbol has positive probability. -/
def ValidDistribution (dist : Array Int32) (accuracyLog : Nat) : Prop :=
  (∀ i : Fin dist.size, dist[i].toInt ≥ -1) ∧
  cellCount dist = 1 <<< accuracyLog ∧
  (∃ i : Fin dist.size, dist[i].toInt > 0)

instance {dist : Array Int32} {accuracyLog : Nat} :
    Decidable (ValidDistribution dist accuracyLog) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- An FSE decoding table satisfies structural invariants when:
    (a) its size equals `1 << accuracyLog`,
    (b) all symbol indices are less than `numSymbols`, and
    (c) all `numBits` values are at most `accuracyLog`. -/
def ValidFseTable (table : Array FseCell) (accuracyLog : Nat)
    (numSymbols : Nat) : Prop :=
  table.size = 1 <<< accuracyLog ∧
  (∀ i : Fin table.size, table[i].symbol.toNat < numSymbols) ∧
  (∀ i : Fin table.size, table[i].numBits.toNat ≤ accuracyLog)

instance {table : Array FseCell} {accuracyLog numSymbols : Nat} :
    Decidable (ValidFseTable table accuracyLog numSymbols) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-! ## cellCount helper lemmas -/

/-- cellCount of a push reduces to a single if-then-else. -/
theorem cellCount_push (dist : Array Int32) (p : Int32) :
    cellCount (dist.push p) =
      if p.toInt > 0 then cellCount dist + p.toInt.toNat
      else if p == -1 then cellCount dist + 1
      else cellCount dist := by
  simp only [cellCount, gt_iff_lt, Int32.toNat_toInt, beq_iff_eq, Array.size_push,
    Array.foldl_push']

@[simp] theorem cellCount_push_zero (dist : Array Int32) :
    cellCount (dist.push 0) = cellCount dist := by
  rw [cellCount_push]
  simp only [show ¬((0 : Int32).toInt > 0) from by decide,
    show ((0 : Int32) == -1) = false from by decide, ↓reduceIte, Bool.false_eq_true]

@[simp] theorem cellCount_empty : cellCount #[] = 0 := by
  simp only [cellCount, List.foldl_toArray', List.foldl_nil]

/-! ## Loop invariant lemmas for decodeFseDistribution -/

open Zip.Native in
/-- Pushing zeros preserves `cellCount`. -/
theorem pushZeros_cellCount (probs : Array Int32) (sym n ms : Nat) :
    cellCount (pushZeros probs sym n ms).1 = cellCount probs := by
  induction n generalizing probs sym with
  | zero => rfl
  | succ n ih =>
    unfold pushZeros
    split
    · rw [ih]; exact cellCount_push_zero probs
    · rfl

open Zip.Native in
/-- The zero-repeat inner loop only pushes zeros, so `cellCount` is preserved. -/
theorem decodeZeroRepeats_cellCount
    {br : BitReader} {probs : Array Int32} {sym ms fuel : Nat}
    {probs' : Array Int32} {sym' : Nat} {br' : BitReader}
    (h : decodeZeroRepeats br probs sym ms fuel = .ok (probs', sym', br')) :
    cellCount probs' = cellCount probs := by
  induction fuel generalizing br probs sym with
  | zero => simp only [decodeZeroRepeats, reduceCtorEq] at h
  | succ fuel ih =>
    unfold decodeZeroRepeats at h
    dsimp only [Bind.bind, Except.bind] at h
    cases hrb : br.readBits 2 with
    | error e => rw [hrb] at h; dsimp only [Bind.bind, Except.bind] at h; exact nomatch h
    | ok val =>
      rw [hrb] at h; dsimp only [Bind.bind, Except.bind] at h
      split at h
      · -- repeatCount == 3, recursive call
        have hpc := pushZeros_cellCount probs sym val.1.toNat ms
        rw [ih h, hpc]
      · -- repeatCount != 3, done
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, _, _⟩ := h
        exact pushZeros_cellCount probs sym val.1.toNat ms

open Zip.Native in
/-- Main loop invariant: `remaining + cellCount probs` is preserved across
    all iterations of `decodeFseLoop`. -/
theorem decodeFseLoop_invariant
    {br : BitReader} {rem : Nat} {probs : Array Int32}
    {sym ms : Nat} {fuel : Nat}
    {rem' : Nat} {probs' : Array Int32} {sym' : Nat} {br' : BitReader}
    (h : decodeFseLoop br rem probs sym ms fuel = .ok (rem', probs', sym', br')) :
    rem' + cellCount probs' = rem + cellCount probs := by
  induction fuel generalizing br rem probs sym with
  | zero => simp only [decodeFseLoop, reduceCtorEq] at h
  | succ fuel ih =>
    -- Use equation lemma to unfold one level (no do-notation artifacts)
    rw [decodeFseLoop.eq_2] at h
    -- Split on loop exit condition
    by_cases hcond : ¬(rem > 0 ∧ sym < ms)
    · -- Loop exits: return unchanged state
      rw [if_pos hcond] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, _, _⟩ := h; rfl
    · -- Loop continues
      rw [if_neg hcond] at h
      -- Split on readProbValue
      cases hrpv : readProbValue br rem with
      | error e => simp only [hrpv, reduceCtorEq] at h
      | ok val =>
        simp only [hrpv] at h
        -- Split on prob == 0
        by_cases hp0 : (Int32.ofNat val.fst - 1 == 0) = true
        · rw [if_pos hp0] at h
          -- Zero probability: split on decodeZeroRepeats
          cases hzr : decodeZeroRepeats val.2 (probs.push 0) (sym + 1) ms 1000 with
          | error e => simp only [hzr, reduceCtorEq] at h
          | ok val₂ =>
            simp only [hzr] at h
            rw [ih h, decodeZeroRepeats_cellCount hzr, cellCount_push_zero]
        · rw [if_neg hp0] at h
          -- Split on prob == -1
          by_cases hp1 : (Int32.ofNat val.fst - 1 == -1) = true
          · rw [if_pos hp1] at h
            rw [ih h, cellCount_push, eq_of_beq hp1]
            simp only [show ((-1 : Int32).toInt > 0) = False from by decide,
                        show ((-1 : Int32) == -1) = true from by decide,
                        ↓reduceIte]
            omega
          · rw [if_neg hp1] at h
            -- Split on probNat > remaining
            by_cases hgt : int32ToNat (Int32.ofNat val.fst - 1) > rem
            · rw [if_pos hgt] at h; exact nomatch h
            · rw [if_neg hgt] at h
              rw [ih h, cellCount_push]
              by_cases hpos : (Int32.ofNat val.fst - 1).toInt > 0
              · rw [if_pos hpos]
                simp only [int32ToNat, show ¬(Int32.ofNat val.fst - 1).toInt < 0 from by omega,
                            ↓reduceIte] at hgt ⊢
                omega
              · rw [if_neg hpos, if_neg hp1]
                simp only [int32ToNat]
                split <;> omega

/-! ## Probability bound invariant: all probs ≥ -1 -/

/-- Pushing a value with `.toInt ≥ -1` preserves the `∀ i, arr[i].toInt ≥ -1` property. -/
private theorem push_preserves_ge_neg1
    {arr : Array Int32} {v : Int32}
    (hall : ∀ i : Fin arr.size, arr[i].toInt ≥ -1)
    (hv : v.toInt ≥ -1) :
    ∀ i : Fin (arr.push v).size, (arr.push v)[i].toInt ≥ -1 := by
  intro ⟨i, hi⟩
  simp only [Array.size_push] at hi
  by_cases hlt : i < arr.size
  · show (arr.push v)[i].toInt ≥ -1
    simp only [Array.getElem_push_lt (h := hlt)]
    exact hall ⟨i, hlt⟩
  · have heq : i = arr.size := by omega
    subst heq
    show (arr.push v)[arr.size].toInt ≥ -1
    rw [Array.getElem_push_eq]; exact hv

open Zip.Native in
/-- `pushZeros` only pushes `0`, so `∀ i, probs[i].toInt ≥ -1` is preserved. -/
theorem pushZeros_probs_ge_neg1 (probs : Array Int32) (sym n ms : Nat)
    (hbase : ∀ i : Fin probs.size, probs[i].toInt ≥ -1) :
    ∀ i : Fin (pushZeros probs sym n ms).1.size,
      (pushZeros probs sym n ms).1[i].toInt ≥ -1 := by
  induction n generalizing probs sym with
  | zero => exact hbase
  | succ n ih =>
    change ∀ i : Fin (if sym < ms then pushZeros (probs.push 0) (sym + 1) n ms
        else (probs, sym)).1.size,
      (if sym < ms then pushZeros (probs.push 0) (sym + 1) n ms
        else (probs, sym)).1[i].toInt ≥ -1
    intro ⟨i, hi⟩
    by_cases hsym : sym < ms
    · simp only [if_pos hsym] at hi ⊢
      exact ih _ _ (push_preserves_ge_neg1 hbase (by decide)) ⟨i, hi⟩
    · simp only [if_neg hsym] at hi ⊢
      exact hbase ⟨i, hi⟩

open Zip.Native in
/-- `decodeZeroRepeats` only pushes zeros, so `∀ i, probs[i].toInt ≥ -1` is preserved. -/
theorem decodeZeroRepeats_probs_ge_neg1
    {br : BitReader} {probs : Array Int32} {sym ms fuel : Nat}
    {probs' : Array Int32} {sym' : Nat} {br' : BitReader}
    (h : decodeZeroRepeats br probs sym ms fuel = .ok (probs', sym', br'))
    (hbase : ∀ i : Fin probs.size, probs[i].toInt ≥ -1) :
    ∀ i : Fin probs'.size, probs'[i].toInt ≥ -1 := by
  induction fuel generalizing br probs sym with
  | zero => simp only [decodeZeroRepeats, reduceCtorEq] at h
  | succ fuel ih =>
    unfold decodeZeroRepeats at h
    dsimp only [Bind.bind, Except.bind] at h
    cases hrb : br.readBits 2 with
    | error e => rw [hrb] at h; dsimp only [Bind.bind, Except.bind] at h; exact nomatch h
    | ok val =>
      rw [hrb] at h; dsimp only [Bind.bind, Except.bind] at h
      have hpz := pushZeros_probs_ge_neg1 probs sym val.1.toNat ms hbase
      split at h
      · exact ih h hpz
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, _, _⟩ := h
        exact hpz

/-- `readBit` returns a value that is 0 or 1, since it masks with `&&& 1`. -/
private theorem readBit_value_lt_2 {br : Zip.Native.BitReader} {val : UInt32}
    {br' : Zip.Native.BitReader}
    (h : br.readBit = .ok (val, br')) : val.toNat < 2 := by
  unfold Zip.Native.BitReader.readBit at h
  split at h
  · exact nomatch h
  · dsimp only at h
    split at h <;> (obtain ⟨rfl, _⟩ := Prod.mk.inj (Except.ok.inj h))
    all_goals
      simp only [UInt32.toNat_and, UInt32.toNat_ofNat]
      exact Nat.lt_of_le_of_lt Nat.and_le_right (by omega)

/-- The inner accumulation loop of forward `BitReader.readBits` produces
    a value less than `2^(shift + k)` when the accumulator starts below `2^shift`.
    Each step OR's a single bit at position `shift + i`, preserving the bound. -/
private theorem readBits_go_value_lt_pow2 (br : Zip.Native.BitReader)
    (k shift : Nat) (acc val : UInt32) (br' : Zip.Native.BitReader)
    (hacc : acc.toNat < 2 ^ shift)
    (hshift : shift + k ≤ 32)
    (h : Zip.Native.BitReader.readBits.go br acc shift k = .ok (val, br')) :
    val.toNat < 2 ^ (shift + k) := by
  induction k generalizing br acc shift with
  | zero =>
    simp only [Zip.Native.BitReader.readBits.go] at h
    obtain ⟨rfl, _⟩ := Prod.mk.inj (Except.ok.inj h)
    simpa only [Nat.add_zero] using hacc
  | succ k ih =>
    simp only [Zip.Native.BitReader.readBits.go, bind, Except.bind] at h
    cases hrb : br.readBit with
    | error e => rw [hrb] at h; exact nomatch h
    | ok bv =>
      rw [hrb] at h
      rw [show shift + (k + 1) = shift + 1 + k from by omega]
      refine ih _ _ _ ?_ (by omega) h
      -- acc' = acc ||| (bit <<< shift), need acc'.toNat < 2^(shift + 1)
      have hbit : bv.1.toNat < 2 := readBit_value_lt_2 hrb
      rw [UInt32.toNat_or]
      apply Nat.or_lt_two_pow
      · calc acc.toNat < 2 ^ shift := hacc
          _ ≤ 2 ^ (shift + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      · simp only [UInt32.toNat_shiftLeft, Nat.shiftLeft_eq]
        have hmod32 : shift.toUInt32.toNat % 32 = shift := by
          change (BitVec.ofNat 32 shift).toNat % 32 = shift
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : shift < 2 ^ 32)]
          exact Nat.mod_eq_of_lt (by omega : shift < 32)
        rw [hmod32]
        calc bv.1.toNat * 2 ^ shift % 2 ^ 32
            ≤ bv.1.toNat * 2 ^ shift := Nat.mod_le _ _
          _ < 2 * 2 ^ shift := (Nat.mul_lt_mul_right (Nat.pow_pos (by omega))).mpr hbit
          _ = 2 ^ (shift + 1) := by rw [Nat.pow_succ, Nat.mul_comm]

open Zip.Native in
/-- Reading `n` bits from a forward bitstream produces a value less than `2^n`,
    provided `n ≤ 32`. -/
theorem fwd_readBits_value_lt_pow2 (br : BitReader) (n : Nat) (val : UInt32)
    (br' : BitReader) (hn : n ≤ 32)
    (h : br.readBits n = .ok (val, br')) :
    val.toNat < 2 ^ n := by
  simp only [BitReader.readBits] at h
  have := readBits_go_value_lt_pow2 br n 0 0 val br'
    (by simp only [UInt32.toNat_zero]; omega) (by omega) h
  simpa only [Nat.zero_add] using this

open Zip.Native in
/-- `readProbValue` returns a value ≤ `remaining + 1`. This follows from the
    variable-length encoding structure: all decoded values are at most
    `maxVal = remaining + 1`. -/
theorem readProbValue_le {br : BitReader} {remaining : Nat}
    {val : Nat} {br' : BitReader}
    (h : readProbValue br remaining = .ok (val, br'))
    (hrem : remaining < 2 ^ 31) :
    val ≤ remaining + 1 := by
  simp only [readProbValue, bind, Except.bind, pure, Except.pure] at h
  cases hrb : br.readBits (Nat.log2 (remaining + 1) + 1 - 1) with
  | error e => simp only [hrb, reduceCtorEq] at h
  | ok rawVal =>
    simp only [hrb] at h
    have hlog_le : Nat.log2 (remaining + 1) + 1 - 1 ≤ 32 := by
      have : Nat.log2 (remaining + 1) < 32 := (Nat.log2_lt (by omega)).mpr (by omega)
      omega
    have hraw := fwd_readBits_value_lt_pow2 br _ rawVal.1 rawVal.2 hlog_le hrb
    simp only [Nat.add_sub_cancel] at hraw
    -- hraw : rawVal.fst.toNat < 2 ^ Nat.log2 (remaining + 1)
    -- Convert 1 <<< k to 2 ^ k in all hypotheses before case split
    have hshift : ∀ k, 1 <<< k = 2 ^ k := fun k => by
      simp only [Nat.shiftLeft_eq, Nat.one_mul]
    simp only [hshift, Nat.add_sub_cancel, Nat.pow_succ] at *
    -- Establish 2^L ≤ remaining + 1 for all cases
    have hle_p : 2 ^ Nat.log2 (remaining + 1) ≤ remaining + 1 :=
      Nat.log2_self_le (by omega)
    split at h
    · -- rawBits < lowThreshold: returns rawBits
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      -- rawBits < 2^L ≤ remaining + 1 → rawBits ≤ remaining
      have := Nat.lt_of_lt_of_le hraw hle_p
      omega
    · -- rawBits ≥ lowThreshold: reads extra bit
      cases hrb2 : rawVal.2.readBits 1 with
      | error e => simp only [hrb2, reduceCtorEq] at h
      | ok extraVal =>
        simp only [hrb2] at h
        split at h
        · -- extraBit == 0: returns rawBits
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, _⟩ := h
          have := Nat.lt_of_lt_of_le hraw hle_p
          omega
        · -- extraBit == 1: returns rawBits + threshold - lowThreshold
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, _⟩ := h
          have hlt_2p : remaining + 1 < 2 ^ (Nat.log2 (remaining + 1) + 1) := Nat.lt_log2_self
          simp only [Nat.pow_succ] at *
          generalize 2 ^ Nat.log2 (remaining + 1) = p at *
          omega

/-- `Int32.ofNat n - 1` has `.toInt ≥ -1` when `n < 2^31`. -/
private theorem int32_ofNat_sub_one_ge_neg1 {n : Nat} (hn : n < 2 ^ 31) :
    (Int32.ofNat n - 1).toInt ≥ -1 := by
  by_cases h0 : n = 0
  · subst h0; decide
  · -- Reduce to BitVec level: Int32/UInt32 subtraction is definitionally BitVec subtraction
    change (BitVec.ofNat 32 n - BitVec.ofNat 32 1).toInt ≥ -1
    simp only [BitVec.toInt, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega

open Zip.Native in
/-- Main loop preserves `∀ i, probs[i].toInt ≥ -1`: each case either pushes
    `0` (via decodeZeroRepeats), `-1`, or `Int32.ofNat val - 1` where
    `Int32.ofNat val ≥ 0` (guaranteed by `rem < 2^31` and `readProbValue_le`).
    The precondition `rem < 2^31` is satisfied by all Zstd FSE distributions
    (accuracy log ≤ 9, so remaining ≤ 512). -/
theorem decodeFseLoop_probs_ge_neg1
    {br : BitReader} {rem : Nat} {probs : Array Int32}
    {sym ms fuel : Nat}
    {rem' : Nat} {probs' : Array Int32} {sym' : Nat} {br' : BitReader}
    (h : decodeFseLoop br rem probs sym ms fuel = .ok (rem', probs', sym', br'))
    (hbase : ∀ i : Fin probs.size, probs[i].toInt ≥ -1)
    (hrem : rem + 1 < 2 ^ 31) :
    ∀ i : Fin probs'.size, probs'[i].toInt ≥ -1 := by
  induction fuel generalizing br rem probs sym with
  | zero => simp only [decodeFseLoop, reduceCtorEq] at h
  | succ fuel ih =>
    rw [decodeFseLoop.eq_2] at h
    by_cases hcond : ¬(rem > 0 ∧ sym < ms)
    · rw [if_pos hcond] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl, _, _⟩ := h; exact hbase
    · rw [if_neg hcond] at h
      cases hrpv : readProbValue br rem with
      | error e => simp only [hrpv, reduceCtorEq] at h
      | ok val =>
        simp only [hrpv] at h
        have hval_le := readProbValue_le hrpv (by omega)
        by_cases hp0 : (Int32.ofNat val.fst - 1 == 0) = true
        · rw [if_pos hp0] at h
          cases hzr : decodeZeroRepeats val.2 (probs.push 0) (sym + 1) ms 1000 with
          | error e => simp only [hzr, reduceCtorEq] at h
          | ok val₂ =>
            simp only [hzr] at h
            have hpush := push_preserves_ge_neg1 hbase (show (0 : Int32).toInt ≥ -1 from by decide)
            exact ih h (decodeZeroRepeats_probs_ge_neg1 hzr hpush) (by omega)
        · rw [if_neg hp0] at h
          by_cases hp1 : (Int32.ofNat val.fst - 1 == -1) = true
          · rw [if_pos hp1] at h
            exact ih h (push_preserves_ge_neg1 hbase (by simp [eq_of_beq hp1])) (by omega)
          · rw [if_neg hp1] at h
            by_cases hgt : int32ToNat (Int32.ofNat val.fst - 1) > rem
            · rw [if_pos hgt] at h; exact nomatch h
            · rw [if_neg hgt] at h
              have hv : (Int32.ofNat val.fst - 1).toInt ≥ -1 :=
                int32_ofNat_sub_one_ge_neg1 (by omega)
              exact ih h (push_preserves_ge_neg1 hbase hv) (by omega)

/-! ## Correctness of predefined distributions -/

open Zip.Native in
/-- The predefined literal length distribution is valid for accuracy log 6. -/
theorem predefined_litLen_valid :
    ValidDistribution predefinedLitLenDistribution 6 := by decide

open Zip.Native in
/-- The predefined match length distribution is valid for accuracy log 6. -/
theorem predefined_matchLen_valid :
    ValidDistribution predefinedMatchLenDistribution 6 := by decide

open Zip.Native in
/-- The predefined offset distribution is valid for accuracy log 5. -/
theorem predefined_offset_valid :
    ValidDistribution predefinedOffsetDistribution 5 := by decide

/-! ## Correctness of `decodeFseDistribution`

These theorems relate the output of `decodeFseDistribution` to the
validity predicates defined above. -/

open Zip.Native in
/-- Decomposition of a successful `decodeFseDistribution` call. Extracts
    the readBits(4) result, the accuracy log relation, the maxAccLog bound,
    and the decodeFseLoop result with remaining = 0. -/
private theorem decodeFseDistribution_ok_decompose
    {br : BitReader} {maxSymbols maxAccLog : Nat}
    {probs : Array Int32} {al : Nat} {br' : BitReader}
    (h : decodeFseDistribution br maxSymbols maxAccLog = .ok (probs, al, br')) :
    ∃ (rdval : UInt32 × BitReader) (sym' : Nat),
      br.readBits 4 = .ok rdval ∧
      al = rdval.1.toNat + 5 ∧
      al ≤ maxAccLog ∧
      decodeFseLoop rdval.2 (1 <<< al) #[] 0 maxSymbols 10000 =
        .ok (0, probs, sym', br') := by
  unfold decodeFseDistribution at h
  cases hrd : br.readBits 4 with
  | error e => simp only [hrd, reduceCtorEq] at h
  | ok val =>
    simp only [hrd] at h
    by_cases hgt : val.fst.toNat + 5 > maxAccLog
    · rw [if_pos hgt] at h; exact nomatch h
    · rw [if_neg hgt] at h
      cases hdl : decodeFseLoop val.snd (1 <<< (val.fst.toNat + 5)) #[] 0 maxSymbols 10000 with
      | error e => simp only [hdl, reduceCtorEq] at h
      | ok dlval =>
        simp only [hdl] at h
        by_cases hrem : dlval.1 != 0
        · rw [if_pos hrem] at h; exact nomatch h
        · rw [if_neg hrem] at h
          simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hrem
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          refine ⟨val, dlval.2.2.1, rfl, h.2.1.symm, by omega, ?_⟩
          rw [h.2.1.symm, hdl]; congr 1
          exact Prod.ext hrem (Prod.ext h.1 (Prod.ext rfl h.2.2))

open Zip.Native in
/-- When `decodeFseDistribution` succeeds, the returned accuracy log is
    at least 5. This follows from the computation `accuracyLog = readBits(4) + 5`
    where `readBits(4)` returns a non-negative value. -/
theorem decodeFseDistribution_accuracyLog_ge
    {br : BitReader} {maxSymbols maxAccLog : Nat}
    {probs : Array Int32} {al : Nat} {br' : BitReader}
    (_h : decodeFseDistribution br maxSymbols maxAccLog = .ok (probs, al, br')) :
    5 ≤ al := by
  obtain ⟨_, _, _, hal, _, _⟩ := decodeFseDistribution_ok_decompose _h; omega

open Zip.Native in
/-- When `decodeFseDistribution` succeeds, the returned accuracy log does
    not exceed `maxAccLog`. This follows from the guard
    `if accuracyLog > maxAccLog then throw ...`. -/
theorem decodeFseDistribution_accuracyLog_le
    {br : BitReader} {maxSymbols maxAccLog : Nat}
    {probs : Array Int32} {al : Nat} {br' : BitReader}
    (_h : decodeFseDistribution br maxSymbols maxAccLog = .ok (probs, al, br')) :
    al ≤ maxAccLog := by
  obtain ⟨_, _, _, _, hle, _⟩ := decodeFseDistribution_ok_decompose _h; exact hle

open Zip.Native in
/-- When `decodeFseDistribution` succeeds, the cell count of the returned
    distribution equals `1 << al`. This follows from the `remaining == 0`
    check at the end of the function: `remaining` starts at `1 << al` and
    is decremented by each probability value. -/
theorem decodeFseDistribution_sum_correct
    {br : BitReader} {maxSymbols maxAccLog : Nat}
    {probs : Array Int32} {al : Nat} {br' : BitReader}
    (_h : decodeFseDistribution br maxSymbols maxAccLog = .ok (probs, al, br')) :
    cellCount probs = 1 <<< al := by
  obtain ⟨_, _, _, _, _, hdl⟩ := decodeFseDistribution_ok_decompose _h
  have hinv := decodeFseLoop_invariant hdl
  simp only [cellCount_empty, Nat.add_zero] at hinv; omega

open Zip.Native in
/-- When `decodeFseDistribution` succeeds, the returned probability array is
    non-empty. This follows from `cellCount probs = 1 <<< al` (sum_correct)
    and `al ≥ 5` (accuracyLog_ge): an empty array has cellCount 0, but
    `1 <<< al ≥ 32 > 0`. -/
theorem decodeFseDistribution_size_pos
    {br : BitReader} {maxSymbols maxAccLog : Nat}
    {probs : Array Int32} {al : Nat} {br' : BitReader}
    (h : decodeFseDistribution br maxSymbols maxAccLog = .ok (probs, al, br')) :
    0 < probs.size := by
  have hcc := decodeFseDistribution_sum_correct h
  have hal := decodeFseDistribution_accuracyLog_ge h
  have hne : probs.size ≠ 0 := by
    intro hsz
    have : probs = #[] := Array.ext (by simp [hsz]) (fun i h1 _ => absurd h1 (by omega))
    rw [this, cellCount_empty, Nat.shiftLeft_eq] at hcc
    have := Nat.two_pow_pos al; omega
  omega

/-! ## Structural properties of `buildFseTable` -/

/-- If `x >>= f = .ok b`, then `x` succeeded and `f` maps its result to `.ok b`. -/
private theorem Except.bind_eq_ok' {α β ε : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = Except.ok b) : ∃ a, x = Except.ok a ∧ f a = Except.ok b := by
  cases x with
  | error e => simp only [bind, Except.bind, reduceCtorEq] at h
  | ok a => exact ⟨a, rfl, h⟩

/-- `List.forIn'.loop` in `Except` preserves a predicate when the body preserves it
    on both `.yield` and `.done` outcomes. Error outcomes are handled by the hypothesis
    that the overall loop succeeded. The body must ignore the membership proof. -/
private theorem forIn'_loop_preserves {α β ε : Type}
    (P : β → Prop) (as curr : List α) (init result : β)
    (f : α → β → Except ε (ForInStep β))
    (h_init : P init)
    (h_yield : ∀ a b b', P b → f a b = .ok (.yield b') → P b')
    (h_done : ∀ a b b', P b → f a b = .ok (.done b') → P b')
    (hsuf : ∃ bs, bs ++ curr = as)
    (h_result : List.forIn'.loop as (fun a _ b => f a b) curr init hsuf = .ok result) :
    P result := by
  induction curr generalizing init with
  | nil =>
    unfold List.forIn'.loop at h_result
    dsimp only [pure, Except.pure] at h_result
    rw [← Except.ok.inj h_result]; exact h_init
  | cons x xs ih =>
    unfold List.forIn'.loop at h_result
    dsimp only [Bind.bind, Except.bind] at h_result
    cases hfx : f x init with
    | error e => rw [hfx] at h_result; exact nomatch h_result
    | ok step =>
      rw [hfx] at h_result
      cases step with
      | done b' =>
        dsimp only [pure, Except.pure] at h_result
        rw [← Except.ok.inj h_result]; exact h_done x init b' h_init hfx
      | yield b' =>
        exact ih b' (h_yield x init b' h_init hfx) _ h_result

open Zip.Native in
/-- When `buildFseTable` succeeds, the returned accuracy log equals the input.
    This follows from the return statement `{ accuracyLog, cells }` where
    `accuracyLog` is the input parameter unchanged. -/
theorem buildFseTable_accuracyLog_eq (probs : Array Int32) (al : Nat)
    (table : FseTable) (h : buildFseTable probs al = .ok table) :
    table.accuracyLog = al := by
  simp only [buildFseTable, bind, Except.bind, pure, Except.pure] at h
  -- grind handles case-splitting through the unfolded if/match/forIn branches,
  -- extracting `table.accuracyLog = al` from each successful return path
  grind

private theorem forIn_range_preserves {β ε : Type}
    (P : β → Prop) (n : Nat) (init result : β)
    (f : Nat → β → Except ε (ForInStep β))
    (h_init : P init)
    (h_yield : ∀ a b b', P b → f a b = .ok (.yield b') → P b')
    (h_done : ∀ a b b', P b → f a b = .ok (.done b') → P b')
    (h_result : forIn [:n] init f = .ok result) :
    P result := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at h_result
  exact forIn'_loop_preserves P _ _ init result f h_init h_yield h_done _ h_result

open Zip.Native in
/-- When `buildFseTable` succeeds, the returned cells array has size `1 <<< al`.
    This follows from `Array.replicate` setting the initial size and `Array.set!`
    preserving size through all loop iterations. -/
theorem buildFseTable_cells_size (probs : Array Int32) (al : Nat)
    (table : FseTable) (h : buildFseTable probs al = .ok table) :
    table.cells.size = 1 <<< al := by
  simp only [buildFseTable] at h
  -- Decompose the do-notation bind chain into individual loop equations
  obtain ⟨v1, hloop1, h⟩ := Except.bind_eq_ok' h
  obtain ⟨v2, hloop2, h⟩ := Except.bind_eq_ok' h
  obtain ⟨v3, hloop3, h⟩ := Except.bind_eq_ok' h
  obtain ⟨v4, hloop4, h⟩ := Except.bind_eq_ok' h
  simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
  -- Thread cells size invariant: replicate → loop1 → loop2 → loop4
  -- (loop3 only modifies symbolCounts, not cells)
  -- Loop 1 (place -1 probability symbols): cells.set! preserves size
  have hsize1 : v1.fst.size = 1 <<< al := by
    apply forIn_range_preserves (fun s => s.fst.size = 1 <<< al) _ _ _ _ _ _ _ hloop1
    · exact Array.size_replicate
    · intro a b b' hb heq
      simp only [bind, Except.bind, pure, Except.pure] at heq
      split at heq
      · split at heq
        · rw [← ForInStep.yield.inj (Except.ok.inj heq)]
          simp only [Nat.toUInt16_eq, Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, hb]
        · rw [← ForInStep.yield.inj (Except.ok.inj heq)]; exact hb
      · rw [← ForInStep.yield.inj (Except.ok.inj heq)]; exact hb
    · intro a b b' hb heq
      simp only [bind, Except.bind, pure, Except.pure] at heq
      split at heq <;> (try split at heq) <;> exact nomatch heq
  -- Loop 2 (distribute symbols with stepping): cells.set! preserves size
  have hsize2 : v2.fst.size = 1 <<< al := by
    apply forIn_range_preserves (fun s => s.fst.size = 1 <<< al) _ _ _ _ _ _ _ hloop2
    · exact hsize1
    · intro a b b' hb heq
      simp only [bind, Except.bind, pure, Except.pure] at heq
      split at heq
      · -- if h_sym : sym < probs.size
        split at heq
        · rw [← ForInStep.yield.inj (Except.ok.inj heq)]; exact hb
        · -- Inner forIn with while loop
          split at heq
          · exact nomatch heq
          · rename_i r hinner
            rw [← ForInStep.yield.inj (Except.ok.inj heq)]; dsimp only
            apply forIn_range_preserves (fun s => s.fst.size = 1 <<< al) _ _ _ _ _ _ _ hinner
            · exact hb
            · intro a2 b2 b2' hb2 heq2
              rw [← ForInStep.yield.inj (Except.ok.inj heq2)]
              simp only [Nat.toUInt16_eq, Array.set!_eq_setIfInBounds,
                Array.size_setIfInBounds, hb2]
            · intro a2 b2 b2' hb2 heq2
              exact nomatch heq2
      · -- h_sym doesn't hold
        rw [← ForInStep.yield.inj (Except.ok.inj heq)]; exact hb
    · intro _ _ _ _ heq; simp only [bind, Except.bind, pure, Except.pure] at heq
      split at heq <;> (try split at heq) <;> (try split at heq) <;> exact nomatch heq
  -- Loop 4 (compute numBits/newState): cells.set! preserves size
  apply forIn_range_preserves (fun s => s.fst.size = 1 <<< al) _ _ _ _ _ _ _ hloop4
  · exact hsize2
  · intro a b b' hb heq
    simp only [bind, Except.bind, pure, Except.pure] at heq
    split at heq
    · -- if h_i : i < cells.size
      split at heq
      · -- if h_sc : sym < symbolCounts.size
        split at heq
        · -- if h_si : sym < symbolStateIndex.size
          split at heq
          · -- if count != 0
            rw [← ForInStep.yield.inj (Except.ok.inj heq)]
            simp only [Nat.toUInt8_eq, Nat.toUInt16_eq, Array.set!_eq_setIfInBounds,
              Array.size_setIfInBounds, hb]
          · -- count == 0
            rw [← ForInStep.yield.inj (Except.ok.inj heq)]; exact hb
        · rw [← ForInStep.yield.inj (Except.ok.inj heq)]; exact hb
      · rw [← ForInStep.yield.inj (Except.ok.inj heq)]; exact hb
    · -- h_i doesn't hold
      rw [← ForInStep.yield.inj (Except.ok.inj heq)]; exact hb
  · intro _ _ _ _ heq; simp only [bind, Except.bind, pure, Except.pure] at heq
    split at heq <;> (try split at heq) <;> (try split at heq) <;>
    (try split at heq) <;> exact nomatch heq

/-- `Array.set!` preserves a Fin-indexed property when the new value satisfies it.
    After `set!`, each cell is either the new value (at the written index) or
    unchanged from the original array. -/
private theorem set!_preserves_forall {P : FseCell → Prop}
    {cells : Array FseCell} {idx : Nat} {v : FseCell}
    (hall : ∀ j : Fin cells.size, P cells[j])
    (hv : P v) :
    ∀ j : Fin (cells.set! idx v).size, P (cells.set! idx v)[j] := by
  intro ⟨j, hj⟩
  simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds] at hj
  show P (cells.setIfInBounds idx v)[j]
  by_cases hij : idx = j
  · subst hij
    exact (Array.getElem_setIfInBounds_self (h := by
      simp only [Array.size_setIfInBounds]; exact hj)) ▸ hv
  · exact (Array.getElem_setIfInBounds_ne hj hij) ▸ hall ⟨j, hj⟩

open Zip.Native in
/-- When `buildFseTable` succeeds, every cell's `numBits` is at most `al`.
    This follows from the construction: loops 1-2 set cells with default
    `numBits = 0`, loop 3 doesn't modify cells, and loop 4 sets
    `numBits := (al - Nat.log2 nextState).toUInt8` where `al - x ≤ al`. -/
theorem buildFseTable_numBits_le (probs : Array Int32) (al : Nat)
    (table : FseTable) (h : buildFseTable probs al = .ok table)
    (i : Fin table.cells.size) :
    table.cells[i].numBits.toNat ≤ al := by
  simp only [buildFseTable] at h
  obtain ⟨v1, hloop1, h⟩ := Except.bind_eq_ok' h
  obtain ⟨v2, hloop2, h⟩ := Except.bind_eq_ok' h
  obtain ⟨v3, hloop3, h⟩ := Except.bind_eq_ok' h
  obtain ⟨v4, hloop4, h⟩ := Except.bind_eq_ok' h
  simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
  show v4.fst[i].numBits.toNat ≤ al
  -- The predicate P: cell.numBits.toNat ≤ al
  let P : FseCell → Prop := fun c => c.numBits.toNat ≤ al
  -- Initial cells: Array.replicate with default has numBits = 0
  have hinit : ∀ j : Fin (Array.replicate (1 <<< al) (default : FseCell)).size,
      P (Array.replicate (1 <<< al) (default : FseCell))[j] := by
    intro ⟨j, hj⟩; show P _
    simp only [Fin.getElem_fin, Array.getElem_replicate]; exact Nat.zero_le _
  -- Loop 1: preserves property (sets cells with { symbol := ... }, default numBits = 0)
  have h1 : ∀ j : Fin v1.fst.size, P v1.fst[j] := by
    apply forIn_range_preserves (fun s => ∀ j : Fin s.fst.size, P s.fst[j])
      _ _ _ _ hinit _ _ hloop1
    · intro a b b' hb heq
      simp only [bind, Except.bind, pure, Except.pure] at heq
      split at heq
      · split at heq
        · rw [← ForInStep.yield.inj (Except.ok.inj heq)]; dsimp only
          exact set!_preserves_forall hb (show P _ from Nat.zero_le _)
        · rw [← ForInStep.yield.inj (Except.ok.inj heq)]; exact hb
      · rw [← ForInStep.yield.inj (Except.ok.inj heq)]; exact hb
    · intro a b b' hb heq
      simp only [bind, Except.bind, pure, Except.pure] at heq
      split at heq <;> (try split at heq) <;> exact nomatch heq
  -- Loop 2: preserves property (sets cells with { symbol := ... }, default numBits = 0)
  have h2 : ∀ j : Fin v2.fst.size, P v2.fst[j] := by
    apply forIn_range_preserves (fun s => ∀ j : Fin s.fst.size, P s.fst[j])
      _ _ _ _ h1 _ _ hloop2
    · intro a b b' hb heq
      simp only [bind, Except.bind, pure, Except.pure] at heq
      split at heq
      · split at heq
        · rw [← ForInStep.yield.inj (Except.ok.inj heq)]; exact hb
        · split at heq
          · exact nomatch heq
          · rename_i r hinner
            rw [← ForInStep.yield.inj (Except.ok.inj heq)]; dsimp only
            apply forIn_range_preserves (fun s => ∀ j : Fin s.fst.size, P s.fst[j])
              _ _ _ _ hb _ _ hinner
            · intro a2 b2 b2' hb2 heq2
              rw [← ForInStep.yield.inj (Except.ok.inj heq2)]; dsimp only
              exact set!_preserves_forall hb2 (show P _ from Nat.zero_le _)
            · intro a2 b2 b2' hb2 heq2; exact nomatch heq2
      · rw [← ForInStep.yield.inj (Except.ok.inj heq)]; exact hb
    · intro _ _ _ _ heq; simp only [bind, Except.bind, pure, Except.pure] at heq
      split at heq <;> (try split at heq) <;> (try split at heq) <;> exact nomatch heq
  -- Loop 3 modifies only symbolCounts (v3 : Array Nat), not cells.
  -- Loop 4 starts with v2.fst as its initial cells.
  -- Loop 4: sets numBits := (al - Nat.log2 nextState).toUInt8
  -- The key bound: (al - x).toUInt8.toNat ≤ al
  have numBits_bound : ∀ x : Nat, (al - x).toUInt8.toNat ≤ al := by
    intro x
    simp only [Nat.toUInt8_eq, UInt8.toNat_ofNat']
    exact Nat.le_trans (Nat.mod_le _ _) (Nat.sub_le al x)
  apply forIn_range_preserves (fun s => ∀ j : Fin s.fst.size, P s.fst[j])
    _ _ _ _ h2 _ _ hloop4
  · intro a b b' hb heq
    simp only [bind, Except.bind, pure, Except.pure] at heq
    split at heq
    · -- if h_i : i < cells.size
      split at heq
      · -- if h_sc
        split at heq
        · -- if h_si
          split at heq
          · -- count != 0: set! with numBits bound
            rw [← ForInStep.yield.inj (Except.ok.inj heq)]; dsimp only
            exact set!_preserves_forall hb (numBits_bound _)
          · -- count == 0
            rw [← ForInStep.yield.inj (Except.ok.inj heq)]; exact hb
        · rw [← ForInStep.yield.inj (Except.ok.inj heq)]; exact hb
      · rw [← ForInStep.yield.inj (Except.ok.inj heq)]; exact hb
    · rw [← ForInStep.yield.inj (Except.ok.inj heq)]; exact hb
  · intro _ _ _ _ heq; simp only [bind, Except.bind, pure, Except.pure] at heq
    split at heq <;> (try split at heq) <;> (try split at heq) <;>
    (try split at heq) <;> exact nomatch heq

/-! ## BackwardBitReader base-case specs -/

open Zip.Native (BackwardBitReader) in
/-- `isFinished` is true iff `totalBitsRemaining` is zero. -/
theorem BackwardBitReader_isFinished_iff_totalBitsRemaining_zero
    (br : BackwardBitReader) :
    br.isFinished = true ↔ br.totalBitsRemaining = 0 := by
  simp only [BackwardBitReader.isFinished, BackwardBitReader.totalBitsRemaining]
  constructor
  · intro h; simp only [beq_iff_eq.mp h, BEq.rfl, ↓reduceIte]
  · intro h
    split at h
    · assumption
    · -- bitsRemaining + 8 * (bytePos - startPos) = 0 contradicts ¬(bitsRemaining == 0)
      rename_i hne
      simp only [beq_iff_eq, Nat.add_eq_zero_iff] at hne h
      exact absurd h.1 hne

open Zip.Native (BackwardBitReader) in
/-- Reading 0 bits is a no-op: returns (0, br) unchanged. -/
theorem readBits_zero (br : BackwardBitReader) :
    br.readBits 0 = .ok (0, br) := by
  simp only [BackwardBitReader.readBits, BackwardBitReader.readBits.go]

open Zip.Native (BackwardBitReader) in
/-- Reading n > 0 bits from a finished reader always errors. -/
theorem readBits_error_of_isFinished (br : BackwardBitReader) (n : Nat)
    (hn : n > 0) (hfin : br.isFinished = true) :
    ∃ e, br.readBits n = .error e := by
  match n, hn with
  | k + 1, _ =>
  simp only [BackwardBitReader.isFinished, beq_iff_eq] at hfin
  simp only [BackwardBitReader.readBits, BackwardBitReader.readBits.go, hfin]
  exact ⟨_, rfl⟩

/-! ## BackwardBitReader value bound -/

/-- Shifting a UInt32 left by 1 and OR-ing with a UInt8 masked to 1 bit
    produces a value less than `2^(m+1)` when the original is less than `2^m`. -/
private theorem uint32_shift_or_bit_bound (acc : UInt32) (byte : UInt8) (pos : UInt8)
    (m : Nat)
    (hacc : acc.toNat < 2 ^ m) :
    (acc <<< 1 ||| (byte >>> pos &&& 1).toUInt32).toNat < 2 ^ (m + 1) := by
  -- The result is always < 2^32, so if m+1 ≥ 32, the bound is trivial
  by_cases hm : m + 1 ≥ 32
  · calc (acc <<< 1 ||| (byte >>> pos &&& 1).toUInt32).toNat
        < 2 ^ 32 := UInt32.toNat_lt _
      _ ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by omega) hm
  · -- m + 1 < 32, so m ≤ 30 and the result fits in 31 bits
    have hm' : m ≤ 30 := by omega
    -- Split into components
    -- Use Nat.or_lt_two_pow: if both operands < 2^(m+1), their OR is too
    rw [UInt32.toNat_or]
    apply Nat.or_lt_two_pow
    · -- (acc <<< 1).toNat < 2^(m+1)
      simp only [UInt32.toNat_shiftLeft, Nat.shiftLeft_eq]
      have : (1 : UInt32).toNat % 32 = 1 := by decide
      rw [this, Nat.pow_one, Nat.mod_eq_of_lt]
      · rw [Nat.pow_succ]; omega
      · calc acc.toNat * 2
            < 2 ^ m * 2 := by omega
          _ = 2 ^ (m + 1) := by rw [Nat.pow_succ]
          _ ≤ 2 ^ 31 := Nat.pow_le_pow_right (by omega) (by omega)
          _ < 2 ^ 32 := by omega
    · -- (byte >>> pos &&& 1).toUInt32.toNat < 2^(m+1)
      simp only [UInt8.toNat_toUInt32, UInt8.toNat_and, UInt8.toNat_shiftRight,
        UInt8.reduceToNat, Nat.and_one_is_mod]
      omega

open Zip.Native (BackwardBitReader) in
/-- The inner loop of `readBits` maintains the value bound: if the accumulator
    starts below `2^(n-k)`, the final value is below `2^n`. -/
private theorem readBits_go_value_bound {n : Nat} (br : BackwardBitReader) (k : Nat)
    (acc : UInt32) (val : UInt32) (br' : BackwardBitReader)
    (hkn : k ≤ n)
    (hacc : acc.toNat < 2 ^ (n - k))
    (h : BackwardBitReader.readBits.go br k acc = .ok (val, br')) :
    val.toNat < 2 ^ n := by
  induction k generalizing br acc with
  | zero =>
    simp only [BackwardBitReader.readBits.go] at h
    obtain ⟨rfl, _⟩ := Prod.mk.inj (Except.ok.inj h)
    simpa only [Nat.sub_zero] using hacc
  | succ k ih =>
    simp only [BackwardBitReader.readBits.go, bind, Except.bind] at h
    split at h
    · exact nomatch h
    · simp only [pure, Except.pure] at h
      refine ih _ _ (by omega) ?_ h
      have hne : n - k = (n - (k + 1)) + 1 := by omega
      rw [hne]
      exact uint32_shift_or_bit_bound acc _ _ _ hacc

open Zip.Native (BackwardBitReader) in
/-- Reading `n` bits from a backward bitstream produces a value less than `2^n`. -/
theorem readBits_value_lt_pow2 (br : BackwardBitReader) (n : Nat)
    (val : UInt32) (br' : BackwardBitReader)
    (h : br.readBits n = .ok (val, br')) :
    val.toNat < 2 ^ n := by
  simp only [BackwardBitReader.readBits] at h
  exact readBits_go_value_bound br n 0 val br' (Nat.le_refl n) (by simp) h

/-! ## BackwardBitReader totalBitsRemaining tracking -/

open Zip.Native (BackwardBitReader) in
/-- The recursive helper `readBits.go` decreases `totalBitsRemaining` by exactly `k`. -/
private theorem readBits_go_totalBitsRemaining (br : BackwardBitReader)
    (k : Nat) (acc val : UInt32) (br' : BackwardBitReader)
    (h : BackwardBitReader.readBits.go br k acc = .ok (val, br')) :
    br'.totalBitsRemaining = br.totalBitsRemaining - k := by
  induction k generalizing br acc with
  | zero =>
    simp only [BackwardBitReader.readBits.go] at h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
    omega
  | succ k ih =>
    simp only [BackwardBitReader.readBits.go, bind, Except.bind] at h
    split at h
    · exact nomatch h
    · simp only [pure, Except.pure] at h
      rename_i hbr_ne; simp only [beq_iff_eq] at hbr_ne
      rw [ih _ _ h]
      simp only [BackwardBitReader.totalBitsRemaining, beq_iff_eq]
      by_cases h1 : br.bitsRemaining - 1 = 0 <;> by_cases h2 : br.bytePos > br.startPos <;>
        simp only [h1, h2, hbr_ne, show ¬((8 : Nat) = 0) from by omega, ↓reduceIte] <;> omega

open Zip.Native (BackwardBitReader) in
/-- When `readBits.go` succeeds, the initial reader had enough bits. -/
private theorem readBits_go_totalBitsRemaining_ge (br : BackwardBitReader)
    (k : Nat) (acc val : UInt32) (br' : BackwardBitReader)
    (h : BackwardBitReader.readBits.go br k acc = .ok (val, br')) :
    br.totalBitsRemaining ≥ k := by
  induction k generalizing br acc with
  | zero => omega
  | succ k ih =>
    simp only [BackwardBitReader.readBits.go, bind, Except.bind] at h
    split at h
    · exact nomatch h
    · simp only [pure, Except.pure] at h
      rename_i hbr_ne; simp only [beq_iff_eq] at hbr_ne
      have hrec := ih _ _ h
      simp only [BackwardBitReader.totalBitsRemaining, beq_iff_eq] at hrec ⊢
      by_cases h1 : br.bitsRemaining - 1 = 0 <;> by_cases h2 : br.bytePos > br.startPos <;>
        simp only [h1, h2, hbr_ne, show ¬((8 : Nat) = 0) from by omega, ↓reduceIte] at hrec ⊢
          <;> omega

open Zip.Native (BackwardBitReader) in
/-- Reading `n` bits from a backward bitstream decreases `totalBitsRemaining`
    by exactly `n`. -/
theorem readBits_totalBitsRemaining_sub (br : BackwardBitReader)
    (n : Nat) (val : UInt32) (br' : BackwardBitReader)
    (h : br.readBits n = .ok (val, br')) :
    br'.totalBitsRemaining = br.totalBitsRemaining - n := by
  simp only [BackwardBitReader.readBits] at h
  exact readBits_go_totalBitsRemaining br n 0 val br' h

open Zip.Native (BackwardBitReader) in
/-- When reading a positive number of bits succeeds, `totalBitsRemaining`
    strictly decreases. -/
theorem readBits_totalBitsRemaining_lt (br : BackwardBitReader)
    (n : Nat) (val : UInt32) (br' : BackwardBitReader)
    (hn : n > 0) (h : br.readBits n = .ok (val, br')) :
    br'.totalBitsRemaining < br.totalBitsRemaining := by
  simp only [BackwardBitReader.readBits] at h
  have hsub := readBits_go_totalBitsRemaining br n 0 val br' h
  have hge := readBits_go_totalBitsRemaining_ge br n 0 val br' h
  omega

/-! ## BackwardBitReader.init specs -/

open Zip.Native (BackwardBitReader) in
/-- When `highBitPos b = some p`, the position is less than 8. -/
private theorem highBitPos_lt_eight (b : UInt8) (p : Nat)
    (h : BackwardBitReader.highBitPos b = some p) : p < 8 := by
  unfold BackwardBitReader.highBitPos at h; grind

open Zip.Native (BackwardBitReader) in
/-- Successful `init` preserves the `startPos` argument. -/
theorem BackwardBitReader_init_startPos_eq (data : ByteArray)
    (startPos endPos : Nat) (br : BackwardBitReader)
    (h : BackwardBitReader.init data startPos endPos = .ok br) :
    br.startPos = startPos := by
  simp only [BackwardBitReader.init, bind, Except.bind, pure, Except.pure] at h
  split at h; · exact nomatch h
  split at h; · exact nomatch h
  split at h; · exact nomatch h
  split at h
  · split at h <;> (obtain rfl := Except.ok.inj h; rfl)
  · obtain rfl := Except.ok.inj h; rfl

open Zip.Native (BackwardBitReader) in
/-- The initial `totalBitsRemaining` is strictly less than `8 * (endPos - startPos)`.
    This is because the sentinel bit itself is consumed during initialization. -/
theorem BackwardBitReader_init_totalBitsRemaining_lt (data : ByteArray)
    (startPos endPos : Nat) (br : BackwardBitReader)
    (h : BackwardBitReader.init data startPos endPos = .ok br) :
    br.totalBitsRemaining < 8 * (endPos - startPos) := by
  simp only [BackwardBitReader.init, bind, Except.bind, pure, Except.pure] at h
  split at h
  · exact nomatch h
  · rename_i hle
    split at h
    · exact nomatch h
    · rename_i hsize
      split at h
      · exact nomatch h
      · rename_i sentinelPos
        split at h
        · rename_i hsp; simp only [beq_iff_eq] at hsp
          split at h <;> (obtain rfl := Except.ok.inj h) <;>
            simp only [BackwardBitReader.totalBitsRemaining, beq_iff_eq,
              show ¬(8 : Nat) = 0 from by omega, ↓reduceIte] <;> omega
        · rename_i hsp; simp only [beq_iff_eq] at hsp
          obtain rfl := Except.ok.inj h
          simp only [BackwardBitReader.totalBitsRemaining, beq_iff_eq, hsp, ↓reduceIte]
          have hlt := highBitPos_lt_eight _ _ ‹_›
          omega

/-! ## BackwardBitReader field preservation -/

open Zip.Native (BackwardBitReader) in
/-- The recursive helper `readBits.go` preserves the `data` field. -/
private theorem readBits_go_data_eq (br : BackwardBitReader)
    (k : Nat) (acc val : UInt32) (br' : BackwardBitReader)
    (h : BackwardBitReader.readBits.go br k acc = .ok (val, br')) :
    br'.data = br.data := by
  induction k generalizing br acc with
  | zero =>
    simp only [BackwardBitReader.readBits.go] at h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (Except.ok.inj h); rfl
  | succ k ih =>
    simp only [BackwardBitReader.readBits.go, bind, Except.bind] at h
    split at h; · exact nomatch h
    simp only [pure, Except.pure] at h; rw [ih _ _ h]
    split <;> (try split) <;> rfl

open Zip.Native (BackwardBitReader) in
/-- Reading `n` bits from a backward bitstream preserves the `data` field. -/
theorem readBits_data_eq (br : BackwardBitReader) (n : Nat)
    (val : UInt32) (br' : BackwardBitReader)
    (h : br.readBits n = .ok (val, br')) :
    br'.data = br.data := by
  simp only [BackwardBitReader.readBits] at h
  exact readBits_go_data_eq br n 0 val br' h

open Zip.Native (BackwardBitReader) in
/-- The recursive helper `readBits.go` preserves the `startPos` field. -/
private theorem readBits_go_startPos_eq (br : BackwardBitReader)
    (k : Nat) (acc val : UInt32) (br' : BackwardBitReader)
    (h : BackwardBitReader.readBits.go br k acc = .ok (val, br')) :
    br'.startPos = br.startPos := by
  induction k generalizing br acc with
  | zero =>
    simp only [BackwardBitReader.readBits.go] at h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (Except.ok.inj h); rfl
  | succ k ih =>
    simp only [BackwardBitReader.readBits.go, bind, Except.bind] at h
    split at h; · exact nomatch h
    simp only [pure, Except.pure] at h; rw [ih _ _ h]
    split <;> (try split) <;> rfl

open Zip.Native (BackwardBitReader) in
/-- Reading `n` bits from a backward bitstream preserves the `startPos` field. -/
theorem readBits_startPos_eq (br : BackwardBitReader) (n : Nat)
    (val : UInt32) (br' : BackwardBitReader)
    (h : br.readBits n = .ok (val, br')) :
    br'.startPos = br.startPos := by
  simp only [BackwardBitReader.readBits] at h
  exact readBits_go_startPos_eq br n 0 val br' h

open Zip.Native (BackwardBitReader) in
/-- Successful `init` sets the `data` field to the input data. -/
theorem BackwardBitReader_init_data_eq (data : ByteArray)
    (startPos endPos : Nat) (br : BackwardBitReader)
    (h : BackwardBitReader.init data startPos endPos = .ok br) :
    br.data = data := by
  simp only [BackwardBitReader.init, bind, Except.bind, pure, Except.pure] at h
  split at h; · exact nomatch h
  split at h; · exact nomatch h
  split at h; · exact nomatch h
  split at h
  · split at h <;> (obtain rfl := Except.ok.inj h; rfl)
  · obtain rfl := Except.ok.inj h; rfl

/-! ## BackwardBitReader.init completeness -/

open Zip.Native (BackwardBitReader) in
/-- When a byte is nonzero, `highBitPos` returns `some`. -/
theorem highBitPos_some_of_ne_zero (b : UInt8) (hb : b ≠ 0) :
    ∃ n, BackwardBitReader.highBitPos b = some n := by
  unfold BackwardBitReader.highBitPos
  simp only [bne_iff_ne, ne_eq, beq_iff_eq, hb, ↓reduceIte]
  repeat (first | exact ⟨_, rfl⟩ | split)

open Zip.Native (BackwardBitReader) in
/-- When `startPos < endPos`, `endPos ≤ data.size`, and the last byte is nonzero,
    `BackwardBitReader.init` succeeds. -/
theorem BackwardBitReader_init_succeeds (data : ByteArray)
    (startPos endPos : Nat)
    (hrange : startPos < endPos)
    (hsize : endPos ≤ data.size)
    (hlast : data[endPos - 1]! ≠ 0) :
    ∃ br, BackwardBitReader.init data startPos endPos = .ok br := by
  simp only [BackwardBitReader.init, bind, Except.bind, pure, Except.pure]
  rw [if_neg (by omega), if_neg (by omega)]
  obtain ⟨n, hn⟩ := highBitPos_some_of_ne_zero _ hlast
  simp only [hn]; split <;> (try split) <;> exact ⟨_, rfl⟩

/-! ## forIn always-ok lemmas -/

/-- `List.forIn'.loop` in `Except` always returns `.ok` when the body never throws. -/
private theorem forIn'_loop_always_ok {α β ε : Type}
    (as curr : List α) (init : β)
    (f : α → β → Except ε (ForInStep β))
    (h_ok : ∀ a b, ∃ r, f a b = .ok r)
    (hsuf : ∃ bs, bs ++ curr = as) :
    ∃ result, List.forIn'.loop as (fun a _ b => f a b) curr init hsuf = .ok result := by
  induction curr generalizing init with
  | nil =>
    unfold List.forIn'.loop
    exact ⟨init, rfl⟩
  | cons x xs ih =>
    unfold List.forIn'.loop
    dsimp only [Bind.bind, Except.bind]
    obtain ⟨r, hr⟩ := h_ok x init
    rw [hr]
    cases r with
    | done b' => exact ⟨b', rfl⟩
    | yield b' => exact ih b' _

/-- `forIn` over a range in `Except` always returns `.ok` when the body never throws. -/
private theorem forIn_range_always_ok {β ε : Type} (n : Nat) (init : β)
    (f : Nat → β → Except ε (ForInStep β))
    (h_ok : ∀ i b, ∃ r, f i b = .ok r) :
    ∃ result, forIn [:n] init f = .ok result := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact forIn'_loop_always_ok _ _ init (fun a b => f a b) h_ok _

/-! ## buildFseTable always succeeds -/

/-- If `x` always returns `.ok` and `f` always returns `.ok`, then `x >>= f`
    always returns `.ok`. -/
private theorem Except.bind_always_ok {α β ε : Type} {x : Except ε α}
    {f : α → Except ε β}
    (hx : ∃ a, x = .ok a) (hf : ∀ a, ∃ b, f a = .ok b) :
    ∃ b, (x >>= f) = .ok b := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hf a
  exact ⟨b, by rw [ha]; exact hb⟩

open Zip.Native in
/-- `buildFseTable` always succeeds — its body contains only pure array
    operations (set!, replicate, arithmetic) and never throws. -/
theorem buildFseTable_ok (probs : Array Int32) (al : Nat) :
    ∃ table, buildFseTable probs al = .ok table := by
  simp only [buildFseTable]
  -- The goal is a chain of binds over 4 forIn loops, ending with pure.
  -- Each loop body only returns .ok (.yield _), so each loop succeeds.
  apply Except.bind_always_ok
  · -- Loop 1: all branches return .ok (.yield _)
    exact forIn_range_always_ok _ _ _ (fun i b => by
      simp only [bind, Except.bind, pure, Except.pure]
      split <;> (try split) <;> exact ⟨_, rfl⟩)
  · intro v1
    apply Except.bind_always_ok
    · -- Loop 2: distribute symbols (body contains nested forIn)
      exact forIn_range_always_ok _ _ _ (fun i b => by
        simp only [bind, Except.bind, pure, Except.pure]
        split
        · -- if h_sym
          split
          · exact ⟨_, rfl⟩
          · -- Nested forIn inside a bind chain
            apply Except.bind_always_ok
            · exact forIn_range_always_ok _ _ _
                (fun j c => ⟨_, rfl⟩)
            · intro r; exact ⟨_, rfl⟩
        · exact ⟨_, rfl⟩)
    · intro v2
      apply Except.bind_always_ok
      · -- Loop 3: count symbols
        exact forIn_range_always_ok _ _ _ (fun i b => by
          simp only [bind, Except.bind, pure, Except.pure]
          split <;> (try split) <;> exact ⟨_, rfl⟩)
      · intro v3
        apply Except.bind_always_ok
        · -- Loop 4: compute numBits/newState
          exact forIn_range_always_ok _ _ _ (fun i b => by
            simp only [bind, Except.bind, pure, Except.pure]
            split <;> (try split) <;> (try split) <;> (try split) <;> exact ⟨_, rfl⟩)
        · intro v4
          exact ⟨_, rfl⟩

/-! ## Structural properties of `buildPredefinedFseTables` -/

open Zip.Native in
/-- `buildPredefinedFseTables` succeeds: the three predefined distributions
    are well-formed and `buildFseTable` accepts them.

    This follows from `buildFseTable_ok`, which shows `buildFseTable` always
    succeeds — its body contains only pure array operations and never throws. -/
theorem buildPredefinedFseTables_success :
    ∃ tables, buildPredefinedFseTables = Except.ok tables := by
  simp only [buildPredefinedFseTables]
  obtain ⟨ll, hll⟩ := buildFseTable_ok predefinedLitLenDistribution 6
  obtain ⟨ml, hml⟩ := buildFseTable_ok predefinedMatchLenDistribution 6
  obtain ⟨of, hof⟩ := buildFseTable_ok predefinedOffsetDistribution 5
  rw [hll, hml, hof]
  exact ⟨_, rfl⟩

open Zip.Native in
/-- When `buildPredefinedFseTables` succeeds, the three tables have the
    expected accuracy logs: 6 for literal lengths, 6 for match lengths,
    and 5 for offsets. -/
theorem buildPredefinedFseTables_accuracyLogs :
    ∀ ll ml of, buildPredefinedFseTables = Except.ok (ll, ml, of) →
      ll.accuracyLog = 6 ∧ ml.accuracyLog = 6 ∧ of.accuracyLog = 5 := by
  intro ll ml of h
  simp only [buildPredefinedFseTables] at h
  obtain ⟨ll', hll, h⟩ := Except.bind_eq_ok' h
  obtain ⟨ml', hml, h⟩ := Except.bind_eq_ok' h
  obtain ⟨of', hof, h⟩ := Except.bind_eq_ok' h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact ⟨buildFseTable_accuracyLog_eq _ _ _ hll,
         buildFseTable_accuracyLog_eq _ _ _ hml,
         buildFseTable_accuracyLog_eq _ _ _ hof⟩

/-! ## BitPos advancement for `decodeFseDistribution`

Proves that `decodeFseDistribution` advances `BitReader.bitPos` by at least 4,
corresponding to the 4 bits read for the accuracy log. This enables proving
that the `fseCompressed` mode of `resolveSingleFseTable` strictly advances
the byte position. -/

-- Helper: readBit always produces bitOff < 8
-- (The equivalent in BitReaderInvariant is private, so we reproduce it here.)
open Zip.Native in
private theorem readBit_bitOff_lt' (br br' : BitReader) (bit : UInt32)
    (h : br.readBit = .ok (bit, br')) :
    br'.bitOff < 8 := by
  simp only [BitReader.readBit] at h
  split at h
  · exact nomatch h
  · split at h <;> simp only [Except.ok.injEq, Prod.mk.injEq] at h <;>
      obtain ⟨_, rfl⟩ := h <;> dsimp only [] <;> omega

-- readBits.go preserves bitOff < 8
open Zip.Native in
private theorem readBits_go_bitOff_lt' (br br' : BitReader)
    (acc : UInt32) (shift n : Nat) (val : UInt32)
    (h : BitReader.readBits.go br acc shift n = .ok (val, br'))
    (hbo : br.bitOff < 8) :
    br'.bitOff < 8 := by
  induction n generalizing br acc shift with
  | zero =>
    simp only [BitReader.readBits.go] at h
    obtain ⟨_, rfl⟩ := h; exact hbo
  | succ n ih =>
    simp only [BitReader.readBits.go, bind, Except.bind] at h
    cases hrb : br.readBit with
    | error e => simp only [hrb] at h; exact nomatch h
    | ok p =>
      obtain ⟨bit, br₁⟩ := p
      simp only [hrb] at h
      exact ih br₁ _ _ h (readBit_bitOff_lt' br br₁ bit hrb)

-- readBits preserves bitOff < 8
open Zip.Native in
private theorem readBits_bitOff_lt' (br br' : BitReader) (n : Nat)
    (val : UInt32) (h : br.readBits n = .ok (val, br'))
    (hbo : br.bitOff < 8) :
    br'.bitOff < 8 :=
  readBits_go_bitOff_lt' br br' 0 0 n val h hbo

open Zip.Native in
/-- `readProbValue` advances or preserves `bitPos` and maintains `bitOff < 8`. -/
private theorem readProbValue_bitPos_ge
    {br br' : BitReader} {remaining val : Nat}
    (h : readProbValue br remaining = .ok (val, br'))
    (hbo : br.bitOff < 8) :
    br'.bitPos ≥ br.bitPos ∧ br'.bitOff < 8 := by
  unfold readProbValue at h
  dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  cases hrb : br.readBits (Nat.log2 (remaining + 1) + 1 - 1) with
  | error e => rw [hrb] at h; dsimp only [Bind.bind, Except.bind] at h; exact nomatch h
  | ok val₁ =>
    rw [hrb] at h; dsimp only [Bind.bind, Except.bind] at h
    have hbp := readBits_bitPos_eq br val₁.2 _ val₁.1 hrb hbo
    have hbo₁ := readBits_bitOff_lt' br val₁.2 _ val₁.1 hrb hbo
    split at h
    · -- rawBits < lowThreshold
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h
      exact ⟨by rw [hbp]; omega, hbo₁⟩
    · -- extra bit needed
      cases hrb₂ : val₁.2.readBits 1 with
      | error e => rw [hrb₂] at h; dsimp only [Bind.bind, Except.bind] at h; exact nomatch h
      | ok val₂ =>
        rw [hrb₂] at h; dsimp only [Bind.bind, Except.bind] at h
        have hbp₂ := readBits_bitPos_eq val₁.2 val₂.2 1 val₂.1 hrb₂ hbo₁
        have hbo₂ := readBits_bitOff_lt' val₁.2 val₂.2 1 val₂.1 hrb₂ hbo₁
        split at h <;>
          simp only [Except.ok.injEq, Prod.mk.injEq] at h <;>
          obtain ⟨_, rfl⟩ := h <;>
          exact ⟨by rw [hbp₂, hbp]; omega, hbo₂⟩

open Zip.Native in
/-- `decodeZeroRepeats` advances or preserves `bitPos` and maintains `bitOff < 8`. -/
private theorem decodeZeroRepeats_bitPos_ge
    {br : BitReader} {probs : Array Int32} {sym ms fuel : Nat}
    {probs' : Array Int32} {sym' : Nat} {br' : BitReader}
    (h : decodeZeroRepeats br probs sym ms fuel = .ok (probs', sym', br'))
    (hbo : br.bitOff < 8) :
    br'.bitPos ≥ br.bitPos ∧ br'.bitOff < 8 := by
  induction fuel generalizing br probs sym with
  | zero => simp only [decodeZeroRepeats, reduceCtorEq] at h
  | succ fuel ih =>
    unfold decodeZeroRepeats at h
    dsimp only [Bind.bind, Except.bind] at h
    cases hrb : br.readBits 2 with
    | error e => rw [hrb] at h; dsimp only [Bind.bind, Except.bind] at h; exact nomatch h
    | ok val =>
      rw [hrb] at h; dsimp only [Bind.bind, Except.bind] at h
      have hbp := readBits_bitPos_eq br val.2 2 val.1 hrb hbo
      have hbo₁ := readBits_bitOff_lt' br val.2 2 val.1 hrb hbo
      split at h
      · -- repeatCount == 3, recursive call
        have ⟨hge, hbo'⟩ := ih h hbo₁
        exact ⟨by rw [hbp] at hge; omega, hbo'⟩
      · -- repeatCount != 3, done
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨_, _, rfl⟩ := h
        exact ⟨by rw [hbp]; omega, hbo₁⟩

open Zip.Native in
/-- `decodeFseLoop` preserves or advances `bitPos` and maintains `bitOff < 8`. -/
private theorem decodeFseLoop_bitPos_ge
    {br : BitReader} {rem : Nat} {probs : Array Int32}
    {sym ms : Nat} {fuel : Nat}
    {rem' : Nat} {probs' : Array Int32} {sym' : Nat} {br' : BitReader}
    (h : decodeFseLoop br rem probs sym ms fuel = .ok (rem', probs', sym', br'))
    (hbo : br.bitOff < 8) :
    br'.bitPos ≥ br.bitPos ∧ br'.bitOff < 8 := by
  induction fuel generalizing br rem probs sym with
  | zero => simp only [decodeFseLoop, reduceCtorEq] at h
  | succ fuel ih =>
    rw [decodeFseLoop.eq_2] at h
    by_cases hcond : ¬(rem > 0 ∧ sym < ms)
    · -- Loop exits: return unchanged state
      rw [if_pos hcond] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨_, _, _, rfl⟩ := h
      exact ⟨Nat.le_refl _, hbo⟩
    · -- Loop continues
      rw [if_neg hcond] at h
      cases hrpv : readProbValue br rem with
      | error e => simp only [hrpv, reduceCtorEq] at h
      | ok val =>
        simp only [hrpv] at h
        have ⟨hge_rpv, hbo_rpv⟩ := readProbValue_bitPos_ge hrpv hbo
        by_cases hp0 : (Int32.ofNat val.fst - 1 == 0) = true
        · rw [if_pos hp0] at h
          cases hzr : decodeZeroRepeats val.2 (probs.push 0) (sym + 1) ms 1000 with
          | error e => simp only [hzr, reduceCtorEq] at h
          | ok val₂ =>
            simp only [hzr] at h
            have ⟨hge_zr, hbo_zr⟩ := decodeZeroRepeats_bitPos_ge hzr hbo_rpv
            have ⟨hge_rec, hbo_rec⟩ := ih h hbo_zr
            exact ⟨by omega, hbo_rec⟩
        · rw [if_neg hp0] at h
          by_cases hp1 : (Int32.ofNat val.fst - 1 == -1) = true
          · rw [if_pos hp1] at h
            have ⟨hge_rec, hbo_rec⟩ := ih h hbo_rpv
            exact ⟨by omega, hbo_rec⟩
          · rw [if_neg hp1] at h
            by_cases hgt : int32ToNat (Int32.ofNat val.fst - 1) > rem
            · rw [if_pos hgt] at h; exact nomatch h
            · rw [if_neg hgt] at h
              have ⟨hge_rec, hbo_rec⟩ := ih h hbo_rpv
              exact ⟨by omega, hbo_rec⟩

open Zip.Native in
/-- When `decodeFseDistribution` succeeds, the returned BitReader's `bitPos` has
    advanced by at least 4 (from the accuracy log) and `bitOff < 8` is maintained.
    Requires `bitOff < 8` (always satisfied when constructed with `bitOff := 0`
    as in the `fseCompressed` mode). -/
theorem decodeFseDistribution_bitPos_ge
    {br : BitReader} {maxSymbols maxAccLog : Nat}
    {probs : Array Int32} {al : Nat} {br' : BitReader}
    (h : decodeFseDistribution br maxSymbols maxAccLog = .ok (probs, al, br'))
    (hbo : br.bitOff < 8) :
    br'.bitPos ≥ br.bitPos + 4 ∧ br'.bitOff < 8 := by
  obtain ⟨rdval, _, hrd, _, _, hdl⟩ := decodeFseDistribution_ok_decompose h
  have hbp := readBits_bitPos_eq br rdval.2 4 rdval.1 hrd hbo
  have hbo₁ := readBits_bitOff_lt' br rdval.2 4 rdval.1 hrd hbo
  have ⟨hge_loop, hbo_loop⟩ := decodeFseLoop_bitPos_ge hdl hbo₁
  exact ⟨by rw [hbp] at hge_loop; omega, hbo_loop⟩

/-! ## BitReader pos_le_size — FSE distribution chain

These theorems establish that `readProbValue`, `decodeZeroRepeats`,
`decodeFseLoop`, and `decodeFseDistribution` preserve the invariant
`pos ≤ data.size` on success. They chain through `readBits_pos_le_size`
from `BitReaderInvariant.lean`. -/

open Zip.Native in
/-- `readProbValue` preserves `pos ≤ data.size`. -/
theorem readProbValue_pos_le_size (br br' : BitReader) (remaining val : Nat)
    (h : readProbValue br remaining = .ok (val, br'))
    (hbr : br.pos ≤ br.data.size) :
    br'.pos ≤ br'.data.size := by
  unfold readProbValue at h
  dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  cases hrb : br.readBits (Nat.log2 (remaining + 1) + 1 - 1) with
  | error e => rw [hrb] at h; dsimp only [Bind.bind, Except.bind] at h; exact nomatch h
  | ok val₁ =>
    rw [hrb] at h; dsimp only [Bind.bind, Except.bind] at h
    have hple₁ := readBits_pos_le_size br val₁.2 _ val₁.1 hrb hbr
    split at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h; exact hple₁
    · cases hrb₂ : val₁.2.readBits 1 with
      | error e => rw [hrb₂] at h; dsimp only [Bind.bind, Except.bind] at h; exact nomatch h
      | ok val₂ =>
        rw [hrb₂] at h; dsimp only [Bind.bind, Except.bind] at h
        have hple₂ := readBits_pos_le_size val₁.2 val₂.2 1 val₂.1 hrb₂ hple₁
        split at h <;>
          simp only [Except.ok.injEq, Prod.mk.injEq] at h <;>
          obtain ⟨_, rfl⟩ := h <;>
          exact hple₂

open Zip.Native in
/-- `decodeZeroRepeats` preserves `pos ≤ data.size`. -/
private theorem decodeZeroRepeats_pos_le_size
    {br : BitReader} {probs : Array Int32} {sym ms fuel : Nat}
    {probs' : Array Int32} {sym' : Nat} {br' : BitReader}
    (h : decodeZeroRepeats br probs sym ms fuel = .ok (probs', sym', br'))
    (hbr : br.pos ≤ br.data.size) :
    br'.pos ≤ br'.data.size := by
  induction fuel generalizing br probs sym with
  | zero => simp only [decodeZeroRepeats, reduceCtorEq] at h
  | succ fuel ih =>
    unfold decodeZeroRepeats at h
    dsimp only [Bind.bind, Except.bind] at h
    cases hrb : br.readBits 2 with
    | error e => rw [hrb] at h; dsimp only [Bind.bind, Except.bind] at h; exact nomatch h
    | ok val =>
      rw [hrb] at h; dsimp only [Bind.bind, Except.bind] at h
      have hple₁ := readBits_pos_le_size br val.2 2 val.1 hrb hbr
      split at h
      · exact ih h hple₁
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨_, _, rfl⟩ := h; exact hple₁

open Zip.Native in
/-- `decodeFseLoop` preserves `pos ≤ data.size`. -/
private theorem decodeFseLoop_pos_le_size
    {br : BitReader} {rem : Nat} {probs : Array Int32}
    {sym ms : Nat} {fuel : Nat}
    {rem' : Nat} {probs' : Array Int32} {sym' : Nat} {br' : BitReader}
    (h : decodeFseLoop br rem probs sym ms fuel = .ok (rem', probs', sym', br'))
    (hbr : br.pos ≤ br.data.size) :
    br'.pos ≤ br'.data.size := by
  induction fuel generalizing br rem probs sym with
  | zero => simp only [decodeFseLoop, reduceCtorEq] at h
  | succ fuel ih =>
    rw [decodeFseLoop.eq_2] at h
    by_cases hcond : ¬(rem > 0 ∧ sym < ms)
    · rw [if_pos hcond] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨_, _, _, rfl⟩ := h; exact hbr
    · rw [if_neg hcond] at h
      cases hrpv : readProbValue br rem with
      | error e => simp only [hrpv, reduceCtorEq] at h
      | ok val =>
        simp only [hrpv] at h
        have hple_rpv := readProbValue_pos_le_size br val.2 rem val.1 hrpv hbr
        by_cases hp0 : (Int32.ofNat val.fst - 1 == 0) = true
        · rw [if_pos hp0] at h
          cases hzr : decodeZeroRepeats val.2 (probs.push 0) (sym + 1) ms 1000 with
          | error e => simp only [hzr, reduceCtorEq] at h
          | ok val₂ =>
            simp only [hzr] at h
            have hple_zr := decodeZeroRepeats_pos_le_size hzr hple_rpv
            exact ih h hple_zr
        · rw [if_neg hp0] at h
          by_cases hp1 : (Int32.ofNat val.fst - 1 == -1) = true
          · rw [if_pos hp1] at h; exact ih h hple_rpv
          · rw [if_neg hp1] at h
            by_cases hgt : int32ToNat (Int32.ofNat val.fst - 1) > rem
            · rw [if_pos hgt] at h; exact nomatch h
            · rw [if_neg hgt] at h; exact ih h hple_rpv

open Zip.Native in
/-- When `decodeFseDistribution` succeeds and the input reader has
    `pos ≤ data.size`, the output reader also has `pos ≤ data.size`. -/
theorem decodeFseDistribution_pos_le_size (br br' : BitReader)
    (maxSymbols maxAccLog : Nat) (probs : Array Int32) (al : Nat)
    (h : decodeFseDistribution br maxSymbols maxAccLog = .ok (probs, al, br'))
    (hbr : br.pos ≤ br.data.size) :
    br'.pos ≤ br'.data.size := by
  obtain ⟨rdval, _, hrd, _, _, hdl⟩ := decodeFseDistribution_ok_decompose h
  exact decodeFseLoop_pos_le_size hdl (readBits_pos_le_size br rdval.2 4 rdval.1 hrd hbr)

/-! ## Helper lemmas for newState bound -/

/-- `Nat.log2 n ≤ k` when `n < 2^(k+1)`. Inverse of `Nat.lt_log2_self`. -/
private theorem log2_le_of_lt_pow2_succ (n k : Nat) (h : n < 2 ^ (k + 1)) :
    Nat.log2 n ≤ k := by
  if hle : Nat.log2 n ≤ k then exact hle else
  exfalso
  have h3 : n ≠ 0 := by intro heq; subst heq; simp at hle
  exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h
    (Nat.le_trans (Nat.pow_le_pow_right (by omega) (by omega)) (Nat.log2_self_le h3)))

/-- `n * 2^(k - log2 n) < 2^(k+1)` when `log2 n ≤ k`. This bounds the
    shifted value `nextState <<< numBits` in FSE table construction. -/
private theorem mul_pow_sub_log2_lt (n k : Nat) (hk : Nat.log2 n ≤ k) :
    n * 2 ^ (k - Nat.log2 n) < 2 ^ (k + 1) :=
  calc n * 2 ^ (k - Nat.log2 n)
      < 2 ^ (Nat.log2 n + 1) * 2 ^ (k - Nat.log2 n) :=
        (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr Nat.lt_log2_self
    _ = 2 ^ (k + 1) := by rw [← Nat.pow_add]; congr 1; omega

/-- The baseline value `(nextState <<< numBits) - tableSize`, converted to
    UInt16, is less than `1 <<< al` when `nextState < 2 * (1 <<< al)`. -/
private theorem baseline_toUInt16_lt (nextState al : Nat)
    (hlt : nextState < 2 * (1 <<< al)) :
    ((nextState <<< (al - Nat.log2 nextState)) - (1 <<< al)).toUInt16.toNat <
      1 <<< al := by
  simp only [Nat.shiftLeft_eq, Nat.one_mul] at *
  have hlog : Nat.log2 nextState ≤ al :=
    log2_le_of_lt_pow2_succ _ _ (by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ al)]; exact hlt)
  have hmul := mul_pow_sub_log2_lt nextState al hlog
  -- hmul : nextState * 2^(al - log2 nextState) < 2^(al+1)
  -- Rewrite 2^(al+1) = 2 * 2^al, keeping LHS unchanged
  rw [Nat.pow_succ, Nat.mul_comm (2 ^ al)] at hmul
  -- Now hmul : nextState * 2^numBits < 2 * 2^al, both sides normalized
  simp only [Nat.toUInt16_eq, UInt16.toNat_ofNat']
  omega

/-- `Array.getD` after `set!`: the result is `v` for the modified index (if in bounds),
    or the original `getD` otherwise. -/
private theorem getD_set! (a : Array Nat) (i v s : Nat) :
    (a.set! i v).getD s 0 = if i = s ∧ i < a.size then v else a.getD s 0 := by
  simp only [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
    Array.getElem?_setIfInBounds]
  split <;> split <;> grind

private theorem getD_eq_getElem (a : Array Nat) (i : Nat) (h : i < a.size) :
    a.getD i 0 = a[i] := by
  unfold Array.getD; exact dif_pos h

/-! ## Indexed loop invariant -/

/-- `List.forIn'.loop` in `Except` preserves an index-dependent predicate.
    The index `offset` tracks how many elements have been processed so far.
    This is stronger than `forIn'_loop_preserves` when the predicate needs
    to grow with the iteration count (e.g., bounding accumulated values). -/
private theorem forIn'_loop_preserves_indexed {α β ε : Type}
    (P : Nat → β → Prop) (target : Nat)
    (as curr : List α) (init result : β)
    (f : α → β → Except ε (ForInStep β))
    (offset : Nat)
    (h_init : P offset init)
    (h_yield : ∀ (k : Nat) (a : α) (b b' : β),
      k < target → P k b → f a b = .ok (.yield b') → P (k + 1) b')
    (h_done : ∀ (k : Nat) (a : α) (b b' : β),
      P k b → f a b = .ok (.done b') → P target b')
    (hsuf : ∃ bs, bs ++ curr = as)
    (h_len : offset + curr.length = target)
    (h_result : List.forIn'.loop as (fun a _ b => f a b) curr init hsuf =
      .ok result) :
    P target result := by
  induction curr generalizing init offset with
  | nil =>
    unfold List.forIn'.loop at h_result
    dsimp only [pure, Except.pure] at h_result
    rw [← Except.ok.inj h_result]
    simp only [List.length_nil, Nat.add_zero] at h_len
    exact h_len ▸ h_init
  | cons x xs ih =>
    unfold List.forIn'.loop at h_result
    dsimp only [Bind.bind, Except.bind] at h_result
    cases hfx : f x init with
    | error e => rw [hfx] at h_result; exact nomatch h_result
    | ok step =>
      rw [hfx] at h_result
      cases step with
      | done b' =>
        dsimp only [pure, Except.pure] at h_result
        rw [← Except.ok.inj h_result]
        exact h_done offset x init b' h_init hfx
      | yield b' =>
        have hlt : offset < target := by
          simp only [List.length_cons] at h_len; omega
        exact ih b' (offset + 1)
          (h_yield offset x init b' hlt h_init hfx) _
          (by simp only [List.length_cons] at h_len; omega) h_result

/-- `forIn` over a range `[:n]` preserves an index-dependent predicate `P k b`
    where `k` tracks the iteration count from 0 to n. -/
private theorem forIn_range_preserves_indexed {β ε : Type}
    (P : Nat → β → Prop) (n : Nat) (init result : β)
    (f : Nat → β → Except ε (ForInStep β))
    (h_init : P 0 init)
    (h_yield : ∀ (k : Nat) (a : Nat) (b b' : β),
      k < n → P k b → f a b = .ok (.yield b') → P (k + 1) b')
    (h_done : ∀ (k : Nat) (a : Nat) (b b' : β),
      P k b → f a b = .ok (.done b') → P n b')
    (h_result : forIn [:n] init f = .ok result) :
    P n result := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at h_result
  exact forIn'_loop_preserves_indexed P n _ _ init result f 0
    h_init h_yield h_done _
    (by simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_one_sub_one, Nat.div_one,
      List.length_range', Nat.zero_add])
    h_result

/-! ## buildFseTable newState bound -/

open Zip.Native in
/-- When `buildFseTable` succeeds, every cell's `newState` is less than
    `1 <<< al` (the table size). This ensures the FSE state machine stays
    in bounds: the next state `newState + readBits(numBits)` lands within
    the table.

    The proof tracks two invariants:
    - Loop 3 (counting): each `symbolCounts[sym] ≤ tableSize` (via indexed
      loop invariant — each count ≤ iteration index ≤ tableSize)
    - Loop 4 (assignment): each `symbolStateIndex[sym] ≤ iteration index`,
      so `stateIdx < tableSize`. Combined with `count ≤ tableSize`, this
      gives `nextState = count + stateIdx < 2 * tableSize`, enabling the
      algebraic bound on `baseline.toUInt16`. -/
theorem buildFseTable_newState_lt (probs : Array Int32) (al : Nat)
    (table : FseTable) (h : buildFseTable probs al = .ok table)
    (i : Fin table.cells.size) :
    table.cells[i].newState.toNat < 1 <<< al := by
  simp only [buildFseTable] at h
  obtain ⟨v1, hloop1, h⟩ := Except.bind_eq_ok' h
  obtain ⟨v2, hloop2, h⟩ := Except.bind_eq_ok' h
  obtain ⟨v3, hloop3, h⟩ := Except.bind_eq_ok' h
  obtain ⟨v4, hloop4, h⟩ := Except.bind_eq_ok' h
  simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
  show v4.fst[i].newState.toNat < 1 <<< al
  -- Establish type aliases for clarity
  -- v3 : Array Nat (symbolCounts)
  -- v4 : Array FseCell × Array Nat (cells × symbolStateIndex)
  -- The per-cell predicate
  let Q : FseCell → Prop := fun c => c.newState.toNat < 1 <<< al
  -- The default cell has newState = 0 < tableSize
  have hQ_default : Q default := by
    change (0 : UInt16).toNat < 1 <<< al
    simp only [Nat.shiftLeft_eq, Nat.one_mul]
    exact Nat.two_pow_pos _
  -- Initial cells: Array.replicate with default has newState = 0
  have hinit : ∀ j : Fin (Array.replicate (1 <<< al) (default : FseCell)).size,
      Q (Array.replicate (1 <<< al) (default : FseCell))[j] := by
    intro ⟨j, hj⟩
    simp only [Fin.getElem_fin, Array.getElem_replicate]; exact hQ_default
  -- Loop 1: preserves Q (sets cells with { symbol := ... }, default newState = 0)
  have h1 : ∀ j : Fin v1.fst.size, Q v1.fst[j] := by
    apply forIn_range_preserves (fun s => ∀ j : Fin s.fst.size, Q s.fst[j])
      _ _ _ _ hinit _ _ hloop1
    · intro a b b' hb heq
      simp only [bind, Except.bind, pure, Except.pure] at heq
      split at heq
      · split at heq
        · rw [← ForInStep.yield.inj (Except.ok.inj heq)]; dsimp only
          exact set!_preserves_forall hb hQ_default
        · rw [← ForInStep.yield.inj (Except.ok.inj heq)]; exact hb
      · rw [← ForInStep.yield.inj (Except.ok.inj heq)]; exact hb
    · intro a b b' hb heq
      simp only [bind, Except.bind, pure, Except.pure] at heq
      split at heq <;> (try split at heq) <;> exact nomatch heq
  -- Loop 2: preserves Q (sets cells with { symbol := ... }, default newState = 0)
  have h2 : ∀ j : Fin v2.fst.size, Q v2.fst[j] := by
    apply forIn_range_preserves (fun s => ∀ j : Fin s.fst.size, Q s.fst[j])
      _ _ _ _ h1 _ _ hloop2
    · intro a b b' hb heq
      simp only [bind, Except.bind, pure, Except.pure] at heq
      split at heq
      · split at heq
        · rw [← ForInStep.yield.inj (Except.ok.inj heq)]; exact hb
        · split at heq
          · exact nomatch heq
          · rename_i r hinner
            rw [← ForInStep.yield.inj (Except.ok.inj heq)]; dsimp only
            apply forIn_range_preserves (fun s => ∀ j : Fin s.fst.size, Q s.fst[j])
              _ _ _ _ hb _ _ hinner
            · intro a2 b2 b2' hb2 heq2
              rw [← ForInStep.yield.inj (Except.ok.inj heq2)]; dsimp only
              exact set!_preserves_forall hb2 hQ_default
            · intro a2 b2 b2' hb2 heq2; exact nomatch heq2
      · rw [← ForInStep.yield.inj (Except.ok.inj heq)]; exact hb
    · intro _ _ _ _ heq; simp only [bind, Except.bind, pure, Except.pure] at heq
      split at heq <;> (try split at heq) <;> (try split at heq) <;> exact nomatch heq
  -- Loop 3 (counting): prove each symbolCounts[sym] ≤ tableSize
  -- Use indexed invariant: after k iterations, each count ≤ k
  have h3_counts : ∀ s, v3.getD s 0 ≤ 1 <<< al := by
    apply forIn_range_preserves_indexed
      (fun k (sc : Array Nat) => ∀ s, sc.getD s 0 ≤ k)
      _ _ _ _ _ _ _ hloop3
    · -- Initial: Array.replicate probs.size 0, all zeros ≤ 0
      intro s; unfold Array.getD; split
        <;> simp only [Array.getInternal_eq_getElem, Array.getElem_replicate, Std.le_refl]
    · -- Yield step: incrementing one element preserves bound
      intro k _ b b' _ hb heq
      simp only [bind, Except.bind, pure, Except.pure] at heq
      split at heq
      · -- if h_i : i < cells.size
        split at heq
        · -- if h_sym : sym < symbolCounts.size — set! sym (count + 1)
          rw [← ForInStep.yield.inj (Except.ok.inj heq)]
          intro s; rw [getD_set!]; split
          · -- modified index: count + 1 ≤ k + 1
            rename_i h; obtain ⟨rfl, h_lt⟩ := h
            rw [← getD_eq_getElem _ _ h_lt]
            exact Nat.succ_le_succ (hb _)
          · -- other index: old value ≤ k ≤ k + 1
            exact Nat.le_succ_of_le (hb s)
        · -- h_sym doesn't hold: no change
          rw [← ForInStep.yield.inj (Except.ok.inj heq)]
          intro s; exact Nat.le_succ_of_le (hb s)
      · -- h_i doesn't hold: no change
        rw [← ForInStep.yield.inj (Except.ok.inj heq)]
        intro s; exact Nat.le_succ_of_le (hb s)
    · -- Done: never happens (body always yields)
      intro k _ b b' hb heq
      simp only [bind, Except.bind, pure, Except.pure] at heq
      split at heq <;> (try split at heq) <;> exact nomatch heq
  -- Loop 4: compute numBits/newState for each cell
  -- Use indexed invariant: symIdx values ≤ iteration count
  -- Combined with h3_counts (count ≤ tableSize) and the algebraic bound
  have h4 : (∀ j : Fin v4.fst.size, Q v4.fst[j]) ∧
      (∀ sym, v4.snd.getD sym 0 ≤ 1 <<< al) := by
    apply forIn_range_preserves_indexed
      (P := fun k s =>
        (∀ j : Fin s.fst.size, Q s.fst[j]) ∧ (∀ sym, s.snd.getD sym 0 ≤ k))
      (h_init := ⟨h2, fun sym => by
        unfold Array.getD; split
          <;> simp only [Array.getInternal_eq_getElem, Array.getElem_replicate, Std.le_refl]⟩)
      (h_result := hloop4)
    · -- Yield step
      intro k kv b b' hk ⟨hcells, hsymIdx⟩ heq
      simp only [bind, Except.bind, pure, Except.pure] at heq
      split at heq
      · -- if h_i : i < cells.size
        split at heq
        · -- if h_sc : sym < symbolCounts.size
          split at heq
          · -- if h_si : sym < symbolStateIndex.size
            split at heq
            · -- count != 0: Main case
              rw [← ForInStep.yield.inj (Except.ok.inj heq)]; dsimp only
              refine ⟨?_, ?_⟩
              · -- Cells property: set! preserves Q, new value satisfies Q
                apply set!_preserves_forall hcells
                show Q _; unfold Q; dsimp only []
                apply baseline_toUInt16_lt
                -- Convert getD to getElem using the in-bounds proofs from the if-guards
                have hcount := h3_counts (b.fst[kv].symbol.toNat)
                rw [getD_eq_getElem _ _ ‹b.fst[kv].symbol.toNat < v3.size›] at hcount
                have hstateIdx := hsymIdx (b.fst[kv].symbol.toNat)
                rw [getD_eq_getElem _ _ ‹b.fst[kv].symbol.toNat < b.snd.size›] at hstateIdx
                omega
              · -- symIdx property: set! sym (stateIdx + 1) preserves getD ≤ k + 1
                intro s; rw [getD_set!]; split
                · rename_i h; obtain ⟨rfl, h_lt⟩ := h
                  rw [← getD_eq_getElem _ _ h_lt]
                  exact Nat.succ_le_succ (hsymIdx _)
                · exact Nat.le_succ_of_le (hsymIdx s)
            · -- count == 0
              rw [← ForInStep.yield.inj (Except.ok.inj heq)]
              exact ⟨hcells, fun sym => Nat.le_succ_of_le (hsymIdx sym)⟩
          · rw [← ForInStep.yield.inj (Except.ok.inj heq)]
            exact ⟨hcells, fun sym => Nat.le_succ_of_le (hsymIdx sym)⟩
        · rw [← ForInStep.yield.inj (Except.ok.inj heq)]
          exact ⟨hcells, fun sym => Nat.le_succ_of_le (hsymIdx sym)⟩
      · rw [← ForInStep.yield.inj (Except.ok.inj heq)]
        exact ⟨hcells, fun sym => Nat.le_succ_of_le (hsymIdx sym)⟩
    · intro _ _ _ _ _ heq; simp only [bind, Except.bind, pure, Except.pure] at heq
      split at heq <;> (try split at heq) <;> (try split at heq) <;>
      (try split at heq) <;> exact nomatch heq
  exact h4.1 i

/-- Helper: `Nat.toUInt16.toNat` preserves strict upper bounds.
    Since `n.toUInt16.toNat = n % UInt16.size ≤ n`, any upper bound on `n`
    transfers to `n.toUInt16.toNat`. -/
private theorem toUInt16_toNat_lt_of_lt {n m : Nat} (h : n < m) :
    n.toUInt16.toNat < m := by
  simp only [Nat.toUInt16_eq, UInt16.toNat_ofNat']
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) h

open Zip.Native in
/-- When `buildFseTable` succeeds and the input distribution is non-empty,
    every cell's symbol index is less than `probs.size`.
    This is condition (b) of `ValidFseTable`.

    The proof threads the invariant through all four bind chains:
    - Initial cells have `symbol = 0 < probs.size` (by `hpos`)
    - Loops 1-2 set `symbol := sym.toUInt16` where `sym < probs.size`
    - Loop 3 doesn't modify cells
    - Loop 4 preserves symbol (`{ cells[i]!.symbol with ... }`) -/
theorem buildFseTable_symbol_lt (probs : Array Int32) (al : Nat)
    (table : FseTable) (h : buildFseTable probs al = .ok table)
    (hpos : 0 < probs.size)
    (i : Fin table.cells.size) :
    table.cells[i].symbol.toNat < probs.size := by
  simp only [buildFseTable] at h
  obtain ⟨v1, hloop1, h⟩ := Except.bind_eq_ok' h
  obtain ⟨v2, hloop2, h⟩ := Except.bind_eq_ok' h
  obtain ⟨v3, hloop3, h⟩ := Except.bind_eq_ok' h
  obtain ⟨v4, hloop4, h⟩ := Except.bind_eq_ok' h
  simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
  show v4.fst[i].symbol.toNat < probs.size
  let P : FseCell → Prop := fun c => c.symbol.toNat < probs.size
  -- Initial cells: Array.replicate with default has symbol = 0
  have hinit : ∀ j : Fin (Array.replicate (1 <<< al) (default : FseCell)).size,
      P (Array.replicate (1 <<< al) (default : FseCell))[j] := by
    intro ⟨j, hj⟩; show P _
    simp only [Fin.getElem_fin, Array.getElem_replicate]; exact hpos
  -- Loop 1: preserves property (sets cells with { symbol := sym.toUInt16 })
  have h1 : ∀ j : Fin v1.fst.size, P v1.fst[j] := by
    apply forIn_range_preserves (fun s => ∀ j : Fin s.fst.size, P s.fst[j])
      _ _ _ _ hinit _ _ hloop1
    · intro a b b' hb heq
      simp only [bind, Except.bind, pure, Except.pure] at heq
      split at heq
      · -- if h_sym : sym < probs.size
        split at heq
        · rw [← ForInStep.yield.inj (Except.ok.inj heq)]; dsimp only
          rename_i h_sym hcond
          apply set!_preserves_forall hb; show P _
          exact toUInt16_toNat_lt_of_lt h_sym
        · rw [← ForInStep.yield.inj (Except.ok.inj heq)]; exact hb
      · rw [← ForInStep.yield.inj (Except.ok.inj heq)]; exact hb
    · intro a b b' hb heq
      simp only [bind, Except.bind, pure, Except.pure] at heq
      split at heq <;> (try split at heq) <;> exact nomatch heq
  -- Loop 2: preserves property (sets cells with { symbol := sym.toUInt16 })
  have h2 : ∀ j : Fin v2.fst.size, P v2.fst[j] := by
    apply forIn_range_preserves (fun s => ∀ j : Fin s.fst.size, P s.fst[j])
      _ _ _ _ h1 _ _ hloop2
    · intro a b b' hb heq
      simp only [bind, Except.bind, pure, Except.pure] at heq
      split at heq
      · -- if h_sym : sym < probs.size
        rename_i ha_bound
        split at heq
        · rw [← ForInStep.yield.inj (Except.ok.inj heq)]; exact hb
        · split at heq
          · exact nomatch heq
          · rename_i _ _ hinner
            rw [← ForInStep.yield.inj (Except.ok.inj heq)]; dsimp only
            apply forIn_range_preserves (fun s => ∀ j : Fin s.fst.size, P s.fst[j])
              _ _ _ _ hb _ _ hinner
            · intro a2 b2 b2' hb2 heq2
              rw [← ForInStep.yield.inj (Except.ok.inj heq2)]; dsimp only
              exact set!_preserves_forall hb2 (toUInt16_toNat_lt_of_lt ha_bound)
            · intro a2 b2 b2' hb2 heq2; exact nomatch heq2
      · rw [← ForInStep.yield.inj (Except.ok.inj heq)]; exact hb
    · intro _ _ _ _ heq; simp only [bind, Except.bind, pure, Except.pure] at heq
      split at heq <;> (try split at heq) <;> (try split at heq) <;> exact nomatch heq
  -- Loop 3 modifies only symbolCounts (v3 : Array Nat), not cells.
  -- Loop 4 starts with v2.fst as its initial cells.
  -- Loop 4: preserves symbol field ({ symbol := cells[i]!.symbol, ... })
  apply forIn_range_preserves (fun s => ∀ j : Fin s.fst.size, P s.fst[j])
    _ _ _ _ h2 _ _ hloop4
  · intro a b b' hb heq
    simp only [bind, Except.bind, pure, Except.pure] at heq
    split at heq
    · -- if h_i : i < cells.size
      split at heq
      · -- if h_sc
        split at heq
        · -- if h_si
          split at heq
          · -- count != 0: set! preserves symbol field
            rw [← ForInStep.yield.inj (Except.ok.inj heq)]; dsimp only
            rename_i h_i _ _ _
            exact set!_preserves_forall hb (show P _ by
              show (b.fst[a]).symbol.toNat < probs.size
              exact hb ⟨a, h_i⟩)
          · -- count == 0
            rw [← ForInStep.yield.inj (Except.ok.inj heq)]; exact hb
        · rw [← ForInStep.yield.inj (Except.ok.inj heq)]; exact hb
      · rw [← ForInStep.yield.inj (Except.ok.inj heq)]; exact hb
    · rw [← ForInStep.yield.inj (Except.ok.inj heq)]; exact hb
  · intro _ _ _ _ heq; simp only [bind, Except.bind, pure, Except.pure] at heq
    split at heq <;> (try split at heq) <;> (try split at heq) <;>
    (try split at heq) <;> exact nomatch heq

open Zip.Native in
/-- When `buildFseTable` succeeds and the input distribution is non-empty,
    the resulting table satisfies `ValidFseTable`: size equals `1 <<< al`,
    all symbols are within bounds, and all `numBits` values are at most `al`.

    This composes `buildFseTable_cells_size`, `buildFseTable_symbol_lt`,
    and `buildFseTable_numBits_le`. -/
theorem buildFseTable_valid (probs : Array Int32) (al : Nat)
    (table : FseTable) (h : buildFseTable probs al = .ok table)
    (hpos : 0 < probs.size) :
    ValidFseTable table.cells al probs.size :=
  ⟨buildFseTable_cells_size probs al table h,
   fun i => buildFseTable_symbol_lt probs al table h hpos i,
   fun i => buildFseTable_numBits_le probs al table h i⟩

/-! ## Predefined FSE table `ValidFseTable` composition

Composes `buildFseTable_valid` with the concrete predefined distributions
to show each predefined table satisfies `ValidFseTable`. -/

open Zip.Native in
/-- The predefined literal-length FSE table satisfies `ValidFseTable` with
    accuracy log 6 and 36 symbols. -/
theorem buildPredefinedFseTables_litLen_valid (ll ml of : FseTable)
    (h : buildPredefinedFseTables = .ok (ll, ml, of)) :
    ValidFseTable ll.cells 6 36 := by
  simp only [buildPredefinedFseTables] at h
  obtain ⟨ll', hll, h⟩ := Except.bind_eq_ok' h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok' h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok' h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, _, _⟩ := h
  exact buildFseTable_valid _ _ _ hll (by decide)

open Zip.Native in
/-- The predefined match-length FSE table satisfies `ValidFseTable` with
    accuracy log 6 and 53 symbols. -/
theorem buildPredefinedFseTables_matchLen_valid (ll ml of : FseTable)
    (h : buildPredefinedFseTables = .ok (ll, ml, of)) :
    ValidFseTable ml.cells 6 53 := by
  simp only [buildPredefinedFseTables] at h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok' h
  obtain ⟨ml', hml, h⟩ := Except.bind_eq_ok' h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok' h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨_, rfl, _⟩ := h
  exact buildFseTable_valid _ _ _ hml (by decide)

open Zip.Native in
/-- The predefined offset FSE table satisfies `ValidFseTable` with
    accuracy log 5 and 29 symbols. -/
theorem buildPredefinedFseTables_offset_valid (ll ml of : FseTable)
    (h : buildPredefinedFseTables = .ok (ll, ml, of)) :
    ValidFseTable of.cells 5 29 := by
  simp only [buildPredefinedFseTables] at h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok' h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok' h
  obtain ⟨of', hof, h⟩ := Except.bind_eq_ok' h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨_, _, rfl⟩ := h
  exact buildFseTable_valid _ _ _ hof (by decide)

/-! ## decodeFseSymbolsWF output size -/

open Zip.Native in
/-- The inner loop of `decodeFseSymbolsWF` produces exactly
    `acc.size + remaining` elements on success. -/
theorem decodeFseSymbolsWF_loop_size
    {table : FseTable} {br br' : BackwardBitReader}
    {state remaining : Nat}
    {acc result : Array UInt8}
    (h : decodeFseSymbolsWF.loop table br state remaining acc
           = .ok (result, br')) :
    result.size = acc.size + remaining := by
  induction remaining generalizing br state acc with
  | zero =>
    simp only [decodeFseSymbolsWF.loop, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    omega
  | succ n ih =>
    simp only [decodeFseSymbolsWF.loop] at h
    split at h
    · exact nomatch h
    · simp only [beq_iff_eq] at h
      split at h
      · -- n = 0, last symbol
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, _⟩ := h
        simp only [Array.size_push]
        omega
      · -- n > 0, recursive case
        simp only [bind, Except.bind] at h
        split at h
        · exact nomatch h
        · rw [ih h]
          simp only [Array.size_push]
          omega

open Zip.Native in
/-- When `decodeFseSymbolsWF` succeeds with `count > 0`, the output array
    has exactly `count` elements. -/
theorem decodeFseSymbolsWF_size
    {table : FseTable} {br br' : BackwardBitReader}
    {count : Nat} {result : Array UInt8}
    (h : decodeFseSymbolsWF table br count = .ok (result, br'))
    (hcount : 0 < count) :
    result.size = count := by
  simp only [decodeFseSymbolsWF, beq_iff_eq] at h
  split at h
  · omega
  · simp only [bind, Except.bind] at h
    cases hrb : br.readBits table.accuracyLog with
    | error e => simp only [hrb] at h; exact nomatch h
    | ok val =>
      simp only [hrb] at h
      have := decodeFseSymbolsWF_loop_size h
      simp only [Array.size_empty] at this; omega

end Zstd.Spec.Fse
