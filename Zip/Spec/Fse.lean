import Zip.Native.Fse

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
validity predicates defined above. The proofs require unfolding the
monadic `do` block and reasoning about its control flow, which is
deferred to a future session. -/

open Zip.Native in
/-- When `decodeFseDistribution` succeeds, the returned accuracy log is
    at least 5. This follows from the computation `accuracyLog = readBits(4) + 5`
    where `readBits(4)` returns a non-negative value. -/
theorem decodeFseDistribution_accuracyLog_ge
    {br : BitReader} {maxSymbols maxAccLog : Nat}
    {probs : Array Int32} {al : Nat} {br' : BitReader}
    (_h : decodeFseDistribution br maxSymbols maxAccLog = .ok (probs, al, br')) :
    5 ≤ al := by
  unfold decodeFseDistribution at _h
  cases hrd : br.readBits 4 with
  | error e => rw [hrd] at _h; dsimp only [Bind.bind, Except.bind] at _h; exact nomatch _h
  | ok val =>
    rw [hrd] at _h; dsimp only [Bind.bind, Except.bind] at _h
    -- Peel through: if > maxAccLog, match pure, match forIn, if != 0, match pure
    split at _h
    · exact nomatch _h
    · split at _h
      · exact nomatch _h
      · split at _h
        · exact nomatch _h
        · split at _h
          · exact nomatch _h
          · split at _h
            · exact nomatch _h
            · simp only [Pure.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at _h
              obtain ⟨_, rfl, _⟩ := _h
              omega

open Zip.Native in
/-- When `decodeFseDistribution` succeeds, the returned accuracy log does
    not exceed `maxAccLog`. This follows from the guard
    `if accuracyLog > maxAccLog then throw ...`. -/
theorem decodeFseDistribution_accuracyLog_le
    {br : BitReader} {maxSymbols maxAccLog : Nat}
    {probs : Array Int32} {al : Nat} {br' : BitReader}
    (_h : decodeFseDistribution br maxSymbols maxAccLog = .ok (probs, al, br')) :
    al ≤ maxAccLog := by
  unfold decodeFseDistribution at _h
  cases hrd : br.readBits 4 with
  | error e => rw [hrd] at _h; dsimp only [Bind.bind, Except.bind] at _h; exact nomatch _h
  | ok val =>
    rw [hrd] at _h; dsimp only [Bind.bind, Except.bind] at _h
    split at _h
    · exact nomatch _h
    · split at _h
      · exact nomatch _h
      · split at _h
        · exact nomatch _h
        · split at _h
          · exact nomatch _h
          · split at _h
            · exact nomatch _h
            · simp only [Pure.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at _h
              obtain ⟨_, rfl, _⟩ := _h
              omega

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
  sorry

end Zstd.Spec.Fse
