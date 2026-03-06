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

/-! ## Structural properties of `buildFseTable`

These theorems relate the output of `buildFseTable` to the validity
predicates defined above. The two simplest structural properties are:
- the accuracy log is passed through unchanged, and
- the cells array has size `1 <<< accuracyLog`.
These establish the foundation for the harder conjuncts of `ValidFseTable`
(symbol bounds, numBits bounds) in future work. -/

open Zip.Native in
/-- When `buildFseTable` succeeds, the returned accuracy log equals the
    input accuracy log. This follows directly from the definition of
    `buildFseTable` which wraps `buildFseTableCells` with unchanged
    `accuracyLog`. -/
theorem buildFseTable_accuracyLog_eq (probs : Array Int32) (al : Nat)
    (table : FseTable) (h : buildFseTable probs al = .ok table) :
    table.accuracyLog = al := by
  simp only [buildFseTable, Except.ok.injEq] at h
  rw [← h]

/-- `List.forIn'.loop` in `Id` preserves any property `P` when every step
    yields a result satisfying `P`. -/
private theorem forIn'_loop_inv {α β : Type}
    (as : List α) (f : (a : α) → a ∈ as → β → Id (ForInStep β))
    (P : β → Prop)
    (hf : ∀ a (h : a ∈ as) b, P b →
      ∃ b', f a h b = ForInStep.yield b' ∧ P b')
    (rest : List α) (init : β) (hinit : P init)
    (hsuf : ∃ bs, bs ++ rest = as) :
    P (List.forIn'.loop (m := Id) as f rest init hsuf) := by
  induction rest generalizing init with
  | nil => rw [List.forIn'.loop.eq_1]; exact hinit
  | cons x xs ih =>
    rw [List.forIn'.loop.eq_2]; simp only [Bind.bind]
    have hx : x ∈ as := by
      obtain ⟨bs, hbs⟩ := hsuf; rw [← hbs]
      exact List.mem_append_right bs (List.Mem.head xs)
    obtain ⟨b', hb'eq, hb'P⟩ := hf x hx init hinit
    simp [hb'eq]; exact ih b' hb'P _

/-- `forIn` on `Std.Legacy.Range` in `Id` equals `forIn` on
    the corresponding `List.range'`. -/
private theorem range_forIn_eq_list_forIn {β : Type} (n : Nat) (init : β)
    (f : Nat → β → Id (ForInStep β)) :
    forIn (m := Id) [:n] init f = forIn (m := Id) (List.range' 0 n 1) init f := by
  show ForIn.forIn [:n] init f = ForIn.forIn (List.range' 0 n 1) init f
  unfold ForIn.forIn; simp only [instForInOfForIn']
  rw [Std.Legacy.Range.forIn'_eq_forIn'_range']
  simp [Std.Legacy.Range.size]

/-- `forIn` on `[:n]` in `Id` preserves any property `P` when every step
    yields a result satisfying `P`. -/
private theorem range_forIn_inv {β : Type} (n : Nat) (init : β)
    (f : Nat → β → Id (ForInStep β)) (P : β → Prop) (hinit : P init)
    (hf : ∀ a b, P b → ∃ b', f a b = ForInStep.yield b' ∧ P b') :
    P (forIn (m := Id) [:n] init f) := by
  rw [range_forIn_eq_list_forIn]
  show P (List.forIn'.loop (m := Id) _ (fun a _ b => f a b) _ init ⟨[], by simp⟩)
  exact forIn'_loop_inv _ (fun a _ b => f a b) P
    (fun a _ b hb => hf a b hb) _ init hinit _

/-- Specialized invariant for `forIn` on `[:n]` in `Id`: if every step
    preserves `fst.size = k` and the `heq` equation decomposes the result,
    then `result.size = k`. The body function `f` is resolved from `heq`
    (which is elaborated first), ensuring `f` is concrete when proving `hf`. -/
private theorem forIn_fst_size_of_heq {α β : Type} {n k : Nat}
    {init : MProd (Array α) β}
    {f : Nat → MProd (Array α) β → Id (ForInStep (MProd (Array α) β))}
    {result : Array α} {rest : β}
    (heq : forIn (m := Id) [:n] init f = ⟨result, rest⟩)
    (hinit : init.fst.size = k)
    (hf : ∀ a b, b.fst.size = k → ∃ b', f a b = ForInStep.yield b' ∧ b'.fst.size = k) :
    result.size = k := by
  have h := range_forIn_inv n init f (fun r => r.fst.size = k) hinit hf
  rw [heq] at h; exact h

open Zip.Native in
/-- When `buildFseTable` succeeds, the cells array has size `1 <<< al`.
    This follows because `buildFseTableCells` initializes cells with
    `Array.replicate (1 <<< al) default` and only modifies them via
    `Array.set!` which preserves size. -/
theorem buildFseTable_cells_size (probs : Array Int32) (al : Nat)
    (table : FseTable) (h : buildFseTable probs al = .ok table) :
    table.cells.size = 1 <<< al := by
  simp only [buildFseTable, Except.ok.injEq] at h
  rw [← h]
  unfold buildFseTableCells
  simp only [Id.run, pure, Pure.pure, Bind.bind]
  -- Destructure the 3 sequential match/forIn passes
  split; rename_i r₁ cells₁ _ _ heq₁
  split; rename_i r₂ cells₂ _ heq₂
  split; rename_i r₃ cells₃ _ heq₃
  -- Pass 1: cells₁.size = 1 <<< al (yield-only, set! preserves size)
  have h₁ : cells₁.size = 1 <<< al :=
    forIn_fst_size_of_heq heq₁ (by simp) (fun _ b hb => by
      split
      · exact ⟨_, rfl, by simp [Array.size_setIfInBounds, hb]⟩
      · exact ⟨_, rfl, hb⟩)
  -- Pass 2: cells₂.size = 1 <<< al (nested inner loop, but set! preserves size)
  have h₂ : cells₂.size = 1 <<< al :=
    forIn_fst_size_of_heq heq₂ h₁ (fun _ b hb => by
      split
      · exact ⟨_, rfl, hb⟩  -- prob ≤ 0: fst unchanged
      · -- else case: inner forIn + match destructuring
        split; rename_i ic ip heq_inner
        exact ⟨⟨ic, ip⟩, rfl, forIn_fst_size_of_heq heq_inner hb
          (fun _ b' h' => ⟨_, rfl, by simp [Array.size_setIfInBounds, h']⟩)⟩)
  -- Pass 4: cells₃.size = 1 <<< al (set! preserves size)
  have h₃ : cells₃.size = 1 <<< al :=
    forIn_fst_size_of_heq heq₃ h₂ (fun _ b hb => by
      split
      · exact ⟨_, rfl, hb⟩  -- sym >= probs.size
      · split
        · exact ⟨_, rfl, hb⟩  -- count == 0
        · exact ⟨_, rfl, by simp [Array.size_setIfInBounds, hb]⟩)
  exact h₃

end Zstd.Spec.Fse
