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
            rw [ih h, cellCount_push]
            have heq : Int32.ofNat val.fst - 1 = -1 := eq_of_beq hp1
            rw [heq]
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
  | error e => simp only [hrd, reduceCtorEq] at _h
  | ok val =>
    simp only [hrd] at _h
    by_cases hgt : val.fst.toNat + 5 > maxAccLog
    · rw [if_pos hgt] at _h; exact nomatch _h
    · rw [if_neg hgt] at _h
      cases hdl : decodeFseLoop val.snd (1 <<< (val.fst.toNat + 5)) #[] 0 maxSymbols 10000 with
      | error e => simp only [hdl, reduceCtorEq] at _h
      | ok dlval =>
        simp only [hdl] at _h
        split at _h
        · exact nomatch _h
        · simp only [Except.ok.injEq, Prod.mk.injEq] at _h
          obtain ⟨_, rfl, _⟩ := _h; omega

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
  | error e => simp only [hrd, reduceCtorEq] at _h
  | ok val =>
    simp only [hrd] at _h
    by_cases hgt : val.fst.toNat + 5 > maxAccLog
    · rw [if_pos hgt] at _h; exact nomatch _h
    · rw [if_neg hgt] at _h
      cases hdl : decodeFseLoop val.snd (1 <<< (val.fst.toNat + 5)) #[] 0 maxSymbols 10000 with
      | error e => simp only [hdl, reduceCtorEq] at _h
      | ok dlval =>
        simp only [hdl] at _h
        split at _h
        · exact nomatch _h
        · simp only [Except.ok.injEq, Prod.mk.injEq] at _h
          obtain ⟨_, rfl, _⟩ := _h; omega

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
  unfold decodeFseDistribution at _h
  cases hrd : br.readBits 4 with
  | error e => simp only [hrd, reduceCtorEq] at _h
  | ok val =>
    simp only [hrd] at _h
    by_cases hgt : val.fst.toNat + 5 > maxAccLog
    · rw [if_pos hgt] at _h; exact nomatch _h
    · rw [if_neg hgt] at _h
      cases hdl : decodeFseLoop val.snd (1 <<< (val.fst.toNat + 5)) #[] 0 maxSymbols 10000 with
      | error e => simp only [hdl, reduceCtorEq] at _h
      | ok dlval =>
        simp only [hdl] at _h
        by_cases hrem : dlval.1 != 0
        · rw [if_pos hrem] at _h; exact nomatch _h
        · rw [if_neg hrem] at _h
          simp only [Except.ok.injEq, Prod.mk.injEq] at _h
          obtain ⟨rfl, rfl, _⟩ := _h
          have hinv := decodeFseLoop_invariant hdl
          simp only [cellCount_empty, Nat.add_zero, bne_iff_ne, ne_eq,
            Decidable.not_not] at hinv hrem
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
  -- Shorthand for Except.ok.inj ∘ ForInStep.yield.inj extraction
  -- After simp [bind, ...], yield case gives Except.ok (yield X) = Except.ok (yield b')
  -- We extract X = b' via ForInStep.yield.inj (Except.ok.inj h)
  -- Loop 1 (place -1 probability symbols): cells.set! preserves size
  have hsize1 : v1.fst.size = 1 <<< al := by
    apply forIn_range_preserves (fun s => s.fst.size = 1 <<< al) _ _ _ _ _ _ _ hloop1
    · exact Array.size_replicate
    · intro a b b' hb heq
      simp only [bind, Except.bind, pure, Except.pure] at heq
      split at heq
      · rw [← ForInStep.yield.inj (Except.ok.inj heq)]
        simp only [Nat.toUInt16_eq, Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, hb]
      · rw [← ForInStep.yield.inj (Except.ok.inj heq)]; exact hb
    · intro a b b' hb heq
      simp only [bind, Except.bind, pure, Except.pure] at heq
      split at heq <;> exact nomatch heq
  -- Loop 2 (distribute symbols with stepping): cells.set! preserves size
  have hsize2 : v2.fst.size = 1 <<< al := by
    apply forIn_range_preserves (fun s => s.fst.size = 1 <<< al) _ _ _ _ _ _ _ hloop2
    · exact hsize1
    · intro a b b' hb heq
      simp only [bind, Except.bind, pure, Except.pure] at heq
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
            split at heq2
            · exact nomatch heq2
            · rw [← ForInStep.yield.inj (Except.ok.inj heq2)]
              simp only [Nat.toUInt16_eq, Array.set!_eq_setIfInBounds,
                Array.size_setIfInBounds, hb2]
          · intro a2 b2 b2' hb2 heq2
            split at heq2 <;> exact nomatch heq2
    · intro a b b' hb heq
      simp only [bind, Except.bind, pure, Except.pure] at heq
      split at heq
      · exact nomatch heq
      · split at heq <;> exact nomatch heq
  -- Loop 4 (compute numBits/newState): cells.set! preserves size
  apply forIn_range_preserves (fun s => s.fst.size = 1 <<< al) _ _ _ _ _ _ _ hloop4
  · exact hsize2
  · intro a b b' hb heq
    simp only [bind, Except.bind, pure, Except.pure] at heq
    split at heq
    · rw [← ForInStep.yield.inj (Except.ok.inj heq)]; exact hb
    · split at heq
      · rw [← ForInStep.yield.inj (Except.ok.inj heq)]; exact hb
      · rw [← ForInStep.yield.inj (Except.ok.inj heq)]
        simp only [Nat.toUInt8_eq, Nat.toUInt16_eq, Array.set!_eq_setIfInBounds,
          Array.size_setIfInBounds, hb]
  · intro a b b' hb heq
    simp only [bind, Except.bind, pure, Except.pure] at heq
    split at heq
    · exact nomatch heq
    · split at heq <;> exact nomatch heq

/-! ## BackwardBitReader base-case specs -/

open Zip.Native (BackwardBitReader) in
/-- `isFinished` is true iff `totalBitsRemaining` is zero. -/
theorem BackwardBitReader_isFinished_iff_totalBitsRemaining_zero
    (br : BackwardBitReader) :
    br.isFinished = true ↔ br.totalBitsRemaining = 0 := by
  simp only [BackwardBitReader.isFinished, BackwardBitReader.totalBitsRemaining]
  constructor
  · intro h; simp only [beq_iff_eq.mp h, BEq.rfl, ↓reduceIte]
  · intro h; split at h <;> simp_all only [beq_iff_eq, Nat.add_eq_zero_iff]

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

end Zstd.Spec.Fse
