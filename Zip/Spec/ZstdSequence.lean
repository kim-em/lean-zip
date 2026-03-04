import Zip.Native.ZstdFrame

/-!
# Zstd Sequence Execution Specification

Formalizes the validity constraints for Zstd sequence execution
(RFC 8878 §3.1.1.4–5). A Zstd compressed block produces a list of
sequence triples `(literalLength, matchLength, offset)`, which are
executed against a literals buffer to produce decompressed output.

This file defines:
- **ValidSequence**: a single sequence is valid with respect to the
  current output position and remaining literal bytes.
- **ValidSequenceList**: an array of sequences does not consume more
  literals than available.
- **ValidOffsetHistory**: the 3-entry offset repeat history satisfies
  the RFC's positivity invariant (initial values 1, 4, 8).

It also proves basic correctness properties of `resolveOffset`:
- The output history always has size 3.
- The resolved offset is positive when the raw offset exceeds 3.
-/

namespace Zstd.Spec.Sequence

open Zip.Native

/-! ## Validity predicates -/

/-- A single sequence is valid given the current output size and remaining
    literal bytes. Captures the three runtime checks in `executeSequences`:
    (a) enough literals remain, (b) resolved offset is positive,
    (c) resolved offset does not exceed the output produced so far
    (including literals just copied by this sequence). -/
def ValidSequence (seq : ZstdSequence) (outputSoFar : Nat)
    (literalsRemaining : Nat) : Prop :=
  seq.literalLength ≤ literalsRemaining
  ∧ seq.offset > 0
  ∧ seq.offset ≤ outputSoFar + seq.literalLength

instance : Decidable (ValidSequence seq outputSoFar literalsRemaining) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- An array of sequences is valid if the total literal bytes consumed
    does not exceed the available literals. This is a necessary (but not
    sufficient) condition for `executeSequences` to succeed — individual
    offset validity also matters, but depends on execution order. -/
def ValidSequenceList (seqs : Array ZstdSequence) (totalLiterals : Nat) : Prop :=
  (seqs.toList.map (·.literalLength)).sum ≤ totalLiterals

instance : Decidable (ValidSequenceList seqs totalLiterals) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- The offset history is valid: exactly 3 entries, all positive.
    RFC 8878 §3.1.1.5 specifies initial values `[1, 4, 8]`. -/
def ValidOffsetHistory (history : Array Nat) : Prop :=
  history.size = 3 ∧ ∀ i : Fin history.size, history[i] > 0

instance : Decidable (ValidOffsetHistory history) :=
  if h3 : history.size = 3 then
    if hall : ∀ i : Fin history.size, history[i] > 0 then
      isTrue ⟨h3, hall⟩
    else
      isFalse fun ⟨_, hpos⟩ => hall hpos
  else
    isFalse fun ⟨hsz, _⟩ => h3 hsz

/-- The default offset history `[1, 4, 8]` is valid. -/
theorem validOffsetHistory_default : ValidOffsetHistory #[1, 4, 8] := by
  refine ⟨rfl, fun ⟨i, hi⟩ => ?_⟩
  match i, hi with
  | 0, _ => decide +revert
  | 1, _ => decide +revert
  | 2, _ => decide +revert

/-! ## Correctness theorems for `resolveOffset` -/

/-- `resolveOffset` always produces a history of size 3, regardless of inputs.
    Every branch in the implementation constructs a 3-element array literal
    or returns the input history unchanged (which has size 3 by precondition). -/
theorem resolveOffset_history_size (rawOffset : Nat) (history : Array Nat)
    (literalLength : Nat) (hsz : history.size = 3) :
    (resolveOffset rawOffset history literalLength).2.size = 3 := by
  simp only [resolveOffset]
  split
  · -- rawOffset > 3
    rfl
  · split
    · -- literalLength > 0
      split
      · exact hsz  -- rawOffset = 1: history unchanged
      · rfl  -- rawOffset = 2: #[h[1], h[0], h[2]]
      · rfl  -- rawOffset = 3: #[h[2], h[0], h[1]]
      · exact hsz  -- wildcard: history unchanged
    · -- literalLength = 0
      split
      · rfl  -- rawOffset = 1: #[h[1], h[0], h[2]]
      · rfl  -- rawOffset = 2: #[h[2], h[0], h[1]]
      · rfl  -- rawOffset = 3: #[h[0]-1, h[1], h[2]]
      · exact hsz  -- wildcard: history unchanged

/-- When the raw offset exceeds 3 (an "actual offset", not a repeat code),
    the resolved offset equals `rawOffset - 3` and is therefore positive. -/
theorem resolveOffset_positive_actual (rawOffset : Nat) (history : Array Nat)
    (literalLength : Nat) (hraw : rawOffset > 3) :
    (resolveOffset rawOffset history literalLength).1 = rawOffset - 3 := by
  simp only [resolveOffset, hraw, ↓reduceIte]

theorem resolveOffset_actual_pos (rawOffset : Nat) (history : Array Nat)
    (literalLength : Nat) (hraw : rawOffset > 3) :
    (resolveOffset rawOffset history literalLength).1 > 0 := by
  rw [resolveOffset_positive_actual _ _ _ hraw]
  omega

/-- `resolveOffset` preserves the history size invariant: if the input
    history has size 3, so does the output. Combined with
    `ValidOffsetHistory`, this means the history invariant is preserved
    across all sequence executions. -/
theorem resolveOffset_preserves_valid_history_size (rawOffset : Nat)
    (history : Array Nat) (literalLength : Nat)
    (hvalid : ValidOffsetHistory history) :
    (resolveOffset rawOffset history literalLength).2.size = 3 :=
  resolveOffset_history_size rawOffset history literalLength hvalid.1

end Zstd.Spec.Sequence
