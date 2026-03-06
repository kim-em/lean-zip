import Zip.Native.ZstdSequence

/-!
# Zstd Sequence Validity and Execution Invariants (RFC 8878 §3.1.1.4–5)

Formal specification of Zstd sequence execution semantics and validity
constraints. Defines what constitutes valid decoded sequences independently
of the decoder implementation:

- `ValidSequence`: a single sequence triple has valid literal length,
  positive offset, and offset within reach of already-produced output
- `ValidSequenceList`: a sequence array doesn't consume more literals
  than available
- `ValidOffsetHistory`: the 3-entry offset history has exactly 3 positive
  entries (RFC 8878 §3.1.1.5 initial values: 1, 4, 8)

Correctness theorems relate the implementation (`resolveOffset`,
`executeSequences`) to these predicates.
-/

namespace Zstd.Spec.Sequence

open Zip.Native (ZstdSequence resolveOffset executeSequences)

/-! ## Validity predicates -/

/-- A single decoded sequence is valid in the context of the current output size
    and remaining literals:
    (a) the literal copy doesn't exceed available literals,
    (b) the resolved offset is positive (no zero offsets), and
    (c) the resolved offset doesn't reach beyond the output produced so far
        plus the literals this sequence will append. -/
def ValidSequence (seq : ZstdSequence) (outputSoFar : Nat) (literalsRemaining : Nat) : Prop :=
  seq.literalLength ≤ literalsRemaining ∧
  seq.offset > 0 ∧
  seq.offset ≤ outputSoFar + seq.literalLength

instance : Decidable (ValidSequence seq outputSoFar literalsRemaining) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- A sequence array is valid with respect to a total literals count when the
    sum of all `literalLength` fields does not exceed the total available
    literals. This is a necessary condition for `executeSequences` to succeed
    without a "not enough literals" error. -/
def ValidSequenceList (seqs : Array ZstdSequence) (totalLiterals : Nat) : Prop :=
  seqs.foldl (fun acc s => acc + s.literalLength) 0 ≤ totalLiterals

instance : Decidable (ValidSequenceList seqs totalLiterals) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- A valid offset history has exactly 3 entries, all positive (RFC 8878 §3.1.1.5).
    The initial offset history is `#[1, 4, 8]`. Uses `get!` to match the
    implementation's `history[i]!` access pattern. -/
def ValidOffsetHistory (history : Array Nat) : Prop :=
  history.size = 3 ∧ history[0]! > 0 ∧ history[1]! > 0 ∧ history[2]! > 0

instance {history : Array Nat} : Decidable (ValidOffsetHistory history) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-! ## Correctness theorems -/

/-- `resolveOffset` preserves the offset history size: if the input history has
    exactly 3 entries, the output history also has exactly 3 entries. This follows
    from every branch of the implementation constructing `#[_, _, _]` or returning
    the history unchanged. -/
theorem resolveOffset_history_size (rawOffset : Nat) (history : Array Nat) (litLen : Nat)
    (h : history.size = 3) :
    (resolveOffset rawOffset history litLen).2.size = 3 := by
  unfold resolveOffset
  split
  · -- rawOffset > 3: history' := #[offset, history[0]!, history[1]!]
    rfl
  · split
    · -- literalLength > 0: normal repeat offset mode
      split
      · -- rawOffset = 1: history unchanged
        exact h
      · -- rawOffset = 2: #[_, _, _]
        rfl
      · -- rawOffset = 3: #[_, _, _]
        rfl
      · -- fallback
        exact h
    · -- literalLength = 0: shifted repeat mode
      split
      · -- rawOffset = 1: #[_, _, _]
        rfl
      · -- rawOffset = 2: #[_, _, _]
        rfl
      · -- rawOffset = 3: #[_, _, _]
        rfl
      · -- fallback
        exact h

/-- When `resolveOffset` is called with `rawOffset > 3`, the resolved offset
    is `rawOffset - 3`, which is positive. -/
theorem resolveOffset_positive_large (rawOffset : Nat) (history : Array Nat) (litLen : Nat)
    (hraw : rawOffset > 3) :
    (resolveOffset rawOffset history litLen).1 > 0 := by
  unfold resolveOffset
  simp [show rawOffset > 3 from hraw]
  omega

/-- When `resolveOffset` is called with a valid offset history, `rawOffset > 0`,
    and `literalLength > 0`, the resolved offset is positive. This covers the
    normal repeat offset case (rawOffset 1–3 returns a history entry, all positive
    by `ValidOffsetHistory`) and actual offsets (rawOffset > 3 gives rawOffset - 3 > 0).
    The `literalLength = 0` case is excluded because rawOffset = 3 with litLen = 0
    gives `history[0] - 1` which can be 0 when `history[0] = 1`. -/
theorem resolveOffset_positive_litLen_pos (rawOffset : Nat) (history : Array Nat) (litLen : Nat)
    (hraw : rawOffset > 0) (hvalid : ValidOffsetHistory history) (hlit : litLen > 0) :
    (resolveOffset rawOffset history litLen).1 > 0 := by
  obtain ⟨_, h0pos, h1pos, h2pos⟩ := hvalid
  -- Case split on rawOffset: 0 (impossible), 1, 2, 3, or ≥ 4
  rcases rawOffset with _ | _ | _ | _ | n
  · omega  -- rawOffset = 0, contradicts hraw
  · -- rawOffset = 1, litLen > 0: returns history[0]!
    simp [resolveOffset, show ¬(1 > 3) from by omega, show litLen > 0 from hlit]
    exact h0pos
  · -- rawOffset = 2, litLen > 0: returns history[1]!
    simp [resolveOffset, show ¬(2 > 3) from by omega, show litLen > 0 from hlit]
    exact h1pos
  · -- rawOffset = 3, litLen > 0: returns history[2]!
    simp [resolveOffset, show ¬(3 > 3) from by omega, show litLen > 0 from hlit]
    exact h2pos
  · -- rawOffset = n + 4 > 3: offset = n + 1 > 0
    simp [resolveOffset, show n + 4 > 3 from by omega]

/-- The initial offset history `#[1, 4, 8]` is valid. -/
theorem initial_history_valid : ValidOffsetHistory #[1, 4, 8] := by decide

/-- `executeSequences` output size characterization: when `executeSequences`
    succeeds with an empty window prefix, the output contains exactly the
    literal bytes consumed plus match bytes copied. The proof requires deep
    unfolding of the monadic `for` loop and `copyMatch`, so it is deferred. -/
theorem executeSequences_output_length (seqs : Array ZstdSequence) (literals : ByteArray)
    (history : Array Nat) (output : ByteArray) (history' : Array Nat)
    (h : executeSequences seqs literals ByteArray.empty history = .ok (output, history')) :
    output.size = literals.size +
      seqs.foldl (fun acc s => acc + s.matchLength) 0 := by
  sorry

end Zstd.Spec.Sequence
