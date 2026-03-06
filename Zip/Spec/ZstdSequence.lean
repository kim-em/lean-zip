import Zip.Native.ZstdSequence
import ZipForStd.ByteArray

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

/-! ## Size lemmas for sequence execution helpers -/

namespace Zip.Native

/-- `copyBytes` increases destination size by exactly `count`. -/
theorem copyBytes_size (dst : ByteArray) (src : ByteArray) (srcPos count : Nat) :
    (copyBytes dst src srcPos count).size = dst.size + count := by
  induction count generalizing dst srcPos with
  | zero => simp [copyBytes]
  | succ n ih =>
    rw [copyBytes.eq_1]
    simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    rw [ih, ByteArray.size_push]; omega

/-- `copyBytes` preserves existing destination bytes: for `i < dst.size`,
    `(copyBytes dst src srcPos count)[i]! = dst[i]!`. -/
theorem copyBytes_getElem_lt (dst src : ByteArray) (srcPos count : Nat) (i : Nat)
    (hi : i < dst.size) :
    (copyBytes dst src srcPos count)[i]! = dst[i]! := by
  induction count generalizing dst srcPos with
  | zero => simp [copyBytes]
  | succ n ih =>
    rw [copyBytes.eq_1]
    simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    rw [ih (dst.push src[srcPos]!) (srcPos + 1) (by simp [ByteArray.size_push]; omega)]
    exact ByteArray.push_getElem!_lt dst src[srcPos]! i hi

/-- `copyBytes` content at new positions: the j-th new byte equals `src[srcPos + j]!`.
    For `j < count` with `srcPos + j < src.size`,
    `(copyBytes dst src srcPos count)[dst.size + j]! = src[srcPos + j]!`. -/
theorem copyBytes_getElem_ge (dst src : ByteArray) (srcPos count : Nat) (j : Nat)
    (hj : j < count) (hsrc : srcPos + count ≤ src.size) :
    (copyBytes dst src srcPos count)[dst.size + j]! = src[srcPos + j]! := by
  induction count generalizing dst srcPos j with
  | zero => omega
  | succ n ih =>
    rw [copyBytes.eq_1]
    simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    cases j with
    | zero =>
      -- The first new byte: after pushing src[srcPos]!, it's at dst.size
      simp only [Nat.add_zero]
      rw [copyBytes_getElem_lt _ _ _ _ dst.size (by simp [ByteArray.size_push])]
      exact ByteArray.push_getElem!_eq dst src[srcPos]!
    | succ j' =>
      -- Later new bytes: use the IH on the recursive call
      have : dst.size + (j' + 1) = (dst.push src[srcPos]!).size + j' := by
        simp [ByteArray.size_push]; omega
      rw [this, ih (dst.push src[srcPos]!) (srcPos + 1) j' (by omega) (by omega)]
      congr 1; omega

private theorem copyMatch_loop_size (offset length start : Nat) (b : ByteArray) (k : Nat)
    (hk : k ≤ length) :
    (copyMatch.loop offset length start b k).size = b.size + (length - k) := by
  rw [copyMatch.loop.eq_1]
  split
  · rename_i hlt
    rw [copyMatch_loop_size offset length start _ (k + 1) (by omega), ByteArray.size_push]; omega
  · rename_i hge; omega
  termination_by length - k

/-- `copyMatch` increases buffer size by exactly `length`. -/
theorem copyMatch_size (buf : ByteArray) (offset length : Nat) :
    (copyMatch buf offset length).size = buf.size + length := by
  unfold copyMatch
  exact copyMatch_loop_size offset length (buf.size - offset) buf 0 (Nat.zero_le _)

private theorem copyMatch_loop_getElem_lt (offset length start : Nat) (b : ByteArray)
    (k : Nat) (_hk : k ≤ length) (i : Nat) (hi : i < b.size) :
    (copyMatch.loop offset length start b k)[i]! = b[i]! := by
  rw [copyMatch.loop.eq_1]
  split
  · rename_i hlt
    rw [copyMatch_loop_getElem_lt offset length start _ (k + 1) (by omega) i
      (by simp [ByteArray.size_push]; omega)]
    exact ByteArray.push_getElem!_lt b _ i hi
  · rfl
  termination_by length - k

/-- `copyMatch` preserves existing buffer bytes: for `i < buf.size`,
    `(copyMatch buf offset length)[i]! = buf[i]!`. -/
theorem copyMatch_getElem_lt (buf : ByteArray) (offset length : Nat) (i : Nat)
    (hi : i < buf.size) :
    (copyMatch buf offset length)[i]! = buf[i]! := by
  unfold copyMatch
  exact copyMatch_loop_getElem_lt offset length (buf.size - offset) buf 0 (Nat.zero_le _) i hi

private theorem copyMatch_loop_getElem_ge_nonoverlap (offset length start : Nat)
    (buf b : ByteArray) (k j : Nat)
    (hoff : offset ≥ length)
    (hstart : start = buf.size - offset)
    (hreach : offset ≤ buf.size)
    (hbsize : b.size = buf.size + k)
    (hprefix : ∀ i, i < buf.size → b[i]! = buf[i]!)
    (hk : k ≤ length)
    (hj : j < length - k) :
    (copyMatch.loop offset length start b k)[b.size + j]! = buf[start + (k + j)]! := by
  rw [copyMatch.loop.eq_1]
  have hklt : k < length := by omega
  simp only [hklt, ↓reduceIte]
  have hkmod : k % offset = k := Nat.mod_eq_of_lt (by omega)
  have hsk : start + k < buf.size := by omega
  rw [hkmod]
  cases j with
  | zero =>
    simp only [Nat.add_zero]
    rw [copyMatch_loop_getElem_lt offset length start _ (k + 1) (by omega)
      b.size (by simp [ByteArray.size_push])]
    rw [ByteArray.push_getElem!_eq]
    exact hprefix _ hsk
  | succ j' =>
    have heq : b.size + (j' + 1) = (b.push b[start + k]!).size + j' := by
      simp [ByteArray.size_push]; omega
    rw [heq, copyMatch_loop_getElem_ge_nonoverlap offset length start buf _ (k + 1) j'
      hoff hstart hreach (by simp [ByteArray.size_push, hbsize]; omega)
      (fun i hi => by rw [ByteArray.push_getElem!_lt _ _ _ (by omega)]; exact hprefix i hi)
      (by omega) (by omega)]
    congr 1; omega
  termination_by length - k

/-- `copyMatch` content at new positions (non-overlapping case): when `offset ≥ length`,
    the j-th new byte equals the byte `offset` positions back in the original buffer.
    For `j < length`, `(copyMatch buf offset length)[buf.size + j]! = buf[buf.size - offset + j]!`.
    Combined with `copyMatch_getElem_lt` and `copyMatch_size`, this fully specifies `copyMatch`
    when the source region doesn't overlap the destination. -/
theorem copyMatch_getElem_ge_nonoverlap (buf : ByteArray) (offset length : Nat) (j : Nat)
    (hoff : offset ≥ length) (hreach : offset ≤ buf.size) (hj : j < length) :
    (copyMatch buf offset length)[buf.size + j]! = buf[buf.size - offset + j]! := by
  unfold copyMatch
  simp only
  have := copyMatch_loop_getElem_ge_nonoverlap offset length (buf.size - offset) buf buf 0 j
    hoff rfl hreach rfl (fun _ _ => rfl) (Nat.zero_le _) (by omega)
  simp only [Nat.zero_add] at this
  exact this

private theorem foldl_matchLen_add (init : Nat) (seqs : List ZstdSequence) :
    List.foldl (fun acc (s : ZstdSequence) => acc + s.matchLength) init seqs =
    init + List.foldl (fun acc (s : ZstdSequence) => acc + s.matchLength) 0 seqs := by
  induction seqs generalizing init with
  | nil => simp
  | cons s rest ih =>
    simp only [List.foldl_cons]
    rw [ih, ih 0, ih (0 + s.matchLength)]
    omega

/-- Loop invariant: if `executeSequences.loop` succeeds, the output size equals
    initial output size + literals consumed + match bytes, and litPos bounds hold. -/
theorem executeSequences_loop_inv (seqs : List ZstdSequence) (literals : ByteArray)
    (output : ByteArray) (history : Array Nat) (litPos : Nat) (windowSize : Nat)
    (output' : ByteArray) (history' : Array Nat) (litPos' : Nat)
    (hlp : litPos ≤ literals.size)
    (h : executeSequences.loop seqs literals output history litPos windowSize
         = .ok (output', history', litPos')) :
    output'.size = output.size + (litPos' - litPos) +
      List.foldl (fun acc (s : ZstdSequence) => acc + s.matchLength) 0 seqs
    ∧ litPos ≤ litPos'
    ∧ litPos' ≤ literals.size := by
  induction seqs generalizing output history litPos with
  | nil =>
    rw [executeSequences.loop.eq_1] at h
    simp at h
    obtain ⟨rfl, _, rfl⟩ := h
    exact ⟨by simp, Nat.le_refl _, hlp⟩
  | cons seq rest ih =>
    rw [executeSequences.loop.eq_2] at h
    split at h
    · simp at h
    · rename_i hlit
      split at h
      dsimp only [letFun] at h
      split at h
      · simp at h
      · split at h
        · simp at h
        · split at h
          · simp at h
          · have hlp' : litPos + seq.literalLength ≤ literals.size := by omega
            have ⟨ih_size, ih_le, ih_bound⟩ := ih _ _ _ hlp' h
            rw [copyMatch_size, copyBytes_size] at ih_size
            refine ⟨?_, ?_, ih_bound⟩
            · rw [ih_size]
              simp only [List.foldl_cons, Nat.zero_add]
              conv => rhs; rw [foldl_matchLen_add]
              generalize List.foldl (fun acc s => acc + s.matchLength) 0 rest = matchSum
              omega
            · omega

/-- The `executeSequences.loop` output buffer is always at least as large as the
    input buffer. Each iteration copies literal bytes then match bytes, both of
    which only grow the buffer. This monotonicity property is the key invariant
    for inductive arguments about the loop. -/
theorem executeSequences_loop_output_size_ge
    (seqs : List ZstdSequence) (literals : ByteArray)
    (output : ByteArray) (history : Array Nat) (litPos windowSize : Nat)
    (result : ByteArray × Array Nat × Nat)
    (h : executeSequences.loop seqs literals output history litPos windowSize
         = .ok result) :
    result.1.size ≥ output.size := by
  induction seqs generalizing output history litPos with
  | nil =>
    rw [executeSequences.loop.eq_1] at h
    simp only [Except.ok.injEq] at h
    subst h; simp
  | cons seq rest ih =>
    rw [executeSequences.loop.eq_2] at h
    split at h
    · simp at h
    · rename_i hlit
      split at h
      simp only [letFun] at h
      split at h
      · simp at h
      · split at h
        · simp at h
        · split at h
          · simp at h
          · have := ih _ _ _ h
            rw [copyMatch_size, copyBytes_size] at this
            omega

end Zip.Native

namespace Zstd.Spec.Sequence

open Zip.Native (ZstdSequence resolveOffset executeSequences
  executeSequences_loop_inv copyBytes_size copyMatch_size
  litLenExtraBits matchLenExtraBits decodeLitLenValue decodeMatchLenValue decodeOffsetValue)

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
  simp only [show rawOffset > 3 from hraw, ↓reduceIte]
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
    simp only [resolveOffset, show ¬(1 > 3) from by omega, show litLen > 0 from hlit,
      ↓reduceIte]
    exact h0pos
  · -- rawOffset = 2, litLen > 0: returns history[1]!
    simp only [resolveOffset, show ¬(2 > 3) from by omega, show litLen > 0 from hlit,
      ↓reduceIte]
    exact h1pos
  · -- rawOffset = 3, litLen > 0: returns history[2]!
    simp only [resolveOffset, show ¬(3 > 3) from by omega, show litLen > 0 from hlit,
      ↓reduceIte]
    exact h2pos
  · -- rawOffset = n + 4 > 3: offset = n + 1 > 0
    simp only [resolveOffset, show n + 4 > 3 from by omega, ↓reduceIte]
    omega

/-- When `rawOffset = 1`, `history.size = 3`, and `literalLength > 0`, the resolved
    offset equals `history[0]!` (the most recent offset). This is the exact value
    returned by the RFC 8878 §3.1.1.5 repeat offset mechanism for code 1. -/
theorem resolveOffset_repeat1_val (history : Array Nat) (litLen : Nat)
    (_hsize : history.size = 3) (hlit : litLen > 0) :
    (resolveOffset 1 history litLen).1 = history[0]! := by
  simp only [resolveOffset, show ¬(1 > 3) from by omega, show litLen > 0 from hlit, ↓reduceIte]

/-- When `rawOffset = 2`, `history.size = 3`, and `literalLength > 0`, the resolved
    offset equals `history[1]!` (the second most recent offset). -/
theorem resolveOffset_repeat2_val (history : Array Nat) (litLen : Nat)
    (_hsize : history.size = 3) (hlit : litLen > 0) :
    (resolveOffset 2 history litLen).1 = history[1]! := by
  simp only [resolveOffset, show ¬(2 > 3) from by omega, show litLen > 0 from hlit, ↓reduceIte]

/-- When `rawOffset = 3`, `history.size = 3`, and `literalLength > 0`, the resolved
    offset equals `history[2]!` (the third most recent offset). -/
theorem resolveOffset_repeat3_val (history : Array Nat) (litLen : Nat)
    (_hsize : history.size = 3) (hlit : litLen > 0) :
    (resolveOffset 3 history litLen).1 = history[2]! := by
  simp only [resolveOffset, show ¬(3 > 3) from by omega, show litLen > 0 from hlit, ↓reduceIte]

/-- When `rawOffset = 1`, `history.size = 3`, and `literalLength = 0` (shifted mode),
    the resolved offset equals `history[1]!` (second most recent) and the history
    becomes `#[history[1]!, history[0]!, history[2]!]`. RFC 8878 §3.1.1.5 shifted case. -/
theorem resolveOffset_shifted1_val (history : Array Nat)
    (_hsize : history.size = 3) :
    (resolveOffset 1 history 0).1 = history[1]!
    ∧ (resolveOffset 1 history 0).2 = #[history[1]!, history[0]!, history[2]!] := by
  simp only [resolveOffset, show ¬(1 > 3) from by omega, show ¬(0 > 0) from by omega,
    ↓reduceIte, and_self]

/-- When `rawOffset = 2`, `history.size = 3`, and `literalLength = 0` (shifted mode),
    the resolved offset equals `history[2]!` (third most recent) and the history
    becomes `#[history[2]!, history[0]!, history[1]!]`. RFC 8878 §3.1.1.5 shifted case. -/
theorem resolveOffset_shifted2_val (history : Array Nat)
    (_hsize : history.size = 3) :
    (resolveOffset 2 history 0).1 = history[2]!
    ∧ (resolveOffset 2 history 0).2 = #[history[2]!, history[0]!, history[1]!] := by
  simp only [resolveOffset, show ¬(2 > 3) from by omega, show ¬(0 > 0) from by omega,
    ↓reduceIte, and_self]

/-- When `rawOffset = 3`, `history.size = 3`, and `literalLength = 0` (shifted mode),
    the resolved offset equals `history[0]! - 1` (most recent minus one) and the history
    becomes `#[history[0]! - 1, history[1]!, history[2]!]`. RFC 8878 §3.1.1.5 shifted case.
    This is the special case used for run-length encoding patterns. -/
theorem resolveOffset_shifted3_val (history : Array Nat)
    (_hsize : history.size = 3) :
    (resolveOffset 3 history 0).1 = history[0]! - 1
    ∧ (resolveOffset 3 history 0).2 = #[history[0]! - 1, history[1]!, history[2]!] := by
  simp only [resolveOffset, show ¬(3 > 3) from by omega, show ¬(0 > 0) from by omega,
    ↓reduceIte, and_self]

/-- When `rawOffset > 3` and input has `ValidOffsetHistory`, the output history
    also satisfies `ValidOffsetHistory`. The new history is
    `#[rawOffset - 3, history[0]!, history[1]!]`, all positive. -/
theorem resolveOffset_history_valid_large (rawOffset litLen : Nat)
    (history : Array Nat) (hh : ValidOffsetHistory history)
    (hr : rawOffset > 3) :
    ValidOffsetHistory (resolveOffset rawOffset history litLen).2 := by
  obtain ⟨_, h0pos, h1pos, _⟩ := hh
  simp only [resolveOffset, hr, ↓reduceIte, ValidOffsetHistory]
  refine ⟨rfl, ?_, ?_, ?_⟩ <;> simp <;> omega

/-- For repeat codes (rawOffset ∈ {1,2,3}), when input has `ValidOffsetHistory`
    and for the shifted rawOffset=3 case `history[0]! ≥ 2`, the output history
    satisfies `ValidOffsetHistory`. Covers both normal (litLen > 0) and shifted
    (litLen = 0) repeat offset modes per RFC 8878 §3.1.1.5. -/
theorem resolveOffset_history_valid_repeat (rawOffset litLen : Nat)
    (history : Array Nat) (hh : ValidOffsetHistory history)
    (hr : rawOffset > 0) (hr' : rawOffset ≤ 3)
    (hshift : litLen = 0 ∧ rawOffset = 3 → history[0]! ≥ 2) :
    ValidOffsetHistory (resolveOffset rawOffset history litLen).2 := by
  obtain ⟨hsz, h0pos, h1pos, h2pos⟩ := hh
  rcases rawOffset with _ | _ | _ | _ | n
  · omega  -- rawOffset = 0
  · -- rawOffset = 1
    unfold resolveOffset
    simp only [show ¬(1 > 3) from by omega, ↓reduceIte]
    split
    · exact ⟨hsz, h0pos, h1pos, h2pos⟩  -- litLen > 0: history unchanged
    · -- litLen = 0: #[history[1]!, history[0]!, history[2]!]
      refine ⟨rfl, ?_, ?_, ?_⟩ <;> simp <;> omega
  · -- rawOffset = 2
    unfold resolveOffset
    simp only [show ¬(2 > 3) from by omega, ↓reduceIte]
    split
    · -- litLen > 0: #[history[1]!, history[0]!, history[2]!]
      refine ⟨rfl, ?_, ?_, ?_⟩ <;> simp <;> omega
    · -- litLen = 0: #[history[2]!, history[0]!, history[1]!]
      refine ⟨rfl, ?_, ?_, ?_⟩ <;> simp <;> omega
  · -- rawOffset = 3
    unfold resolveOffset
    simp only [show ¬(3 > 3) from by omega, ↓reduceIte]
    split
    · -- litLen > 0: #[history[2]!, history[0]!, history[1]!]
      refine ⟨rfl, ?_, ?_, ?_⟩ <;> simp <;> omega
    · -- litLen = 0: #[history[0]! - 1, history[1]!, history[2]!]
      rename_i hlit
      have h02 := hshift ⟨by omega, rfl⟩
      refine ⟨rfl, ?_, ?_, ?_⟩ <;> simp <;> omega
  · omega  -- rawOffset ≥ 4

/-- The initial offset history `#[1, 4, 8]` is valid. -/
theorem initial_history_valid : ValidOffsetHistory #[1, 4, 8] := by decide

/-! ## Extra bits table correctness (RFC 8878 Tables 14–15) -/

/-- The literal length extra bits table has exactly 36 entries (codes 0–35, RFC 8878 Table 14). -/
theorem litLenExtraBits_size : litLenExtraBits.size = 36 := by rfl

/-- The match length extra bits table has exactly 53 entries (codes 0–52, RFC 8878 Table 15). -/
theorem matchLenExtraBits_size : matchLenExtraBits.size = 53 := by rfl

/-- For literal length codes 0–15, the decoded value equals `code + extraBits`
    (baseline equals code, zero extra bits in the table). This validates that
    the first 16 entries of RFC 8878 Table 14 are identity mappings. -/
theorem decodeLitLenValue_small (code : Nat) (extraBits : UInt32) (h : code ≤ 15) :
    decodeLitLenValue code extraBits = .ok (code + extraBits.toNat) := by
  have hlt : code < litLenExtraBits.size := by simp only [litLenExtraBits_size]; omega
  unfold decodeLitLenValue
  simp only [hlt, ↓reduceDIte]
  rcases code with _ | _ | _ | _ | _ | _ | _ | _ |
                   _ | _ | _ | _ | _ | _ | _ | _ | _
  all_goals first | omega | rfl

/-- For match length codes 0–31, the decoded value equals `code + 3 + extraBits`
    (baseline equals code + 3, zero extra bits in the table). This validates that
    the first 32 entries of RFC 8878 Table 15 are offset-by-3 identity mappings. -/
theorem decodeMatchLenValue_small (code : Nat) (extraBits : UInt32) (h : code ≤ 31) :
    decodeMatchLenValue code extraBits = .ok (code + 3 + extraBits.toNat) := by
  have hlt : code < matchLenExtraBits.size := by simp only [matchLenExtraBits_size]; omega
  unfold decodeMatchLenValue
  simp only [hlt, ↓reduceDIte]
  rcases code with _ | _ | _ | _ | _ | _ | _ | _ |
                   _ | _ | _ | _ | _ | _ | _ | _ |
                   _ | _ | _ | _ | _ | _ | _ | _ |
                   _ | _ | _ | _ | _ | _ | _ | _ | _
  all_goals first | omega | rfl

/-- When `code > 0`, `decodeOffsetValue` returns a positive value.
    This follows from `1 <<< code > 0` for any natural `code`. -/
theorem decodeOffsetValue_positive (code : Nat) (extraBits : UInt32) (hcode : code > 0) :
    decodeOffsetValue code extraBits > 0 := by
  unfold decodeOffsetValue
  split
  · rename_i h; simp only [beq_iff_eq] at h; omega
  · have : 1 <<< code ≥ 1 := by rw [Nat.one_shiftLeft]; exact Nat.one_le_two_pow
    omega

/-- `executeSequences` output size characterization: when `executeSequences`
    succeeds with an empty window prefix, the output contains exactly the
    literal bytes consumed plus match bytes copied. -/
theorem executeSequences_output_length (seqs : Array ZstdSequence) (literals : ByteArray)
    (history : Array Nat) (output : ByteArray) (history' : Array Nat)
    (h : executeSequences seqs literals ByteArray.empty history = .ok (output, history')) :
    output.size = literals.size +
      seqs.foldl (fun acc s => acc + s.matchLength) 0 := by
  unfold executeSequences at h
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h
  split at h
  · simp at h
  · rename_i v heq
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨hout, _⟩ := h
    have ⟨hsize, _, hbound⟩ := executeSequences_loop_inv _ _ _ _ _ _ _ _ _ (Nat.zero_le _) heq
    rw [ByteArray.size_empty, Nat.zero_add, Nat.sub_zero] at hsize
    rw [← hout, ByteArray.size_extract, copyBytes_size, hsize]
    rw [← Array.foldl_toList]
    simp only [Nat.min_self, ByteArray.size_empty]
    omega

/-! ## Base case and monotonicity for executeSequences -/

/-- When the sequence array is empty, `executeSequences` succeeds with block
    output of size equal to `literals.size`, and the offset history is unchanged.
    This is the base case for inductive arguments about sequence execution;
    Zstd frames with only raw or RLE blocks have no sequences, so this theorem
    directly characterizes their sequence execution step. -/
theorem executeSequences_empty (literals : ByteArray)
    (windowPrefix : ByteArray) (history : Array Nat) (windowSize : Nat)
    (blockOutput : ByteArray) (history' : Array Nat)
    (h : executeSequences #[] literals windowPrefix history windowSize
         = .ok (blockOutput, history')) :
    blockOutput.size = literals.size ∧ history' = history := by
  unfold executeSequences at h
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure,
    executeSequences.loop, Nat.sub_zero] at h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨hout, hhist⟩ := h
  exact ⟨by rw [← hout, ByteArray.size_extract, copyBytes_size]; omega, hhist.symm⟩

end Zstd.Spec.Sequence
