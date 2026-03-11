import Zip.Native.ZstdSequence
import Zip.Spec.Fse
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
  | zero => simp only [copyBytes, ↓reduceIte]; omega
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
  | zero => simp only [copyBytes, ↓reduceIte]
  | succ n ih =>
    rw [copyBytes.eq_1]
    simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    rw [ih (dst.push src[srcPos]!) (srcPos + 1) (by simp only [ByteArray.size_push]; omega)]
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
      rw [copyBytes_getElem_lt _ _ _ _ dst.size (by simp only [ByteArray.size_push]; omega)]
      exact ByteArray.push_getElem!_eq dst src[srcPos]!
    | succ j' =>
      -- Later new bytes: use the IH on the recursive call
      have : dst.size + (j' + 1) = (dst.push src[srcPos]!).size + j' := by
        simp only [ByteArray.size_push]; omega
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
      (by simp only [ByteArray.size_push]; omega)]
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
      b.size (by simp only [ByteArray.size_push]; omega)]
    rw [ByteArray.push_getElem!_eq]
    exact hprefix _ hsk
  | succ j' =>
    have heq : b.size + (j' + 1) = (b.push b[start + k]!).size + j' := by
      simp only [ByteArray.size_push]; omega
    rw [heq, copyMatch_loop_getElem_ge_nonoverlap offset length start buf _ (k + 1) j'
      hoff hstart hreach (by simp only [ByteArray.size_push, hbsize]; omega)
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

private theorem copyMatch_loop_getElem_ge (offset length start : Nat)
    (buf b : ByteArray) (k j : Nat)
    (hoff : offset > 0) (hstart : start + offset = buf.size)
    (hbsize : b.size = buf.size + k)
    (hprefix : ∀ i, i < buf.size → b[i]! = buf[i]!)
    (hk : k ≤ length)
    (hj : j < length - k) :
    (copyMatch.loop offset length start b k)[b.size + j]! =
      buf[start + ((k + j) % offset)]! := by
  rw [copyMatch.loop.eq_1]
  have hklt : k < length := by omega
  simp only [hklt, ↓reduceIte]
  have hsk : start + (k % offset) < buf.size := by
    have := Nat.mod_lt k hoff; omega
  cases j with
  | zero =>
    simp only [Nat.add_zero]
    rw [copyMatch_loop_getElem_lt offset length start _ (k + 1) (by omega)
      b.size (by simp only [ByteArray.size_push]; omega)]
    rw [ByteArray.push_getElem!_eq]
    exact hprefix _ hsk
  | succ j' =>
    have heq : b.size + (j' + 1) = (b.push b[start + (k % offset)]!).size + j' := by
      simp only [ByteArray.size_push]; omega
    simp only [show k + (j' + 1) = k + 1 + j' from by omega]
    rw [heq, copyMatch_loop_getElem_ge offset length start buf _ (k + 1) j'
      hoff hstart (by simp only [ByteArray.size_push, hbsize]; omega)
      (fun i hi => by rw [ByteArray.push_getElem!_lt _ _ _ (by omega)]; exact hprefix i hi)
      (by omega) (by omega)]
  termination_by length - k

/-- `copyMatch` content at new positions (general case, including overlap): the j-th
    new byte equals the byte at position `buf.size - offset + (j % offset)` in the
    original buffer. This captures the cyclic repetition semantics of LZ77
    back-references (RFC 1951 §3.2.3, RFC 8878 §3.1.1.4).

    Combined with `copyMatch_getElem_lt` (preservation) and `copyMatch_size` (size),
    this fully specifies `copyMatch` for ALL cases — including overlapping matches
    used for run-length encoding and pattern repetition.

    Subsumes `copyMatch_getElem_ge_nonoverlap`: when `offset ≥ length`, `j < length`
    implies `j % offset = j` by `Nat.mod_eq_of_lt`. -/
theorem copyMatch_getElem_ge (buf : ByteArray) (offset length : Nat) (j : Nat)
    (hoff : offset > 0) (hreach : offset ≤ buf.size) (hj : j < length) :
    (copyMatch buf offset length)[buf.size + j]! =
      buf[buf.size - offset + (j % offset)]! := by
  unfold copyMatch
  simp only
  have := copyMatch_loop_getElem_ge offset length (buf.size - offset) buf buf 0 j
    hoff (by omega) rfl (fun _ _ => rfl) (Nat.zero_le _) (by omega)
  simp only [Nat.zero_add] at this
  exact this

private theorem foldl_matchLen_add (init : Nat) (seqs : List ZstdSequence) :
    List.foldl (fun acc (s : ZstdSequence) => acc + s.matchLength) init seqs =
    init + List.foldl (fun acc (s : ZstdSequence) => acc + s.matchLength) 0 seqs := by
  induction seqs generalizing init with
  | nil => simp only [List.foldl_nil, Nat.add_zero]
  | cons s rest ih =>
    simp only [List.foldl_cons]
    rw [ih, ih 0, ih (0 + s.matchLength)]
    omega

/-- Loop invariant: if `executeSequences.loop` succeeds, the output size equals
    initial output size + literals consumed + match bytes, litPos bounds hold,
    and the output is at least as large as the input (monotonicity). -/
theorem executeSequences_loop_inv (seqs : List ZstdSequence) (literals : ByteArray)
    (output : ByteArray) (history : Array Nat) (litPos : Nat) (windowSize : Nat)
    (output' : ByteArray) (history' : Array Nat) (litPos' : Nat)
    (hlp : litPos ≤ literals.size)
    (h : executeSequences.loop seqs literals output history litPos windowSize
         = .ok (output', history', litPos')) :
    output'.size = output.size + (litPos' - litPos) +
      List.foldl (fun acc (s : ZstdSequence) => acc + s.matchLength) 0 seqs
    ∧ litPos ≤ litPos'
    ∧ litPos' ≤ literals.size
    ∧ output'.size ≥ output.size := by
  induction seqs generalizing output history litPos with
  | nil =>
    rw [executeSequences.loop.eq_1] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _, rfl⟩ := h
    exact ⟨by simp only [List.foldl_nil]; omega, Nat.le_refl _, hlp, Nat.le_refl _⟩
  | cons seq rest ih =>
    rw [executeSequences.loop.eq_2] at h
    split at h; · exact nomatch h
    rename_i hlit
    split at h; dsimp only [letFun] at h
    split at h; · exact nomatch h
    split at h; · exact nomatch h
    split at h; · exact nomatch h
    have hlp' : litPos + seq.literalLength ≤ literals.size := by omega
    have ⟨ih_size, ih_le, ih_bound, ih_mono⟩ := ih _ _ _ hlp' h
    rw [copyMatch_size, copyBytes_size] at ih_size ih_mono
    refine ⟨?_, ?_, ih_bound, by omega⟩
    · rw [ih_size]
      simp only [List.foldl_cons, Nat.zero_add]
      conv => rhs; rw [foldl_matchLen_add]
      generalize List.foldl (fun acc s => acc + s.matchLength) 0 rest = matchSum
      omega
    · omega

/-- The `executeSequences.loop` output buffer is always at least as large as the
    input buffer. Corollary of `executeSequences_loop_inv`. -/
theorem executeSequences_loop_output_size_ge
    (seqs : List ZstdSequence) (literals : ByteArray)
    (output : ByteArray) (history : Array Nat) (litPos windowSize : Nat)
    (result : ByteArray × Array Nat × Nat)
    (h : executeSequences.loop seqs literals output history litPos windowSize
         = .ok result) :
    result.1.size ≥ output.size := by
  obtain ⟨output', history', litPos'⟩ := result
  show output'.size ≥ output.size
  cases seqs with
  | nil =>
    rw [executeSequences.loop.eq_1] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _, _⟩ := h; omega
  | cons seq rest =>
    have h' := h
    rw [executeSequences.loop.eq_2] at h'
    split at h'
    · exact nomatch h'
    · exact (executeSequences_loop_inv _ _ _ _ _ _ _ _ _ (by omega) h).2.2.2

/-- Single-step unfolding: when all guards pass, processing `seq :: rest` equals
    processing `rest` with the intermediate state after one copy-literal +
    resolve-offset + copy-match step. This is the fundamental building block
    for compositional reasoning about `executeSequences.loop`. -/
theorem executeSequences_loop_cons (seq : ZstdSequence) (rest : List ZstdSequence)
    (literals : ByteArray) (output : ByteArray) (history : Array Nat)
    (litPos windowSize : Nat)
    (hlit : litPos + seq.literalLength ≤ literals.size)
    (hoff : (resolveOffset seq.offset history seq.literalLength).1 ≠ 0)
    (hreach : (resolveOffset seq.offset history seq.literalLength).1
      ≤ (copyBytes output literals litPos seq.literalLength).size)
    (hwin : windowSize = 0
      ∨ (resolveOffset seq.offset history seq.literalLength).1 ≤ windowSize) :
    executeSequences.loop (seq :: rest) literals output history litPos windowSize =
      let output' := copyBytes output literals litPos seq.literalLength
      let (offset, history') := resolveOffset seq.offset history seq.literalLength
      let output'' := copyMatch output' offset seq.matchLength
      executeSequences.loop rest literals output'' history'
        (litPos + seq.literalLength) windowSize := by
  rw [executeSequences.loop.eq_2]
  simp only [show ¬(litPos + seq.literalLength > literals.size) from by omega, ↓reduceIte]
  split
  · rename_i h; exact absurd (beq_iff_eq.mp h) hoff
  · split
    · rename_i h; exact absurd hreach (by omega)
    · split
      · rename_i h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        exact absurd h.2 (by cases hwin with | inl hw => omega | inr hw => omega)
      · rfl

/-- After processing one sequence, the intermediate output has grown by exactly
    `seq.literalLength + seq.matchLength` bytes. Composes `copyMatch_size` and
    `copyBytes_size`. -/
theorem executeSequences_loop_cons_output_size (seq : ZstdSequence)
    (literals : ByteArray) (output : ByteArray) (history : Array Nat)
    (litPos : Nat) :
    let output' := copyBytes output literals litPos seq.literalLength
    let (offset, _) := resolveOffset seq.offset history seq.literalLength
    (copyMatch output' offset seq.matchLength).size =
      output.size + seq.literalLength + seq.matchLength := by
  simp only [copyMatch_size, copyBytes_size]

/-- When the sequence execution loop succeeds, every byte that was in the
    output buffer before the loop started is still there at the same index.
    This composes `copyBytes_getElem_lt` and `copyMatch_getElem_lt` through
    the recursive loop structure via induction on the sequence list. -/
theorem executeSequences_loop_getElem_lt
    (seqs : List ZstdSequence) (literals : ByteArray)
    (output : ByteArray) (history : Array Nat) (litPos : Nat) (windowSize : Nat)
    (result : ByteArray × Array Nat × Nat)
    (h : executeSequences.loop seqs literals output history litPos windowSize
         = .ok result)
    (i : Nat) (hi : i < output.size) :
    result.1[i]! = output[i]! := by
  induction seqs generalizing output history litPos with
  | nil =>
    rw [executeSequences.loop.eq_1] at h
    simp only [Except.ok.injEq] at h
    obtain ⟨rfl, _, _⟩ := h; rfl
  | cons seq rest ih =>
    rw [executeSequences.loop.eq_2] at h
    split at h; · exact nomatch h
    split at h; dsimp only [letFun] at h
    split at h; · exact nomatch h
    split at h; · exact nomatch h
    split at h; · exact nomatch h
    have hcb_size := copyBytes_size output literals litPos seq.literalLength
    have hi_cb : i < (copyBytes output literals litPos seq.literalLength).size := by
      rw [hcb_size]; omega
    exact ih _ _ _ h (by rw [copyMatch_size, hcb_size]; omega)
      |>.trans (copyMatch_getElem_lt _ _ _ _ hi_cb)
      |>.trans (copyBytes_getElem_lt _ _ _ _ _ hi)

/-! ## parseSequencesHeader structural properties -/

/-- When `parseSequencesHeader` succeeds, the returned position is strictly greater
    than the input and advances by at most 4 bytes. -/
private theorem parseSequencesHeader_pos_range (data : ByteArray) (pos : Nat)
    (numSeq : Nat) (modes : SequenceCompressionModes) (pos' : Nat)
    (h : parseSequencesHeader data pos = .ok (numSeq, modes, pos')) :
    pos < pos' ∧ pos' ≤ pos + 4 ∧ pos' ≤ data.size := by
  simp only [parseSequencesHeader, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  split at h; · exact nomatch h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨-, -, rfl⟩ := h; omega
  · split at h
    · split at h; · exact nomatch h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨-, -, rfl⟩ := h; omega
    · split at h
      · split at h; · exact nomatch h
        simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨-, -, rfl⟩ := h; omega
      · split at h; · exact nomatch h
        simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨-, -, rfl⟩ := h; omega

/-- When `parseSequencesHeader` succeeds, the returned position is strictly greater
    than the input position. Each branch advances by 1–4 bytes. -/
theorem parseSequencesHeader_pos_gt (data : ByteArray) (pos : Nat)
    (numSeq : Nat) (modes : SequenceCompressionModes) (pos' : Nat)
    (h : parseSequencesHeader data pos = .ok (numSeq, modes, pos')) :
    pos' > pos :=
  (parseSequencesHeader_pos_range data pos numSeq modes pos' h).1

/-- When `parseSequencesHeader` succeeds, the position advances by at most 4 bytes.
    The maximum occurs in the 3-byte count case (byte0 = 255): 3 count bytes +
    1 modes byte. -/
theorem parseSequencesHeader_pos_bounded (data : ByteArray) (pos : Nat)
    (numSeq : Nat) (modes : SequenceCompressionModes) (pos' : Nat)
    (h : parseSequencesHeader data pos = .ok (numSeq, modes, pos')) :
    pos' ≤ pos + 4 :=
  (parseSequencesHeader_pos_range data pos numSeq modes pos' h).2.1

/-- When `parseSequencesHeader` succeeds, the returned position is within
    `data.size`. Each branch checks `data.size < pos + k` before reading `k`
    bytes, so on success `pos + k ≤ data.size` and `pos' = pos + k`. -/
theorem parseSequencesHeader_le_size (data : ByteArray) (pos : Nat)
    (numSeq : Nat) (modes : SequenceCompressionModes) (pos' : Nat)
    (h : parseSequencesHeader data pos = .ok (numSeq, modes, pos')) :
    pos' ≤ data.size :=
  (parseSequencesHeader_pos_range data pos numSeq modes pos' h).2.2

/-- When the input byte at `pos` is zero, `parseSequencesHeader` returns 0 sequences
    with predefined compression modes and advances by exactly 1 byte.
    This is the "no sequences" case (RFC 8878 §3.1.1.3.2): blocks that contain
    only literals have byte0 = 0 and no compression modes byte follows.

    Note: The converse does not hold — `parseSequencesHeader` can also return
    numSeq = 0 from the 2-byte encoding when byte0 = 128 and the next byte is 0,
    but in that case pos' = pos + 3 and modes are parsed from the data. -/
theorem parseSequencesHeader_byte0_zero (data : ByteArray) (pos : Nat)
    (hsize : pos + 1 ≤ data.size) (hbyte : data[pos]!.toNat = 0) :
    parseSequencesHeader data pos =
      .ok (0, { litLenMode := .predefined, offsetMode := .predefined,
                matchLenMode := .predefined }, pos + 1) := by
  simp only [parseSequencesHeader, Bind.bind, Except.bind, Pure.pure, Except.pure]
  simp only [show ¬(data.size < pos + 1) from by omega, ↓reduceIte, hbyte,
    beq_self_eq_true]

/-- When 0 < byte0 < 128, the number of sequences is exactly byte0.
    This is the 1-byte encoding (RFC 8878 §3.1.1.3.2.1) used for up to
    127 sequences, covering the vast majority of real-world Zstd frames. -/
theorem parseSequencesHeader_numSeq_small (data : ByteArray) (pos : Nat)
    (numSeq : Nat) (modes : SequenceCompressionModes) (pos' : Nat)
    (h : parseSequencesHeader data pos = .ok (numSeq, modes, pos'))
    (hbyte0_pos : data[pos]!.toNat > 0)
    (hbyte0_lt : data[pos]!.toNat < 128) :
    numSeq = data[pos]!.toNat := by
  unfold parseSequencesHeader at h
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  -- Size check
  by_cases hsz : data.size < pos + 1
  · simp only [hsz, ↓reduceIte] at h; exact nomatch h
  · simp only [hsz, ↓reduceIte] at h
    -- byte0 == 0 check
    have hbeq : ¬((data[pos]!.toNat == 0) = true) := by
      intro heq; exact absurd (eq_of_beq heq) (by omega)
    rw [if_neg hbeq] at h
    -- byte0 < 128 check
    rw [if_pos hbyte0_lt] at h
    -- Inner size check
    by_cases hsz2 : data.size < pos + 2
    · simp only [hsz2, ↓reduceIte] at h; exact nomatch h
    · simp only [hsz2, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at h
      exact h.1.symm

/-- When 128 ≤ byte0 < 255, the number of sequences uses the 2-byte encoding:
    `numSeq = ((byte0 - 128) << 8) + byte1` (RFC 8878 §3.1.1.3.2.1).
    This covers sequence counts from 128 to 32511. -/
theorem parseSequencesHeader_numSeq_medium (data : ByteArray) (pos : Nat)
    (numSeq : Nat) (modes : SequenceCompressionModes) (pos' : Nat)
    (h : parseSequencesHeader data pos = .ok (numSeq, modes, pos'))
    (hbyte0_ge : data[pos]!.toNat ≥ 128)
    (hbyte0_lt : data[pos]!.toNat < 255) :
    numSeq = ((data[pos]!.toNat - 128) <<< 8) + data[pos + 1]!.toNat := by
  unfold parseSequencesHeader at h
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  -- Size check
  by_cases hsz : data.size < pos + 1
  · simp only [hsz, ↓reduceIte] at h; exact nomatch h
  · simp only [hsz, ↓reduceIte] at h
    -- byte0 == 0 check
    have hbeq : ¬((data[pos]!.toNat == 0) = true) := by
      intro heq; exact absurd (eq_of_beq heq) (by omega)
    rw [if_neg hbeq] at h
    -- byte0 < 128 check
    have hlt128 : ¬(data[pos]!.toNat < 128) := by omega
    rw [if_neg hlt128] at h
    -- byte0 < 255 check
    rw [if_pos hbyte0_lt] at h
    -- Inner size check
    by_cases hsz2 : data.size < pos + 3
    · simp only [hsz2, ↓reduceIte] at h; exact nomatch h
    · simp only [hsz2, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at h
      exact h.1.symm

/-- For the 1-byte encoding (byte0 < 128), numSeq = 0 iff byte0 = 0.
    Completes the characterization of zero vs positive sequence counts
    when byte0 < 128. The 2-byte case (byte0 ≥ 128) can yield numSeq = 0
    with byte0 ≠ 0, so this iff requires the byte0 < 128 restriction. -/
theorem parseSequencesHeader_numSeq_zero_iff (data : ByteArray) (pos : Nat)
    (numSeq : Nat) (modes : SequenceCompressionModes) (pos' : Nat)
    (h : parseSequencesHeader data pos = .ok (numSeq, modes, pos'))
    (hbyte0_lt : data[pos]!.toNat < 128) :
    numSeq = 0 ↔ data[pos]!.toNat = 0 := by
  constructor
  · -- → : numSeq = 0 → byte0 = 0
    intro hzero
    by_cases hne : data[pos]!.toNat = 0
    · exact hne
    · exfalso
      have hpos : data[pos]!.toNat > 0 := by omega
      have := parseSequencesHeader_numSeq_small data pos numSeq modes pos' h hpos hbyte0_lt
      omega
  · -- ← : byte0 = 0 → numSeq = 0
    intro hbyte0
    unfold parseSequencesHeader at h
    simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    by_cases hsz : data.size < pos + 1
    · simp only [hsz, ↓reduceIte] at h; exact nomatch h
    · simp only [hsz, ↓reduceIte] at h
      have hbeq : (data[pos]!.toNat == 0) = true := beq_iff_eq.mpr hbyte0
      rw [if_pos hbeq] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      exact h.1.symm

/-! ## buildRleFseTable structural properties -/

/-- The accuracy log of an RLE FSE table is always 0. -/
theorem buildRleFseTable_accuracyLog (symbol : UInt8) :
    (buildRleFseTable symbol).accuracyLog = 0 := by
  rfl

/-- The RLE FSE table has exactly 1 cell. -/
theorem buildRleFseTable_cells_size (symbol : UInt8) :
    (buildRleFseTable symbol).cells.size = 1 := by
  rfl

/-- The RLE FSE table has a single cell, so any index into it must be 0. -/
private theorem buildRleFseTable_fin_eq_zero (symbol : UInt8)
    (i : Fin (buildRleFseTable symbol).cells.size) :
    i = ⟨0, by show 0 < 1; omega⟩ :=
  Fin.ext (by have : (buildRleFseTable symbol).cells.size = 1 := rfl; omega)

/-- The single cell's symbol in an RLE FSE table is within bounds. -/
theorem buildRleFseTable_symbol_lt (symbol : UInt8) (numSymbols : Nat)
    (hsym : symbol.toNat < numSymbols)
    (i : Fin (buildRleFseTable symbol).cells.size) :
    (buildRleFseTable symbol).cells[i].symbol.toNat < numSymbols := by
  have hi := buildRleFseTable_fin_eq_zero symbol i; subst hi
  show symbol.toUInt16.toNat < numSymbols
  rw [UInt8.toNat_toUInt16]
  exact hsym

/-- The RLE-constructed table satisfies the `ValidFseTable` predicate. -/
theorem buildRleFseTable_valid (symbol : UInt8) (numSymbols : Nat)
    (hsym : symbol.toNat < numSymbols) :
    Zstd.Spec.Fse.ValidFseTable (buildRleFseTable symbol).cells 0 numSymbols := by
  refine ⟨buildRleFseTable_cells_size symbol, buildRleFseTable_symbol_lt symbol numSymbols hsym, ?_⟩
  intro i; have hi := buildRleFseTable_fin_eq_zero symbol i; subst hi
  show (0 : UInt8).toNat ≤ 0; decide

/-! ## resolveSingleFseTable position properties -/

/-- In predefined mode, the position is unchanged. -/
theorem resolveSingleFseTable_predefined_pos (maxSymbols maxAccLog : Nat)
    (data : ByteArray) (pos : Nat)
    (predefinedDist : Array Int32) (predefinedAccLog : Nat)
    (prevTable : Option FseTable)
    (table : FseTable) (pos' : Nat)
    (h : resolveSingleFseTable .predefined maxSymbols maxAccLog data pos
           predefinedDist predefinedAccLog prevTable = .ok (table, pos')) :
    pos' = pos := by
  simp only [resolveSingleFseTable, bind, Except.bind, pure, Except.pure] at h
  split at h
  · simp only [reduceCtorEq] at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    exact h.2.symm

/-- In predefined mode, the returned position is at most `data.size`.
    Since predefined mode doesn't advance the position (`pos' = pos`),
    this follows directly from the input bound. -/
theorem resolveSingleFseTable_predefined_le_size (maxSymbols maxAccLog : Nat)
    (data : ByteArray) (pos : Nat)
    (predefinedDist : Array Int32) (predefinedAccLog : Nat)
    (prevTable : Option FseTable)
    (table : FseTable) (pos' : Nat)
    (h : resolveSingleFseTable .predefined maxSymbols maxAccLog data pos
           predefinedDist predefinedAccLog prevTable = .ok (table, pos'))
    (hpos : pos ≤ data.size) :
    pos' ≤ data.size := by
  have := resolveSingleFseTable_predefined_pos _ _ _ _ _ _ _ _ _ h
  omega

/-- In RLE mode, the position advances by exactly 1. The RLE branch reads one byte
    at `pos` for the symbol and returns `(buildRleFseTable symbol, pos + 1)`. -/
theorem resolveSingleFseTable_rle_pos (maxSymbols maxAccLog : Nat)
    (data : ByteArray) (pos : Nat)
    (predefinedDist : Array Int32) (predefinedAccLog : Nat)
    (prevTable : Option FseTable)
    (table : FseTable) (pos' : Nat)
    (h : resolveSingleFseTable .rle maxSymbols maxAccLog data pos
           predefinedDist predefinedAccLog prevTable = .ok (table, pos')) :
    pos' = pos + 1 := by
  simp only [resolveSingleFseTable, bind, Except.bind, pure, Except.pure] at h
  split at h
  · exact nomatch h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    exact h.2.symm

/-- In RLE mode, the returned position is at most `data.size`.
    Success implies `data.size ≥ pos + 1` (from the guard), and
    `pos' = pos + 1`, so `pos' ≤ data.size`. -/
theorem resolveSingleFseTable_rle_le_size (maxSymbols maxAccLog : Nat)
    (data : ByteArray) (pos : Nat)
    (predefinedDist : Array Int32) (predefinedAccLog : Nat)
    (prevTable : Option FseTable)
    (table : FseTable) (pos' : Nat)
    (h : resolveSingleFseTable .rle maxSymbols maxAccLog data pos
           predefinedDist predefinedAccLog prevTable = .ok (table, pos')) :
    pos' ≤ data.size := by
  have hpos_eq := resolveSingleFseTable_rle_pos _ _ _ _ _ _ _ _ _ h
  -- Extract the guard: success means ¬(data.size < pos + 1)
  simp only [resolveSingleFseTable, bind, Except.bind, pure, Except.pure] at h
  split at h
  · exact nomatch h
  · rename_i hguard
    omega

/-- In repeat mode, the position is unchanged. The repeat branch returns
    `(prevTable.get!, pos)` without consuming any data. -/
theorem resolveSingleFseTable_repeat_pos (maxSymbols maxAccLog : Nat)
    (data : ByteArray) (pos : Nat)
    (predefinedDist : Array Int32) (predefinedAccLog : Nat)
    (prevTable : Option FseTable)
    (table : FseTable) (pos' : Nat)
    (h : resolveSingleFseTable .repeat maxSymbols maxAccLog data pos
           predefinedDist predefinedAccLog prevTable = .ok (table, pos')) :
    pos' = pos := by
  simp only [resolveSingleFseTable, pure, Except.pure] at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    exact h.2.symm
  · exact nomatch h

/-- In repeat mode, the returned position is at most `data.size`.
    Since repeat mode doesn't advance the position (`pos' = pos`),
    this follows directly from the input bound. -/
theorem resolveSingleFseTable_repeat_le_size (maxSymbols maxAccLog : Nat)
    (data : ByteArray) (pos : Nat)
    (predefinedDist : Array Int32) (predefinedAccLog : Nat)
    (prevTable : Option FseTable)
    (table : FseTable) (pos' : Nat)
    (h : resolveSingleFseTable .repeat maxSymbols maxAccLog data pos
           predefinedDist predefinedAccLog prevTable = .ok (table, pos'))
    (hpos : pos ≤ data.size) :
    pos' ≤ data.size := by
  have := resolveSingleFseTable_repeat_pos _ _ _ _ _ _ _ _ _ h
  omega

/-- In fseCompressed mode, the returned position is strictly greater than the input.
    The branch creates a BitReader at `(pos, bitOff=0)`, calls `decodeFseDistribution`
    (which reads ≥4 bits for the accuracy log), then rounds up to the next byte
    boundary. Since ≥4 bits are consumed starting from bit offset 0, the resulting
    byte position must exceed the input. -/
theorem resolveSingleFseTable_fseCompressed_pos_gt (maxSymbols maxAccLog : Nat)
    (data : ByteArray) (pos : Nat)
    (predefinedDist : Array Int32) (predefinedAccLog : Nat)
    (prevTable : Option FseTable)
    (table : FseTable) (pos' : Nat)
    (h : resolveSingleFseTable .fseCompressed maxSymbols maxAccLog data pos
           predefinedDist predefinedAccLog prevTable = .ok (table, pos')) :
    pos' > pos := by
  simp only [resolveSingleFseTable, bind, Except.bind, pure, Except.pure] at h
  -- Extract decodeFseDistribution call
  cases hfse : decodeFseDistribution { data, pos, bitOff := 0 } maxSymbols maxAccLog with
  | error e => rw [hfse] at h; dsimp only [Bind.bind, Except.bind] at h; exact nomatch h
  | ok val =>
    rw [hfse] at h; dsimp only [Bind.bind, Except.bind] at h
    -- Extract buildFseTable call
    cases hbt : buildFseTable val.1 val.2.1 with
    | error e => rw [hbt] at h; dsimp only [Bind.bind, Except.bind] at h; exact nomatch h
    | ok tbl =>
      rw [hbt] at h; dsimp only [Bind.bind, Except.bind] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h
      -- Use decodeFseDistribution_bitPos_ge: bitPos ≥ pos*8 + 4 and bitOff < 8
      have ⟨hge, hbo_lt⟩ := Zstd.Spec.Fse.decodeFseDistribution_bitPos_ge hfse
        (by omega : (0 : Nat) < 8)
      simp only [BitReader.bitPos] at hge
      -- Two cases: bitOff = 0 or bitOff > 0
      by_cases hbo : val.2.2.bitOff == 0
      · -- bitOff = 0: afterPos = br'.pos
        simp only [hbo, ↓reduceIte]
        have : val.2.2.bitOff = 0 := eq_of_beq hbo
        rw [this] at hge; omega
      · -- bitOff > 0: afterPos = br'.pos + 1
        simp only [hbo, Bool.false_eq_true, ↓reduceIte]
        -- bitOff < 8 from decodeFseDistribution_bitPos_ge, so pos ≥ pos
        omega

/-! ## resolveSingleFseTable validity — per-mode ValidFseTable proofs -/

/-- In predefined mode, the returned table satisfies `ValidFseTable` with the predefined
    distribution's accuracy log and symbol count, provided the distribution is non-empty. -/
theorem resolveSingleFseTable_predefined_valid (maxSymbols maxAccLog : Nat)
    (data : ByteArray) (pos : Nat)
    (predefinedDist : Array Int32) (predefinedAccLog : Nat)
    (prevTable : Option FseTable)
    (table : FseTable) (pos' : Nat)
    (h : resolveSingleFseTable .predefined maxSymbols maxAccLog data pos
           predefinedDist predefinedAccLog prevTable = .ok (table, pos'))
    (hpos : 0 < predefinedDist.size) :
    Zstd.Spec.Fse.ValidFseTable table.cells predefinedAccLog predefinedDist.size := by
  simp only [resolveSingleFseTable, bind, Except.bind, pure, Except.pure] at h
  cases hbt : buildFseTable predefinedDist predefinedAccLog with
  | error e => rw [hbt] at h; exact nomatch h
  | ok tbl =>
    rw [hbt] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact Zstd.Spec.Fse.buildFseTable_valid _ _ _ hbt hpos

/-- In RLE mode, the returned table satisfies `ValidFseTable` with accuracy log 0
    and 256 symbols. Since the symbol is a `UInt8`, `symbol.toNat < 256` always holds. -/
theorem resolveSingleFseTable_rle_valid (maxSymbols maxAccLog : Nat)
    (data : ByteArray) (pos : Nat)
    (predefinedDist : Array Int32) (predefinedAccLog : Nat)
    (prevTable : Option FseTable)
    (table : FseTable) (pos' : Nat)
    (h : resolveSingleFseTable .rle maxSymbols maxAccLog data pos
           predefinedDist predefinedAccLog prevTable = .ok (table, pos')) :
    Zstd.Spec.Fse.ValidFseTable table.cells 0 256 := by
  simp only [resolveSingleFseTable, bind, Except.bind, pure, Except.pure] at h
  split at h
  · exact nomatch h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact buildRleFseTable_valid _ 256 (UInt8.toNat_lt _)

/-- In repeat mode, the returned table IS the previous table. If the previous table
    satisfies `ValidFseTable`, so does the returned table. -/
theorem resolveSingleFseTable_repeat_valid (maxSymbols maxAccLog : Nat)
    (data : ByteArray) (pos : Nat)
    (predefinedDist : Array Int32) (predefinedAccLog : Nat)
    (prevTable : Option FseTable)
    (table : FseTable) (pos' : Nat)
    (h : resolveSingleFseTable .repeat maxSymbols maxAccLog data pos
           predefinedDist predefinedAccLog prevTable = .ok (table, pos'))
    (al ns : Nat)
    (hprev : ∀ t, prevTable = some t → Zstd.Spec.Fse.ValidFseTable t.cells al ns) :
    Zstd.Spec.Fse.ValidFseTable table.cells al ns := by
  simp only [resolveSingleFseTable, pure, Except.pure] at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact hprev _ rfl
  · exact nomatch h

/-- In fseCompressed mode, the returned table satisfies `ValidFseTable` for the decoded
    distribution. The existential quantification is needed because `probs` and `accLog`
    are read from the bitstream (not input parameters). -/
theorem resolveSingleFseTable_fseCompressed_valid (maxSymbols maxAccLog : Nat)
    (data : ByteArray) (pos : Nat)
    (predefinedDist : Array Int32) (predefinedAccLog : Nat)
    (prevTable : Option FseTable)
    (table : FseTable) (pos' : Nat)
    (h : resolveSingleFseTable .fseCompressed maxSymbols maxAccLog data pos
           predefinedDist predefinedAccLog prevTable = .ok (table, pos')) :
    ∃ (probs : Array Int32) (accLog : Nat),
      Zstd.Spec.Fse.ValidFseTable table.cells accLog probs.size := by
  simp only [resolveSingleFseTable, bind, Except.bind, pure, Except.pure] at h
  -- Extract decodeFseDistribution call
  cases hfse : decodeFseDistribution { data, pos, bitOff := 0 } maxSymbols maxAccLog with
  | error e => rw [hfse] at h; dsimp only [Bind.bind, Except.bind] at h; exact nomatch h
  | ok val =>
    rw [hfse] at h; dsimp only [Bind.bind, Except.bind] at h
    -- Extract buildFseTable call
    cases hbt : buildFseTable val.1 val.2.1 with
    | error e => rw [hbt] at h; dsimp only [Bind.bind, Except.bind] at h; exact nomatch h
    | ok tbl =>
      rw [hbt] at h; dsimp only [Bind.bind, Except.bind] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      exact ⟨val.1, val.2.1,
        Zstd.Spec.Fse.buildFseTable_valid _ _ _ hbt
          (Zstd.Spec.Fse.decodeFseDistribution_size_pos hfse)⟩

/-! ## resolveSingleFseTable unified validity -/

/-- Across all four compression modes, when `resolveSingleFseTable` succeeds, the returned
    table satisfies `ValidFseTable` for some accuracy log and symbol count. Requires
    non-empty predefined distribution (for predefined mode) and validity of previous table
    (for repeat mode). -/
theorem resolveSingleFseTable_valid_ex (mode : SequenceCompressionMode) (maxSymbols maxAccLog : Nat)
    (data : ByteArray) (pos : Nat) (predefinedDist : Array Int32) (predefinedAccLog : Nat)
    (prevTable : Option FseTable) (table : FseTable) (pos' : Nat)
    (h : resolveSingleFseTable mode maxSymbols maxAccLog data pos
           predefinedDist predefinedAccLog prevTable = .ok (table, pos'))
    (hpos : 0 < predefinedDist.size)
    (hprev : ∀ t, prevTable = some t → ∃ al ns, Zstd.Spec.Fse.ValidFseTable t.cells al ns) :
    ∃ al ns, Zstd.Spec.Fse.ValidFseTable table.cells al ns := by
  cases mode with
  | predefined =>
    exact ⟨predefinedAccLog, predefinedDist.size,
      resolveSingleFseTable_predefined_valid _ _ _ _ _ _ _ _ _ h hpos⟩
  | rle =>
    exact ⟨0, 256, resolveSingleFseTable_rle_valid _ _ _ _ _ _ _ _ _ h⟩
  | «repeat» =>
    -- In repeat mode, table = prevTable.get!
    simp only [resolveSingleFseTable, pure, Except.pure] at h
    cases hpt : prevTable with
    | none => rw [hpt] at h; exact nomatch h
    | some t =>
      rw [hpt] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      exact hprev t hpt
  | fseCompressed =>
    obtain ⟨probs, accLog, hv⟩ := resolveSingleFseTable_fseCompressed_valid _ _ _ _ _ _ _ _ _ h
    exact ⟨accLog, probs.size, hv⟩

/-! ## resolveSingleFseTable unified position monotonicity -/

/-- Across all four compression modes, the returned position is at least the input position.
    This unifies predefined (=), rle (+1), repeat (=), and fseCompressed (>). -/
theorem resolveSingleFseTable_pos_ge (mode : SequenceCompressionMode) (maxSymbols maxAccLog : Nat)
    (data : ByteArray) (pos : Nat) (predefinedDist : Array Int32) (predefinedAccLog : Nat)
    (prevTable : Option FseTable) (table : FseTable) (pos' : Nat)
    (h : resolveSingleFseTable mode maxSymbols maxAccLog data pos
           predefinedDist predefinedAccLog prevTable = .ok (table, pos')) :
    pos' ≥ pos := by
  cases mode with
  | predefined =>
    have := resolveSingleFseTable_predefined_pos _ _ _ _ _ _ _ _ _ h
    omega
  | rle =>
    have := resolveSingleFseTable_rle_pos _ _ _ _ _ _ _ _ _ h
    omega
  | «repeat» =>
    have := resolveSingleFseTable_repeat_pos _ _ _ _ _ _ _ _ _ h
    omega
  | fseCompressed =>
    have := resolveSingleFseTable_fseCompressed_pos_gt _ _ _ _ _ _ _ _ _ h
    omega

/-! ## resolveSequenceFseTables position composition -/

/-- The 3-table resolver doesn't decrease position. Composes three
    `resolveSingleFseTable_pos_ge` applications via transitivity. -/
theorem resolveSequenceFseTables_pos_ge (modes : SequenceCompressionModes)
    (data : ByteArray) (pos : Nat) (prev : PrevFseTables)
    (llTable ofTable mlTable : FseTable) (pos' : Nat)
    (h : resolveSequenceFseTables modes data pos prev = .ok (llTable, ofTable, mlTable, pos')) :
    pos' ≥ pos := by
  simp only [resolveSequenceFseTables, bind, Except.bind, pure, Except.pure] at h
  cases hll : resolveSingleFseTable modes.litLenMode 36 9 data pos
      predefinedLitLenDistribution 6 prev.litLen with
  | error e => rw [hll] at h; exact nomatch h
  | ok val₁ =>
    rw [hll] at h; dsimp only [Bind.bind, Except.bind] at h
    cases hof : resolveSingleFseTable modes.offsetMode 32 8 data val₁.2
        predefinedOffsetDistribution 5 prev.offset with
    | error e => rw [hof] at h; exact nomatch h
    | ok val₂ =>
      rw [hof] at h; dsimp only [Bind.bind, Except.bind] at h
      cases hml : resolveSingleFseTable modes.matchLenMode 53 9 data val₂.2
          predefinedMatchLenDistribution 6 prev.matchLen with
      | error e => rw [hml] at h; exact nomatch h
      | ok val₃ =>
        rw [hml] at h; dsimp only [Bind.bind, Except.bind] at h
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, -, -, rfl⟩ := h
        have h₁ := resolveSingleFseTable_pos_ge _ _ _ _ _ _ _ _ _ _ hll
        have h₂ := resolveSingleFseTable_pos_ge _ _ _ _ _ _ _ _ _ _ hof
        have h₃ := resolveSingleFseTable_pos_ge _ _ _ _ _ _ _ _ _ _ hml
        omega

/-! ## resolveSequenceFseTables validity composition -/

/-- When `resolveSequenceFseTables` succeeds, all three returned FSE tables satisfy
    `ValidFseTable` for some accuracy log and symbol count. Requires that any previous
    tables (for repeat mode) are also valid. Composes three applications of
    `resolveSingleFseTable_valid_ex` — one for each of litLen, offset, matchLen. -/
theorem resolveSequenceFseTables_valid (modes : SequenceCompressionModes)
    (data : ByteArray) (pos : Nat) (prev : PrevFseTables)
    (llTable ofTable mlTable : FseTable) (pos' : Nat)
    (h : resolveSequenceFseTables modes data pos prev = .ok (llTable, ofTable, mlTable, pos'))
    (hprevLL : ∀ t, prev.litLen = some t → ∃ al ns, Zstd.Spec.Fse.ValidFseTable t.cells al ns)
    (hprevOF : ∀ t, prev.offset = some t → ∃ al ns, Zstd.Spec.Fse.ValidFseTable t.cells al ns)
    (hprevML : ∀ t, prev.matchLen = some t → ∃ al ns, Zstd.Spec.Fse.ValidFseTable t.cells al ns) :
    (∃ al ns, Zstd.Spec.Fse.ValidFseTable llTable.cells al ns) ∧
    (∃ al ns, Zstd.Spec.Fse.ValidFseTable ofTable.cells al ns) ∧
    (∃ al ns, Zstd.Spec.Fse.ValidFseTable mlTable.cells al ns) := by
  simp only [resolveSequenceFseTables, bind, Except.bind, pure, Except.pure] at h
  cases hll : resolveSingleFseTable modes.litLenMode 36 9 data pos
      predefinedLitLenDistribution 6 prev.litLen with
  | error e => rw [hll] at h; exact nomatch h
  | ok val₁ =>
    rw [hll] at h; dsimp only [Bind.bind, Except.bind] at h
    cases hof : resolveSingleFseTable modes.offsetMode 32 8 data val₁.2
        predefinedOffsetDistribution 5 prev.offset with
    | error e => rw [hof] at h; exact nomatch h
    | ok val₂ =>
      rw [hof] at h; dsimp only [Bind.bind, Except.bind] at h
      cases hml : resolveSingleFseTable modes.matchLenMode 53 9 data val₂.2
          predefinedMatchLenDistribution 6 prev.matchLen with
      | error e => rw [hml] at h; exact nomatch h
      | ok val₃ =>
        rw [hml] at h; dsimp only [Bind.bind, Except.bind] at h
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, _⟩ := h
        exact ⟨resolveSingleFseTable_valid_ex _ _ _ _ _ _ _ _ _ _ hll (by decide) hprevLL,
               resolveSingleFseTable_valid_ex _ _ _ _ _ _ _ _ _ _ hof (by decide) hprevOF,
               resolveSingleFseTable_valid_ex _ _ _ _ _ _ _ _ _ _ hml (by decide) hprevML⟩

/-! ## resolveSequenceFseTables completeness -/

/-- When each of the three `resolveSingleFseTable` calls succeeds, the composed
    `resolveSequenceFseTables` succeeds and returns the exact output. The three
    hypotheses capture position-threading: `pos → pos1 → pos2 → pos3`. -/
theorem resolveSequenceFseTables_succeeds
    (modes : SequenceCompressionModes) (data : ByteArray) (pos : Nat)
    (prev : PrevFseTables)
    (litLenTable : FseTable) (pos1 : Nat)
    (offsetTable : FseTable) (pos2 : Nat)
    (matchLenTable : FseTable) (pos3 : Nat)
    (hlit : resolveSingleFseTable modes.litLenMode 36 9 data pos
            predefinedLitLenDistribution 6 prev.litLen = .ok (litLenTable, pos1))
    (hoff : resolveSingleFseTable modes.offsetMode 32 8 data pos1
            predefinedOffsetDistribution 5 prev.offset = .ok (offsetTable, pos2))
    (hml : resolveSingleFseTable modes.matchLenMode 53 9 data pos2
           predefinedMatchLenDistribution 6 prev.matchLen = .ok (matchLenTable, pos3)) :
    resolveSequenceFseTables modes data pos prev =
      .ok (litLenTable, offsetTable, matchLenTable, pos3) := by
  simp only [resolveSequenceFseTables, bind, Except.bind, pure, Except.pure, hlit, hoff, hml]

/-! ## resolveSingleFseTable completeness -/

/-- In predefined mode, `resolveSingleFseTable` always succeeds (unconditionally).
    The only fallible operation is `buildFseTable`, which always succeeds by `buildFseTable_ok`. -/
theorem resolveSingleFseTable_succeeds_predefined (maxSymbols maxAccLog : Nat)
    (data : ByteArray) (pos : Nat)
    (predefinedDist : Array Int32) (predefinedAccLog : Nat)
    (prevTable : Option FseTable) :
    ∃ table,
      resolveSingleFseTable .predefined maxSymbols maxAccLog data pos
        predefinedDist predefinedAccLog prevTable = .ok (table, pos) := by
  simp only [resolveSingleFseTable, bind, Except.bind, pure, Except.pure]
  obtain ⟨t, ht⟩ := Zstd.Spec.Fse.buildFseTable_ok predefinedDist predefinedAccLog
  rw [ht]
  exact ⟨t, rfl⟩

/-- In RLE mode, `resolveSingleFseTable` succeeds when there is at least 1 byte at `pos`. -/
theorem resolveSingleFseTable_succeeds_rle (maxSymbols maxAccLog : Nat)
    (data : ByteArray) (pos : Nat)
    (predefinedDist : Array Int32) (predefinedAccLog : Nat)
    (prevTable : Option FseTable)
    (hsize : data.size ≥ pos + 1) :
    ∃ table,
      resolveSingleFseTable .rle maxSymbols maxAccLog data pos
        predefinedDist predefinedAccLog prevTable = .ok (table, pos + 1) := by
  simp only [resolveSingleFseTable, bind, Except.bind, pure, Except.pure]
  have : ¬(data.size < pos + 1) := by omega
  simp only [this, ↓reduceIte]
  exact ⟨_, rfl⟩

/-- In repeat mode, `resolveSingleFseTable` succeeds when a previous table is available. -/
theorem resolveSingleFseTable_succeeds_repeat (maxSymbols maxAccLog : Nat)
    (data : ByteArray) (pos : Nat)
    (predefinedDist : Array Int32) (predefinedAccLog : Nat)
    (table : FseTable) :
    resolveSingleFseTable .repeat maxSymbols maxAccLog data pos
      predefinedDist predefinedAccLog (some table) = .ok (table, pos) := by
  simp only [resolveSingleFseTable, pure, Except.pure]

/-- In FSE-compressed mode, `resolveSingleFseTable` succeeds when
    `decodeFseDistribution` and `buildFseTable` both succeed. -/
theorem resolveSingleFseTable_succeeds_fse (maxSymbols maxAccLog : Nat)
    (data : ByteArray) (pos : Nat)
    (predefinedDist : Array Int32) (predefinedAccLog : Nat)
    (prevTable : Option FseTable)
    (probs : Array Int32) (accLog : Nat) (br' : BitReader)
    (hfse : decodeFseDistribution ⟨data, pos, 0⟩ maxSymbols maxAccLog
            = .ok (probs, accLog, br'))
    (table : FseTable)
    (hbuild : buildFseTable probs accLog = .ok table) :
    resolveSingleFseTable .fseCompressed maxSymbols maxAccLog data pos
      predefinedDist predefinedAccLog prevTable =
      .ok (table, if br'.bitOff == 0 then br'.pos else br'.pos + 1) := by
  simp only [resolveSingleFseTable, bind, Except.bind, hfse, hbuild, pure, Except.pure]

/-! ## decodeSequencesWF completeness -/

/-- When `numSeq = 0`, `decodeSequencesWF` returns an empty array and
    the unchanged backward bit reader. -/
theorem decodeSequencesWF_succeeds_zero
    (litLenTable offsetTable matchLenTable : FseTable)
    (br : BackwardBitReader) :
    decodeSequencesWF litLenTable offsetTable matchLenTable br 0 =
      .ok (#[], br) := by
  simp only [decodeSequencesWF, beq_self_eq_true, ↓reduceIte]

/-! ## decodeSequencesWF output size -/

/-- When the inner loop succeeds, the output array has exactly
    `acc.size + remaining` elements. -/
theorem decodeSequencesWF_loop_size
    {litLenTable offsetTable matchLenTable : FseTable}
    {br br' : BackwardBitReader}
    {litLenState offsetState matchLenState remaining total : Nat}
    {acc result : Array ZstdSequence}
    (h : decodeSequencesWF.loop litLenTable offsetTable matchLenTable br
           litLenState offsetState matchLenState remaining total acc
           = .ok (result, br')) :
    result.size = acc.size + remaining := by
  induction remaining generalizing br litLenState offsetState matchLenState acc with
  | zero =>
    simp only [decodeSequencesWF.loop, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h; omega
  | succ n ih =>
    simp only [decodeSequencesWF.loop] at h
    split at h; · exact nomatch h  -- bounds check 1
    split at h; · exact nomatch h  -- bounds check 2
    split at h; · exact nomatch h  -- bounds check 3
    split at h; · exact nomatch h  -- decodeOneSequence
    simp only [beq_iff_eq] at h
    split at h
    · -- Last sequence
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      simp only [Array.size_push]; omega
    · -- Not last: 3 readBits for state update + recursion
      split at h; · exact nomatch h
      split at h; · exact nomatch h
      split at h; · exact nomatch h
      rw [ih h]; simp only [Array.size_push]; omega

/-- When `decodeSequencesWF` succeeds with `numSeq > 0`, the result has
    exactly `numSeq` elements. -/
theorem decodeSequencesWF_size
    {litLenTable offsetTable matchLenTable : FseTable}
    {br br' : BackwardBitReader}
    {numSeq : Nat} {result : Array ZstdSequence}
    (h : decodeSequencesWF litLenTable offsetTable matchLenTable br numSeq
           = .ok (result, br'))
    (hcount : 0 < numSeq) :
    result.size = numSeq := by
  simp only [decodeSequencesWF] at h
  split at h
  · rename_i h0; simp only [beq_iff_eq] at h0; omega
  · split at h; · exact nomatch h
    split at h; · exact nomatch h
    split at h; · exact nomatch h
    have := decodeSequencesWF_loop_size h
    simp only [Array.size_empty] at this; omega

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
  -- Every branch returns either a literal #[_, _, _] (size = 3 by rfl)
  -- or the unchanged history (size = 3 by h).
  split <;> (try rfl)
  split <;> (split <;> first | rfl | exact h)

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

/-- Any 3-element array of positive naturals is a `ValidOffsetHistory`. -/
private theorem validOffsetHistory_mk3 (a b c : Nat) (ha : a > 0) (hb : b > 0) (hc : c > 0) :
    ValidOffsetHistory #[a, b, c] := by
  refine ⟨rfl, ?_, ?_, ?_⟩ <;> simp only [List.size_toArray, List.length_cons, List.length_nil,
    Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, getElem!_pos,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
    gt_iff_lt] <;> omega

/-- When `rawOffset > 3` and input has `ValidOffsetHistory`, the output history
    also satisfies `ValidOffsetHistory`. The new history is
    `#[rawOffset - 3, history[0]!, history[1]!]`, all positive. -/
theorem resolveOffset_history_valid_large (rawOffset litLen : Nat)
    (history : Array Nat) (hh : ValidOffsetHistory history)
    (hr : rawOffset > 3) :
    ValidOffsetHistory (resolveOffset rawOffset history litLen).2 := by
  obtain ⟨_, h0pos, h1pos, _⟩ := hh
  simp only [resolveOffset, hr, ↓reduceIte]
  exact validOffsetHistory_mk3 _ _ _ (by omega) h0pos h1pos

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
    · exact validOffsetHistory_mk3 _ _ _ h1pos h0pos h2pos
  · -- rawOffset = 2
    unfold resolveOffset
    simp only [show ¬(2 > 3) from by omega, ↓reduceIte]
    split
    · exact validOffsetHistory_mk3 _ _ _ h1pos h0pos h2pos
    · exact validOffsetHistory_mk3 _ _ _ h2pos h0pos h1pos
  · -- rawOffset = 3
    unfold resolveOffset
    simp only [show ¬(3 > 3) from by omega, ↓reduceIte]
    split
    · exact validOffsetHistory_mk3 _ _ _ h2pos h0pos h1pos
    · have h02 := hshift ⟨by omega, rfl⟩
      exact validOffsetHistory_mk3 _ _ _ (by omega) h1pos h2pos
  · omega  -- rawOffset ≥ 4

/-- When `resolveOffset` returns a nonzero offset and the input history is valid,
    the output history is also valid. Unifies `resolveOffset_history_valid_large`
    and `resolveOffset_history_valid_repeat` into a single lemma whose precondition
    matches the `executeSequences.loop` guard (`if offset == 0 then .error ...`). -/
theorem resolveOffset_history_valid_of_fst_ne_zero
    (rawOffset litLen : Nat) (history : Array Nat)
    (hh : ValidOffsetHistory history)
    (hne : (resolveOffset rawOffset history litLen).1 ≠ 0) :
    ValidOffsetHistory (resolveOffset rawOffset history litLen).2 := by
  by_cases hr : rawOffset > 3
  · exact resolveOffset_history_valid_large rawOffset litLen history hh hr
  · -- rawOffset ≤ 3
    by_cases hr0 : rawOffset = 0
    · -- rawOffset = 0: resolveOffset returns (1, history), history unchanged
      subst hr0
      simp only [resolveOffset, show ¬(0 > 3) from by omega, ↓reduceIte]
      split <;> (simp only [Nat.not_lt] at * <;> exact hh)
    · -- rawOffset ∈ {1, 2, 3}
      apply resolveOffset_history_valid_repeat rawOffset litLen history hh (by omega) (by omega)
      intro ⟨hlit0, hraw3⟩
      -- litLen = 0 ∧ rawOffset = 3: resolveOffset returns history[0]! - 1
      subst hraw3; subst hlit0
      have := (resolveOffset_shifted3_val history hh.1).1
      -- hne : (resolveOffset 3 history 0).1 ≠ 0, and .1 = history[0]! - 1
      rw [this] at hne
      omega

/-- When `executeSequences.loop` succeeds and the input offset history is valid,
    the output offset history is also valid. Threads `ValidOffsetHistory` through the
    sequence loop by applying `resolveOffset_history_valid_of_fst_ne_zero` at each
    step (the loop's `if offset == 0 then .error` guard ensures the precondition). -/
theorem executeSequences_loop_history_valid
    (seqs : List ZstdSequence) (literals : ByteArray)
    (output : ByteArray) (history : Array Nat) (litPos windowSize : Nat)
    (output' : ByteArray) (history' : Array Nat) (litPos' : Nat)
    (hvalid : ValidOffsetHistory history)
    (h : executeSequences.loop seqs literals output history litPos windowSize
         = .ok (output', history', litPos')) :
    ValidOffsetHistory history' := by
  induction seqs generalizing output history litPos with
  | nil =>
    rw [Zip.Native.executeSequences.loop.eq_1] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl, _⟩ := h
    exact hvalid
  | cons seq rest ih =>
    rw [Zip.Native.executeSequences.loop.eq_2] at h
    split at h; · exact nomatch h
    dsimp only [letFun] at h
    split at h; · exact nomatch h
    split at h; · exact nomatch h
    split at h; · exact nomatch h
    exact ih _ _ _ (resolveOffset_history_valid_of_fst_ne_zero _ _ _ hvalid (by
        simp only [ne_eq, beq_iff_eq] at *; assumption)) h

/-- The loop preserves the history array size. Uses the weaker hypothesis
    `history.size = 3` rather than full `ValidOffsetHistory`. -/
theorem executeSequences_loop_history_size
    (seqs : List ZstdSequence) (literals : ByteArray)
    (output : ByteArray) (history : Array Nat) (litPos windowSize : Nat)
    (output' : ByteArray) (history' : Array Nat) (litPos' : Nat)
    (hsize : history.size = 3)
    (h : executeSequences.loop seqs literals output history litPos windowSize
         = .ok (output', history', litPos')) :
    history'.size = 3 := by
  induction seqs generalizing output history litPos with
  | nil =>
    rw [Zip.Native.executeSequences.loop.eq_1] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl, _⟩ := h
    exact hsize
  | cons seq rest ih =>
    rw [Zip.Native.executeSequences.loop.eq_2] at h
    split at h; · exact nomatch h
    dsimp only [letFun] at h
    split at h; · exact nomatch h
    split at h; · exact nomatch h
    split at h; · exact nomatch h
    exact ih _ _ _ (resolveOffset_history_size _ _ _ hsize) h

/-- For shifted repeat codes 1–2 (rawOffset ∈ {1,2}, literalLength = 0),
    `ValidOffsetHistory` implies the resolved offset is positive. Shifted code 1
    returns `history[1]!` and shifted code 2 returns `history[2]!`, both positive
    by `ValidOffsetHistory`. The shifted code 3 case (`history[0]! - 1`) is excluded
    because it can be 0 when `history[0]! = 1`. -/
theorem resolveOffset_positive_shifted12 (rawOffset : Nat) (history : Array Nat)
    (hraw : rawOffset > 0) (hraw' : rawOffset ≤ 2)
    (hvalid : ValidOffsetHistory history) :
    (resolveOffset rawOffset history 0).1 > 0 := by
  obtain ⟨_, _, h1pos, h2pos⟩ := hvalid
  rcases rawOffset with _ | _ | _ | n
  · omega  -- rawOffset = 0
  · -- rawOffset = 1: shifted → history[1]!
    simp only [resolveOffset, show ¬(1 > 3) from by omega, show ¬(0 > 0) from by omega,
      ↓reduceIte]
    exact h1pos
  · -- rawOffset = 2: shifted → history[2]!
    simp only [resolveOffset, show ¬(2 > 3) from by omega, show ¬(0 > 0) from by omega,
      ↓reduceIte]
    exact h2pos
  · omega  -- rawOffset ≥ 3

/-- Unified positivity theorem for `resolveOffset`: covers all cases where the
    resolved offset is guaranteed positive. This subsumes `resolveOffset_positive_large`
    (rawOffset > 3), `resolveOffset_positive_litLen_pos` (litLen > 0), and
    `resolveOffset_positive_shifted12` (shifted codes 1–2).

    The only case requiring an extra hypothesis is rawOffset = 3 with litLen = 0
    (shifted mode returns `history[0]! - 1`), captured by `hshift3`. For all other
    inputs with `rawOffset > 0` and `ValidOffsetHistory`, positivity holds unconditionally.

    This is the single theorem downstream proofs (e.g. `executeSequences` loop
    invariants) should use, avoiding case splits on litLen and rawOffset at each
    loop iteration. -/
theorem resolveOffset_positive_all (rawOffset : Nat) (history : Array Nat) (litLen : Nat)
    (hraw : rawOffset > 0) (hvalid : ValidOffsetHistory history)
    (hshift3 : litLen = 0 ∧ rawOffset = 3 → history[0]! ≥ 2) :
    (resolveOffset rawOffset history litLen).1 > 0 := by
  by_cases hlit : litLen > 0
  · exact resolveOffset_positive_litLen_pos rawOffset history litLen hraw hvalid hlit
  · -- litLen = 0
    have hlit0 : litLen = 0 := by omega
    subst hlit0
    by_cases hle : rawOffset ≤ 2
    · exact resolveOffset_positive_shifted12 rawOffset history hraw hle hvalid
    · by_cases heq3 : rawOffset = 3
      · -- rawOffset = 3, litLen = 0: resolved offset = history[0]! - 1
        have h02 := hshift3 ⟨rfl, heq3⟩
        rw [heq3]
        have := (resolveOffset_shifted3_val history hvalid.1).1
        rw [this]
        omega
      · -- rawOffset > 3
        have : rawOffset > 3 := by omega
        exact resolveOffset_positive_large rawOffset history 0 this

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

/-- Any successful match length decoding produces a value ≥ 3.
    This is the Zstd minimum match length (RFC 8878 §3.1.1.3.2.1.2):
    every entry in `matchLenExtraBits` has baseline ≥ 3, and the decoded
    value is `baseline + extraBits.toNat`. -/
private theorem matchLen_baselines_ge_three_aux :
    ∀ i : Fin matchLenExtraBits.size, (matchLenExtraBits[i.val]'i.isLt).1 ≥ 3 := by
  decide_cbv

private theorem matchLen_baselines_ge_three (i : Nat) (hi : i < matchLenExtraBits.size) :
    (matchLenExtraBits[i]'hi).1 ≥ 3 :=
  matchLen_baselines_ge_three_aux ⟨i, hi⟩

theorem decodeMatchLenValue_ge_three (code : Nat) (extraBits : UInt32) (n : Nat)
    (h : decodeMatchLenValue code extraBits = .ok n) :
    n ≥ 3 := by
  unfold decodeMatchLenValue at h
  split at h
  · rename_i hlt
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact Nat.le_trans (matchLen_baselines_ge_three code hlt) (Nat.le_add_right _ _)
  · exact nomatch h

/-- `decodeOffsetValue` always returns a positive value.
    This follows from `(1 <<< code) ≥ 1` for any natural `code`. -/
theorem decodeOffsetValue_positive (code : Nat) (extraBits : UInt32) :
    decodeOffsetValue code extraBits > 0 := by
  unfold decodeOffsetValue
  have : 1 <<< code ≥ 1 := by rw [Nat.one_shiftLeft]; exact Nat.one_le_two_pow
  omega

/-- When `code ≥ 1`, `decodeOffsetValue` returns a value ≥ 2.
    This distinguishes non-repeat offsets (≥ 2) from repeat offsets (code 0).
    Follows from `1 <<< code = 2^code ≥ 2` when `code ≥ 1`. -/
theorem decodeOffsetValue_ge_two (code : Nat) (extraBits : UInt32) (hcode : code ≥ 1) :
    decodeOffsetValue code extraBits ≥ 2 := by
  unfold decodeOffsetValue
  have : 1 <<< code ≥ 2 := by
    rw [Nat.one_shiftLeft]
    cases code with
    | zero => omega
    | succ n => rw [Nat.pow_succ]; have := Nat.one_le_two_pow (n := n); omega
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
  · exact nomatch h
  · rename_i v heq
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨hout, _⟩ := h
    have ⟨hsize, _, hbound, _⟩ := executeSequences_loop_inv _ _ _ _ _ _ _ _ _ (Nat.zero_le _) heq
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

/-- When `executeSequences` succeeds and the input offset history is valid,
    the output offset history is also valid. Lifts `executeSequences_loop_history_valid`
    through the monadic wrapper. -/
theorem executeSequences_history_valid
    (sequences : Array ZstdSequence) (literals : ByteArray)
    (windowPrefix : ByteArray) (offsetHistory : Array Nat) (windowSize : Nat)
    (blockOutput : ByteArray) (history' : Array Nat)
    (hvalid : ValidOffsetHistory offsetHistory)
    (h : executeSequences sequences literals windowPrefix offsetHistory windowSize
         = .ok (blockOutput, history')) :
    ValidOffsetHistory history' := by
  unfold executeSequences at h
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h
  split at h
  · exact nomatch h
  · rename_i v heq
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    exact executeSequences_loop_history_valid _ _ _ _ _ _ _ _ _ hvalid heq

/-- The output history from `executeSequences` has exactly 3 entries when the
    input history does. Uses the weaker hypothesis `offsetHistory.size = 3`
    rather than full `ValidOffsetHistory`. -/
theorem executeSequences_history_size
    (sequences : Array ZstdSequence) (literals : ByteArray)
    (windowPrefix : ByteArray) (offsetHistory : Array Nat) (windowSize : Nat)
    (blockOutput : ByteArray) (history' : Array Nat)
    (hinit : offsetHistory.size = 3)
    (h : executeSequences sequences literals windowPrefix offsetHistory windowSize
         = .ok (blockOutput, history')) :
    history'.size = 3 := by
  unfold executeSequences at h
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h
  split at h
  · exact nomatch h
  · rename_i v heq
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    exact executeSequences_loop_history_size _ _ _ _ _ _ _ _ _ hinit heq

end Zstd.Spec.Sequence
