import Zip.Spec.DeflateEncode
import Zip.Spec.BitstreamWriteCorrect

/-!
# DEFLATE Dynamic Block Header Encoding (RFC 1951 §3.2.7)

RLE encoding of code lengths and dynamic Huffman tree header assembly:
- `CLEntry`, `countRun`, `rlEncodeLengths`: RLE encoding of code lengths
- `rlDecodeLengths`: RLE decoding (inverse)
- `rlDecodeLengths_rlEncodeLengths`: RLE roundtrip proof
- `rlEncodeLengths_valid`: entry constraint validation
- `encodeDynamicTrees`: full dynamic tree header encoder
- `encodeDynamicTrees_decodeDynamicTables`: header roundtrip theorem
-/

namespace Deflate.Spec

/-! ## RLE encoding of DEFLATE code lengths (RFC 1951 §3.2.7) -/

/-- A code-length entry for DEFLATE dynamic blocks (RFC 1951 §3.2.7).
    Each entry is `(clCode, extraValue)` where:
    - clCode 0–15: literal code length, extraValue = 0
    - clCode 16: repeat previous, extraValue = count − 3 (0–3, 2 bits)
    - clCode 17: repeat zero, extraValue = count − 3 (0–7, 3 bits)
    - clCode 18: repeat zero long, extraValue = count − 11 (0–127, 7 bits) -/
abbrev CLEntry := Nat × Nat

/-- Count consecutive occurrences of `val` at the front of `xs`. -/
def countRun (val : Nat) : List Nat → Nat
  | x :: xs => if x == val then 1 + countRun val xs else 0
  | [] => 0

theorem countRun_le_length (val : Nat) (xs : List Nat) :
    countRun val xs ≤ xs.length := by
  induction xs with
  | nil => simp [countRun]
  | cons x xs ih =>
    simp only [countRun]
    split <;> simp <;> omega

/-- RLE-encode a list of code lengths into CL entries.
    Greedy strategy: use the longest possible run at each position.
    For runs of zeros: use codes 17 or 18.
    For runs of the same non-zero value: emit literal then code 16. -/
def rlEncodeLengths (lengths : List Nat) : List CLEntry :=
  go lengths
where
  go : List Nat → List CLEntry
    | [] => []
    | x :: xs =>
      if x == 0 then
        let runLen := 1 + countRun 0 xs
        if runLen >= 11 then
          let take := min runLen 138
          (18, take - 11) :: go (xs.drop (take - 1))
        else if runLen >= 3 then
          (17, runLen - 3) :: go (xs.drop (runLen - 1))
        else
          -- 1 or 2 zeros: emit as literals
          (0, 0) :: go xs
      else
        let runLen := countRun x xs
        if runLen >= 3 then
          let take := min runLen 6
          (x, 0) :: (16, take - 3) :: go (xs.drop take)
        else
          (x, 0) :: go xs
  termination_by xs => xs.length
  decreasing_by
    all_goals simp_all [List.length_drop]
    all_goals have := countRun_le_length 0 xs; omega

/-- Decode a list of CL entries back into code lengths.
    This is the pure (non-Huffman) inverse of `rlEncodeLengths`.
    Code 16 requires a previous value, so we use an accumulator. -/
def rlDecodeLengths (entries : List CLEntry) : Option (List Nat) :=
  go entries []
where
  go : List CLEntry → List Nat → Option (List Nat)
    | [], acc => some acc
    | (code, extra) :: rest, acc =>
      if code ≤ 15 then
        go rest (acc ++ [code])
      else if code == 16 then do
        guard (acc.length > 0)
        let prev := acc.getLast!
        go rest (acc ++ List.replicate (extra + 3) prev)
      else if code == 17 then
        go rest (acc ++ List.replicate (extra + 3) 0)
      else if code == 18 then
        go rest (acc ++ List.replicate (extra + 11) 0)
      else none

theorem countRun_take (val : Nat) (xs : List Nat) :
    xs.take (countRun val xs) = List.replicate (countRun val xs) val := by
  induction xs with
  | nil => simp [countRun]
  | cons x xs ih =>
    simp only [countRun]
    split
    · rename_i heq; simp only [beq_iff_eq] at heq; subst heq
      show (x :: xs).take (1 + countRun x xs) = List.replicate (1 + countRun x xs) x
      rw [show 1 + countRun x xs = (countRun x xs) + 1 from by omega]
      rw [List.take_succ_cons, List.replicate_succ]
      exact congrArg (x :: ·) ih
    · show (x :: xs).take 0 = List.replicate 0 val
      simp

/-- Taking at most `countRun val xs` elements from `xs` gives all `val`s. -/
theorem take_countRun_eq_replicate (val : Nat) (xs : List Nat) (n : Nat) (hn : n ≤ countRun val xs) :
    xs.take n = List.replicate n val := by
  induction xs generalizing n with
  | nil => simp [countRun] at hn; simp [hn]
  | cons x xs ih =>
    simp only [countRun] at hn
    split at hn
    · rename_i heq; simp only [beq_iff_eq] at heq; subst heq
      cases n with
      | zero => simp
      | succ n =>
        simp only [List.take_succ_cons, List.replicate_succ]
        exact congrArg (x :: ·) (ih n (by omega))
    · have : n = 0 := by omega
      subst this; simp

private theorem drop_subset_valid {xs : List Nat} {n : Nat}
    (hvalid : ∀ y ∈ xs, y ≤ 15) : ∀ y ∈ xs.drop n, y ≤ 15 :=
  fun y hy => hvalid y (List.drop_subset n xs hy)

-- Step lemmas for rlDecodeLengths.go on each code type
private theorem rlDecode_go_literal (code : Nat) (extra : Nat)
    (rest : List CLEntry) (acc : List Nat) (hle : code ≤ 15) :
    rlDecodeLengths.go ((code, extra) :: rest) acc =
      rlDecodeLengths.go rest (acc ++ [code]) := by
  simp only [rlDecodeLengths.go, hle, ↓reduceIte]

private theorem rlDecode_go_code17 (extra : Nat)
    (rest : List CLEntry) (acc : List Nat) :
    rlDecodeLengths.go ((17, extra) :: rest) acc =
      rlDecodeLengths.go rest (acc ++ List.replicate (extra + 3) 0) := by
  simp [rlDecodeLengths.go]

private theorem rlDecode_go_code18 (extra : Nat)
    (rest : List CLEntry) (acc : List Nat) :
    rlDecodeLengths.go ((18, extra) :: rest) acc =
      rlDecodeLengths.go rest (acc ++ List.replicate (extra + 11) 0) := by
  simp [rlDecodeLengths.go]

private theorem rlDecode_go_code16 (extra : Nat)
    (rest : List CLEntry) (acc : List Nat) (hne : acc.length > 0) :
    rlDecodeLengths.go ((16, extra) :: rest) acc =
      rlDecodeLengths.go rest (acc ++ List.replicate (extra + 3) acc.getLast!) := by
  simp [rlDecodeLengths.go, hne, guard, pure, bind]

/-- Replicate zeros plus the rest of the list equals the original cons-zero list. -/
private theorem replicate_drop_eq_cons_zero (xs : List Nat) (n : Nat)
    (hn1 : n ≥ 1) (hn : n ≤ 1 + countRun 0 xs) :
    List.replicate n 0 ++ xs.drop (n - 1) = 0 :: xs := by
  rw [← take_countRun_eq_replicate 0 (0 :: xs) n (by simp [countRun]; omega)]
  have hdrop : xs.drop (n - 1) = (0 :: xs).drop n := by
    cases n with
    | zero => omega
    | succ k => simp [List.drop_succ_cons]
  rw [hdrop, List.take_append_drop]

/-- Singleton plus replicate plus drop equals the original cons list. -/
private theorem singleton_replicate_drop_eq_cons (x : Nat) (xs : List Nat) (m : Nat)
    (hm : m ≤ countRun x xs) :
    [x] ++ List.replicate m x ++ xs.drop m = x :: xs := by
  rw [← take_countRun_eq_replicate x xs m hm]
  simp [List.take_append_drop]

/-- Generalized roundtrip: decoding an encoded list recovers the accumulator plus the list. -/
theorem rlDecodeLengths_go_rlEncodeLengths_go (lengths : List Nat) (acc : List Nat)
    (hvalid : ∀ x ∈ lengths, x ≤ 15) :
    rlDecodeLengths.go (rlEncodeLengths.go lengths) acc = some (acc ++ lengths) := by
  match lengths with
  | [] => simp [rlEncodeLengths.go, rlDecodeLengths.go]
  | x :: xs =>
    have hx_valid : x ≤ 15 := hvalid x (.head ..)
    have hxs_valid : ∀ y ∈ xs, y ≤ 15 := fun y hy => hvalid y (List.mem_cons_of_mem x hy)
    have hcr0 := countRun_le_length 0 xs
    have hcrx := countRun_le_length x xs
    rw [rlEncodeLengths.go]
    by_cases hx0 : x = 0
    · subst hx0
      simp only [beq_self_eq_true, ↓reduceIte]
      by_cases hge11 : 1 + countRun 0 xs >= 11
      · -- code 18: repeat zero 11-138
        rw [if_pos (by omega : 1 + countRun 0 xs ≥ 11), rlDecode_go_code18]
        rw [show min (1 + countRun 0 xs) 138 - 11 + 11 = min (1 + countRun 0 xs) 138 from by omega]
        rw [rlDecodeLengths_go_rlEncodeLengths_go _ _ (drop_subset_valid hxs_valid)]
        simp only [List.append_assoc]
        exact congrArg (fun z => some (acc ++ z))
          (replicate_drop_eq_cons_zero xs _ (by omega) (by omega))
      · rw [if_neg (by omega)]
        by_cases hge3 : 1 + countRun 0 xs >= 3
        · -- code 17: repeat zero 3-10
          rw [if_pos (by omega : 1 + countRun 0 xs ≥ 3), rlDecode_go_code17]
          rw [show 1 + countRun 0 xs - 3 + 3 = 1 + countRun 0 xs from by omega]
          rw [rlDecodeLengths_go_rlEncodeLengths_go _ _ (drop_subset_valid hxs_valid)]
          simp only [List.append_assoc]
          exact congrArg (fun z => some (acc ++ z))
            (replicate_drop_eq_cons_zero xs _ (by omega) (by omega))
        · -- literal 0
          rw [if_neg (by omega), rlDecode_go_literal 0 0 _ _ (by omega)]
          rw [rlDecodeLengths_go_rlEncodeLengths_go xs (acc ++ [0]) hxs_valid]
          simp [List.append_assoc]
    · simp only [show (x == 0) = false from by cases h : x == 0 <;> simp_all [beq_iff_eq],
                  Bool.false_eq_true, ↓reduceIte]
      by_cases hge3 : countRun x xs >= 3
      · -- literal + code 16: repeat previous 3-6
        rw [if_pos (by omega : countRun x xs ≥ 3)]
        rw [rlDecode_go_literal x 0 _ _ hx_valid, rlDecode_go_code16 _ _ _ (by simp)]
        rw [show (acc ++ [x]).getLast! = x from by simp]
        rw [show min (countRun x xs) 6 - 3 + 3 = min (countRun x xs) 6 from by omega]
        rw [rlDecodeLengths_go_rlEncodeLengths_go _ _ (drop_subset_valid hxs_valid)]
        simp only [List.append_assoc]
        exact congrArg (fun z => some (acc ++ z))
          (singleton_replicate_drop_eq_cons x xs _ (Nat.min_le_left _ _))
      · -- literal (no repeat)
        rw [if_neg (by omega), rlDecode_go_literal x 0 _ _ hx_valid]
        rw [rlDecodeLengths_go_rlEncodeLengths_go xs (acc ++ [x]) hxs_valid]
        simp [List.append_assoc]
termination_by lengths.length
decreasing_by all_goals simp_all [List.length_drop] <;> omega

/-- Encoding then decoding code lengths recovers the original list. -/
theorem rlDecodeLengths_rlEncodeLengths (lengths : List Nat)
    (hvalid : ∀ x ∈ lengths, x ≤ 15) :
    rlDecodeLengths (rlEncodeLengths lengths) = some lengths := by
  simp only [rlDecodeLengths, rlEncodeLengths]
  have := rlDecodeLengths_go_rlEncodeLengths_go lengths [] hvalid
  simp at this
  exact this

/-- Every entry produced by `rlEncodeLengths.go` satisfies the CL code constraints. -/
theorem rlEncodeLengths_go_valid (lengths : List Nat)
    (hvalid : ∀ x ∈ lengths, x ≤ 15) :
    ∀ entry ∈ rlEncodeLengths.go lengths,
      (entry.1 ≤ 15 ∧ entry.2 = 0) ∨
      (entry.1 = 16 ∧ entry.2 ≤ 3) ∨
      (entry.1 = 17 ∧ entry.2 ≤ 7) ∨
      (entry.1 = 18 ∧ entry.2 ≤ 127) := by
  match lengths with
  | [] => simp [rlEncodeLengths.go]
  | x :: xs =>
    have hx_valid : x ≤ 15 := hvalid x (.head ..)
    have hxs_valid : ∀ y ∈ xs, y ≤ 15 := fun y hy => hvalid y (List.mem_cons_of_mem x hy)
    rw [rlEncodeLengths.go]
    by_cases hx0 : x = 0
    · subst hx0
      simp only [beq_self_eq_true, ↓reduceIte]
      by_cases hge11 : 1 + countRun 0 xs ≥ 11
      · rw [if_pos (by omega : 1 + countRun 0 xs ≥ 11)]
        intro entry hmem
        simp only [List.mem_cons] at hmem
        cases hmem with
        | inl h => subst h; right; right; right; constructor <;> omega
        | inr h =>
          exact rlEncodeLengths_go_valid _ (drop_subset_valid hxs_valid) entry h
      · rw [if_neg (by omega)]
        by_cases hge3 : 1 + countRun 0 xs ≥ 3
        · rw [if_pos (by omega : 1 + countRun 0 xs ≥ 3)]
          intro entry hmem
          simp only [List.mem_cons] at hmem
          cases hmem with
          | inl h => subst h; right; right; left; constructor <;> omega
          | inr h =>
            exact rlEncodeLengths_go_valid _ (drop_subset_valid hxs_valid) entry h
        · rw [if_neg (by omega)]
          intro entry hmem
          simp only [List.mem_cons] at hmem
          cases hmem with
          | inl h => subst h; left; exact ⟨by omega, rfl⟩
          | inr h =>
            exact rlEncodeLengths_go_valid _ hxs_valid entry h
    · simp only [show (x == 0) = false from by cases h : x == 0 <;> simp_all [beq_iff_eq],
                  Bool.false_eq_true, ↓reduceIte]
      by_cases hge3 : countRun x xs ≥ 3
      · rw [if_pos (by omega : countRun x xs ≥ 3)]
        intro entry hmem
        simp only [List.mem_cons] at hmem
        cases hmem with
        | inl h => subst h; left; exact ⟨hx_valid, rfl⟩
        | inr h =>
          cases h with
          | inl h => subst h; right; left; constructor <;> omega
          | inr h =>
            exact rlEncodeLengths_go_valid _ (drop_subset_valid hxs_valid) entry h
      · rw [if_neg (by omega)]
        intro entry hmem
        simp only [List.mem_cons] at hmem
        cases hmem with
        | inl h => subst h; left; exact ⟨hx_valid, rfl⟩
        | inr h =>
          exact rlEncodeLengths_go_valid _ hxs_valid entry h
termination_by lengths.length
decreasing_by all_goals simp_all [List.length_drop] <;> omega

/-- Every entry produced by `rlEncodeLengths` satisfies the CL code constraints:
    codes 0-15 have extra = 0, code 16 has extra ≤ 3, code 17 has extra ≤ 7,
    code 18 has extra ≤ 127. -/
theorem rlEncodeLengths_valid (lengths : List Nat)
    (hvalid : ∀ x ∈ lengths, x ≤ 15) :
    ∀ entry ∈ rlEncodeLengths lengths,
      (entry.1 ≤ 15 ∧ entry.2 = 0) ∨
      (entry.1 = 16 ∧ entry.2 ≤ 3) ∨
      (entry.1 = 17 ∧ entry.2 ≤ 7) ∨
      (entry.1 = 18 ∧ entry.2 ≤ 127) := by
  exact rlEncodeLengths_go_valid lengths hvalid

/-! ## Dynamic block header encoding (RFC 1951 §3.2.7) -/

/-- CL code length alphabet order for DEFLATE dynamic block headers
    (RFC 1951 §3.2.7). This is the same permutation as `codeLengthOrder`
    on the decode side. -/
protected def clPermutation : List Nat :=
  [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15]

/-- Count frequencies of CL symbols (0–18) in a list of `CLEntry` pairs.
    Returns a list of 19 frequency counts indexed by symbol. -/
def clSymbolFreqs (entries : List CLEntry) : List Nat :=
  entries.foldl (fun acc (code, _) =>
    if code < acc.length then acc.set code (acc.getD code 0 + 1) else acc)
    (List.replicate 19 0)

/-- Encode the extra bits for a CL entry.
    - Code 16: 2 extra bits (repeat count − 3)
    - Code 17: 3 extra bits (repeat count − 3)
    - Code 18: 7 extra bits (repeat count − 11)
    - Codes 0–15: no extra bits -/
def encodeCLExtra (code extra : Nat) : List Bool :=
  if code == 16 then writeBitsLSB 2 extra
  else if code == 17 then writeBitsLSB 3 extra
  else if code == 18 then writeBitsLSB 7 extra
  else []

/-- Write the CL code lengths in permuted order as 3-bit values.
    This is the inverse of `readCLLengths`. -/
def writeCLLengths (clLens : List Nat) (numCodeLen : Nat) : List Bool :=
  (Deflate.Spec.clPermutation.take numCodeLen).flatMap fun pos =>
    writeBitsLSB 3 (clLens.getD pos 0)

/-- Encode CL entries using the CL Huffman table.
    Each entry is encoded as: Huffman codeword + extra bits.
    This is the inverse of `decodeCLSymbols`. -/
def encodeCLEntries (clTable : List (Huffman.Spec.Codeword × Nat))
    (entries : List CLEntry) : Option (List Bool) :=
  match entries with
  | [] => some []
  | (code, extra) :: rest => do
    let cw ← encodeSymbol clTable code
    let restBits ← encodeCLEntries clTable rest
    return cw ++ encodeCLExtra code extra ++ restBits

/-- Determine the number of CL code lengths to transmit (HCLEN + 4).
    We need at least 4 and find the last non-zero entry in permuted order. -/
def computeHCLEN (clLens : List Nat) : Nat :=
  let permutedLens := Deflate.Spec.clPermutation.map fun pos => clLens.getD pos 0
  let lastNonZero := permutedLens.length -
    (permutedLens.reverse.takeWhile (· == 0)).length
  max 4 lastNonZero

/-- Encode the dynamic Huffman tree header for a DEFLATE dynamic block.
    Takes lit/len code lengths and distance code lengths, returns the
    header bit sequence that `decodeDynamicTables` can decode.
    Returns `none` if the code lengths cannot be validly encoded. -/
def encodeDynamicTrees (litLens : List Nat) (distLens : List Nat) :
    Option (List Bool) := do
  -- Validate input sizes
  guard (litLens.length ≥ 257 ∧ litLens.length ≤ 288)
  guard (distLens.length ≥ 1 ∧ distLens.length ≤ 32)
  let hlit := litLens.length - 257
  let hdist := distLens.length - 1

  -- Step 1: RLE-encode the concatenated code lengths
  let allLens := litLens ++ distLens
  let clEntries := rlEncodeLengths allLens

  -- Step 2: Compute CL code lengths from symbol frequencies
  let clFreqs := clSymbolFreqs clEntries
  let clFreqPairs := (List.range clFreqs.length).map fun i => (i, clFreqs.getD i 0)
  let clLens := Huffman.Spec.computeCodeLengths clFreqPairs 19 7

  -- Step 3: Build CL Huffman codes
  let clCodes := Huffman.Spec.allCodes clLens 7
  let clTable := clCodes.map fun (sym, cw) => (cw, sym)

  -- Step 4: Determine HCLEN
  let numCodeLen := computeHCLEN clLens
  let hclen := numCodeLen - 4

  -- Step 5: Encode CL entries using the CL Huffman table
  let symbolBits ← encodeCLEntries clTable clEntries

  -- Step 6: Assemble header bits
  let headerBits := writeBitsLSB 5 hlit ++
    writeBitsLSB 5 hdist ++
    writeBitsLSB 4 hclen
  let clLenBits := writeCLLengths clLens numCodeLen

  return headerBits ++ clLenBits ++ symbolBits

/-! ## Helper lemmas for the dynamic tree header roundtrip -/

protected theorem clPermutation_length : Deflate.Spec.clPermutation.length = 19 := by decide

/-- `codeLengthOrder.toList` is the same list as `clPermutation`. -/
private theorem codeLengthOrder_toList_eq_clPermutation :
    codeLengthOrder.toList = Deflate.Spec.clPermutation := by rfl

theorem computeHCLEN_ge_four (clLens : List Nat) : computeHCLEN clLens ≥ 4 := by
  simp [computeHCLEN]; omega

theorem computeHCLEN_le_nineteen (clLens : List Nat) : computeHCLEN clLens ≤ 19 := by
  simp only [computeHCLEN]
  have : (Deflate.Spec.clPermutation.map fun pos => clLens.getD pos 0).length = 19 := by
    simp [Deflate.Spec.clPermutation_length]
  omega

/-! ## readCLLengths / writeCLLengths roundtrip -/

/-- Reading back CL lengths written by `writeCLLengths` recovers the values
    in the correct permuted positions.

    The result accumulator has `clLens.getD pos 0` at each position `pos`
    that is `codeLengthOrder[j]` for some `j < numCodeLen`, and retains
    the original `acc` values elsewhere. -/
private theorem readCLLengths_writeCLLengths_go
    (clLens : List Nat) (n idx : Nat) (acc : List Nat) (rest : List Bool)
    (hacc : acc.length = 19) (hidx : idx + n ≤ 19)
    (hvals : ∀ i, clLens.getD i 0 < 8) :
    Deflate.Spec.readCLLengths n idx acc
      ((Deflate.Spec.clPermutation.drop idx |>.take n).flatMap
        (fun pos => writeBitsLSB 3 (clLens.getD pos 0)) ++ rest) =
    some ((Deflate.Spec.clPermutation.drop idx |>.take n).foldl
      (fun a pos => a.set pos (clLens.getD pos 0))
      acc, rest) := by
  induction n generalizing idx acc with
  | zero =>
    simp [Deflate.Spec.readCLLengths]
  | succ k ih =>
    have hidx_lt : idx < 19 := by omega
    have hperm_len := Deflate.Spec.clPermutation_length
    -- Unfold the drop/take to expose the head element
    have hdrop_cons : Deflate.Spec.clPermutation.drop idx =
        Deflate.Spec.clPermutation[idx] :: Deflate.Spec.clPermutation.drop (idx + 1) :=
      (List.getElem_cons_drop (h := by omega)).symm
    simp only [hdrop_cons, List.take_succ_cons, List.flatMap_cons, List.foldl_cons]
    rw [List.append_assoc]
    -- readCLLengths unfolds one step
    rw [Deflate.Spec.readCLLengths]
    -- Bridge: codeLengthOrder[idx]! = clPermutation[idx]
    have hCOsize : codeLengthOrder.size = 19 := by
      have := congrArg List.length codeLengthOrder_toList_eq_clPermutation
      simp only [Array.length_toList] at this; omega
    have hpos : codeLengthOrder[idx]! = Deflate.Spec.clPermutation[idx] := by
      rw [getElem!_pos codeLengthOrder idx (by omega)]
      rw [show codeLengthOrder[idx] =
          codeLengthOrder.toList[idx]'(by
            rw [codeLengthOrder_toList_eq_clPermutation]; omega) from
        (Array.getElem_toList (h := by omega)).symm]
      exact List.getElem_of_eq codeLengthOrder_toList_eq_clPermutation _
    -- readBitsLSB 3 recovers the value
    have hval : clLens.getD Deflate.Spec.clPermutation[idx] 0 < 2 ^ 3 := by
      have := hvals Deflate.Spec.clPermutation[idx]; omega
    rw [Deflate.Correctness.readBitsLSB_writeBitsLSB 3 _ _ hval]
    simp only [bind, Option.bind]
    -- The position written by readCLLengths matches clPermutation[idx]
    rw [hpos]
    -- Apply IH with updated accumulator
    have hacc' : (acc.set Deflate.Spec.clPermutation[idx]
        (clLens.getD Deflate.Spec.clPermutation[idx] 0)).length = 19 := by
      simp [hacc]
    exact ih (idx + 1) _ hacc' (by omega)

/-- `writeCLLengths` unfolds to a flatMap over the clPermutation. -/
private theorem writeCLLengths_eq_flatMap (clLens : List Nat) (numCodeLen : Nat) :
    writeCLLengths clLens numCodeLen =
    (Deflate.Spec.clPermutation.take numCodeLen).flatMap
      (fun pos => writeBitsLSB 3 (clLens.getD pos 0)) := by
  simp [writeCLLengths]

/-- Full roundtrip: `readCLLengths` on `writeCLLengths` output produces
    the expected accumulator. -/
theorem readCLLengths_writeCLLengths
    (clLens : List Nat) (numCodeLen : Nat) (rest : List Bool)
    (hnum : numCodeLen ≤ 19)
    (hvals : ∀ i, clLens.getD i 0 < 8) :
    Deflate.Spec.readCLLengths numCodeLen 0 (List.replicate 19 0)
      (writeCLLengths clLens numCodeLen ++ rest) =
    some ((Deflate.Spec.clPermutation.take numCodeLen).foldl
      (fun a pos => a.set pos (clLens.getD pos 0))
      (List.replicate 19 0), rest) := by
  rw [writeCLLengths_eq_flatMap]
  have := readCLLengths_writeCLLengths_go clLens numCodeLen 0 (List.replicate 19 0) rest
    (by simp) (by omega) hvals
  simp only [List.drop_zero] at this
  exact this

/-! ## CL entry encoding/decoding roundtrip -/

/-- The CL Huffman table constructed by `encodeDynamicTrees` is prefix-free,
    enabling single-symbol encode/decode roundtrip via `encodeSymbol_decode`. -/
private theorem clTable_prefix_free
    (clLens : List Nat) (maxBits : Nat)
    (hv : Huffman.Spec.ValidLengths clLens maxBits) :
    let clTable := (Huffman.Spec.allCodes clLens maxBits).map fun (sym, cw) => (cw, sym)
    ∀ cw₁ s₁ cw₂ s₂, (cw₁, s₁) ∈ clTable → (cw₂, s₂) ∈ clTable →
      (cw₁, s₁) ≠ (cw₂, s₂) → ¬cw₁.IsPrefix cw₂ :=
  flipped_allCodes_prefix_free clLens maxBits hv

/-- `rlDecodeLengths.go` only appends to the accumulator, so the result
    is at least as long as the input accumulator. -/
private theorem rlDecodeLengths_go_mono (entries : List CLEntry) (acc result : List Nat)
    (h : rlDecodeLengths.go entries acc = some result) :
    acc.length ≤ result.length := by
  induction entries generalizing acc with
  | nil => simp [rlDecodeLengths.go] at h; subst h; omega
  | cons entry rest ih =>
    obtain ⟨code, extra⟩ := entry
    by_cases hle : code ≤ 15
    · rw [rlDecode_go_literal code extra rest acc hle] at h
      have := ih _ h; simp at this; omega
    · by_cases h16 : code = 16
      · subst h16
        by_cases hg : 0 < acc.length
        · rw [rlDecode_go_code16 extra rest acc hg] at h
          have := ih _ h; simp at this; omega
        · exfalso; simp [rlDecodeLengths.go, hg, guard, bind, failure] at h
      · by_cases h17 : code = 17
        · subst h17; rw [rlDecode_go_code17 extra rest acc] at h
          have := ih _ h; simp at this; omega
        · by_cases h18 : code = 18
          · subst h18; rw [rlDecode_go_code18 extra rest acc] at h
            have := ih _ h; simp at this; omega
          · exfalso; simp only [rlDecodeLengths.go] at h
            split at h; · omega
            split at h; · exact absurd (beq_iff_eq.mp ‹_›) h16
            split at h; · exact absurd (beq_iff_eq.mp ‹_›) h17
            split at h; · exact absurd (beq_iff_eq.mp ‹_›) h18
            exact absurd h (by simp)

/-- When `rlDecodeLengths.go` succeeds on a non-empty list, the result is
    strictly longer than the input accumulator. -/
private theorem rlDecodeLengths_go_strict_mono
    (entry : CLEntry) (rest : List CLEntry) (acc result : List Nat)
    (h : rlDecodeLengths.go (entry :: rest) acc = some result) :
    acc.length < result.length := by
  obtain ⟨code, extra⟩ := entry
  by_cases hle : code ≤ 15
  · rw [rlDecode_go_literal code extra rest acc hle] at h
    have := rlDecodeLengths_go_mono rest _ _ h; simp at this; omega
  · by_cases h16 : code = 16
    · subst h16
      by_cases hg : 0 < acc.length
      · rw [rlDecode_go_code16 extra rest acc hg] at h
        have := rlDecodeLengths_go_mono rest _ _ h; simp at this; omega
      · exfalso; simp [rlDecodeLengths.go, hg, guard, bind, failure] at h
    · by_cases h17 : code = 17
      · subst h17; rw [rlDecode_go_code17 extra rest acc] at h
        have := rlDecodeLengths_go_mono rest _ _ h; simp at this; omega
      · by_cases h18 : code = 18
        · subst h18; rw [rlDecode_go_code18 extra rest acc] at h
          have := rlDecodeLengths_go_mono rest _ _ h; simp at this; omega
        · exfalso; simp only [rlDecodeLengths.go] at h
          split at h; · omega
          split at h; · exact absurd (beq_iff_eq.mp ‹_›) h16
          split at h; · exact absurd (beq_iff_eq.mp ‹_›) h17
          split at h; · exact absurd (beq_iff_eq.mp ‹_›) h18
          exact absurd h (by simp)

private theorem getLast?_getD_eq_getLast! (l : List Nat) (h : l.length > 0) :
    l.getLast?.getD 0 = l.getLast! := by
  induction l with
  | nil => simp at h
  | cons a as ih =>
    cases as with
    | nil => rfl
    | cons b bs => simp [List.getLast?, List.getLast!]

/-- Encoding CL entries then decoding with `decodeCLSymbols` recovers
    the original code lengths (via RLE decode).

    Uses `rlDecodeLengths.go` with a general accumulator for induction.
    The fuel parameter must be ≥ entries.length + 1 (one per entry plus
    one for the final base-case check). -/
private theorem encodeCLEntries_decodeCLSymbols_go
    (clLens : List Nat)
    (clTable : List (Huffman.Spec.Codeword × Nat))
    (entries : List CLEntry)
    (symbolBits : List Bool)
    (rest : List Bool)
    (totalCodes : Nat)
    (acc : List Nat)
    (fuel : Nat)
    (hv : Huffman.Spec.ValidLengths clLens 7)
    (htable : clTable = (Huffman.Spec.allCodes clLens 7).map fun (sym, cw) => (cw, sym))
    (henc : encodeCLEntries clTable entries = some symbolBits)
    (hvalid : ∀ entry ∈ entries, (entry.1 ≤ 15 ∧ entry.2 = 0) ∨
      (entry.1 = 16 ∧ entry.2 ≤ 3) ∨
      (entry.1 = 17 ∧ entry.2 ≤ 7) ∨
      (entry.1 = 18 ∧ entry.2 ≤ 127))
    (hdec : rlDecodeLengths.go entries acc = some result)
    (hlen : result.length = totalCodes)
    (hacc_le : acc.length ≤ totalCodes)
    (hfuel : fuel ≥ entries.length + 1) :
    decodeDynamicTables.decodeCLSymbols clTable totalCodes acc
      (symbolBits ++ rest) fuel =
    some (result, rest) := by
  induction entries generalizing acc symbolBits fuel with
  | nil =>
    -- Base case: no entries, result = acc, fuel ≥ 1
    simp [encodeCLEntries] at henc; subst henc
    simp [rlDecodeLengths.go] at hdec; subst hdec
    simp only [List.nil_append]
    match fuel, hfuel with
    | fuel' + 1, _ =>
      simp [decodeDynamicTables.decodeCLSymbols, show acc.length ≥ totalCodes from by omega]
  | cons entry restEntries ih =>
    obtain ⟨code, extra⟩ := entry
    -- Decompose encodeCLEntries
    simp only [encodeCLEntries] at henc
    cases hcw : encodeSymbol clTable code with
    | none => simp [hcw, bind, Option.bind] at henc
    | some cw =>
      cases hrestBits : encodeCLEntries clTable restEntries with
      | none => simp [hcw, hrestBits, bind, Option.bind] at henc
      | some restBits =>
        simp only [hcw, hrestBits, bind, Option.bind, pure, Pure.pure] at henc
        simp only [Option.some.injEq] at henc; subst henc
        -- Key facts
        have hacc_lt : acc.length < totalCodes :=
          hlen ▸ rlDecodeLengths_go_strict_mono (code, extra) restEntries acc result hdec
        have hvalid_rest : ∀ entry ∈ restEntries,
            (entry.1 ≤ 15 ∧ entry.2 = 0) ∨ (entry.1 = 16 ∧ entry.2 ≤ 3) ∨
            (entry.1 = 17 ∧ entry.2 ≤ 7) ∨ (entry.1 = 18 ∧ entry.2 ≤ 127) :=
          fun e he => hvalid e (List.mem_cons_of_mem _ he)
        have hpf : ∀ cw₁ s₁ cw₂ s₂, (cw₁, s₁) ∈ clTable → (cw₂, s₂) ∈ clTable →
            (cw₁, s₁) ≠ (cw₂, s₂) → ¬cw₁.IsPrefix cw₂ := by
          rw [htable]; exact flipped_allCodes_prefix_free clLens 7 hv
        have hentry := hvalid (code, extra) (.head ..)
        -- Decompose fuel
        match fuel, hfuel with
        | fuel' + 1, hfuel' =>
          -- Unfold decodeCLSymbols, enter decode branch
          simp only [decodeDynamicTables.decodeCLSymbols,
            show ¬(acc.length ≥ totalCodes) from by omega, ↓reduceIte]
          -- Reassociate bits for Huffman decode
          rw [show (cw ++ encodeCLExtra code extra ++ restBits) ++ rest =
              cw ++ (encodeCLExtra code extra ++ restBits ++ rest) from by
            simp [List.append_assoc]]
          rw [encodeSymbol_decode _ _ _ _ hcw hpf]
          simp only [bind, Option.bind]
          -- Case split on the code type
          by_cases hle : code ≤ 15
          · -- Literal code (0-15): no extra bits
            rw [if_pos (show code < 16 from by omega)]
            -- encodeCLExtra for code ≤ 15 is []
            have h16f : (code == 16) = false := by
              cases h : code == 16 <;> simp_all [beq_iff_eq] <;> omega
            have h17f : (code == 17) = false := by
              cases h : code == 17 <;> simp_all [beq_iff_eq] <;> omega
            have h18f : (code == 18) = false := by
              cases h : code == 18 <;> simp_all [beq_iff_eq] <;> omega
            simp only [encodeCLExtra, h16f, h17f, h18f,
              Bool.false_eq_true, ↓reduceIte, List.nil_append]
            -- rlDecodeLengths.go step for literal
            rw [rlDecode_go_literal code extra restEntries acc hle] at hdec
            -- Apply IH
            exact ih restBits (acc ++ [code]) fuel' hrestBits hvalid_rest hdec
              (by simp; omega) (by simp at hfuel' ⊢; omega)
          · -- Repeat codes (16, 17, 18)
            rw [if_neg (show ¬(code < 16) from by omega)]
            -- From hentry and ¬(code ≤ 15), code must be 16, 17, or 18
            cases hentry with
            | inl h => exact absurd h.1 (by omega)
            | inr h => cases h with
              | inl h16 =>
                -- Code 16: repeat previous code
                have h16eq := h16.1; have hextra := h16.2; subst h16eq
                -- Prove acc non-empty (guard in rlDecodeLengths.go for code 16)
                have haccpos : acc.length > 0 := by
                  by_cases hpos : acc.length > 0
                  · exact hpos
                  · exfalso; have : acc.length = 0 := by omega
                    simp [rlDecodeLengths.go, this, guard, failure, bind, Option.bind] at hdec
                -- rlDecodeLengths step
                rw [rlDecode_go_code16 extra restEntries acc haccpos] at hdec
                have hacc' : (acc ++ List.replicate (extra + 3) acc.getLast!).length ≤ totalCodes :=
                  hlen ▸ rlDecodeLengths_go_mono restEntries _ _ hdec
                -- readBitsLSB roundtrip
                have hrb : readBitsLSB 2 (writeBitsLSB 2 extra ++ (restBits ++ rest)) =
                    some (extra, restBits ++ rest) :=
                  Deflate.Correctness.readBitsLSB_writeBitsLSB 2 extra _ (by omega)
                -- Reduce desugared do-notation
                simp [encodeCLExtra, guard, haccpos, hrb, List.append_assoc, pure, Pure.pure]
                have : acc.length + (extra + 3) ≤ totalCodes := by
                  have := hacc'; simp at this; exact this
                simp only [this, ↓reduceIte]
                rw [getLast?_getD_eq_getLast! acc haccpos]
                exact ih restBits (acc ++ List.replicate (extra + 3) acc.getLast!) fuel'
                  hrestBits hvalid_rest hdec hacc'
                  (by simp only [List.length_cons] at hfuel'; omega)
              | inr h => cases h with
                | inl h17 =>
                  -- Code 17: repeat 0, 3-10 times
                  have h17eq := h17.1; have hextra := h17.2; subst h17eq
                  -- rlDecodeLengths step
                  rw [rlDecode_go_code17 extra restEntries acc] at hdec
                  have hacc' : (acc ++ List.replicate (extra + 3) 0).length ≤ totalCodes :=
                    hlen ▸ rlDecodeLengths_go_mono restEntries _ _ hdec
                  -- readBitsLSB roundtrip
                  have hrb : readBitsLSB 3 (writeBitsLSB 3 extra ++ (restBits ++ rest)) =
                      some (extra, restBits ++ rest) :=
                    Deflate.Correctness.readBitsLSB_writeBitsLSB 3 extra _ (by omega)
                  -- Reduce desugared do-notation
                  simp [encodeCLExtra, guard, hrb, List.append_assoc, pure, Pure.pure]
                  have : acc.length + (extra + 3) ≤ totalCodes := by
                    have := hacc'; simp at this; exact this
                  simp [this]
                  exact ih restBits (acc ++ List.replicate (extra + 3) 0) fuel'
                    hrestBits hvalid_rest hdec hacc'
                    (by simp only [List.length_cons] at hfuel'; omega)
                | inr h18 =>
                  -- Code 18: repeat 0, 11-138 times
                  have h18eq := h18.1; have hextra := h18.2; subst h18eq
                  -- rlDecodeLengths step
                  rw [rlDecode_go_code18 extra restEntries acc] at hdec
                  have hacc' : (acc ++ List.replicate (extra + 11) 0).length ≤ totalCodes :=
                    hlen ▸ rlDecodeLengths_go_mono restEntries _ _ hdec
                  -- readBitsLSB roundtrip
                  have hrb : readBitsLSB 7 (writeBitsLSB 7 extra ++ (restBits ++ rest)) =
                      some (extra, restBits ++ rest) :=
                    Deflate.Correctness.readBitsLSB_writeBitsLSB 7 extra _ (by omega)
                  -- Reduce desugared do-notation
                  simp [encodeCLExtra, guard, hrb, List.append_assoc, pure, Pure.pure]
                  have : acc.length + (extra + 11) ≤ totalCodes := by
                    have := hacc'; simp at this; exact this
                  simp [this]
                  exact ih restBits (acc ++ List.replicate (extra + 11) 0) fuel'
                    hrestBits hvalid_rest hdec hacc'
                    (by simp only [List.length_cons] at hfuel'; omega)

/-! ## Dynamic tree header roundtrip -/

/-- The dynamic tree header roundtrip: encoding then decoding recovers
    the original code lengths. -/
theorem encodeDynamicTrees_decodeDynamicTables
    (litLens distLens : List Nat)
    (headerBits rest : List Bool)
    (hlit : ∀ x ∈ litLens, x ≤ 15) (hdist : ∀ x ∈ distLens, x ≤ 15)
    (hlitLen : litLens.length ≥ 257 ∧ litLens.length ≤ 288)
    (hdistLen : distLens.length ≥ 1 ∧ distLens.length ≤ 32)
    (henc : encodeDynamicTrees litLens distLens = some headerBits) :
    decodeDynamicTables (headerBits ++ rest) = some (litLens, distLens, rest) := by
  sorry

end Deflate.Spec
