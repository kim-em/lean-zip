import Zip.Spec.BitstreamCorrect
import Zip.Spec.BitstreamComplete
import ZipForStd.Array

/-!
# Huffman Decode Correspondence

Proves that the native `HuffTree.decode` agrees with the spec's table-based
`Huffman.Spec.decode`. The proof is decomposed into two steps:
1. **BitReader→bits**: `decode_go_decodeBits` — the tree-based decode via
   `BitReader` corresponds to a pure decode on the bit list (`decodeBits`).
2. **Tree→table**: the pure tree decode agrees with the spec's linear-search
   decode on the code table, via `TreeHasLeaf` and `fromLengths` correspondence.
-/

namespace Deflate.Correctness

/-! ### insert bit-value helpers

These bridge `UInt32` shift-and-mask to `Nat.testBit` for the insert proofs. -/

/-- When `testBit n = false`, insert's bit comparison yields `true` (bit == 0). -/
private theorem insert_bit_zero (code : UInt32) (n : Nat) (hn : n < 32)
    (h : code.toNat.testBit n = false) :
    ((code >>> n.toUInt32) &&& 1 == (0 : UInt32)) = true := by
  have := uint32_testBit code n hn; rw [h] at this; simp [this]

/-- When `testBit n = true`, insert's bit comparison yields `false` (bit != 0). -/
private theorem insert_bit_one (code : UInt32) (n : Nat) (hn : n < 32)
    (h : code.toNat.testBit n = true) :
    ((code >>> n.toUInt32) &&& 1 == (0 : UInt32)) = false := by
  have := uint32_testBit code n hn; rw [h] at this; simp [this]

/-! ## Pure tree decode -/

/-- Pure tree decode on a bit list. Follows the same logic as
    `HuffTree.decode.go` but operates on `List Bool` instead of `BitReader`. -/
def decodeBits : Zip.Native.HuffTree → List Bool → Option (UInt16 × List Bool)
  | .leaf s, bits => some (s, bits)
  | .empty, _ => none
  | .node _ _, [] => none
  | .node _ o, true :: bits => decodeBits o bits
  | .node z _, false :: bits => decodeBits z bits

/-- Step 1: `decode.go` via BitReader corresponds to `decodeBits` on the
    spec bit list. By induction on the tree structure. -/
protected theorem decode_go_decodeBits (tree : Zip.Native.HuffTree)
    (br : Zip.Native.BitReader) (n : Nat)
    (sym : UInt16) (br' : Zip.Native.BitReader)
    (hwf : br.bitOff < 8)
    (h : Zip.Native.HuffTree.decode.go tree br n = .ok (sym, br')) :
    decodeBits tree br.toBits = some (sym, br'.toBits) ∧
    br'.bitOff < 8 := by
  induction tree generalizing br n with
  | leaf s =>
    simp only [Zip.Native.HuffTree.decode.go] at h
    obtain ⟨rfl, rfl⟩ := Except.ok.inj h
    exact ⟨rfl, hwf⟩
  | empty =>
    simp [Zip.Native.HuffTree.decode.go] at h
  | node z o ihz iho =>
    simp only [Zip.Native.HuffTree.decode.go] at h
    split at h
    · simp at h
    · -- n ≤ 20: readBit + recurse
      cases hrd : br.readBit with
      | error e =>
        simp [hrd, bind, Except.bind] at h
      | ok p =>
        obtain ⟨bit, br₁⟩ := p
        simp only [hrd, bind, Except.bind] at h
        -- Get bit correspondence
        obtain ⟨b, rest₁, hbr_bits, hbr1_bits, hbit_val⟩ :=
          readBit_toBits br bit br₁ hwf hrd
        have hwf₁ := readBit_wf br bit br₁ hwf hrd
        -- Case split on the bit value
        split at h
        · -- bit == 0: go left (b = false)
          rename_i hbit
          have hb : b = false := by cases b <;> simp_all
          obtain ⟨hspec, hwf'⟩ := ihz br₁ (n + 1) hwf₁ h
          refine ⟨?_, hwf'⟩
          rw [hbr_bits, hb]; simp only [decodeBits]
          rw [← hbr1_bits]; exact hspec
        · -- bit != 0: go right (b = true)
          rename_i hbit
          have hb : b = true := by cases b <;> simp_all
          obtain ⟨hspec, hwf'⟩ := iho br₁ (n + 1) hwf₁ h
          refine ⟨?_, hwf'⟩
          rw [hbr_bits, hb]; simp only [decodeBits]
          rw [← hbr1_bits]; exact hspec

/-! ### Tree-table correspondence via TreeHasLeaf

The proof that `decodeBits` agrees with `Huffman.Spec.decode` is structured
in layers:
1. **TreeHasLeaf**: inductive predicate relating tree paths to symbols
2. **decodeBits ↔ TreeHasLeaf**: structural correspondence
3. **insert creates correct paths**: `insert.go` places leaves correctly
4. **fromLengths establishes all paths**: the construction loop builds
   leaves for all canonical codes
5. **Final connection**: via `decode_prefix_free` from Huffman.Spec -/

/-- Predicate: tree `t` has a leaf with symbol `sym` at path `cw`,
    where `false` means "go left (zero)" and `true` means "go right (one)". -/
inductive TreeHasLeaf : Zip.Native.HuffTree → List Bool → UInt16 → Prop
  | leaf : TreeHasLeaf (.leaf s) [] s
  | left : TreeHasLeaf z cw s → TreeHasLeaf (.node z o) (false :: cw) s
  | right : TreeHasLeaf o cw s → TreeHasLeaf (.node z o) (true :: cw) s

/-- If the tree has a leaf at path `cw`, then `decodeBits` on `cw ++ rest`
    returns `(sym, rest)`. -/
protected theorem decodeBits_of_hasLeaf (tree : Zip.Native.HuffTree) (cw : List Bool)
    (sym : UInt16) (rest : List Bool) (h : TreeHasLeaf tree cw sym) :
    decodeBits tree (cw ++ rest) = some (sym, rest) := by
  induction h <;> simp_all [decodeBits]

/-- **Completeness for `decode.go`**: if the tree has a leaf at path `cw` and
    the BitReader's bits start with `cw ++ rest`, then the native `decode.go`
    succeeds with the same symbol. This is the reverse of `decode_go_decodeBits`. -/
protected theorem decode_go_complete (tree : Zip.Native.HuffTree)
    (cw : List Bool) (sym : UInt16) (rest : List Bool)
    (br : Zip.Native.BitReader) (n : Nat)
    (hleaf : TreeHasLeaf tree cw sym)
    (hwf : br.bitOff < 8)
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (hbits : br.toBits = cw ++ rest)
    (hn : n + cw.length ≤ 20) :
    ∃ br', Zip.Native.HuffTree.decode.go tree br n = .ok (sym, br') ∧
      br'.toBits = rest ∧ br'.bitOff < 8 ∧
      (br'.bitOff = 0 ∨ br'.pos < br'.data.size) := by
  induction hleaf generalizing br n with
  | leaf =>
    -- tree = .leaf s, cw = []: decode.go returns immediately
    simp only [List.nil_append] at hbits
    exact ⟨br, by simp [Zip.Native.HuffTree.decode.go], hbits, hwf, hpos⟩
  | left hleft ih =>
    -- tree = .node z o, cw = false :: cw': read bit false, recurse into z
    simp only [List.length_cons] at hn
    simp only [Zip.Native.HuffTree.decode.go, show ¬(n > 20) from by omega, ↓reduceIte]
    simp only [List.cons_append] at hbits
    obtain ⟨br₁, hrd, hbr1_bits, hwf₁, hpos₁⟩ :=
      Deflate.Correctness.readBit_complete br false _ hwf hbits
    simp only [hrd, bind, Except.bind]
    exact ih br₁ (n + 1) hwf₁ hpos₁ hbr1_bits (by omega)
  | right hright ih =>
    -- tree = .node z o, cw = true :: cw': read bit true, recurse into o
    simp only [List.length_cons] at hn
    simp only [Zip.Native.HuffTree.decode.go, show ¬(n > 20) from by omega, ↓reduceIte]
    simp only [List.cons_append] at hbits
    obtain ⟨br₁, hrd, hbr1_bits, hwf₁, hpos₁⟩ :=
      Deflate.Correctness.readBit_complete br true _ hwf hbits
    simp only [hrd, bind, Except.bind]
    exact ih br₁ (n + 1) hwf₁ hpos₁ hbr1_bits (by omega)

/-- If `decodeBits` returns `(sym, rest)`, then the tree has a leaf at some
    path `cw` with `bits = cw ++ rest`. -/
protected theorem hasLeaf_of_decodeBits (tree : Zip.Native.HuffTree) (bits : List Bool)
    (sym : UInt16) (rest : List Bool)
    (h : decodeBits tree bits = some (sym, rest)) :
    ∃ cw, TreeHasLeaf tree cw sym ∧ bits = cw ++ rest := by
  induction tree generalizing bits with
  | leaf s =>
    simp [decodeBits] at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], .leaf, by simp⟩
  | empty => simp [decodeBits] at h
  | node z o ihz iho =>
    cases bits with
    | nil => simp [decodeBits] at h
    | cons b rest' =>
      cases b with
      | false =>
        simp only [decodeBits] at h
        obtain ⟨cw, hleaf, hrst⟩ := ihz rest' h
        exact ⟨false :: cw, .left hleaf, by rw [hrst]; rfl⟩
      | true =>
        simp only [decodeBits] at h
        obtain ⟨cw, hleaf, hrst⟩ := iho rest' h
        exact ⟨true :: cw, .right hleaf, by rw [hrst]; rfl⟩

/-! ### insert.go creates the correct leaf path -/

/-- Predicate: tree `t` has no leaf at an intermediate position along `path`.
    This ensures `insert.go` can traverse the path without hitting a collision. -/
private def NoLeafOnPath : Zip.Native.HuffTree → List Bool → Prop
  | .leaf _, _ :: _ => False
  | .node z _, false :: rest => NoLeafOnPath z rest
  | .node _ o, true :: rest => NoLeafOnPath o rest
  | _, _ => True

/-- `insert.go` places a leaf at the path `natToBits code.toNat len` in the tree,
    provided no existing leaf blocks the path. -/
private theorem insert_go_hasLeaf (code : UInt32) (sym : UInt16)
    (tree : Zip.Native.HuffTree) (len : Nat) (hlen : len < 32)
    (hnl : NoLeafOnPath tree (Huffman.Spec.natToBits code.toNat len)) :
    TreeHasLeaf (Zip.Native.HuffTree.insert.go code sym tree len)
      (Huffman.Spec.natToBits code.toNat len) sym := by
  induction len generalizing tree with
  | zero =>
    simp only [Zip.Native.HuffTree.insert.go, Huffman.Spec.natToBits]
    exact .leaf
  | succ n ih =>
    simp only [Huffman.Spec.natToBits]
    cases htb : code.toNat.testBit n with
    | false =>
      have hbit : ((code >>> n.toUInt32) &&& 1 == (0 : UInt32)) = true :=
        insert_bit_zero code n (by omega) htb
      cases tree with
      | empty =>
        show TreeHasLeaf (Zip.Native.HuffTree.insert.go code sym .empty (n + 1)) _ _
        unfold Zip.Native.HuffTree.insert.go
        simp [hbit]
        exact .left (ih .empty (by omega) trivial)
      | node z o =>
        show TreeHasLeaf (Zip.Native.HuffTree.insert.go code sym (.node z o) (n + 1)) _ _
        unfold Zip.Native.HuffTree.insert.go
        simp [hbit]
        simp only [Huffman.Spec.natToBits, htb, NoLeafOnPath] at hnl
        exact .left (ih z (by omega) hnl)
      | leaf s =>
        simp only [Huffman.Spec.natToBits, htb, NoLeafOnPath] at hnl
    | true =>
      have hbit : ((code >>> n.toUInt32) &&& 1 == (0 : UInt32)) = false :=
        insert_bit_one code n (by omega) htb
      cases tree with
      | empty =>
        show TreeHasLeaf (Zip.Native.HuffTree.insert.go code sym .empty (n + 1)) _ _
        unfold Zip.Native.HuffTree.insert.go
        simp [hbit]
        exact .right (ih .empty (by omega) trivial)
      | node z o =>
        show TreeHasLeaf (Zip.Native.HuffTree.insert.go code sym (.node z o) (n + 1)) _ _
        unfold Zip.Native.HuffTree.insert.go
        simp [hbit]
        simp only [Huffman.Spec.natToBits, htb, NoLeafOnPath] at hnl
        exact .right (ih o (by omega) hnl)
      | leaf s =>
        simp only [Huffman.Spec.natToBits, htb, NoLeafOnPath] at hnl

/-! ### insert.go preserves existing leaves -/

/-- `insert.go` preserves existing leaves at paths that the insertion path is not
    a prefix of. This is the key preservation property: inserting a new code doesn't
    disrupt decoding of existing codes, provided they are prefix-free. -/
private theorem insert_go_preserves (code : UInt32) (sym : UInt16)
    (tree : Zip.Native.HuffTree) (len : Nat) (hlen : len < 32)
    (cw : List Bool) (s : UInt16)
    (h : TreeHasLeaf tree cw s)
    (hne : ¬(Huffman.Spec.natToBits code.toNat len).IsPrefix cw) :
    TreeHasLeaf (Zip.Native.HuffTree.insert.go code sym tree len) cw s := by
  induction len generalizing tree cw with
  | zero =>
    exact absurd List.nil_prefix hne
  | succ n ih =>
    cases h with
    | leaf =>
      -- tree = .leaf s, cw = []. Collision: insert.go returns .leaf s unchanged.
      show TreeHasLeaf
        (Zip.Native.HuffTree.insert.go code sym (.leaf _) (n + 1)) [] _
      unfold Zip.Native.HuffTree.insert.go
      exact .leaf
    | left h' =>
      -- tree = .node z o, cw = false :: cw', leaf is in z
      cases htb : code.toNat.testBit n with
      | false =>
        -- Same direction: insertion goes left too; recurse into z
        have hbit := insert_bit_zero code n (by omega) htb
        show TreeHasLeaf (Zip.Native.HuffTree.insert.go code sym _ (n + 1)) _ _
        unfold Zip.Native.HuffTree.insert.go
        simp [hbit]
        exact .left (ih _ (by omega) _ h' fun hpre =>
          hne (by simp [Huffman.Spec.natToBits, htb, hpre]))
      | true =>
        -- Different direction: insertion goes right; z is untouched
        have hbit := insert_bit_one code n (by omega) htb
        show TreeHasLeaf (Zip.Native.HuffTree.insert.go code sym _ (n + 1)) _ _
        unfold Zip.Native.HuffTree.insert.go
        simp [hbit]
        exact .left h'
    | right h' =>
      -- tree = .node z o, cw = true :: cw', leaf is in o
      cases htb : code.toNat.testBit n with
      | false =>
        -- Different direction: insertion goes left; o is untouched
        have hbit := insert_bit_zero code n (by omega) htb
        show TreeHasLeaf (Zip.Native.HuffTree.insert.go code sym _ (n + 1)) _ _
        unfold Zip.Native.HuffTree.insert.go
        simp [hbit]
        exact .right h'
      | true =>
        -- Same direction: insertion goes right too; recurse into o
        have hbit := insert_bit_one code n (by omega) htb
        show TreeHasLeaf (Zip.Native.HuffTree.insert.go code sym _ (n + 1)) _ _
        unfold Zip.Native.HuffTree.insert.go
        simp [hbit]
        exact .right (ih _ (by omega) _ h' fun hpre =>
          hne (by simp [Huffman.Spec.natToBits, htb, hpre]))

/-! ### insert.go preserves NoLeafOnPath for non-prefix paths -/

/-- `NoLeafOnPath` is trivially true for an empty path. -/
private theorem noLeafOnPath_nil (tree : Zip.Native.HuffTree) :
    NoLeafOnPath tree [] := by
  cases tree <;> trivial

/-- Inserting a code preserves `NoLeafOnPath` for a path that the inserted code
    is not a prefix of. This is needed to maintain the NoLeafOnPath invariant
    through sequential insertions of prefix-free codes. -/
private theorem insert_go_noLeafOnPath (code : UInt32) (sym : UInt16)
    (tree : Zip.Native.HuffTree) (len : Nat) (hlen : len < 32)
    (path : List Bool)
    (hno : NoLeafOnPath tree path)
    (hnp : ¬(Huffman.Spec.natToBits code.toNat len).IsPrefix path) :
    NoLeafOnPath (Zip.Native.HuffTree.insert.go code sym tree len) path := by
  induction len generalizing tree path with
  | zero =>
    exact absurd List.nil_prefix hnp
  | succ n ih =>
    cases path with
    | nil => exact noLeafOnPath_nil _
    | cons b rest =>
      cases htb : code.toNat.testBit n with
      | false =>
        have hbit := insert_bit_zero code n (by omega) htb
        cases tree with
        | empty =>
          -- insert into empty creates a node
          show NoLeafOnPath (Zip.Native.HuffTree.insert.go code sym .empty (n + 1)) (b :: rest)
          unfold Zip.Native.HuffTree.insert.go; simp [hbit]
          cases b with
          | false =>
            -- Same direction: recurse
            exact ih .empty (by omega) rest trivial fun hpre =>
              hnp (by simp [Huffman.Spec.natToBits, htb, hpre])
          | true => trivial  -- different direction, child is .empty
        | node z o =>
          show NoLeafOnPath (Zip.Native.HuffTree.insert.go code sym (.node z o) (n + 1)) (b :: rest)
          unfold Zip.Native.HuffTree.insert.go; simp [hbit]
          cases b with
          | false =>
            simp only [NoLeafOnPath] at hno
            exact ih z (by omega) rest hno fun hpre =>
              hnp (by simp [Huffman.Spec.natToBits, htb, hpre])
          | true =>
            simp only [NoLeafOnPath] at hno; exact hno
        | leaf s =>
          -- tree is leaf at intermediate position: NoLeafOnPath (leaf s) (b :: rest) = False
          simp only [NoLeafOnPath] at hno
      | true =>
        have hbit := insert_bit_one code n (by omega) htb
        cases tree with
        | empty =>
          show NoLeafOnPath (Zip.Native.HuffTree.insert.go code sym .empty (n + 1)) (b :: rest)
          unfold Zip.Native.HuffTree.insert.go; simp [hbit]
          cases b with
          | false => trivial  -- different direction, child is .empty
          | true =>
            exact ih .empty (by omega) rest trivial fun hpre =>
              hnp (by simp [Huffman.Spec.natToBits, htb, hpre])
        | node z o =>
          show NoLeafOnPath (Zip.Native.HuffTree.insert.go code sym (.node z o) (n + 1)) (b :: rest)
          unfold Zip.Native.HuffTree.insert.go; simp [hbit]
          cases b with
          | false =>
            simp only [NoLeafOnPath] at hno; exact hno
          | true =>
            simp only [NoLeafOnPath] at hno
            exact ih o (by omega) rest hno fun hpre =>
              hnp (by simp [Huffman.Spec.natToBits, htb, hpre])
        | leaf s =>
          simp only [NoLeafOnPath] at hno

/-- Every leaf in `insert.go` output is either from the original tree or at the
    inserted path. Unlike `insert_go_hasLeaf` (forward) which requires `NoLeafOnPath`,
    this handles the `.leaf` case (where `insert.go` returns the tree unchanged) by
    returning `.inl h`. -/
private theorem insert_go_complete' (code : UInt32) (sym : UInt16)
    (tree : Zip.Native.HuffTree) (len : Nat) (hlen : len < 32)
    (cw : List Bool) (s : UInt16)
    (h : TreeHasLeaf (Zip.Native.HuffTree.insert.go code sym tree len) cw s) :
    TreeHasLeaf tree cw s ∨ (cw = Huffman.Spec.natToBits code.toNat len ∧ s = sym) := by
  induction len generalizing tree cw with
  | zero =>
    simp only [Zip.Native.HuffTree.insert.go] at h
    cases h with
    | leaf => exact .inr ⟨by simp [Huffman.Spec.natToBits], rfl⟩
  | succ n ih =>
    cases htb : code.toNat.testBit n with
    | false =>
      have hbit := insert_bit_zero code n (by omega) htb
      cases tree with
      | empty =>
        simp only [Zip.Native.HuffTree.insert.go, hbit, ite_true] at h
        cases h with
        | left h' =>
          rcases ih .empty (by omega) _ h' with h | ⟨rfl, rfl⟩
          · exact absurd h (by intro h; cases h)
          · exact .inr ⟨by simp [Huffman.Spec.natToBits, htb], rfl⟩
        | right h' => exact absurd h' (by intro h; cases h)
      | node z o =>
        simp only [Zip.Native.HuffTree.insert.go, hbit, ite_true] at h
        cases h with
        | left h' =>
          rcases ih z (by omega) _ h' with h | ⟨rfl, rfl⟩
          · exact .inl (.left h)
          · exact .inr ⟨by simp [Huffman.Spec.natToBits, htb], rfl⟩
        | right h' => exact .inl (.right h')
      | leaf s' =>
        simp only [Zip.Native.HuffTree.insert.go] at h
        exact .inl h
    | true =>
      have hbit := insert_bit_one code n (by omega) htb
      cases tree with
      | empty =>
        simp only [Zip.Native.HuffTree.insert.go, hbit] at h
        cases h with
        | left h' => exact absurd h' (by intro h; cases h)
        | right h' =>
          rcases ih .empty (by omega) _ h' with h | ⟨rfl, rfl⟩
          · exact absurd h (by intro h; cases h)
          · exact .inr ⟨by simp [Huffman.Spec.natToBits, htb], rfl⟩
      | node z o =>
        simp only [Zip.Native.HuffTree.insert.go, hbit] at h
        cases h with
        | left h' => exact .inl (.left h')
        | right h' =>
          rcases ih o (by omega) _ h' with h | ⟨rfl, rfl⟩
          · exact .inl (.right h)
          · exact .inr ⟨by simp [Huffman.Spec.natToBits, htb], rfl⟩
      | leaf s' =>
        simp only [Zip.Native.HuffTree.insert.go] at h
        exact .inl h

/-! ### Connecting fromLengths to allCodes -/

/-- When `fromLengths` succeeds, the tree is `fromLengthsTree`. -/
private theorem fromLengths_ok_eq (lengths : Array UInt8) (maxBits : Nat)
    (tree : Zip.Native.HuffTree)
    (htree : Zip.Native.HuffTree.fromLengths lengths maxBits = .ok tree) :
    tree = Zip.Native.HuffTree.fromLengthsTree lengths maxBits := by
  simp only [Zip.Native.HuffTree.fromLengths] at htree
  split at htree
  · simp at htree
  · split at htree
    · simp at htree
    · exact (Except.ok.inj htree).symm

/-- The count of elements equal to `b` in a prefix is at most the count in the full list. -/
theorem count_foldl_take_le (ls : List Nat) (b : Nat) (k : Nat) :
    (ls.take k).foldl (fun acc l => if (l == b) = true then acc + 1 else acc) 0 ≤
    ls.foldl (fun acc l => if (l == b) = true then acc + 1 else acc) 0 := by
  rw [show ls.foldl (fun acc l => if (l == b) = true then acc + 1 else acc) 0 =
    (ls.drop k).foldl (fun acc l => if (l == b) = true then acc + 1 else acc)
      ((ls.take k).foldl (fun acc l => if (l == b) = true then acc + 1 else acc) 0)
    from by rw [← List.foldl_append, List.take_append_drop]]
  exact Huffman.Spec.count_foldl_mono _ _ _


/-- `codeFor` returns `some` for symbols with valid nonzero length. -/
theorem codeFor_some (lsList : List Nat) (maxBits : Nat) (s : Nat)
    (hs : s < lsList.length) (hlen : lsList[s] ≠ 0) (hle : lsList[s] ≤ maxBits) :
    ∃ cw, Huffman.Spec.codeFor lsList maxBits s = some cw := by
  simp only [Huffman.Spec.codeFor, show s < lsList.length from hs, ↓reduceDIte]
  simp only [show (lsList[s] == 0 || decide (lsList[s] > maxBits)) = false from by
    simp [hlen]; omega]
  exact ⟨_, rfl⟩

/-- NC invariant update: after incrementing `nextCode[len]`, the NC invariant
    holds at `start + 1`. Shared by `insertLoop_forward` and `insertLoop_backward`. -/
private theorem nc_invariant_step
    (lengths : Array UInt8) (nextCode : Array UInt32) (start : Nat)
    (lsList : List Nat) (maxBits : Nat)
    (blCount : Array Nat) (hblCount : blCount = Huffman.Spec.countLengths lsList maxBits)
    (ncSpec : Array Nat) (hncSpec : ncSpec = Huffman.Spec.nextCodes blCount maxBits)
    (hv : Huffman.Spec.ValidLengths lsList maxBits) (hmb : maxBits < 32)
    (hncSize : nextCode.size ≥ maxBits + 1)
    (hstart : start < lengths.size)
    (hls_len : start < lsList.length)
    (hls_start : lsList[start] = lengths[start].toNat)
    (hlen_le : lengths[start].toNat ≤ maxBits)
    (hlen_pos_nat : 0 < lengths[start].toNat)
    (hnc : ∀ b, 1 ≤ b → b ≤ maxBits →
      nextCode[b]!.toNat = ncSpec[b]! +
        (lsList.take start).foldl (fun acc l => if l == b then acc + 1 else acc) 0)
    (b : Nat) (hb1 : 1 ≤ b) (hb15 : b ≤ maxBits) :
    (nextCode.set! lengths[start].toNat (nextCode[lengths[start].toNat]! + 1))[b]!.toNat =
      ncSpec[b]! +
        (lsList.take (start + 1)).foldl (fun acc l => if l == b then acc + 1 else acc) 0 := by
  rw [List.take_add_one]
  simp only [List.getElem?_eq_getElem hls_len, Option.toList,
             List.foldl_append, List.foldl_cons, List.foldl_nil, hls_start]
  by_cases hbeq : lengths[start].toNat = b
  · subst hbeq
    simp only [if_pos (beq_self_eq_true lengths[start].toNat)]
    rw [Array.getElem!_set!_self _ _ _ (by omega : lengths[start].toNat < nextCode.size)]
    have h_nc_val := hnc lengths[start].toNat (by omega) hlen_le
    have h_partial_le := count_foldl_take_le lsList lengths[start].toNat start
    have h_npc := Huffman.Spec.nextCodes_plus_count_le lsList maxBits
      lengths[start].toNat hv (by omega) hlen_le
    rw [← hblCount, ← hncSpec] at h_npc
    have h_pow := Nat.pow_le_pow_right (by omega : 0 < 2) (show lengths[start].toNat ≤ 31 from by omega)
    rw [UInt32.toNat_add, show (1 : UInt32).toNat = 1 from rfl,
        Nat.mod_eq_of_lt (by omega), h_nc_val]
    omega
  · have hf : ¬((lengths[start].toNat == b) = true) := by rw [beq_iff_eq]; exact hbeq
    simp only [if_neg hf]
    rw [Array.getElem!_set!_ne _ _ _ _ hbeq]
    exact hnc b hb1 hb15

/-- The tree produced by `insertLoop` has a leaf for every symbol with nonzero length,
    at the codeword given by `codeFor`. Proved by well-founded induction on `lengths.size - start`,
    maintaining the NC invariant, forward invariant, and NoLeafOnPath invariant. -/
private theorem insertLoop_forward
    (lengths : Array UInt8) (nextCode : Array UInt32)
    (start : Nat) (tree : Zip.Native.HuffTree)
    (lsList : List Nat) (hlsList : lsList = lengths.toList.map UInt8.toNat)
    (maxBits : Nat) (hmb : maxBits < 32)
    (blCount : Array Nat) (hblCount : blCount = Huffman.Spec.countLengths lsList maxBits)
    (ncSpec : Array Nat) (hncSpec : ncSpec = Huffman.Spec.nextCodes blCount maxBits)
    (hv : Huffman.Spec.ValidLengths lsList maxBits)
    (hncSize : nextCode.size ≥ maxBits + 1)
    -- NC invariant: nextCode tracks ncSpec + partial offset
    (hnc : ∀ b, 1 ≤ b → b ≤ maxBits →
      nextCode[b]!.toNat = ncSpec[b]! +
        (lsList.take start).foldl (fun acc l => if l == b then acc + 1 else acc) 0)
    -- Forward: tree has leaves for all k < start
    (hprev : ∀ k, k < start → (hk : k < lengths.size) → lengths[k] > 0 →
      ∀ cw, Huffman.Spec.codeFor lsList maxBits k = some cw →
        TreeHasLeaf tree cw k.toUInt16)
    -- NoLeafOnPath for all future codes
    (hnlop : ∀ k, start ≤ k → (hk : k < lengths.size) → lengths[k] > 0 →
      ∀ cw, Huffman.Spec.codeFor lsList maxBits k = some cw →
        NoLeafOnPath tree cw)
    -- Target symbol
    (j : Nat) (hjs : j < lengths.size) (hjlen : lengths[j] > 0)
    (cw : Huffman.Spec.Codeword) (hcf : Huffman.Spec.codeFor lsList maxBits j = some cw) :
    TreeHasLeaf (Zip.Native.HuffTree.insertLoop lengths nextCode start tree).1 cw j.toUInt16 := by
  unfold Zip.Native.HuffTree.insertLoop
  split
  · -- start < lengths.size
    rename_i hstart
    dsimp only []
    split
    · -- lengths[start] > 0: insert + recurse
      rename_i hlen_pos
      -- Common facts for insert case
      have hls_len : start < lsList.length := by simp [hlsList, hstart]
      have hls_start : lsList[start] = lengths[start].toNat := by
        simp only [hlsList, List.getElem_map, Array.getElem_toList]
      have hlen_le : lengths[start].toNat ≤ maxBits := by
        rw [← hls_start]; exact hv.1 _ (List.getElem_mem hls_len)
      have hlen_pos_nat : 0 < lengths[start].toNat := hlen_pos
      -- The codeword for symbol `start` matches the insert path
      obtain ⟨cw_s, hcf_s⟩ := codeFor_some lsList maxBits start hls_len
        (by rw [hls_start]; omega) (by rw [hls_start]; omega)
      have hcw_s : cw_s = Huffman.Spec.natToBits
          (nextCode[lengths[start].toNat]!).toNat lengths[start].toNat := by
        obtain ⟨_, _, hcw⟩ := Huffman.Spec.codeFor_spec hcf_s
        rw [hcw, hls_start]; congr 1
        rw [← hblCount, ← hncSpec]
        exact (hnc lengths[start].toNat (by omega) hlen_le).symm
      -- Prefix-freeness: insert path is not prefix of any other codeword
      have hpf : ∀ k, k ≠ start → ∀ cw', Huffman.Spec.codeFor lsList maxBits k = some cw' →
          ¬(Huffman.Spec.natToBits (nextCode[lengths[start].toNat]!).toNat
            lengths[start].toNat).IsPrefix cw' := by
        intro k hne cw' hcf_k
        have hcf_s' := hcw_s ▸ hcf_s
        exact Huffman.Spec.canonical_prefix_free lsList maxBits hv start k _ cw'
          hcf_s' hcf_k (by omega)
      exact insertLoop_forward lengths
        (nextCode.set! lengths[start].toNat (nextCode[lengths[start].toNat]! + 1))
        (start + 1)
        (tree.insert (nextCode[lengths[start].toNat]!) lengths[start].toNat start.toUInt16)
        lsList hlsList maxBits hmb blCount hblCount ncSpec hncSpec hv
        (by -- hncSize': set! preserves array size
          simp [Array.set!_eq_setIfInBounds, Array.setIfInBounds]
          split <;> simp_all)
        (nc_invariant_step lengths nextCode start lsList maxBits blCount hblCount
          ncSpec hncSpec hv hmb hncSize hstart hls_len hls_start hlen_le hlen_pos_nat hnc)
        (by -- hprev': forward invariant after insertion
          intro k hk hks hklen cw' hcf'
          by_cases hk_eq : k = start
          · -- k = start: newly inserted leaf
            have hcf_start : Huffman.Spec.codeFor lsList maxBits start = some cw' := by
              rw [← hk_eq]; exact hcf'
            have hcw_eq : cw_s = cw' := Option.some.inj (hcf_s.symm.trans hcf_start)
            subst hcw_eq; rw [hcw_s, hk_eq]
            have h_nlop : NoLeafOnPath tree cw_s :=
              hnlop start Nat.le.refl hstart hlen_pos cw_s hcf_s
            rw [hcw_s] at h_nlop
            exact insert_go_hasLeaf _ _ _ _ (by omega) h_nlop
          · -- k < start: leaf preserved by insert
            exact insert_go_preserves _ _ _ _ (by omega) cw' k.toUInt16
              (hprev k (by omega) hks hklen cw' hcf')
              (hpf k hk_eq cw' hcf'))
        (by -- hnlop': NoLeafOnPath preserved after insert
          intro k hk hks hklen cw' hcf'
          exact insert_go_noLeafOnPath _ _ _ _ (by omega) cw'
            (hnlop k (by omega) hks hklen cw' hcf')
            (hpf k (by omega) cw' hcf'))
        j hjs hjlen cw hcf
    · -- ¬(lengths[start] > 0): skip, recurse with same tree/nextCode
      rename_i hlen_zero
      have hls_len : start < lsList.length := by simp [hlsList, hstart]
      have hls_val : lsList[start] = 0 := by
        have : ¬(0 < lengths[start].toNat) := fun hp => hlen_zero hp
        simp [hlsList]; omega
      exact insertLoop_forward lengths nextCode (start + 1) tree
        lsList hlsList maxBits hmb blCount hblCount ncSpec hncSpec hv hncSize
        (by -- NC: lsList[start] = 0 doesn't change count for any b ≥ 1
          intro b hb1 hb15
          rw [hnc b hb1 hb15]; congr 1
          rw [List.take_add_one]
          simp [List.getElem?_eq_getElem hls_len, hls_val, List.foldl_append]
          omega)
        (by intro k hk hks hklen cw' hcf'
            have : k < start := by
              by_cases h : k = start
              · subst h; exact absurd hklen hlen_zero
              · omega
            exact hprev k this hks hklen cw' hcf')
        (by intro k hk hks hklen cw' hcf'; exact hnlop k (by omega) hks hklen cw' hcf')
        j hjs hjlen cw hcf
  · exact hprev j (by omega) hjs hjlen cw hcf
termination_by lengths.size - start

/-- Backward direction of `insertLoop_forward`: every leaf in the tree
    after `insertLoop` was either pre-existing or corresponds to a symbol
    with nonzero code length that was inserted during the loop. -/
private theorem insertLoop_backward
    (lengths : Array UInt8) (nextCode : Array UInt32)
    (start : Nat) (tree : Zip.Native.HuffTree)
    (lsList : List Nat) (hlsList : lsList = lengths.toList.map UInt8.toNat)
    (maxBits : Nat) (hmb : maxBits < 32)
    (blCount : Array Nat) (hblCount : blCount = Huffman.Spec.countLengths lsList maxBits)
    (ncSpec : Array Nat) (hncSpec : ncSpec = Huffman.Spec.nextCodes blCount maxBits)
    (hv : Huffman.Spec.ValidLengths lsList maxBits)
    (hncSize : nextCode.size ≥ maxBits + 1)
    (hnc : ∀ b, 1 ≤ b → b ≤ maxBits →
      nextCode[b]!.toNat = ncSpec[b]! +
        (lsList.take start).foldl (fun acc l => if l == b then acc + 1 else acc) 0)
    (cw : List Bool) (sym : UInt16)
    (h : TreeHasLeaf (Zip.Native.HuffTree.insertLoop lengths nextCode start tree).1 cw sym) :
    TreeHasLeaf tree cw sym ∨
    ∃ k, start ≤ k ∧ k < lsList.length ∧
      sym = k.toUInt16 ∧ Huffman.Spec.codeFor lsList maxBits k = some cw := by
  unfold Zip.Native.HuffTree.insertLoop at h
  split at h
  · -- start < lengths.size
    rename_i hstart
    dsimp only [] at h
    split at h
    · -- lengths[start] > 0: insert case
      rename_i hlen_pos
      have hls_len : start < lsList.length := by simp [hlsList, hstart]
      have hls_start : lsList[start] = lengths[start].toNat := by
        simp only [hlsList, List.getElem_map, Array.getElem_toList]
      have hlen_le : lengths[start].toNat ≤ maxBits := by
        rw [← hls_start]; exact hv.1 _ (List.getElem_mem hls_len)
      have hlen_pos_nat : 0 < lengths[start].toNat := hlen_pos
      -- The codeword for symbol `start`
      obtain ⟨cw_s, hcf_s⟩ := codeFor_some lsList maxBits start hls_len
        (by rw [hls_start]; omega) (by rw [hls_start]; omega)
      have hcw_s : cw_s = Huffman.Spec.natToBits
          (nextCode[lengths[start].toNat]!).toNat lengths[start].toNat := by
        obtain ⟨_, _, hcw⟩ := Huffman.Spec.codeFor_spec hcf_s
        rw [hcw, hls_start]; congr 1
        rw [← hblCount, ← hncSpec]
        exact (hnc lengths[start].toNat (by omega) hlen_le).symm
      -- Apply IH to the recursive call
      have ih := insertLoop_backward lengths
        (nextCode.set! lengths[start].toNat (nextCode[lengths[start].toNat]! + 1))
        (start + 1)
        (tree.insert (nextCode[lengths[start].toNat]!) lengths[start].toNat start.toUInt16)
        lsList hlsList maxBits hmb blCount hblCount ncSpec hncSpec hv
        (by simp [Array.set!_eq_setIfInBounds, Array.setIfInBounds]; split <;> simp_all)
        (nc_invariant_step lengths nextCode start lsList maxBits blCount hblCount
          ncSpec hncSpec hv hmb hncSize hstart hls_len hls_start hlen_le hlen_pos_nat hnc)
        cw sym h
      cases ih with
      | inl h_in_insert =>
        -- Leaf was in tree.insert: apply insert_go_complete'
        have ih2 := insert_go_complete' _ _ tree _ (by omega) cw sym h_in_insert
        cases ih2 with
        | inl h_in_tree => exact .inl h_in_tree
        | inr h_eq =>
          obtain ⟨hcw_eq, hsym_eq⟩ := h_eq
          exact .inr ⟨start, Nat.le.refl, hls_len, hsym_eq,
            by rw [hcw_eq, ← hcw_s]; exact hcf_s⟩
      | inr h_exists =>
        obtain ⟨k, hk_ge, hk_lt, hk_sym, hk_cf⟩ := h_exists
        exact .inr ⟨k, by omega, hk_lt, hk_sym, hk_cf⟩
    · -- lengths[start] = 0: skip case
      rename_i hlen_zero
      have hls_len : start < lsList.length := by simp [hlsList, hstart]
      have hls_val : lsList[start] = 0 := by
        have : ¬(0 < lengths[start].toNat) := fun hp => hlen_zero hp
        simp [hlsList]; omega
      have ih := insertLoop_backward lengths nextCode (start + 1) tree
        lsList hlsList maxBits hmb blCount hblCount ncSpec hncSpec hv hncSize
        (by intro b hb1 hb15; rw [hnc b hb1 hb15]; congr 1
            rw [List.take_add_one]
            simp [List.getElem?_eq_getElem hls_len, hls_val, List.foldl_append]; omega)
        cw sym h
      cases ih with
      | inl h_pre => exact .inl h_pre
      | inr h_exists =>
        obtain ⟨k, hk_ge, hk_lt, hk_sym, hk_cf⟩ := h_exists
        exact .inr ⟨k, by omega, hk_lt, hk_sym, hk_cf⟩
  · -- start ≥ lengths.size: base case (insertLoop returns tree unchanged)
    exact .inl h
termination_by lengths.size - start

/-- If `decode table bits = some (sym, rest)`, then there exists a matching
    codeword entry in the table with `bits = cw ++ rest`. -/
protected theorem decode_some_mem {α : Type} (table : List (Huffman.Spec.Codeword × α))
    (bits : List Bool) (sym : α) (rest : List Bool)
    (h : Huffman.Spec.decode table bits = some (sym, rest)) :
    ∃ cw, (cw, sym) ∈ table ∧ bits = cw ++ rest := by
  induction table with
  | nil => simp [Huffman.Spec.decode] at h
  | cons entry entries ih =>
    obtain ⟨cw', sym'⟩ := entry
    simp only [Huffman.Spec.decode] at h
    split at h
    · -- isPrefixOf true: match found
      rename_i hpre
      obtain ⟨rfl, rfl⟩ := Option.some.inj h
      rw [Huffman.Spec.isPrefixOf_iff] at hpre
      obtain ⟨t, rfl⟩ := hpre
      exact ⟨cw', List.mem_cons_self .., by simp⟩
    · -- isPrefixOf false: recurse
      obtain ⟨cw, hmem, hbits⟩ := ih h
      exact ⟨cw, List.mem_cons_of_mem _ hmem, hbits⟩

/-- The initial `nextCode` array (`ncSpec.map (·.toUInt32)`) satisfies the NC
    invariant at `start = 0`: each entry's `toNat` equals the spec value.
    Shared by `fromLengths_hasLeaf` and `fromLengths_leaf_spec`. -/
private theorem initial_nc_invariant (lengths : Array UInt8)
    (maxBits : Nat) (hmb : maxBits < 32)
    (hv : Huffman.Spec.ValidLengths (lengths.toList.map UInt8.toNat) maxBits)
    (b : Nat) (hb1 : 1 ≤ b) (hb15 : b ≤ maxBits) :
    ((Huffman.Spec.nextCodes (Huffman.Spec.countLengths
        (lengths.toList.map UInt8.toNat) maxBits) maxBits).map
      Nat.toUInt32)[b]!.toNat =
    (Huffman.Spec.nextCodes (Huffman.Spec.countLengths
        (lengths.toList.map UInt8.toNat) maxBits) maxBits)[b]! := by
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
             Array.getElem?_map]
  have hbs : b < (Huffman.Spec.nextCodes (Huffman.Spec.countLengths
      (List.map UInt8.toNat lengths.toList) maxBits) maxBits).size := by
    rw [Huffman.Spec.nextCodes_size]; omega
  simp only [Array.getElem?_eq_getElem hbs, Option.map_some, Option.getD_some]
  have h_npc := Huffman.Spec.nextCodes_plus_count_le
    (List.map UInt8.toNat lengths.toList) maxBits b hv (by omega) hb15
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
             Array.getElem?_eq_getElem hbs, Option.getD_some] at h_npc
  -- Bound 2^b ≤ 2^31 needed by omega to prove value fits in UInt32
  have h_pow := Nat.pow_le_pow_right (by omega : 0 < 2) (show b ≤ 31 from by omega)
  show (Huffman.Spec.nextCodes _ maxBits)[b].toUInt32.toNat =
       (Huffman.Spec.nextCodes _ maxBits)[b]
  rw [show ∀ n : Nat, n.toUInt32.toNat = n % 2 ^ 32 from fun _ => rfl,
      Nat.mod_eq_of_lt (by omega)]

/-- The tree built by `fromLengths` has a leaf for every canonical codeword.
    Requires `ValidLengths` to ensure no collisions during insertion. -/
protected theorem fromLengths_hasLeaf (lengths : Array UInt8)
    (maxBits : Nat) (hmb : maxBits < 32)
    (tree : Zip.Native.HuffTree)
    (htree : Zip.Native.HuffTree.fromLengths lengths maxBits = .ok tree)
    (hv : Huffman.Spec.ValidLengths (lengths.toList.map UInt8.toNat) maxBits)
    (s : Nat) (cw : Huffman.Spec.Codeword)
    (hmem : (s, cw) ∈ Huffman.Spec.allCodes (lengths.toList.map UInt8.toNat) maxBits) :
    TreeHasLeaf tree cw s.toUInt16 := by
  -- Extract facts from allCodes membership
  rw [Huffman.Spec.allCodes_mem_iff] at hmem
  obtain ⟨hs_len, hcf⟩ := hmem
  -- Get lengths[s] > 0 from codeFor returning some
  obtain ⟨_, hlen_cond, _⟩ := Huffman.Spec.codeFor_spec hcf
  have ⟨hlen_ne, _⟩ := Huffman.Spec.codeFor_len_bounds hlen_cond
  have hs : s < lengths.size := by simp at hs_len; omega
  have hjlen : lengths[s] > 0 := by
    have : (lengths.toList.map UInt8.toNat)[s] ≠ 0 := hlen_ne
    simp [List.getElem_map, Array.getElem_toList] at this
    exact Nat.pos_of_ne_zero this
  -- Rewrite tree to fromLengthsTree = (insertLoop ...).1
  rw [fromLengths_ok_eq lengths maxBits tree htree]
  -- fromLengthsTree unfolds to insertLoop with spec-derived nextCode
  show TreeHasLeaf (Zip.Native.HuffTree.fromLengthsTree lengths maxBits) cw s.toUInt16
  unfold Zip.Native.HuffTree.fromLengthsTree
  dsimp only []
  -- Apply insertLoop_forward with start = 0
  exact insertLoop_forward lengths _ 0 .empty _ rfl maxBits hmb _ rfl _ rfl hv
    (by -- hncSize: nextCode.size ≥ maxBits + 1
      simp [Array.size_map, Huffman.Spec.nextCodes_size])
    (by -- hnc: initial NC invariant
      intro b hb1 hb15
      simp only [List.take_zero, List.foldl_nil, Nat.add_zero]
      exact initial_nc_invariant lengths maxBits hmb hv b hb1 hb15)
    (by intro k hk; omega) -- hprev: vacuously true (start = 0)
    (by intro k _ _ _ cw' _; cases cw' <;> trivial) -- hnlop: empty tree
    s hs hjlen cw hcf

/-- Every leaf in the tree built by `fromLengths` corresponds to an entry
    in `allCodes`. -/
protected theorem fromLengths_leaf_spec (lengths : Array UInt8)
    (maxBits : Nat) (hmb : maxBits < 32)
    (tree : Zip.Native.HuffTree)
    (htree : Zip.Native.HuffTree.fromLengths lengths maxBits = .ok tree)
    (hv : Huffman.Spec.ValidLengths (lengths.toList.map UInt8.toNat) maxBits)
    (hlen_bound : lengths.size ≤ UInt16.size)
    (cw : List Bool) (sym : UInt16)
    (h : TreeHasLeaf tree cw sym) :
    (sym.toNat, cw) ∈ Huffman.Spec.allCodes (lengths.toList.map UInt8.toNat) maxBits := by
  rw [fromLengths_ok_eq lengths maxBits tree htree] at h
  unfold Zip.Native.HuffTree.fromLengthsTree at h
  dsimp only [] at h
  have ih := insertLoop_backward lengths _ 0 .empty _ rfl maxBits hmb _ rfl _ rfl hv
    (by simp [Array.size_map, Huffman.Spec.nextCodes_size])
    (by -- hnc: initial NC invariant
      intro b hb1 hb15
      simp only [List.take_zero, List.foldl_nil, Nat.add_zero]
      exact initial_nc_invariant lengths maxBits hmb hv b hb1 hb15)
    cw sym h
  cases ih with
  | inl h_empty => cases h_empty
  | inr h_exists =>
    obtain ⟨k, _, hk_len, rfl, hcf⟩ := h_exists
    have hk_small : k < UInt16.size := by simp at hk_len; omega
    have hk_toNat : k.toUInt16.toNat = k :=
      Nat.mod_eq_of_lt hk_small
    rw [Huffman.Spec.allCodes_mem_iff]
    exact ⟨by rw [hk_toNat]; exact hk_len, by rw [hk_toNat]; exact hcf⟩

end Deflate.Correctness
