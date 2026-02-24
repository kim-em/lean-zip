import Zip.Spec.BitstreamCorrect
import Zip.Spec.BitstreamComplete

/-!
# Huffman Tree Primitives

Core definitions and proofs for Huffman tree correctness:
- `decodeBits`: pure tree decode on bit lists
- `decode_go_decodeBits`: BitReader decode ↔ `decodeBits` correspondence
- `TreeHasLeaf`: inductive predicate for tree-path-symbol relationships
- `insert.go` correctness: `insert_go_hasLeaf`, `insert_go_preserves`,
  `insert_go_noLeafOnPath`, `insert_go_complete'`

The `fromLengths` loop invariants and main theorems are in `HuffmanCorrectLoop`.
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
def NoLeafOnPath : Zip.Native.HuffTree → List Bool → Prop
  | .leaf _, _ :: _ => False
  | .node z _, false :: rest => NoLeafOnPath z rest
  | .node _ o, true :: rest => NoLeafOnPath o rest
  | _, _ => True

/-- `insert.go` places a leaf at the path `natToBits code.toNat len` in the tree,
    provided no existing leaf blocks the path. -/
theorem insert_go_hasLeaf (code : UInt32) (sym : UInt16)
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
theorem insert_go_preserves (code : UInt32) (sym : UInt16)
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
theorem insert_go_noLeafOnPath (code : UInt32) (sym : UInt16)
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
theorem insert_go_complete' (code : UInt32) (sym : UInt16)
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

end Deflate.Correctness
