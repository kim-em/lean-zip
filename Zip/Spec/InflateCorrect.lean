import Zip.Spec.Deflate
import Zip.Native.Inflate
import ZipForStd.Nat

/-!
# DEFLATE Decompressor Correctness

States the main correctness theorem: the native pure-Lean DEFLATE
decompressor (`Zip.Native.Inflate.inflateRaw`) agrees with the formal
bitstream specification (`Deflate.Spec.decode`).

The proof is decomposed into layers matching the decode pipeline:
1. **Bitstream layer**: `BitReader` operations correspond to `bytesToBits` + `readBitsLSB`
2. **Huffman layer**: `HuffTree.decode` corresponds to `Huffman.Spec.decode`
3. **LZ77 layer**: the native copy loop corresponds to `resolveLZ77`
4. **Block layer**: each block type decodes identically
5. **Stream layer**: the block sequence produces the same output
-/

/-! ## Bitstream correspondence

A `BitReader` at position `(pos, bitOff)` in a `ByteArray` corresponds
to the bit list `(bytesToBits data).drop (pos * 8 + bitOff)`.
-/

/-- The spec-level bit list corresponding to a `BitReader`'s current position. -/
def Zip.Native.BitReader.toBits (br : Zip.Native.BitReader) : List Bool :=
  (Deflate.Spec.bytesToBits br.data).drop (br.pos * 8 + br.bitOff)

namespace Deflate.Correctness

/-! ### Helper lemmas for flatMap with uniform-length functions -/

/-- Dropping `n * k` elements from a flatMap with uniform-length-`k` outputs
    skips exactly `n` segments. -/
private theorem flatMap_drop_mul {α β : Type} (l : List α) (f : α → List β)
    (k n : Nat) (hk : ∀ a ∈ l, (f a).length = k) :
    (l.flatMap f).drop (n * k) = (l.drop n).flatMap f := by
  induction n generalizing l with
  | zero => simp
  | succ m ih =>
    cases l with
    | nil => simp
    | cons a rest =>
      simp only [List.flatMap_cons, List.drop_succ_cons]
      have hlen := hk a (List.mem_cons_self ..)
      have hk_eq : (m + 1) * k = (f a).length + m * k := by
        rw [Nat.succ_mul, hlen, Nat.add_comm]
      rw [hk_eq, ← List.drop_drop, List.drop_left]
      exact ih rest (fun b hb => hk b (List.mem_cons_of_mem _ hb))

/-- Dropping within the first segment of a flatMap. -/
private theorem flatMap_cons_drop {α β : Type} (a : α) (rest : List α)
    (f : α → List β) (off : Nat) (hoff : off ≤ (f a).length) :
    ((a :: rest).flatMap f).drop off = (f a).drop off ++ rest.flatMap f :=
  List.drop_append_of_le_length hoff

/-- Dropping `off` elements from `List.ofFn (n := n) f` gives a list
    headed by `f ⟨off, _⟩` when `off < n`. -/
private theorem ofFn_drop_head {n : Nat} {f : Fin n → β} {off : Nat}
    (hoff : off < n) :
    ∃ rest, (List.ofFn f).drop off = f ⟨off, hoff⟩ :: rest := by
  have hlen : off < (List.ofFn f).length := by simp; exact hoff
  rw [List.drop_eq_getElem_cons hlen, List.getElem_ofFn]
  exact ⟨_, rfl⟩

/-- `byteToBits` dropped by `off < 8` starts with `testBit off`. -/
private theorem byteToBits_drop_head (b : UInt8) (off : Nat) (hoff : off < 8) :
    ∃ rest, (Deflate.Spec.bytesToBits.byteToBits b).drop off =
      b.toNat.testBit off :: rest := by
  exact ofFn_drop_head hoff

/-- The key structural lemma: `bytesToBits data` dropped by `pos * 8 + off`
    starts with `data[pos].toNat.testBit off`. -/
private theorem bytesToBits_drop_testBit (data : ByteArray) (pos off : Nat)
    (hpos : pos < data.size) (hoff : off < 8) :
    ∃ rest, (Deflate.Spec.bytesToBits data).drop (pos * 8 + off) =
      data[pos].toNat.testBit off :: rest := by
  simp only [Deflate.Spec.bytesToBits]
  -- Step 1: split drop (pos * 8 + off) into drop off ∘ drop (pos * 8)
  rw [← List.drop_drop]
  -- Step 2: drop (pos * 8) skips pos complete 8-bit segments
  rw [flatMap_drop_mul data.data.toList _ 8 pos
    (fun b _ => Deflate.Spec.bytesToBits.byteToBits_length b)]
  -- Step 3: data.data.toList.drop pos = data[pos] :: tail
  have hlen : pos < data.data.toList.length := by
    rw [Array.length_toList]; exact hpos
  rw [List.drop_eq_getElem_cons hlen]
  -- Step 4: drop off within first segment
  rw [flatMap_cons_drop _ _ _ off
    (by rw [Deflate.Spec.bytesToBits.byteToBits_length]; omega)]
  -- Step 5: head of (byteToBits data[pos]).drop off is testBit off
  have heq : data.data.toList[pos] = data[pos] := by
    simp [Array.getElem_toList]; rfl
  obtain ⟨tail, htail⟩ := byteToBits_drop_head (data.data.toList[pos]) off hoff
  rw [htail, heq]; exact ⟨_, rfl⟩

/-! ### Bit-value correspondence -/

private theorem shift_and_one_eq_testBit (n i : Nat) :
    (n >>> i) &&& 1 = if n.testBit i then 1 else 0 := by
  simp only [Nat.testBit, Nat.and_comm (n >>> i) 1, Nat.one_and_eq_mod_two, bne_iff_ne]
  split <;> omega

/-- The bit extracted at position `n` from a UInt32 corresponds to `testBit`. -/
private theorem uint32_testBit (code : UInt32) (n : Nat) (hn : n < 32) :
    ((code >>> n.toUInt32) &&& 1) =
      if code.toNat.testBit n then 1 else 0 := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_and, UInt32.toNat_shiftRight]
  have hn_eq : n.toUInt32.toNat % 32 = n := by simp [Nat.toUInt32]; omega
  rw [hn_eq, UInt32.toNat_one, shift_and_one_eq_testBit]
  split <;> simp

/-- `uint32_testBit` specialized to UInt8 input. -/
private theorem uint32_bit_eq_testBit (byte : UInt8) (off : Nat) (hoff : off < 8) :
    ((byte.toUInt32 >>> off.toUInt32) &&& 1) =
      if byte.toNat.testBit off then 1 else 0 := by
  have := uint32_testBit byte.toUInt32 off (by omega)
  rwa [UInt8.toNat_toUInt32] at this

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

private theorem list_drop_cons_tail {l : List α} {a : α} {rest : List α} {n : Nat}
    (h : l.drop n = a :: rest) : rest = l.drop (n + 1) := by
  have : l.drop (n + 1) = (l.drop n).drop 1 := by rw [List.drop_drop, Nat.add_comm]
  rw [this, h, List.drop_one, List.tail_cons]

/-- `readBit` preserves the well-formedness invariant `bitOff < 8`. -/
theorem readBit_wf (br : Zip.Native.BitReader) (bit : UInt32)
    (br' : Zip.Native.BitReader) (hwf : br.bitOff < 8)
    (h : br.readBit = .ok (bit, br')) : br'.bitOff < 8 := by
  simp only [Zip.Native.BitReader.readBit] at h
  split at h
  · simp at h
  · split at h <;> simp only [Except.ok.injEq, Prod.mk.injEq] at h
    · obtain ⟨_, rfl⟩ := h; simp
    · obtain ⟨_, rfl⟩ := h; simp; omega

/-! ### readBit correspondence -/

/-- Reading a single bit from the `BitReader` corresponds to consuming
    the head of the corresponding bit list. Requires `bitOff < 8`. -/
theorem readBit_toBits (br : Zip.Native.BitReader)
    (bit : UInt32) (br' : Zip.Native.BitReader)
    (hwf : br.bitOff < 8)
    (h : br.readBit = .ok (bit, br')) :
    ∃ b rest,
      br.toBits = b :: rest ∧
      br'.toBits = rest ∧
      bit = if b then 1 else 0 := by
  -- Unfold readBit; the error case is impossible since h says it succeeded
  simp only [Zip.Native.BitReader.readBit] at h
  split at h
  · simp at h
  · rename_i hpos
    -- hpos : ¬(br.pos ≥ br.data.size), so br.pos < br.data.size
    have hpos' : br.pos < br.data.size := by omega
    -- Get the bit list structure from bytesToBits_drop_testBit
    obtain ⟨rest, hrest⟩ := bytesToBits_drop_testBit br.data br.pos br.bitOff hpos' hwf
    have hrest_eq : rest =
        (Deflate.Spec.bytesToBits br.data).drop (br.pos * 8 + br.bitOff + 1) :=
      list_drop_cons_tail hrest
    -- The bit read by readBit matches data[pos]! which equals data[pos]
    have hget : br.data[br.pos]! = br.data[br.pos] := by simp [hpos']
    refine ⟨br.data[br.pos].toNat.testBit br.bitOff, rest, hrest, ?_, ?_⟩
    · -- br'.toBits = rest
      split at h <;> simp only [Except.ok.injEq, Prod.mk.injEq] at h
      · obtain ⟨_, rfl⟩ := h
        simp only [Zip.Native.BitReader.toBits, hrest_eq]; congr 1; omega
      · obtain ⟨_, rfl⟩ := h
        simp only [Zip.Native.BitReader.toBits, hrest_eq]; congr 1
    · -- bit = if testBit then 1 else 0 (same in both bitOff cases)
      split at h <;> simp only [Except.ok.injEq, Prod.mk.injEq] at h
      all_goals (obtain ⟨rfl, _⟩ := h; rw [hget];
                 exact uint32_bit_eq_testBit br.data[br.pos] br.bitOff hwf)

/-! ### UInt32 accumulator arithmetic

Helper lemmas for the `readBits.go` loop invariant. The loop accumulates
bits via `acc ||| (bit <<< shift.toUInt32)`. When the bits don't overlap
(ensured by `acc.toNat < 2^shift`), this OR equals addition. -/

private theorem shift_toUInt32_mod32 {shift : Nat} (hshift : shift < 32) :
    shift.toUInt32.toNat % 32 = shift := by
  simp [Nat.toUInt32]; omega

private theorem acc_or_shift_toNat (acc bit : UInt32) (shift : Nat)
    (hacc : acc.toNat < 2 ^ shift) (hbit : bit = 0 ∨ bit = 1) (hshift : shift < 32) :
    (acc ||| (bit <<< shift.toUInt32)).toNat = acc.toNat + bit.toNat * 2 ^ shift := by
  rcases hbit with rfl | rfl
  · simp [UInt32.toNat_zero]
  · rw [UInt32.toNat_or, UInt32.toNat_shiftLeft, shift_toUInt32_mod32 hshift,
        UInt32.toNat_one, Nat.shiftLeft_eq, Nat.one_mul,
        Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) hshift),
        Nat.or_two_pow_eq_add hacc]

private theorem acc_or_shift_bound (acc bit : UInt32) (shift : Nat)
    (hacc : acc.toNat < 2 ^ shift) (hbit : bit = 0 ∨ bit = 1) (hshift : shift < 32) :
    (acc ||| (bit <<< shift.toUInt32)).toNat < 2 ^ (shift + 1) := by
  rw [acc_or_shift_toNat acc bit shift hacc hbit hshift, Nat.pow_succ]
  rcases hbit with rfl | rfl <;> simp <;> omega

/-! ### Generalized readBits.go invariant -/

/-- Generalized loop invariant for `readBits.go`: the spec-level
    `readBitsLSB k` on the corresponding bit list produces a value `specVal`
    such that `val.toNat = acc.toNat + specVal * 2^shift`. -/
private theorem readBits_go_spec (br : Zip.Native.BitReader) (acc : UInt32)
    (shift k : Nat) (val : UInt32) (br' : Zip.Native.BitReader)
    (hwf : br.bitOff < 8) (hsk : shift + k ≤ 32) (hacc : acc.toNat < 2 ^ shift)
    (h : Zip.Native.BitReader.readBits.go br acc shift k = .ok (val, br')) :
    ∃ specVal rest,
      Deflate.Spec.readBitsLSB k br.toBits = some (specVal, rest) ∧
      br'.toBits = rest ∧
      val.toNat = acc.toNat + specVal * 2 ^ shift ∧
      br'.bitOff < 8 := by
  induction k generalizing br acc shift with
  | zero =>
    simp only [Zip.Native.BitReader.readBits.go] at h
    obtain ⟨rfl, rfl⟩ := Except.ok.inj h
    exact ⟨0, br'.toBits, by simp [Deflate.Spec.readBitsLSB], rfl, by simp, hwf⟩
  | succ k ih =>
    -- Case split on whether readBit succeeds
    cases hrd : br.readBit with
    | error e =>
      -- readBit failed → readBits.go (k+1) fails, contradicting h
      simp only [Zip.Native.BitReader.readBits.go, bind, Except.bind, hrd] at h
      simp at h
    | ok p =>
      obtain ⟨bit, br₁⟩ := p
      -- readBit succeeded, unfold readBits.go using hrd
      simp only [Zip.Native.BitReader.readBits.go, bind, Except.bind, hrd] at h
      -- h : readBits.go br₁ (acc ||| (bit <<< shift.toUInt32)) (shift + 1) k = .ok (val, br')
      -- Extract bit correspondence from readBit_toBits
      obtain ⟨b, rest₁, hbr_bits, hbr1_bits, hbit_val⟩ :=
        readBit_toBits br bit br₁ hwf hrd
      have hwf₁ := readBit_wf br bit br₁ hwf hrd
      -- bit is 0 or 1
      have hbit01 : bit = 0 ∨ bit = 1 := by
        cases b <;> simp_all
      -- New accumulator bounds
      have hshift : shift < 32 := by omega
      have hacc' := acc_or_shift_bound acc bit shift hacc hbit01 hshift
      -- Apply IH to the recursive call (val, br' not generalized — don't pass them)
      obtain ⟨specVal', rest', hspec', hbr', hval', hwf'⟩ :=
        ih br₁ (acc ||| (bit <<< shift.toUInt32)) (shift + 1)
          hwf₁ (by omega) hacc' h
      -- Connect readBitsLSB (k+1) to the IH result
      rw [hbr1_bits] at hspec'
      refine ⟨(if b then 1 else 0) + specVal' * 2, rest', ?_, hbr', ?_, hwf'⟩
      · -- readBitsLSB (k+1) br.toBits = some (...)
        simp [Deflate.Spec.readBitsLSB, hbr_bits, hspec']
      · -- val.toNat = acc.toNat + ((if b then 1 else 0) + specVal' * 2) * 2^shift
        rw [hval', acc_or_shift_toNat acc bit shift hacc hbit01 hshift, Nat.pow_succ]
        cases b <;> simp_all [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm] <;> omega

/-! ### readBits correspondence -/

/-- Reading `n` bits via `BitReader.readBits` corresponds to
    `readBitsLSB n` on the spec bit list.
    Requires `bitOff < 8` (well-formedness) and `n ≤ 32` (UInt32 shift
    correctness — native `readBits.go` uses `bit <<< shift.toUInt32`
    where `UInt32.shiftLeft` reduces shift mod 32). -/
theorem readBits_toBits (br : Zip.Native.BitReader)
    (n : Nat) (val : UInt32) (br' : Zip.Native.BitReader)
    (hwf : br.bitOff < 8) (hn : n ≤ 32)
    (h : br.readBits n = .ok (val, br')) :
    ∃ rest,
      Deflate.Spec.readBitsLSB n br.toBits = some (val.toNat, rest) ∧
      br'.toBits = rest := by
  -- readBits = readBits.go br 0 0 n
  simp only [Zip.Native.BitReader.readBits] at h
  obtain ⟨specVal, rest, hspec, hrest, hval, _⟩ :=
    readBits_go_spec br 0 0 n val br' hwf (by omega) (by simp) h
  simp at hval
  -- hval : val.toNat = specVal, need to rewrite specVal → val.toNat in hspec
  rw [← hval] at hspec
  exact ⟨rest, hspec, hrest⟩

/-! ## Huffman decode correspondence

The proof is decomposed into two steps:
1. **BitReader→bits**: `decode_go_decodeBits` — the tree-based decode via
   `BitReader` corresponds to a pure decode on the bit list (`decodeBits`).
2. **Tree→table**: `decodeBits_eq_spec_decode` — the pure tree decode
   agrees with the spec's linear-search decode on the code table.

Step 1 uses `readBit_toBits` at each tree node. Step 2 connects the tree
structure (built by `fromLengths`) to the code table (from `allCodes`). -/

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
private theorem decode_go_decodeBits (tree : Zip.Native.HuffTree)
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
private theorem decodeBits_of_hasLeaf (tree : Zip.Native.HuffTree) (cw : List Bool)
    (sym : UInt16) (rest : List Bool) (h : TreeHasLeaf tree cw sym) :
    decodeBits tree (cw ++ rest) = some (sym, rest) := by
  induction h <;> simp_all [decodeBits]

/-- If `decodeBits` returns `(sym, rest)`, then the tree has a leaf at some
    path `cw` with `bits = cw ++ rest`. -/
private theorem hasLeaf_of_decodeBits (tree : Zip.Native.HuffTree) (bits : List Bool)
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
    (tree : Zip.Native.HuffTree) (len : Nat) (hlen : len ≤ 15)
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
    (tree : Zip.Native.HuffTree) (len : Nat) (hlen : len ≤ 15)
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
    (tree : Zip.Native.HuffTree) (len : Nat) (hlen : len ≤ 15)
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

/-! ### insert.go leaf completeness -/

/-- Every leaf in `insert.go` output is either from the original tree or at the
    inserted path. Requires `NoLeafOnPath` (no collision at intermediate positions). -/
private theorem insert_go_complete (code : UInt32) (sym : UInt16)
    (tree : Zip.Native.HuffTree) (len : Nat) (hlen : len ≤ 15)
    (cw : List Bool) (s : UInt16)
    (hnl : NoLeafOnPath tree (Huffman.Spec.natToBits code.toNat len))
    (h : TreeHasLeaf (Zip.Native.HuffTree.insert.go code sym tree len) cw s) :
    TreeHasLeaf tree cw s ∨ (cw = Huffman.Spec.natToBits code.toNat len ∧ s = sym) := by
  induction len generalizing tree cw with
  | zero =>
    -- insert.go returns .leaf sym, so cw = [] and s = sym
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
          rcases ih .empty (by omega) _ trivial h' with h | ⟨rfl, rfl⟩
          · exact absurd h (by intro h; cases h)
          · exact .inr ⟨by simp [Huffman.Spec.natToBits, htb], rfl⟩
        | right h' => exact absurd h' (by intro h; cases h)
      | node z o =>
        simp only [Zip.Native.HuffTree.insert.go, hbit, ite_true] at h
        simp only [Huffman.Spec.natToBits, htb, NoLeafOnPath] at hnl
        cases h with
        | left h' =>
          rcases ih z (by omega) _ hnl h' with h | ⟨rfl, rfl⟩
          · exact .inl (.left h)
          · exact .inr ⟨by simp [Huffman.Spec.natToBits, htb], rfl⟩
        | right h' => exact .inl (.right h')
      | leaf s' =>
        simp only [Huffman.Spec.natToBits, htb, NoLeafOnPath] at hnl
    | true =>
      have hbit := insert_bit_one code n (by omega) htb
      cases tree with
      | empty =>
        simp only [Zip.Native.HuffTree.insert.go, hbit] at h
        cases h with
        | left h' => exact absurd h' (by intro h; cases h)
        | right h' =>
          rcases ih .empty (by omega) _ trivial h' with h | ⟨rfl, rfl⟩
          · exact absurd h (by intro h; cases h)
          · exact .inr ⟨by simp [Huffman.Spec.natToBits, htb], rfl⟩
      | node z o =>
        simp only [Zip.Native.HuffTree.insert.go, hbit] at h
        simp only [Huffman.Spec.natToBits, htb, NoLeafOnPath] at hnl
        cases h with
        | left h' => exact .inl (.left h')
        | right h' =>
          rcases ih o (by omega) _ hnl h' with h | ⟨rfl, rfl⟩
          · exact .inl (.right h)
          · exact .inr ⟨by simp [Huffman.Spec.natToBits, htb], rfl⟩
      | leaf s' =>
        simp only [Huffman.Spec.natToBits, htb, NoLeafOnPath] at hnl

/-- Like `insert_go_complete` but without `NoLeafOnPath` requirement.
    The `.leaf` case (where insert returns the tree unchanged) is handled
    by returning the pre-existing leaf. -/
private theorem insert_go_complete' (code : UInt32) (sym : UInt16)
    (tree : Zip.Native.HuffTree) (len : Nat) (hlen : len ≤ 15)
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
private theorem fromLengths_ok_eq (lengths : Array UInt8) (tree : Zip.Native.HuffTree)
    (htree : Zip.Native.HuffTree.fromLengths lengths = .ok tree) :
    tree = Zip.Native.HuffTree.fromLengthsTree lengths := by
  simp only [Zip.Native.HuffTree.fromLengths] at htree
  cases hval : Zip.Native.HuffTree.validateLengths lengths 15 with
  | ok _ =>
    simp [hval, bind, Except.bind, pure, Except.pure] at htree; exact htree.symm
  | error _ => simp [hval, bind, Except.bind] at htree

/-- `Array.set!` at a different index doesn't affect the target (UInt32 version). -/
private theorem array_set_ne_u32 (arr : Array UInt32) (i j : Nat) (v : UInt32) (hij : i ≠ j) :
    (arr.set! i v)[j]! = arr[j]! := by
  simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
        Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne hij]

/-- `Array.set!` at the same index replaces the value (UInt32 version). -/
private theorem array_set_self_u32 (arr : Array UInt32) (i : Nat) (v : UInt32) (hi : i < arr.size) :
    (arr.set! i v)[i]! = v := by
  simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
        Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt hi]

/-- `codeFor` returns `some` for symbols with valid nonzero length. -/
private theorem codeFor_some (lsList : List Nat) (s : Nat)
    (hs : s < lsList.length) (hlen : lsList[s] ≠ 0) (hle : lsList[s] ≤ 15) :
    ∃ cw, Huffman.Spec.codeFor lsList 15 s = some cw := by
  simp only [Huffman.Spec.codeFor, show s < lsList.length from hs, ↓reduceDIte]
  simp only [show (lsList[s] == 0 || decide (lsList[s] > 15)) = false from by
    simp [beq_iff_eq, hlen]; omega]
  exact ⟨_, rfl⟩

/-- The tree produced by `insertLoop` has a leaf for every symbol with nonzero length,
    at the codeword given by `codeFor`. Proved by well-founded induction on `lengths.size - start`,
    maintaining the NC invariant, forward invariant, and NoLeafOnPath invariant. -/
private theorem insertLoop_forward
    (lengths : Array UInt8) (nextCode : Array UInt32)
    (start : Nat) (tree : Zip.Native.HuffTree)
    (lsList : List Nat) (hlsList : lsList = lengths.toList.map UInt8.toNat)
    (blCount : Array Nat) (hblCount : blCount = Huffman.Spec.countLengths lsList 15)
    (ncSpec : Array Nat) (hncSpec : ncSpec = Huffman.Spec.nextCodes blCount 15)
    (hv : Huffman.Spec.ValidLengths lsList 15)
    (hncSize : nextCode.size ≥ 16)
    -- NC invariant: nextCode tracks ncSpec + partial offset
    (hnc : ∀ b, 1 ≤ b → b ≤ 15 →
      nextCode[b]!.toNat = ncSpec[b]! +
        (lsList.take start).foldl (fun acc l => if l == b then acc + 1 else acc) 0)
    -- Forward: tree has leaves for all k < start
    (hprev : ∀ k, k < start → (hk : k < lengths.size) → lengths[k] > 0 →
      ∀ cw, Huffman.Spec.codeFor lsList 15 k = some cw →
        TreeHasLeaf tree cw k.toUInt16)
    -- NoLeafOnPath for all future codes
    (hnlop : ∀ k, start ≤ k → (hk : k < lengths.size) → lengths[k] > 0 →
      ∀ cw, Huffman.Spec.codeFor lsList 15 k = some cw →
        NoLeafOnPath tree cw)
    -- Target symbol
    (j : Nat) (hjs : j < lengths.size) (hjlen : lengths[j] > 0)
    (cw : Huffman.Spec.Codeword) (hcf : Huffman.Spec.codeFor lsList 15 j = some cw) :
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
        simp only [hlsList, List.getElem_map, Array.getElem_toList]; rfl
      have hlen_le : lengths[start].toNat ≤ 15 := by
        rw [← hls_start]; exact hv.1 _ (List.getElem_mem hls_len)
      have hlen_pos_nat : 0 < lengths[start].toNat := hlen_pos
      -- The codeword for symbol `start` matches the insert path
      obtain ⟨cw_s, hcf_s⟩ := codeFor_some lsList start hls_len
        (by rw [hls_start]; omega) (by rw [hls_start]; omega)
      have hcw_s : cw_s = Huffman.Spec.natToBits
          (nextCode[lengths[start].toNat]!).toNat lengths[start].toNat := by
        obtain ⟨_, _, hcw⟩ := Huffman.Spec.codeFor_spec hcf_s
        rw [hcw, hls_start]; congr 1
        rw [← hblCount, ← hncSpec]
        exact (hnc lengths[start].toNat (by omega) hlen_le).symm
      -- Prefix-freeness: insert path is not prefix of any other codeword
      have hpf : ∀ k, k ≠ start → ∀ cw', Huffman.Spec.codeFor lsList 15 k = some cw' →
          ¬(Huffman.Spec.natToBits (nextCode[lengths[start].toNat]!).toNat
            lengths[start].toNat).IsPrefix cw' := by
        intro k hne cw' hcf_k
        have hcf_s' := hcw_s ▸ hcf_s
        exact Huffman.Spec.canonical_prefix_free lsList 15 hv start k _ cw'
          hcf_s' hcf_k (by omega)
      exact insertLoop_forward lengths
        (nextCode.set! lengths[start].toNat (nextCode[lengths[start].toNat]! + 1))
        (start + 1)
        (tree.insert (nextCode[lengths[start].toNat]!) lengths[start].toNat start.toUInt16)
        lsList hlsList blCount hblCount ncSpec hncSpec hv
        (by -- hncSize': set! preserves array size
          simp [Array.set!_eq_setIfInBounds, Array.setIfInBounds]
          split <;> simp_all)
        (by -- hnc': NC invariant after increment
          intro b hb1 hb15
          rw [List.take_add_one]
          simp only [List.getElem?_eq_getElem hls_len, Option.toList,
                     List.foldl_append, List.foldl_cons, List.foldl_nil, hls_start]
          by_cases hbeq : lengths[start].toNat = b
          · -- b = len: both sides incremented
            subst hbeq
            simp only [if_pos (beq_self_eq_true lengths[start].toNat)]
            rw [array_set_self_u32 _ _ _ (by omega : lengths[start].toNat < nextCode.size)]
            have h_nc_val := hnc lengths[start].toNat (by omega) hlen_le
            -- Bound: partial ≤ full (for UInt32 overflow)
            have h_partial_le : (lsList.take start).foldl
                (fun acc l => if (l == lengths[start].toNat) = true then acc + 1 else acc) 0 ≤
                lsList.foldl
                (fun acc l => if (l == lengths[start].toNat) = true then acc + 1 else acc) 0 := by
              rw [show lsList.foldl
                (fun acc l => if (l == lengths[start].toNat) = true then acc + 1 else acc) 0 =
                (lsList.drop start).foldl
                  (fun acc l => if (l == lengths[start].toNat) = true then acc + 1 else acc)
                  ((lsList.take start).foldl
                    (fun acc l => if (l == lengths[start].toNat) = true then acc + 1 else acc) 0)
                from by rw [← List.foldl_append, List.take_append_drop]]
              exact Huffman.Spec.count_foldl_mono _ _ _
            have h_npc := Huffman.Spec.nextCodes_plus_count_le lsList 15
              lengths[start].toNat hv (by omega) hlen_le
            rw [← hblCount, ← hncSpec] at h_npc
            have h_pow := Nat.pow_le_pow_right (by omega : 0 < 2) hlen_le
            rw [UInt32.toNat_add, show (1 : UInt32).toNat = 1 from rfl,
                Nat.mod_eq_of_lt (by omega), h_nc_val]
            omega
          · -- b ≠ len: unchanged
            have hf : ¬((lengths[start].toNat == b) = true) := by
              rw [beq_iff_eq]; exact hbeq
            simp only [if_neg hf]
            rw [array_set_ne_u32 _ _ _ _ hbeq]
            exact hnc b hb1 hb15)
        (by -- hprev': forward invariant after insertion
          intro k hk hks hklen cw' hcf'
          by_cases hk_eq : k = start
          · -- k = start: newly inserted leaf
            have hcf_start : Huffman.Spec.codeFor lsList 15 start = some cw' := by
              rw [← hk_eq]; exact hcf'
            have hcw_eq : cw_s = cw' := Option.some.inj (hcf_s.symm.trans hcf_start)
            subst hcw_eq; rw [hcw_s, hk_eq]
            have h_nlop : NoLeafOnPath tree cw_s :=
              hnlop start Nat.le.refl hstart hlen_pos cw_s hcf_s
            rw [hcw_s] at h_nlop
            exact insert_go_hasLeaf _ _ _ _ hlen_le h_nlop
          · -- k < start: leaf preserved by insert
            exact insert_go_preserves _ _ _ _ hlen_le cw' k.toUInt16
              (hprev k (by omega) hks hklen cw' hcf')
              (hpf k hk_eq cw' hcf'))
        (by -- hnlop': NoLeafOnPath preserved after insert
          intro k hk hks hklen cw' hcf'
          exact insert_go_noLeafOnPath _ _ _ _ hlen_le cw'
            (hnlop k (by omega) hks hklen cw' hcf')
            (hpf k (by omega) cw' hcf'))
        j hjs hjlen cw hcf
    · -- ¬(lengths[start] > 0): skip, recurse with same tree/nextCode
      rename_i hlen_zero
      have hls_len : start < lsList.length := by
        simp [hlsList, hstart]
      have hls_val : lsList[start] = 0 := by
        have h0 : lengths[start].toNat = 0 := by
          have : ¬(0 < lengths[start].toNat) := fun hp => hlen_zero hp
          omega
        simp [hlsList]; exact h0
      exact insertLoop_forward lengths nextCode (start + 1) tree
        lsList hlsList blCount hblCount ncSpec hncSpec hv hncSize
        (by -- NC: lsList[start] = 0 doesn't change count for any b ≥ 1
          intro b hb1 hb15
          rw [hnc b hb1 hb15]; congr 1
          rw [List.take_add_one]
          simp [List.getElem?_eq_getElem hls_len, hls_val, List.foldl_append]
          omega)
        (by -- Forward: k < start+1 with lengths[k]>0 means k < start
          intro k hk hks hklen cw' hcf'
          have : k < start := by
            by_cases h : k = start
            · exfalso; subst h; exact hlen_zero hklen
            · omega
          exact hprev k this hks hklen cw' hcf')
        (by -- NoLeafOnPath: start+1 ≤ k implies start ≤ k
          intro k hk hks hklen cw' hcf'
          exact hnlop k (by omega) hks hklen cw' hcf')
        j hjs hjlen cw hcf
  · -- start ≥ lengths.size: base case
    exact hprev j (by omega) hjs hjlen cw hcf
termination_by lengths.size - start

/-- Backward direction of `insertLoop_forward`: every leaf in the tree
    after `insertLoop` was either pre-existing or corresponds to a symbol
    with nonzero code length that was inserted during the loop. -/
private theorem insertLoop_backward
    (lengths : Array UInt8) (nextCode : Array UInt32)
    (start : Nat) (tree : Zip.Native.HuffTree)
    (lsList : List Nat) (hlsList : lsList = lengths.toList.map UInt8.toNat)
    (blCount : Array Nat) (hblCount : blCount = Huffman.Spec.countLengths lsList 15)
    (ncSpec : Array Nat) (hncSpec : ncSpec = Huffman.Spec.nextCodes blCount 15)
    (hv : Huffman.Spec.ValidLengths lsList 15)
    (hncSize : nextCode.size ≥ 16)
    (hnc : ∀ b, 1 ≤ b → b ≤ 15 →
      nextCode[b]!.toNat = ncSpec[b]! +
        (lsList.take start).foldl (fun acc l => if l == b then acc + 1 else acc) 0)
    (cw : List Bool) (sym : UInt16)
    (h : TreeHasLeaf (Zip.Native.HuffTree.insertLoop lengths nextCode start tree).1 cw sym) :
    TreeHasLeaf tree cw sym ∨
    ∃ k, start ≤ k ∧ k < lsList.length ∧
      sym = k.toUInt16 ∧ Huffman.Spec.codeFor lsList 15 k = some cw := by
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
        simp only [hlsList, List.getElem_map, Array.getElem_toList]; rfl
      have hlen_le : lengths[start].toNat ≤ 15 := by
        rw [← hls_start]; exact hv.1 _ (List.getElem_mem hls_len)
      have hlen_pos_nat : 0 < lengths[start].toNat := hlen_pos
      -- The codeword for symbol `start`
      obtain ⟨cw_s, hcf_s⟩ := codeFor_some lsList start hls_len
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
        lsList hlsList blCount hblCount ncSpec hncSpec hv
        (by simp [Array.set!_eq_setIfInBounds, Array.setIfInBounds]; split <;> simp_all)
        (by -- hnc': NC invariant after increment (same as insertLoop_forward)
          intro b hb1 hb15
          rw [List.take_add_one]
          simp only [List.getElem?_eq_getElem hls_len, Option.toList,
                     List.foldl_append, List.foldl_cons, List.foldl_nil, hls_start]
          by_cases hbeq : lengths[start].toNat = b
          · subst hbeq
            simp only [if_pos (beq_self_eq_true lengths[start].toNat)]
            rw [array_set_self_u32 _ _ _ (by omega : lengths[start].toNat < nextCode.size)]
            have h_nc_val := hnc lengths[start].toNat (by omega) hlen_le
            have h_partial_le : (lsList.take start).foldl
                (fun acc l => if (l == lengths[start].toNat) = true then acc + 1 else acc) 0 ≤
                lsList.foldl
                (fun acc l => if (l == lengths[start].toNat) = true then acc + 1 else acc) 0 := by
              rw [show lsList.foldl
                (fun acc l => if (l == lengths[start].toNat) = true then acc + 1 else acc) 0 =
                (lsList.drop start).foldl
                  (fun acc l => if (l == lengths[start].toNat) = true then acc + 1 else acc)
                  ((lsList.take start).foldl
                    (fun acc l => if (l == lengths[start].toNat) = true then acc + 1 else acc) 0)
                from by rw [← List.foldl_append, List.take_append_drop]]
              exact Huffman.Spec.count_foldl_mono _ _ _
            have h_npc := Huffman.Spec.nextCodes_plus_count_le lsList 15
              lengths[start].toNat hv (by omega) hlen_le
            rw [← hblCount, ← hncSpec] at h_npc
            have h_pow := Nat.pow_le_pow_right (by omega : 0 < 2) hlen_le
            rw [UInt32.toNat_add, show (1 : UInt32).toNat = 1 from rfl,
                Nat.mod_eq_of_lt (by omega), h_nc_val]
            omega
          · have hf : ¬((lengths[start].toNat == b) = true) := by
              rw [beq_iff_eq]; exact hbeq
            simp only [if_neg hf]
            rw [array_set_ne_u32 _ _ _ _ hbeq]
            exact hnc b hb1 hb15)
        cw sym h
      cases ih with
      | inl h_in_insert =>
        -- Leaf was in tree.insert: apply insert_go_complete'
        have ih2 := insert_go_complete' _ _ tree _ hlen_le cw sym h_in_insert
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
        have h0 : lengths[start].toNat = 0 := by
          have : ¬(0 < lengths[start].toNat) := fun hp => hlen_zero hp
          omega
        simp [hlsList]; exact h0
      have ih := insertLoop_backward lengths nextCode (start + 1) tree
        lsList hlsList blCount hblCount ncSpec hncSpec hv hncSize
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
private theorem decode_some_mem {α : Type} (table : List (Huffman.Spec.Codeword × α))
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

/-- The tree built by `fromLengths` has a leaf for every canonical codeword.
    Requires `ValidLengths` to ensure no collisions during insertion. -/
private theorem fromLengths_hasLeaf (lengths : Array UInt8)
    (tree : Zip.Native.HuffTree)
    (htree : Zip.Native.HuffTree.fromLengths lengths = .ok tree)
    (hv : Huffman.Spec.ValidLengths (lengths.toList.map UInt8.toNat) 15)
    (s : Nat) (cw : Huffman.Spec.Codeword)
    (hmem : (s, cw) ∈ Huffman.Spec.allCodes (lengths.toList.map UInt8.toNat)) :
    TreeHasLeaf tree cw s.toUInt16 := by
  -- Extract facts from allCodes membership
  rw [Huffman.Spec.allCodes_mem_iff] at hmem
  obtain ⟨hs_len, hcf⟩ := hmem
  -- Get lengths[s] > 0 from codeFor returning some
  obtain ⟨_, hlen_cond, _⟩ := Huffman.Spec.codeFor_spec hcf
  have ⟨hlen_ne, _⟩ := Huffman.Spec.codeFor_len_bounds hlen_cond
  have hs : s < lengths.size := by
    have : (lengths.toList.map UInt8.toNat).length = lengths.size := by simp
    omega
  have hjlen : lengths[s] > 0 := by
    have : (lengths.toList.map UInt8.toNat)[s] ≠ 0 := hlen_ne
    simp [List.getElem_map, Array.getElem_toList] at this
    exact Nat.pos_of_ne_zero this
  -- Rewrite tree to fromLengthsTree = (insertLoop ...).1
  rw [fromLengths_ok_eq lengths tree htree]
  -- fromLengthsTree unfolds to insertLoop with spec-derived nextCode
  show TreeHasLeaf (Zip.Native.HuffTree.fromLengthsTree lengths) cw s.toUInt16
  unfold Zip.Native.HuffTree.fromLengthsTree
  dsimp only []
  -- Apply insertLoop_forward with start = 0
  exact insertLoop_forward lengths _ 0 .empty _ rfl _ rfl _ rfl hv
    (by -- hncSize: nextCode.size ≥ 16
      simp [Array.size_map, Huffman.Spec.nextCodes_size])
    (by -- hnc: initial NC invariant (take 0 = [], so foldl = 0)
      intro b hb1 hb15
      simp only [List.take_zero, List.foldl_nil, Nat.add_zero]
      -- (ncSpec.map (·.toUInt32))[b]!.toNat = ncSpec[b]!
      -- Unfold [b]! to getD/getElem? chain
      simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
                 Array.getElem?_map]
      have hbs : b < (Huffman.Spec.nextCodes (Huffman.Spec.countLengths
          (List.map UInt8.toNat lengths.toList) 15) 15).size := by
        rw [Huffman.Spec.nextCodes_size]; omega
      simp only [Array.getElem?_eq_getElem hbs, Option.map_some, Option.getD_some]
      -- Goal: ncSpec[b].toUInt32.toNat = ncSpec[b]
      -- toUInt32.toNat = n % 2^32 (by rfl), and n < 2^32 from Huffman bounds
      have h_npc := Huffman.Spec.nextCodes_plus_count_le
        (List.map UInt8.toNat lengths.toList) 15 b hv (by omega) hb15
      -- Rewrite h_npc to use [b] instead of [b]!
      simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
                 Array.getElem?_eq_getElem hbs, Option.getD_some] at h_npc
      have h_pow := Nat.pow_le_pow_right (by omega : 0 < 2) hb15
      show (Huffman.Spec.nextCodes _ 15)[b].toUInt32.toNat =
           (Huffman.Spec.nextCodes _ 15)[b]
      rw [show ∀ n : Nat, n.toUInt32.toNat = n % 2 ^ 32 from fun _ => rfl,
          Nat.mod_eq_of_lt (by omega)])
    (by intro k hk; omega) -- hprev: vacuously true (start = 0)
    (by intro k _ _ _ cw' _; cases cw' <;> trivial) -- hnlop: empty tree
    s hs hjlen cw hcf

/-- Every leaf in the tree built by `fromLengths` corresponds to an entry
    in `allCodes`. -/
private theorem fromLengths_leaf_spec (lengths : Array UInt8)
    (tree : Zip.Native.HuffTree)
    (htree : Zip.Native.HuffTree.fromLengths lengths = .ok tree)
    (hv : Huffman.Spec.ValidLengths (lengths.toList.map UInt8.toNat) 15)
    (hlen_bound : lengths.size ≤ UInt16.size)
    (cw : List Bool) (sym : UInt16)
    (h : TreeHasLeaf tree cw sym) :
    (sym.toNat, cw) ∈ Huffman.Spec.allCodes (lengths.toList.map UInt8.toNat) := by
  rw [fromLengths_ok_eq lengths tree htree] at h
  unfold Zip.Native.HuffTree.fromLengthsTree at h
  dsimp only [] at h
  have ih := insertLoop_backward lengths _ 0 .empty _ rfl _ rfl _ rfl hv
    (by simp [Array.size_map, Huffman.Spec.nextCodes_size])
    (by -- hnc: initial NC invariant (same as fromLengths_hasLeaf)
      intro b hb1 hb15
      simp only [List.take_zero, List.foldl_nil, Nat.add_zero]
      simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
                 Array.getElem?_map]
      have hbs : b < (Huffman.Spec.nextCodes (Huffman.Spec.countLengths
          (List.map UInt8.toNat lengths.toList) 15) 15).size := by
        rw [Huffman.Spec.nextCodes_size]; omega
      simp only [Array.getElem?_eq_getElem hbs, Option.map_some, Option.getD_some]
      have h_npc := Huffman.Spec.nextCodes_plus_count_le
        (List.map UInt8.toNat lengths.toList) 15 b hv (by omega) hb15
      simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
                 Array.getElem?_eq_getElem hbs, Option.getD_some] at h_npc
      have h_pow := Nat.pow_le_pow_right (by omega : 0 < 2) hb15
      show (Huffman.Spec.nextCodes _ 15)[b].toUInt32.toNat =
           (Huffman.Spec.nextCodes _ 15)[b]
      rw [show ∀ n : Nat, n.toUInt32.toNat = n % 2 ^ 32 from fun _ => rfl,
          Nat.mod_eq_of_lt (by omega)])
    cw sym h
  cases ih with
  | inl h_empty => cases h_empty
  | inr h_exists =>
    obtain ⟨k, _, hk_len, rfl, hcf⟩ := h_exists
    have hk_small : k < UInt16.size := by
      have : (List.map UInt8.toNat lengths.toList).length = lengths.size := by
        simp [List.length_map]
      omega
    have hk_toNat : k.toUInt16.toNat = k :=
      Nat.mod_eq_of_lt hk_small
    rw [Huffman.Spec.allCodes_mem_iff]
    exact ⟨by rw [hk_toNat]; exact hk_len, by rw [hk_toNat]; exact hcf⟩

/-- Step 2: For a tree built from code lengths, `decodeBits` agrees with
    the spec's table-based decode. Requires the tree to be well-formed
    (built via `fromLengths`) and the lengths to satisfy the Kraft inequality. -/
private theorem decodeBits_eq_spec_decode (lengths : Array UInt8)
    (tree : Zip.Native.HuffTree) (bits : List Bool)
    (htree : Zip.Native.HuffTree.fromLengths lengths = .ok tree)
    (hv : Huffman.Spec.ValidLengths (lengths.toList.map UInt8.toNat) 15)
    (hlen_bound : lengths.size ≤ UInt16.size) :
    let specLengths := lengths.toList.map UInt8.toNat
    let specCodes := Huffman.Spec.allCodes specLengths
    let specTable := specCodes.map fun (s, cw) => (cw, s)
    (decodeBits tree bits).map (fun (s, rest) => (s.toNat, rest)) =
      Huffman.Spec.decode specTable bits := by
  intro specLengths specCodes specTable
  -- Helper: specTable membership ↔ specCodes membership
  have to_codes : ∀ {cw : List Bool} {s : Nat},
      (cw, s) ∈ specTable → (s, cw) ∈ specCodes := by
    intro cw s h
    obtain ⟨⟨s', cw'⟩, hm, he⟩ := List.mem_map.mp h
    simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he; exact hm
  have to_table : ∀ {s : Nat} {cw : List Bool},
      (s, cw) ∈ specCodes → (cw, s) ∈ specTable := by
    intro s cw h; exact List.mem_map.mpr ⟨(s, cw), h, rfl⟩
  -- Prefix-free property of specTable (needed for decode_prefix_free)
  have hpf : ∀ cw₁ (s₁ : Nat) cw₂ (s₂ : Nat),
      (cw₁, s₁) ∈ specTable → (cw₂, s₂) ∈ specTable →
      (cw₁, s₁) ≠ (cw₂, s₂) → ¬cw₁.IsPrefix cw₂ := by
    intro cw₁ s₁ cw₂ s₂ h₁ h₂ hne hpre
    have hm₁ := to_codes h₁; have hm₂ := to_codes h₂
    by_cases heq : s₁ = s₂
    · subst heq
      rw [Huffman.Spec.allCodes_mem_iff] at hm₁ hm₂
      have : cw₁ = cw₂ := Option.some.inj (hm₁.2.symm.trans hm₂.2)
      subst this; exact absurd rfl hne
    · exact absurd hpre (Huffman.Spec.allCodes_prefix_free_of_ne
        _ _ hv _ _ _ _ hm₁ hm₂ heq)
  match hdb : decodeBits tree bits with
  | none =>
    simp only [Option.map]
    match hdec : Huffman.Spec.decode specTable bits with
    | none => rfl
    | some (v, rest) =>
      exfalso
      obtain ⟨cw, hmem_table, hbits⟩ := decode_some_mem specTable bits v rest hdec
      have hleaf := fromLengths_hasLeaf lengths tree htree hv v cw (to_codes hmem_table)
      have hdb' := decodeBits_of_hasLeaf tree cw v.toUInt16 rest hleaf
      rw [hbits] at hdb; rw [hdb'] at hdb; simp at hdb
  | some (sym, rest) =>
    simp only [Option.map]
    obtain ⟨cw, hleaf, hbits⟩ := hasLeaf_of_decodeBits tree bits sym rest hdb
    have hmem_codes := fromLengths_leaf_spec lengths tree htree hv hlen_bound cw sym hleaf
    have hdec := Huffman.Spec.decode_prefix_free specTable cw sym.toNat rest
      (to_table hmem_codes) hpf
    rw [hbits]; exact hdec.symm

/-- A `HuffTree` built from code lengths decodes the same symbol as the
    spec's `Huffman.Spec.decode` on the corresponding code table.
    Requires `bitOff < 8` because the proof traces through individual
    `readBit` calls via `readBit_toBits`. -/
theorem huffTree_decode_correct (lengths : Array UInt8)
    (tree : Zip.Native.HuffTree) (br : Zip.Native.BitReader)
    (sym : UInt16) (br' : Zip.Native.BitReader)
    (hwf : br.bitOff < 8)
    (htree : Zip.Native.HuffTree.fromLengths lengths = .ok tree)
    (hv : Huffman.Spec.ValidLengths (lengths.toList.map UInt8.toNat) 15)
    (hlen_bound : lengths.size ≤ UInt16.size)
    (hdecode : tree.decode br = .ok (sym, br')) :
    let specLengths := lengths.toList.map UInt8.toNat
    let specCodes := Huffman.Spec.allCodes specLengths
    let specTable := specCodes.map fun (s, cw) => (cw, s)
    ∃ rest,
      Huffman.Spec.decode specTable br.toBits = some (sym.toNat, rest) ∧
      br'.toBits = rest := by
  -- Step 1: BitReader decode → pure decodeBits
  have hdecode_go : Zip.Native.HuffTree.decode.go tree br 0 = .ok (sym, br') := by
    simp only [Zip.Native.HuffTree.decode] at hdecode; exact hdecode
  obtain ⟨hdb, _⟩ := decode_go_decodeBits tree br 0 sym br' hwf hdecode_go
  -- Step 2: decodeBits → spec decode via tree-table correspondence
  have hspec := decodeBits_eq_spec_decode lengths tree br.toBits htree hv hlen_bound
  -- Connect the two
  rw [hdb] at hspec; simp at hspec
  exact ⟨br'.toBits, hspec.symm, rfl⟩

/-! ## Main correctness theorem -/

/-- **Main theorem**: If the native DEFLATE decompressor succeeds, then
    the formal specification also succeeds and produces the same output.

    The native decompressor `inflateRaw` processes a `ByteArray` starting
    at byte offset `startPos`, reads DEFLATE blocks until a final block,
    and returns the decompressed data with the ending byte position.

    The spec `decode` converts the same data to a bit list via
    `bytesToBits`, decodes blocks according to RFC 1951, and returns
    the decompressed output as a `List UInt8`.

    The existential over `fuel` accounts for the fuel-based termination
    in the spec's decode function. The native implementation uses bounded
    loops (at most 10001 blocks) that correspond to the spec's fuel. -/
theorem inflate_correct (data : ByteArray) (startPos maxOutputSize : Nat)
    (result : ByteArray) (endPos : Nat)
    (h : Zip.Native.Inflate.inflateRaw data startPos maxOutputSize =
      .ok (result, endPos)) :
    ∃ fuel,
      Deflate.Spec.decode
        ((Deflate.Spec.bytesToBits data).drop (startPos * 8)) fuel =
        some result.data.toList := by
  sorry

/-- Corollary: `inflate` (which starts at position 0) agrees with
    `decodeBytes` (which also starts at position 0). -/
theorem inflate_correct' (data : ByteArray) (maxOutputSize : Nat)
    (result : ByteArray)
    (h : Zip.Native.Inflate.inflate data maxOutputSize = .ok result) :
    ∃ fuel,
      Deflate.Spec.decode (Deflate.Spec.bytesToBits data) fuel =
        some result.data.toList := by
  sorry

end Deflate.Correctness
