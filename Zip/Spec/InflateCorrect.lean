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

private theorem uint32_bit_eq_testBit (byte : UInt8) (off : Nat) (hoff : off < 8) :
    ((byte.toUInt32 >>> off.toUInt32) &&& 1) =
      if byte.toNat.testBit off then 1 else 0 := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_and, UInt32.toNat_shiftRight, UInt8.toNat_toUInt32]
  have hoff_eq : off.toUInt32.toNat % 32 = off := by simp [Nat.toUInt32]; omega
  rw [hoff_eq]
  have : UInt32.toNat 1 = 1 := by decide
  rw [this, shift_and_one_eq_testBit]
  split <;> simp

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
          have hb : b = false := by
            have : bit = 0 := by rwa [beq_iff_eq] at hbit
            cases b <;> simp_all
          obtain ⟨hspec, hwf'⟩ := ihz br₁ (n + 1) hwf₁ h
          refine ⟨?_, hwf'⟩
          rw [hbr_bits, hb]; simp only [decodeBits]
          rw [← hbr1_bits]; exact hspec
        · -- bit != 0: go right (b = true)
          rename_i hbit
          have hb : b = true := by
            cases b with
            | true => rfl
            | false => exfalso; exact hbit (by simp_all)
          obtain ⟨hspec, hwf'⟩ := iho br₁ (n + 1) hwf₁ h
          refine ⟨?_, hwf'⟩
          rw [hbr_bits, hb]; simp only [decodeBits]
          rw [← hbr1_bits]; exact hspec

/-- Step 2: For a tree built from code lengths, `decodeBits` agrees with
    the spec's table-based decode. Requires the tree to be well-formed
    (built via `fromLengths`). -/
private theorem decodeBits_eq_spec_decode (lengths : Array UInt8)
    (tree : Zip.Native.HuffTree) (bits : List Bool)
    (htree : Zip.Native.HuffTree.fromLengths lengths = .ok tree) :
    let specLengths := lengths.toList.map UInt8.toNat
    let specCodes := Huffman.Spec.allCodes specLengths
    let specTable := specCodes.map fun (s, cw) => (cw, s)
    (decodeBits tree bits).map (fun (s, rest) => (s.toNat, rest)) =
      Huffman.Spec.decode specTable bits := by
  sorry

/-- A `HuffTree` built from code lengths decodes the same symbol as the
    spec's `Huffman.Spec.decode` on the corresponding code table.
    Requires `bitOff < 8` because the proof traces through individual
    `readBit` calls via `readBit_toBits`. -/
theorem huffTree_decode_correct (lengths : Array UInt8)
    (tree : Zip.Native.HuffTree) (br : Zip.Native.BitReader)
    (sym : UInt16) (br' : Zip.Native.BitReader)
    (hwf : br.bitOff < 8)
    (htree : Zip.Native.HuffTree.fromLengths lengths = .ok tree)
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
  have hspec := decodeBits_eq_spec_decode lengths tree br.toBits htree
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
