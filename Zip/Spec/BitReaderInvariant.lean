import Zip.Native.Inflate

/-!
# BitReader invariant preservation

All BitReader operations preserve `data` and the position invariant
`bitOff = 0 ∨ pos < data.size`. We prove individual preservation lemmas,
then combined `_inv` lemmas that bundle data preservation, hpos, and
`pos ≤ data.size` into a single conjunction.

These properties are used by `InflateLoopBounds` and `InflateRawSuffix`
to track invariants through the inflate decompression pipeline.
-/

namespace Zip.Native

/-- `readBit` preserves the data field and the hpos invariant. -/
private theorem readBit_data_eq (br br' : BitReader) (bit : UInt32)
    (h : br.readBit = .ok (bit, br')) : br'.data = br.data := by
  simp only [BitReader.readBit] at h
  split at h
  · simp at h
  · split at h <;> simp [Except.ok.injEq, Prod.mk.injEq] at h <;>
      obtain ⟨_, rfl⟩ := h <;> rfl

/-- `readBits.go` preserves the data field. -/
private theorem readBits_go_data_eq (br br' : BitReader) (acc : UInt32)
    (shift n : Nat) (val : UInt32)
    (h : BitReader.readBits.go br acc shift n = .ok (val, br')) :
    br'.data = br.data := by
  induction n generalizing br acc shift with
  | zero =>
    simp [BitReader.readBits.go] at h
    obtain ⟨_, rfl⟩ := h; rfl
  | succ n ih =>
    simp only [BitReader.readBits.go, bind, Except.bind] at h
    cases hrb : br.readBit with
    | error e => simp [hrb] at h
    | ok p =>
      obtain ⟨bit, br₁⟩ := p
      simp only [hrb] at h
      have hd₁ := readBit_data_eq br br₁ bit hrb
      have hd' := ih br₁ _ _ h
      rw [hd', hd₁]

/-- `readBits` preserves the data field. -/
private theorem readBits_data_eq (br br' : BitReader) (n : Nat)
    (val : UInt32) (h : br.readBits n = .ok (val, br')) :
    br'.data = br.data := by
  exact readBits_go_data_eq br br' 0 0 n val h

/-- After a successful `readBit`, the hpos invariant `bitOff = 0 ∨ pos < data.size` holds. -/
private theorem readBit_hpos (br br' : BitReader) (bit : UInt32)
    (h : br.readBit = .ok (bit, br'))
    (_hpos : br.bitOff = 0 ∨ br.pos < br.data.size) :
    br'.bitOff = 0 ∨ br'.pos < br'.data.size := by
  simp only [BitReader.readBit] at h
  split at h
  · simp at h
  · rename_i hlt
    split at h <;> simp [Except.ok.injEq, Prod.mk.injEq] at h <;>
      obtain ⟨_, rfl⟩ := h <;> simp_all

/-- `readBits.go` preserves the hpos invariant. -/
private theorem readBits_go_hpos (br br' : BitReader) (acc : UInt32)
    (shift n : Nat) (val : UInt32)
    (h : BitReader.readBits.go br acc shift n = .ok (val, br'))
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size) :
    br'.bitOff = 0 ∨ br'.pos < br'.data.size := by
  induction n generalizing br acc shift with
  | zero =>
    simp [BitReader.readBits.go] at h
    obtain ⟨_, rfl⟩ := h; exact hpos
  | succ n ih =>
    simp only [BitReader.readBits.go, bind, Except.bind] at h
    cases hrb : br.readBit with
    | error e => simp [hrb] at h
    | ok p =>
      obtain ⟨bit, br₁⟩ := p
      simp only [hrb] at h
      have hpos₁ := readBit_hpos br br₁ bit hrb hpos
      have hd₁ := readBit_data_eq br br₁ bit hrb
      exact ih br₁ _ _ h (hd₁ ▸ hpos₁)

/-- `readBits` preserves the hpos invariant. -/
private theorem readBits_hpos (br br' : BitReader) (n : Nat)
    (val : UInt32) (h : br.readBits n = .ok (val, br'))
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size) :
    br'.bitOff = 0 ∨ br'.pos < br'.data.size := by
  exact readBits_go_hpos br br' 0 0 n val h hpos

/-- `alignToByte.pos ≤ data.size` when `pos ≤ data.size`. In the `bitOff ≠ 0` case,
    we need the stronger `pos < data.size` (from the hpos invariant). -/
theorem alignToByte_pos_le (br : BitReader)
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (hle : br.pos ≤ br.data.size) :
    br.alignToByte.pos ≤ br.data.size := by
  simp only [BitReader.alignToByte]
  split
  · exact hle
  · rename_i hne
    cases hpos with
    | inl h => simp [h] at hne
    | inr h => simp only; omega


/-! ### BitReader invariant preservation

All BitReader operations preserve `data` and the position invariant
`bitOff = 0 ∨ pos < data.size`. We bundle these into combined lemmas
for each function to minimize code. -/

/-- Combined: readBit preserves data, hpos, and gives pos ≤ data.size. -/
private theorem readBit_inv (br br' : BitReader) (bit : UInt32)
    (h : br.readBit = .ok (bit, br'))
    (_hpos : br.bitOff = 0 ∨ br.pos < br.data.size) :
    br'.data = br.data ∧
    (br'.bitOff = 0 ∨ br'.pos < br'.data.size) ∧
    br'.pos ≤ br'.data.size := by
  simp only [BitReader.readBit] at h
  split at h
  · simp at h
  · rename_i hlt
    split at h <;> simp [Except.ok.injEq, Prod.mk.injEq] at h <;>
      obtain ⟨_, rfl⟩ := h <;> simp_all <;> omega

/-- Combined: readBits.go preserves data, hpos, and pos ≤ data.size. -/
private theorem readBits_go_inv (br br' : BitReader) (acc : UInt32)
    (shift n : Nat) (val : UInt32)
    (h : BitReader.readBits.go br acc shift n = .ok (val, br'))
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (hple : br.pos ≤ br.data.size) :
    br'.data = br.data ∧
    (br'.bitOff = 0 ∨ br'.pos < br'.data.size) ∧
    br'.pos ≤ br'.data.size := by
  induction n generalizing br acc shift with
  | zero =>
    simp [BitReader.readBits.go] at h
    obtain ⟨_, rfl⟩ := h; exact ⟨rfl, hpos, hple⟩
  | succ n ih =>
    simp only [BitReader.readBits.go, bind, Except.bind] at h
    cases hrb : br.readBit with
    | error e => simp [hrb] at h
    | ok p =>
      obtain ⟨bit, br₁⟩ := p
      simp only [hrb] at h
      have ⟨hd₁, hpos₁, hple₁⟩ := readBit_inv br br₁ bit hrb hpos
      have ⟨hd', hpos', hple'⟩ := ih br₁ _ _ h hpos₁ hple₁
      exact ⟨hd'.trans hd₁, hpos', hple'⟩

/-- Combined: readBits preserves data, hpos, and pos ≤ data.size. -/
theorem readBits_inv (br br' : BitReader) (n : Nat)
    (val : UInt32) (h : br.readBits n = .ok (val, br'))
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (hple : br.pos ≤ br.data.size) :
    br'.data = br.data ∧
    (br'.bitOff = 0 ∨ br'.pos < br'.data.size) ∧
    br'.pos ≤ br'.data.size :=
  readBits_go_inv br br' 0 0 n val h hpos hple

/-- Combined: HuffTree.decode.go preserves data, hpos, and pos ≤ data.size. -/
private theorem decode_go_inv (tree : HuffTree) (br br' : BitReader) (n : Nat)
    (sym : UInt16) (h : HuffTree.decode.go tree br n = .ok (sym, br'))
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (hple : br.pos ≤ br.data.size) :
    br'.data = br.data ∧
    (br'.bitOff = 0 ∨ br'.pos < br'.data.size) ∧
    br'.pos ≤ br'.data.size := by
  induction tree generalizing br n with
  | leaf s =>
    simp [HuffTree.decode.go] at h
    obtain ⟨_, rfl⟩ := h; exact ⟨rfl, hpos, hple⟩
  | empty => simp [HuffTree.decode.go] at h
  | node z o ihz iho =>
    simp only [HuffTree.decode.go] at h
    split at h
    · simp at h
    · simp only [bind, Except.bind] at h
      cases hrb : br.readBit with
      | error e => simp [hrb] at h
      | ok p =>
        obtain ⟨bit, br₁⟩ := p
        simp only [hrb] at h
        have ⟨hd₁, hpos₁, hple₁⟩ := readBit_inv br br₁ bit hrb hpos
        split at h
        · have ⟨hd', hp', hl'⟩ := ihz br₁ _ h hpos₁ hple₁
          exact ⟨hd'.trans hd₁, hp', hl'⟩
        · have ⟨hd', hp', hl'⟩ := iho br₁ _ h hpos₁ hple₁
          exact ⟨hd'.trans hd₁, hp', hl'⟩

/-- Combined: HuffTree.decode preserves data, hpos, and pos ≤ data.size. -/
theorem decode_inv (tree : HuffTree) (br br' : BitReader)
    (sym : UInt16) (h : tree.decode br = .ok (sym, br'))
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (hple : br.pos ≤ br.data.size) :
    br'.data = br.data ∧
    (br'.bitOff = 0 ∨ br'.pos < br'.data.size) ∧
    br'.pos ≤ br'.data.size :=
  decode_go_inv tree br br' 0 sym h hpos hple

/-- readUInt16LE preserves data and sets bitOff = 0. -/
private theorem readUInt16LE_inv (br br' : BitReader) (v : UInt16)
    (h : br.readUInt16LE = .ok (v, br')) :
    br'.data = br.data ∧ br'.bitOff = 0 ∧ br'.pos ≤ br'.data.size := by
  simp only [BitReader.readUInt16LE, BitReader.alignToByte] at h
  split at h
  next hbo =>
    split at h
    · simp at h
    · next hle =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h
      have hbo' : br.bitOff = 0 := eq_of_beq hbo
      exact ⟨rfl, hbo', by dsimp [BitReader.data, BitReader.pos] at hle ⊢; omega⟩
  next hbo =>
    split at h
    · simp at h
    · next hle =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h
      exact ⟨rfl, rfl, by dsimp [BitReader.data, BitReader.pos] at hle ⊢; omega⟩

/-- readBytes preserves data and sets bitOff = 0. -/
private theorem readBytes_inv (br br' : BitReader) (n : Nat) (bytes : ByteArray)
    (h : br.readBytes n = .ok (bytes, br')) :
    br'.data = br.data ∧ br'.bitOff = 0 ∧ br'.pos ≤ br'.data.size := by
  simp only [BitReader.readBytes, BitReader.alignToByte] at h
  split at h
  next hbo =>
    split at h
    · simp at h
    · next hle =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h
      have hbo' : br.bitOff = 0 := eq_of_beq hbo
      exact ⟨rfl, hbo', by dsimp [BitReader.data, BitReader.pos] at hle ⊢; omega⟩
  next hbo =>
    split at h
    · simp at h
    · next hle =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h
      exact ⟨rfl, rfl, by dsimp [BitReader.data, BitReader.pos] at hle ⊢; omega⟩

/-- Combined: decodeStored preserves data, and gives hpos + pos_le. -/
theorem decodeStored_inv (br br' : BitReader)
    (output output' : ByteArray) (maxOut : Nat)
    (h : Inflate.decodeStored br output maxOut = .ok (output', br')) :
    br'.data = br.data ∧
    (br'.bitOff = 0 ∨ br'.pos < br'.data.size) ∧
    br'.pos ≤ br'.data.size := by
  -- decodeStored chains: readUInt16LE → readUInt16LE → checks → readBytes
  -- All three preserve data and produce bitOff = 0.
  -- Extract that readBytes succeeded from the successful decodeStored call.
  simp only [Inflate.decodeStored, bind, Except.bind] at h
  match h1 : br.readUInt16LE with
  | .error e => simp [h1] at h
  | .ok (len, br₁) =>
    rw [h1] at h; simp only [] at h
    match h2 : br₁.readUInt16LE with
    | .error e => simp [h2] at h
    | .ok (nlen, br₂) =>
      rw [h2] at h; simp only [] at h
      have h_rb : ∃ bytes, br₂.readBytes len.toNat = .ok (bytes, br') := by
        revert h; intro h
        simp only [pure, Except.pure] at h
        by_cases hxor : (len ^^^ nlen != 0xFFFF) = true
        · simp [hxor] at h
        · simp only [hxor] at h
          by_cases hsize : output.size + len.toNat > maxOut
          · simp [hsize] at h
          · simp only [hsize, ite_false] at h
            match h3 : br₂.readBytes len.toNat with
            | .error e => simp [h3] at h
            | .ok (bytes, br₃) =>
              simp [h3] at h
              exact ⟨bytes, by rw [h.2]⟩
      obtain ⟨bytes, h_rb⟩ := h_rb
      have ⟨hd3, hbo3, hple3⟩ := readBytes_inv br₂ br' _ _ h_rb
      have ⟨hd1, _, _⟩ := readUInt16LE_inv br br₁ _ h1
      have ⟨hd2, _, _⟩ := readUInt16LE_inv br₁ br₂ _ h2
      exact ⟨hd3.trans (hd2.trans hd1), Or.inl hbo3, hple3⟩

/-- Combined: decodeHuffman.go preserves data, hpos, and pos ≤ data.size. -/
theorem decodeHuffman_go_inv (litTree distTree : HuffTree)
    (br br' : BitReader) (output output' : ByteArray)
    (maxOut fuel : Nat)
    (h : Inflate.decodeHuffman.go litTree distTree maxOut br output fuel =
      .ok (output', br'))
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (hple : br.pos ≤ br.data.size) :
    br'.data = br.data ∧
    (br'.bitOff = 0 ∨ br'.pos < br'.data.size) ∧
    br'.pos ≤ br'.data.size := by
  induction fuel generalizing br output with
  | zero => simp [Inflate.decodeHuffman.go] at h
  | succ n ih =>
    unfold Inflate.decodeHuffman.go at h
    cases hlit : litTree.decode br with
    | error e => rw [hlit] at h; simp [Bind.bind, Except.bind] at h
    | ok p =>
      obtain ⟨sym, br₁⟩ := p; rw [hlit] at h; dsimp only [Bind.bind, Except.bind] at h
      -- Reduce `match pure PUnit.unit` to just the ok branch
      simp only [pure, Except.pure] at h
      have ⟨hd₁, hpos₁, hple₁⟩ := decode_inv litTree br br₁ sym hlit hpos hple
      split at h
      · -- sym < 256: literal byte
        split at h
        · simp at h  -- output.size ≥ maxOut → error
        · -- recursive call
          have ⟨hd', hp', hl'⟩ := ih br₁ _ h hpos₁ hple₁
          exact ⟨hd'.trans hd₁, hp', hl'⟩
      · split at h
        · -- sym == 256: end of block
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨_, rfl⟩ := h
          exact ⟨hd₁, hpos₁, hple₁⟩
        · -- sym ≥ 257: length+distance code
          split at h
          · simp at h  -- invalid length code → error
          · split at h
            · simp at h  -- readBits error
            · rename_i v hrb1_eq
              split at h
              · simp at h  -- decode dist error
              · rename_i v₁ hdist_eq
                split at h
                · simp at h  -- invalid distance code
                · split at h
                  · simp at h  -- readBits dist extra error
                  · rename_i v₂ hrb2_eq
                    split at h
                    · simp at h  -- distance > output.size
                    · split at h
                      · simp at h  -- output.size + length > maxOut
                      · -- recursive go call remains
                        obtain ⟨extraBits, br₂⟩ := v
                        obtain ⟨distSym, br₃⟩ := v₁
                        obtain ⟨dExtraBits, br₄⟩ := v₂
                        simp only [] at hrb1_eq hdist_eq hrb2_eq h
                        have ⟨hd₂, hpos₂, hple₂⟩ := readBits_inv br₁ br₂ _ _ hrb1_eq hpos₁ hple₁
                        have ⟨hd₃, hpos₃, hple₃⟩ := decode_inv distTree br₂ br₃ distSym hdist_eq hpos₂ hple₂
                        have ⟨hd₄, hpos₄, hple₄⟩ := readBits_inv br₃ br₄ _ _ hrb2_eq hpos₃ hple₃
                        have ⟨hd', hp', hl'⟩ := ih br₄ _ h hpos₄ hple₄
                        exact ⟨hd'.trans (hd₄.trans (hd₃.trans (hd₂.trans hd₁))), hp', hl'⟩

/-- `decodeHuffman` preserves the BitReader invariant. Wrapper around `decodeHuffman_go_inv`. -/
theorem decodeHuffman_inv (litTree distTree : HuffTree)
    (br br' : BitReader) (output output' : ByteArray) (maxOut : Nat)
    (h : Inflate.decodeHuffman br output litTree distTree maxOut = .ok (output', br'))
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (hple : br.pos ≤ br.data.size) :
    br'.data = br.data ∧
    (br'.bitOff = 0 ∨ br'.pos < br'.data.size) ∧
    br'.pos ≤ br'.data.size :=
  decodeHuffman_go_inv litTree distTree br br' output output' maxOut _ h hpos hple

/-- Combined: readCLCodeLengths preserves data, hpos, and pos ≤ data.size. -/
theorem readCLCodeLengths_inv (br br' : BitReader)
    (clLengths clLengths' : Array UInt8) (i numCodeLen : Nat)
    (h : Inflate.readCLCodeLengths br clLengths i numCodeLen = .ok (clLengths', br'))
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (hple : br.pos ≤ br.data.size) :
    br'.data = br.data ∧
    (br'.bitOff = 0 ∨ br'.pos < br'.data.size) ∧
    br'.pos ≤ br'.data.size := by
  -- Use strong induction on numCodeLen - i
  suffices ∀ (m : Nat) br (clLengths : Array UInt8) (i numCodeLen : Nat),
      m = numCodeLen - i →
      Inflate.readCLCodeLengths br clLengths i numCodeLen = .ok (clLengths', br') →
      (br.bitOff = 0 ∨ br.pos < br.data.size) → br.pos ≤ br.data.size →
      br'.data = br.data ∧
      (br'.bitOff = 0 ∨ br'.pos < br'.data.size) ∧
      br'.pos ≤ br'.data.size from this _ _ _ _ _ rfl h hpos hple
  intro m
  induction m with
  | zero =>
    intro br cl i ncl heq h hpos hple
    unfold Inflate.readCLCodeLengths at h
    split at h
    · rename_i hlt; omega
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h; exact ⟨rfl, hpos, hple⟩
  | succ k ih =>
    intro br cl i ncl heq h hpos hple
    unfold Inflate.readCLCodeLengths at h
    split at h
    · simp only [bind, Except.bind] at h
      cases hrb : br.readBits 3 with
      | error e => simp [hrb] at h
      | ok p =>
        obtain ⟨v, br₁⟩ := p; simp only [hrb] at h
        have ⟨hd₁, hpos₁, hple₁⟩ := readBits_inv br br₁ 3 v hrb hpos hple
        have ⟨hd', hp', hl'⟩ := ih br₁ _ (i + 1) ncl (by omega) h hpos₁ hple₁
        exact ⟨hd'.trans hd₁, hp', hl'⟩
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h; exact ⟨rfl, hpos, hple⟩

/-- Combined: decodeCLSymbols preserves data, hpos, and pos ≤ data.size. -/
theorem decodeCLSymbols_inv (clTree : HuffTree) (br br' : BitReader)
    (codeLengths codeLengths' : Array UInt8) (idx totalCodes fuel : Nat)
    (h : Inflate.decodeCLSymbols clTree br codeLengths idx totalCodes fuel =
      .ok (codeLengths', br'))
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (hple : br.pos ≤ br.data.size) :
    br'.data = br.data ∧
    (br'.bitOff = 0 ∨ br'.pos < br'.data.size) ∧
    br'.pos ≤ br'.data.size := by
  induction fuel generalizing br codeLengths idx with
  | zero => simp [Inflate.decodeCLSymbols] at h
  | succ n ih =>
    unfold Inflate.decodeCLSymbols at h
    split at h
    · -- idx ≥ totalCodes: return
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h; exact ⟨rfl, hpos, hple⟩
    · -- idx < totalCodes: do block
      dsimp only [Bind.bind, Except.bind] at h
      split at h
      · simp at h  -- decode error
      · rename_i v hdec_eq
        simp only [pure, Except.pure] at h
        obtain ⟨sym, br₁⟩ := v; simp only [] at hdec_eq h
        have ⟨hd₁, hpos₁, hple₁⟩ := decode_inv clTree br br₁ sym hdec_eq hpos hple
        split at h
        · -- sym < 16: literal code length
          have ⟨hd', hp', hl'⟩ := ih br₁ _ _ h hpos₁ hple₁
          exact ⟨hd'.trans hd₁, hp', hl'⟩
        · split at h
          · -- sym == 16: repeat previous
            split at h
            · simp at h  -- idx == 0 error
            · -- readBits 2
              split at h
              · simp at h  -- readBits error
              · rename_i v₁ hrb_eq
                obtain ⟨rep, br₂⟩ := v₁; simp only [] at hrb_eq h
                have ⟨hd₂, hpos₂, hple₂⟩ := readBits_inv br₁ br₂ 2 rep hrb_eq hpos₁ hple₁
                split at h
                · simp at h  -- repeat exceeds total
                · have ⟨hd', hp', hl'⟩ := ih br₂ _ _ h hpos₂ hple₂
                  exact ⟨hd'.trans (hd₂.trans hd₁), hp', hl'⟩
          · split at h
            · -- sym == 17: zero-fill short
              split at h
              · simp at h  -- readBits error
              · rename_i v₂ hrb_eq
                obtain ⟨rep, br₂⟩ := v₂; simp only [] at hrb_eq h
                have ⟨hd₂, hpos₂, hple₂⟩ := readBits_inv br₁ br₂ 3 rep hrb_eq hpos₁ hple₁
                split at h
                · simp at h  -- repeat exceeds total
                · have ⟨hd', hp', hl'⟩ := ih br₂ _ _ h hpos₂ hple₂
                  exact ⟨hd'.trans (hd₂.trans hd₁), hp', hl'⟩
            · split at h
              · -- sym == 18: zero-fill long
                split at h
                · simp at h  -- readBits error
                · rename_i v₃ hrb_eq
                  obtain ⟨rep, br₂⟩ := v₃; simp only [] at hrb_eq h
                  have ⟨hd₂, hpos₂, hple₂⟩ := readBits_inv br₁ br₂ 7 rep hrb_eq hpos₁ hple₁
                  split at h
                  · simp at h  -- repeat exceeds total
                  · have ⟨hd', hp', hl'⟩ := ih br₂ _ _ h hpos₂ hple₂
                    exact ⟨hd'.trans (hd₂.trans hd₁), hp', hl'⟩
              · simp at h  -- invalid symbol

/-- Combined: decodeDynamicTrees preserves data, hpos, and pos ≤ data.size. -/
theorem decodeDynamicTrees_inv (br br' : BitReader)
    (litTree distTree : HuffTree)
    (h : Inflate.decodeDynamicTrees br = .ok (litTree, distTree, br'))
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (hple : br.pos ≤ br.data.size) :
    br'.data = br.data ∧
    (br'.bitOff = 0 ∨ br'.pos < br'.data.size) ∧
    br'.pos ≤ br'.data.size := by
  simp only [Inflate.decodeDynamicTrees] at h
  dsimp only [Bind.bind, Except.bind] at h
  -- readBits 5 (hlit)
  split at h
  · simp at h
  · rename_i v₁ hrb1_eq
    obtain ⟨hlit_val, br₁⟩ := v₁; simp only [] at hrb1_eq h
    have ⟨hd₁, hpos₁, hple₁⟩ := readBits_inv br br₁ 5 hlit_val hrb1_eq hpos hple
    -- readBits 5 (hdist)
    split at h
    · simp at h
    · rename_i v₂ hrb2_eq
      obtain ⟨hdist_val, br₂⟩ := v₂; simp only [] at hrb2_eq h
      have ⟨hd₂, hpos₂, hple₂⟩ := readBits_inv br₁ br₂ 5 hdist_val hrb2_eq hpos₁ hple₁
      -- readBits 4 (hclen)
      split at h
      · simp at h
      · rename_i v₃ hrb3_eq
        obtain ⟨hclen_val, br₃⟩ := v₃; simp only [] at hrb3_eq h
        have ⟨hd₃, hpos₃, hple₃⟩ := readBits_inv br₂ br₃ 4 hclen_val hrb3_eq hpos₂ hple₂
        -- readCLCodeLengths
        split at h
        · simp at h
        · rename_i v₄ hrcl_eq
          obtain ⟨clLengths, br₄⟩ := v₄; simp only [] at hrcl_eq h
          have ⟨hd₄, hpos₄, hple₄⟩ := readCLCodeLengths_inv br₃ br₄ _ clLengths _ _ hrcl_eq hpos₃ hple₃
          -- HuffTree.fromLengths (pure, no BitReader change)
          split at h
          · simp at h
          · rename_i clTree _
            -- decodeCLSymbols
            split at h
            · simp at h
            · rename_i v₅ hdcl_eq
              obtain ⟨codeLengths, br₅⟩ := v₅; simp only [] at hdcl_eq h
              have ⟨hd₅, hpos₅, hple₅⟩ := decodeCLSymbols_inv clTree br₄ br₅
                _ codeLengths _ _ _ hdcl_eq hpos₄ hple₄
              -- HuffTree.fromLengths (litTree) — pure
              split at h
              · simp at h
              · rename_i litTree' _
                -- HuffTree.fromLengths (distTree) — pure
                split at h
                · simp at h
                · rename_i distTree' _
                  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
                  obtain ⟨_, _, rfl⟩ := h
                  exact ⟨hd₅.trans (hd₄.trans (hd₃.trans (hd₂.trans hd₁))),
                         hpos₅, hple₅⟩

end Zip.Native
