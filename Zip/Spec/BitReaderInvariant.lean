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

/-- `readBit` preserves the data field. -/
private theorem readBit_data_eq (br br' : BitReader) (bit : UInt32)
    (h : br.readBit = .ok (bit, br')) : br'.data = br.data := by
  simp only [BitReader.readBit] at h
  split at h
  · exact nomatch h
  · split at h <;> simp only [Except.ok.injEq, Prod.mk.injEq] at h <;>
      obtain ⟨_, rfl⟩ := h <;> rfl

/-- `readBits.go` preserves the data field. -/
private theorem readBits_go_data_eq (br br' : BitReader) (acc : UInt32)
    (shift n : Nat) (val : UInt32)
    (h : BitReader.readBits.go br acc shift n = .ok (val, br')) :
    br'.data = br.data := by
  induction n generalizing br acc shift with
  | zero =>
    simp only [BitReader.readBits.go] at h
    obtain ⟨_, rfl⟩ := h; rfl
  | succ n ih =>
    simp only [BitReader.readBits.go, bind, Except.bind] at h
    cases hrb : br.readBit with
    | error e => simp only [hrb] at h; exact nomatch h
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
  · exact nomatch h
  · rename_i hlt
    split at h <;> simp only [Except.ok.injEq, Prod.mk.injEq] at h <;>
      obtain ⟨_, rfl⟩ := h <;> dsimp only <;> omega

/-- `readBits.go` preserves the hpos invariant. -/
private theorem readBits_go_hpos (br br' : BitReader) (acc : UInt32)
    (shift n : Nat) (val : UInt32)
    (h : BitReader.readBits.go br acc shift n = .ok (val, br'))
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size) :
    br'.bitOff = 0 ∨ br'.pos < br'.data.size := by
  induction n generalizing br acc shift with
  | zero =>
    simp only [BitReader.readBits.go] at h
    obtain ⟨_, rfl⟩ := h; exact hpos
  | succ n ih =>
    simp only [BitReader.readBits.go, bind, Except.bind] at h
    cases hrb : br.readBit with
    | error e => simp only [hrb] at h; exact nomatch h
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
    | inl h => exact absurd (by rw [h]; decide) hne
    | inr h => dsimp only; omega

/-! ### BitReader bitPos advancement

`readBit` advances `bitPos` by exactly 1, and `readBits n` advances by exactly `n`.
These are characterizing properties — they describe the quantitative behavior
of the BitReader, not just invariant preservation. -/

/-- A successful `readBit` always produces `bitOff < 8`. -/
private theorem readBit_bitOff_lt (br br' : BitReader) (bit : UInt32)
    (h : br.readBit = .ok (bit, br')) :
    br'.bitOff < 8 := by
  simp only [BitReader.readBit] at h
  split at h
  · exact nomatch h
  · split at h <;> simp only [Except.ok.injEq, Prod.mk.injEq] at h <;>
      obtain ⟨_, rfl⟩ := h <;> dsimp only <;> omega

/-- Reading one bit advances bitPos by exactly 1 (requires `bitOff < 8`). -/
theorem readBit_bitPos_eq (br br' : BitReader) (bit : UInt32)
    (h : br.readBit = .ok (bit, br'))
    (hbo : br.bitOff < 8) :
    br'.bitPos = br.bitPos + 1 := by
  simp only [BitReader.readBit] at h
  split at h
  · exact nomatch h
  · split at h <;> simp only [Except.ok.injEq, Prod.mk.injEq] at h <;>
      obtain ⟨_, rfl⟩ := h <;> simp only [BitReader.bitPos] <;> omega

/-- `readBits.go` reading `n` bits advances bitPos by exactly `n`. -/
private theorem readBits_go_bitPos_eq (br br' : BitReader)
    (acc : UInt32) (shift n : Nat) (val : UInt32)
    (h : BitReader.readBits.go br acc shift n = .ok (val, br'))
    (hbo : br.bitOff < 8) :
    br'.bitPos = br.bitPos + n := by
  induction n generalizing br acc shift with
  | zero =>
    simp only [BitReader.readBits.go] at h
    obtain ⟨_, rfl⟩ := h; omega
  | succ n ih =>
    simp only [BitReader.readBits.go, bind, Except.bind] at h
    cases hrb : br.readBit with
    | error e => simp only [hrb] at h; exact nomatch h
    | ok p =>
      obtain ⟨bit, br₁⟩ := p
      simp only [hrb] at h
      have hbo₁ := readBit_bitOff_lt br br₁ bit hrb
      have h₁ := readBit_bitPos_eq br br₁ bit hrb hbo
      have h₂ := ih br₁ _ _ h hbo₁
      omega

/-- Reading `n` bits advances bitPos by exactly `n` (requires `bitOff < 8`). -/
theorem readBits_bitPos_eq (br br' : BitReader) (n : Nat)
    (val : UInt32) (h : br.readBits n = .ok (val, br'))
    (hbo : br.bitOff < 8) :
    br'.bitPos = br.bitPos + n :=
  readBits_go_bitPos_eq br br' 0 0 n val h hbo

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
  · exact nomatch h
  · rename_i hlt
    split at h <;> simp only [Except.ok.injEq, Prod.mk.injEq] at h <;>
      obtain ⟨_, rfl⟩ := h <;> dsimp only <;> (exact ⟨rfl, by omega, by omega⟩)

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
    simp only [BitReader.readBits.go] at h
    obtain ⟨_, rfl⟩ := h; exact ⟨rfl, hpos, hple⟩
  | succ n ih =>
    simp only [BitReader.readBits.go, bind, Except.bind] at h
    cases hrb : br.readBit with
    | error e => simp only [hrb] at h; exact nomatch h
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
    simp only [HuffTree.decode.go] at h
    obtain ⟨_, rfl⟩ := h; exact ⟨rfl, hpos, hple⟩
  | empty => simp only [HuffTree.decode.go] at h; exact nomatch h
  | node z o ihz iho =>
    simp only [HuffTree.decode.go] at h
    split at h
    · exact nomatch h
    · simp only [bind, Except.bind] at h
      cases hrb : br.readBit with
      | error e => simp only [hrb] at h; exact nomatch h
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
    · exact nomatch h
    · next hle =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h
      have hbo' : br.bitOff = 0 := eq_of_beq hbo
      exact ⟨rfl, hbo', by dsimp [BitReader.data, BitReader.pos] at hle ⊢; omega⟩
  next hbo =>
    split at h
    · exact nomatch h
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
    · exact nomatch h
    · next hle =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h
      have hbo' : br.bitOff = 0 := eq_of_beq hbo
      exact ⟨rfl, hbo', by dsimp [BitReader.data, BitReader.pos] at hle ⊢; omega⟩
  next hbo =>
    split at h
    · exact nomatch h
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
  | .error e => simp only [h1] at h; exact nomatch h
  | .ok (len, br₁) =>
    simp only [h1] at h
    match h2 : br₁.readUInt16LE with
    | .error e => simp only [h2] at h; exact nomatch h
    | .ok (nlen, br₂) =>
      simp only [h2] at h
      have h_rb : ∃ bytes, br₂.readBytes len.toNat = .ok (bytes, br') := by
        revert h; intro h
        simp only [pure, Except.pure] at h
        by_cases hxor : (len ^^^ nlen != 0xFFFF) = true
        · simp only [hxor, ite_true] at h; exact nomatch h
        · simp only [hxor] at h
          by_cases hsize : output.size + len.toNat > maxOut
          · simp only [hsize, ite_true] at h; exact nomatch h
          · simp only [hsize, ite_false] at h
            match h3 : br₂.readBytes len.toNat with
            | .error e => simp only [h3] at h; exact nomatch h
            | .ok (bytes, br₃) =>
              simp only [h3, if_neg Bool.false_ne_true, Except.ok.injEq,
                Prod.mk.injEq] at h
              exact ⟨bytes, by rw [h.2]⟩
      obtain ⟨bytes, h_rb⟩ := h_rb
      have ⟨hd3, hbo3, hple3⟩ := readBytes_inv br₂ br' _ _ h_rb
      have ⟨hd1, _, _⟩ := readUInt16LE_inv br br₁ _ h1
      have ⟨hd2, _, _⟩ := readUInt16LE_inv br₁ br₂ _ h2
      exact ⟨hd3.trans (hd2.trans hd1), Or.inl hbo3, hple3⟩

/-- Combined: decodeHuffman.go preserves data, hpos, and pos ≤ data.size. -/
theorem decodeHuffman_go_inv (litTree distTree : HuffTree)
    (br br' : BitReader) (output output' : ByteArray)
    (maxOut dataSize : Nat)
    (h : Inflate.decodeHuffman.go litTree distTree maxOut dataSize br output =
      .ok (output', br'))
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (hple : br.pos ≤ br.data.size) :
    br'.data = br.data ∧
    (br'.bitOff = 0 ∨ br'.pos < br'.data.size) ∧
    br'.pos ≤ br'.data.size := by
  -- WF induction on the termination measure
  have hrec : ∀ (br_i : BitReader) (out : ByteArray),
      dataSize * 8 - br_i.bitPos < dataSize * 8 - br.bitPos →
      Inflate.decodeHuffman.go litTree distTree maxOut dataSize br_i out =
        .ok (output', br') →
      (br_i.bitOff = 0 ∨ br_i.pos < br_i.data.size) →
      br_i.pos ≤ br_i.data.size →
      br'.data = br_i.data ∧
      (br'.bitOff = 0 ∨ br'.pos < br'.data.size) ∧
      br'.pos ≤ br'.data.size :=
    fun br_i out hlt h' hpos' hple' =>
      decodeHuffman_go_inv litTree distTree br_i br' out output' maxOut dataSize h' hpos' hple'
  unfold Inflate.decodeHuffman.go at h
  cases hlit : litTree.decode br with
  | error e => rw [hlit] at h; simp only [Bind.bind, Except.bind] at h; exact nomatch h
  | ok p =>
    obtain ⟨sym, br₁⟩ := p; rw [hlit] at h; dsimp only [Bind.bind, Except.bind] at h
    simp only [pure, Except.pure] at h
    have ⟨hd₁, hpos₁, hple₁⟩ := decode_inv litTree br br₁ sym hlit hpos hple
    split at h
    · -- sym < 256: literal byte
      split at h
      · exact nomatch h  -- output.size ≥ maxOut → error
      · -- advancement guards
        split at h
        · exact nomatch h  -- bitPos ≤ guard → error
        · split at h
          · exact nomatch h  -- bitPos out of range → error
          · -- recursive call: have advancement + bound from passed guards
            have hmeasure : dataSize * 8 - br₁.bitPos < dataSize * 8 - br.bitPos := by
              simp only [BitReader.bitPos] at *; omega
            have ⟨hd', hp', hl'⟩ := hrec br₁ _ hmeasure h hpos₁ hple₁
            exact ⟨hd'.trans hd₁, hp', hl'⟩
    · split at h
      · -- sym == 256: end of block
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl⟩ := h
        exact ⟨hd₁, hpos₁, hple₁⟩
      · -- sym ≥ 257: length+distance code
        split at h
        · exact nomatch h  -- invalid length code → error
        · split at h
          · exact nomatch h  -- readBits error
          · rename_i v hrb1_eq
            split at h
            · exact nomatch h  -- decode dist error
            · rename_i v₁ hdist_eq
              split at h
              · exact nomatch h  -- invalid distance code
              · split at h
                · exact nomatch h  -- readBits dist extra error
                · rename_i v₂ hrb2_eq
                  split at h
                  · exact nomatch h  -- distance = 0
                  · split at h
                    · exact nomatch h  -- distance > output.size
                    · split at h
                      · exact nomatch h  -- output.size + length > maxOut
                      · -- advancement guards before recursive call
                        split at h
                        · exact nomatch h  -- bitPos ≤ guard → error
                        · split at h
                          · exact nomatch h  -- bitPos out of range → error
                          · -- recursive go call remains
                            obtain ⟨extraBits, br₂⟩ := v
                            obtain ⟨distSym, br₃⟩ := v₁
                            obtain ⟨dExtraBits, br₄⟩ := v₂
                            simp only [] at hrb1_eq hdist_eq hrb2_eq h
                            have ⟨hd₂, hpos₂, hple₂⟩ := readBits_inv br₁ br₂ _ _ hrb1_eq hpos₁ hple₁
                            have ⟨hd₃, hpos₃, hple₃⟩ := decode_inv distTree br₂ br₃ distSym hdist_eq hpos₂ hple₂
                            have ⟨hd₄, hpos₄, hple₄⟩ := readBits_inv br₃ br₄ _ _ hrb2_eq hpos₃ hple₃
                            have hmeasure : dataSize * 8 - br₄.bitPos < dataSize * 8 - br.bitPos := by
                              simp only [BitReader.bitPos] at *; omega
                            have ⟨hd', hp', hl'⟩ := hrec br₄ _ hmeasure h hpos₄ hple₄
                            exact ⟨hd'.trans (hd₄.trans (hd₃.trans (hd₂.trans hd₁))), hp', hl'⟩
termination_by dataSize * 8 - br.bitPos

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
    · split at h
      · simp only [bind, Except.bind] at h
        cases hrb : br.readBits 3 with
        | error e => simp only [hrb] at h; exact nomatch h
        | ok p =>
          obtain ⟨v, br₁⟩ := p; simp only [hrb] at h
          have ⟨hd₁, hpos₁, hple₁⟩ := readBits_inv br br₁ 3 v hrb hpos hple
          have ⟨hd', hp', hl'⟩ := ih br₁ _ (i + 1) ncl (by omega) h hpos₁ hple₁
          exact ⟨hd'.trans hd₁, hp', hl'⟩
      · exact nomatch h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h; exact ⟨rfl, hpos, hple⟩

/-- Combined: decodeCLSymbols preserves data, hpos, and pos ≤ data.size. -/
theorem decodeCLSymbols_inv (clTree : HuffTree) (br br' : BitReader)
    (codeLengths codeLengths' : Array UInt8) (idx totalCodes : Nat)
    (h : Inflate.decodeCLSymbols clTree br codeLengths idx totalCodes =
      .ok (codeLengths', br'))
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (hple : br.pos ≤ br.data.size) :
    br'.data = br.data ∧
    (br'.bitOff = 0 ∨ br'.pos < br'.data.size) ∧
    br'.pos ≤ br'.data.size := by
  have hrec : ∀ (idx' : Nat) (br_i : BitReader) (cl : Array UInt8),
      totalCodes - idx' < totalCodes - idx →
      Inflate.decodeCLSymbols clTree br_i cl idx' totalCodes = .ok (codeLengths', br') →
      (br_i.bitOff = 0 ∨ br_i.pos < br_i.data.size) →
      br_i.pos ≤ br_i.data.size →
      br'.data = br_i.data ∧
      (br'.bitOff = 0 ∨ br'.pos < br'.data.size) ∧
      br'.pos ≤ br'.data.size :=
    fun idx' br_i cl hlt h' hpos' hple' =>
      decodeCLSymbols_inv clTree br_i br' cl codeLengths' idx' totalCodes h' hpos' hple'
  unfold Inflate.decodeCLSymbols at h
  split at h
  · -- idx ≥ totalCodes: return
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h; exact ⟨rfl, hpos, hple⟩
  · -- idx < totalCodes: do block
    rename_i hlt
    dsimp only [Bind.bind, Except.bind] at h
    split at h
    · exact nomatch h  -- decode error
    · rename_i v hdec_eq
      simp only [pure, Except.pure] at h
      obtain ⟨sym, br₁⟩ := v; simp only [] at hdec_eq h
      have ⟨hd₁, hpos₁, hple₁⟩ := decode_inv clTree br br₁ sym hdec_eq hpos hple
      split at h
      · -- sym < 16: literal code length
        have ⟨hd', hp', hl'⟩ := hrec _ br₁ _ (by omega) h hpos₁ hple₁
        exact ⟨hd'.trans hd₁, hp', hl'⟩
      · split at h
        · -- sym == 16: repeat previous
          split at h
          · exact nomatch h  -- idx == 0 error
          · -- idx ≠ 0
            split at h
            · -- idx - 1 < codeLengths.size
              -- readBits 2
              split at h
              · exact nomatch h  -- readBits error
              · rename_i v₁ hrb_eq
                obtain ⟨rep, br₂⟩ := v₁; simp only [] at hrb_eq h
                have ⟨hd₂, hpos₂, hple₂⟩ := readBits_inv br₁ br₂ 2 rep hrb_eq hpos₁ hple₁
                split at h
                · exact nomatch h  -- repeat exceeds total
                · have ⟨hd', hp', hl'⟩ := hrec _ br₂ _ (by omega) h hpos₂ hple₂
                  exact ⟨hd'.trans (hd₂.trans hd₁), hp', hl'⟩
            · exact nomatch h  -- idx out of bounds error
        · split at h
          · -- sym == 17: zero-fill short
            split at h
            · exact nomatch h  -- readBits error
            · rename_i v₂ hrb_eq
              obtain ⟨rep, br₂⟩ := v₂; simp only [] at hrb_eq h
              have ⟨hd₂, hpos₂, hple₂⟩ := readBits_inv br₁ br₂ 3 rep hrb_eq hpos₁ hple₁
              split at h
              · exact nomatch h  -- repeat exceeds total
              · have ⟨hd', hp', hl'⟩ := hrec _ br₂ _ (by omega) h hpos₂ hple₂
                exact ⟨hd'.trans (hd₂.trans hd₁), hp', hl'⟩
          · split at h
            · -- sym == 18: zero-fill long
              split at h
              · exact nomatch h  -- readBits error
              · rename_i v₃ hrb_eq
                obtain ⟨rep, br₂⟩ := v₃; simp only [] at hrb_eq h
                have ⟨hd₂, hpos₂, hple₂⟩ := readBits_inv br₁ br₂ 7 rep hrb_eq hpos₁ hple₁
                split at h
                · exact nomatch h  -- repeat exceeds total
                · have ⟨hd', hp', hl'⟩ := hrec _ br₂ _ (by omega) h hpos₂ hple₂
                  exact ⟨hd'.trans (hd₂.trans hd₁), hp', hl'⟩
            · exact nomatch h  -- invalid symbol
termination_by totalCodes - idx

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
  · exact nomatch h
  · rename_i v₁ hrb1_eq
    obtain ⟨hlit_val, br₁⟩ := v₁; simp only [] at hrb1_eq h
    have ⟨hd₁, hpos₁, hple₁⟩ := readBits_inv br br₁ 5 hlit_val hrb1_eq hpos hple
    -- readBits 5 (hdist)
    split at h
    · exact nomatch h
    · rename_i v₂ hrb2_eq
      obtain ⟨hdist_val, br₂⟩ := v₂; simp only [] at hrb2_eq h
      have ⟨hd₂, hpos₂, hple₂⟩ := readBits_inv br₁ br₂ 5 hdist_val hrb2_eq hpos₁ hple₁
      -- readBits 4 (hclen)
      split at h
      · exact nomatch h
      · rename_i v₃ hrb3_eq
        obtain ⟨hclen_val, br₃⟩ := v₃; simp only [] at hrb3_eq h
        have ⟨hd₃, hpos₃, hple₃⟩ := readBits_inv br₂ br₃ 4 hclen_val hrb3_eq hpos₂ hple₂
        -- readCLCodeLengths
        split at h
        · exact nomatch h
        · rename_i v₄ hrcl_eq
          obtain ⟨clLengths, br₄⟩ := v₄; simp only [] at hrcl_eq h
          have ⟨hd₄, hpos₄, hple₄⟩ := readCLCodeLengths_inv br₃ br₄ _ clLengths _ _ hrcl_eq hpos₃ hple₃
          -- HuffTree.fromLengths (pure, no BitReader change)
          split at h
          · exact nomatch h
          · rename_i clTree _
            -- decodeCLSymbols
            split at h
            · exact nomatch h
            · rename_i v₅ hdcl_eq
              obtain ⟨codeLengths, br₅⟩ := v₅; simp only [] at hdcl_eq h
              have ⟨hd₅, hpos₅, hple₅⟩ := decodeCLSymbols_inv clTree br₄ br₅
                _ codeLengths _ _ hdcl_eq hpos₄ hple₄
              -- HuffTree.fromLengths (litTree) — pure
              split at h
              · exact nomatch h
              · rename_i litTree' _
                -- HuffTree.fromLengths (distTree) — pure
                split at h
                · exact nomatch h
                · rename_i distTree' _
                  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
                  obtain ⟨_, _, rfl⟩ := h
                  exact ⟨hd₅.trans (hd₄.trans (hd₃.trans (hd₂.trans hd₁))),
                         hpos₅, hple₅⟩

/-! ### BitReader pos_le_size — unconditional position bounds

`readBit` and `readBits` guarantee `pos ≤ data.size` on success.
`readBit_pos_le_size` is fully unconditional — the success of `readBit`
implies the guard `pos < data.size` passed. `readBits_pos_le_size`
requires `br.pos ≤ br.data.size` for the `n = 0` base case (which
returns the reader unchanged). -/

/-- After a successful `readBit`, the resulting `pos ≤ data.size`. Unconditional. -/
theorem readBit_pos_le_size (br br' : BitReader) (bit : UInt32)
    (h : br.readBit = .ok (bit, br')) :
    br'.pos ≤ br'.data.size := by
  simp only [BitReader.readBit] at h
  split at h
  · exact nomatch h
  · rename_i hlt
    split at h <;> simp only [Except.ok.injEq, Prod.mk.injEq] at h <;>
      obtain ⟨_, rfl⟩ := h <;> dsimp only <;> omega

/-- `readBits.go` preserves `pos ≤ data.size`. -/
private theorem readBits_go_pos_le_size (br br' : BitReader) (acc : UInt32)
    (shift n : Nat) (val : UInt32)
    (h : BitReader.readBits.go br acc shift n = .ok (val, br'))
    (hple : br.pos ≤ br.data.size) :
    br'.pos ≤ br'.data.size := by
  induction n generalizing br acc shift with
  | zero =>
    simp only [BitReader.readBits.go] at h
    obtain ⟨_, rfl⟩ := h; exact hple
  | succ n ih =>
    simp only [BitReader.readBits.go, bind, Except.bind] at h
    cases hrb : br.readBit with
    | error e => simp only [hrb] at h; exact nomatch h
    | ok p =>
      obtain ⟨bit, br₁⟩ := p
      simp only [hrb] at h
      exact ih br₁ _ _ h (readBit_pos_le_size br br₁ bit hrb)

/-- After a successful `readBits`, the resulting `pos ≤ data.size`. -/
theorem readBits_pos_le_size (br br' : BitReader) (n : Nat)
    (val : UInt32) (h : br.readBits n = .ok (val, br'))
    (hple : br.pos ≤ br.data.size) :
    br'.pos ≤ br'.data.size :=
  readBits_go_pos_le_size br br' 0 0 n val h hple

end Zip.Native
