import Zip.Native.Inflate
import Zip.Spec.BinaryCorrect
import Zip.Spec.InflateComplete

/-!
# inflateRaw suffix invariance

If inflateRaw succeeds on `data`, it also succeeds on `data ++ suffix`
with the SAME result and endPos. This is because all BitReader operations
read bytes at positions `pos < data.size`, and appending a suffix
doesn't change those bytes.

We prove this by first establishing suffix invariance for each basic
BitReader operation, then composing through the inflate machinery.
-/

namespace Zip.Native

private theorem getElem!_ba_append_left (a b : ByteArray) (i : Nat) (h : i < a.size) :
    (a ++ b)[i]! = a[i]! := by
  rw [getElem!_pos (a ++ b) i (by simp only [ByteArray.size_append]; omega),
      getElem!_pos a i h]
  exact ByteArray.getElem_append_left h

private abbrev brAppend (br : BitReader) (suffix : ByteArray) : BitReader :=
  ⟨br.data ++ suffix, br.pos, br.bitOff⟩

/-- readBit with appended suffix produces the same result. -/
private theorem readBit_append (br : BitReader) (suffix : ByteArray)
    (bit : UInt32) (br' : BitReader)
    (h : br.readBit = .ok (bit, br')) :
    (brAppend br suffix).readBit = .ok (bit, brAppend br' suffix) := by
  simp only [brAppend, BitReader.readBit] at h ⊢
  split at h
  · exact nomatch h
  · rename_i hge
    have hlt : br.pos < br.data.size := by omega
    rw [if_neg (show ¬ br.pos ≥ (br.data ++ suffix).size from by
        simp only [ByteArray.size_append]; omega),
      getElem!_pos (br.data ++ suffix) br.pos (by simp only [ByteArray.size_append]; omega),
      ByteArray.getElem_append_left hlt]
    rw [getElem!_pos br.data br.pos hlt] at h
    split at h <;> {
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨hval, hbr'⟩ := h
      subst hbr'; subst hval
      split <;> (first | rfl | contradiction)
    }

/-- readBits.go with appended suffix produces the same result. -/
private theorem readBits_go_append (br : BitReader) (suffix : ByteArray)
    (acc : UInt32) (shift n : Nat) (val : UInt32) (br' : BitReader)
    (h : BitReader.readBits.go br acc shift n = .ok (val, br')) :
    BitReader.readBits.go (brAppend br suffix) acc shift n =
    .ok (val, brAppend br' suffix) := by
  induction n generalizing br acc shift with
  | zero =>
    simp only [brAppend, BitReader.readBits.go] at h ⊢
    obtain ⟨rfl, rfl⟩ := h; rfl
  | succ n ih =>
    simp only [BitReader.readBits.go, bind, Except.bind] at h ⊢
    cases hrb : br.readBit with
    | error e => simp only [hrb] at h; exact nomatch h
    | ok p =>
      obtain ⟨bit, br₁⟩ := p; simp only [hrb] at h
      rw [readBit_append br suffix bit br₁ hrb]
      exact ih br₁ _ _ h

/-- readBits with appended suffix produces the same result. -/
private theorem readBits_append (br : BitReader) (suffix : ByteArray)
    (n : Nat) (val : UInt32) (br' : BitReader)
    (h : br.readBits n = .ok (val, br')) :
    (brAppend br suffix).readBits n = .ok (val, brAppend br' suffix) :=
  readBits_go_append br suffix 0 0 n val br' h

/-- alignToByte with appended suffix. -/
private theorem alignToByte_append (br : BitReader) (suffix : ByteArray) :
    (brAppend br suffix).alignToByte = brAppend br.alignToByte suffix := by
  simp only [brAppend, BitReader.alignToByte]; split <;> rfl

/-- readUInt16LE with appended suffix produces the same result. -/
private theorem readUInt16LE_append (br : BitReader) (suffix : ByteArray)
    (val : UInt16) (br' : BitReader)
    (h : br.readUInt16LE = .ok (val, br')) :
    (brAppend br suffix).readUInt16LE = .ok (val, brAppend br' suffix) := by
  simp only [BitReader.readUInt16LE] at h ⊢
  rw [alignToByte_append]; simp only []
  by_cases hle : br.alignToByte.pos + 2 > br.alignToByte.data.size
  · rw [if_pos hle] at h; exact nomatch h
  · rw [if_neg hle] at h
    rw [if_neg (show ¬ br.alignToByte.pos + 2 > (br.alignToByte.data ++ suffix).size from by
      simp only [ByteArray.size_append]; omega)]
    rw [getElem!_ba_append_left _ _ _ (by omega),
        getElem!_ba_append_left _ _ _ (by omega)]
    simp only [Except.ok.injEq, Prod.mk.injEq] at h ⊢
    obtain ⟨hval, hbr'⟩ := h
    subst hbr'; constructor
    · exact hval
    · rfl

/-- readBytes with appended suffix produces the same result. -/
private theorem readBytes_append (br : BitReader) (suffix : ByteArray)
    (n : Nat) (bytes : ByteArray) (br' : BitReader)
    (h : br.readBytes n = .ok (bytes, br')) :
    (brAppend br suffix).readBytes n = .ok (bytes, brAppend br' suffix) := by
  simp only [BitReader.readBytes] at h ⊢
  rw [alignToByte_append]; simp only []
  by_cases hle : br.alignToByte.pos + n > br.alignToByte.data.size
  · rw [if_pos hle] at h; exact nomatch h
  · rw [if_neg hle] at h
    rw [if_neg (show ¬ br.alignToByte.pos + n > (br.alignToByte.data ++ suffix).size from by
      simp only [ByteArray.size_append]; omega)]
    have hext : (br.alignToByte.data ++ suffix).extract br.alignToByte.pos
        (br.alignToByte.pos + n) =
        br.alignToByte.data.extract br.alignToByte.pos (br.alignToByte.pos + n) := by
      apply ByteArray.ext
      simp only [ByteArray.data_extract, ByteArray.data_append, Array.extract_append,
        ByteArray.size_data, Array.append_right_eq_self, Array.extract_eq_empty_iff]
      omega
    rw [hext]
    simp only [Except.ok.injEq, Prod.mk.injEq] at h ⊢
    obtain ⟨hval, hbr'⟩ := h
    subst hbr'; constructor
    · exact hval
    · rfl

/-! ### Higher-level suffix invariance -/

/-- HuffTree.decode.go with appended suffix. -/
private theorem decode_go_append (tree : HuffTree) (br : BitReader) (suffix : ByteArray)
    (n : Nat) (sym : UInt16) (br' : BitReader)
    (h : HuffTree.decode.go tree br n = .ok (sym, br')) :
    HuffTree.decode.go tree (brAppend br suffix) n = .ok (sym, brAppend br' suffix) := by
  induction tree generalizing br n with
  | leaf s =>
    simp only [HuffTree.decode.go] at h ⊢
    obtain ⟨rfl, rfl⟩ := h; rfl
  | empty => simp only [HuffTree.decode.go] at h; exact nomatch h
  | node z o ihz iho =>
    simp only [HuffTree.decode.go, bind, Except.bind] at h ⊢
    split at h
    · exact nomatch h
    · rename_i hle
      rw [if_neg hle]
      cases hrb : br.readBit with
      | error e => simp only [hrb] at h; exact nomatch h
      | ok p =>
        obtain ⟨bit, br₁⟩ := p; simp only [hrb] at h
        rw [readBit_append br suffix bit br₁ hrb]; dsimp only []
        split at h
        · rw [if_pos (by assumption)]; exact ihz br₁ _ h
        · rw [if_neg (by assumption)]; exact iho br₁ _ h

/-- HuffTree.decode with appended suffix. -/
private theorem huffDecode_append (tree : HuffTree) (br : BitReader) (suffix : ByteArray)
    (sym : UInt16) (br' : BitReader)
    (h : tree.decode br = .ok (sym, br')) :
    tree.decode (brAppend br suffix) = .ok (sym, brAppend br' suffix) :=
  decode_go_append tree br suffix 0 sym br' h

/-- decodeStored with appended suffix. -/
private theorem decodeStored_append (br : BitReader) (suffix : ByteArray)
    (output : ByteArray) (maxOut : Nat) (result : ByteArray) (br' : BitReader)
    (h : Inflate.decodeStored br output maxOut = .ok (result, br')) :
    Inflate.decodeStored (brAppend br suffix) output maxOut =
      .ok (result, brAppend br' suffix) := by
  simp only [Inflate.decodeStored, bind, Except.bind] at h ⊢
  cases h1 : br.readUInt16LE with
  | error e => simp only [h1] at h; exact nomatch h
  | ok p1 =>
    obtain ⟨len, br₁⟩ := p1; simp only [h1] at h
    rw [readUInt16LE_append br suffix len br₁ h1]; dsimp only []
    cases h2 : br₁.readUInt16LE with
    | error e => simp only [h2] at h; exact nomatch h
    | ok p2 =>
      obtain ⟨nlen, br₂⟩ := p2; simp only [h2] at h
      rw [readUInt16LE_append br₁ suffix nlen br₂ h2]; dsimp only []
      by_cases hxor : (len ^^^ nlen != 65535) = true
      · rw [if_pos hxor] at h ⊢; exact nomatch h
      · rw [if_neg hxor] at h ⊢
        by_cases hmaxOut : output.size + len.toNat > maxOut
        · simp only [pure, Except.pure] at h ⊢; rw [if_pos hmaxOut] at h ⊢; exact nomatch h
        · simp only [pure, Except.pure] at h ⊢; rw [if_neg hmaxOut] at h ⊢
          cases h3 : br₂.readBytes len.toNat with
          | error e => simp only [h3] at h; exact nomatch h
          | ok p3 =>
            obtain ⟨bytes, br₃⟩ := p3; simp only [h3] at h
            rw [readBytes_append br₂ suffix len.toNat bytes br₃ h3]; dsimp only []
            simp only [Except.ok.injEq, Prod.mk.injEq] at h ⊢
            obtain ⟨hval, hbr'⟩ := h; subst hbr'; exact ⟨hval, rfl⟩

/-- readCLCodeLengths with appended suffix. -/
private theorem readCLCodeLengths_append (br : BitReader) (suffix : ByteArray)
    (clLengths : Array UInt8) (i numCodeLen : Nat)
    (result : Array UInt8) (br' : BitReader)
    (h : Inflate.readCLCodeLengths br clLengths i numCodeLen = .ok (result, br')) :
    Inflate.readCLCodeLengths (brAppend br suffix) clLengths i numCodeLen =
      .ok (result, brAppend br' suffix) := by
  unfold Inflate.readCLCodeLengths at h ⊢
  by_cases hlt : i < numCodeLen
  · rw [if_pos hlt] at h ⊢
    simp only [bind, Except.bind] at h ⊢
    cases hrb : br.readBits 3 with
    | error e => simp only [hrb] at h; exact nomatch h
    | ok p =>
      obtain ⟨v, br₁⟩ := p; simp only [hrb] at h
      rw [readBits_append br suffix 3 v br₁ hrb]; dsimp only []
      exact readCLCodeLengths_append br₁ suffix _ (i + 1) numCodeLen result br' h
  · rw [if_neg hlt] at h ⊢
    simp only [Except.ok.injEq, Prod.mk.injEq] at h ⊢
    obtain ⟨hval, hbr'⟩ := h; subst hbr'; exact ⟨hval, rfl⟩
termination_by numCodeLen - i

/-- decodeCLSymbols with appended suffix. -/
private theorem decodeCLSymbols_append (clTree : HuffTree) (br : BitReader) (suffix : ByteArray)
    (codeLengths : Array UInt8) (idx totalCodes : Nat)
    (result : Array UInt8) (br' : BitReader)
    (h : Inflate.decodeCLSymbols clTree br codeLengths idx totalCodes =
      .ok (result, br')) :
    Inflate.decodeCLSymbols clTree (brAppend br suffix) codeLengths idx totalCodes =
      .ok (result, brAppend br' suffix) := by
  have hrec : ∀ (idx' : Nat) (br_i : BitReader) (cl : Array UInt8),
      totalCodes - idx' < totalCodes - idx →
      Inflate.decodeCLSymbols clTree br_i cl idx' totalCodes = .ok (result, br') →
      Inflate.decodeCLSymbols clTree (brAppend br_i suffix) cl idx' totalCodes =
        .ok (result, brAppend br' suffix) :=
    fun idx' br_i cl hlt h' =>
      decodeCLSymbols_append clTree br_i suffix cl idx' totalCodes result br' h'
  unfold Inflate.decodeCLSymbols at h ⊢
  by_cases hge : idx ≥ totalCodes
  · rw [if_pos hge] at h ⊢
    simp only [Except.ok.injEq, Prod.mk.injEq] at h ⊢
    obtain ⟨hval, hbr'⟩ := h; subst hbr'; exact ⟨hval, rfl⟩
  · rw [if_neg hge] at h ⊢
    simp only [bind, Except.bind] at h ⊢
    cases hd : clTree.decode br with
    | error e => simp only [hd] at h; exact nomatch h
    | ok p =>
      obtain ⟨sym, br₁⟩ := p; simp only [hd] at h
      rw [huffDecode_append clTree br suffix sym br₁ hd]; dsimp only []
      by_cases hs16 : sym < 16
      · rw [if_pos hs16] at h ⊢; exact hrec _ br₁ _ (by omega) h
      · rw [if_neg hs16] at h ⊢
        by_cases hs16eq : (sym == 16) = true
        · rw [if_pos hs16eq] at h ⊢
          by_cases hidx0 : (idx == 0) = true
          · rw [if_pos hidx0] at h ⊢; exact nomatch h
          · rw [if_neg hidx0] at h ⊢
            simp only [pure, Except.pure] at h ⊢
            cases hrb : br₁.readBits 2 with
            | error e => simp only [hrb] at h; exact nomatch h
            | ok p =>
              obtain ⟨rep, br₂⟩ := p; simp only [hrb] at h
              rw [readBits_append br₁ suffix 2 rep br₂ hrb]; dsimp only []
              by_cases hgt : idx + (rep.toNat + 3) > totalCodes
              · rw [if_pos hgt] at h ⊢; exact nomatch h
              · rw [if_neg hgt] at h ⊢
                exact hrec _ br₂ _ (by omega) h
        · rw [if_neg hs16eq] at h ⊢
          by_cases hs17 : (sym == 17) = true
          · rw [if_pos hs17] at h ⊢
            cases hrb : br₁.readBits 3 with
            | error e => simp only [hrb] at h; exact nomatch h
            | ok p =>
              obtain ⟨rep, br₂⟩ := p; simp only [hrb] at h
              rw [readBits_append br₁ suffix 3 rep br₂ hrb]; dsimp only []
              by_cases hgt : idx + (rep.toNat + 3) > totalCodes
              · rw [if_pos hgt] at h ⊢; exact nomatch h
              · rw [if_neg hgt] at h ⊢
                simp only [pure, Except.pure] at h ⊢
                exact hrec _ br₂ _ (by omega) h
          · rw [if_neg hs17] at h ⊢
            by_cases hs18 : (sym == 18) = true
            · rw [if_pos hs18] at h ⊢
              cases hrb : br₁.readBits 7 with
              | error e => simp only [hrb] at h; exact nomatch h
              | ok p =>
                obtain ⟨rep, br₂⟩ := p; simp only [hrb] at h
                rw [readBits_append br₁ suffix 7 rep br₂ hrb]; dsimp only []
                by_cases hgt : idx + (rep.toNat + 11) > totalCodes
                · rw [if_pos hgt] at h ⊢; exact nomatch h
                · rw [if_neg hgt] at h ⊢
                  exact hrec _ br₂ _ (by omega) h
            · rw [if_neg hs18] at h ⊢; exact nomatch h
termination_by totalCodes - idx

/-- decodeDynamicTrees with appended suffix. -/
private theorem decodeDynamicTrees_append (br : BitReader) (suffix : ByteArray)
    (litTree distTree : HuffTree) (br' : BitReader)
    (h : Inflate.decodeDynamicTrees br = .ok (litTree, distTree, br')) :
    Inflate.decodeDynamicTrees (brAppend br suffix) =
      .ok (litTree, distTree, brAppend br' suffix) := by
  unfold Inflate.decodeDynamicTrees at h ⊢
  simp only [bind, Except.bind] at h ⊢
  -- readBits 5 (hlit)
  cases hlit_eq : br.readBits 5 with
  | error e => simp only [hlit_eq] at h; exact nomatch h
  | ok p =>
    obtain ⟨hlit, br₁⟩ := p; simp only [hlit_eq] at h
    rw [readBits_append br suffix 5 hlit br₁ hlit_eq]; dsimp only []
    -- readBits 5 (hdist)
    cases hdist_eq : br₁.readBits 5 with
    | error e => simp only [hdist_eq] at h; exact nomatch h
    | ok p =>
      obtain ⟨hdist, br₂⟩ := p; simp only [hdist_eq] at h
      rw [readBits_append br₁ suffix 5 hdist br₂ hdist_eq]; dsimp only []
      -- readBits 4 (hclen)
      cases hclen_eq : br₂.readBits 4 with
      | error e => simp only [hclen_eq] at h; exact nomatch h
      | ok p =>
        obtain ⟨hclen, br₃⟩ := p; simp only [hclen_eq] at h
        rw [readBits_append br₂ suffix 4 hclen br₃ hclen_eq]; dsimp only []
        -- readCLCodeLengths
        cases hcl_eq : Inflate.readCLCodeLengths br₃ (.replicate 19 0) 0
            (hclen.toNat + 4) with
        | error e => simp only [hcl_eq] at h; exact nomatch h
        | ok p =>
          obtain ⟨clLengths, br₄⟩ := p; simp only [hcl_eq] at h
          rw [readCLCodeLengths_append br₃ suffix (.replicate 19 0) 0
              (hclen.toNat + 4) clLengths br₄ hcl_eq]; dsimp only []
          -- HuffTree.fromLengths clLengths (pure, no BitReader)
          cases hft_eq : HuffTree.fromLengths clLengths 7 with
          | error e => simp only [hft_eq] at h; exact nomatch h
          | ok clTree =>
            simp only [hft_eq] at h; dsimp only [] at h ⊢
            -- decodeCLSymbols
            cases hcls_eq : Inflate.decodeCLSymbols clTree br₄
                (.replicate (hlit.toNat + 257 + (hdist.toNat + 1)) 0) 0
                (hlit.toNat + 257 + (hdist.toNat + 1)) with
            | error e => simp only [hcls_eq] at h; exact nomatch h
            | ok p =>
              obtain ⟨codeLengths, br₅⟩ := p; simp only [hcls_eq] at h
              rw [decodeCLSymbols_append clTree br₄ suffix
                  (.replicate (hlit.toNat + 257 + (hdist.toNat + 1)) 0) 0
                  (hlit.toNat + 257 + (hdist.toNat + 1))
                  codeLengths br₅ hcls_eq]; dsimp only []
              -- fromLengths litLenLengths (pure)
              cases hlt_eq : HuffTree.fromLengths (codeLengths.extract 0 (hlit.toNat + 257)) with
              | error e => simp only [hlt_eq] at h; exact nomatch h
              | ok litTree' =>
                simp only [hlt_eq] at h; dsimp only [] at h ⊢
                -- fromLengths distLengths (pure)
                cases hdt_eq : HuffTree.fromLengths
                    (codeLengths.extract (hlit.toNat + 257)
                      (hlit.toNat + 257 + (hdist.toNat + 1))) with
                | error e => simp only [hdt_eq] at h; exact nomatch h
                | ok distTree' =>
                  simp only [hdt_eq] at h; dsimp only [] at h ⊢
                  simp only [pure, Except.pure] at h ⊢
                  have hinj := Except.ok.inj h
                  simp only [Prod.mk.injEq] at hinj
                  obtain ⟨h1, h2, h3⟩ := hinj
                  subst h1; subst h2; subst h3; rfl

set_option maxRecDepth 4096 in
/-- decodeHuffman.go with appended suffix. -/
private theorem decodeHuffman_go_append (litTree distTree : HuffTree)
    (br : BitReader) (suffix : ByteArray) (output : ByteArray)
    (maxOut dataSize dataSize' : Nat)
    (result : ByteArray) (br' : BitReader)
    (hds : dataSize ≤ dataSize')
    (h : Inflate.decodeHuffman.go litTree distTree maxOut dataSize br output =
      .ok (result, br')) :
    Inflate.decodeHuffman.go litTree distTree maxOut dataSize' (brAppend br suffix) output =
      .ok (result, brAppend br' suffix) := by
  unfold Inflate.decodeHuffman.go at h
  simp only [bind, Except.bind] at h
  cases hdec : litTree.decode br with
  | error e => simp only [hdec] at h; exact nomatch h
  | ok p =>
    obtain ⟨sym, br₁⟩ := p; simp only [hdec] at h
    unfold Inflate.decodeHuffman.go
    rw [huffDecode_append litTree br suffix sym br₁ hdec]
    simp only [bind, Except.bind]
    split at h
    · -- sym < 256: literal byte
      rename_i hsym; rw [if_pos hsym]
      split at h
      · exact nomatch h
      · rename_i hout; rw [if_neg hout]
        simp only [pure, Except.pure] at h ⊢
        split at h
        · exact nomatch h
        · rename_i h₁
          split at h
          · exact nomatch h
          · rename_i h₂
            have : (brAppend br₁ suffix).bitPos = br₁.bitPos := rfl
            split
            · rename_i h₁'; exact absurd h₁' h₁
            · split
              · rename_i h₂'; exfalso; exact h₂ (by omega)
              · exact decodeHuffman_go_append litTree distTree br₁ suffix
                  (output.push sym.toUInt8) maxOut dataSize dataSize' result br' hds h
    · -- sym ≥ 256
      split at h
      · -- sym == 256: end of block
        rename_i hge hsym256
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [if_neg hge, if_pos hsym256]
      · -- sym > 256: length/distance code
        rename_i hge hne256
        rw [if_neg hge, if_neg hne256]
        split at h
        · exact nomatch h
        · rename_i hidx; rw [if_neg hidx]
          simp only [pure, Except.pure] at h ⊢
          cases hextra_r : br₁.readBits (Inflate.lengthExtra[sym.toNat - 257]!).toNat with
          | error e => simp only [hextra_r] at h; exact nomatch h
          | ok p =>
            obtain ⟨extraBits, br₂⟩ := p; simp only [hextra_r] at h
            rw [readBits_append br₁ suffix _ extraBits br₂ hextra_r]; dsimp only []
            cases hdist_dec : distTree.decode br₂ with
            | error e => simp only [hdist_dec] at h; exact nomatch h
            | ok p =>
              obtain ⟨distSym, br₃⟩ := p; simp only [hdist_dec] at h
              rw [huffDecode_append distTree br₂ suffix distSym br₃ hdist_dec]; dsimp only []
              split at h
              · exact nomatch h
              · rename_i hdidx; rw [if_neg hdidx]
                cases hdextra_r : br₃.readBits (Inflate.distExtra[distSym.toNat]!).toNat with
                | error e => simp only [hdextra_r] at h; exact nomatch h
                | ok p =>
                  obtain ⟨dExtraBits, br₄⟩ := p; simp only [hdextra_r] at h
                  rw [readBits_append br₃ suffix _ dExtraBits br₄ hdextra_r]; dsimp only []
                  split at h
                  · exact nomatch h
                  · rename_i hdist_ok; rw [if_neg hdist_ok]
                    split at h
                    · exact nomatch h
                    · rename_i hmax_ok; rw [if_neg hmax_ok]
                      split at h
                      · exact nomatch h
                      · rename_i h₁
                        split at h
                        · exact nomatch h
                        · rename_i h₂
                          have : (brAppend br₄ suffix).bitPos = br₄.bitPos := rfl
                          split
                          · rename_i h₁'; exact absurd h₁' h₁
                          · split
                            · rename_i h₂'; exfalso; exact h₂ (by omega)
                            · exact decodeHuffman_go_append litTree distTree br₄ suffix
                                _ maxOut dataSize dataSize' result br' hds h
  termination_by dataSize * 8 - br.bitPos

/-- inflateLoop with appended suffix. -/
private theorem inflateLoop_append_suffix (br : BitReader) (suffix : ByteArray)
    (output : ByteArray) (fixedLit fixedDist : HuffTree) (maxOut dataSize : Nat)
    (result : ByteArray) (endPos : Nat)
    (h : Inflate.inflateLoop br output fixedLit fixedDist maxOut dataSize =
      .ok (result, endPos)) :
    Inflate.inflateLoop (brAppend br suffix) output fixedLit fixedDist maxOut dataSize =
      .ok (result, endPos) := by
  suffices ∀ k (br : BitReader) (output : ByteArray)
      (result : ByteArray) (endPos : Nat),
      dataSize * 8 - br.bitPos ≤ k →
      Inflate.inflateLoop br output fixedLit fixedDist maxOut dataSize =
        .ok (result, endPos) →
      Inflate.inflateLoop (brAppend br suffix) output fixedLit fixedDist maxOut dataSize =
        .ok (result, endPos) from
    this _ br output result endPos Nat.le.refl h
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro br output result endPos hk h
    rw [Inflate.inflateLoop.eq_1] at h
    rw [Inflate.inflateLoop.eq_1]
    simp only [bind, Except.bind] at h ⊢
    cases hbf : br.readBits 1 with
    | error e => simp only [hbf] at h; exact nomatch h
    | ok p =>
      obtain ⟨bfinal, br₁⟩ := p; simp only [hbf] at h
      rw [readBits_append br suffix 1 bfinal br₁ hbf]; dsimp only []
      cases hbt : br₁.readBits 2 with
      | error e => simp only [hbt] at h; exact nomatch h
      | ok p =>
        obtain ⟨btype, br₂⟩ := p; simp only [hbt] at h
        rw [readBits_append br₁ suffix 2 btype br₂ hbt]; dsimp only []
        split at h <;> rename_i hbt_eq <;> (try (rw [show btype = _ from hbt_eq] at *))
        · -- btype = 0: stored block
          cases hds : Inflate.decodeStored br₂ output maxOut with
          | error e => simp only [hds] at h; exact nomatch h
          | ok v =>
            obtain ⟨out', br'⟩ := v; simp only [hds] at h
            rw [decodeStored_append br₂ suffix _ _ out' br' hds]; dsimp only []
            by_cases hbf1 : (bfinal == 1) = true
            · rw [if_pos hbf1] at h ⊢; simp only [pure, Except.pure] at h ⊢
              rw [alignToByte_append]; exact h
            · rw [if_neg hbf1] at h ⊢
              -- WF guards in h
              split at h
              · exact nomatch h
              · rename_i h_progress
                split at h
                · exact nomatch h
                · -- WF guards in goal (same conditions via brAppend preserving bitPos)
                  split
                  · rename_i h₁'; exact absurd h₁' h_progress
                  · split
                    · rename_i h₂'; exact absurd h₂' (by assumption)
                    · exact ih _ (by omega) br' out' result endPos Nat.le.refl h
        · -- btype = 1: fixed Huffman
          simp only [Inflate.decodeHuffman] at h ⊢
          cases hdh : Inflate.decodeHuffman.go fixedLit fixedDist maxOut br₂.data.size br₂ output with
          | error e => simp only [hdh] at h; exact nomatch h
          | ok v =>
            obtain ⟨out', br'⟩ := v; simp only [hdh] at h
            rw [decodeHuffman_go_append fixedLit fixedDist br₂ suffix _ _ _
              (brAppend br₂ suffix).data.size out' br' (by simp only [ByteArray.size_append]; omega) hdh]
            dsimp only []
            by_cases hbf1 : (bfinal == 1) = true
            · rw [if_pos hbf1] at h ⊢; simp only [pure, Except.pure] at h ⊢
              rw [alignToByte_append]; exact h
            · rw [if_neg hbf1] at h ⊢
              split at h
              · exact nomatch h
              · rename_i h_progress
                split at h
                · exact nomatch h
                · split
                  · rename_i h₁'; exact absurd h₁' h_progress
                  · split
                    · rename_i h₂'; exact absurd h₂' (by assumption)
                    · exact ih _ (by omega) br' out' result endPos Nat.le.refl h
        · -- btype = 2: dynamic Huffman
          cases hdt : Inflate.decodeDynamicTrees br₂ with
          | error e => simp only [hdt] at h; exact nomatch h
          | ok v =>
            obtain ⟨litT, distT, br₃⟩ := v; simp only [hdt] at h
            rw [decodeDynamicTrees_append br₂ suffix litT distT br₃ hdt]; dsimp only []
            simp only [Inflate.decodeHuffman] at h ⊢
            cases hdh : Inflate.decodeHuffman.go litT distT maxOut br₃.data.size br₃ output with
            | error e => simp only [hdh] at h; exact nomatch h
            | ok v₂ =>
              obtain ⟨out', br'⟩ := v₂; simp only [hdh] at h
              rw [decodeHuffman_go_append litT distT br₃ suffix _ _ _
                (brAppend br₃ suffix).data.size out' br' (by simp only [ByteArray.size_append]; omega) hdh]
              dsimp only []
              by_cases hbf1 : (bfinal == 1) = true
              · rw [if_pos hbf1] at h ⊢; simp only [pure, Except.pure] at h ⊢
                rw [alignToByte_append]; exact h
              · rw [if_neg hbf1] at h ⊢
                split at h
                · exact nomatch h
                · rename_i h_progress
                  split at h
                  · exact nomatch h
                  · split
                    · rename_i h₁'; exact absurd h₁' h_progress
                    · split
                      · rename_i h₂'; exact absurd h₂' (by assumption)
                      · exact ih _ (by omega) br' out' result endPos Nat.le.refl h
        · -- btype ≥ 3: reserved
          exact h

/-- inflateRaw with appended suffix: if inflateRaw succeeds on data, it also
    succeeds on data ++ suffix with the same result and endPos. -/
theorem inflateRaw_append_suffix (data suffix : ByteArray) (startPos maxOut : Nat)
    (result : ByteArray) (endPos : Nat)
    (h : Inflate.inflateRaw data startPos maxOut = .ok (result, endPos)) :
    Inflate.inflateRaw (data ++ suffix) startPos maxOut = .ok (result, endPos) := by
  simp only [Inflate.inflateRaw, bind, Except.bind] at h ⊢
  cases hflit : HuffTree.fromLengths Inflate.fixedLitLengths with
  | error e => simp only [hflit] at h; exact nomatch h
  | ok fixedLit =>
    simp only [hflit] at h
    cases hfdist : HuffTree.fromLengths Inflate.fixedDistLengths with
    | error e => simp only [hfdist] at h; exact nomatch h
    | ok fixedDist =>
      simp only [hfdist] at h
      -- h has dataSize = data.size, goal has dataSize = (data ++ suffix).size
      have h' := inflateLoop_append_suffix ⟨data, startPos, 0⟩ suffix .empty
        fixedLit fixedDist maxOut data.size result endPos h
      exact Deflate.Correctness.inflateLoop_fuel_le
        ⟨data ++ suffix, startPos, 0⟩ .empty fixedLit fixedDist maxOut
        data.size (data ++ suffix).size (result, endPos)
        h' (by simp only [ByteArray.size_append]; omega)

end Zip.Native
