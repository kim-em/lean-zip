import Zip.Spec.DynamicTreesComplete

/-!
# DEFLATE Stream-Level Correctness

Proves the main correctness theorem: the native pure-Lean DEFLATE
decompressor (`Zip.Native.Inflate.inflateRaw`) agrees with the formal
bitstream specification (`Deflate.Spec.decode`).

This file handles the block loop (`inflateLoop_correct`) and the
top-level `inflate_correct` / `inflate_correct'` wrappers. Block-level
decode proofs (stored, Huffman) are in `DecodeCorrect`; dynamic tree
proofs are in `DynamicTreesCorrect`.
-/

namespace Deflate.Correctness

/-! ## Block loop helpers -/

/-- `decodeStored` preserves `bitOff < 8` and the position invariant. -/
theorem decodeStored_invariants (br : Zip.Native.BitReader) (output : ByteArray)
    (maxOutputSize : Nat) (output' : ByteArray) (br' : Zip.Native.BitReader)
    (h : Zip.Native.Inflate.decodeStored br output maxOutputSize = .ok (output', br')) :
    br'.bitOff < 8 ∧ (br'.bitOff = 0 ∨ br'.pos < br'.data.size) := by
  simp only [Zip.Native.Inflate.decodeStored, bind, Except.bind] at h
  cases h₁ : br.readUInt16LE with
  | error e => simp only [h₁] at h; exact absurd h nofun
  | ok p₁ =>
    obtain ⟨len, br₁⟩ := p₁; simp only [h₁] at h
    cases h₂ : br₁.readUInt16LE with
    | error e => simp only [h₂] at h; exact absurd h nofun
    | ok p₂ =>
      obtain ⟨nlen, br₂⟩ := p₂; simp only [h₂] at h
      split at h
      · exact absurd h nofun
      · simp only [pure, Except.pure] at h
        split at h
        · exact absurd h nofun
        · cases h₃ : br₂.readBytes len.toNat with
          | error e => simp only [h₃] at h; exact absurd h nofun
          | ok p₃ =>
            obtain ⟨bytes, br₃⟩ := p₃
            simp only [h₃, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨_, rfl⟩ := h
            have hwf := readBytes_wf br₂ len.toNat bytes br₃ h₃
            exact ⟨by omega, Or.inl hwf⟩

/-! ## Fixed code length correspondence -/

set_option maxRecDepth 2048 in
set_option maxHeartbeats 2000000 in
protected theorem Deflate.Correctness.fixedLitLengths_eq :
    (Zip.Native.Inflate.fixedLitLengths).toList.map UInt8.toNat =
    Deflate.Spec.fixedLitLengths := by rfl

set_option maxRecDepth 2048 in
protected theorem Deflate.Correctness.fixedDistLengths_eq :
    (Zip.Native.Inflate.fixedDistLengths).toList.map UInt8.toNat =
    Deflate.Spec.fixedDistLengths := by decide

set_option maxRecDepth 2048 in
protected theorem Deflate.Correctness.fixedLitLengths_size :
    Zip.Native.Inflate.fixedLitLengths.size ≤ UInt16.size := by
  show 288 ≤ 65536; omega

protected theorem Deflate.Correctness.fixedDistLengths_size :
    Zip.Native.Inflate.fixedDistLengths.size ≤ UInt16.size := by decide

/-! ## Block decode length invariants -/

/-- `readNBytes n bits acc = some (bytes, rest)` implies `rest.length + n * 8 = bits.length`. -/
private theorem readNBytes_rest_length {n : Nat} {bits : List Bool} {acc bytes : List UInt8}
    {rest : List Bool}
    (h : Deflate.Spec.decodeStored.readNBytes n bits acc = some (bytes, rest)) :
    rest.length + n * 8 = bits.length := by
  induction n generalizing bits acc with
  | zero =>
    simp only [Deflate.Spec.decodeStored.readNBytes] at h
    obtain ⟨_, rfl⟩ := h; omega
  | succ k ih =>
    simp only [Deflate.Spec.decodeStored.readNBytes] at h
    cases hrd : Deflate.Spec.readBitsLSB 8 bits with
    | none => simp only [hrd] at h; exact absurd h nofun
    | some p =>
      obtain ⟨v, bits'⟩ := p
      simp only [hrd, bind, Option.bind] at h
      have hlen := Deflate.Spec.readBitsLSB_some_length hrd
      have := ih h
      omega

/-- If `decodeStored bits = some (bytes, rest)`, then `rest.length ≤ bits.length`. -/
theorem decodeStored_rest_le {bits : List Bool} {bytes : List UInt8}
    {rest : List Bool}
    (h : Deflate.Spec.decodeStored bits = some (bytes, rest)) :
    rest.length ≤ bits.length := by
  unfold Deflate.Spec.decodeStored at h
  simp only [bind, Option.bind] at h
  have halign_len : (Deflate.Spec.alignToByte bits).length ≤ bits.length := by
    simp only [Deflate.Spec.alignToByte, List.length_drop]; omega
  cases h₁ : Deflate.Spec.readBitsLSB 16 (Deflate.Spec.alignToByte bits) with
  | none => simp only [h₁] at h; exact absurd h nofun
  | some p₁ =>
    obtain ⟨len, bits₁⟩ := p₁; simp only [h₁] at h
    have hlen₁ := Deflate.Spec.readBitsLSB_some_length h₁
    cases h₂ : Deflate.Spec.readBitsLSB 16 bits₁ with
    | none => simp only [h₂] at h; exact absurd h nofun
    | some p₂ =>
      obtain ⟨nlen, bits₂⟩ := p₂; simp only [h₂] at h
      have hlen₂ := Deflate.Spec.readBitsLSB_some_length h₂
      -- guard: split on the if
      split at h
      · exact absurd h nofun
      · simp only [] at h  -- reduce lambda application
        have hlen₃ := readNBytes_rest_length h
        omega

set_option maxRecDepth 2048 in
/-- `decodeLitLen` strictly decreases bits.length. -/
private theorem decodeLitLen_rest_lt {litLens distLens : List Nat}
    {bits : List Bool} {sym : Deflate.Spec.LZ77Symbol} {rest : List Bool}
    (h : Deflate.Spec.decodeLitLen litLens distLens bits = some (sym, rest)) :
    rest.length < bits.length := by
  unfold Deflate.Spec.decodeLitLen at h
  simp only [bind, Option.bind] at h
  -- Extract Huffman decode result
  cases hdec : Huffman.Spec.decode
      ((Huffman.Spec.allCodes litLens).map fun (sym, cw) => (cw, sym)) bits with
  | none => simp only [hdec] at h; exact absurd h nofun
  | some p =>
    obtain ⟨sym_val, bits'⟩ := p
    simp only [hdec] at h
    -- bits'.length < bits.length from decode_shorter
    have hlt := Huffman.Spec.decode_shorter _ _ _ _ hdec
        (specTable_cw_nonempty _ _)
    -- All branches return a suffix of bits' (or shorter)
    split at h
    · -- sym < 256: literal
      simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h; exact hlt
    · split at h
      · -- sym == 256: endOfBlock
        simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl⟩ := h; exact hlt
      · -- sym ≥ 257: length+distance
        -- Each read only consumes more bits from bits'
        cases h₁ : (Deflate.Spec.lengthBase[sym_val - 257]?) with
        | none => simp only [h₁] at h; exact absurd h nofun
        | some base =>
          simp only [h₁] at h
          cases h₂ : (Deflate.Spec.lengthExtra[sym_val - 257]?) with
          | none => simp only [h₂] at h; exact absurd h nofun
          | some extra =>
            simp only [h₂] at h
            cases h₃ : Deflate.Spec.readBitsLSB extra bits' with
            | none => simp only [h₃] at h; exact absurd h nofun
            | some p₃ =>
              obtain ⟨extraVal, bits₁⟩ := p₃
              simp only [h₃] at h
              have hlen₃ := Deflate.Spec.readBitsLSB_some_length h₃
              cases h₄ : Huffman.Spec.decode
                  ((Huffman.Spec.allCodes distLens).map fun (s, cw) => (cw, s)) bits₁ with
              | none => simp only [h₄] at h; exact absurd h nofun
              | some p₄ =>
                obtain ⟨dSym, bits₂⟩ := p₄
                simp only [h₄] at h
                cases h₅ : (Deflate.Spec.distBase[dSym]?) with
                | none => simp only [h₅] at h; exact absurd h nofun
                | some dBase =>
                  simp only [h₅] at h
                  cases h₆ : (Deflate.Spec.distExtra[dSym]?) with
                  | none => simp only [h₆] at h; exact absurd h nofun
                  | some dExtra =>
                    simp only [h₆] at h
                    cases h₇ : Deflate.Spec.readBitsLSB dExtra bits₂ with
                    | none => simp only [h₇] at h; exact absurd h nofun
                    | some p₇ =>
                      obtain ⟨dExtraVal, bits₃⟩ := p₇
                      simp only [h₇, pure,
                        Option.some.injEq, Prod.mk.injEq] at h
                      obtain ⟨_, rfl⟩ := h
                      have hlen₇ := Deflate.Spec.readBitsLSB_some_length h₇
                      have hlen₄ := Huffman.Spec.decode_shorter _ _ _ _ h₄
                          (specTable_cw_nonempty _ _)
                      omega

/-- If `decodeSymbols` succeeds, `rest.length ≤ bits.length`. -/
theorem decodeSymbols_rest_le {litLens distLens : List Nat}
    {bits : List Bool} {syms : List Deflate.Spec.LZ77Symbol} {rest : List Bool}
    (h : Deflate.Spec.decodeSymbols litLens distLens bits = some (syms, rest)) :
    rest.length ≤ bits.length := by
  -- Strong induction on bits.length
  suffices ∀ n (bits : List Bool) (syms : List Deflate.Spec.LZ77Symbol) (rest : List Bool),
      bits.length = n →
      Deflate.Spec.decodeSymbols litLens distLens bits = some (syms, rest) →
      rest.length ≤ bits.length from this _ bits syms rest rfl h
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro bits syms rest hlen hds
    unfold Deflate.Spec.decodeSymbols at hds
    cases hdl : Deflate.Spec.decodeLitLen litLens distLens bits with
    | none => simp only [hdl] at hds; exact absurd hds nofun
    | some p =>
      obtain ⟨sym, bits'⟩ := p
      simp only [hdl, bind, Option.bind] at hds
      have hlt := decodeLitLen_rest_lt hdl
      match sym with
      | .endOfBlock =>
        simp only [pure, Option.some.injEq, Prod.mk.injEq] at hds
        obtain ⟨_, rfl⟩ := hds; omega
      | .literal b =>
        simp only [] at hds  -- iota reduction
        split at hds
        · -- WF guard holds
          cases hds_rec : Deflate.Spec.decodeSymbols litLens distLens bits' with
          | none => simp only [hds_rec] at hds; exact absurd hds nofun
          | some p₂ =>
            simp only [hds_rec] at hds
            obtain ⟨_, rfl⟩ := hds
            have := ih bits'.length (by omega) bits' p₂.1 p₂.2 rfl hds_rec
            omega
        · exact absurd hlt ‹_›  -- guard fails, contradicts hlt
      | .reference len dist =>
        simp only [] at hds  -- iota reduction
        split at hds
        · -- WF guard holds
          cases hds_rec : Deflate.Spec.decodeSymbols litLens distLens bits' with
          | none => simp only [hds_rec] at hds; exact absurd hds nofun
          | some p₂ =>
            simp only [hds_rec] at hds
            obtain ⟨_, rfl⟩ := hds
            have := ih bits'.length (by omega) bits' p₂.1 p₂.2 rfl hds_rec
            omega
        · exact absurd hlt ‹_›  -- guard fails, contradicts hlt

/-- `readCLLengths` preserves the length invariant: `rest.length + n * 3 = bits.length`. -/
private theorem readCLLengths_rest_length {n idx : Nat} {acc acc' : List Nat}
    {bits rest : List Bool}
    (h : Deflate.Spec.readCLLengths n idx acc bits = some (acc', rest)) :
    rest.length + n * 3 = bits.length := by
  induction n generalizing idx acc bits with
  | zero =>
    simp only [Deflate.Spec.readCLLengths] at h
    obtain ⟨_, rfl⟩ := h; omega
  | succ k ih =>
    simp only [Deflate.Spec.readCLLengths, bind, Option.bind] at h
    cases h₁ : Deflate.Spec.readBitsLSB 3 bits with
    | none => simp only [h₁] at h; exact absurd h nofun
    | some p =>
      obtain ⟨v, bits'⟩ := p
      simp only [h₁] at h
      have hlen₁ := Deflate.Spec.readBitsLSB_some_length h₁
      have := ih h
      omega

/-- `decodeCLSymbols` returns `rest` with `rest.length ≤ bits.length`. -/
private theorem decodeCLSymbols_rest_le {clTable : List (Huffman.Spec.Codeword × Nat)}
    {totalCodes : Nat} {acc codeLens : List Nat} {bits rest : List Bool}
    (hcw : ∀ cw s, (cw, s) ∈ clTable → cw ≠ [])
    (h : Deflate.Spec.decodeDynamicTables.decodeCLSymbols clTable totalCodes acc bits
        = some (codeLens, rest)) :
    rest.length ≤ bits.length := by
  -- Strong induction on bits.length
  suffices ∀ n (bits : List Bool) (acc codeLens : List Nat) (rest : List Bool),
      bits.length = n →
      Deflate.Spec.decodeDynamicTables.decodeCLSymbols clTable totalCodes acc bits
        = some (codeLens, rest) →
      rest.length ≤ bits.length from this _ bits acc codeLens rest rfl h
  clear h
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro bits acc codeLens rest hlen hds
    unfold Deflate.Spec.decodeDynamicTables.decodeCLSymbols at hds
    split at hds
    · -- acc.length ≥ totalCodes: return
      simp only [Option.some.injEq, Prod.mk.injEq] at hds
      obtain ⟨_, rfl⟩ := hds; omega
    · -- Need to decode more symbols
      cases hdec : Huffman.Spec.decode clTable bits with
      | none => simp only [hdec] at hds; exact absurd hds nofun
      | some p =>
        obtain ⟨sym, bits'⟩ := p
        simp only [hdec] at hds
        have hlt := Huffman.Spec.decode_shorter _ _ _ _ hdec hcw
        -- All recursive branches return a suffix of bits' (or shorter)
        split at hds
        · -- sym < 16: literal code length
          have := ih bits'.length (by omega) bits' _ _ _ rfl hds
          omega
        · split at hds
          · -- sym == 16: repeat
            split at hds
            · exact absurd hds nofun
            · cases hrd : Deflate.Spec.readBitsLSB 2 bits' with
              | none => simp only [hrd] at hds; exact absurd hds nofun
              | some p₂ =>
                obtain ⟨rep, bits''⟩ := p₂
                simp only [hrd] at hds
                have hlen₂ := Deflate.Spec.readBitsLSB_some_length hrd
                split at hds
                · have := ih bits''.length (by omega) bits'' _ _ _ rfl hds
                  omega
                · exact absurd hds nofun
          · split at hds
            · -- sym == 17: repeat 0
              cases hrd : Deflate.Spec.readBitsLSB 3 bits' with
              | none => simp only [hrd] at hds; exact absurd hds nofun
              | some p₂ =>
                obtain ⟨rep, bits''⟩ := p₂
                simp only [hrd] at hds
                have hlen₂ := Deflate.Spec.readBitsLSB_some_length hrd
                split at hds
                · have := ih bits''.length (by omega) bits'' _ _ _ rfl hds
                  omega
                · exact absurd hds nofun
            · -- ¬(sym == 17): split on sym == 18
              split at hds
              · -- sym == 18: repeat 0 (longer)
                cases hrd : Deflate.Spec.readBitsLSB 7 bits' with
                | none => simp only [hrd] at hds; exact absurd hds nofun
                | some p₂ =>
                  obtain ⟨rep, bits''⟩ := p₂
                  simp only [hrd] at hds
                  have hlen₂ := Deflate.Spec.readBitsLSB_some_length hrd
                  split at hds
                  · have := ih bits''.length (by omega) bits'' _ _ _ rfl hds
                    omega
                  · exact absurd hds nofun
              · -- sym ≥ 19: none, contradiction
                exact absurd hds nofun

/-- If `decodeDynamicTables` succeeds, `rest.length ≤ bits.length`. -/
theorem decodeDynamicTables_rest_le {bits : List Bool}
    {litLens distLens : List Nat} {rest : List Bool}
    (h : Deflate.Spec.decodeDynamicTables bits = some (litLens, distLens, rest)) :
    rest.length ≤ bits.length := by
  unfold Deflate.Spec.decodeDynamicTables at h
  simp only [bind, Option.bind] at h
  cases h₁ : Deflate.Spec.readBitsLSB 5 bits with
  | none => simp only [h₁] at h; exact absurd h nofun
  | some p₁ =>
    obtain ⟨hlit, bits₁⟩ := p₁; simp only [h₁] at h
    have hlen₁ := Deflate.Spec.readBitsLSB_some_length h₁
    cases h₂ : Deflate.Spec.readBitsLSB 5 bits₁ with
    | none => simp only [h₂] at h; exact absurd h nofun
    | some p₂ =>
      obtain ⟨hdist, bits₂⟩ := p₂; simp only [h₂] at h
      have hlen₂ := Deflate.Spec.readBitsLSB_some_length h₂
      cases h₃ : Deflate.Spec.readBitsLSB 4 bits₂ with
      | none => simp only [h₃] at h; exact absurd h nofun
      | some p₃ =>
        obtain ⟨hclen, bits₃⟩ := p₃; simp only [h₃] at h
        have hlen₃ := Deflate.Spec.readBitsLSB_some_length h₃
        -- Normalize List.replicate 19 0 to explicit list to match simp output
        have hrep : (List.replicate 19 (0 : Nat)) =
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide
        rw [hrep] at h
        cases h₄ : Deflate.Spec.readCLLengths (hclen + 4) 0
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] bits₃ with
        | none => simp only [h₄] at h; exact absurd h nofun
        | some p₄ =>
          obtain ⟨clLens, bits₄⟩ := p₄; simp only [h₄] at h
          have hlen₄ := readCLLengths_rest_length h₄
          -- guard (ValidLengths clLens 7)
          split at h
          · exact absurd h nofun
          · -- Reduce continuation after guard
            simp only [] at h
            -- decodeCLSymbols
            cases h₅ : Deflate.Spec.decodeDynamicTables.decodeCLSymbols
                (List.map (fun x => (x.snd, x.fst)) (Huffman.Spec.allCodes clLens 7))
                (hlit + 257 + (hdist + 1)) [] bits₄ with
            | none => simp only [h₅] at h; exact absurd h nofun
            | some p₅ =>
              obtain ⟨codeLens, bits₅⟩ := p₅; simp only [h₅] at h
              have hlen₅ := decodeCLSymbols_rest_le (specTable_cw_nonempty clLens 7) h₅
              -- guard (codeLens.length == totalCodes)
              split at h
              · exact absurd h nofun
              · simp only [] at h
                -- guard (ValidLengths litLenLengths 15)
                split at h
                · exact absurd h nofun
                · simp only [] at h
                  -- guard (ValidLengths distLengths 15)
                  split at h
                  · exact absurd h nofun
                  · simp only [pure] at h
                    obtain ⟨_, _, rfl⟩ := h
                    omega

/-! ## Main correctness theorem -/

/-- Bridge: `(bfinal == 1) = true` (UInt32) implies `(bfinal.toNat == 1) = true` (Nat). -/
theorem bfinal_beq_nat_true (bfinal : UInt32) (h : (bfinal == 1) = true) :
    (bfinal.toNat == 1) = true := by
  rw [beq_iff_eq] at h ⊢; exact congrArg UInt32.toNat h

/-- Bridge: `¬((bfinal == 1) = true)` (UInt32) implies `(bfinal.toNat == 1) = false`. -/
theorem bfinal_beq_nat_false (bfinal : UInt32) (h : ¬((bfinal == 1) = true)) :
    (bfinal.toNat == 1) = false := by
  cases heq : bfinal.toNat == 1 <;> simp_all [← UInt32.toNat_inj]

/-- Bridge (reverse): `(v == 1) = true` (Nat) with `v < 2` implies
    `(v.toUInt32 == 1) = true` (UInt32). -/
protected theorem nat_beq_to_uint32_true (v : Nat) (hv : v < 2) (h : (v == 1) = true) :
    (v.toUInt32 == 1) = true := by
  rw [beq_iff_eq] at h ⊢; subst h; rfl

/-- Bridge (reverse): `¬((v == 1) = true)` (Nat) with `v < 2` implies
    `(v.toUInt32 == 1) = false` (UInt32). -/
protected theorem nat_beq_to_uint32_false (v : Nat) (hv : v < 2) (h : ¬((v == 1) = true)) :
    ¬((v.toUInt32 == 1) = true) := by
  have hv0 : v = 0 := by simp only [beq_iff_eq] at h; omega
  subst hv0; decide

set_option maxRecDepth 2048 in
/-- Block loop correspondence: the native `inflateLoop` agrees with
    the spec's `decode.go` on a block-by-block basis. -/
theorem inflateLoop_correct (br : Zip.Native.BitReader)
    (output : ByteArray)
    (fixedLit fixedDist : Zip.Native.HuffTree)
    (maxOutputSize dataSize : Nat)
    (result : ByteArray) (endPos : Nat)
    (hwf : br.bitOff < 8)
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (hflit : Zip.Native.HuffTree.fromLengths
      Zip.Native.Inflate.fixedLitLengths = .ok fixedLit)
    (hfdist : Zip.Native.HuffTree.fromLengths
      Zip.Native.Inflate.fixedDistLengths = .ok fixedDist)
    (h : Zip.Native.Inflate.inflateLoop br output fixedLit fixedDist
      maxOutputSize dataSize = .ok (result, endPos)) :
    Deflate.Spec.decode.go br.toBits output.data.toList =
      some result.data.toList := by
  -- Strong induction on the WF termination measure
  suffices ∀ m : Nat, ∀ (br : Zip.Native.BitReader) (output : ByteArray)
      (result : ByteArray) (endPos : Nat),
      dataSize * 8 - br.bitPos = m →
      br.bitOff < 8 →
      (br.bitOff = 0 ∨ br.pos < br.data.size) →
      Zip.Native.Inflate.inflateLoop br output fixedLit fixedDist
        maxOutputSize dataSize = .ok (result, endPos) →
      Deflate.Spec.decode.go br.toBits output.data.toList =
        some result.data.toList from
    this _ br output result endPos rfl hwf hpos h
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
  intro br output result endPos hm hwf hpos h
  -- Unfold inflateLoop one step using the equation lemma
  rw [Zip.Native.Inflate.inflateLoop.eq_1] at h
  simp only [bind, Except.bind] at h
  -- Read bfinal (1 bit)
  cases hbf : br.readBits 1 with
  | error e => simp only [hbf] at h; exact absurd h nofun
  | ok p₁ =>
    obtain ⟨bfinal, br₁⟩ := p₁; simp only [hbf] at h
    have hwf₁ := readBits_wf br 1 bfinal br₁ hwf hbf
    have hpos₁ := readBits_pos_inv br 1 bfinal br₁ hwf hpos hbf
    have ⟨bits₁, hspec_bf, hbits₁⟩ := readBits_toBits br 1 bfinal br₁ hwf (by omega) hbf
    -- Read btype (2 bits)
    cases hbt : br₁.readBits 2 with
    | error e => simp only [hbt] at h; exact absurd h nofun
    | ok p₂ =>
      obtain ⟨btype, br₂⟩ := p₂; simp only [hbt] at h
      have hwf₂ := readBits_wf br₁ 2 btype br₂ hwf₁ hbt
      have hpos₂ := readBits_pos_inv br₁ 2 btype br₂ hwf₁ hpos₁ hbt
      have ⟨bits₂, hspec_bt, hbits₂⟩ := readBits_toBits br₁ 2 btype br₂ hwf₁ (by omega) hbt
      -- Spec-level readBitsLSB in terms of br.toBits
      have hspec_bt' : Deflate.Spec.readBitsLSB 2 bits₁ =
          some (btype.toNat, bits₂) := by rw [← hbits₁]; exact hspec_bt
      -- Unfold spec one step and simplify the do-block
      unfold Deflate.Spec.decode.go
      simp only [hspec_bf, bind, Option.bind, hspec_bt']
      -- Now br₂.toBits = bits₂
      have hbr₂_bits : br₂.toBits = bits₂ := hbits₂
      -- Dispatch on btype (native match in h)
      split at h
      · -- Case 1 (btype = 0): stored
        simp only [show UInt32.toNat 0 = 0 from rfl]
        -- Extract decodeStored result from h
        split at h
        · exact absurd h nofun
        · rename_i v hds; obtain ⟨out', br'⟩ := v; simp only [] at hds h
          -- Use decodeStored_correct to get spec result
          have ⟨storedBytes, rest, hspec_ds, hout, hrest⟩ :=
            decodeStored_correct br₂ output maxOutputSize out' br' hwf₂ hpos₂ hds
          rw [hbr₂_bits] at hspec_ds
          -- Rewrite spec decodeStored with known result
          simp only [hspec_ds]
          rw [← hout]
          -- Handle bfinal check
          split at h
          · -- bfinal = 1: final block
            simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨hrout, _⟩ := h
            have hbf_nat := bfinal_beq_nat_true bfinal ‹_›
            simp only [hbf_nat, ↓reduceIte, pure]
            rw [hrout]
          · -- bfinal ≠ 1: recursive
            have hbf_nat := bfinal_beq_nat_false bfinal ‹_›
            simp only [hbf_nat, Bool.false_eq_true, ↓reduceIte]
            -- Need rest.length < br.toBits.length for spec WF guard
            have hlen₁ := Deflate.Spec.readBitsLSB_some_length hspec_bf
            have hlen₂ := Deflate.Spec.readBitsLSB_some_length hspec_bt'
            have hlen_ds := decodeStored_rest_le hspec_ds
            have hrest_lt : rest.length < br.toBits.length := by omega
            simp only [hrest_lt, ↓reduceDIte]
            -- Discharge native WF guards
            split at h
            · exact absurd h nofun
            · rename_i h_progress
              split at h
              · exact absurd h nofun
              · rename_i h_range
                -- Apply IH with decreased measure
                have hinv := decodeStored_invariants br₂ output maxOutputSize out' br' hds
                have h_ih := ih (dataSize * 8 - br'.bitPos)
                  (by simp only [Zip.Native.BitReader.bitPos] at h_progress h_range hm ⊢; omega)
                  br' out' result endPos rfl hinv.1 hinv.2 h
                rw [hrest] at h_ih
                exact h_ih
      · -- Case 2 (btype = 1): fixed Huffman
        simp only [show UInt32.toNat 1 = 1 from rfl]
        -- Extract decodeHuffman result from h
        split at h
        · exact absurd h nofun
        · rename_i v hdh; obtain ⟨out', br'⟩ := v; simp only [] at hdh h
          -- Unfold decodeHuffman to get decodeHuffman.go
          unfold Zip.Native.Inflate.decodeHuffman at hdh
          -- Apply decodeHuffman_correct with fixed tables
          have ⟨syms, rest, hspec_ds, hresolve, hrest, hwf', hpos'⟩ :=
            decodeHuffman_correct
              Zip.Native.Inflate.fixedLitLengths
              Zip.Native.Inflate.fixedDistLengths
              fixedLit fixedDist maxOutputSize br₂.data.size
              br₂ output out' br' hwf₂ hpos₂ hflit hfdist
              (by rw [Deflate.Correctness.fixedLitLengths_eq]; exact Deflate.Spec.fixedLitLengths_valid)
              (by rw [Deflate.Correctness.fixedDistLengths_eq]; exact Deflate.Spec.fixedDistLengths_valid)
              Deflate.Correctness.fixedLitLengths_size Deflate.Correctness.fixedDistLengths_size
              hdh
          rw [hbr₂_bits] at hspec_ds
          rw [Deflate.Correctness.fixedLitLengths_eq, Deflate.Correctness.fixedDistLengths_eq] at hspec_ds
          simp only [hspec_ds, hresolve]
          -- Handle bfinal check
          split at h
          · -- bfinal = 1: final block
            simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨hrout, _⟩ := h
            have hbf_nat := bfinal_beq_nat_true bfinal ‹_›
            simp only [hbf_nat, ↓reduceIte, pure]
            rw [hrout]
          · -- bfinal ≠ 1: recursive
            have hbf_nat := bfinal_beq_nat_false bfinal ‹_›
            simp only [hbf_nat, Bool.false_eq_true, ↓reduceIte]
            -- Spec WF guard
            have hlen₁ := Deflate.Spec.readBitsLSB_some_length hspec_bf
            have hlen₂ := Deflate.Spec.readBitsLSB_some_length hspec_bt'
            have hlen_ds := decodeSymbols_rest_le hspec_ds
            have hrest_lt : rest.length < br.toBits.length := by omega
            simp only [hrest_lt, ↓reduceDIte]
            -- Discharge native WF guards
            split at h
            · exact absurd h nofun
            · rename_i h_progress
              split at h
              · exact absurd h nofun
              · rename_i h_range
                -- Apply IH with decreased measure
                have h_ih := ih (dataSize * 8 - br'.bitPos)
                  (by simp only [Zip.Native.BitReader.bitPos] at h_progress h_range hm ⊢; omega)
                  br' out' result endPos rfl hwf' hpos' h
                rw [hrest] at h_ih
                exact h_ih
      · -- Case 3 (btype = 2): dynamic Huffman
        simp only [show UInt32.toNat 2 = 2 from rfl]
        -- Extract decodeDynamicTrees + decodeHuffman from h
        split at h
        · exact absurd h nofun
        · rename_i v hdt
          obtain ⟨litTree, distTree, br₃⟩ := v; simp only [] at hdt h
          -- Apply decodeDynamicTrees_correct
          have ⟨litLens, distLens, rest_dt, hspec_dt, hbr₃_bits, hwf₃, hpos₃,
                hflit₃, hfdist₃, hvlit, hvdist, hlen_lit, hlen_dist⟩ :=
            Deflate.Correctness.decodeDynamicTrees_correct br₂ litTree distTree br₃
              hwf₂ hpos₂ hdt
          rw [hbr₂_bits] at hspec_dt
          -- Now extract decodeHuffman from h
          split at h
          · exact absurd h nofun
          · rename_i v₂ hdh; obtain ⟨out', br'⟩ := v₂; simp only [] at hdh h
            -- Unfold decodeHuffman to get decodeHuffman.go
            unfold Zip.Native.Inflate.decodeHuffman at hdh
            -- Apply decodeHuffman_correct with dynamic tables
            have ⟨syms, rest, hspec_ds, hresolve, hrest, hwf', hpos'⟩ :=
              decodeHuffman_correct litLens distLens
                litTree distTree maxOutputSize br₃.data.size
                br₃ output out' br' hwf₃ hpos₃ hflit₃ hfdist₃
                hvlit hvdist hlen_lit hlen_dist hdh
            rw [hbr₃_bits] at hspec_ds
            simp only [hspec_dt, hspec_ds, hresolve]
            -- Handle bfinal check
            split at h
            · -- bfinal = 1: final block
              simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨hrout, _⟩ := h
              have hbf_nat := bfinal_beq_nat_true bfinal ‹_›
              simp only [hbf_nat, ↓reduceIte, pure]
              rw [hrout]
            · -- bfinal ≠ 1: recursive
              have hbf_nat := bfinal_beq_nat_false bfinal ‹_›
              simp only [hbf_nat, Bool.false_eq_true, ↓reduceIte]
              -- Spec WF guard
              have hlen₁ := Deflate.Spec.readBitsLSB_some_length hspec_bf
              have hlen₂ := Deflate.Spec.readBitsLSB_some_length hspec_bt'
              have hlen_dt := decodeDynamicTables_rest_le hspec_dt
              have hlen_ds := decodeSymbols_rest_le hspec_ds
              have hrest_lt : rest.length < br.toBits.length := by omega
              simp only [hrest_lt, ↓reduceDIte]
              -- Discharge native WF guards
              split at h
              · exact absurd h nofun
              · rename_i h_progress
                split at h
                · exact absurd h nofun
                · rename_i h_range
                  -- Apply IH with decreased measure
                  have h_ih := ih (dataSize * 8 - br'.bitPos)
                    (by simp only [Zip.Native.BitReader.bitPos] at h_progress h_range hm ⊢; omega)
                    br' out' result endPos rfl hwf' hpos' h
                  rw [hrest] at h_ih
                  exact h_ih
      · -- Case 4: reserved (btype ≥ 3)
        exact absurd h nofun

/-- **Main theorem**: If the native DEFLATE decompressor succeeds, then
    the formal specification also succeeds and produces the same output. -/
theorem inflate_correct (data : ByteArray) (startPos maxOutputSize : Nat)
    (result : ByteArray) (endPos : Nat)
    (h : Zip.Native.Inflate.inflateRaw data startPos maxOutputSize =
      .ok (result, endPos)) :
    Deflate.Spec.decode
      ((Deflate.Spec.bytesToBits data).drop (startPos * 8)) =
      some result.data.toList := by
  -- Unfold inflateRaw
  simp only [Zip.Native.Inflate.inflateRaw, bind, Except.bind] at h
  -- Build fixed trees
  cases hflit : Zip.Native.HuffTree.fromLengths
      Zip.Native.Inflate.fixedLitLengths with
  | error e => simp only [hflit] at h; exact absurd h nofun
  | ok fixedLit =>
    simp only [hflit] at h
    cases hfdist : Zip.Native.HuffTree.fromLengths
        Zip.Native.Inflate.fixedDistLengths with
    | error e => simp only [hfdist] at h; exact absurd h nofun
    | ok fixedDist =>
      simp only [hfdist] at h
      have hbr_wf : (Zip.Native.BitReader.mk data startPos 0).bitOff < 8 := by
        show 0 < 8; omega
      have hbr_pos : (Zip.Native.BitReader.mk data startPos 0).bitOff = 0 ∨
          (Zip.Native.BitReader.mk data startPos 0).pos <
          (Zip.Native.BitReader.mk data startPos 0).data.size := by exact Or.inl rfl
      have hgo := inflateLoop_correct
        ⟨data, startPos, 0⟩ .empty fixedLit fixedDist
        maxOutputSize data.size result endPos
        hbr_wf hbr_pos hflit hfdist h
      simp only [Deflate.Spec.decode]; exact hgo

/-- Corollary: `inflate` (which starts at position 0) agrees with
    the spec `decode` applied to the full bitstream. -/
theorem inflate_correct' (data : ByteArray) (maxOutputSize : Nat)
    (result : ByteArray)
    (h : Zip.Native.Inflate.inflate data maxOutputSize = .ok result) :
    Deflate.Spec.decode (Deflate.Spec.bytesToBits data) =
      some result.data.toList := by
  simp only [Zip.Native.Inflate.inflate, bind, Except.bind] at h
  cases hinf : Zip.Native.Inflate.inflateRaw data 0 maxOutputSize with
  | error e => simp only [hinf] at h; exact absurd h nofun
  | ok p =>
    simp only [hinf, pure, Except.pure, Except.ok.injEq] at h
    have := inflate_correct data 0 maxOutputSize p.1 p.2 (by rw [hinf])
    simp only [Nat.zero_mul, List.drop_zero] at this
    rw [← h]; exact this

end Deflate.Correctness
