import Zip.Spec.DecodeCorrect

/-!
# Block-Level Decode Completeness (reverse direction)

Proves that if the spec decoders succeed, the native decoders also succeed
with the same output. This is the reverse direction of `DecodeCorrect`.

The proof layers:
1. **Stored block**: `decodeStored_complete` — spec success → native success
2. **Huffman decode**: `huffTree_decode_complete` — spec decode → native decode
3. **Huffman block**: `decodeHuffman_complete` — spec symbols + LZ77 → native success
-/

namespace Deflate.Correctness

/-- **Completeness for stored blocks**: if the spec `decodeStored` succeeds,
    the native `Inflate.decodeStored` also succeeds with the same output.

    This is the reverse of `decodeStored_correct`. -/
theorem decodeStored_complete (br : Zip.Native.BitReader)
    (output : ByteArray) (maxOutputSize : Nat)
    (storedBytes : List UInt8) (rest : List Bool)
    (hwf : br.bitOff < 8)
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (hmax : output.size + storedBytes.length ≤ maxOutputSize)
    (hspec : Deflate.Spec.decodeStored br.toBits = some (storedBytes, rest)) :
    ∃ br', Zip.Native.Inflate.decodeStored br output maxOutputSize =
      .ok (output ++ ⟨⟨storedBytes⟩⟩, br') ∧
      br'.toBits = rest ∧
      br'.bitOff = 0 ∧
      (br'.bitOff = 0 ∨ br'.pos < br'.data.size) := by
  -- Unfold spec decodeStored to extract len, nlen, and bytes
  simp only [Deflate.Spec.decodeStored, bind, Option.bind] at hspec
  -- First readBitsLSB 16 (after alignment)
  cases hlen_spec : Deflate.Spec.readBitsLSB 16 (Deflate.Spec.alignToByte br.toBits) with
  | none => simp [hlen_spec] at hspec
  | some p1 =>
    obtain ⟨len_val, bits1⟩ := p1
    simp only [hlen_spec] at hspec
    -- Second readBitsLSB 16
    cases hnlen_spec : Deflate.Spec.readBitsLSB 16 bits1 with
    | none => simp [hnlen_spec] at hspec
    | some p2 =>
      obtain ⟨nlen_val, bits2⟩ := p2
      simp only [hnlen_spec] at hspec
      -- Guard: len ^^^ nlen == 0xFFFF
      -- In Option monad, guard uses `if cond then pure () else none`
      -- Bounds from readBitsLSB
      have hlen_bound : len_val < 2 ^ 16 := Deflate.Spec.readBitsLSB_bound hlen_spec
      have hnlen_bound : nlen_val < 2 ^ 16 := Deflate.Spec.readBitsLSB_bound hnlen_spec
      -- Split on guard condition
      by_cases hguard : (len_val ^^^ nlen_val == 0xFFFF) = true
      · -- guard passed — use simp to reduce guard + do-notation chain
        simp [hguard] at hspec
        -- hspec : readNBytes len_val bits2 [] = some (storedBytes, rest)
        -- Use readUInt16LE_complete for LEN
        obtain ⟨br1, hrd1, hbr1_bits, hbr1_off, hbr1_pos⟩ :=
          readUInt16LE_complete br len_val bits1 hwf hpos hlen_bound hlen_spec
        -- br1 is byte-aligned
        have hbr1_aligned : Deflate.Spec.alignToByte br1.toBits = br1.toBits :=
          alignToByte_id_of_aligned br1 hbr1_off
        -- Rewrite hnlen_spec to use br1.toBits
        rw [← hbr1_bits, ← hbr1_aligned] at hnlen_spec
        -- Use readUInt16LE_complete for NLEN
        obtain ⟨br2, hrd2, hbr2_bits, hbr2_off, hbr2_pos⟩ :=
          readUInt16LE_complete br1 nlen_val bits2 (by omega) hbr1_pos hnlen_bound hnlen_spec
        -- br2 is byte-aligned
        have hbr2_aligned : Deflate.Spec.alignToByte br2.toBits = br2.toBits :=
          alignToByte_id_of_aligned br2 hbr2_off
        -- Rewrite hspec to use br2.toBits
        rw [← hbr2_bits, ← hbr2_aligned] at hspec
        -- Derive halign_pos for readBytes_complete: br2.alignToByte.pos ≤ data.size
        have halign_pos2 : br2.alignToByte.pos ≤ br2.alignToByte.data.size := by
          rw [show br2.alignToByte = br2 from by
            simp [Zip.Native.BitReader.alignToByte, hbr2_off]]
          -- Unfold readUInt16LE on br1 to extract the bounds check
          simp only [Zip.Native.BitReader.readUInt16LE, Zip.Native.BitReader.alignToByte,
            hbr1_off] at hrd2
          by_cases hle2 : br1.data.size < br1.pos + 2
          · simp [hle2] at hrd2
          · simp [hle2] at hrd2
            obtain ⟨_, rfl⟩ := hrd2
            have hd1 : br1.data = br.data := readUInt16LE_data br _ br1 hrd1
            simp only [hd1] at hle2 ⊢
            omega
        -- Derive readNBytes output length = len_val for size check
        have hbytes_len : storedBytes.length = len_val := by
          have := readNBytes_output_length hspec; simp at this; exact this
        -- Use readBytes_complete
        obtain ⟨br3, hrd3, hbr3_bits, hbr3_off, hbr3_pos⟩ :=
          readBytes_complete br2 len_val storedBytes rest (by omega) hbr2_pos halign_pos2 hspec
        -- Complement check in native
        have hcomp : len_val.toUInt16 ^^^ nlen_val.toUInt16 = 0xFFFF := by
          simp [beq_iff_eq] at hguard; exact UInt16.toNat_inj.mp (by
            rw [UInt16.toNat_xor]
            simp [Nat.toUInt16, Nat.mod_eq_of_lt hlen_bound, Nat.mod_eq_of_lt hnlen_bound]
            exact hguard)
        have hcomp_ne : ¬(len_val.toUInt16 ^^^ nlen_val.toUInt16 != 0xFFFF) := by
          simp [hcomp]
        -- Size check in native
        have hsize_ok : ¬(output.size + len_val > maxOutputSize) := by
          rw [← hbytes_len]; omega
        -- Bridge len_val.toUInt16.toNat = len_val for readBytes
        have hlen_toNat : len_val.toUInt16.toNat = len_val := by
          simp [Nat.toUInt16, Nat.mod_eq_of_lt hlen_bound]
        -- Construct the result
        refine ⟨br3, ?_, hbr3_bits, hbr3_off, hbr3_pos⟩
        simp only [Zip.Native.Inflate.decodeStored, bind, Except.bind, hrd1, hrd2,
          hcomp_ne, Bool.false_eq_true, ↓reduceIte, pure, Except.pure, hsize_ok,
          hlen_toNat, hrd3]
      · -- guard failed → spec produces none, contradiction
        -- hguard : ¬(... == 65535) = true means the beq is false
        have hbeq_false : (len_val ^^^ nlen_val == 65535) = false := by
          cases h : (len_val ^^^ nlen_val == 65535) <;> simp_all
        -- Rewrite the guard condition in hspec to get guard (false = true) = guard False = none
        rw [hbeq_false] at hspec
        simp [guard, Bool.false_eq_true] at hspec

/-- **Completeness for `HuffTree.decode`**: if the spec `Huffman.Spec.decode`
    succeeds on the bit list corresponding to a `BitReader`, then the native
    tree decode also succeeds, producing the same symbol.

    This is the reverse of `huffTree_decode_correct`. -/
theorem huffTree_decode_complete (lengths : Array UInt8)
    (maxBits : Nat) (hmb : maxBits ≤ 20)
    (tree : Zip.Native.HuffTree) (br : Zip.Native.BitReader)
    (sym : Nat) (rest : List Bool)
    (hwf : br.bitOff < 8)
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (htree : Zip.Native.HuffTree.fromLengths lengths maxBits = .ok tree)
    (hv : Huffman.Spec.ValidLengths (lengths.toList.map UInt8.toNat) maxBits)
    (hlen_bound : lengths.size ≤ UInt16.size)
    (hsym_bound : sym < lengths.size)
    (hspec : Huffman.Spec.decode
      ((Huffman.Spec.allCodes (lengths.toList.map UInt8.toNat) maxBits).map
        fun (s, cw) => (cw, s)) br.toBits = some (sym, rest)) :
    ∃ br', tree.decode br = .ok (sym.toUInt16, br') ∧
      br'.toBits = rest ∧
      br'.bitOff < 8 ∧
      (br'.bitOff = 0 ∨ br'.pos < br'.data.size) := by
  -- Extract codeword from spec decode success
  obtain ⟨cw, hmem_table, hbits_eq⟩ :=
    Deflate.Correctness.decode_some_mem _ br.toBits sym rest hspec
  -- Convert (cw, sym) ∈ specTable to (sym, cw) ∈ allCodes
  have hmem_codes : (sym, cw) ∈ Huffman.Spec.allCodes
      (lengths.toList.map UInt8.toNat) maxBits := by
    obtain ⟨⟨s', cw'⟩, hm, he⟩ := List.mem_map.mp hmem_table
    simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he; exact hm
  -- Get TreeHasLeaf from fromLengths_hasLeaf
  have hleaf := Deflate.Correctness.fromLengths_hasLeaf lengths maxBits
    (by omega) tree htree hv sym cw hmem_codes
  -- Get codeword length bound: cw.length ≤ maxBits ≤ 20
  rw [Huffman.Spec.allCodes_mem_iff] at hmem_codes
  obtain ⟨_, hcf⟩ := hmem_codes
  obtain ⟨_, hlen_cond, hcw_eq⟩ := Huffman.Spec.codeFor_spec hcf
  have ⟨_, hcw_le⟩ := Huffman.Spec.codeFor_len_bounds hlen_cond
  have hcw_len : cw.length ≤ 20 := by
    rw [hcw_eq, Huffman.Spec.natToBits_length]; omega
  -- Apply decode_go_complete with n = 0
  obtain ⟨br', hgo, hbr'_bits, hwf', hpos'⟩ :=
    Deflate.Correctness.decode_go_complete tree _ sym.toUInt16 rest br 0
      hleaf hwf hpos hbits_eq (by omega)
  -- Wrap decode.go → decode
  exact ⟨br', hgo, hbr'_bits, hwf', hpos'⟩

/-- If `decodeLitLen` succeeds, the underlying Huffman decode succeeded. -/
private theorem decodeLitLen_huffDecode {litLengths distLengths : List Nat}
    {bits : List Bool} {sym : Deflate.Spec.LZ77Symbol} {rest : List Bool}
    (h : Deflate.Spec.decodeLitLen litLengths distLengths bits = some (sym, rest)) :
    ∃ sym_nat rest₁,
      Huffman.Spec.decode
        ((Huffman.Spec.allCodes litLengths).map fun (s, cw) => (cw, s))
        bits = some (sym_nat, rest₁) := by
  unfold Deflate.Spec.decodeLitLen at h
  cases hd : Huffman.Spec.decode
      ((Huffman.Spec.allCodes litLengths).map fun (s, cw) => (cw, s)) bits with
  | none => simp [hd] at h
  | some p =>
    obtain ⟨sym_nat, rest₁⟩ := p
    exact ⟨sym_nat, rest₁, rfl⟩

/-- If `decodeLitLen` returns `.literal b` and the Huffman decode returns
    `(sym_nat, rest₁)`, then `sym_nat < 256`, `b = sym_nat.toUInt8`, and `rest = rest₁`. -/
private theorem decodeLitLen_literal_inv {litLengths distLengths : List Nat}
    {bits rest : List Bool} {b : UInt8} {sym_nat : Nat} {rest₁ : List Bool}
    (hdll : Deflate.Spec.decodeLitLen litLengths distLengths bits = some (.literal b, rest))
    (hd : Huffman.Spec.decode
        ((Huffman.Spec.allCodes litLengths).map fun (s, cw) => (cw, s))
        bits = some (sym_nat, rest₁)) :
    sym_nat < 256 ∧ b = sym_nat.toUInt8 ∧ rest = rest₁ := by
  unfold Deflate.Spec.decodeLitLen at hdll
  simp [hd] at hdll
  -- After substituting the Huffman decode result, hdll has the if/then/else body
  by_cases h256 : sym_nat < 256
  · simp only [if_pos h256] at hdll
    -- hdll : some (.literal (UInt8.ofNat sym_nat), rest₁) = some (.literal b, rest)
    have heq := Option.some.inj hdll
    have hlz : Deflate.Spec.LZ77Symbol.literal (UInt8.ofNat sym_nat) = .literal b :=
      congrArg Prod.fst heq
    have hrest : rest₁ = rest := congrArg Prod.snd heq
    have hb : UInt8.ofNat sym_nat = b := by
      cases hlz; rfl
    exact ⟨h256, hb.symm, hrest.symm⟩
  · -- sym_nat ≥ 256: decodeLitLen cannot produce .literal
    exfalso
    by_cases h256eq : sym_nat = 256
    · simp [h256eq] at hdll
    · -- sym_nat ≥ 257: reference chain produces .reference, not .literal
      have h256ne : ¬(sym_nat = 256) := h256eq
      simp only [show ¬(sym_nat < 256) from h256, ↓reduceIte, h256ne] at hdll
      -- hdll : lengthBase[...]?.bind ... = some (.literal b, rest)
      -- Split each bind; none case → contradiction, some case → continue
      cases hlb : Deflate.Spec.lengthBase[sym_nat - 257]? with
      | none => simp [hlb] at hdll
      | some base =>
      cases hle : Deflate.Spec.lengthExtra[sym_nat - 257]? with
      | none => simp [hlb, hle] at hdll
      | some extra =>
      cases hrb : Deflate.Spec.readBitsLSB extra rest₁ with
      | none => simp [hlb, hle, hrb] at hdll
      | some p =>
      cases hdd : Huffman.Spec.decode
          ((Huffman.Spec.allCodes distLengths).map fun x => (x.snd, x.fst))
          p.2 with
      | none => simp [hlb, hle, hrb, hdd] at hdll
      | some pd =>
      cases hdb : Deflate.Spec.distBase[pd.1]? with
      | none => simp [hlb, hle, hrb, hdd, hdb] at hdll
      | some dBase =>
      cases hde : Deflate.Spec.distExtra[pd.1]? with
      | none => simp [hlb, hle, hrb, hdd, hdb, hde] at hdll
      | some dExtra =>
      cases hrd : Deflate.Spec.readBitsLSB dExtra pd.2 with
      | none => simp [hlb, hle, hrb, hdd, hdb, hde, hrd] at hdll
      | some q => simp [hlb, hle, hrb, hdd, hdb, hde, hrd] at hdll

/-- If `decodeLitLen` returns `.endOfBlock` and the Huffman decode returns
    `(sym_nat, rest₁)`, then `sym_nat = 256` and `rest = rest₁`. -/
private theorem decodeLitLen_endOfBlock_inv {litLengths distLengths : List Nat}
    {bits rest : List Bool} {sym_nat : Nat} {rest₁ : List Bool}
    (hdll : Deflate.Spec.decodeLitLen litLengths distLengths bits = some (.endOfBlock, rest))
    (hd : Huffman.Spec.decode
        ((Huffman.Spec.allCodes litLengths).map fun (s, cw) => (cw, s))
        bits = some (sym_nat, rest₁)) :
    sym_nat = 256 ∧ rest = rest₁ := by
  unfold Deflate.Spec.decodeLitLen at hdll
  simp [hd] at hdll
  -- After substituting the Huffman decode result, hdll has the if/then/else body
  by_cases h256 : sym_nat < 256
  · -- sym_nat < 256 → literal, not endOfBlock → contradiction
    exfalso; simp [h256] at hdll
  · by_cases h256eq : sym_nat = 256
    · -- sym_nat = 256: endOfBlock case
      simp only [↓reduceIte, h256eq] at hdll
      have heq := Option.some.inj hdll
      exact ⟨h256eq, (congrArg Prod.snd heq).symm⟩
    · -- sym_nat ≥ 257 → reference, not endOfBlock → contradiction
      exfalso
      have h256ne : ¬(sym_nat = 256) := h256eq
      simp only [show ¬(sym_nat < 256) from h256, ↓reduceIte, h256ne] at hdll
      -- Split each bind; none case → contradiction, some case → continue
      cases hlb : Deflate.Spec.lengthBase[sym_nat - 257]? with
      | none => simp [hlb] at hdll
      | some base =>
      cases hle : Deflate.Spec.lengthExtra[sym_nat - 257]? with
      | none => simp [hlb, hle] at hdll
      | some extra =>
      cases hrb : Deflate.Spec.readBitsLSB extra rest₁ with
      | none => simp [hlb, hle, hrb] at hdll
      | some p =>
      cases hdd : Huffman.Spec.decode
          ((Huffman.Spec.allCodes distLengths).map fun x => (x.snd, x.fst))
          p.2 with
      | none => simp [hlb, hle, hrb, hdd] at hdll
      | some pd =>
      cases hdb : Deflate.Spec.distBase[pd.1]? with
      | none => simp [hlb, hle, hrb, hdd, hdb] at hdll
      | some dBase =>
      cases hde : Deflate.Spec.distExtra[pd.1]? with
      | none => simp [hlb, hle, hrb, hdd, hdb, hde] at hdll
      | some dExtra =>
      cases hrd : Deflate.Spec.readBitsLSB dExtra pd.2 with
      | none => simp [hlb, hle, hrb, hdd, hdb, hde, hrd] at hdll
      | some q => simp [hlb, hle, hrb, hdd, hdb, hde, hrd] at hdll

set_option maxRecDepth 4096 in
/-- If `decodeLitLen` returns `.reference len dist` and the Huffman decode returns
    `(sym_nat, rest₁)`, then `sym_nat ≥ 257` and the reference chain succeeded:
    there exist all intermediate values (length base/extra, distance Huffman decode,
    distance base/extra) and the final rest bits. -/
private theorem decodeLitLen_reference_inv {litLengths distLengths : List Nat}
    {bits rest : List Bool} {len dist sym_nat : Nat} {rest₁ : List Bool}
    (hdll : Deflate.Spec.decodeLitLen litLengths distLengths bits = some (.reference len dist, rest))
    (hd : Huffman.Spec.decode
        ((Huffman.Spec.allCodes litLengths).map fun (s, cw) => (cw, s))
        bits = some (sym_nat, rest₁)) :
    sym_nat ≥ 257 ∧
    ∃ (base extra extraVal : Nat) (bits₂ : List Bool)
      (dSym : Nat) (bits₃ : List Bool)
      (dBase dExtra dExtraVal : Nat),
      Deflate.Spec.lengthBase[sym_nat - 257]? = some base ∧
      Deflate.Spec.lengthExtra[sym_nat - 257]? = some extra ∧
      Deflate.Spec.readBitsLSB extra rest₁ = some (extraVal, bits₂) ∧
      Huffman.Spec.decode
        ((Huffman.Spec.allCodes distLengths).map fun (s, cw) => (cw, s))
        bits₂ = some (dSym, bits₃) ∧
      Deflate.Spec.distBase[dSym]? = some dBase ∧
      Deflate.Spec.distExtra[dSym]? = some dExtra ∧
      Deflate.Spec.readBitsLSB dExtra bits₃ = some (dExtraVal, rest) ∧
      len = base + extraVal ∧
      dist = dBase + dExtraVal := by
  unfold Deflate.Spec.decodeLitLen at hdll
  simp [hd] at hdll
  by_cases h256 : sym_nat < 256
  · exfalso; simp [h256] at hdll
  · by_cases h256eq : sym_nat = 256
    · exfalso
      simp only [↓reduceIte, h256eq] at hdll
      exact absurd (Option.some.inj hdll) (by simp)
    · have h_ge : sym_nat ≥ 257 := by omega
      refine ⟨h_ge, ?_⟩
      have h256ne : ¬(sym_nat = 256) := h256eq
      simp only [show ¬(sym_nat < 256) from h256, ↓reduceIte, h256ne] at hdll
      cases hlb : Deflate.Spec.lengthBase[sym_nat - 257]? with
      | none => simp [hlb] at hdll
      | some base =>
      cases hle : Deflate.Spec.lengthExtra[sym_nat - 257]? with
      | none => simp [hlb, hle] at hdll
      | some extra =>
      cases hrb : Deflate.Spec.readBitsLSB extra rest₁ with
      | none => simp [hlb, hle, hrb] at hdll
      | some p =>
        obtain ⟨extraVal, bits₂⟩ := p
        cases hdd : Huffman.Spec.decode
            ((Huffman.Spec.allCodes distLengths).map fun x => (x.snd, x.fst))
            bits₂ with
        | none => simp [hlb, hle, hrb, hdd] at hdll
        | some pd =>
          obtain ⟨dSym, bits₃⟩ := pd
          cases hdb : Deflate.Spec.distBase[dSym]? with
          | none => simp [hlb, hle, hrb, hdd, hdb] at hdll
          | some dBase =>
          cases hde : Deflate.Spec.distExtra[dSym]? with
          | none => simp [hlb, hle, hrb, hdd, hdb, hde] at hdll
          | some dExtra =>
          cases hrd : Deflate.Spec.readBitsLSB dExtra bits₃ with
          | none => simp [hlb, hle, hrb, hdd, hdb, hde, hrd] at hdll
          | some q =>
            obtain ⟨dExtraVal, rest'⟩ := q
            simp [hlb, hle, hrb, hdd, hdb, hde, hrd] at hdll
            obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hdll
            exact ⟨base, extra, extraVal, bits₂, dSym, bits₃, dBase, dExtra, dExtraVal,
              rfl, rfl, hrb, hdd, hdb, hde, hrd, rfl, rfl⟩

/-- **Completeness for Huffman block decode**: if the spec `decodeSymbols`
    succeeds and `resolveLZ77` produces output, then the native
    `decodeHuffman.go` also succeeds with the same output.

    This is the reverse of `decodeHuffman_correct`. -/
theorem decodeHuffman_complete
    (litLengths distLengths : Array UInt8)
    (litTree distTree : Zip.Native.HuffTree)
    (maxOutputSize : Nat)
    (br : Zip.Native.BitReader) (output : ByteArray)
    (syms : List Deflate.Spec.LZ77Symbol) (rest : List Bool)
    (result : List UInt8)
    (hwf : br.bitOff < 8)
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (hlit : Zip.Native.HuffTree.fromLengths litLengths = .ok litTree)
    (hdist : Zip.Native.HuffTree.fromLengths distLengths = .ok distTree)
    (hvlit : Huffman.Spec.ValidLengths (litLengths.toList.map UInt8.toNat) 15)
    (hvdist : Huffman.Spec.ValidLengths (distLengths.toList.map UInt8.toNat) 15)
    (hlen_lit : litLengths.size ≤ UInt16.size)
    (hlen_dist : distLengths.size ≤ UInt16.size)
    (hmax : result.length ≤ maxOutputSize)
    (hfuel : Nat)
    (hds : Deflate.Spec.decodeSymbols (litLengths.toList.map UInt8.toNat)
        (distLengths.toList.map UInt8.toNat) br.toBits hfuel =
        some (syms, rest))
    (hlz : Deflate.Spec.resolveLZ77 syms output.data.toList = some result) :
    ∃ br', Zip.Native.Inflate.decodeHuffman.go litTree distTree maxOutputSize
        br output hfuel = .ok (⟨⟨result⟩⟩, br') ∧
      br'.toBits = rest ∧
      br'.bitOff < 8 ∧
      (br'.bitOff = 0 ∨ br'.pos < br'.data.size) := by
  induction hfuel generalizing br output syms result with
  | zero => simp [Deflate.Spec.decodeSymbols] at hds
  | succ n ih =>
    -- Unfold spec decodeSymbols to extract decodeLitLen
    simp only [Deflate.Spec.decodeSymbols, bind, Option.bind] at hds
    cases hdll : Deflate.Spec.decodeLitLen
        (litLengths.toList.map UInt8.toNat) (distLengths.toList.map UInt8.toNat)
        br.toBits with
    | none => simp [hdll] at hds
    | some p =>
      obtain ⟨sym_val, bits₁⟩ := p
      simp only [hdll] at hds
      -- Extract the Huffman decode from decodeLitLen
      obtain ⟨sym_nat, rest₁, hspec_sym⟩ := decodeLitLen_huffDecode hdll
      -- Extract sym_nat < litLengths.size
      obtain ⟨cw_lit, hmem_table, _⟩ :=
        Deflate.Correctness.decode_some_mem _ _ _ _ hspec_sym
      have hmem_codes : (sym_nat, cw_lit) ∈
          Huffman.Spec.allCodes (litLengths.toList.map UInt8.toNat) 15 := by
        obtain ⟨⟨s', cw'⟩, hm, he⟩ := List.mem_map.mp hmem_table
        simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he; exact hm
      have hsym_bound : sym_nat < litLengths.size := by
        rw [Huffman.Spec.allCodes_mem_iff] at hmem_codes
        simp at hmem_codes; exact hmem_codes.1
      -- Get native litTree.decode via huffTree_decode_complete
      obtain ⟨br₁, hdec_lit, hrest₁, hwf₁, hpos₁⟩ :=
        huffTree_decode_complete litLengths 15 (by omega) litTree br
          sym_nat rest₁ hwf hpos hlit hvlit hlen_lit hsym_bound hspec_sym
      -- Case split on sym_val (the LZ77Symbol from decodeLitLen)
      cases sym_val with
      | literal b =>
        -- From decodeLitLen_literal_inv: sym_nat < 256, b = sym_nat.toUInt8, bits₁ = rest₁
        obtain ⟨hsym_lt, hb_eq, hbits_eq⟩ := decodeLitLen_literal_inv hdll hspec_sym
        -- Reduce the match on .literal in hds
        simp at hds
        -- hds should now be: decodeSymbols ... bits₁ n >>= ... = some (syms, rest)
        cases hds_rec : Deflate.Spec.decodeSymbols
            (litLengths.toList.map UInt8.toNat) (distLengths.toList.map UInt8.toNat)
            bits₁ n with
        | none => simp [hds_rec] at hds
        | some p₂ =>
          obtain ⟨syms', rest'⟩ := p₂
          simp only [hds_rec] at hds
          have heq := Option.some.inj hds
          have hsyms : syms = .literal b :: syms' := by
            have := congrArg Prod.fst heq; simp at this; exact this.symm
          have hrest_eq : rest = rest' := by
            have := congrArg Prod.snd heq; simp at this; exact this.symm
          -- resolveLZ77: .literal b :: syms' resolves
          rw [hsyms] at hlz
          simp only [Deflate.Spec.resolveLZ77_literal] at hlz
          -- hlz : resolveLZ77 syms' (output.data.toList ++ [b]) = some result
          have hpush : (output.push b).data.toList = output.data.toList ++ [b] := by simp
          -- output.size < maxOutputSize (result extends output ++ [b])
          have hout_ok : ¬(output.size ≥ maxOutputSize) := by
            have hpfx := Deflate.Spec.resolveLZ77_extends _ _ _ hlz
            have := List.IsPrefix.length_le hpfx
            simp at this; omega
          -- Apply IH with (output.push b) and remaining symbols
          rw [hbits_eq, ← hrest₁] at hds_rec
          rw [← hrest_eq] at hds_rec
          rw [← hpush] at hlz
          obtain ⟨br', hgo, hbr', hwf', hpos'⟩ :=
            ih br₁ (output.push b) syms' result hwf₁ hpos₁ hmax hds_rec hlz
          -- Unfold native go to show it takes the literal branch
          unfold Zip.Native.Inflate.decodeHuffman.go
          rw [show litTree.decode br = Except.ok (sym_nat.toUInt16, br₁) from hdec_lit]
          dsimp only [bind, Except.bind]
          -- sym < 256 branch
          have hsym_toNat : sym_nat.toUInt16.toNat = sym_nat := by
            simp [Nat.mod_eq_of_lt (by omega : sym_nat < UInt16.size)]
          have hsym_lt_u16 : sym_nat.toUInt16 < 256 := by
            rw [UInt16.lt_iff_toNat_lt, hsym_toNat]; exact hsym_lt
          simp only [hsym_lt_u16, ↓reduceIte, hout_ok, pure, Except.pure]
          -- sym_nat.toUInt16.toUInt8 = b
          have hsym_u8 : sym_nat.toUInt16.toUInt8 = b := by
            rw [hb_eq]; simp [UInt16.toUInt8, hsym_toNat]
          rw [hsym_u8]
          exact ⟨br', hgo, hbr', hwf', hpos'⟩
      | endOfBlock =>
        -- From decodeLitLen_endOfBlock_inv: sym_nat = 256, bits₁ = rest₁
        obtain ⟨hsym_eq, hbits_eq⟩ := decodeLitLen_endOfBlock_inv hdll hspec_sym
        -- Reduce the match on .endOfBlock in hds
        dsimp only [] at hds
        -- hds : pure ([.endOfBlock], bits₁) = some (syms, rest)
        simp only [pure, Pure.pure] at hds
        -- hds : some (...) = some (syms, rest)
        have heq := Option.some.inj hds
        have hsyms : syms = [.endOfBlock] := by
          have := congrArg Prod.fst heq; simp at this; exact this.symm
        have hrest_eq : rest = bits₁ := by
          have := congrArg Prod.snd heq; simp at this; exact this.symm
        -- resolveLZ77 [.endOfBlock] output = some output
        rw [hsyms] at hlz
        simp [Deflate.Spec.resolveLZ77_endOfBlock] at hlz
        -- hlz : output.data.toList = result
        -- Unfold native go
        unfold Zip.Native.Inflate.decodeHuffman.go
        rw [show litTree.decode br = Except.ok (sym_nat.toUInt16, br₁) from hdec_lit]
        dsimp only [bind, Except.bind]
        -- sym ≥ 256 (sym_nat = 256)
        have hsym_toNat : sym_nat.toUInt16.toNat = sym_nat := by
          have hsym_lt_u16 : sym_nat < UInt16.size :=
            Nat.lt_of_lt_of_le hsym_bound hlen_lit
          simp [Nat.mod_eq_of_lt hsym_lt_u16]
        have hsym_ge : ¬(sym_nat.toUInt16 < 256) := by
          rw [UInt16.lt_iff_toNat_lt, hsym_toNat, hsym_eq]
          exact Nat.not_lt.mpr (Nat.le.refl)
        simp only [hsym_ge, ↓reduceIte]
        -- sym == 256
        have hsym_beq : (sym_nat.toUInt16 == 256) = true := by
          rw [beq_iff_eq]
          exact UInt16.toNat_inj.mp (by rw [hsym_toNat, hsym_eq]; rfl)
        simp only [hsym_beq, ↓reduceIte]
        -- Goal: ∃ br', .ok (output, br₁) = .ok ({data := {toList := result}}, br') ∧ ...
        have hout_eq : output = ⟨⟨result⟩⟩ := by
          have : output.data.toList = result := hlz
          exact congrArg (fun x => (ByteArray.mk (Array.mk x))) this
        refine ⟨br₁, ?_, ?_, hwf₁, hpos₁⟩
        · rw [hout_eq]
        · rw [hrest₁, ← hbits_eq, ← hrest_eq]
      | reference len dist =>
        -- Extract intermediate values from decodeLitLen_reference_inv
        obtain ⟨hsym_ge, base, extra, extraVal, bits₂, dSym, bits₃,
          dBase, dExtra, dExtraVal,
          hlb, hle, hrb, hdd, hdb, hde, hrd, hlen_eq, hdist_eq⟩ :=
          decodeLitLen_reference_inv hdll hspec_sym
        -- Reduce the match on .reference in hds
        simp at hds
        cases hds_rec : Deflate.Spec.decodeSymbols
            (litLengths.toList.map UInt8.toNat) (distLengths.toList.map UInt8.toNat)
            bits₁ n with
        | none => simp [hds_rec] at hds
        | some p₂ =>
          obtain ⟨syms', rest'⟩ := p₂
          simp only [hds_rec] at hds
          have heq := Option.some.inj hds
          have hsyms : syms = .reference len dist :: syms' := by
            have := congrArg Prod.fst heq; simp at this; exact this.symm
          have hrest_eq : rest = rest' := by
            have := congrArg Prod.snd heq; simp at this; exact this.symm
          -- resolveLZ77: .reference len dist :: syms' resolves
          rw [hsyms] at hlz
          -- dist > 0 and dist ≤ output length (from resolveLZ77 succeeding)
          have hdist_pos : dist ≠ 0 := by
            intro hd0; rw [hd0] at hlz
            simp [Deflate.Spec.resolveLZ77_reference_dist_zero] at hlz
          have hdist_le : dist ≤ output.data.toList.length := by
            by_cases hd : dist ≤ output.data.toList.length
            · exact hd
            · exfalso
              have : dist > output.data.toList.length := by omega
              rw [Deflate.Spec.resolveLZ77_reference_dist_too_large _ _ _ _ this] at hlz
              simp at hlz
          -- Unfold resolveLZ77 for reference
          rw [Deflate.Spec.resolveLZ77_reference_valid len dist syms' output.data.toList
            hdist_pos hdist_le] at hlz
          -- Table index bounds from getElem? succeeding
          have hidx : sym_nat - 257 < 29 := by
            rw [Array.getElem?_eq_some_iff] at hlb
            obtain ⟨h, _⟩ := hlb; simp [Deflate.Spec.lengthBase] at h; exact h
          have hdidx : dSym < 30 := by
            rw [Array.getElem?_eq_some_iff] at hdb
            obtain ⟨h, _⟩ := hdb; simp [Deflate.Spec.distBase] at h; exact h
          -- Table value correspondence (spec getElem? → spec getElem!)
          have hbase_eq : base = Deflate.Spec.lengthBase[sym_nat - 257]! := by
            have h := getElem?_eq_some_getElem! Deflate.Spec.lengthBase
              (sym_nat - 257) (by simp [Deflate.Spec.lengthBase]; omega)
            rw [h] at hlb; exact (Option.some.inj hlb).symm
          have hextra_eq : extra = Deflate.Spec.lengthExtra[sym_nat - 257]! := by
            have h := getElem?_eq_some_getElem! Deflate.Spec.lengthExtra
              (sym_nat - 257) (by simp [Deflate.Spec.lengthExtra]; omega)
            rw [h] at hle; exact (Option.some.inj hle).symm
          have hdbase_eq : dBase = Deflate.Spec.distBase[dSym]! := by
            have h := getElem?_eq_some_getElem! Deflate.Spec.distBase dSym
              (by simp [Deflate.Spec.distBase]; omega)
            rw [h] at hdb; exact (Option.some.inj hdb).symm
          have hdextra_eq : dExtra = Deflate.Spec.distExtra[dSym]! := by
            have h := getElem?_eq_some_getElem! Deflate.Spec.distExtra dSym
              (by simp [Deflate.Spec.distExtra]; omega)
            rw [h] at hde; exact (Option.some.inj hde).symm
          -- Bounds for readBits_complete (extra ≤ 32 via native table correspondence)
          have hextra_le : extra ≤ 32 := by
            rw [hextra_eq]
            have : (Zip.Native.Inflate.lengthExtra[sym_nat - 257]!).toNat ≤ 32 :=
              lengthExtra_le_32 ⟨sym_nat - 257, hidx⟩
            have : (Zip.Native.Inflate.lengthExtra[sym_nat - 257]!).toNat =
                Deflate.Spec.lengthExtra[sym_nat - 257]! :=
              lengthExtra_eq ⟨sym_nat - 257, hidx⟩
            omega
          have hdextra_le : dExtra ≤ 32 := by
            rw [hdextra_eq]
            have : (Zip.Native.Inflate.distExtra[dSym]!).toNat ≤ 32 :=
              distExtra_le_32 ⟨dSym, hdidx⟩
            have : (Zip.Native.Inflate.distExtra[dSym]!).toNat =
                Deflate.Spec.distExtra[dSym]! :=
              distExtra_eq ⟨dSym, hdidx⟩
            omega
          have hextraVal_bound : extraVal < 2 ^ extra :=
            Deflate.Spec.readBitsLSB_bound hrb
          have hdExtraVal_bound : dExtraVal < 2 ^ dExtra :=
            Deflate.Spec.readBitsLSB_bound hrd
          -- Native readBits for length extra via readBits_complete
          obtain ⟨br₂, hrd_extra, hrest₂, hwf₂, hpos₂⟩ :=
            readBits_complete br₁ extra extraVal bits₂ hwf₁ hpos₁
              hextra_le hextraVal_bound (by rw [hrest₁]; exact hrb)
          -- Native distTree.decode via huffTree_decode_complete
          obtain ⟨cw_dist, hmem_dist_table, _⟩ :=
            Deflate.Correctness.decode_some_mem _ _ _ _ hdd
          have hmem_dist_codes : (dSym, cw_dist) ∈
              Huffman.Spec.allCodes (distLengths.toList.map UInt8.toNat) 15 := by
            obtain ⟨⟨s', cw'⟩, hm, he⟩ := List.mem_map.mp hmem_dist_table
            simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he; exact hm
          have hdSym_bound : dSym < distLengths.size := by
            rw [Huffman.Spec.allCodes_mem_iff] at hmem_dist_codes
            simp at hmem_dist_codes; exact hmem_dist_codes.1
          obtain ⟨br₃, hdec_dist, hrest₃, hwf₃, hpos₃⟩ :=
            huffTree_decode_complete distLengths 15 (by omega) distTree br₂
              dSym bits₃ hwf₂ hpos₂ hdist hvdist hlen_dist hdSym_bound
              (by rw [hrest₂]; exact hdd)
          -- Native readBits for distance extra
          -- hrd : readBitsLSB dExtra bits₃ = some (dExtraVal, bits₁)
          obtain ⟨br₄, hrd_dextra, hrest₄, hwf₄, hpos₄⟩ :=
            readBits_complete br₃ dExtra dExtraVal bits₁ hwf₃ hpos₃
              hdextra_le hdExtraVal_bound (by rw [hrest₃]; exact hrd)
          -- Helper: extraVal.toUInt32.toNat = extraVal
          have hextraVal_toNat : extraVal.toUInt32.toNat = extraVal :=
            Nat.mod_eq_of_lt (by calc extraVal < 2 ^ extra := hextraVal_bound
              _ ≤ 2 ^ 32 := Nat.pow_le_pow_right (by omega) hextra_le)
          -- Helper: dExtraVal.toUInt32.toNat = dExtraVal
          have hdExtraVal_toNat : dExtraVal.toUInt32.toNat = dExtraVal :=
            Nat.mod_eq_of_lt (by calc dExtraVal < 2 ^ dExtra := hdExtraVal_bound
              _ ≤ 2 ^ 32 := Nat.pow_le_pow_right (by omega) hdextra_le)
          -- Native↔spec table value bridges
          have hnative_extra_eq :
              (Zip.Native.Inflate.lengthExtra[sym_nat - 257]!).toNat = extra := by
            have : (Zip.Native.Inflate.lengthExtra[sym_nat - 257]!).toNat =
                Deflate.Spec.lengthExtra[sym_nat - 257]! :=
              lengthExtra_eq ⟨sym_nat - 257, hidx⟩
            rw [hextra_eq]; omega
          have hnative_dextra_eq :
              (Zip.Native.Inflate.distExtra[dSym]!).toNat = dExtra := by
            have : (Zip.Native.Inflate.distExtra[dSym]!).toNat =
                Deflate.Spec.distExtra[dSym]! :=
              distExtra_eq ⟨dSym, hdidx⟩
            rw [hdextra_eq]; omega
          have hnative_len : (Zip.Native.Inflate.lengthBase[sym_nat - 257]!).toNat +
              extraVal.toUInt32.toNat = len := by
            have : (Zip.Native.Inflate.lengthBase[sym_nat - 257]!).toNat =
                Deflate.Spec.lengthBase[sym_nat - 257]! :=
              lengthBase_eq ⟨sym_nat - 257, hidx⟩
            rw [hlen_eq, hbase_eq, hextraVal_toNat]; omega
          have hnative_dist : (Zip.Native.Inflate.distBase[dSym]!).toNat +
              dExtraVal.toUInt32.toNat = dist := by
            have : (Zip.Native.Inflate.distBase[dSym]!).toNat =
                Deflate.Spec.distBase[dSym]! :=
              distBase_eq ⟨dSym, hdidx⟩
            rw [hdist_eq, hdbase_eq, hdExtraVal_toNat]; omega
          -- Unfold native go to show it takes the reference branch
          unfold Zip.Native.Inflate.decodeHuffman.go
          rw [show litTree.decode br = Except.ok (sym_nat.toUInt16, br₁) from hdec_lit]
          dsimp only [bind, Except.bind]
          -- sym ≥ 256
          have hsym_toNat : sym_nat.toUInt16.toNat = sym_nat :=
            Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hsym_bound hlen_lit)
          have hsym_ge_u16 : ¬(sym_nat.toUInt16 < 256) := by
            simp only [UInt16.lt_iff_toNat_lt, hsym_toNat]
            show ¬(sym_nat < 256); omega
          simp only [hsym_ge_u16, ↓reduceIte]
          -- sym ≠ 256
          have hsym_ne_256 : ¬((sym_nat.toUInt16 == 256) = true) := by
            rw [beq_iff_eq]; intro heq
            have := congrArg UInt16.toNat heq
            rw [hsym_toNat] at this; simp at this; omega
          simp only [hsym_ne_256, Bool.false_eq_true, ↓reduceIte]
          -- idx bounds check: sym.toNat - 257 < lengthBase.size
          have hidx_ok : ¬(sym_nat - 257 ≥ Zip.Native.Inflate.lengthBase.size) := by
            simp [Zip.Native.Inflate.lengthBase]; omega
          simp only [hsym_toNat, hidx_ok, ↓reduceIte, pure, Except.pure]
          -- readBits for length extra
          rw [hnative_extra_eq,
            show br₁.readBits extra = .ok (extraVal.toUInt32, br₂) from hrd_extra]
          dsimp only [bind, Except.bind]
          -- distTree.decode br₂ succeeds
          rw [show distTree.decode br₂ = .ok (dSym.toUInt16, br₃) from hdec_dist]
          dsimp only [bind, Except.bind]
          -- distance idx bounds check
          have hdSym_toNat : dSym.toUInt16.toNat = dSym :=
            Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hdSym_bound hlen_dist)
          have hdidx_ok : ¬(dSym ≥ Zip.Native.Inflate.distBase.size) := by
            simp [Zip.Native.Inflate.distBase]; omega
          simp only [hdSym_toNat, hdidx_ok, ↓reduceIte]
          -- readBits for distance extra
          rw [hnative_dextra_eq,
            show br₃.readBits dExtra = .ok (dExtraVal.toUInt32, br₄) from hrd_dextra]
          dsimp only [bind, Except.bind]
          -- Distance > output.size check
          have hdist_ok : ¬((Zip.Native.Inflate.distBase[dSym]!).toNat +
              dExtraVal.toUInt32.toNat > output.size) := by
            rw [hnative_dist]; simp [Array.length_toList, ByteArray.size_data] at hdist_le; omega
          simp only [hdist_ok, ↓reduceIte]
          -- MaxOutputSize check
          have hmax_ok : ¬(output.size +
              ((Zip.Native.Inflate.lengthBase[sym_nat - 257]!).toNat +
                extraVal.toUInt32.toNat) > maxOutputSize) := by
            rw [hnative_len]
            have hpfx := Deflate.Spec.resolveLZ77_extends _ _ _ hlz
            have hpfx_len := List.IsPrefix.length_le hpfx
            simp only [List.length_append, List.length_ofFn,
              Array.length_toList, ByteArray.size_data] at hpfx_len
            omega
          simp only [hmax_ok, ↓reduceIte]
          -- Apply IH with copyLoop output
          have hcopy := copyLoop_eq_ofFn output len dist
            (by omega)
            (by simp [Array.length_toList, ByteArray.size_data] at hdist_le; omega)
          -- Bridge native copyLoop to spec form
          have hcopy_native : (Zip.Native.Inflate.copyLoop output
              (output.size - ((Zip.Native.Inflate.distBase[dSym]!).toNat +
                dExtraVal.toUInt32.toNat))
              ((Zip.Native.Inflate.distBase[dSym]!).toNat + dExtraVal.toUInt32.toNat) 0
              ((Zip.Native.Inflate.lengthBase[sym_nat - 257]!).toNat +
                extraVal.toUInt32.toNat)).data.toList =
              output.data.toList ++ List.ofFn (fun (i : Fin len) =>
                output.data.toList[(output.data.toList.length - dist) +
                  (i.val % dist)]!) := by
            rw [hnative_dist, hnative_len,
              show output.size = output.data.toList.length from by
                simp [Array.length_toList, ByteArray.size_data]]
            exact hcopy
          -- IH needs: decodeSymbols br₄.toBits n = some (syms', rest)
          -- hds_rec: decodeSymbols ... bits₁ n = some (syms', rest')
          -- hrest₄: br₄.toBits = bits₁, hrest_eq: rest = rest'
          have hds_br₄ : Deflate.Spec.decodeSymbols
              (litLengths.toList.map UInt8.toNat) (distLengths.toList.map UInt8.toNat)
              br₄.toBits n = some (syms', rest) := by
            rw [hrest₄, hrest_eq]; exact hds_rec
          -- hlz : resolveLZ77 syms' (output.data.toList ++ copied) = some result
          -- The copied list uses output.data.toList.length
          let newOutput := Zip.Native.Inflate.copyLoop output
            (output.size - ((Zip.Native.Inflate.distBase[dSym]!).toNat +
              dExtraVal.toUInt32.toNat))
            ((Zip.Native.Inflate.distBase[dSym]!).toNat + dExtraVal.toUInt32.toNat) 0
            ((Zip.Native.Inflate.lengthBase[sym_nat - 257]!).toNat +
              extraVal.toUInt32.toNat)
          set_option maxRecDepth 2048 in
          have hlz' : Deflate.Spec.resolveLZ77 syms' newOutput.data.toList =
              some result := by rw [hcopy_native]; exact hlz
          exact ih br₄ newOutput syms' result hwf₄ hpos₄ hmax hds_br₄ hlz'

end Deflate.Correctness
