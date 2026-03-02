import Zip.Spec.DecodeCorrect
import Zip.Spec.BitReaderInvariant

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

/-- If `arr[i]? = some val` and `i < arr.size`, then `val = arr[i]!`. -/
private theorem getElem?_some_eq_getElem! [Inhabited α] {arr : Array α} {i : Nat} {val : α}
    (hsome : arr[i]? = some val) (h : i < arr.size) : val = arr[i]! := by
  rw [Array.getElem?_eq_some_getElem! arr i h] at hsome; exact (Option.some.inj hsome).symm

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
  | none => simp only [hlen_spec] at hspec; contradiction
  | some p1 =>
    obtain ⟨len_val, bits1⟩ := p1
    simp only [hlen_spec] at hspec
    -- Second readBitsLSB 16
    cases hnlen_spec : Deflate.Spec.readBitsLSB 16 bits1 with
    | none => simp only [hnlen_spec] at hspec; contradiction
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
      · -- guard passed
        simp [hguard] at hspec -- bare simp: Option do-notation match chain
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
            simp [Zip.Native.BitReader.alignToByte, hbr2_off]] -- bare simp: struct field reduction
          -- Unfold readUInt16LE on br1 to extract the bounds check
          simp only [Zip.Native.BitReader.readUInt16LE, Zip.Native.BitReader.alignToByte,
            hbr1_off] at hrd2
          by_cases hle2 : br1.data.size < br1.pos + 2
          · simp [hle2] at hrd2 -- bare simp: readUInt16LE if-reduction
          · simp [hle2] at hrd2 -- bare simp: readUInt16LE if-reduction
            obtain ⟨_, rfl⟩ := hrd2
            have hd1 : br1.data = br.data := readUInt16LE_data br _ br1 hrd1
            simp only [hd1] at hle2 ⊢
            omega
        -- Derive readNBytes output length = len_val for size check
        have hbytes_len : storedBytes.length = len_val := by
          have := readNBytes_output_length hspec
          simp at this -- bare simp: List.length_reverse
          exact this
        -- Use readBytes_complete
        obtain ⟨br3, hrd3, hbr3_bits, hbr3_off, hbr3_pos⟩ :=
          readBytes_complete br2 len_val storedBytes rest (by omega) hbr2_pos halign_pos2 hspec
        -- Complement check in native
        have hcomp : len_val.toUInt16 ^^^ nlen_val.toUInt16 = 0xFFFF := by
          simp [beq_iff_eq] at hguard -- bare simp: beq to Prop conversion
          exact UInt16.toNat_inj.mp (by
            rw [UInt16.toNat_xor]
            simp [Nat.toUInt16, Nat.mod_eq_of_lt hlen_bound, Nat.mod_eq_of_lt hnlen_bound] -- bare simp: UInt16 modular arithmetic
            exact hguard)
        have hcomp_ne : ¬(len_val.toUInt16 ^^^ nlen_val.toUInt16 != 0xFFFF) := by
          simp [hcomp] -- bare simp: bne reduction
        -- Size check in native
        have hsize_ok : ¬(output.size + len_val > maxOutputSize) := by
          rw [← hbytes_len]; omega
        -- Bridge len_val.toUInt16.toNat = len_val for readBytes
        have hlen_toNat : len_val.toUInt16.toNat = len_val := by
          simp [Nat.toUInt16, Nat.mod_eq_of_lt hlen_bound] -- bare simp: UInt16 modular arithmetic
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
        simp [guard, Bool.false_eq_true] at hspec -- bare simp: guard false reduction

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
  | none => simp only [hd] at h; contradiction
  | some p =>
    obtain ⟨sym_nat, rest₁⟩ := p
    exact ⟨sym_nat, rest₁, rfl⟩

/-- When the Huffman decode returns `sym_nat ≥ 257`, the reference chain in `decodeLitLen`
    always produces `.reference`. Used to derive contradictions in the literal and endOfBlock
    completeness lemmas. -/
private theorem decodeLitLen_ge257_isReference {litLengths distLengths : List Nat}
    {bits rest : List Bool} {sym : Deflate.Spec.LZ77Symbol} {sym_nat : Nat} {rest₁ : List Bool}
    (hdll : Deflate.Spec.decodeLitLen litLengths distLengths bits = some (sym, rest))
    (hd : Huffman.Spec.decode
        ((Huffman.Spec.allCodes litLengths).map fun (s, cw) => (cw, s))
        bits = some (sym_nat, rest₁))
    (h256 : ¬(sym_nat < 256)) (h256ne : ¬(sym_nat = 256)) :
    ∃ len dist, sym = .reference len dist := by
  unfold Deflate.Spec.decodeLitLen at hdll
  -- bare simp: 7-level Option.bind chain after unfold decodeLitLen
  simp [hd] at hdll
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
  | some q =>
    simp [hlb, hle, hrb, hdd, hdb, hde, hrd] at hdll
    exact ⟨_, _, hdll.1.symm⟩

/-- If `decodeLitLen` returns `.literal b` and the Huffman decode returns
    `(sym_nat, rest₁)`, then `sym_nat < 256`, `b = sym_nat.toUInt8`, and `rest = rest₁`. -/
private theorem decodeLitLen_literal_inv {litLengths distLengths : List Nat}
    {bits rest : List Bool} {b : UInt8} {sym_nat : Nat} {rest₁ : List Bool}
    (hdll : Deflate.Spec.decodeLitLen litLengths distLengths bits = some (.literal b, rest))
    (hd : Huffman.Spec.decode
        ((Huffman.Spec.allCodes litLengths).map fun (s, cw) => (cw, s))
        bits = some (sym_nat, rest₁)) :
    sym_nat < 256 ∧ b = sym_nat.toUInt8 ∧ rest = rest₁ := by
  by_cases h256 : sym_nat < 256
  · unfold Deflate.Spec.decodeLitLen at hdll
    -- bare simp: Option do-notation match chain after unfold
    simp [hd, h256] at hdll
    exact ⟨h256, hdll.1.symm, hdll.2.symm⟩
  · exfalso
    by_cases h256eq : sym_nat = 256
    · unfold Deflate.Spec.decodeLitLen at hdll
      simp [hd, h256eq] at hdll -- bare simp: Option do-notation match chain
    · obtain ⟨_, _, h⟩ := decodeLitLen_ge257_isReference hdll hd h256 h256eq
      exact absurd h nofun

/-- If `decodeLitLen` returns `.endOfBlock` and the Huffman decode returns
    `(sym_nat, rest₁)`, then `sym_nat = 256` and `rest = rest₁`. -/
private theorem decodeLitLen_endOfBlock_inv {litLengths distLengths : List Nat}
    {bits rest : List Bool} {sym_nat : Nat} {rest₁ : List Bool}
    (hdll : Deflate.Spec.decodeLitLen litLengths distLengths bits = some (.endOfBlock, rest))
    (hd : Huffman.Spec.decode
        ((Huffman.Spec.allCodes litLengths).map fun (s, cw) => (cw, s))
        bits = some (sym_nat, rest₁)) :
    sym_nat = 256 ∧ rest = rest₁ := by
  by_cases h256 : sym_nat < 256
  · exfalso; unfold Deflate.Spec.decodeLitLen at hdll
    simp [hd, h256] at hdll -- bare simp: Option do-notation match chain
  · by_cases h256eq : sym_nat = 256
    · unfold Deflate.Spec.decodeLitLen at hdll
      simp [hd, h256eq] at hdll -- bare simp: Option do-notation match chain
      exact ⟨h256eq, hdll.symm⟩
    · exfalso
      obtain ⟨_, _, h⟩ := decodeLitLen_ge257_isReference hdll hd h256 h256eq
      exact absurd h nofun

set_option maxRecDepth 1024 in
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
  simp [hd] at hdll -- bare simp: Option do-notation match chain
  by_cases h256 : sym_nat < 256
  · exfalso; simp [h256] at hdll -- bare simp: Option do-notation match chain
  · by_cases h256eq : sym_nat = 256
    · exfalso
      simp only [↓reduceIte, h256eq] at hdll
      exact absurd (Option.some.inj hdll) nofun
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

set_option maxRecDepth 2048 in
set_option maxHeartbeats 400000 in
/-- **Completeness for Huffman block decode**: if the spec `decodeSymbols`
    succeeds and `resolveLZ77` produces output, then the native
    `decodeHuffman.go` also succeeds with the same output.

    This is the reverse of `decodeHuffman_correct`.

    `hple` and `hdata` ensure the native termination guards pass:
    the BitReader position is within bounds and `dataSize` is large
    enough to cover the data. Both hold when `dataSize = br.data.size`
    (the value used by the `decodeHuffman` wrapper). -/
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
    (dataSize : Nat)
    (hple : br.pos ≤ br.data.size)
    (hdata : br.data.size ≤ dataSize)
    (hds : Deflate.Spec.decodeSymbols (litLengths.toList.map UInt8.toNat)
        (distLengths.toList.map UInt8.toNat) br.toBits =
        some (syms, rest))
    (hlz : Deflate.Spec.resolveLZ77 syms output.data.toList = some result) :
    ∃ br', Zip.Native.Inflate.decodeHuffman.go litTree distTree maxOutputSize
        dataSize br output = .ok (⟨⟨result⟩⟩, br') ∧
      br'.toBits = rest ∧
      br'.bitOff < 8 ∧
      (br'.bitOff = 0 ∨ br'.pos < br'.data.size) := by
  -- Unfold spec decodeSymbols to extract decodeLitLen
  unfold Deflate.Spec.decodeSymbols at hds
  simp only [bind, Option.bind] at hds
  cases hdll : Deflate.Spec.decodeLitLen
      (litLengths.toList.map UInt8.toNat) (distLengths.toList.map UInt8.toNat)
      br.toBits with
  | none => simp only [hdll] at hds; contradiction
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
      simp only [List.length_map, Array.length_toList] at hmem_codes; exact hmem_codes.1
    -- Get native litTree.decode via huffTree_decode_complete
    obtain ⟨br₁, hdec_lit, hrest₁, hwf₁, hpos₁⟩ :=
      huffTree_decode_complete litLengths 15 (by omega) litTree br
        sym_nat rest₁ hwf hpos hlit hvlit hsym_bound hspec_sym
    -- Data preservation and pos bound from decode
    have ⟨hdata₁, _, hple₁⟩ :=
      Zip.Native.decode_inv litTree br br₁ sym_nat.toUInt16 hdec_lit hpos hple
    -- UInt16 roundtrip — shared across all cases
    have hsym_toNat : sym_nat.toUInt16.toNat = sym_nat :=
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hsym_bound hlen_lit)
    -- Bits get shorter (for WF guard)
    have hlen_shorter : rest₁.length < br.toBits.length :=
      Huffman.Spec.decode_shorter _ _ _ _ hspec_sym
        (Deflate.Correctness.specTable_cw_nonempty _ _)
    -- bitPos advances: ¬(br₁.bitPos ≤ br.bitPos)
    have hbp_advance : ¬(br₁.bitPos ≤ br.bitPos) := by
      intro hle
      have htl := Deflate.Correctness.toBits_length br
      have htl₁ := Deflate.Correctness.toBits_length br₁
      rw [hdata₁] at htl₁
      rw [← hrest₁] at hlen_shorter
      simp only [Zip.Native.BitReader.bitPos] at hle
      omega
    -- bitPos stays within dataSize: ¬(dataSize * 8 < br₁.bitPos)
    have hbp_bound : ¬(dataSize * 8 < br₁.bitPos) := by
      simp only [Zip.Native.BitReader.bitPos]
      rw [hdata₁] at hple₁
      rcases hpos₁ with h | h <;> simp_all <;> omega
    -- Case split on sym_val (the LZ77Symbol from decodeLitLen)
    cases sym_val with
    | literal b =>
        -- From decodeLitLen_literal_inv: sym_nat < 256, b = sym_nat.toUInt8, bits₁ = rest₁
        obtain ⟨hsym_lt, hb_eq, hbits_eq⟩ := decodeLitLen_literal_inv hdll hspec_sym
        -- Reduce the match on .literal in hds
        dsimp at hds
        -- hds should now be: decodeSymbols ... bits₁ >>= ... = some (syms, rest)
        -- WF guard in decodeSymbols: bits₁.length < br.toBits.length
        -- This is satisfied since hlen_shorter and hbits_eq : bits₁ = rest₁
        rw [hbits_eq] at hds
        -- WF guard: rest₁.length < br.toBits.length
        simp only [hlen_shorter] at hds
        cases hds_rec : Deflate.Spec.decodeSymbols
            (litLengths.toList.map UInt8.toNat) (distLengths.toList.map UInt8.toNat)
            rest₁ with
        | none => simp only [hds_rec] at hds; contradiction
        | some p₂ =>
          obtain ⟨syms', rest'⟩ := p₂
          simp [hds_rec] at hds -- bare simp: Option do-notation match chain
          obtain ⟨hsyms, hrest_eq⟩ : syms = .literal b :: syms' ∧ rest = rest' :=
            ⟨hds.1.symm, hds.2.symm⟩
          -- resolveLZ77: .literal b :: syms' resolves
          rw [hsyms] at hlz
          simp only [Deflate.Spec.resolveLZ77_literal] at hlz
          -- hlz : resolveLZ77 syms' (output.data.toList ++ [b]) = some result
          have hpush : (output.push b).data.toList = output.data.toList ++ [b] := by
            simp -- bare simp: ByteArray.push toList
          -- output.size < maxOutputSize (result extends output ++ [b])
          have hout_ok : ¬(output.size ≥ maxOutputSize) := by
            have hpfx := Deflate.Spec.resolveLZ77_extends _ _ _ hlz
            have := List.IsPrefix.length_le hpfx
            simp at this; omega -- bare simp: List.length bridging
          -- Apply IH with (output.push b) and remaining symbols
          rw [← hrest₁] at hds_rec
          rw [← hrest_eq] at hds_rec
          rw [← hpush] at hlz
          -- data preservation for recursive call
          have hdata₁' : br₁.data.size ≤ dataSize := by rw [hdata₁]; exact hdata
          obtain ⟨br', hgo, hbr', hwf', hpos'⟩ :=
            decodeHuffman_complete litLengths distLengths litTree distTree
              maxOutputSize br₁ (output.push b) syms' rest result
              hwf₁ hpos₁ hlit hdist hvlit hvdist hlen_lit hlen_dist hmax
              dataSize hple₁ hdata₁' hds_rec hlz
          -- Unfold native go to show it takes the literal branch
          unfold Zip.Native.Inflate.decodeHuffman.go
          rw [show litTree.decode br = Except.ok (sym_nat.toUInt16, br₁) from hdec_lit]
          dsimp only [bind, Except.bind]
          -- sym < 256 branch
          have hsym_lt_u16 : sym_nat.toUInt16 < 256 := by
            rw [UInt16.lt_iff_toNat_lt, hsym_toNat]; exact hsym_lt
          simp only [hsym_lt_u16, ↓reduceIte, hout_ok, pure, Except.pure]
          -- sym_nat.toUInt16.toUInt8 = b
          have hsym_u8 : sym_nat.toUInt16.toUInt8 = b := by
            rw [hb_eq]; simp only [UInt16.toUInt8, hsym_toNat]
          rw [hsym_u8]
          -- bitPos guards
          simp only [hbp_advance, ↓reduceDIte, hbp_bound]
          exact ⟨br', hgo, hbr', hwf', hpos'⟩
    | endOfBlock =>
        -- From decodeLitLen_endOfBlock_inv: sym_nat = 256, bits₁ = rest₁
        obtain ⟨hsym_eq, hbits_eq⟩ := decodeLitLen_endOfBlock_inv hdll hspec_sym
        -- Reduce the match on .endOfBlock in hds → syms = [.endOfBlock], rest = bits₁
        dsimp only [] at hds; simp only [pure, Pure.pure] at hds
        have heq := (Option.some.inj hds).symm
        have hsyms : syms = [.endOfBlock] := congrArg Prod.fst heq
        have hrest_eq : rest = bits₁ := congrArg Prod.snd heq
        -- resolveLZ77 [.endOfBlock] output = some output
        rw [hsyms] at hlz
        simp only [Deflate.Spec.resolveLZ77_endOfBlock, Option.some.injEq] at hlz
        -- Unfold native go
        unfold Zip.Native.Inflate.decodeHuffman.go
        rw [show litTree.decode br = Except.ok (sym_nat.toUInt16, br₁) from hdec_lit]
        dsimp only [bind, Except.bind]
        -- sym ≥ 256 (sym_nat = 256)
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
        -- Reduce the match on .reference in hds (also resolves WF guard)
        simp at hds -- bare simp: Option do-notation match reduction
        -- WF guard for rest after decodeLitLen
        -- bits₁ is the rest from decodeLitLen (.reference case)
        -- From decodeLitLen_reference_inv, bits₁ is the rest from readBitsLSB dExtra bits₃
        -- which equals the final `rest` from decodeLitLen. So bits₁ = the rest after all
        -- the reference decoding (Huffman + length extra + dist Huffman + dist extra)
        -- Actually, bits₁ comes from decodeLitLen, so it should equal the final bits
        -- after the full .reference decoding chain.
        -- The WF guard checks bits₁.length < br.toBits.length
        -- We need to show this. From hrd, bits₁ is the rest after readBitsLSB dExtra bits₃.
        -- We'll derive this from the chain of length reductions.
        have hbits₁_shorter : bits₁.length < br.toBits.length := by
          -- bits₁ is the final rest from the decodeLitLen .reference chain
          -- The Huffman decode: rest₁.length < br.toBits.length (hlen_shorter)
          -- readBitsLSB extra rest₁ = some (extraVal, bits₂): bits₂.length + extra = rest₁.length
          have h1 := Deflate.Spec.readBitsLSB_some_length hrb
          -- Huffman decode on bits₂: bits₃ shorter than bits₂
          -- Distance Huffman decode: bits₃ shorter
          -- readBitsLSB dExtra bits₃ = some (dExtraVal, bits₁): bits₁.length + dExtra = bits₃.length
          have h3 := Deflate.Spec.readBitsLSB_some_length hrd
          omega
        rw [show bits₁ = bits₁ from rfl] at hds
        simp only [hbits₁_shorter] at hds
        cases hds_rec : Deflate.Spec.decodeSymbols
            (litLengths.toList.map UInt8.toNat) (distLengths.toList.map UInt8.toNat)
            bits₁ with
        | none => simp [hds_rec] at hds -- bare simp: Option do-notation match chain
        | some p₂ =>
          obtain ⟨syms', rest'⟩ := p₂
          simp [hds_rec] at hds -- bare simp: Option do-notation match chain
          obtain ⟨hsyms, hrest_eq⟩ : syms = .reference len dist :: syms' ∧ rest = rest' :=
            ⟨hds.1.symm, hds.2.symm⟩
          -- resolveLZ77: .reference len dist :: syms' resolves
          rw [hsyms] at hlz
          -- dist > 0 and dist ≤ output length (from resolveLZ77 succeeding)
          have hdist_pos : dist ≠ 0 := by
            intro hd0; rw [hd0] at hlz
            simp only [Deflate.Spec.resolveLZ77_reference_dist_zero] at hlz
            contradiction
          have hdist_le : dist ≤ output.data.toList.length := by
            by_cases hd : dist ≤ output.data.toList.length
            · exact hd
            · exfalso
              have : dist > output.data.toList.length := by omega
              rw [Deflate.Spec.resolveLZ77_reference_dist_too_large _ _ _ _ this] at hlz
              exact absurd hlz nofun
          -- Unfold resolveLZ77 for reference
          rw [Deflate.Spec.resolveLZ77_reference_valid len dist syms' output.data.toList
            hdist_pos hdist_le] at hlz
          -- Table index bounds from getElem? succeeding
          have hidx : sym_nat - 257 < 29 := by
            rw [Array.getElem?_eq_some_iff] at hlb
            obtain ⟨h, _⟩ := hlb; simp only [Deflate.Spec.lengthBase] at h; exact h
          have hdidx : dSym < 30 := by
            rw [Array.getElem?_eq_some_iff] at hdb
            obtain ⟨h, _⟩ := hdb; simp only [Deflate.Spec.distBase] at h; exact h
          -- Table value correspondence (spec getElem? → spec getElem!)
          have hbase_eq : base = Deflate.Spec.lengthBase[sym_nat - 257]! :=
            getElem?_some_eq_getElem! hlb (by show _ < 29; omega)
          have hextra_eq : extra = Deflate.Spec.lengthExtra[sym_nat - 257]! :=
            getElem?_some_eq_getElem! hle (by show _ < 29; omega)
          have hdbase_eq : dBase = Deflate.Spec.distBase[dSym]! :=
            getElem?_some_eq_getElem! hdb (by show _ < 30; omega)
          have hdextra_eq : dExtra = Deflate.Spec.distExtra[dSym]! :=
            getElem?_some_eq_getElem! hde (by show _ < 30; omega)
          -- Bounds for readBits_complete (extra ≤ 32 via native table correspondence)
          have hextra_le : extra ≤ 32 := hextra_eq ▸
            (lengthExtra_eq ⟨sym_nat - 257, hidx⟩) ▸
            (lengthExtra_le_32 ⟨sym_nat - 257, hidx⟩)
          have hdextra_le : dExtra ≤ 32 := hdextra_eq ▸
            (distExtra_eq ⟨dSym, hdidx⟩) ▸
            (distExtra_le_32 ⟨dSym, hdidx⟩)
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
            simp only [List.length_map, Array.length_toList] at hmem_dist_codes
            exact hmem_dist_codes.1
          obtain ⟨br₃, hdec_dist, hrest₃, hwf₃, hpos₃⟩ :=
            huffTree_decode_complete distLengths 15 (by omega) distTree br₂
              dSym bits₃ hwf₂ hpos₂ hdist hvdist hdSym_bound
              (by rw [hrest₂]; exact hdd)
          -- Native readBits for distance extra
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
            rw [hextra_eq]; exact lengthExtra_eq ⟨sym_nat - 257, hidx⟩
          have hnative_dextra_eq :
              (Zip.Native.Inflate.distExtra[dSym]!).toNat = dExtra := by
            rw [hdextra_eq]; exact distExtra_eq ⟨dSym, hdidx⟩
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
          have hsym_ge_u16 : ¬(sym_nat.toUInt16 < 256) := by
            simp only [UInt16.lt_iff_toNat_lt, hsym_toNat]
            show ¬(sym_nat < 256); omega
          simp only [hsym_ge_u16, ↓reduceIte]
          -- sym ≠ 256
          have hsym_ne_256 : ¬((sym_nat.toUInt16 == 256) = true) := by
            rw [beq_iff_eq]; intro heq
            have := congrArg UInt16.toNat heq
            rw [hsym_toNat] at this; simp at this; omega -- bare simp: UInt16 toNat injection
          simp only [hsym_ne_256, Bool.false_eq_true, ↓reduceIte]
          -- idx bounds check: sym.toNat - 257 < lengthBase.size
          have hidx_ok : ¬(sym_nat - 257 ≥ Zip.Native.Inflate.lengthBase.size) := by
            show ¬(_ ≥ 29); omega
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
            show ¬(_ ≥ 30); omega
          simp only [hdSym_toNat, hdidx_ok, ↓reduceIte]
          -- readBits for distance extra
          rw [hnative_dextra_eq,
            show br₃.readBits dExtra = .ok (dExtraVal.toUInt32, br₄) from hrd_dextra]
          dsimp only [bind, Except.bind]
          -- Distance > output.size check
          have hdist_ok : ¬((Zip.Native.Inflate.distBase[dSym]!).toNat +
              dExtraVal.toUInt32.toNat > output.size) := by
            rw [hnative_dist]; simp only [Array.length_toList, ByteArray.size_data] at hdist_le; omega
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
          -- bitPos guards for reference branch (br₄)
          -- Data preservation chain
          have ⟨hd₂, _, hple₂⟩ := Zip.Native.readBits_inv br₁ br₂ _ _ hrd_extra hpos₁ hple₁
          have ⟨hd₃, _, hple₃⟩ := Zip.Native.decode_inv distTree br₂ br₃ _ hdec_dist hpos₂ hple₂
          have ⟨hd₄, _, hple₄⟩ := Zip.Native.readBits_inv br₃ br₄ _ _ hrd_dextra hpos₃ hple₃
          have hbp_advance₄ : ¬(br₄.bitPos ≤ br.bitPos) := by
            intro hle'
            have htl := Deflate.Correctness.toBits_length br
            have htl₄ := Deflate.Correctness.toBits_length br₄
            rw [hd₄, hd₃, hd₂, hdata₁] at htl₄
            rw [← hrest₄] at hbits₁_shorter
            simp only [Zip.Native.BitReader.bitPos] at hle'
            omega
          have hbp_bound₄ : ¬(dataSize * 8 < br₄.bitPos) := by
            simp only [Zip.Native.BitReader.bitPos]
            have : br₄.data.size ≤ dataSize := by
              have : br₄.data.size = br.data.size := by rw [hd₄, hd₃, hd₂, hdata₁]
              omega
            rcases hpos₄ with h | h <;> omega
          simp only [hbp_advance₄, ↓reduceDIte, hbp_bound₄]
          -- Apply IH with copyLoop output
          have hcopy := copyLoop_eq_ofFn output len dist
            (by omega)
            (by simp only [Array.length_toList, ByteArray.size_data] at hdist_le; omega)
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
                simp only [Array.length_toList, ByteArray.size_data]]
            exact hcopy
          let newOutput := Zip.Native.Inflate.copyLoop output
            (output.size - ((Zip.Native.Inflate.distBase[dSym]!).toNat +
              dExtraVal.toUInt32.toNat))
            ((Zip.Native.Inflate.distBase[dSym]!).toNat + dExtraVal.toUInt32.toNat) 0
            ((Zip.Native.Inflate.lengthBase[sym_nat - 257]!).toNat +
              extraVal.toUInt32.toNat)
          -- IH needs: decodeSymbols br₄.toBits = some (syms', rest)
          have hds_br₄ : Deflate.Spec.decodeSymbols
              (litLengths.toList.map UInt8.toNat) (distLengths.toList.map UInt8.toNat)
              br₄.toBits = some (syms', rest) := by
            rw [hrest₄, hrest_eq]; exact hds_rec
          -- hlz' for IH
          set_option maxRecDepth 1024 in
          have hlz' : Deflate.Spec.resolveLZ77 syms' newOutput.data.toList =
              some result := by rw [hcopy_native]; exact hlz
          -- Data preservation for recursive call
          have hdata₄ : br₄.data.size ≤ dataSize := by
            have : br₄.data.size = br.data.size := by rw [hd₄, hd₃, hd₂, hdata₁]
            omega
          have hple₄' : br₄.pos ≤ br₄.data.size := hple₄
          obtain ⟨br', hgo, hbr', hwf', hpos'⟩ :=
            decodeHuffman_complete litLengths distLengths litTree distTree
              maxOutputSize br₄ newOutput syms' rest result
              hwf₄ hpos₄ hlit hdist hvlit hvdist hlen_lit hlen_dist hmax
              dataSize hple₄' hdata₄ hds_br₄ hlz'
          exact ⟨br', hgo, hbr', hwf', hpos'⟩
  termination_by br.toBits.length

end Deflate.Correctness

