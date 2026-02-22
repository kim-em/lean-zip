import Zip.Spec.HuffmanCorrect

/-!
# DEFLATE Decompressor Correctness

States the main correctness theorem: the native pure-Lean DEFLATE
decompressor (`Zip.Native.Inflate.inflateRaw`) agrees with the formal
bitstream specification (`Deflate.Spec.decode`).

The proof is decomposed into layers matching the decode pipeline:
1. **Bitstream layer** (`BitstreamCorrect`): `BitReader` operations correspond
   to `bytesToBits` + `readBitsLSB`
2. **Huffman layer** (`HuffmanCorrect`): `HuffTree.decode` corresponds to
   `Huffman.Spec.decode`
3. **LZ77 layer**: the native copy loop corresponds to `resolveLZ77`
4. **Block layer**: each block type decodes identically
5. **Stream layer**: the block sequence produces the same output
-/

namespace Deflate.Correctness

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
      obtain ⟨cw, hmem_table, hbits⟩ :=
        Deflate.Correctness.decode_some_mem specTable bits v rest hdec
      have hleaf :=
        Deflate.Correctness.fromLengths_hasLeaf lengths tree htree hv v cw (to_codes hmem_table)
      have hdb' := Deflate.Correctness.decodeBits_of_hasLeaf tree cw v.toUInt16 rest hleaf
      rw [hbits] at hdb; rw [hdb'] at hdb; simp at hdb
  | some (sym, rest) =>
    simp only [Option.map]
    obtain ⟨cw, hleaf, hbits⟩ :=
      Deflate.Correctness.hasLeaf_of_decodeBits tree bits sym rest hdb
    have hmem_codes :=
      Deflate.Correctness.fromLengths_leaf_spec lengths tree htree hv hlen_bound cw sym hleaf
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
  obtain ⟨hdb, _⟩ :=
    Deflate.Correctness.decode_go_decodeBits tree br 0 sym br' hwf hdecode_go
  -- Step 2: decodeBits → spec decode via tree-table correspondence
  have hspec := decodeBits_eq_spec_decode lengths tree br.toBits htree hv hlen_bound
  -- Connect the two
  rw [hdb] at hspec; simp only [Option.map] at hspec
  exact ⟨br'.toBits, hspec.symm, rfl⟩

/-! ## Stored block correctness -/

/-- If the native stored-block decoder succeeds, the spec's `decodeStored`
    also succeeds and produces the same bytes and remaining bit position.
    The `output` parameter is pass-through (native prepends to output). -/
theorem decodeStored_correct (br : Zip.Native.BitReader)
    (output : ByteArray) (maxOutputSize : Nat)
    (output' : ByteArray) (br' : Zip.Native.BitReader)
    (hwf : br.bitOff < 8)
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (h : Zip.Native.Inflate.decodeStored br output maxOutputSize = .ok (output', br')) :
    ∃ storedBytes rest,
      Deflate.Spec.decodeStored br.toBits = some (storedBytes, rest) ∧
      output'.data.toList = output.data.toList ++ storedBytes ∧
      br'.toBits = rest := by
  -- Unfold native decodeStored
  simp only [Zip.Native.Inflate.decodeStored, bind, Except.bind] at h
  -- First readUInt16LE (reads LEN)
  cases hlen_r : br.readUInt16LE with
  | error e => simp [hlen_r] at h
  | ok p1 =>
    obtain ⟨len, br1⟩ := p1
    simp only [hlen_r] at h
    -- Second readUInt16LE (reads NLEN)
    cases hnlen_r : br1.readUInt16LE with
    | error e => simp [hnlen_r] at h
    | ok p2 =>
      obtain ⟨nlen, br2⟩ := p2
      simp only [hnlen_r] at h
      -- Complement check (if len ^^^ nlen != 0xFFFF then throw else ...)
      split at h
      · simp at h
      · rename_i hcomp
        -- Size check (if output.size + len.toNat > maxOutputSize then throw else ...)
        simp only [pure, Except.pure] at h
        split at h
        · simp at h
        · -- readBytes
          cases hbytes_r : br2.readBytes len.toNat with
          | error e => simp [hbytes_r] at h
          | ok p3 =>
            obtain ⟨bytes, br3⟩ := p3
            simp only [hbytes_r, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            -- output' = output ++ bytes, br' = br3
            -- Now chain spec correspondence
            -- First readUInt16LE → spec readBitsLSB 16 (alignToByte br.toBits)
            obtain ⟨rest1, hspec_len, hrest1⟩ :=
              readUInt16LE_toBits br len br1 hwf hpos hlen_r
            -- br1 is byte-aligned
            have hwf1 : br1.bitOff = 0 := readUInt16LE_wf br len br1 hlen_r
            -- Second readUInt16LE → spec readBitsLSB 16 (alignToByte br1.toBits)
            obtain ⟨rest2, hspec_nlen, hrest2⟩ :=
              readUInt16LE_toBits br1 nlen br2 (by omega) (Or.inl hwf1) hnlen_r
            -- alignToByte br1.toBits = br1.toBits (already byte-aligned)
            rw [alignToByte_id_of_aligned br1 hwf1] at hspec_nlen
            -- br2 is byte-aligned
            have hwf2 : br2.bitOff = 0 := readUInt16LE_wf br1 nlen br2 hnlen_r
            -- readBytes → spec readNBytes (br3 was substituted for br')
            obtain ⟨rest3, hspec_bytes, hrest3⟩ :=
              readBytes_toBits br2 len.toNat bytes br3 (by omega) (Or.inl hwf2) hbytes_r
            -- alignToByte br2.toBits = br2.toBits
            rw [alignToByte_id_of_aligned br2 hwf2] at hspec_bytes
            -- Complement check: native ¬(len ^^^ nlen != 0xFFFF) → spec guard
            have hcomp_eq : len ^^^ nlen = 0xFFFF := by
              simp [bne_iff_ne] at hcomp; exact hcomp
            have hcomp_nat : len.toNat ^^^ nlen.toNat = 0xFFFF := by
              rw [← UInt16.toNat_xor, hcomp_eq]; rfl
            -- Prepare spec-level hypotheses in unified form
            have h_nlen : Deflate.Spec.readBitsLSB 16 rest1 = some (nlen.toNat, rest2) := by
              rw [← hrest1]; exact hspec_nlen
            have h_bytes : Deflate.Spec.decodeStored.readNBytes len.toNat rest2 [] =
                some (bytes.data.toList, rest3) := by
              rw [← hrest2]; exact hspec_bytes
            -- Construct the spec result
            refine ⟨bytes.data.toList, rest3, ?_, ?_, hrest3⟩
            · -- Spec.decodeStored br.toBits = some (bytes.data.toList, rest3)
              simp only [Deflate.Spec.decodeStored, bind, Option.bind,
                hspec_len, h_nlen, hcomp_nat, h_bytes]
              rfl
            · -- (output ++ bytes).data.toList = output.data.toList ++ bytes.data.toList
              simp

/-! ## Huffman block correctness -/

/-- `HuffTree.decode` preserves the well-formedness invariant `bitOff < 8`. -/
private theorem decode_wf (tree : Zip.Native.HuffTree)
    (br : Zip.Native.BitReader) (sym : UInt16) (br' : Zip.Native.BitReader)
    (hwf : br.bitOff < 8)
    (h : tree.decode br = .ok (sym, br')) : br'.bitOff < 8 := by
  have hgo : Zip.Native.HuffTree.decode.go tree br 0 = .ok (sym, br') := by
    simp only [Zip.Native.HuffTree.decode] at h; exact h
  exact (Deflate.Correctness.decode_go_decodeBits tree br 0 sym br' hwf hgo).2

/-- `readBits.go` preserves the well-formedness invariant `bitOff < 8`. -/
private theorem readBits_go_wf (br : Zip.Native.BitReader)
    (acc : UInt32) (shift k : Nat) (val : UInt32) (br' : Zip.Native.BitReader)
    (hwf : br.bitOff < 8)
    (h : Zip.Native.BitReader.readBits.go br acc shift k = .ok (val, br')) :
    br'.bitOff < 8 := by
  induction k generalizing br acc shift with
  | zero =>
    simp only [Zip.Native.BitReader.readBits.go] at h
    obtain ⟨_, rfl⟩ := Except.ok.inj h; exact hwf
  | succ k ih =>
    simp only [Zip.Native.BitReader.readBits.go, bind, Except.bind] at h
    cases hrd : br.readBit with
    | error e => simp [hrd] at h
    | ok p =>
      obtain ⟨bit, br₁⟩ := p
      simp only [hrd] at h
      exact ih br₁ _ _ (readBit_wf br bit br₁ hwf hrd) h

/-- `readBits` preserves the well-formedness invariant `bitOff < 8`. -/
private theorem readBits_wf (br : Zip.Native.BitReader)
    (n : Nat) (val : UInt32) (br' : Zip.Native.BitReader)
    (hwf : br.bitOff < 8)
    (h : br.readBits n = .ok (val, br')) : br'.bitOff < 8 := by
  simp only [Zip.Native.BitReader.readBits] at h
  exact readBits_go_wf br 0 0 n val br' hwf h

/-! ## Table correspondence lemmas -/

set_option maxRecDepth 1024 in
private theorem lengthBase_eq : ∀ i : Fin 29,
    (Zip.Native.Inflate.lengthBase[i.val]!).toNat =
    (Deflate.Spec.lengthBase[i.val]!) := by decide

set_option maxRecDepth 1024 in
private theorem lengthExtra_eq : ∀ i : Fin 29,
    (Zip.Native.Inflate.lengthExtra[i.val]!).toNat =
    (Deflate.Spec.lengthExtra[i.val]!) := by decide

set_option maxRecDepth 1024 in
private theorem distBase_eq : ∀ i : Fin 30,
    (Zip.Native.Inflate.distBase[i.val]!).toNat =
    (Deflate.Spec.distBase[i.val]!) := by decide

set_option maxRecDepth 1024 in
private theorem distExtra_eq : ∀ i : Fin 30,
    (Zip.Native.Inflate.distExtra[i.val]!).toNat =
    (Deflate.Spec.distExtra[i.val]!) := by decide

set_option maxRecDepth 1024 in
private theorem lengthExtra_le_32 : ∀ i : Fin 29,
    (Zip.Native.Inflate.lengthExtra[i.val]!).toNat ≤ 32 := by decide

set_option maxRecDepth 1024 in
private theorem distExtra_le_32 : ∀ i : Fin 30,
    (Zip.Native.Inflate.distExtra[i.val]!).toNat ≤ 32 := by decide

set_option maxRecDepth 1024 in
private theorem spec_distBase_pos : ∀ i : Fin 30,
    (Deflate.Spec.distBase[i.val]!) ≥ 1 := by decide

/-- `ba[j]!` equals `ba.data.toList[j]!` when `j` is in bounds. -/
private theorem ba_getElem!_eq_toList (ba : ByteArray) (j : Nat) (hj : j < ba.size) :
    ba[j]! = ba.data.toList[j]! := by
  rw [getElem!_pos ba j hj,
      getElem!_pos ba.data.toList j (by simp [Array.length_toList, ByteArray.size_data]; exact hj)]
  show ba.data[j] = ba.data.toList[j]
  rw [Array.getElem_toList]

/-- `ByteArray.push` preserves earlier elements: for `j < buf.size`,
    `(buf.push b)[j]! = buf[j]!`. -/
private theorem push_getElem_lt (buf : ByteArray) (b : UInt8) (j : Nat)
    (hj : j < buf.size) :
    (buf.push b)[j]! = buf[j]! := by
  have hj' : j < (buf.push b).size := by simp [ByteArray.size_push]; omega
  rw [getElem!_pos (buf.push b) j hj', getElem!_pos buf j hj]
  exact Array.getElem_push_lt hj

/-- `ByteArray.push` appends one element to `data.toList`. -/
private theorem push_data_toList (buf : ByteArray) (b : UInt8) :
    (buf.push b).data.toList = buf.data.toList ++ [b] := by
  simp [ByteArray.push, Array.toList_push]

/-- Generalized loop invariant for `copyLoop`. After running from index
    `k`, the result has the original buffer contents plus `List.ofFn` of
    the remaining elements. -/
private theorem copyLoop_spec (output : ByteArray) (start distance : Nat)
    (k length : Nat) (buf : ByteArray)
    (hd_pos : distance > 0)
    (hstart : start + distance ≤ output.size)
    (hk_le : k ≤ length)
    (hbuf_size : buf.size = output.size + k)
    (hbuf_prefix : ∀ j, j < output.size → buf[j]! = output[j]!)
    (hbuf_data : buf.data.toList = output.data.toList ++
      List.ofFn (fun (i : Fin k) =>
        output.data.toList[start + (i.val % distance)]!)) :
    (Zip.Native.Inflate.copyLoop buf start distance k length).data.toList =
      output.data.toList ++
      List.ofFn (fun (i : Fin length) =>
        output.data.toList[start + (i.val % distance)]!) := by
  unfold Zip.Native.Inflate.copyLoop
  split
  · rename_i hk_lt
    have hmod_lt : k % distance < distance := Nat.mod_lt k hd_pos
    have hidx_lt : start + (k % distance) < output.size := by omega
    have hnew_eq : buf[start + (k % distance)]! = output[start + (k % distance)]! :=
      hbuf_prefix _ hidx_lt
    apply copyLoop_spec output start distance (k + 1) length
    · exact hd_pos
    · exact hstart
    · omega
    · simp [ByteArray.size_push]; omega
    · intro j hj
      rw [push_getElem_lt _ _ _ (by rw [hbuf_size]; omega)]
      exact hbuf_prefix j hj
    · rw [push_data_toList, hbuf_data, List.append_assoc]
      congr 1
      rw [hnew_eq, ba_getElem!_eq_toList _ _ hidx_lt]
      symm
      exact List.ofFn_succ_last
  · rename_i hk_nlt
    have hk_eq : k = length := by omega
    subst hk_eq
    exact hbuf_data
termination_by length - k

/-- The native copy loop produces the same result as the spec's `List.ofFn`
    for LZ77 back-references. -/
private theorem copyLoop_eq_ofFn
    (output : ByteArray) (length distance : Nat)
    (hd_pos : distance > 0) (hd_le : distance ≤ output.size) :
    (Zip.Native.Inflate.copyLoop output (output.size - distance) distance
      0 length).data.toList =
    output.data.toList ++
      List.ofFn (fun (i : Fin length) =>
        output.data.toList[(output.size - distance) +
          (i.val % distance)]!) := by
  exact copyLoop_spec output (output.size - distance) distance 0 length output
    hd_pos (by omega) (Nat.zero_le _) rfl (fun _ _ => rfl) (by simp [List.ofFn])

set_option maxRecDepth 4096 in
/-- If the native Huffman block decoder succeeds, the spec's `decodeSymbols`
    produces a corresponding list of LZ77 symbols, and resolving those symbols
    with the current accumulator produces the same output.

    This connects the native's inline symbol decoding + LZ77 resolution
    (which interleaves decode and copy) to the spec's two-phase approach
    (collect all symbols, then resolve). -/
theorem decodeHuffman_correct
    (litLengths distLengths : Array UInt8)
    (litTree distTree : Zip.Native.HuffTree)
    (maxOutputSize fuel : Nat)
    (br : Zip.Native.BitReader) (output : ByteArray)
    (output' : ByteArray) (br' : Zip.Native.BitReader)
    (hwf : br.bitOff < 8)
    (hlit : Zip.Native.HuffTree.fromLengths litLengths = .ok litTree)
    (hdist : Zip.Native.HuffTree.fromLengths distLengths = .ok distTree)
    (hvlit : Huffman.Spec.ValidLengths (litLengths.toList.map UInt8.toNat) 15)
    (hvdist : Huffman.Spec.ValidLengths (distLengths.toList.map UInt8.toNat) 15)
    (hlen_lit : litLengths.size ≤ UInt16.size)
    (hlen_dist : distLengths.size ≤ UInt16.size)
    (h : Zip.Native.Inflate.decodeHuffman.go litTree distTree maxOutputSize
          br output fuel = .ok (output', br')) :
    ∃ specFuel syms rest,
      Deflate.Spec.decodeSymbols (litLengths.toList.map UInt8.toNat)
        (distLengths.toList.map UInt8.toNat) br.toBits specFuel =
        some (syms, rest) ∧
      Deflate.Spec.resolveLZ77 syms output.data.toList =
        some output'.data.toList ∧
      br'.toBits = rest ∧
      br'.bitOff < 8 := by
  induction fuel generalizing br output with

  | zero =>
    unfold Zip.Native.Inflate.decodeHuffman.go at h; simp at h
  | succ n ih =>
    -- Unfold one step of decodeHuffman.go — split on litTree.decode
    unfold Zip.Native.Inflate.decodeHuffman.go at h
    cases hdec : litTree.decode br with
    | error e => simp [hdec, bind, Except.bind] at h
    | ok p =>
      obtain ⟨sym, br₁⟩ := p
      simp only [hdec, bind, Except.bind] at h
      -- Get spec-level Huffman decode correspondence
      have hwf₁ := decode_wf litTree br sym br₁ hwf hdec
      obtain ⟨rest₁, hspec_sym, hrest₁⟩ :=
        huffTree_decode_correct litLengths litTree br sym br₁ hwf hlit hvlit hlen_lit hdec
      -- Case split on symbol value
      split at h
      · -- sym < 256: literal byte
        rename_i hsym
        -- h has: if output.size ≥ maxOutputSize then error else go br₁ (output.push sym.toUInt8) n
        split at h
        · simp at h -- maxOutputSize check failed → contradiction
        · -- Simplify the pure PUnit.unit match
          simp only [pure, Except.pure] at h
          -- Apply IH
          obtain ⟨sf, syms, rest, hds, hlz, hbr, hwf'⟩ := ih br₁ (output.push sym.toUInt8) hwf₁ h
          have hsym_nat : sym.toNat < 256 := hsym
          -- decodeLitLen returns .literal
          have hlit_dec : Deflate.Spec.decodeLitLen
              (litLengths.toList.map UInt8.toNat) (distLengths.toList.map UInt8.toNat)
              br.toBits = some (.literal sym.toNat.toUInt8, rest₁) := by
            unfold Deflate.Spec.decodeLitLen
            simp only [bind, Option.bind, hspec_sym, hsym_nat, ↓reduceIte, pure]
          -- decodeSymbols (sf + 1) gives .literal :: syms
          have hds' : Deflate.Spec.decodeSymbols (litLengths.toList.map UInt8.toNat)
              (distLengths.toList.map UInt8.toNat) br.toBits (sf + 1) =
              some (.literal sym.toNat.toUInt8 :: syms, rest) := by
            simp only [Deflate.Spec.decodeSymbols, bind, Option.bind, hlit_dec,
              ← hrest₁, hds, pure]
          -- resolveLZ77 (.literal :: syms) output = some output'
          have hlz' : Deflate.Spec.resolveLZ77
              (.literal sym.toNat.toUInt8 :: syms) output.data.toList =
              some output'.data.toList := by
            simp only [Deflate.Spec.resolveLZ77_literal]
            have : (output.push sym.toUInt8).data.toList =
                output.data.toList ++ [sym.toNat.toUInt8] := by simp
            rw [this] at hlz; exact hlz
          exact ⟨sf + 1, .literal sym.toNat.toUInt8 :: syms, rest, hds', hlz', hbr, hwf'⟩
      · -- sym ≥ 256
        split at h
        · -- sym == 256: end of block
          rename_i hge hsym256
          obtain ⟨rfl, rfl⟩ := Except.ok.inj h
          -- sym.toNat = 256
          have hsym_nat : sym.toNat = 256 := by
            simp [beq_iff_eq] at hsym256; simp [hsym256]
          -- decodeLitLen returns endOfBlock
          have hlit_dec : Deflate.Spec.decodeLitLen
              (litLengths.toList.map UInt8.toNat) (distLengths.toList.map UInt8.toNat)
              br.toBits = some (.endOfBlock, rest₁) := by
            unfold Deflate.Spec.decodeLitLen
            simp only [bind, Option.bind, hspec_sym, hsym_nat,
              show ¬((256 : Nat) < 256) from by omega,
              show ((256 : Nat) == 256) = true from rfl, ↓reduceIte, pure]
          refine ⟨1, [.endOfBlock], rest₁, ?_, rfl, hrest₁, hwf₁⟩
          simp only [Deflate.Spec.decodeSymbols, bind, Option.bind, hlit_dec, pure]
        · -- sym > 256: length/distance code
          rename_i hge hne256
          -- sym.toNat > 256, sym.toNat ≠ 256
          have hsym_ge : sym.toNat ≥ 257 := by
            have h1 : sym.toNat ≥ 256 := Nat.le_of_not_lt hge
            have h2 : sym.toNat ≠ 256 := by
              intro heq; apply hne256; simp [beq_iff_eq]
              exact UInt16.toNat_inj.mp (by simp; exact heq)
            omega
          -- Step 1: idx bounds check
          split at h
          · simp at h
          · rename_i hidx
            have hidx : sym.toNat - 257 < 29 := by
              simp [Zip.Native.Inflate.lengthBase] at hidx; omega
            -- Clean up pure PUnit.unit patterns
            simp only [pure, Except.pure] at h
            -- Step 2: readBits for length extra bits
            cases hextra_r :
              br₁.readBits (Zip.Native.Inflate.lengthExtra[sym.toNat - 257]!).toNat with
            | error e => simp [hextra_r] at h
            | ok p =>
              obtain ⟨extraBits, br₂⟩ := p
              simp only [hextra_r] at h
              -- Step 3: distTree.decode
              cases hdist_dec : distTree.decode br₂ with
              | error e => simp [hdist_dec] at h
              | ok p =>
                obtain ⟨distSym, br₃⟩ := p
                simp only [hdist_dec] at h
                -- Step 4: distance idx bounds
                split at h
                · simp at h
                · rename_i hdidx
                  have hdidx : distSym.toNat < 30 := by
                    simp [Zip.Native.Inflate.distBase] at hdidx; omega
                  -- Step 5: readBits for distance extra
                  cases hdextra_r :
                    br₃.readBits (Zip.Native.Inflate.distExtra[distSym.toNat]!).toNat with
                  | error e => simp [hdextra_r] at h
                  | ok p =>
                    obtain ⟨dExtraBits, br₄⟩ := p
                    simp only [hdextra_r] at h
                    -- Step 6: distance > output.size check
                    split at h
                    · simp at h
                    · rename_i hdist_ok
                      -- Step 7: maxOutputSize check
                      split at h
                      · simp at h
                      · rename_i hmax_ok
                        -- h : go br₄ (copyLoop output start distance 0 length) n = .ok (output', br')
                        -- Well-formedness chain
                        have hwf₂ : br₂.bitOff < 8 :=
                          readBits_wf br₁ _ extraBits br₂ hwf₁ hextra_r
                        have hwf₃ : br₃.bitOff < 8 :=
                          decode_wf distTree br₂ distSym br₃ hwf₂ hdist_dec
                        have hwf₄ : br₄.bitOff < 8 :=
                          readBits_wf br₃ _ dExtraBits br₄ hwf₃ hdextra_r
                        -- Apply IH
                        obtain ⟨sf, syms, rest, hds, hlz, hbr, hwf'⟩ :=
                          ih br₄ _ hwf₄ h
                        -- Spec-level readBits for length extra
                        obtain ⟨rest₂, hspec_extra, hrest₂⟩ :=
                          readBits_toBits br₁ _ extraBits br₂ hwf₁
                            (lengthExtra_le_32 ⟨sym.toNat - 257, hidx⟩)
                            hextra_r
                        -- Spec-level distance tree decode
                        obtain ⟨rest₃, hspec_dist_sym, hrest₃⟩ :=
                          huffTree_decode_correct distLengths distTree br₂
                            distSym br₃ hwf₂ hdist hvdist hlen_dist hdist_dec
                        -- Spec-level readBits for distance extra
                        obtain ⟨rest₄, hspec_dextra, hrest₄⟩ :=
                          readBits_toBits br₃ _ dExtraBits br₄ hwf₃
                            (distExtra_le_32 ⟨distSym.toNat, hdidx⟩)
                            hdextra_r
                        -- Table correspondence
                        have hlen_eq : Zip.Native.Inflate.lengthBase[sym.toNat - 257]!.toNat =
                            Deflate.Spec.lengthBase[sym.toNat - 257]! :=
                          lengthBase_eq ⟨sym.toNat - 257, hidx⟩
                        have hdist_val_eq : Zip.Native.Inflate.distBase[distSym.toNat]!.toNat =
                            Deflate.Spec.distBase[distSym.toNat]! :=
                          distBase_eq ⟨distSym.toNat, hdidx⟩
                        -- Prepare chained spec hypotheses in terms of rest₁
                        have h_extra : Deflate.Spec.readBitsLSB
                            (Deflate.Spec.lengthExtra[sym.toNat - 257]!) rest₁ =
                            some (extraBits.toNat, rest₂) := by
                          rw [← lengthExtra_eq ⟨sym.toNat - 257, hidx⟩,
                              ← hrest₁]; exact hspec_extra
                        have h_dist : Huffman.Spec.decode
                            ((Huffman.Spec.allCodes
                              (distLengths.toList.map UInt8.toNat)).map
                              fun x => match x with | (s, cw) => (cw, s))
                            rest₂ = some (distSym.toNat, rest₃) := by
                          rw [← hrest₂]; exact hspec_dist_sym
                        have h_dextra : Deflate.Spec.readBitsLSB
                            (Deflate.Spec.distExtra[distSym.toNat]!) rest₃ =
                            some (dExtraBits.toNat, rest₄) := by
                          rw [← distExtra_eq ⟨distSym.toNat, hdidx⟩,
                              ← hrest₃]; exact hspec_dextra
                        -- Build decodeLitLen result
                        have hlit_dec : Deflate.Spec.decodeLitLen
                            (litLengths.toList.map UInt8.toNat)
                            (distLengths.toList.map UInt8.toNat)
                            br.toBits = some (.reference
                              (Deflate.Spec.lengthBase[sym.toNat - 257]! + extraBits.toNat)
                              (Deflate.Spec.distBase[distSym.toNat]! + dExtraBits.toNat),
                            rest₄) := by
                          unfold Deflate.Spec.decodeLitLen
                          simp only [bind, Option.bind, hspec_sym,
                            if_neg (show ¬(sym.toNat < 256) from by omega)]
                          have hne256 : (sym.toNat == 256) = false := by
                            cases heq : sym.toNat == 256 <;> simp_all [beq_iff_eq]
                          simp only [hne256, Bool.false_eq_true, ↓reduceIte]
                          have h1 : Deflate.Spec.lengthBase[sym.toNat - 257]? =
                              some Deflate.Spec.lengthBase[sym.toNat - 257]! := by
                            rw [getElem!_pos Deflate.Spec.lengthBase _ hidx]
                            exact getElem?_pos Deflate.Spec.lengthBase _ hidx
                          have h2 : Deflate.Spec.lengthExtra[sym.toNat - 257]? =
                              some Deflate.Spec.lengthExtra[sym.toNat - 257]! := by
                            rw [getElem!_pos Deflate.Spec.lengthExtra _ hidx]
                            exact getElem?_pos Deflate.Spec.lengthExtra _ hidx
                          have h3 : Deflate.Spec.distBase[distSym.toNat]? =
                              some Deflate.Spec.distBase[distSym.toNat]! := by
                            rw [getElem!_pos Deflate.Spec.distBase _ hdidx]
                            exact getElem?_pos Deflate.Spec.distBase _ hdidx
                          have h4 : Deflate.Spec.distExtra[distSym.toNat]? =
                              some Deflate.Spec.distExtra[distSym.toNat]! := by
                            rw [getElem!_pos Deflate.Spec.distExtra _ hdidx]
                            exact getElem?_pos Deflate.Spec.distExtra _ hdidx
                          simp only [h1, h2, h_extra, h3, h4, h_dist,
                            h_dextra, pure]
                        -- Build decodeSymbols result
                        have hds' : Deflate.Spec.decodeSymbols
                            (litLengths.toList.map UInt8.toNat)
                            (distLengths.toList.map UInt8.toNat)
                            br.toBits (sf + 1) =
                            some (.reference
                              (Deflate.Spec.lengthBase[sym.toNat - 257]! + extraBits.toNat)
                              (Deflate.Spec.distBase[distSym.toNat]! + dExtraBits.toNat)
                              :: syms, rest) := by
                          simp only [Deflate.Spec.decodeSymbols, bind, Option.bind,
                            hlit_dec, ← hrest₄, hds, pure]
                        refine ⟨sf + 1, _, rest, hds', ?_, hbr, hwf'⟩
                        -- Unfold resolveLZ77 for .reference
                        simp only [Deflate.Spec.resolveLZ77]
                        -- Guard conditions
                        have hdist_pos' : ¬(Deflate.Spec.distBase[distSym.toNat]! +
                            dExtraBits.toNat == 0) := by
                          simp only [beq_iff_eq]
                          have : Deflate.Spec.distBase[distSym.toNat]! ≥ 1 :=
                            spec_distBase_pos ⟨distSym.toNat, hdidx⟩
                          omega
                        have hdist_le' : ¬(Deflate.Spec.distBase[distSym.toNat]! +
                            dExtraBits.toNat > output.data.toList.length) := by
                          rw [Array.length_toList, ByteArray.size_data,
                            ← hdist_val_eq]; exact hdist_ok
                        simp only [hdist_pos', hdist_le', decide_false,
                          Bool.false_or, Bool.false_eq_true, ↓reduceIte]
                        -- Copy loop correspondence
                        have hcopy := copyLoop_eq_ofFn output
                          (Zip.Native.Inflate.lengthBase[sym.toNat - 257]!.toNat +
                            extraBits.toNat)
                          (Zip.Native.Inflate.distBase[distSym.toNat]!.toNat +
                            dExtraBits.toNat)
                          (by have : Deflate.Spec.distBase[distSym.toNat]! ≥ 1 :=
                                spec_distBase_pos ⟨distSym.toNat, hdidx⟩
                              rw [hdist_val_eq]; omega)
                          (by rw [Nat.not_lt] at hdist_ok; exact hdist_ok)
                        -- Substitute copyLoop result into IH before changing table names
                        rw [hcopy] at hlz
                        -- Now rewrite native table values to spec values in hlz and goal
                        rw [hlen_eq, hdist_val_eq] at hlz
                        -- Align output.size vs output.data.toList.length
                        conv at hlz => rw [show output.size = output.data.toList.length from by
                          simp [Array.length_toList, ByteArray.size_data]]
                        exact hlz

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
  -- Unfold inflate: it calls inflateRaw data 0 maxOutputSize and discards endPos
  simp only [Zip.Native.Inflate.inflate, bind, Except.bind] at h
  cases hinf : Zip.Native.Inflate.inflateRaw data 0 maxOutputSize with
  | error e => simp [hinf] at h
  | ok p =>
    simp [hinf, pure, Except.pure] at h
    have := inflate_correct data 0 maxOutputSize p.1 p.2 (by rw [hinf])
    simp at this
    rw [← h]; exact this

end Deflate.Correctness
