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
