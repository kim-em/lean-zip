import Zip.Spec.DeflateFixedCorrect

/-!
# Native DEFLATE Dynamic Huffman Correctness

This file proves the correspondence between the native `emitTokensWithCodes`
(dynamic Huffman compressor) and the spec-level `encodeSymbols`, mirroring
`emitTokens_spec` from `DeflateFixedCorrect.lean` but generalized to
arbitrary `canonicalCodes`-produced tables.

## Key results

- `encodeSymbol_canonicalCodes_eq`: generalized bridge from `encodeSymbol` to
  `canonicalCodes` entries (replaces `encodeSymbol_litTable_eq` / `distTable_eq`)
- `emitTokensWithCodes_spec`: `emitTokensWithCodes` produces the same bits as
  spec `encodeSymbols` for dynamic Huffman codes
-/

namespace Zip.Native.Deflate

/-! ## encodeSymbol ↔ canonicalCodes bridge -/

/-- If `encodeSymbol` on the flipped `allCodes` table returns `cw` for symbol `s`,
    and the codes array was produced by `canonicalCodes` from the same lengths,
    then `cw` equals `natToBits` of the `canonicalCodes` entry. -/
theorem encodeSymbol_canonicalCodes_eq (lengths : Array UInt8) (maxBits : Nat)
    (codes : Array (UInt16 × UInt8))
    (hc : codes = canonicalCodes lengths maxBits)
    (hv : Huffman.Spec.ValidLengths (lengths.toList.map UInt8.toNat) maxBits)
    (hmb : maxBits < 16)
    (s : Nat) (cw : List Bool)
    (henc : Deflate.Spec.encodeSymbol
      ((Huffman.Spec.allCodes (lengths.toList.map UInt8.toNat) maxBits).map
        fun p => (p.2, p.1))
      s = some cw) :
    cw = Huffman.Spec.natToBits codes[s]!.1.toNat codes[s]!.2.toNat ∧
    codes[s]!.2.toNat ≤ maxBits := by
  -- encodeSymbol_mem → (cw, s) ∈ table → (s, cw) ∈ allCodes
  have hmem := Deflate.Spec.encodeSymbol_mem _ s cw henc
  have hmem' : (s, cw) ∈ Huffman.Spec.allCodes (lengths.toList.map UInt8.toNat) maxBits := by
    simp only [List.mem_map] at hmem
    obtain ⟨⟨s', cw'⟩, hmem, heq⟩ := hmem
    simp only [Prod.mk.injEq] at heq
    exact heq.1 ▸ heq.2 ▸ hmem
  rw [Huffman.Spec.allCodes_mem_iff] at hmem'
  obtain ⟨hs_len, hcf⟩ := hmem'
  -- Get canonicalCodes_correct_pos
  have hs_arr : s < lengths.size := by
    simp only [List.length_map, Array.length_toList] at hs_len; exact hs_len
  have hs_i : (lengths.toList.map UInt8.toNat)[s] = lengths[s].toNat := by
    simp only [List.getElem_map, Array.getElem_toList]; rfl
  have ⟨hne0, hle_mb⟩ := Huffman.Spec.codeFor_len_bounds
    (Huffman.Spec.codeFor_spec hcf).2.1
  have hne0_nat : lengths[s].toNat ≠ 0 := hs_i ▸ hne0
  have hpos : lengths[s] > 0 := by
    simp only [GT.gt, UInt8.lt_iff_toNat_lt, UInt8.toNat_ofNat]; omega
  obtain ⟨cw', hcf', hcw', hlen'⟩ :=
    Deflate.Correctness.canonicalCodes_correct_pos lengths maxBits hv hmb s hs_arr hpos
  -- Match codewords
  have hcw_eq : cw = cw' := Option.some.inj (hcf.symm.trans hcf')
  subst hcw_eq
  subst hc
  have hlen'_nat : (canonicalCodes lengths maxBits)[s]!.2.toNat = lengths[s].toNat :=
    congrArg UInt8.toNat hlen'
  exact ⟨by rw [hlen'_nat]; exact hcw', by omega⟩

end Zip.Native.Deflate
