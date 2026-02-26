import Zip.Spec.DeflateFixedCorrect
import Zip.Spec.DeflateDynamicCorrect

/-!
# Unified DEFLATE Roundtrip (Phase B4 Capstone)

Proves the unified roundtrip theorem for `deflateRaw`:
`inflate (deflateRaw data level) = .ok data`.

`deflateRaw` is defined in `Zip/Native/DeflateDynamic.lean` and selects the
compression strategy based on level (0 = stored, 1 = fixed Huffman,
2-4 = lazy LZ77 + fixed, 5+ = dynamic Huffman).

This composes the per-level roundtrip theorems:
- `inflate_deflateStoredPure` (Level 0)
- `inflate_deflateFixed` (Level 1)
- `inflate_deflateLazy` (Levels 2-4)
- `inflate_deflateDynamic` (Levels 5+)
-/

namespace Zip.Native.Deflate

open Zip.Spec.DeflateStoredCorrect (inflate_deflateStoredPure)

/-- Unified DEFLATE roundtrip: inflate ∘ deflateRaw = identity.
    This is the Phase B4 capstone theorem from PLAN.md.
    The size bound (1 GiB) is now determined by the native inflate's default
    maxOutputSize, not the decoder fuel (which supports ~500 PB). -/
theorem inflate_deflateRaw (data : ByteArray) (level : UInt8)
    (hsize : data.size < 1024 * 1024 * 1024) :
    Zip.Native.Inflate.inflate (deflateRaw data level) = .ok data := by
  unfold deflateRaw
  split
  · exact inflate_deflateStoredPure data (by omega)
  · split
    · exact inflate_deflateFixedIter data (by omega)
    · split
      · exact inflate_deflateLazy data hsize
      · exact inflate_deflateDynamic data (by omega)

/-- The output of `deflateRaw` decomposes into content bits plus short padding.
    This is needed by `inflateRaw_endPos_ge` to establish that the native decoder
    consumes all of the deflated byte array. -/
theorem deflateRaw_pad (data : ByteArray) (level : UInt8) :
    ∃ (contentBits padding : List Bool),
      Deflate.Spec.bytesToBits (deflateRaw data level) = contentBits ++ padding ∧
      padding.length < 8 := by
  unfold deflateRaw
  split
  · -- Level 0: stored blocks — all byte-aligned, padding = []
    exact ⟨Deflate.Spec.bytesToBits (Zip.Spec.DeflateStoredCorrect.deflateStoredPure data),
      [], by simp, by simp⟩
  · split
    · -- Level 1: fixed Huffman (iterative LZ77)
      rw [deflateFixedIter, lz77GreedyIter_eq_lz77Greedy]
      obtain ⟨bits, _, hbytes⟩ := deflateFixed_spec data
      exact ⟨bits, List.replicate ((8 - bits.length % 8) % 8) false,
        hbytes, by simp [List.length_replicate]; omega⟩
    · split
      · -- Levels 2-4: lazy LZ77 + fixed Huffman
        obtain ⟨bits, _, hbytes⟩ := deflateLazy_spec data
        exact ⟨bits, List.replicate ((8 - bits.length % 8) % 8) false,
          hbytes, by simp [List.length_replicate]; omega⟩
      · -- Levels 5+: dynamic Huffman
        obtain ⟨_, _, headerBits, symBits, _, _, _, _, _, _, _, _, _, _, hbytes⟩ :=
          deflateDynamic_spec data
        exact ⟨[true, false, true] ++ headerBits ++ symBits,
          List.replicate ((8 - ([true, false, true] ++ headerBits ++ symBits).length % 8) % 8) false,
          hbytes, by simp [List.length_replicate]; omega⟩

/-- For the encoder's output, `decode.goR` returns a short remaining (< 8 bits).
    This is the key fact connecting encoder structure to decoder bit consumption,
    needed by `inflateRaw_endPos_ge` to prove the decoder consumes all of `deflated`. -/
theorem deflateRaw_goR_pad (data : ByteArray) (level : UInt8)
    (hsize : data.size < 1024 * 1024 * 1024) :
    ∃ remaining,
      Deflate.Spec.decode.goR (Deflate.Spec.bytesToBits (deflateRaw data level)) []
        10000000000 = some (data.data.toList, remaining) ∧ remaining.length < 8 := by
  unfold deflateRaw
  split
  · -- Level 0: stored blocks — byte-aligned, remaining = []
    sorry
  · split
    · -- Level 1: fixed Huffman (iterative LZ77)
      rw [deflateFixedIter, lz77GreedyIter_eq_lz77Greedy, ← deflateFixed]
      obtain ⟨bits_enc, henc_fixed, hbytes⟩ := deflateFixed_spec data
      simp only [Deflate.Spec.encodeFixed] at henc_fixed
      cases henc_syms : Deflate.Spec.encodeSymbols Deflate.Spec.fixedLitLengths
          Deflate.Spec.fixedDistLengths
          (tokensToSymbols (lz77Greedy data)) with
      | none => simp [henc_syms] at henc_fixed
      | some allBits =>
        simp only [henc_syms, bind, Option.bind, pure, Pure.pure] at henc_fixed
        have hbits_eq : bits_enc = [true, true, false] ++ allBits :=
          (Option.some.inj henc_fixed).symm
        subst hbits_eq
        rw [hbytes]
        let padding := List.replicate
          ((8 - ([true, true, false] ++ allBits).length % 8) % 8) false
        refine ⟨padding, ?_, ?_⟩
        · exact Deflate.Spec.encodeFixed_goR_rest
            (tokensToSymbols (lz77Greedy data)) data.data.toList allBits padding
            henc_syms (lz77Greedy_resolves data 32768 (by omega))
            (by rw [tokensToSymbols_length]; have := lz77Greedy_size_le data 32768; omega)
            (tokensToSymbols_validSymbolList _)
        · simp [padding, List.length_replicate]; omega
    · split
      · -- Levels 2-4: lazy LZ77 + fixed Huffman
        obtain ⟨bits_enc, henc_fixed, hbytes⟩ := deflateLazy_spec data
        simp only [Deflate.Spec.encodeFixed] at henc_fixed
        cases henc_syms : Deflate.Spec.encodeSymbols Deflate.Spec.fixedLitLengths
            Deflate.Spec.fixedDistLengths
            (tokensToSymbols (lz77Lazy data)) with
        | none => simp [henc_syms] at henc_fixed
        | some allBits =>
          simp only [henc_syms, bind, Option.bind, pure, Pure.pure] at henc_fixed
          have hbits_eq : bits_enc = [true, true, false] ++ allBits :=
            (Option.some.inj henc_fixed).symm
          subst hbits_eq
          rw [hbytes]
          let padding := List.replicate
            ((8 - ([true, true, false] ++ allBits).length % 8) % 8) false
          refine ⟨padding, ?_, ?_⟩
          · exact Deflate.Spec.encodeFixed_goR_rest
              (tokensToSymbols (lz77Lazy data)) data.data.toList allBits padding
              henc_syms (lz77Lazy_resolves data 32768 (by omega))
              (by rw [tokensToSymbols_length]; have := lz77Lazy_size_le data 32768; omega)
              (tokensToSymbols_validSymbolList _)
          · simp [padding, List.length_replicate]; omega
      · -- Levels 5+: dynamic Huffman
        obtain ⟨litLens, distLens, headerBits, symBits, hv_lit, hv_dist,
            hlitLen_lo, hlitLen_hi, hdistLen_lo, hdistLen_hi,
            hlit_bound, hdist_bound,
            henc_trees, henc_syms, hbytes⟩ := deflateDynamic_spec data
        rw [hbytes]
        let padding := List.replicate
          ((8 - ([true, false, true] ++ headerBits ++ symBits).length % 8) % 8) false
        have hheader : Deflate.Spec.decodeDynamicTables
            (headerBits ++ symBits ++ padding) =
            some (litLens, distLens, symBits ++ padding) := by
          rw [List.append_assoc]
          exact Deflate.Spec.encodeDynamicTrees_decodeDynamicTables
            litLens distLens headerBits (symBits ++ padding)
            hlit_bound hdist_bound
            ⟨hlitLen_lo, hlitLen_hi⟩ ⟨hdistLen_lo, hdistLen_hi⟩
            hv_lit hv_dist henc_trees
        refine ⟨padding, ?_, ?_⟩
        · exact Deflate.Spec.encodeDynamic_goR_rest
            (tokensToSymbols (lz77Greedy data 32768)) data.data.toList
            litLens distLens headerBits symBits padding
            hv_lit hv_dist hheader henc_syms
            (lz77Greedy_resolves data 32768 (by omega))
            (by have := lz77Greedy_size_le data 32768; rw [tokensToSymbols_length]; omega)
            (tokensToSymbols_validSymbolList _)
        · simp [padding, List.length_replicate]; omega

end Zip.Native.Deflate
