import Zip.Spec.DeflateFixedCorrect
import Zip.Spec.DeflateDynamicCorrect
import Zip.Spec.LZ77ChainCorrect
import Zip.Spec.DeflateBlockSplit

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
- `inflate_deflateLazyIter` (Levels 2-4)
- `inflate_deflateDynamic` (Levels 5+)
-/

namespace Zip.Native.Deflate

open Zip.Spec.DeflateStoredCorrect (inflate_deflateStoredPure)

/-- The level-≥5 token stream: the hash-chain matcher at the level's search depth.
    The three contracts (`cEnc`/`cEmpty`/`cRes`) are what `inflate_deflateFixedBlock`
    / `inflate_deflateDynamicBlock` / their `_spec`s consume. -/
private theorem cEnc (data : ByteArray) (level : UInt8) :
    ∀ t ∈ (lz77ChainIter data (chainDepth level) 32768 (insertCap level)).toList,
      match t with
      | .literal _ => True
      | .reference len dist => 3 ≤ len ∧ len ≤ 258 ∧ 1 ≤ dist ∧ dist ≤ 32768 :=
  lz77ChainIter_encodable data (chainDepth level) 32768 (insertCap level) (by omega) (by omega)

private theorem cEmpty (data : ByteArray) (level : UInt8) (hz : data.size = 0) :
    lz77ChainIter data (chainDepth level) 32768 (insertCap level) = #[] :=
  lz77ChainIter_empty data (chainDepth level) 32768 (insertCap level) hz

private theorem cRes (data : ByteArray) (level : UInt8) :
    Deflate.Spec.resolveLZ77 (tokensToSymbols (lz77ChainIter data (chainDepth level) 32768 (insertCap level))) [] =
      some data.data.toList :=
  lz77ChainIter_resolves data (chainDepth level) 32768 (insertCap level) (by omega)

set_option maxRecDepth 8000 in
/-- `pickSmaller` of two byte arrays that both roundtrip also roundtrips. -/
theorem inflate_pickSmaller (a b dataOut : ByteArray) (m : Nat)
    (ha : Zip.Native.Inflate.inflate a m = .ok dataOut)
    (hb : Zip.Native.Inflate.inflate b m = .ok dataOut) :
    Zip.Native.Inflate.inflate (pickSmaller a b) m = .ok dataOut := by
  unfold pickSmaller; split <;> assumption

/-- `pickSmaller` preserves any predicate on the bit stream both candidates meet. -/
theorem pickSmaller_bytesToBits {P : List Bool → Prop} (a b : ByteArray)
    (ha : P (Deflate.Spec.bytesToBits a)) (hb : P (Deflate.Spec.bytesToBits b)) :
    P (Deflate.Spec.bytesToBits (pickSmaller a b)) := by
  unfold pickSmaller; split <;> assumption

/-- Roundtrip for the compressed-block dispatch (`deflateCompressed`), i.e. the
    `deflateRaw` cases without the stored-block fallback. -/
theorem inflate_deflateCompressed (data : ByteArray) (level : UInt8)
    (maxOutputSize : Nat) (hsize : data.size ≤ maxOutputSize) :
    Zip.Native.Inflate.inflate (deflateCompressed data level) maxOutputSize = .ok data := by
  unfold deflateCompressed
  dsimp only []
  split
  · exact inflate_deflateFixedBlock data (lz77ChainIter data (chainDepth level) 32768 (insertCap level))
      (cEnc data level) (fun hz => cEmpty data level hz) (cRes data level) _ (by omega)
  · exact inflate_deflateDynamicBlock data (lz77ChainIter data (chainDepth level) 32768 (insertCap level))
      (cEnc data level) (fun hz => cEmpty data level hz)
      (cRes data level) _ (by omega)

set_option maxRecDepth 8000 in
/-- Unified DEFLATE roundtrip: inflate ∘ deflateRaw = identity.
    This is the Phase B4 capstone theorem from PLAN.md. Generalized to any
    `maxOutputSize` large enough to hold the input. The stored-block fallback
    (for incompressible input) is covered by the `pickSmaller` case.

    `maxRecDepth` is raised because `split`ting the level-≥5 selection forces the
    elaborator to whnf the nested size comparison. -/
theorem inflate_deflateRaw (data : ByteArray) (level : UInt8)
    (maxOutputSize : Nat) (hsize : data.size ≤ maxOutputSize) :
    Zip.Native.Inflate.inflate (deflateRaw data level) maxOutputSize = .ok data := by
  unfold deflateRaw
  split
  · exact inflate_deflateStoredPure data _ (by omega)
  · -- Levels ≥ 1: stored / fixed / dynamic all sized from one chain token pass.
    -- The outer `split` fires on `fixedBytes < dynBytes`, then each side on the
    -- stored-vs-compressed comparison.
    dsimp only []
    split <;> split
    · exact inflate_deflateStoredPure data _ hsize
    · exact inflate_deflateFixedBlock data (lz77ChainIter data (chainDepth level) 32768 (insertCap level))
        (cEnc data level) (fun hz => cEmpty data level hz) (cRes data level) _ hsize
    · exact inflate_deflateStoredPure data _ hsize
    · -- Dynamic: `if 7 ≤ level then pickSmaller single split else single`.
      have hsingle := inflate_deflateDynamicBlock data
        (lz77ChainIter data (chainDepth level) 32768 (insertCap level))
        (cEnc data level) (fun hz => cEmpty data level hz) (cRes data level) _ hsize
      split
      · exact inflate_pickSmaller _ _ data maxOutputSize
          (inflate_pickSmaller _ _ data maxOutputSize hsingle
            (inflate_deflateDynamicBlocksSC data splitChunkSize level _ hsize))
          (inflate_deflateDynamicBlocksShared data sharedTokChunk level _ hsize)
      · exact hsingle

/-- Padding decomposition for the compressed-block dispatch. -/
theorem deflateCompressed_pad (data : ByteArray) (level : UInt8) :
    ∃ (contentBits padding : List Bool),
      Deflate.Spec.bytesToBits (deflateCompressed data level) = contentBits ++ padding ∧
      padding.length < 8 := by
  unfold deflateCompressed
  dsimp only []
  split
  · -- fixed Huffman over the chain token stream
    obtain ⟨bits, _, hbytes⟩ := deflateFixedBlock_spec_of data
      (lz77ChainIter data (chainDepth level) 32768 (insertCap level)) (cEnc data level) (fun hz => cEmpty data level hz)
    exact ⟨bits, List.replicate ((8 - bits.length % 8) % 8) false,
      hbytes, by simp only [List.length_replicate]; omega⟩
  · -- dynamic Huffman over the chain token stream
    obtain ⟨_, _, headerBits, symBits, _, _, _, _, _, _, _, _, _, _, hbytes⟩ :=
      deflateDynamicBlock_spec data (lz77ChainIter data (chainDepth level) 32768 (insertCap level))
        (cEnc data level) (fun hz => cEmpty data level hz)
    exact ⟨[true, false, true] ++ headerBits ++ symBits,
      List.replicate ((8 - ([true, false, true] ++ headerBits ++ symBits).length % 8) % 8) false,
      hbytes, by simp only [List.length_replicate]; omega⟩

set_option maxRecDepth 8000 in
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
      [], by simp only [List.append_nil], by decide⟩
  · -- Levels ≥ 1: stored / fixed / dynamic sized; emit only the winner.
    -- The outer `split` fires on `fixedBytes < dynBytes`, then each side on the
    -- stored-vs-compressed comparison (stored appears in both).
    dsimp only []
    have hstored : ∃ (contentBits padding : List Bool),
        Deflate.Spec.bytesToBits
            (Zip.Spec.DeflateStoredCorrect.deflateStoredPure data) = contentBits ++ padding ∧
          padding.length < 8 :=
      ⟨Deflate.Spec.bytesToBits (Zip.Spec.DeflateStoredCorrect.deflateStoredPure data),
        [], by simp only [List.append_nil], by decide⟩
    have hfixed : ∃ (contentBits padding : List Bool),
        Deflate.Spec.bytesToBits (deflateFixedBlock data (lz77ChainIter data (chainDepth level) 32768 (insertCap level))) =
          contentBits ++ padding ∧ padding.length < 8 := by
      obtain ⟨bits, _, hbytes⟩ := deflateFixedBlock_spec_of data
        (lz77ChainIter data (chainDepth level) 32768 (insertCap level)) (cEnc data level) (fun hz => cEmpty data level hz)
      exact ⟨bits, List.replicate ((8 - bits.length % 8) % 8) false,
        hbytes, by simp only [List.length_replicate]; omega⟩
    have hdyn : ∃ (contentBits padding : List Bool),
        Deflate.Spec.bytesToBits (deflateDynamicBlock data (lz77ChainIter data (chainDepth level) 32768 (insertCap level))) =
          contentBits ++ padding ∧ padding.length < 8 := by
      obtain ⟨_, _, headerBits, symBits, _, _, _, _, _, _, _, _, _, _, hbytes⟩ :=
        deflateDynamicBlock_spec data (lz77ChainIter data (chainDepth level) 32768 (insertCap level))
          (cEnc data level) (fun hz => cEmpty data level hz)
      exact ⟨[true, false, true] ++ headerBits ++ symBits,
        List.replicate ((8 - ([true, false, true] ++ headerBits ++ symBits).length % 8) % 8) false,
        hbytes, by simp only [List.length_replicate]; omega⟩
    split <;> split
    · exact hstored
    · exact hfixed
    · exact hstored
    · split
      · exact pickSmaller_bytesToBits
          (P := fun bits => ∃ (contentBits padding : List Bool),
            bits = contentBits ++ padding ∧ padding.length < 8)
          _ _
          (pickSmaller_bytesToBits
            (P := fun bits => ∃ (contentBits padding : List Bool),
              bits = contentBits ++ padding ∧ padding.length < 8)
            _ _ hdyn (deflateDynamicBlocksSC_pad data splitChunkSize level))
          (deflateDynamicBlocksShared_pad data sharedTokChunk level)
      · exact hdyn

/-- `goR` short-remaining for a fixed-Huffman block over the lazy token stream —
    the level 2-4 path and the level ≥ 5 fixed candidate (both `= deflateLazy`). -/
private theorem deflateLazy_goR_pad (data : ByteArray) :
    ∃ remaining,
      Deflate.Spec.decode.goR (Deflate.Spec.bytesToBits (deflateLazy data)) []
        = some (data.data.toList, remaining) ∧ remaining.length < 8 := by
  obtain ⟨bits_enc, henc_fixed, hbytes⟩ := deflateLazy_spec data
  simp only [Deflate.Spec.encodeFixed] at henc_fixed
  cases henc_syms : Deflate.Spec.encodeSymbols Deflate.Spec.fixedLitLengths
      Deflate.Spec.fixedDistLengths
      (tokensToSymbols (lz77Lazy data)) with
  | none => exact nomatch (henc_syms ▸ henc_fixed)
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
        (tokensToSymbols_validSymbolList _)
    · simp only [padding, List.length_replicate]; omega

/-- `goR` short-remaining for a fixed-Huffman block over *any* valid token stream
    (the level ≥ 5 fixed candidate). -/
private theorem deflateFixedBlock_goR_pad (data : ByteArray) (tokens : Array LZ77Token)
    (henc : ∀ t ∈ tokens.toList,
      match t with
      | .literal _ => True
      | .reference len dist => 3 ≤ len ∧ len ≤ 258 ∧ 1 ≤ dist ∧ dist ≤ 32768)
    (hempty : data.size = 0 → tokens = #[])
    (hresolve : Deflate.Spec.resolveLZ77 (tokensToSymbols tokens) [] = some data.data.toList) :
    ∃ remaining,
      Deflate.Spec.decode.goR (Deflate.Spec.bytesToBits (deflateFixedBlock data tokens)) []
        = some (data.data.toList, remaining) ∧ remaining.length < 8 := by
  obtain ⟨bits_enc, henc_fixed, hbytes⟩ := deflateFixedBlock_spec_of data tokens henc hempty
  simp only [Deflate.Spec.encodeFixed] at henc_fixed
  cases henc_syms : Deflate.Spec.encodeSymbols Deflate.Spec.fixedLitLengths
      Deflate.Spec.fixedDistLengths (tokensToSymbols tokens) with
  | none => exact nomatch (henc_syms ▸ henc_fixed)
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
        (tokensToSymbols tokens) data.data.toList allBits padding
        henc_syms hresolve (tokensToSymbols_validSymbolList _)
    · simp only [padding, List.length_replicate]; omega

/-- `goR` short-remaining for a dynamic-Huffman block over *any* valid token
    stream (the level ≥ 5 dynamic candidate). -/
private theorem deflateDynamicBlock_goR_pad (data : ByteArray) (tokens : Array LZ77Token)
    (henc : ∀ t ∈ tokens.toList,
      match t with
      | .literal _ => True
      | .reference len dist => 3 ≤ len ∧ len ≤ 258 ∧ 1 ≤ dist ∧ dist ≤ 32768)
    (hempty : data.size = 0 → tokens = #[])
    (hresolve : Deflate.Spec.resolveLZ77 (tokensToSymbols tokens) [] = some data.data.toList) :
    ∃ remaining,
      Deflate.Spec.decode.goR (Deflate.Spec.bytesToBits (deflateDynamicBlock data tokens)) []
        = some (data.data.toList, remaining) ∧ remaining.length < 8 := by
  obtain ⟨litLens, distLens, headerBits, symBits, hv_lit, hv_dist,
      hlitLen_lo, hlitLen_hi, hdistLen_lo, hdistLen_hi,
      hlit_bound, hdist_bound,
      henc_trees, henc_syms, hbytes⟩ := deflateDynamicBlock_spec data tokens henc hempty
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
      (tokensToSymbols tokens) data.data.toList
      litLens distLens headerBits symBits padding
      hv_lit hv_dist hheader henc_syms hresolve
      (tokensToSymbols_validSymbolList _)
  · simp only [padding, List.length_replicate]; omega

/-- `goR` short-remaining for the compressed-block dispatch. -/
theorem deflateCompressed_goR_pad (data : ByteArray) (level : UInt8) :
    ∃ remaining,
      Deflate.Spec.decode.goR (Deflate.Spec.bytesToBits (deflateCompressed data level)) []
        = some (data.data.toList, remaining) ∧ remaining.length < 8 := by
  unfold deflateCompressed
  dsimp only []
  split
  · -- fixed Huffman over the chain token stream
    exact deflateFixedBlock_goR_pad data (lz77ChainIter data (chainDepth level) 32768 (insertCap level))
      (cEnc data level) (fun hz => cEmpty data level hz) (cRes data level)
  · -- dynamic Huffman over the chain token stream
    exact deflateDynamicBlock_goR_pad data (lz77ChainIter data (chainDepth level) 32768 (insertCap level))
      (cEnc data level) (fun hz => cEmpty data level hz) (cRes data level)

set_option maxRecDepth 8000 in
/-- For the encoder's output, `decode.goR` returns a short remaining (< 8 bits).
    This is the key fact connecting encoder structure to decoder bit consumption,
    needed by `inflateRaw_endPos_ge` to prove the decoder consumes all of `deflated`. -/
theorem deflateRaw_goR_pad (data : ByteArray) (level : UInt8) :
    ∃ remaining,
      Deflate.Spec.decode.goR (Deflate.Spec.bytesToBits (deflateRaw data level)) []
        = some (data.data.toList, remaining) ∧ remaining.length < 8 := by
  unfold deflateRaw
  split
  · -- Level 0: stored blocks — byte-aligned, remaining = []
    exact ⟨[], Deflate.Spec.deflateStoredPure_goR data, by decide⟩
  · -- Levels ≥ 1: stored / fixed / dynamic sized; emit only the winner.
    dsimp only []
    have hfixed : ∃ remaining,
        Deflate.Spec.decode.goR
            (Deflate.Spec.bytesToBits (deflateFixedBlock data (lz77ChainIter data (chainDepth level) 32768 (insertCap level)))) []
          = some (data.data.toList, remaining) ∧ remaining.length < 8 := by
      exact deflateFixedBlock_goR_pad data (lz77ChainIter data (chainDepth level) 32768 (insertCap level))
        (cEnc data level) (fun hz => cEmpty data level hz) (cRes data level)
    split <;> split
    · exact ⟨[], Deflate.Spec.deflateStoredPure_goR data, by decide⟩
    · exact hfixed
    · exact ⟨[], Deflate.Spec.deflateStoredPure_goR data, by decide⟩
    · have hsingle := deflateDynamicBlock_goR_pad data
        (lz77ChainIter data (chainDepth level) 32768 (insertCap level))
        (cEnc data level) (fun hz => cEmpty data level hz) (cRes data level)
      split
      · exact pickSmaller_bytesToBits
          (P := fun bits => ∃ remaining,
            Deflate.Spec.decode.goR bits [] = some (data.data.toList, remaining) ∧
              remaining.length < 8)
          _ _
          (pickSmaller_bytesToBits
            (P := fun bits => ∃ remaining,
              Deflate.Spec.decode.goR bits [] = some (data.data.toList, remaining) ∧
                remaining.length < 8)
            _ _ hsingle (deflateDynamicBlocksSC_goR_pad data splitChunkSize level))
          (deflateDynamicBlocksShared_goR_pad data sharedTokChunk level)
      · exact hsingle

end Zip.Native.Deflate
