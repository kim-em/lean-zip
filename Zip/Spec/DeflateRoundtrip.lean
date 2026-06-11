import Zip.Spec.DeflateFixedCorrect
import Zip.Spec.DeflateDynamicCorrect
import Zip.Spec.LZ77ChainCorrect
import Zip.Spec.DeflateBlockSplit

/-!
# Unified DEFLATE Roundtrip (Phase B4 Capstone)

Proves the unified roundtrip theorem for `deflateRaw`:
`inflate (deflateRaw data level) = .ok data`.

`deflateRaw` is defined in `Zip/Native/DeflateDynamic.lean`. Level 0 is a stored
block; level ≥ 1 runs the single-block cost-model dispatch `deflateRawBase`
(stored / fixed / dynamic, all sized from one hash-chain token pass, emitting
only the smallest); and level ≥ 7 additionally compares two block-split streams
(self-contained #2524 and cross-block shared-window #2525) against that base via
`pickSmaller`, so the split is a first-class candidate that can only ever win.

This composes:
- `inflate_deflateRawBase` — the stored / fixed / dynamic base, in turn built
  from `inflate_deflateStoredPure`, `inflate_deflateFixedBlock`,
  `inflate_deflateDynamicBlock`
- `inflate_deflateDynamicBlocksSC` / `inflate_deflateDynamicBlocksSharedAt` — the
  two block-split candidates (`Zip/Spec/DeflateBlockSplit.lean`); the shared-window
  candidate holds for any boundary selector, so the entropy-divergence partition
  (`chooseSplitsArbitrated`, #2528) needs no proof of its own
- `inflate_pickSmaller` — selecting the smaller of two roundtripping candidates
-/

namespace Zip.Native.Deflate

open Zip.Spec.DeflateStoredCorrect (inflate_deflateStoredPure)

/-- The level-dispatched token stream (`lzMatch`: greedy chain at levels 1–3, lazy
    chain at ≥ 4). The three contracts (`cEnc`/`cEmpty`/`cRes`) are what
    `inflate_deflateFixedBlock` / `inflate_deflateDynamicBlock` / their `_spec`s
    consume; each delegates to the `lzMatch_*` trio (which cases on the level). -/
private theorem cEnc (data : ByteArray) (level : UInt8) :
    ∀ t ∈ (lzMatch data level).toList,
      match t with
      | .literal _ => True
      | .reference len dist => 3 ≤ len ∧ len ≤ 258 ∧ 1 ≤ dist ∧ dist ≤ 32768 :=
  lzMatch_encodable data level

private theorem cEmpty (data : ByteArray) (level : UInt8) (hz : data.size = 0) :
    lzMatch data level = #[] :=
  lzMatch_empty data level hz

private theorem cRes (data : ByteArray) (level : UInt8) :
    Deflate.Spec.resolveLZ77 (tokensToSymbols (lzMatch data level)) [] =
      some data.data.toList :=
  lzMatch_resolves data level

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
  · exact inflate_deflateFixedBlock data (lzMatch data level)
      (cEnc data level) (fun hz => cEmpty data level hz) (cRes data level) _ (by omega)
  · exact inflate_deflateDynamicBlock data (lzMatch data level)
      (cEnc data level) (fun hz => cEmpty data level hz)
      (cRes data level) _ (by omega)

set_option maxRecDepth 8000 in
/-- Roundtrip for the single-block cost-model dispatch (`deflateRawBase`): the
    `deflateRaw` level-≥1 base without the block-split candidates.

    `maxRecDepth` is raised because `split`ting the selection forces the
    elaborator to whnf the nested size comparison. -/
theorem inflate_deflateRawBase (data : ByteArray) (level : UInt8)
    (maxOutputSize : Nat) (hsize : data.size ≤ maxOutputSize) :
    Zip.Native.Inflate.inflate (deflateRawBase data level) maxOutputSize = .ok data := by
  unfold deflateRawBase
  dsimp only []
  -- stored / fixed / dynamic, sized from one chain token pass. The outer `split`
  -- fires on `fixedBytes < dynBytes`, then each side on the stored comparison.
  split <;> split
  · exact inflate_deflateStoredPure data _ hsize
  · exact inflate_deflateFixedBlock data (lzMatch data level)
      (cEnc data level) (fun hz => cEmpty data level hz) (cRes data level) _ hsize
  · exact inflate_deflateStoredPure data _ hsize
  · exact inflate_deflateDynamicBlock data
      (lzMatch data level)
      (cEnc data level) (fun hz => cEmpty data level hz) (cRes data level) _ hsize

/-- Unified DEFLATE roundtrip: inflate ∘ deflateRaw = identity.
    This is the Phase B4 capstone theorem from PLAN.md. Generalized to any
    `maxOutputSize` large enough to hold the input. The stored-block fallback
    (for incompressible input) is covered by `deflateRawBase`; the level-≥7
    block-split candidates are covered by the `pickSmaller` cases. -/
theorem inflate_deflateRaw (data : ByteArray) (level : UInt8)
    (maxOutputSize : Nat) (hsize : data.size ≤ maxOutputSize) :
    Zip.Native.Inflate.inflate (deflateRaw data level) maxOutputSize = .ok data := by
  unfold deflateRaw
  split
  · exact inflate_deflateStoredPure data _ (by omega)
  · split
    · split
      · exact inflate_pickSmaller _ _ data maxOutputSize
          (inflate_pickSmaller _ _ data maxOutputSize
            (inflate_deflateRawBase data level _ hsize)
            (inflate_pickSmaller _ _ data maxOutputSize
              (inflate_deflateDynamicBlocksSC data splitChunkSize level _ hsize)
              (inflate_deflateDynamicBlocksSharedAt data chooseSplitsArbitrated level _ hsize)))
          (inflate_deflateDynamicBlocksOptimal data sharedTokChunk _ hsize)
      · exact inflate_pickSmaller _ _ data maxOutputSize
          (inflate_deflateRawBase data level _ hsize)
          (inflate_pickSmaller _ _ data maxOutputSize
            (inflate_deflateDynamicBlocksSC data splitChunkSize level _ hsize)
            (inflate_deflateDynamicBlocksSharedAt data chooseSplitsArbitrated level _ hsize))
    · exact inflate_deflateRawBase data level _ hsize

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
      (lzMatch data level) (cEnc data level) (fun hz => cEmpty data level hz)
    exact ⟨bits, List.replicate ((8 - bits.length % 8) % 8) false,
      hbytes, by simp only [List.length_replicate]; omega⟩
  · -- dynamic Huffman over the chain token stream
    obtain ⟨_, _, headerBits, symBits, _, _, _, _, _, _, _, _, _, _, hbytes⟩ :=
      deflateDynamicBlock_spec data (lzMatch data level)
        (cEnc data level) (fun hz => cEmpty data level hz)
    exact ⟨[true, false, true] ++ headerBits ++ symBits,
      List.replicate ((8 - ([true, false, true] ++ headerBits ++ symBits).length % 8) % 8) false,
      hbytes, by simp only [List.length_replicate]; omega⟩

set_option maxRecDepth 8000 in
/-- Padding decomposition for the single-block cost-model dispatch (`deflateRawBase`). -/
theorem deflateRawBase_pad (data : ByteArray) (level : UInt8) :
    ∃ (contentBits padding : List Bool),
      Deflate.Spec.bytesToBits (deflateRawBase data level) = contentBits ++ padding ∧
      padding.length < 8 := by
  unfold deflateRawBase
  dsimp only []
  -- stored / fixed / dynamic sized; emit only the winner. The outer `split` fires
  -- on `fixedBytes < dynBytes`, then each side on the stored comparison.
  have hstored : ∃ (contentBits padding : List Bool),
      Deflate.Spec.bytesToBits
          (Zip.Spec.DeflateStoredCorrect.deflateStoredPure data) = contentBits ++ padding ∧
        padding.length < 8 :=
    ⟨Deflate.Spec.bytesToBits (Zip.Spec.DeflateStoredCorrect.deflateStoredPure data),
      [], by simp only [List.append_nil], by decide⟩
  have hfixed : ∃ (contentBits padding : List Bool),
      Deflate.Spec.bytesToBits (deflateFixedBlock data (lzMatch data level)) =
        contentBits ++ padding ∧ padding.length < 8 := by
    obtain ⟨bits, _, hbytes⟩ := deflateFixedBlock_spec_of data
      (lzMatch data level) (cEnc data level) (fun hz => cEmpty data level hz)
    exact ⟨bits, List.replicate ((8 - bits.length % 8) % 8) false,
      hbytes, by simp only [List.length_replicate]; omega⟩
  have hdyn : ∃ (contentBits padding : List Bool),
      Deflate.Spec.bytesToBits (deflateDynamicBlock data (lzMatch data level)) =
        contentBits ++ padding ∧ padding.length < 8 := by
    obtain ⟨_, _, headerBits, symBits, _, _, _, _, _, _, _, _, _, _, hbytes⟩ :=
      deflateDynamicBlock_spec data (lzMatch data level)
        (cEnc data level) (fun hz => cEmpty data level hz)
    exact ⟨[true, false, true] ++ headerBits ++ symBits,
      List.replicate ((8 - ([true, false, true] ++ headerBits ++ symBits).length % 8) % 8) false,
      hbytes, by simp only [List.length_replicate]; omega⟩
  split <;> split
  · exact hstored
  · exact hfixed
  · exact hstored
  · exact hdyn

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
  · split
    · split
      · exact pickSmaller_bytesToBits
          (P := fun bits => ∃ (contentBits padding : List Bool),
            bits = contentBits ++ padding ∧ padding.length < 8)
          _ _
          (pickSmaller_bytesToBits
            (P := fun bits => ∃ (contentBits padding : List Bool),
              bits = contentBits ++ padding ∧ padding.length < 8)
            _ _ (deflateRawBase_pad data level)
            (pickSmaller_bytesToBits
              (P := fun bits => ∃ (contentBits padding : List Bool),
                bits = contentBits ++ padding ∧ padding.length < 8)
              _ _ (deflateDynamicBlocksSC_pad data splitChunkSize level)
              (deflateDynamicBlocksSharedAt_pad data chooseSplitsArbitrated level)))
          (deflateDynamicBlocksOptimal_pad data sharedTokChunk)
      · exact pickSmaller_bytesToBits
          (P := fun bits => ∃ (contentBits padding : List Bool),
            bits = contentBits ++ padding ∧ padding.length < 8)
          _ _ (deflateRawBase_pad data level)
          (pickSmaller_bytesToBits
            (P := fun bits => ∃ (contentBits padding : List Bool),
              bits = contentBits ++ padding ∧ padding.length < 8)
            _ _ (deflateDynamicBlocksSC_pad data splitChunkSize level)
            (deflateDynamicBlocksSharedAt_pad data chooseSplitsArbitrated level))
    · exact deflateRawBase_pad data level

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
    exact deflateFixedBlock_goR_pad data (lzMatch data level)
      (cEnc data level) (fun hz => cEmpty data level hz) (cRes data level)
  · -- dynamic Huffman over the chain token stream
    exact deflateDynamicBlock_goR_pad data (lzMatch data level)
      (cEnc data level) (fun hz => cEmpty data level hz) (cRes data level)

set_option maxRecDepth 8000 in
/-- `goR` short-remaining for the single-block cost-model dispatch (`deflateRawBase`). -/
private theorem deflateRawBase_goR_pad (data : ByteArray) (level : UInt8) :
    ∃ remaining,
      Deflate.Spec.decode.goR (Deflate.Spec.bytesToBits (deflateRawBase data level)) []
        = some (data.data.toList, remaining) ∧ remaining.length < 8 := by
  unfold deflateRawBase
  dsimp only []
  have hfixed : ∃ remaining,
      Deflate.Spec.decode.goR
          (Deflate.Spec.bytesToBits (deflateFixedBlock data (lzMatch data level))) []
        = some (data.data.toList, remaining) ∧ remaining.length < 8 :=
    deflateFixedBlock_goR_pad data (lzMatch data level)
      (cEnc data level) (fun hz => cEmpty data level hz) (cRes data level)
  split <;> split
  · exact ⟨[], Deflate.Spec.deflateStoredPure_goR data, by decide⟩
  · exact hfixed
  · exact ⟨[], Deflate.Spec.deflateStoredPure_goR data, by decide⟩
  · exact deflateDynamicBlock_goR_pad data
      (lzMatch data level)
      (cEnc data level) (fun hz => cEmpty data level hz) (cRes data level)

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
  · split
    · split
      · exact pickSmaller_bytesToBits
          (P := fun bits => ∃ remaining,
            Deflate.Spec.decode.goR bits [] = some (data.data.toList, remaining) ∧
              remaining.length < 8)
          _ _
          (pickSmaller_bytesToBits
            (P := fun bits => ∃ remaining,
              Deflate.Spec.decode.goR bits [] = some (data.data.toList, remaining) ∧
                remaining.length < 8)
            _ _ (deflateRawBase_goR_pad data level)
            (pickSmaller_bytesToBits
              (P := fun bits => ∃ remaining,
                Deflate.Spec.decode.goR bits [] = some (data.data.toList, remaining) ∧
                  remaining.length < 8)
              _ _ (deflateDynamicBlocksSC_goR_pad data splitChunkSize level)
              (deflateDynamicBlocksSharedAt_goR_pad data chooseSplitsArbitrated level)))
          (deflateDynamicBlocksOptimal_goR_pad data sharedTokChunk)
      · exact pickSmaller_bytesToBits
          (P := fun bits => ∃ remaining,
            Deflate.Spec.decode.goR bits [] = some (data.data.toList, remaining) ∧
              remaining.length < 8)
          _ _ (deflateRawBase_goR_pad data level)
          (pickSmaller_bytesToBits
            (P := fun bits => ∃ remaining,
              Deflate.Spec.decode.goR bits [] = some (data.data.toList, remaining) ∧
                remaining.length < 8)
            _ _ (deflateDynamicBlocksSC_goR_pad data splitChunkSize level)
            (deflateDynamicBlocksSharedAt_goR_pad data chooseSplitsArbitrated level))
    · exact deflateRawBase_goR_pad data level

end Zip.Native.Deflate
