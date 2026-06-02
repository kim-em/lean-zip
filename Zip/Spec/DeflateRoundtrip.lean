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
- `inflate_deflateLazyIter` (Levels 2-4)
- `inflate_deflateDynamic` (Levels 5+)
-/

namespace Zip.Native.Deflate

open Zip.Spec.DeflateStoredCorrect (inflate_deflateStoredPure)

/-- Per-token encodability bound for the iterative lazy matcher — the hypothesis
    `deflateDynamicBlock_spec` / `inflate_deflateDynamicBlock` need at level ≥ 5. -/
private theorem lz77LazyIter_encodable (data : ByteArray) :
    ∀ t ∈ (lz77LazyIter data).toList,
      match t with
      | .literal _ => True
      | .reference len dist => 3 ≤ len ∧ len ≤ 258 ∧ 1 ≤ dist ∧ dist ≤ 32768 :=
  fun t ht => lz77Lazy_encodable data 32768 (by omega) (by omega) t
    (by rwa [lz77LazyIter_eq_lz77Lazy] at ht)

/-- The iterative lazy matcher emits no tokens on empty input. -/
private theorem lz77LazyIter_empty (data : ByteArray) (hzero : data.size = 0) :
    lz77LazyIter data = #[] := by
  rw [lz77LazyIter_eq_lz77Lazy]
  simp only [lz77Lazy, show data.size < 3 from by omega, ↓reduceIte]
  have htrail : lz77Lazy.trailing data 0 = [] := by
    unfold lz77Lazy.trailing
    simp only [show ¬(0 < data.size) from by omega, ↓reduceDIte]
  simp only [htrail]

/-- The iterative lazy matcher's tokens resolve back to the original data. -/
private theorem lz77LazyIter_resolves (data : ByteArray) :
    Deflate.Spec.resolveLZ77 (tokensToSymbols (lz77LazyIter data)) [] =
      some data.data.toList := by
  rw [lz77LazyIter_eq_lz77Lazy]; exact lz77Lazy_resolves data 32768 (by omega)

/-- Roundtrip for the compressed-block dispatch (`deflateCompressed`), i.e. the
    `deflateRaw` cases without the stored-block fallback. -/
theorem inflate_deflateCompressed (data : ByteArray) (level : UInt8)
    (maxOutputSize : Nat) (hsize : data.size ≤ maxOutputSize) :
    Zip.Native.Inflate.inflate (deflateCompressed data level) maxOutputSize = .ok data := by
  unfold deflateCompressed
  split
  · exact inflate_deflateFixedIter data _ (by omega)
  · split
    · exact inflate_deflateLazyIter data _ hsize
    · -- Levels 5+: one lazy token pass sizes both candidates; emit only the winner.
      dsimp only []
      split
      · exact inflate_deflateLazyIter data _ (by omega)
      · exact inflate_deflateDynamicBlock data (lz77LazyIter data)
          (lz77LazyIter_encodable data) (fun hz => lz77LazyIter_empty data hz)
          (lz77LazyIter_resolves data) _ (by omega)

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
  · split
    · -- Levels 1-4: stored fallback vs. one compressed block.
      unfold pickSmaller
      split
      · exact inflate_deflateStoredPure data _ (by omega)
      · exact inflate_deflateCompressed data level maxOutputSize hsize
    · -- Levels 5+: stored / fixed / dynamic all sized; emit only the winner.
      -- The outer `split` fires on `fixedBytes < dynBytes`, then each side on the
      -- stored-vs-compressed comparison.
      dsimp only []
      split <;> split
      · exact inflate_deflateStoredPure data _ hsize
      · exact inflate_deflateLazyIter data _ hsize
      · exact inflate_deflateStoredPure data _ hsize
      · exact inflate_deflateDynamicBlock data (lz77LazyIter data)
          (lz77LazyIter_encodable data) (fun hz => lz77LazyIter_empty data hz)
          (lz77LazyIter_resolves data) _ hsize

/-- Padding decomposition for the compressed-block dispatch. -/
theorem deflateCompressed_pad (data : ByteArray) (level : UInt8) :
    ∃ (contentBits padding : List Bool),
      Deflate.Spec.bytesToBits (deflateCompressed data level) = contentBits ++ padding ∧
      padding.length < 8 := by
  unfold deflateCompressed
  split
  · -- Level 1: fixed Huffman (iterative LZ77)
    rw [deflateFixedIter, lz77GreedyIter_eq_lz77Greedy]
    obtain ⟨bits, _, hbytes⟩ := deflateFixed_spec data
    exact ⟨bits, List.replicate ((8 - bits.length % 8) % 8) false,
      hbytes, by simp only [List.length_replicate]; omega⟩
  · split
    · -- Levels 2-4: lazy LZ77 + fixed Huffman (iterative)
      rw [deflateLazyIter_eq_deflateLazy]
      obtain ⟨bits, _, hbytes⟩ := deflateLazy_spec data
      exact ⟨bits, List.replicate ((8 - bits.length % 8) % 8) false,
        hbytes, by simp only [List.length_replicate]; omega⟩
    · -- Levels 5+: smaller of fixed / dynamic Huffman over a shared lazy token stream.
      dsimp only []
      split
      · -- fixed Huffman over lazy tokens (= deflateLazyIter)
        rw [show deflateFixedBlock data (lz77LazyIter data) = deflateLazy data
          from deflateLazyIter_eq_deflateLazy data]
        obtain ⟨bits, _, hbytes⟩ := deflateLazy_spec data
        exact ⟨bits, List.replicate ((8 - bits.length % 8) % 8) false,
          hbytes, by simp only [List.length_replicate]; omega⟩
      · -- dynamic Huffman over lazy tokens
        obtain ⟨_, _, headerBits, symBits, _, _, _, _, _, _, _, _, _, _, hbytes⟩ :=
          deflateDynamicBlock_spec data (lz77LazyIter data)
            (lz77LazyIter_encodable data) (fun hz => lz77LazyIter_empty data hz)
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
  · split
    · -- Levels 1-4: stored fallback vs. one compressed block.
      unfold pickSmaller
      split
      · -- stored-block fallback chosen — byte-aligned, padding = []
        exact ⟨Deflate.Spec.bytesToBits (Zip.Spec.DeflateStoredCorrect.deflateStoredPure data),
          [], by simp only [List.append_nil], by decide⟩
      · exact deflateCompressed_pad data level
    · -- Levels 5+: stored / fixed / dynamic sized; emit only the winner.
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
          Deflate.Spec.bytesToBits (deflateFixedBlock data (lz77LazyIter data)) =
            contentBits ++ padding ∧ padding.length < 8 := by
        rw [show deflateFixedBlock data (lz77LazyIter data) = deflateLazy data
          from deflateLazyIter_eq_deflateLazy data]
        obtain ⟨bits, _, hbytes⟩ := deflateLazy_spec data
        exact ⟨bits, List.replicate ((8 - bits.length % 8) % 8) false,
          hbytes, by simp only [List.length_replicate]; omega⟩
      have hdyn : ∃ (contentBits padding : List Bool),
          Deflate.Spec.bytesToBits (deflateDynamicBlock data (lz77LazyIter data)) =
            contentBits ++ padding ∧ padding.length < 8 := by
        obtain ⟨_, _, headerBits, symBits, _, _, _, _, _, _, _, _, _, _, hbytes⟩ :=
          deflateDynamicBlock_spec data (lz77LazyIter data)
            (lz77LazyIter_encodable data) (fun hz => lz77LazyIter_empty data hz)
        exact ⟨[true, false, true] ++ headerBits ++ symBits,
          List.replicate ((8 - ([true, false, true] ++ headerBits ++ symBits).length % 8) % 8) false,
          hbytes, by simp only [List.length_replicate]; omega⟩
      split <;> split
      · exact hstored
      · exact hfixed
      · exact hstored
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

/-- `goR` short-remaining for a dynamic-Huffman block over the lazy token stream
    (the level ≥ 5 dynamic candidate). -/
private theorem deflateDynamicBlock_lazy_goR_pad (data : ByteArray) :
    ∃ remaining,
      Deflate.Spec.decode.goR
        (Deflate.Spec.bytesToBits (deflateDynamicBlock data (lz77LazyIter data))) []
        = some (data.data.toList, remaining) ∧ remaining.length < 8 := by
  obtain ⟨litLens, distLens, headerBits, symBits, hv_lit, hv_dist,
      hlitLen_lo, hlitLen_hi, hdistLen_lo, hdistLen_hi,
      hlit_bound, hdist_bound,
      henc_trees, henc_syms, hbytes⟩ := deflateDynamicBlock_spec data (lz77LazyIter data)
        (lz77LazyIter_encodable data) (fun hz => lz77LazyIter_empty data hz)
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
      (tokensToSymbols (lz77LazyIter data)) data.data.toList
      litLens distLens headerBits symBits padding
      hv_lit hv_dist hheader henc_syms
      (lz77LazyIter_resolves data)
      (tokensToSymbols_validSymbolList _)
  · simp only [padding, List.length_replicate]; omega

/-- `goR` short-remaining for the compressed-block dispatch. -/
theorem deflateCompressed_goR_pad (data : ByteArray) (level : UInt8) :
    ∃ remaining,
      Deflate.Spec.decode.goR (Deflate.Spec.bytesToBits (deflateCompressed data level)) []
        = some (data.data.toList, remaining) ∧ remaining.length < 8 := by
  unfold deflateCompressed
  split
  · -- Level 1: fixed Huffman (iterative LZ77)
    rw [deflateFixedIter, lz77GreedyIter_eq_lz77Greedy, ← deflateFixed]
    obtain ⟨bits_enc, henc_fixed, hbytes⟩ := deflateFixed_spec data
    simp only [Deflate.Spec.encodeFixed] at henc_fixed
    cases henc_syms : Deflate.Spec.encodeSymbols Deflate.Spec.fixedLitLengths
        Deflate.Spec.fixedDistLengths
        (tokensToSymbols (lz77Greedy data)) with
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
          (tokensToSymbols (lz77Greedy data)) data.data.toList allBits padding
          henc_syms (lz77Greedy_resolves data 32768 (by omega))
          (tokensToSymbols_validSymbolList _)
      · simp only [padding, List.length_replicate]; omega
  · split
    · -- Levels 2-4: lazy LZ77 + fixed Huffman (iterative)
      rw [deflateLazyIter_eq_deflateLazy]
      exact deflateLazy_goR_pad data
    · -- Levels 5+: smaller of fixed / dynamic Huffman over a shared lazy token stream.
      dsimp only []
      split
      · -- fixed Huffman over lazy tokens (= deflateLazyIter)
        rw [show deflateFixedBlock data (lz77LazyIter data) = deflateLazy data
          from deflateLazyIter_eq_deflateLazy data]
        exact deflateLazy_goR_pad data
      · -- dynamic Huffman over lazy tokens
        exact deflateDynamicBlock_lazy_goR_pad data

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
  · split
    · -- Levels 1-4: stored fallback vs. one compressed block.
      unfold pickSmaller
      split
      · -- stored-block fallback chosen — byte-aligned, remaining = []
        exact ⟨[], Deflate.Spec.deflateStoredPure_goR data, by decide⟩
      · exact deflateCompressed_goR_pad data level
    · -- Levels 5+: stored / fixed / dynamic sized; emit only the winner.
      -- The outer `split` fires on `fixedBytes < dynBytes`, then each side on the
      -- stored-vs-compressed comparison (stored appears in both).
      dsimp only []
      have hfixed : ∃ remaining,
          Deflate.Spec.decode.goR
              (Deflate.Spec.bytesToBits (deflateFixedBlock data (lz77LazyIter data))) []
            = some (data.data.toList, remaining) ∧ remaining.length < 8 := by
        rw [show deflateFixedBlock data (lz77LazyIter data) = deflateLazy data
          from deflateLazyIter_eq_deflateLazy data]
        exact deflateLazy_goR_pad data
      split <;> split
      · exact ⟨[], Deflate.Spec.deflateStoredPure_goR data, by decide⟩
      · exact hfixed
      · exact ⟨[], Deflate.Spec.deflateStoredPure_goR data, by decide⟩
      · exact deflateDynamicBlock_lazy_goR_pad data

end Zip.Native.Deflate
