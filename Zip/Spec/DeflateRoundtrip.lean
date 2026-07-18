import Zip.Spec.DeflateFixedCorrect
import Zip.Spec.DeflateDynamicCorrect
import Zip.Spec.LZ77ChainCorrect
import Zip.Spec.LZ77PackedCorrect
import Zip.Spec.DeflateBaseFreqsReuse
import Zip.Spec.DeflateBlockSplit

/-!
# Unified DEFLATE Roundtrip (Phase B4 Capstone)

Proves the unified roundtrip theorem for `deflateRaw`:
`inflate (deflateRaw data level) = .ok data`.

`deflateRaw` is defined in `Zip/Native/DeflateDynamic.lean`. Level 0 is a stored
block; level ≥ 1 runs the single-block cost-model dispatch `deflateRawBase`
(stored / fixed / dynamic, all sized from one hash-chain token pass, emitting
only the smallest); levels 5–8 additionally compare the cross-block
shared-window split at the observation-divergence boundaries (#2737) against
that base via `pickSmaller`, so the split is a first-class candidate that can
only ever win; and levels 9/10 compare the near-optimal / exact-DP candidates
instead.

This composes:
- `inflate_deflateRawBase` — the stored / fixed / dynamic base, in turn built
  from `inflate_deflateStoredPure`, `inflate_deflateFixedBlock`,
  `inflate_deflateDynamicBlock`
- `inflate_deflateDynamicBlocksSharedAt` — the shared-window block-split
  candidate (`Zip/Spec/DeflateBlockSplit.lean`); it holds for **any** boundary
  selector, so the observation-divergence partition (`chooseSplitsHeuristicP`,
  #2737) needs no proof of its own — the packed emit pipeline transfers via
  `deflateDynamicBlocksSharedAtP_eq` (`Zip/Spec/LZ77PackedCorrect.lean`)
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
    (ha : Zip.Native.Inflate.inflateReference a m = .ok dataOut)
    (hb : Zip.Native.Inflate.inflateReference b m = .ok dataOut) :
    Zip.Native.Inflate.inflateReference (pickSmaller a b) m = .ok dataOut := by
  unfold pickSmaller; split <;> assumption

/-- `pickSmaller` preserves any predicate on the bit stream both candidates meet. -/
theorem pickSmaller_bytesToBits {P : List Bool → Prop} (a b : ByteArray)
    (ha : P (Deflate.Spec.bytesToBits a)) (hb : P (Deflate.Spec.bytesToBits b)) :
    P (Deflate.Spec.bytesToBits (pickSmaller a b)) := by
  unfold pickSmaller; split <;> assumption

set_option maxRecDepth 8000 in
/-- `emitSmallerBy` (the size-arbitrated, emit-only-the-winner selector, #2753)
    of two candidates that both roundtrip also roundtrips — whichever the size
    comparison forces is emitted, and both decode to `dataOut`. -/
theorem inflate_emitSmallerBy (sa sb : Nat) (a b : Unit → ByteArray) (dataOut : ByteArray) (m : Nat)
    (ha : Zip.Native.Inflate.inflateReference (a ()) m = .ok dataOut)
    (hb : Zip.Native.Inflate.inflateReference (b ()) m = .ok dataOut) :
    Zip.Native.Inflate.inflateReference (emitSmallerBy sa a sb b) m = .ok dataOut := by
  unfold emitSmallerBy; split <;> assumption

/-- `emitSmallerBy` preserves any predicate on the bit stream both candidates meet. -/
theorem emitSmallerBy_bytesToBits {P : List Bool → Prop} (sa sb : Nat) (a b : Unit → ByteArray)
    (ha : P (Deflate.Spec.bytesToBits (a ()))) (hb : P (Deflate.Spec.bytesToBits (b ()))) :
    P (Deflate.Spec.bytesToBits (emitSmallerBy sa a sb b)) := by
  unfold emitSmallerBy; split <;> assumption

/-- Roundtrip for the compressed-block dispatch (`deflateCompressed`), i.e. the
    `deflateRaw` cases without the stored-block fallback. -/
theorem inflate_deflateCompressed (data : ByteArray) (level : UInt8)
    (maxOutputSize : Nat) (hsize : data.size ≤ maxOutputSize) :
    Zip.Native.Inflate.inflateReference (deflateCompressed data level) maxOutputSize = .ok data := by
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
    Zip.Native.Inflate.inflateReference (deflateRawBase data level) maxOutputSize = .ok data := by
  rw [← deflateRawBase_def]
  unfold deflateRawBaseTokens
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

set_option maxRecDepth 8000 in
/-- Unified DEFLATE roundtrip: inflate ∘ deflateRaw = identity.
    This is the Phase B4 capstone theorem from PLAN.md. Generalized to any
    `maxOutputSize` large enough to hold the input. The incompressible pre-scan
    and the level-0 path both dispatch to `deflateStoredPure` directly; the
    cost-model stored fallback is covered by `deflateRawBase`; the level-5–8
    size-arbitrated split (`emitSmallerBy`, #2753) and level-9/10 optimal
    candidates each emit one of concretely-roundtripping blocks. -/
theorem inflate_deflateRaw (data : ByteArray) (level : UInt8)
    (maxOutputSize : Nat) (hsize : data.size ≤ maxOutputSize) :
    Zip.Native.Inflate.inflateReference (deflateRaw data level) maxOutputSize = .ok data := by
  unfold deflateRaw
  dsimp only []
  -- The base and split candidates are *prepared* (sized-with-trees), and only the
  -- winner's emit thunk is forced. Each thunk decodes: the base thunk is
  -- `deflateRawBaseP` (`deflateRawBasePPrep_emit`), each split thunk is
  -- `deflateDynamicBlocksSharedAtP` (`deflateDynamicBlocksSharedAtSizedP_emit`);
  -- both transfer to the already-proven roundtrips. `hbase`/`hsplit` are
  -- generalized over the matcher's level argument because the optimal tiers'
  -- floor pass now runs the cheap L5 knobs (`if 9 ≤ level then 5 else level`).
  have hbase : ∀ l' : UInt8, Zip.Native.Inflate.inflateReference
      ((deflateRawBasePPrep data (lzMatchP data l')).2 ()) maxOutputSize = .ok data := by
    intro l'
    rw [deflateRawBasePPrep_emit, deflateRawBaseP_def]
    exact inflate_deflateRawBase data l' _ hsize
  have hsplit : ∀ (l' : UInt8) cuts, Zip.Native.Inflate.inflateReference
      ((deflateDynamicBlocksSharedAtSizedP data (lzMatchP data l') cuts).2 ())
      maxOutputSize = .ok data := by
    intro l' cuts
    rw [deflateDynamicBlocksSharedAtSizedP_emit, deflateDynamicBlocksSharedAtP_eq,
      lzMatchP_map, deflateDynamicBlocksSharedAt_def]
    exact inflate_deflateDynamicBlocksSharedAt data _ l' _ hsize
  -- `withObs`: base, or the eagerly-selected smaller of base and the obs-split.
  have hwithObs : ∀ (l' : UInt8) (p : Nat × (Unit → ByteArray)),
      p = (if (chooseSplitsHeuristicP (lzMatchP data l') data.size).isEmpty then
            deflateRawBasePPrep data (lzMatchP data l')
          else
            let obsFreqs := deflateObsSplitSizedFreqsP data (lzMatchP data l')
              (chooseSplitsHeuristicP (lzMatchP data l') data.size)
            let basePrep := deflateRawBasePPrepF data (lzMatchP data l') obsFreqs.2
            if basePrep.1 < obsFreqs.1.1 then basePrep else obsFreqs.1) →
      Zip.Native.Inflate.inflateReference (p.2 ()) maxOutputSize = .ok data := by
    intro l' p hp; subst hp
    dsimp only []
    rw [deflateRawBasePPrepF_obsFreqs, deflateObsSplitSizedFreqsP_fst]
    split
    · exact hbase l'
    · split
      · exact hbase l'
      · exact hsplit l' _
  split
  · exact inflate_deflateStoredPure data _ (by omega)
  -- The incompressible pre-scan routes straight to the same stored block.
  · split
    · exact inflate_deflateStoredPure data _ (by omega)
    · split
      · split
        · -- level 9 (L9-fast, #2638): sized floor + optimal via `emitSmallerBy`.
          -- Two nested ites (the floor-level choice and the memory gate) give
          -- four leaves; each is the same `inflate_emitSmallerBy` with the
          -- matching optimal roundtrip and the level-generalized floor.
          split <;>
            first
            | exact inflate_emitSmallerBy _ _ _ _ data maxOutputSize (hbase _)
                (inflate_deflateDynamicBlocksOptimalFast data sharedTokChunk _ hsize)
            | exact inflate_emitSmallerBy _ _ _ _ data maxOutputSize (hbase _)
                (inflate_deflateDynamicBlocksOptimalWindowedFast data sharedTokChunk _ hsize)
        · split
          · -- level ≥ 10: exact-DP crown, sized floor + optimal (see level 9)
            split <;>
              first
              | exact inflate_emitSmallerBy _ _ _ _ data maxOutputSize (hbase _)
                  (inflate_deflateDynamicBlocksOptimal data sharedTokChunk _ hsize)
              | exact inflate_emitSmallerBy _ _ _ _ data maxOutputSize (hbase _)
                  (inflate_deflateDynamicBlocksOptimalWindowed data sharedTokChunk _ hsize)
          · -- levels 5–8: obs-split candidate, `hwithObs`
            exact hwithObs _ _ rfl
      · split
        · -- level 4: the lazy-tier base candidate, unchanged
          exact inflate_deflateRawBase data level _ hsize
        · -- levels 1–3: fused greedy base candidate, byte-identical to
          -- `deflateRawBase` (`deflateRawBaseF_eq`)
          rw [Zip.Native.Deflate.deflateRawBaseF_eq data level (by assumption)]
          exact inflate_deflateRawBase data level _ hsize

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
  rw [← deflateRawBase_def]
  unfold deflateRawBaseTokens
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
  dsimp only []
  have hstored : ∃ (contentBits padding : List Bool),
      Deflate.Spec.bytesToBits (Zip.Spec.DeflateStoredCorrect.deflateStoredPure data)
        = contentBits ++ padding ∧ padding.length < 8 :=
    ⟨Deflate.Spec.bytesToBits (Zip.Spec.DeflateStoredCorrect.deflateStoredPure data),
      [], by simp only [List.append_nil], by decide⟩
  -- The prepared base and split thunks each pad shortly: the base thunk is
  -- `deflateRawBaseP` (`deflateRawBasePPrep_emit`), each split thunk is
  -- `deflateDynamicBlocksSharedAtP` (`deflateDynamicBlocksSharedAtSizedP_emit`).
  have hbase : ∀ l' : UInt8, ∃ (contentBits padding : List Bool),
      Deflate.Spec.bytesToBits ((deflateRawBasePPrep data (lzMatchP data l')).2 ())
        = contentBits ++ padding ∧ padding.length < 8 := by
    intro l'
    rw [deflateRawBasePPrep_emit, deflateRawBaseP_def]; exact deflateRawBase_pad data l' 
  have hsplit : ∀ (l' : UInt8) cuts, ∃ (contentBits padding : List Bool),
      Deflate.Spec.bytesToBits
        ((deflateDynamicBlocksSharedAtSizedP data (lzMatchP data l') cuts).2 ())
        = contentBits ++ padding ∧ padding.length < 8 := by
    intro l' cuts
    rw [deflateDynamicBlocksSharedAtSizedP_emit, deflateDynamicBlocksSharedAtP_eq,
      lzMatchP_map, deflateDynamicBlocksSharedAt_def]
    exact deflateDynamicBlocksSharedAt_pad data _ l' 
  -- `withObs`: base, or the eagerly-selected smaller of base and the obs-split.
  have hwithObs : ∀ (l' : UInt8) (p : Nat × (Unit → ByteArray)),
      p = (if (chooseSplitsHeuristicP (lzMatchP data l') data.size).isEmpty then
            deflateRawBasePPrep data (lzMatchP data l')
          else
            let obsFreqs := deflateObsSplitSizedFreqsP data (lzMatchP data l')
              (chooseSplitsHeuristicP (lzMatchP data l') data.size)
            let basePrep := deflateRawBasePPrepF data (lzMatchP data l') obsFreqs.2
            if basePrep.1 < obsFreqs.1.1 then basePrep else obsFreqs.1) →
      ∃ (contentBits padding : List Bool),
        Deflate.Spec.bytesToBits (p.2 ()) = contentBits ++ padding ∧ padding.length < 8 := by
    intro l' p hp; subst hp
    dsimp only []
    rw [deflateRawBasePPrepF_obsFreqs, deflateObsSplitSizedFreqsP_fst]
    split
    · exact hbase l'
    · split
      · exact hbase l'
      · exact hsplit l' _
  split
  · -- Level 0: stored blocks — all byte-aligned, padding = []
    exact hstored
  -- The incompressible pre-scan routes to the same stored block.
  · split
    · exact hstored
    · split
      · split
        · -- level 9 (L9-fast, #2638): sized floor, four ite leaves (see the
          -- roundtrip theorem's level-9 arm)
          split <;>
            first
            | exact emitSmallerBy_bytesToBits
                (P := fun bits => ∃ (contentBits padding : List Bool),
                  bits = contentBits ++ padding ∧ padding.length < 8)
                _ _ _ _ (hbase _)
                (deflateDynamicBlocksOptimalFast_pad data sharedTokChunk)
            | exact emitSmallerBy_bytesToBits
                (P := fun bits => ∃ (contentBits padding : List Bool),
                  bits = contentBits ++ padding ∧ padding.length < 8)
                _ _ _ _ (hbase _)
                (deflateDynamicBlocksOptimalWindowedFast_pad data sharedTokChunk)
        · split
          · -- level ≥ 10: exact-DP crown, sized floor (see level 9)
            split <;>
              first
              | exact emitSmallerBy_bytesToBits
                  (P := fun bits => ∃ (contentBits padding : List Bool),
                    bits = contentBits ++ padding ∧ padding.length < 8)
                  _ _ _ _ (hbase _)
                  (deflateDynamicBlocksOptimal_pad data sharedTokChunk)
              | exact emitSmallerBy_bytesToBits
                  (P := fun bits => ∃ (contentBits padding : List Bool),
                    bits = contentBits ++ padding ∧ padding.length < 8)
                  _ _ _ _ (hbase _)
                  (deflateDynamicBlocksOptimalWindowed_pad data sharedTokChunk)
          · -- levels 5–8
            exact hwithObs _ _ rfl
      · split
        · -- level 4: lazy-tier base, unchanged
          exact deflateRawBase_pad data level
        · -- levels 1–3: fused greedy base (`deflateRawBaseF_eq`)
          rw [Zip.Native.Deflate.deflateRawBaseF_eq data level (by assumption)]
          exact deflateRawBase_pad data level

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
  rw [← deflateRawBase_def]
  unfold deflateRawBaseTokens
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
  dsimp only []
  have hstored : ∃ remaining,
      Deflate.Spec.decode.goR
          (Deflate.Spec.bytesToBits (Zip.Spec.DeflateStoredCorrect.deflateStoredPure data)) []
        = some (data.data.toList, remaining) ∧ remaining.length < 8 :=
    ⟨[], Deflate.Spec.deflateStoredPure_goR data, by decide⟩
  -- The prepared base and split thunks each leave a short remaining: the base
  -- thunk is `deflateRawBaseP` (`deflateRawBasePPrep_emit`), each split thunk is
  -- `deflateDynamicBlocksSharedAtP` (`deflateDynamicBlocksSharedAtSizedP_emit`).
  have hbase : ∀ l' : UInt8, ∃ remaining,
      Deflate.Spec.decode.goR
        (Deflate.Spec.bytesToBits ((deflateRawBasePPrep data (lzMatchP data l')).2 ())) []
        = some (data.data.toList, remaining) ∧ remaining.length < 8 := by
    intro l'
    rw [deflateRawBasePPrep_emit, deflateRawBaseP_def]; exact deflateRawBase_goR_pad data l' 
  have hsplit : ∀ (l' : UInt8) cuts, ∃ remaining,
      Deflate.Spec.decode.goR
        (Deflate.Spec.bytesToBits
          ((deflateDynamicBlocksSharedAtSizedP data (lzMatchP data l') cuts).2 ())) []
        = some (data.data.toList, remaining) ∧ remaining.length < 8 := by
    intro l' cuts
    rw [deflateDynamicBlocksSharedAtSizedP_emit, deflateDynamicBlocksSharedAtP_eq,
      lzMatchP_map, deflateDynamicBlocksSharedAt_def]
    exact deflateDynamicBlocksSharedAt_goR_pad data _ l' 
  -- `withObs`: base, or the eagerly-selected smaller of base and the obs-split.
  have hwithObs : ∀ (l' : UInt8) (p : Nat × (Unit → ByteArray)),
      p = (if (chooseSplitsHeuristicP (lzMatchP data l') data.size).isEmpty then
            deflateRawBasePPrep data (lzMatchP data l')
          else
            let obsFreqs := deflateObsSplitSizedFreqsP data (lzMatchP data l')
              (chooseSplitsHeuristicP (lzMatchP data l') data.size)
            let basePrep := deflateRawBasePPrepF data (lzMatchP data l') obsFreqs.2
            if basePrep.1 < obsFreqs.1.1 then basePrep else obsFreqs.1) →
      ∃ remaining,
        Deflate.Spec.decode.goR (Deflate.Spec.bytesToBits (p.2 ())) []
          = some (data.data.toList, remaining) ∧ remaining.length < 8 := by
    intro l' p hp; subst hp
    dsimp only []
    rw [deflateRawBasePPrepF_obsFreqs, deflateObsSplitSizedFreqsP_fst]
    split
    · exact hbase l'
    · split
      · exact hbase l'
      · exact hsplit l' _
  split
  · -- Level 0: stored blocks — byte-aligned, remaining = []
    exact hstored
  -- The incompressible pre-scan routes to the same stored block.
  · split
    · exact hstored
    · split
      · split
        · -- level 9 (L9-fast, #2638): sized floor, four ite leaves
          split <;>
            first
            | exact emitSmallerBy_bytesToBits
                (P := fun bits => ∃ remaining,
                  Deflate.Spec.decode.goR bits [] = some (data.data.toList, remaining) ∧
                    remaining.length < 8)
                _ _ _ _ (hbase _)
                (deflateDynamicBlocksOptimalFast_goR_pad data sharedTokChunk)
            | exact emitSmallerBy_bytesToBits
                (P := fun bits => ∃ remaining,
                  Deflate.Spec.decode.goR bits [] = some (data.data.toList, remaining) ∧
                    remaining.length < 8)
                _ _ _ _ (hbase _)
                (deflateDynamicBlocksOptimalWindowedFast_goR_pad data sharedTokChunk)
        · split
          · -- level ≥ 10: exact-DP crown, sized floor (see level 9)
            split <;>
              first
              | exact emitSmallerBy_bytesToBits
                  (P := fun bits => ∃ remaining,
                    Deflate.Spec.decode.goR bits [] = some (data.data.toList, remaining) ∧
                      remaining.length < 8)
                  _ _ _ _ (hbase _)
                  (deflateDynamicBlocksOptimal_goR_pad data sharedTokChunk)
              | exact emitSmallerBy_bytesToBits
                  (P := fun bits => ∃ remaining,
                    Deflate.Spec.decode.goR bits [] = some (data.data.toList, remaining) ∧
                      remaining.length < 8)
                  _ _ _ _ (hbase _)
                  (deflateDynamicBlocksOptimalWindowed_goR_pad data sharedTokChunk)
          · -- levels 5–8
            exact hwithObs _ _ rfl
      · split
        · -- level 4: lazy-tier base, unchanged
          exact deflateRawBase_goR_pad data level
        · -- levels 1–3: fused greedy base (`deflateRawBaseF_eq`)
          rw [Zip.Native.Deflate.deflateRawBaseF_eq data level (by assumption)]
          exact deflateRawBase_goR_pad data level

end Zip.Native.Deflate
