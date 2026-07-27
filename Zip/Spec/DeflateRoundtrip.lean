import Zip.Spec.DeflateFixedCorrect
import Zip.Spec.DeflateDynamicCorrect
import Zip.Spec.LZ77ChainCorrect
import Zip.Spec.LZ77PackedCorrect
import Zip.Spec.DeflateBaseFreqsReuse
import Zip.Spec.DeflateBlockSplit
import Zip.Spec.SplitWalkerPackedCorrect

/-!
# Unified DEFLATE Roundtrip (Phase B4 Capstone)

Proves the unified roundtrip theorem for `deflateRaw`:
`inflate (deflateRaw data level) = .ok data`.

`deflateRaw` is defined in `Zip/Native/DeflateDynamic.lean`. Level 0 is stored
and level 1 is the single-block cost-model point. Within the inclusive
5–64 MiB band, levels 2–6 use a content profile to select among proven greedy,
split, and retained-profile L7 constituents; outside it they keep their exact
pre-adaptive pipelines. Level 7 uses its retained profile directly, level 8
compares the cross-block shared-window split at the observation-divergence
boundaries (#2737) against its base, adaptive level 9 selects exact L8/L10
constituents within the same bounded band, and level 10 remains the exact-DP
crown.

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

/-- The level-dispatched token stream (`lzMatch`: greedy chain at levels 1–4, lazy
    chain at ≥ 5). The three contracts (`cEnc`/`cEmpty`/`cRes`) are what
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

/-- Contracts for an arbitrary greedy policy used by the adaptive fast tier. -/
private theorem cGreedyEnc (data : ByteArray) (maxChain insertCap niceLen : Nat) :
    ∀ t ∈ (lz77ChainIter data maxChain 32768 insertCap niceLen).toList,
      match t with
      | .literal _ => True
      | .reference len dist => 3 ≤ len ∧ len ≤ 258 ∧ 1 ≤ dist ∧ dist ≤ 32768 :=
  lz77ChainIter_encodable data maxChain 32768 insertCap niceLen (by omega) (by omega)

private theorem cGreedyEmpty (data : ByteArray) (maxChain insertCap niceLen : Nat)
    (hz : data.size = 0) :
    lz77ChainIter data maxChain 32768 insertCap niceLen = #[] :=
  lz77ChainIter_empty data maxChain 32768 insertCap niceLen hz

private theorem cGreedyRes (data : ByteArray) (maxChain insertCap niceLen : Nat) :
    Deflate.Spec.resolveLZ77
        (tokensToSymbols (lz77ChainIter data maxChain 32768 insertCap niceLen)) [] =
      some data.data.toList :=
  lz77ChainIter_resolves data maxChain 32768 insertCap niceLen (by omega)

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
/-- Roundtrip for the arbitrary native-wide greedy base used by adaptive
    L2–L6. -/
theorem inflate_deflateRawBaseFNU64 (data : ByteArray)
    (maxChain insertCap niceLen maxOutputSize : Nat)
    (hsize : data.size ≤ maxOutputSize) :
    Zip.Native.Inflate.inflateReference
        (deflateRawBaseFNU64 data maxChain insertCap niceLen) maxOutputSize =
      .ok data := by
  rw [deflateRawBaseFNU64_eq, ← deflateRawBaseP_eq,
    lz77ChainIterP_map data maxChain 32768 insertCap niceLen (by omega) (by omega)]
  unfold deflateRawBaseTokens
  dsimp only []
  split <;> split
  · exact inflate_deflateStoredPure data _ hsize
  · exact inflate_deflateFixedBlock data
      (lz77ChainIter data maxChain 32768 insertCap niceLen)
      (cGreedyEnc data maxChain insertCap niceLen)
      (fun hz => cGreedyEmpty data maxChain insertCap niceLen hz)
      (cGreedyRes data maxChain insertCap niceLen) _ hsize
  · exact inflate_deflateStoredPure data _ hsize
  · exact inflate_deflateDynamicBlock data
      (lz77ChainIter data maxChain 32768 insertCap niceLen)
      (cGreedyEnc data maxChain insertCap niceLen)
      (fun hz => cGreedyEmpty data maxChain insertCap niceLen hz)
      (cGreedyRes data maxChain insertCap niceLen) _ hsize

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8000 in
/-- Unified DEFLATE roundtrip against the **reference** decoder:
    `inflateReference ∘ deflateRaw = identity`.
    This is the Phase B4 capstone theorem from PLAN.md. Generalized to any
    `maxOutputSize` large enough to hold the input. The incompressible pre-scan
    and the level-0 path both dispatch to `deflateStoredPure` directly; the
    cost-model stored fallback is covered by `deflateRawBase`; every adaptive
    L2–L6 constituent, the level-8 size-arbitrated split (`emitSmallerBy`,
    #2753), retained L9-fast source, adaptive L9 endpoint, and level-10 optimal
    candidate each emit concretely-roundtripping blocks.

    The whole inductive proof is built on the reference decoder; the capstone
    stated against the decoder we actually ship, `Inflate.inflate`, is
    `inflate_deflateRaw` (`Zip/Spec/DeflateRoundtripProduction.lean`), a direct
    corollary via the accept-set equality `inflate_ok_iff_reference`. -/
theorem inflateReference_deflateRaw (data : ByteArray) (level : UInt8)
    (maxOutputSize : Nat) (hsize : data.size ≤ maxOutputSize) :
    Zip.Native.Inflate.inflateReference (deflateRaw data level) maxOutputSize = .ok data := by
  unfold deflateRaw
  dsimp only []
  -- The base and split candidates are *prepared* (sized-with-trees), and only the
  -- winner's emit thunk is forced. Each thunk decodes: the base thunk is
  -- `deflateRawBaseP` (`deflateRawBasePPrep_emit`), each split thunk is
  -- `deflateDynamicBlocksSharedAtP` (`deflateDynamicBlocksSharedAtSizedP_emit`);
  -- both transfer to the already-proven roundtrips. `hbase`/`hsplit` remain
  -- generalized over the matcher's level argument because several exact
  -- pre-adaptive constituents reuse these prepared pipelines.
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
  have hbaseDirect : ∀ l' : UInt8, Zip.Native.Inflate.inflateReference
      (deflateRawBaseP data (lzMatchP data l')) maxOutputSize = .ok data := by
    intro l'
    rw [← deflateRawBasePPrep_emit]
    exact hbase l'
  have hsplitDirect : ∀ (l' : UInt8) cuts, Zip.Native.Inflate.inflateReference
      (deflateDynamicBlocksSharedAtTreesP data (lzMatchP data l') cuts)
      maxOutputSize = .ok data := by
    intro l' cuts
    rw [deflateDynamicBlocksSharedAtTreesP_eq, deflateDynamicBlocksSharedAtP_eq,
      lzMatchP_map, deflateDynamicBlocksSharedAt_def]
    exact inflate_deflateDynamicBlocksSharedAt data _ l' _ hsize
  -- `withObs`: base, or the eagerly-selected smaller of base and the obs-split.
  have hwithObs : ∀ (l' checkLevel : UInt8) (p : Nat × (Unit → ByteArray)),
      p = (if (chooseSplitsHeuristicP (lzMatchP data l') data.size splitMinBlockBytes
              splitSoftMaxBlockBytes (splitCheckTokensFor data checkLevel)).isEmpty then
            deflateRawBasePPrep data (lzMatchP data l')
          else
            let obsFreqs := deflateObsSplitSizedFreqsP data (lzMatchP data l')
              (chooseSplitsHeuristicP (lzMatchP data l') data.size splitMinBlockBytes
                splitSoftMaxBlockBytes (splitCheckTokensFor data checkLevel))
            let basePrep := deflateRawBasePPrepF data (lzMatchP data l') obsFreqs.2
            if basePrep.1 < obsFreqs.1.1 then basePrep else obsFreqs.1) →
      Zip.Native.Inflate.inflateReference (p.2 ()) maxOutputSize = .ok data := by
    intro l' checkLevel p hp; subst hp
    dsimp only []
    rw [deflateRawBasePPrepF_obsFreqs, deflateObsSplitSizedFreqsP_fst]
    split
    · exact hbase l'
    · split
      · exact hbase l'
      · exact hsplit l' _
  have hcheck7 : l7SplitCheckTokensFor data (l7ProfileFor data) =
      splitCheckTokensFor data 7 := by rfl
  have hsplitLevel : ∀ l' : UInt8, Zip.Native.Inflate.inflateReference
      (deflateRawSplitLevelP data l') maxOutputSize = .ok data := by
    intro l'
    unfold deflateRawSplitLevelP deflateRawSplitLevelTokensP
    dsimp only []
    simp only [chooseSplitsHeuristicPUPacked_lzMatchP_eq,
      chooseSplitsHeuristicPU_eq, ite_self]
    unfold deflateRawSplitTierP
    exact hwithObs l' l' _ rfl
  have hl7 : Zip.Native.Inflate.inflateReference
      (deflateRawL7P data (l7ProfileFor data)) maxOutputSize = .ok data := by
    change Zip.Native.Inflate.inflateReference
        (deflateRawL7RouteP data (l7ProfileFor data) (lzMatchP data 7))
          maxOutputSize = .ok data
    unfold deflateRawL7RouteP
    split
    · dsimp only
      rw [hcheck7, chooseSplitsHeuristicPUPacked_lzMatchP_eq]
      unfold deflateRawSplitTierP
      exact hwithObs 7 7 _ rfl
    · exact hbaseDirect 7
    · dsimp only
      rw [hcheck7, chooseSplitsHeuristicPUPacked_lzMatchP_eq]
      split
      · exact hbaseDirect 7
      · exact hsplitDirect 7 _
  have hgreedyLevel : ∀ (l' : UInt8), ¬(5 ≤ l') →
      Zip.Native.Inflate.inflateReference
        (deflateRawBaseF data l') maxOutputSize = .ok data := by
    intro l' hl'
    rw [deflateRawBaseF_eq data l' hl']
    exact inflate_deflateRawBase data l' _ hsize
  have hfast : Zip.Native.Inflate.inflateReference
      (deflateRawAdaptiveFast data) maxOutputSize = .ok data := by
    unfold deflateRawAdaptiveFast
    exact inflate_deflateRawBaseFNU64 data 8 12 258 maxOutputSize hsize
  have hl2 : Zip.Native.Inflate.inflateReference
      (deflateRawL2Adaptive data) maxOutputSize = .ok data := by
    unfold deflateRawL2Adaptive
    split
    · exact hgreedyLevel 2 (by decide)
    · exact hgreedyLevel 1 (by decide)
  have hl3 : Zip.Native.Inflate.inflateReference
      (deflateRawL3Adaptive data) maxOutputSize = .ok data := by
    unfold deflateRawL3Adaptive
    split
    · exact hgreedyLevel 3 (by decide)
    · exact hfast
    · exact hgreedyLevel 2 (by decide)
    · exact hgreedyLevel 4 (by decide)
  have hl4 : Zip.Native.Inflate.inflateReference
      (deflateRawL4Adaptive data) maxOutputSize = .ok data := by
    unfold deflateRawL4Adaptive
    split
    · exact hgreedyLevel 4 (by decide)
    · exact hfast
    · exact hsplitLevel 5
  have hl5 : Zip.Native.Inflate.inflateReference
      (deflateRawL5Adaptive data) maxOutputSize = .ok data := by
    unfold deflateRawL5Adaptive
    split
    · exact hsplitLevel 5
    · dsimp only
      split
      · exact hsplitLevel 5
      · exact hfast
      · exact hl7
  have hl6 : Zip.Native.Inflate.inflateReference
      (deflateRawL6Adaptive data) maxOutputSize = .ok data := by
    unfold deflateRawL6Adaptive
    split
    · exact hsplitLevel 6
    · dsimp only
      split
      · exact hsplitLevel 6
      · exact hfast
      · exact hsplitLevel 5
      · exact hl7
  have hl8 : Zip.Native.Inflate.inflateReference
      (deflateRawL8P data) maxOutputSize = .ok data := by
    unfold deflateRawL8P deflateRawL8TokensP
    rw [chooseSplitsHeuristicPUPacked_lzMatchP_eq]
    unfold deflateRawSplitTierP
    exact hwithObs 8 8 _ rfl
  have hl9 : Zip.Native.Inflate.inflateReference
      (deflateRawL9P data) maxOutputSize = .ok data := by
    unfold deflateRawL9P deflateRawL9TokensP
    dsimp only []
    split <;>
      first
      | exact inflate_emitSmallerBy _ _ _ _ data maxOutputSize (hbase 9)
          (inflate_deflateDynamicBlocksOptimalFast data sharedTokChunk _ hsize)
      | exact inflate_emitSmallerBy _ _ _ _ data maxOutputSize (hbase 9)
          (inflate_deflateDynamicBlocksOptimalWindowedFast data sharedTokChunk _ hsize)
  have hl10 : Zip.Native.Inflate.inflateReference
      (deflateRawL10P data) maxOutputSize = .ok data := by
    unfold deflateRawL10P deflateRawL10TokensP
    dsimp only []
    split <;>
      first
      | exact inflate_emitSmallerBy _ _ _ _ data maxOutputSize (hbase 10)
          (inflate_deflateDynamicBlocksOptimal data sharedTokChunk _ hsize)
      | exact inflate_emitSmallerBy _ _ _ _ data maxOutputSize (hbase 10)
          (inflate_deflateDynamicBlocksOptimalWindowed data sharedTokChunk _ hsize)
  have hadaptive : Zip.Native.Inflate.inflateReference
      (deflateRawL9AdaptiveP data (l7ProfileFor data)) maxOutputSize = .ok data := by
    unfold deflateRawL9AdaptiveP deflateRawL9RouteP
    split
    · exact hl9
    · exact hl8
    · exact hl10
  split
  · exact inflate_deflateStoredPure data _ (by omega)
  -- The incompressible pre-scan routes straight to the same stored block.
  · split
    · exact inflate_deflateStoredPure data _ (by omega)
    · split
      · split
        · exact hl5
        · split
          · exact hl6
          · split
            · exact hl7
            · split
              · split
                · exact hadaptive
                · exact hl9
              · split
                · -- level ≥ 10: exact-DP crown, sized floor + optimal.
                  unfold deflateRawL10TokensP
                  dsimp only []
                  split <;>
                    first
                    | exact inflate_emitSmallerBy _ _ _ _ data maxOutputSize (hbase _)
                        (inflate_deflateDynamicBlocksOptimal data sharedTokChunk _ hsize)
                    | exact inflate_emitSmallerBy _ _ _ _ data maxOutputSize (hbase _)
                        (inflate_deflateDynamicBlocksOptimalWindowed data sharedTokChunk _ hsize)
                · split
                  · -- level 8: exact named source point used by adaptive L9.
                    have hlevel : level = 8 := by
                      simpa only [beq_iff_eq] using
                        (show (level == 8) = true by assumption)
                    subst level
                    exact hl8
                  · change Zip.Native.Inflate.inflateReference
                      (deflateRawSplitLevelP data level) maxOutputSize = .ok data
                    exact hsplitLevel level
      · split
        · exact hl2
        · split
          · exact hl3
          · split
            · exact hl4
            · exact hgreedyLevel level (by assumption)

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

set_option maxRecDepth 8000 in
/-- Padding decomposition for the arbitrary native-wide greedy base used by
    adaptive L2–L6. -/
theorem deflateRawBaseFNU64_pad (data : ByteArray)
    (maxChain insertCap niceLen : Nat) :
    ∃ (contentBits padding : List Bool),
      Deflate.Spec.bytesToBits
          (deflateRawBaseFNU64 data maxChain insertCap niceLen) =
        contentBits ++ padding ∧ padding.length < 8 := by
  rw [deflateRawBaseFNU64_eq, ← deflateRawBaseP_eq,
    lz77ChainIterP_map data maxChain 32768 insertCap niceLen (by omega) (by omega)]
  unfold deflateRawBaseTokens
  dsimp only []
  have hstored : ∃ (contentBits padding : List Bool),
      Deflate.Spec.bytesToBits
          (Zip.Spec.DeflateStoredCorrect.deflateStoredPure data) =
        contentBits ++ padding ∧ padding.length < 8 :=
    ⟨Deflate.Spec.bytesToBits (Zip.Spec.DeflateStoredCorrect.deflateStoredPure data),
      [], by simp only [List.append_nil], by decide⟩
  have hfixed : ∃ (contentBits padding : List Bool),
      Deflate.Spec.bytesToBits
          (deflateFixedBlock data
            (lz77ChainIter data maxChain 32768 insertCap niceLen)) =
        contentBits ++ padding ∧ padding.length < 8 := by
    obtain ⟨bits, _, hbytes⟩ := deflateFixedBlock_spec_of data
      (lz77ChainIter data maxChain 32768 insertCap niceLen)
      (cGreedyEnc data maxChain insertCap niceLen)
      (fun hz => cGreedyEmpty data maxChain insertCap niceLen hz)
    exact ⟨bits, List.replicate ((8 - bits.length % 8) % 8) false,
      hbytes, by simp only [List.length_replicate]; omega⟩
  have hdyn : ∃ (contentBits padding : List Bool),
      Deflate.Spec.bytesToBits
          (deflateDynamicBlock data
            (lz77ChainIter data maxChain 32768 insertCap niceLen)) =
        contentBits ++ padding ∧ padding.length < 8 := by
    obtain ⟨_, _, headerBits, symBits, _, _, _, _, _, _, _, _, _, _, hbytes⟩ :=
      deflateDynamicBlock_spec data
        (lz77ChainIter data maxChain 32768 insertCap niceLen)
        (cGreedyEnc data maxChain insertCap niceLen)
        (fun hz => cGreedyEmpty data maxChain insertCap niceLen hz)
    exact ⟨[true, false, true] ++ headerBits ++ symBits,
      List.replicate
        ((8 - ([true, false, true] ++ headerBits ++ symBits).length % 8) % 8) false,
      hbytes, by simp only [List.length_replicate]; omega⟩
  split <;> split
  · exact hstored
  · exact hfixed
  · exact hstored
  · exact hdyn

set_option maxHeartbeats 1000000 in
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
  have hbaseDirect : ∀ l' : UInt8, ∃ (contentBits padding : List Bool),
      Deflate.Spec.bytesToBits (deflateRawBaseP data (lzMatchP data l')) =
        contentBits ++ padding ∧ padding.length < 8 := by
    intro l'
    rw [← deflateRawBasePPrep_emit]
    exact hbase l'
  have hsplitDirect : ∀ (l' : UInt8) cuts, ∃ (contentBits padding : List Bool),
      Deflate.Spec.bytesToBits
        (deflateDynamicBlocksSharedAtTreesP data (lzMatchP data l') cuts) =
          contentBits ++ padding ∧ padding.length < 8 := by
    intro l' cuts
    rw [deflateDynamicBlocksSharedAtTreesP_eq, deflateDynamicBlocksSharedAtP_eq,
      lzMatchP_map, deflateDynamicBlocksSharedAt_def]
    exact deflateDynamicBlocksSharedAt_pad data _ l'
  -- `withObs`: base, or the eagerly-selected smaller of base and the obs-split.
  have hwithObs : ∀ (l' checkLevel : UInt8) (p : Nat × (Unit → ByteArray)),
      p = (if (chooseSplitsHeuristicP (lzMatchP data l') data.size splitMinBlockBytes
              splitSoftMaxBlockBytes (splitCheckTokensFor data checkLevel)).isEmpty then
            deflateRawBasePPrep data (lzMatchP data l')
          else
            let obsFreqs := deflateObsSplitSizedFreqsP data (lzMatchP data l')
              (chooseSplitsHeuristicP (lzMatchP data l') data.size splitMinBlockBytes
                splitSoftMaxBlockBytes (splitCheckTokensFor data checkLevel))
            let basePrep := deflateRawBasePPrepF data (lzMatchP data l') obsFreqs.2
            if basePrep.1 < obsFreqs.1.1 then basePrep else obsFreqs.1) →
      ∃ (contentBits padding : List Bool),
        Deflate.Spec.bytesToBits (p.2 ()) = contentBits ++ padding ∧ padding.length < 8 := by
    intro l' checkLevel p hp; subst hp
    dsimp only []
    rw [deflateRawBasePPrepF_obsFreqs, deflateObsSplitSizedFreqsP_fst]
    split
    · exact hbase l'
    · split
      · exact hbase l'
      · exact hsplit l' _
  have hcheck7 : l7SplitCheckTokensFor data (l7ProfileFor data) =
      splitCheckTokensFor data 7 := by rfl
  have hsplitLevel : ∀ l' : UInt8, ∃ (contentBits padding : List Bool),
      Deflate.Spec.bytesToBits (deflateRawSplitLevelP data l') =
        contentBits ++ padding ∧ padding.length < 8 := by
    intro l'
    unfold deflateRawSplitLevelP deflateRawSplitLevelTokensP
    dsimp only []
    simp only [chooseSplitsHeuristicPUPacked_lzMatchP_eq,
      chooseSplitsHeuristicPU_eq, ite_self]
    unfold deflateRawSplitTierP
    exact hwithObs l' l' _ rfl
  have hl7 : ∃ (contentBits padding : List Bool),
      Deflate.Spec.bytesToBits (deflateRawL7P data (l7ProfileFor data)) =
        contentBits ++ padding ∧ padding.length < 8 := by
    change ∃ (contentBits padding : List Bool),
      Deflate.Spec.bytesToBits
          (deflateRawL7RouteP data (l7ProfileFor data) (lzMatchP data 7)) =
        contentBits ++ padding ∧ padding.length < 8
    unfold deflateRawL7RouteP
    split
    · dsimp only
      rw [hcheck7, chooseSplitsHeuristicPUPacked_lzMatchP_eq]
      unfold deflateRawSplitTierP
      exact hwithObs 7 7 _ rfl
    · exact hbaseDirect 7
    · dsimp only
      rw [hcheck7, chooseSplitsHeuristicPUPacked_lzMatchP_eq]
      split
      · exact hbaseDirect 7
      · exact hsplitDirect 7 _
  have hgreedyLevel : ∀ (l' : UInt8), ¬(5 ≤ l') →
      ∃ (contentBits padding : List Bool),
        Deflate.Spec.bytesToBits (deflateRawBaseF data l') =
          contentBits ++ padding ∧ padding.length < 8 := by
    intro l' hl'
    rw [deflateRawBaseF_eq data l' hl']
    exact deflateRawBase_pad data l'
  have hfast : ∃ (contentBits padding : List Bool),
      Deflate.Spec.bytesToBits (deflateRawAdaptiveFast data) =
        contentBits ++ padding ∧ padding.length < 8 := by
    unfold deflateRawAdaptiveFast
    exact deflateRawBaseFNU64_pad data 8 12 258
  have hl2 : ∃ (contentBits padding : List Bool),
      Deflate.Spec.bytesToBits (deflateRawL2Adaptive data) =
        contentBits ++ padding ∧ padding.length < 8 := by
    unfold deflateRawL2Adaptive
    split
    · exact hgreedyLevel 2 (by decide)
    · exact hgreedyLevel 1 (by decide)
  have hl3 : ∃ (contentBits padding : List Bool),
      Deflate.Spec.bytesToBits (deflateRawL3Adaptive data) =
        contentBits ++ padding ∧ padding.length < 8 := by
    unfold deflateRawL3Adaptive
    split
    · exact hgreedyLevel 3 (by decide)
    · exact hfast
    · exact hgreedyLevel 2 (by decide)
    · exact hgreedyLevel 4 (by decide)
  have hl4 : ∃ (contentBits padding : List Bool),
      Deflate.Spec.bytesToBits (deflateRawL4Adaptive data) =
        contentBits ++ padding ∧ padding.length < 8 := by
    unfold deflateRawL4Adaptive
    split
    · exact hgreedyLevel 4 (by decide)
    · exact hfast
    · exact hsplitLevel 5
  have hl5 : ∃ (contentBits padding : List Bool),
      Deflate.Spec.bytesToBits (deflateRawL5Adaptive data) =
        contentBits ++ padding ∧ padding.length < 8 := by
    unfold deflateRawL5Adaptive
    split
    · exact hsplitLevel 5
    · dsimp only
      split
      · exact hsplitLevel 5
      · exact hfast
      · exact hl7
  have hl6 : ∃ (contentBits padding : List Bool),
      Deflate.Spec.bytesToBits (deflateRawL6Adaptive data) =
        contentBits ++ padding ∧ padding.length < 8 := by
    unfold deflateRawL6Adaptive
    split
    · exact hsplitLevel 6
    · dsimp only
      split
      · exact hsplitLevel 6
      · exact hfast
      · exact hsplitLevel 5
      · exact hl7
  have hl8 : ∃ (contentBits padding : List Bool),
      Deflate.Spec.bytesToBits (deflateRawL8P data) =
        contentBits ++ padding ∧ padding.length < 8 := by
    unfold deflateRawL8P deflateRawL8TokensP
    rw [chooseSplitsHeuristicPUPacked_lzMatchP_eq]
    unfold deflateRawSplitTierP
    exact hwithObs 8 8 _ rfl
  have hl9 : ∃ (contentBits padding : List Bool),
      Deflate.Spec.bytesToBits (deflateRawL9P data) =
        contentBits ++ padding ∧ padding.length < 8 := by
    unfold deflateRawL9P deflateRawL9TokensP
    dsimp only []
    split <;>
      first
      | exact emitSmallerBy_bytesToBits
          (P := fun bits => ∃ (contentBits padding : List Bool),
            bits = contentBits ++ padding ∧ padding.length < 8)
          _ _ _ _ (hbase 9)
          (deflateDynamicBlocksOptimalFast_pad data sharedTokChunk)
      | exact emitSmallerBy_bytesToBits
          (P := fun bits => ∃ (contentBits padding : List Bool),
            bits = contentBits ++ padding ∧ padding.length < 8)
          _ _ _ _ (hbase 9)
          (deflateDynamicBlocksOptimalWindowedFast_pad data sharedTokChunk)
  have hl10 : ∃ (contentBits padding : List Bool),
      Deflate.Spec.bytesToBits (deflateRawL10P data) =
        contentBits ++ padding ∧ padding.length < 8 := by
    unfold deflateRawL10P deflateRawL10TokensP
    dsimp only []
    split <;>
      first
      | exact emitSmallerBy_bytesToBits
          (P := fun bits => ∃ (contentBits padding : List Bool),
            bits = contentBits ++ padding ∧ padding.length < 8)
          _ _ _ _ (hbase 10)
          (deflateDynamicBlocksOptimal_pad data sharedTokChunk)
      | exact emitSmallerBy_bytesToBits
          (P := fun bits => ∃ (contentBits padding : List Bool),
            bits = contentBits ++ padding ∧ padding.length < 8)
          _ _ _ _ (hbase 10)
          (deflateDynamicBlocksOptimalWindowed_pad data sharedTokChunk)
  have hadaptive : ∃ (contentBits padding : List Bool),
      Deflate.Spec.bytesToBits
          (deflateRawL9AdaptiveP data (l7ProfileFor data)) =
        contentBits ++ padding ∧ padding.length < 8 := by
    unfold deflateRawL9AdaptiveP deflateRawL9RouteP
    split
    · exact hl9
    · exact hl8
    · exact hl10
  split
  · -- Level 0: stored blocks — all byte-aligned, padding = []
    exact hstored
  -- The incompressible pre-scan routes to the same stored block.
  · split
    · exact hstored
    · split
      · split
        · exact hl5
        · split
          · exact hl6
          · split
            · exact hl7
            · split
              · split
                · exact hadaptive
                · exact hl9
              · split
                · -- level ≥ 10: exact-DP crown, sized floor.
                  unfold deflateRawL10TokensP
                  dsimp only []
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
                · split
                  · -- level 8: exact named source point used by adaptive L9.
                    have hlevel : level = 8 := by
                      simpa only [beq_iff_eq] using
                        (show (level == 8) = true by assumption)
                    subst level
                    exact hl8
                  · change ∃ (contentBits padding : List Bool),
                      Deflate.Spec.bytesToBits (deflateRawSplitLevelP data level) =
                        contentBits ++ padding ∧ padding.length < 8
                    exact hsplitLevel level
      · split
        · exact hl2
        · split
          · exact hl3
          · split
            · exact hl4
            · exact hgreedyLevel level (by assumption)

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

set_option maxRecDepth 8000 in
/-- `goR` short-remaining for the arbitrary native-wide greedy base used by
    adaptive L2–L6. -/
theorem deflateRawBaseFNU64_goR_pad (data : ByteArray)
    (maxChain insertCap niceLen : Nat) :
    ∃ remaining,
      Deflate.Spec.decode.goR
          (Deflate.Spec.bytesToBits
            (deflateRawBaseFNU64 data maxChain insertCap niceLen)) [] =
        some (data.data.toList, remaining) ∧ remaining.length < 8 := by
  rw [deflateRawBaseFNU64_eq, ← deflateRawBaseP_eq,
    lz77ChainIterP_map data maxChain 32768 insertCap niceLen (by omega) (by omega)]
  unfold deflateRawBaseTokens
  dsimp only []
  have hfixed : ∃ remaining,
      Deflate.Spec.decode.goR
          (Deflate.Spec.bytesToBits
            (deflateFixedBlock data
              (lz77ChainIter data maxChain 32768 insertCap niceLen))) [] =
        some (data.data.toList, remaining) ∧ remaining.length < 8 :=
    deflateFixedBlock_goR_pad data
      (lz77ChainIter data maxChain 32768 insertCap niceLen)
      (cGreedyEnc data maxChain insertCap niceLen)
      (fun hz => cGreedyEmpty data maxChain insertCap niceLen hz)
      (cGreedyRes data maxChain insertCap niceLen)
  split <;> split
  · exact ⟨[], Deflate.Spec.deflateStoredPure_goR data, by decide⟩
  · exact hfixed
  · exact ⟨[], Deflate.Spec.deflateStoredPure_goR data, by decide⟩
  · exact deflateDynamicBlock_goR_pad data
      (lz77ChainIter data maxChain 32768 insertCap niceLen)
      (cGreedyEnc data maxChain insertCap niceLen)
      (fun hz => cGreedyEmpty data maxChain insertCap niceLen hz)
      (cGreedyRes data maxChain insertCap niceLen)

set_option maxHeartbeats 1000000 in
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
  have hbaseDirect : ∀ l' : UInt8, ∃ remaining,
      Deflate.Spec.decode.goR
        (Deflate.Spec.bytesToBits (deflateRawBaseP data (lzMatchP data l'))) [] =
          some (data.data.toList, remaining) ∧ remaining.length < 8 := by
    intro l'
    rw [← deflateRawBasePPrep_emit]
    exact hbase l'
  have hsplitDirect : ∀ (l' : UInt8) cuts, ∃ remaining,
      Deflate.Spec.decode.goR
        (Deflate.Spec.bytesToBits
          (deflateDynamicBlocksSharedAtTreesP data (lzMatchP data l') cuts)) [] =
            some (data.data.toList, remaining) ∧ remaining.length < 8 := by
    intro l' cuts
    rw [deflateDynamicBlocksSharedAtTreesP_eq, deflateDynamicBlocksSharedAtP_eq,
      lzMatchP_map, deflateDynamicBlocksSharedAt_def]
    exact deflateDynamicBlocksSharedAt_goR_pad data _ l'
  -- `withObs`: base, or the eagerly-selected smaller of base and the obs-split.
  have hwithObs : ∀ (l' checkLevel : UInt8) (p : Nat × (Unit → ByteArray)),
      p = (if (chooseSplitsHeuristicP (lzMatchP data l') data.size splitMinBlockBytes
              splitSoftMaxBlockBytes (splitCheckTokensFor data checkLevel)).isEmpty then
            deflateRawBasePPrep data (lzMatchP data l')
          else
            let obsFreqs := deflateObsSplitSizedFreqsP data (lzMatchP data l')
              (chooseSplitsHeuristicP (lzMatchP data l') data.size splitMinBlockBytes
                splitSoftMaxBlockBytes (splitCheckTokensFor data checkLevel))
            let basePrep := deflateRawBasePPrepF data (lzMatchP data l') obsFreqs.2
            if basePrep.1 < obsFreqs.1.1 then basePrep else obsFreqs.1) →
      ∃ remaining,
        Deflate.Spec.decode.goR (Deflate.Spec.bytesToBits (p.2 ())) []
          = some (data.data.toList, remaining) ∧ remaining.length < 8 := by
    intro l' checkLevel p hp; subst hp
    dsimp only []
    rw [deflateRawBasePPrepF_obsFreqs, deflateObsSplitSizedFreqsP_fst]
    split
    · exact hbase l'
    · split
      · exact hbase l'
      · exact hsplit l' _
  have hcheck7 : l7SplitCheckTokensFor data (l7ProfileFor data) =
      splitCheckTokensFor data 7 := by rfl
  have hsplitLevel : ∀ l' : UInt8, ∃ remaining,
      Deflate.Spec.decode.goR
          (Deflate.Spec.bytesToBits (deflateRawSplitLevelP data l')) [] =
        some (data.data.toList, remaining) ∧ remaining.length < 8 := by
    intro l'
    unfold deflateRawSplitLevelP deflateRawSplitLevelTokensP
    dsimp only []
    simp only [chooseSplitsHeuristicPUPacked_lzMatchP_eq,
      chooseSplitsHeuristicPU_eq, ite_self]
    unfold deflateRawSplitTierP
    exact hwithObs l' l' _ rfl
  have hl7 : ∃ remaining,
      Deflate.Spec.decode.goR
          (Deflate.Spec.bytesToBits
            (deflateRawL7P data (l7ProfileFor data))) [] =
        some (data.data.toList, remaining) ∧ remaining.length < 8 := by
    change ∃ remaining,
      Deflate.Spec.decode.goR
          (Deflate.Spec.bytesToBits
            (deflateRawL7RouteP data (l7ProfileFor data) (lzMatchP data 7))) [] =
        some (data.data.toList, remaining) ∧ remaining.length < 8
    unfold deflateRawL7RouteP
    split
    · dsimp only
      rw [hcheck7, chooseSplitsHeuristicPUPacked_lzMatchP_eq]
      unfold deflateRawSplitTierP
      exact hwithObs 7 7 _ rfl
    · exact hbaseDirect 7
    · dsimp only
      rw [hcheck7, chooseSplitsHeuristicPUPacked_lzMatchP_eq]
      split
      · exact hbaseDirect 7
      · exact hsplitDirect 7 _
  have hgreedyLevel : ∀ (l' : UInt8), ¬(5 ≤ l') → ∃ remaining,
      Deflate.Spec.decode.goR
          (Deflate.Spec.bytesToBits (deflateRawBaseF data l')) [] =
        some (data.data.toList, remaining) ∧ remaining.length < 8 := by
    intro l' hl'
    rw [deflateRawBaseF_eq data l' hl']
    exact deflateRawBase_goR_pad data l'
  have hfast : ∃ remaining,
      Deflate.Spec.decode.goR
          (Deflate.Spec.bytesToBits (deflateRawAdaptiveFast data)) [] =
        some (data.data.toList, remaining) ∧ remaining.length < 8 := by
    unfold deflateRawAdaptiveFast
    exact deflateRawBaseFNU64_goR_pad data 8 12 258
  have hl2 : ∃ remaining,
      Deflate.Spec.decode.goR
          (Deflate.Spec.bytesToBits (deflateRawL2Adaptive data)) [] =
        some (data.data.toList, remaining) ∧ remaining.length < 8 := by
    unfold deflateRawL2Adaptive
    split
    · exact hgreedyLevel 2 (by decide)
    · exact hgreedyLevel 1 (by decide)
  have hl3 : ∃ remaining,
      Deflate.Spec.decode.goR
          (Deflate.Spec.bytesToBits (deflateRawL3Adaptive data)) [] =
        some (data.data.toList, remaining) ∧ remaining.length < 8 := by
    unfold deflateRawL3Adaptive
    split
    · exact hgreedyLevel 3 (by decide)
    · exact hfast
    · exact hgreedyLevel 2 (by decide)
    · exact hgreedyLevel 4 (by decide)
  have hl4 : ∃ remaining,
      Deflate.Spec.decode.goR
          (Deflate.Spec.bytesToBits (deflateRawL4Adaptive data)) [] =
        some (data.data.toList, remaining) ∧ remaining.length < 8 := by
    unfold deflateRawL4Adaptive
    split
    · exact hgreedyLevel 4 (by decide)
    · exact hfast
    · exact hsplitLevel 5
  have hl5 : ∃ remaining,
      Deflate.Spec.decode.goR
          (Deflate.Spec.bytesToBits (deflateRawL5Adaptive data)) [] =
        some (data.data.toList, remaining) ∧ remaining.length < 8 := by
    unfold deflateRawL5Adaptive
    split
    · exact hsplitLevel 5
    · dsimp only
      split
      · exact hsplitLevel 5
      · exact hfast
      · exact hl7
  have hl6 : ∃ remaining,
      Deflate.Spec.decode.goR
          (Deflate.Spec.bytesToBits (deflateRawL6Adaptive data)) [] =
        some (data.data.toList, remaining) ∧ remaining.length < 8 := by
    unfold deflateRawL6Adaptive
    split
    · exact hsplitLevel 6
    · dsimp only
      split
      · exact hsplitLevel 6
      · exact hfast
      · exact hsplitLevel 5
      · exact hl7
  have hl8 : ∃ remaining,
      Deflate.Spec.decode.goR
          (Deflate.Spec.bytesToBits (deflateRawL8P data)) [] =
        some (data.data.toList, remaining) ∧ remaining.length < 8 := by
    unfold deflateRawL8P deflateRawL8TokensP
    rw [chooseSplitsHeuristicPUPacked_lzMatchP_eq]
    unfold deflateRawSplitTierP
    exact hwithObs 8 8 _ rfl
  have hl9 : ∃ remaining,
      Deflate.Spec.decode.goR
          (Deflate.Spec.bytesToBits (deflateRawL9P data)) [] =
        some (data.data.toList, remaining) ∧ remaining.length < 8 := by
    unfold deflateRawL9P deflateRawL9TokensP
    dsimp only []
    split <;>
      first
      | exact emitSmallerBy_bytesToBits
          (P := fun bits => ∃ remaining,
            Deflate.Spec.decode.goR bits [] = some (data.data.toList, remaining) ∧
              remaining.length < 8)
          _ _ _ _ (hbase 9)
          (deflateDynamicBlocksOptimalFast_goR_pad data sharedTokChunk)
      | exact emitSmallerBy_bytesToBits
          (P := fun bits => ∃ remaining,
            Deflate.Spec.decode.goR bits [] = some (data.data.toList, remaining) ∧
              remaining.length < 8)
          _ _ _ _ (hbase 9)
          (deflateDynamicBlocksOptimalWindowedFast_goR_pad data sharedTokChunk)
  have hl10 : ∃ remaining,
      Deflate.Spec.decode.goR
          (Deflate.Spec.bytesToBits (deflateRawL10P data)) [] =
        some (data.data.toList, remaining) ∧ remaining.length < 8 := by
    unfold deflateRawL10P deflateRawL10TokensP
    dsimp only []
    split <;>
      first
      | exact emitSmallerBy_bytesToBits
          (P := fun bits => ∃ remaining,
            Deflate.Spec.decode.goR bits [] = some (data.data.toList, remaining) ∧
              remaining.length < 8)
          _ _ _ _ (hbase 10)
          (deflateDynamicBlocksOptimal_goR_pad data sharedTokChunk)
      | exact emitSmallerBy_bytesToBits
          (P := fun bits => ∃ remaining,
            Deflate.Spec.decode.goR bits [] = some (data.data.toList, remaining) ∧
              remaining.length < 8)
          _ _ _ _ (hbase 10)
          (deflateDynamicBlocksOptimalWindowed_goR_pad data sharedTokChunk)
  have hadaptive : ∃ remaining,
      Deflate.Spec.decode.goR
          (Deflate.Spec.bytesToBits
            (deflateRawL9AdaptiveP data (l7ProfileFor data))) [] =
        some (data.data.toList, remaining) ∧ remaining.length < 8 := by
    unfold deflateRawL9AdaptiveP deflateRawL9RouteP
    split
    · exact hl9
    · exact hl8
    · exact hl10
  split
  · -- Level 0: stored blocks — byte-aligned, remaining = []
    exact hstored
  -- The incompressible pre-scan routes to the same stored block.
  · split
    · exact hstored
    · split
      · split
        · exact hl5
        · split
          · exact hl6
          · split
            · exact hl7
            · split
              · split
                · exact hadaptive
                · exact hl9
              · split
                · -- level ≥ 10: exact-DP crown, sized floor.
                  unfold deflateRawL10TokensP
                  dsimp only []
                  split <;>
                    first
                    | exact emitSmallerBy_bytesToBits
                        (P := fun bits => ∃ remaining,
                          Deflate.Spec.decode.goR bits [] =
                            some (data.data.toList, remaining) ∧ remaining.length < 8)
                        _ _ _ _ (hbase _)
                        (deflateDynamicBlocksOptimal_goR_pad data sharedTokChunk)
                    | exact emitSmallerBy_bytesToBits
                        (P := fun bits => ∃ remaining,
                          Deflate.Spec.decode.goR bits [] =
                            some (data.data.toList, remaining) ∧ remaining.length < 8)
                        _ _ _ _ (hbase _)
                        (deflateDynamicBlocksOptimalWindowed_goR_pad data sharedTokChunk)
                · split
                  · -- level 8: exact named source point used by adaptive L9.
                    have hlevel : level = 8 := by
                      simpa only [beq_iff_eq] using
                        (show (level == 8) = true by assumption)
                    subst level
                    exact hl8
                  · change ∃ remaining,
                      Deflate.Spec.decode.goR
                          (Deflate.Spec.bytesToBits
                            (deflateRawSplitLevelP data level)) [] =
                        some (data.data.toList, remaining) ∧ remaining.length < 8
                    exact hsplitLevel level
      · split
        · exact hl2
        · split
          · exact hl3
          · split
            · exact hl4
            · exact hgreedyLevel level (by assumption)

/-- The encoder always produces exactly one valid raw-DEFLATE stream for its
    input, as judged by the independent formal bitstream specification. -/
theorem isValidStreamFor_deflateRaw (data : ByteArray) (level : UInt8) :
    Deflate.Spec.IsValidStreamFor (deflateRaw data level) data :=
  deflateRaw_goR_pad data level

/-- The encoder always produces a valid raw-DEFLATE stream. -/
theorem isValidStream_deflateRaw (data : ByteArray) (level : UInt8) :
    Deflate.Spec.IsValidStream (deflateRaw data level) :=
  ⟨data, isValidStreamFor_deflateRaw data level⟩

end Zip.Native.Deflate
