import Zip.Spec.LZ77ChainCorrect
import Zip.Spec.LZ77ChainLazyCorrect
import Zip.Spec.LZ77MergedCorrect
import Zip.Spec.EmitPackedCorrect
import Zip.Native.DeflateDynamic

/-!
# Correctness of the packed-token matcher twins (Wave 3b stage A)

`lz77ChainIterP`/`lz77ChainLazyIterP` are the iterative matchers with a
`packTok`-encoded `Array UInt32` accumulator in place of the boxed
`Array LZ77Token`. This file proves the boxed view recovers the boxed
matchers exactly:

    (lz77ChainIterP data mc ws ic).map unpackTok = lz77ChainIter data mc ws ic

(and the lazy twin, and the `lzMatch`/`lzMatchP` dispatch pair).

The proof goes through the *pack* direction first: a lockstep accumulator
induction (the `mainLoop_eq_chain` shape) shows each packed loop equals
`(·.map packTok)` of its boxed twin — every push site is literally
`packTok` of the boxed push, so `Array.map_push` commutes the map through
each push with **no** side conditions, and the chain state never enters the
argument. The `unpackTok` view theorems then follow by composing with
`unpackTok_packTok`, whose encodability hypotheses (`3 ≤ len ≤ 258`,
`1 ≤ dist ≤ 32768`) are discharged *wholesale* by the existing
`lz77ChainIter_encodable`/`lz77ChainLazyIter_encodable` theorems — no replay
of the `chainWalk_spec` emission-guard analysis is needed.
-/

namespace Zip.Native.Deflate

open Zip.Native.Deflate (lz77ChainIter lz77ChainLazyIter lz77ChainIterP lz77ChainLazyIterP)

/-! ## Pack direction: lockstep accumulator inductions -/

/-- `trailingP` is the packed image of the boxed trailing-literals loop. -/
private theorem trailingP_eq (data : ByteArray) (pos : Nat) (acc : Array LZ77Token) :
    trailingP data pos (acc.map packTok) =
      (lz77GreedyIter.trailing data pos acc).map packTok := by
  induction h : data.size - pos using Nat.strongRecOn generalizing pos acc with
  | _ n ih =>
    unfold trailingP lz77GreedyIter.trailing
    by_cases hp : pos < data.size
    · simp only [hp, ↓reduceDIte]
      rw [← Array.map_push, ih _ (by omega) _ _ rfl]
    · simp only [hp, ↓reduceDIte]

/-- The packed greedy `mainLoop` is the packed image of the boxed one:
    identical control flow and chain state, `packTok` at each push. -/
private theorem mainLoopP_eq (data : ByteArray) (windowSize hashSize maxChain insertCap niceLen : Nat)
    (hashTable : Array Nat) (prev : Array Nat) (pos : Nat) (acc : Array LZ77Token) :
    lz77ChainIterP.mainLoop data windowSize hashSize maxChain insertCap niceLen hashTable prev pos
        (acc.map packTok) =
      (lz77ChainIter.mainLoop data windowSize hashSize maxChain insertCap niceLen hashTable prev pos
        acc).map packTok := by
  induction h : data.size - pos using Nat.strongRecOn generalizing pos acc hashTable prev with
  | _ n ih =>
    unfold lz77ChainIterP.mainLoop lz77ChainIter.mainLoop
    simp only [chainWalkGuardedPackedU_eq]
    by_cases hlt : pos + 2 < data.size
    · simp only [hlt, ↓reduceDIte]
      split
      · split
        · rw [← Array.map_push, ih _ (by omega) _ _ _ _ rfl]
        · rw [← Array.map_push, ih _ (by omega) _ _ _ _ rfl]
      · rw [← Array.map_push, ih _ (by omega) _ _ _ _ rfl]
    · simp only [hlt, ↓reduceDIte]
      exact trailingP_eq data pos acc

/-- `lz77ChainIterP` produces exactly the `packTok` image of `lz77ChainIter`. -/
theorem lz77ChainIterP_eq (data : ByteArray) (maxChain windowSize insertCap niceLen : Nat) :
    lz77ChainIterP data maxChain windowSize insertCap niceLen =
      (lz77ChainIter data maxChain windowSize insertCap niceLen).map packTok := by
  unfold lz77ChainIterP lz77ChainIter
  split
  · simpa only [List.map_toArray, List.map_nil] using trailingP_eq data 0 #[]
  · simpa only [List.map_toArray, List.map_nil, Array.emptyWithCapacity_eq] using
      mainLoopP_eq data windowSize 65536 maxChain insertCap niceLen _ _ 0 #[]

set_option backward.split false in
set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
mutual

/-- Packed image of `lz77ChainLazyIter.rollDefer`: the packed rolling deferral is
    `(·.map packTok)` of the boxed-token one. Mutual with `mainLoopLazyP_eq` (rung 4
    of #2837): the roll arm recurses at `mp+1`, the commit arms re-enter `mainLoop`.
    The `USize` re-probe aligns to its `Nat` twin via `chainWalkGuardedPackedU_eq`,
    so both sides land on the same walk; `Array.map_push` commutes `packTok` through
    each push. -/
private theorem rollDefer_P_eq (data : ByteArray) (windowSize hashSize maxChain insertCap goodMatch niceLen lazyDepth lazy2Steps : Nat) (useH3 : Bool)
    (hashTable : Array Nat) (prev h3tab : Array Nat) (mp pLen pMatchPos step : Nat) (acc : Array LZ77Token) :
    lz77ChainLazyIterP.rollDefer data windowSize hashSize maxChain insertCap goodMatch niceLen lazyDepth lazy2Steps useH3 hashTable prev h3tab mp pLen pMatchPos step
        (acc.map packTok) =
      (lz77ChainLazyIter.rollDefer data windowSize hashSize maxChain insertCap goodMatch niceLen lazyDepth lazy2Steps useH3 hashTable prev h3tab mp pLen pMatchPos step
        acc).map packTok := by
  unfold lz77ChainLazyIterP.rollDefer lz77ChainLazyIter.rollDefer
  by_cases hcan : step < lazy2Steps ∧ mp + 3 < data.size ∧ pLen < goodMatch
  · rw [dif_pos hcan, dif_pos hcan]
    simp (config := { maxSteps := 4000000 }) only [chainWalkGuardedPackedU_eq]
    split
    · -- roll: literal at mp, then rollDefer at mp+1
      simp only [← Array.map_push]
      rw [rollDefer_P_eq]
    · -- no improvement: commit reference(pLen), then mainLoop
      simp only [← Array.map_push]
      rw [mainLoopLazyP_eq]
  · rw [dif_neg hcan, dif_neg hcan]
    simp only [← Array.map_push]
    rw [mainLoopLazyP_eq]
termination_by 2 * (data.size - mp) + 1
decreasing_by all_goals omega

/-- The packed lazy `mainLoop` is the packed image of the boxed one, generalized to
    *all* `lazy2Steps` (rung 4 of #2837): the live rolling dispatch is threaded
    through the walk-decode via the mutual `rollDefer_P_eq`. The gate
    (`matchLen < goodMatch`) is applied identically in both, so the branch tree stays
    in lockstep. `set_option backward.split false` keeps the `split` on the
    `rollDefer`-live goal from blowing its motive (the rung-3 fix). -/
private theorem mainLoopLazyP_eq (data : ByteArray) (windowSize hashSize maxChain insertCap goodMatch niceLen lazyDepth lazy2Steps : Nat) (useH3 : Bool)
    (hashTable : Array Nat) (prev h3tab : Array Nat) (pos : Nat) (acc : Array LZ77Token) :
    lz77ChainLazyIterP.mainLoop data windowSize hashSize maxChain insertCap goodMatch niceLen lazyDepth lazy2Steps useH3 hashTable prev h3tab pos
        (acc.map packTok) =
      (lz77ChainLazyIter.mainLoop data windowSize hashSize maxChain insertCap goodMatch niceLen lazyDepth lazy2Steps useH3 hashTable prev h3tab pos
        acc).map packTok := by
  unfold lz77ChainLazyIterP.mainLoop lz77ChainLazyIter.mainLoop
  by_cases hlt : pos + 2 < data.size
  · -- Reduce the outer dite with `zeta := false`, abstract the opaque hash3 terms,
    -- then align the `USize` walk to its `Nat` twin (`chainWalkGuardedPackedU_eq`).
    simp (config := { zeta := false }) only [hlt, ↓reduceDIte]
    generalize h3Seed useH3 data h3tab windowSize pos hlt = sd
    generalize hash3Single data pos hlt = hsg
    simp (config := { maxSteps := 4000000 }) only [chainWalkGuardedPackedU_eq]
    -- Branch tree: hge / hle / h3lt / gate / lazyAccept / hle2 / h1 (rung 5: no hpl2)
    split
    · split
      · split
        · split
          · split
            · split
              · split
                · -- roll arm: literal push, then rollDefer
                  rw [← Array.map_push, rollDefer_P_eq]
                · -- ¬h1: single deferral, two pushes
                  rw [← Array.map_push, ← Array.map_push, mainLoopLazyP_eq]
              · -- ¬hle2: reference(matchLen)
                rw [← Array.map_push, mainLoopLazyP_eq]
            · -- ¬lazyAccept: reference(matchLen)
              rw [← Array.map_push, mainLoopLazyP_eq]
          · -- gated: reference(matchLen)
            rw [← Array.map_push, mainLoopLazyP_eq]
        · -- ¬h3lt: reference(matchLen)
          rw [← Array.map_push, mainLoopLazyP_eq]
      · -- ¬hle: literal
        rw [← Array.map_push, mainLoopLazyP_eq]
    · -- ¬hge: literal
      rw [← Array.map_push, mainLoopLazyP_eq]
  · simp only [hlt, ↓reduceDIte]
    exact trailingP_eq data pos acc
termination_by 2 * (data.size - pos)
decreasing_by all_goals (first | omega | (refine Nat.mul_lt_mul_of_pos_left ?_ (by decide); omega))

end

/-- `lz77ChainLazyIterP` produces exactly the `packTok` image of
    `lz77ChainLazyIter`. -/
theorem lz77ChainLazyIterP_eq (data : ByteArray) (maxChain windowSize insertCap goodMatch niceLen lazyDepth : Nat) (useH3 : Bool) (lazy2Steps : Nat) :
    lz77ChainLazyIterP data maxChain windowSize insertCap goodMatch niceLen lazyDepth useH3 lazy2Steps =
      (lz77ChainLazyIter data maxChain windowSize insertCap goodMatch niceLen lazyDepth useH3 lazy2Steps).map packTok := by
  unfold lz77ChainLazyIterP lz77ChainLazyIter
  split
  · simpa only [List.map_toArray, List.map_nil] using trailingP_eq data 0 #[]
  · simpa only [List.map_toArray, List.map_nil, Array.emptyWithCapacity_eq] using
      mainLoopLazyP_eq data windowSize 65536 maxChain insertCap goodMatch niceLen lazyDepth lazy2Steps useH3 _ _ _ 0 #[]

/-! ## View direction: the boxed view recovers the boxed matchers

`unpackTok_packTok` needs the encoder bounds on each token, which the
existing encodability theorems provide for the whole stream. -/

/-- The boxed view of the packed greedy matcher is the boxed greedy matcher. -/
theorem lz77ChainIterP_map (data : ByteArray) (maxChain windowSize insertCap niceLen : Nat)
    (hw : windowSize > 0) (hws : windowSize ≤ 32768) :
    (lz77ChainIterP data maxChain windowSize insertCap niceLen).map unpackTok =
      lz77ChainIter data maxChain windowSize insertCap niceLen := by
  have henc := lz77ChainIter_encodable data maxChain windowSize insertCap niceLen hw hws
  rw [lz77ChainIterP_eq, Array.map_map]
  have hcongr : Array.map (unpackTok ∘ packTok) (lz77ChainIter data maxChain windowSize insertCap niceLen) =
      Array.map id (lz77ChainIter data maxChain windowSize insertCap niceLen) :=
    Array.map_congr_left fun t ht => unpackTok_packTok t (henc t (by simpa only [Array.mem_toList_iff] using ht))
  rw [hcongr, Array.map_id]

/-- The boxed view of the packed lazy matcher is the boxed lazy matcher. -/
theorem lz77ChainLazyIterP_map (data : ByteArray) (maxChain windowSize insertCap goodMatch niceLen lazyDepth : Nat) (useH3 : Bool) (lazy2Steps : Nat)
    (hw : windowSize > 0) (hws : windowSize ≤ 32768) :
    (lz77ChainLazyIterP data maxChain windowSize insertCap goodMatch niceLen lazyDepth useH3 lazy2Steps).map unpackTok =
      lz77ChainLazyIter data maxChain windowSize insertCap goodMatch niceLen lazyDepth useH3 lazy2Steps := by
  have henc := lz77ChainLazyIter_encodable data maxChain windowSize insertCap goodMatch niceLen lazyDepth useH3 lazy2Steps hw hws
  rw [lz77ChainLazyIterP_eq, Array.map_map]
  have hcongr : Array.map (unpackTok ∘ packTok)
        (lz77ChainLazyIter data maxChain windowSize insertCap goodMatch niceLen lazyDepth useH3 lazy2Steps) =
      Array.map id (lz77ChainLazyIter data maxChain windowSize insertCap goodMatch niceLen lazyDepth useH3 lazy2Steps) :=
    Array.map_congr_left fun t ht => unpackTok_packTok t (henc t (by simpa only [Array.mem_toList_iff] using ht))
  rw [hcongr, Array.map_id]

/-! ## Dispatch boundary -/

/-- `lzMatchP` is the `packTok` image of `lzMatch` at every level. -/
theorem lzMatchP_eq (data : ByteArray) (level : UInt8) :
    lzMatchP data level = (lzMatch data level).map packTok := by
  unfold lzMatchP lzMatch
  split
  · rw [lz77ChainLazyIterPMerged_eq]
    exact lz77ChainLazyIterP_eq data (chainDepth level) 32768 (insertCap level) (goodMatch level) (niceLen level) (lazyDepth level) (useH3For data level) (lazy2StepsLevel level)
  · rw [lz77ChainIterPMerged_eq]
    exact lz77ChainIterP_eq data (chainDepth level) 32768 (insertCap level) (niceLen level)

/-- The boxed view of the packed token stream is exactly `lzMatch`'s stream:
    stage B+ consumers of `lzMatchP` inherit every `lzMatch` contract through
    this equation. -/
theorem lzMatchP_map (data : ByteArray) (level : UInt8) :
    (lzMatchP data level).map unpackTok = lzMatch data level := by
  unfold lzMatchP lzMatch
  split
  · rw [lz77ChainLazyIterPMerged_eq]
    exact lz77ChainLazyIterP_map data (chainDepth level) 32768 (insertCap level) (goodMatch level) (niceLen level) (lazyDepth level) (useH3For data level) (lazy2StepsLevel level)
      (by omega) (by omega)
  · rw [lz77ChainIterPMerged_eq]
    exact lz77ChainIterP_map data (chainDepth level) 32768 (insertCap level) (niceLen level)
      (by omega) (by omega)

/-! ## Stages B+C: the packed base candidate equals the boxed one

`deflateRawBase` is now *defined* as `deflateRawBaseP data (lzMatchP data
level)` (packed frequency pass *and* packed emit — no unpack anywhere on
the base path). The equation below recovers the boxed formulation — same
statement as the old definitional `deflateRawBase_def`, now proven from
`tokenFreqsP_eq` (the packed histogram is the boxed one over the
`unpackTok` view), the stage-C packed-emitter equalities
(`deflateFixedBlockP_eq`/`deflateDynamicBlockCoreP_eq`,
`Zip/Spec/EmitPackedCorrect.lean`) and `lzMatchP_map` (the view of the
packed stream is `lzMatch`). The three `deflateRawBase` spec lemmas in
`Zip/Spec/DeflateRoundtrip.lean` keep their statements and rewrite through
this equation. -/

/-- The boxed base dispatch over `lzMatch` is the (packed-pipeline)
    `deflateRawBase`. -/
theorem deflateRawBase_def (data : ByteArray) (level : UInt8) :
    deflateRawBaseTokens data (lzMatch data level) = deflateRawBase data level := by
  unfold deflateRawBase deflateRawBaseP deflateRawBaseTokens
  -- The packed dispatch shares one `dynHeaderCodes` plan across sizing and emit
  -- (#2627); collapse the plan-taking variants back to the un-deduped forms, then
  -- finish with the boxed/packed emitter and frequency equalities.
  simp only [dynBlockBytesWith_dynHeaderCodes, deflateDynamicBlockCorePWith_dynHeaderCodes,
    deflateFixedBlockP_eq, deflateDynamicBlockCoreP_eq, tokenFreqsP_eq, lzMatchP_map]

/-! ## The packed shared-window split candidate equals the boxed one (#2737)

`deflateDynamicBlocksSharedAtP` is the observation-divergence split candidate
on packed tokens end-to-end: per block, `tokenFreqsP` for the trees and
`emitTokensWithCodesP` (inside `emitDynBlockP`) for the emit. The equalities
below recover the boxed reference
`deflateDynamicBlocksSharedAtTokens … (fun _ => cuts)` for **every** word
array and **every** cut list, so the whole `deflateDynamicBlocksSharedAt`
spec quadruple (`Zip/Spec/DeflateBlockSplit.lean`, quantified over an
arbitrary selector) transfers by a rewrite — the packed heuristic
`chooseSplitsHeuristicP` never appears in a proof. -/

/-- The packed observation class is the boxed one over the `unpackTok` view —
    unconditionally, for every word: both sides read exactly `unpackTok`'s
    field expressions (`toUInt8` for literals, `(w >>> 16) &&& 0x7FFF` for the
    match length), so the heuristic's bit tricks can never drift from the
    packed-token layout. The `chooseSplitsHeuristicP` conformance test
    (`ZipTest/PackedTokens.lean`) checks the full loop; this pins the
    per-token classification. -/
theorem splitTokenClassP_eq (w : UInt32) :
    splitTokenClassP w = splitTokenClass (unpackTok w) := by
  unfold splitTokenClassP splitTokenClass unpackTok
  split <;> rfl

/-- The packed per-token output-byte count is the boxed one over the
    `unpackTok` view — unconditionally, for every word. -/
theorem splitTokenBytesP_eq (w : UInt32) :
    splitTokenBytesP w = splitTokenBytes (unpackTok w) := by
  unfold splitTokenBytesP splitTokenBytes unpackTok
  split <;> rfl

/-- `Array.extract` commutes with `Array.map` (no core lemma at this
    toolchain): the group a packed emitter cuts out of the packed stream views
    to the group the boxed emitter cuts out of the boxed stream. -/
private theorem extract_map {α β : Type} (f : α → β) (a : Array α) (s e : Nat) :
    (a.map f).extract s e = (a.extract s e).map f := by
  ext i hi₁ hi₂
  · simp only [Array.size_extract, Array.size_map]
  · simp only [Array.getElem_extract, Array.getElem_map]

/-- The packed per-block emitter is the boxed one over the `unpackTok` view:
    the bodies are identical up to `emitTokensWithCodesP_eq`. -/
theorem emitDynBlockP_eq (bw : BitWriter) (data : ByteArray) (ws : Array UInt32)
    (litLens distLens : List Nat)
    (hlit : litLens.length = 286) (hdist : distLens.length = 30) (isFinal : Bool) :
    emitDynBlockP bw data ws litLens distLens hlit hdist isFinal =
      emitDynBlock bw data (ws.map unpackTok) litLens distLens hlit hdist isFinal := by
  unfold emitDynBlockP emitDynBlock
  simp only [emitTokensWithCodesPTG_eq, emitTokensWithCodesPT_eq, emitTokensWithCodesP_eq]

/-- The packed shared-window block emitter is the boxed one over the
    `unpackTok` view: the trees agree by `tokenFreqsP_eq`, the emit by
    `emitDynBlockP_eq`. -/
theorem emitSharedBlockP_eq (bw : BitWriter) (data : ByteArray) (ws : Array UInt32)
    (isFinal : Bool) :
    emitSharedBlockP bw data ws isFinal =
      emitSharedBlock bw data (ws.map unpackTok) isFinal := by
  unfold emitSharedBlockP emitSharedBlock
  simp only [tokenFreqsP_eq, emitDynBlockP_eq]

/-- The packed cut-list block fold is the boxed one over the `unpackTok` view
    (fuel-quantified form for the induction): the map preserves size, so the
    clamped cuts coincide, and each block agrees by `emitSharedBlockP_eq` +
    `extract_map`. -/
private theorem emitSharedBlocksAtP_eq_fuel (data : ByteArray) (ws : Array UInt32) :
    ∀ (fuel pos : Nat), ws.size - pos < fuel → ∀ (cuts : List Nat) (bw : BitWriter),
      emitSharedBlocksAtP data ws cuts pos bw =
        emitSharedBlocksAt data (ws.map unpackTok) cuts pos bw := by
  intro fuel
  induction fuel with
  | zero => intro pos hf; omega
  | succ fuel ih =>
    intro pos hf cuts bw
    conv => lhs; unfold emitSharedBlocksAtP
    conv => rhs; unfold emitSharedBlocksAt
    simp only [Array.size_map, emitSharedBlockP_eq, extract_map]
    by_cases hend : min (max (cuts.headD ws.size) (pos + 1)) ws.size ≥ ws.size
    · simp only [if_pos hend]
    · simp only [if_neg hend]
      exact ih (min (max (cuts.headD ws.size) (pos + 1)) ws.size) (by omega) cuts.tail _

/-- The packed cut-list block fold is the boxed one over the `unpackTok` view,
    for any cut list and start position. -/
theorem emitSharedBlocksAtP_eq (data : ByteArray) (ws : Array UInt32)
    (cuts : List Nat) (pos : Nat) (bw : BitWriter) :
    emitSharedBlocksAtP data ws cuts pos bw =
      emitSharedBlocksAt data (ws.map unpackTok) cuts pos bw :=
  emitSharedBlocksAtP_eq_fuel data ws (ws.size - pos + 1) pos (by omega) cuts bw

/-- The packed observation-divergence split candidate is byte-identical to the
    boxed reference at the same (constant) cut list: `deflateRaw`'s level 6–8
    split branch and the roundtrip proofs see
    `deflateDynamicBlocksSharedAtTokens … (fun _ => cuts)` through this
    rewrite, and the `DeflateBlockSplit` theorems hold for any selector. -/
theorem deflateDynamicBlocksSharedAtP_eq (data : ByteArray) (ws : Array UInt32)
    (cuts : List Nat) :
    deflateDynamicBlocksSharedAtP data ws cuts =
      deflateDynamicBlocksSharedAtTokens data (ws.map unpackTok) (fun _ => cuts) := by
  unfold deflateDynamicBlocksSharedAtP deflateDynamicBlocksSharedAtTokens
  split
  · rfl
  · rw [emitSharedBlocksAtP_eq]

/-! ## The packed sized-tree split candidate reuses trees (Wave 5 → #2753)

`emitSharedBlocksAtSizedP`, fed the trees `sharedPartitionSizedP` builds while
sizing, emits byte-for-byte what `emitSharedBlocksAtP` emits recomputing them —
the packed twin of `emitSharedBlocksAtSized_eq`. Each block's trees are
`sizedTrees (tokenFreqsP group) = dynamicCodeLengths (tokenFreqsP group)`, which
is exactly what `emitSharedBlockP` recomputes; the `emitDynBlockP` calls then
coincide (the alphabet-size proofs are proof-irrelevant). -/

/-- Fed the sizing pass's trees, the tree-taking packed emitter equals the
    reference packed emitter (fuel-quantified form for the induction). -/
private theorem emitSharedBlocksAtSizedP_eq_fuel (data : ByteArray) (ws : Array UInt32) :
    ∀ (fuel pos : Nat), ws.size - pos < fuel → ∀ (cuts : List Nat) (bw : BitWriter),
      emitSharedBlocksAtSizedP data ws cuts (sharedPartitionSizedP ws cuts pos).2 pos bw
        = emitSharedBlocksAtP data ws cuts pos bw := by
  intro fuel
  induction fuel with
  | zero => intro pos hf; omega
  | succ fuel ih =>
    intro pos hf cuts bw
    by_cases hend : min (max (cuts.headD ws.size) (pos + 1)) ws.size ≥ ws.size
    · have hsnd : (sharedPartitionSizedP ws cuts pos).2 =
          [sizedTrees (tokenFreqsP (ws.extract pos
            (min (max (cuts.headD ws.size) (pos + 1)) ws.size))).1
            (tokenFreqsP (ws.extract pos
            (min (max (cuts.headD ws.size) (pos + 1)) ws.size))).2] := by
        conv => lhs; unfold sharedPartitionSizedP
        simp only [if_pos hend]
      rw [hsnd]
      conv => lhs; unfold emitSharedBlocksAtSizedP
      conv => rhs; unfold emitSharedBlocksAtP
      simp only [if_pos hend, List.headD_cons, emitSharedBlockP, sizedTrees]
    · have hsnd : (sharedPartitionSizedP ws cuts pos).2 =
          sizedTrees (tokenFreqsP (ws.extract pos
            (min (max (cuts.headD ws.size) (pos + 1)) ws.size))).1
            (tokenFreqsP (ws.extract pos
            (min (max (cuts.headD ws.size) (pos + 1)) ws.size))).2 ::
          (sharedPartitionSizedP ws cuts.tail
            (min (max (cuts.headD ws.size) (pos + 1)) ws.size)).2 := by
        conv => lhs; unfold sharedPartitionSizedP
        simp only [if_neg hend]
      rw [hsnd]
      conv => lhs; unfold emitSharedBlocksAtSizedP
      conv => rhs; unfold emitSharedBlocksAtP
      simp only [if_neg hend, List.headD_cons, List.tail_cons, emitSharedBlockP, sizedTrees]
      exact ih (min (max (cuts.headD ws.size) (pos + 1)) ws.size) (by omega) cuts.tail _

/-- Fed the sizing pass's trees, the tree-taking packed emitter equals the
    reference packed emitter, for any cut list and start position. -/
theorem emitSharedBlocksAtSizedP_eq (data : ByteArray) (ws : Array UInt32)
    (cuts : List Nat) (pos : Nat) (bw : BitWriter) :
    emitSharedBlocksAtSizedP data ws cuts (sharedPartitionSizedP ws cuts pos).2 pos bw
      = emitSharedBlocksAtP data ws cuts pos bw :=
  emitSharedBlocksAtSizedP_eq_fuel data ws (ws.size - pos + 1) pos (by omega) cuts bw

/-- The packed sized-tree split candidate's emit thunk is byte-identical to the
    reference `deflateDynamicBlocksSharedAtP`: the roundtrip and padding theorems
    transfer through this, exactly as for the un-sized packed candidate. -/
theorem deflateDynamicBlocksSharedAtSizedP_emit (data : ByteArray) (ws : Array UInt32)
    (cuts : List Nat) :
    (deflateDynamicBlocksSharedAtSizedP data ws cuts).2 () =
      deflateDynamicBlocksSharedAtP data ws cuts := by
  unfold deflateDynamicBlocksSharedAtSizedP
  split
  · rfl
  · rename_i h
    show (emitSharedBlocksAtSizedP data ws cuts (sharedPartitionSizedP ws cuts 0).2 0
      BitWriter.empty).flush = deflateDynamicBlocksSharedAtP data ws cuts
    rw [emitSharedBlocksAtSizedP_eq]
    unfold deflateDynamicBlocksSharedAtP
    rw [if_neg h]

end Zip.Native.Deflate
