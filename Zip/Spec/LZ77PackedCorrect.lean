import Zip.Spec.LZ77ChainCorrect
import Zip.Spec.LZ77ChainLazyCorrect
import Zip.Spec.EmitPackedCorrect
import Zip.Spec.HtMatchCorrect
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

/-- The packed lazy `mainLoop` is the packed image of the boxed one. The gate
    (`matchLen < goodMatch`) is applied identically in both, so the branch tree
    stays in lockstep — one extra split versus the ungated proof. -/
private theorem mainLoopLazyP_eq (data : ByteArray) (windowSize hashSize maxChain insertCap goodMatch niceLen : Nat)
    (hashTable : Array Nat) (prev : Array Nat) (pos : Nat) (acc : Array LZ77Token) :
    lz77ChainLazyIterP.mainLoop data windowSize hashSize maxChain insertCap goodMatch niceLen hashTable prev pos
        (acc.map packTok) =
      (lz77ChainLazyIter.mainLoop data windowSize hashSize maxChain insertCap goodMatch niceLen hashTable prev pos
        acc).map packTok := by
  induction h : data.size - pos using Nat.strongRecOn generalizing pos acc hashTable prev with
  | _ n ih =>
    unfold lz77ChainLazyIterP.mainLoop lz77ChainLazyIter.mainLoop
    by_cases hlt : pos + 2 < data.size
    · simp only [hlt, ↓reduceDIte]
      -- Branch tree: hge / hle / h3lt / gate / deferral / hle2
      split
      · split
        · split
          · split
            · split
              · split
                · -- deferral arm: literal + reference, two pushes
                  rw [← Array.map_push, ← Array.map_push, ih _ (by omega) _ _ _ _ rfl]
                · rw [← Array.map_push, ih _ (by omega) _ _ _ _ rfl]
              · rw [← Array.map_push, ih _ (by omega) _ _ _ _ rfl]
            · -- gated: reference(matchLen)
              rw [← Array.map_push, ih _ (by omega) _ _ _ _ rfl]
          · rw [← Array.map_push, ih _ (by omega) _ _ _ _ rfl]
        · rw [← Array.map_push, ih _ (by omega) _ _ _ _ rfl]
      · rw [← Array.map_push, ih _ (by omega) _ _ _ _ rfl]
    · simp only [hlt, ↓reduceDIte]
      exact trailingP_eq data pos acc

/-- `lz77ChainLazyIterP` produces exactly the `packTok` image of
    `lz77ChainLazyIter`. -/
theorem lz77ChainLazyIterP_eq (data : ByteArray) (maxChain windowSize insertCap goodMatch niceLen : Nat) :
    lz77ChainLazyIterP data maxChain windowSize insertCap goodMatch niceLen =
      (lz77ChainLazyIter data maxChain windowSize insertCap goodMatch niceLen).map packTok := by
  unfold lz77ChainLazyIterP lz77ChainLazyIter
  split
  · simpa only [List.map_toArray, List.map_nil] using trailingP_eq data 0 #[]
  · simpa only [List.map_toArray, List.map_nil, Array.emptyWithCapacity_eq] using
      mainLoopLazyP_eq data windowSize 65536 maxChain insertCap goodMatch niceLen _ _ 0 #[]

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
theorem lz77ChainLazyIterP_map (data : ByteArray) (maxChain windowSize insertCap goodMatch niceLen : Nat)
    (hw : windowSize > 0) (hws : windowSize ≤ 32768) :
    (lz77ChainLazyIterP data maxChain windowSize insertCap goodMatch niceLen).map unpackTok =
      lz77ChainLazyIter data maxChain windowSize insertCap goodMatch niceLen := by
  have henc := lz77ChainLazyIter_encodable data maxChain windowSize insertCap goodMatch niceLen hw hws
  rw [lz77ChainLazyIterP_eq, Array.map_map]
  have hcongr : Array.map (unpackTok ∘ packTok)
        (lz77ChainLazyIter data maxChain windowSize insertCap goodMatch niceLen) =
      Array.map id (lz77ChainLazyIter data maxChain windowSize insertCap goodMatch niceLen) :=
    Array.map_congr_left fun t ht => unpackTok_packTok t (henc t (by simpa only [Array.mem_toList_iff] using ht))
  rw [hcongr, Array.map_id]

/-! ## Dispatch boundary -/

/-- `lzMatchP` is the `packTok` image of `lzMatch` at every level. -/
theorem lzMatchP_eq (data : ByteArray) (level : UInt8) :
    lzMatchP data level = (lzMatch data level).map packTok := by
  unfold lzMatchP lzMatch
  split
  · exact lz77ChainLazyIterP_eq data (chainDepth level) 32768 (insertCap level) (goodMatch level) (niceLen level)
  · exact lz77ChainIterP_eq data (chainDepth level) 32768 (insertCap level) (niceLen level)

/-- The boxed view of the packed token stream is exactly `lzMatch`'s stream:
    stage B+ consumers of `lzMatchP` inherit every `lzMatch` contract through
    this equation. -/
theorem lzMatchP_map (data : ByteArray) (level : UInt8) :
    (lzMatchP data level).map unpackTok = lzMatch data level := by
  unfold lzMatchP lzMatch
  split
  · exact lz77ChainLazyIterP_map data (chainDepth level) 32768 (insertCap level) (goodMatch level) (niceLen level)
      (by omega) (by omega)
  · exact lz77ChainIterP_map data (chainDepth level) 32768 (insertCap level) (niceLen level)
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

end Zip.Native.Deflate
