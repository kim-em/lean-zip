import Zip.Native.DeflateFreqsFused
import Zip.Spec.DeflateFreqsAdditive

/-!
# Correctness of the fused greedy matcher

`lz77GreedyMergedLoopF` (`Zip.Native.DeflateFreqsFused`) threads the two
frequency histograms alongside the token accumulator, bumping at each push site.
This file proves it computes exactly the plain matcher's tokens *and* their
`tokenFreqsP` histogram in one pass:

    lz77ChainIterPMergedF data mc ws ic nl
      = (lz77ChainIterPMerged data mc ws ic nl,
         tokenFreqsP (lz77ChainIterPMerged data mc ws ic nl))            (`lz77ChainIterPMergedF_eq`)

Both loops now accumulate the same `TokenArray` (stage 4/7 of the token-stream
unboxing), so the loop invariant is `(litF, distF) = tokenFreqsP acc.toArray`:
seeded like `tokenFreqsP` (EOB pre-counted), each `TokenArray.push` keeps the
running histogram equal to `tokenFreqsP` of the `.toArray` view of the running
accumulator. The per-step correspondence (`bump* = tokenFreqsP (acc.push w)`)
stays stated over the `Array UInt32` boxed model — proved element-wise from
`tokenFreqsP_lit`/`tokenFreqsP_dist` and the single-element additivity of
`litDeltaP`/`distDeltaP` (`Zip/Spec/DeflateFreqsAdditive.lean`, unchanged) — and
is bridged to each `TokenArray.push` by `TokenArray.push_toArray`. Because the
fused loop and `lz77GreedyMergedLoop` run the *same* merged-array chain state and
the *same* `TokenArray` accumulator, their control flow aligns definitionally, so
the loop induction only has to discharge the freq hypotheses at each recursion.
-/

namespace Zip.Native.Deflate

/-- A packed literal token has the tag bit clear. -/
theorem packTok_literal_tag (b : UInt8) :
    packTok (.literal b) &&& ((1 : UInt32) <<< 31) = 0 := by
  simp only [packTok]; bv_decide

/-- A packed reference token has the tag bit set. -/
theorem packTok_reference_tag (len dist : Nat) :
    ¬ (packTok (.reference len dist) &&& ((1 : UInt32) <<< 31) = 0) := by
  simp only [packTok]
  generalize len.toUInt32 = l
  generalize dist.toUInt32 = d
  bv_decide

/-- `acc.push w` as an append, so the `litDeltaP`/`distDeltaP` append lemmas apply. -/
theorem push_eq_append (acc : Array UInt32) (w : UInt32) : acc.push w = acc ++ #[w] := by
  apply Array.ext'
  simp [Array.toList_push]

/-- One trailing element adds exactly its lit/len bump to the running count. -/
theorem litDeltaP_push (acc : Array UInt32) (w : UInt32) (k : Nat) :
    litDeltaP (acc.push w) 0 k = litDeltaP acc 0 k + (if litBumpIdxP w = k then 1 else 0) := by
  rw [push_eq_append, litDeltaP_append acc #[w] 0 k (Nat.zero_le _)]
  congr 1
  rw [litDeltaP_succ #[w] 0 k (by simp), litDeltaP_of_ge #[w] 1 k (by simp), Nat.add_zero]
  simp

/-- One trailing element adds exactly its distance bump to the running count. -/
theorem distDeltaP_push (acc : Array UInt32) (w : UInt32) (k : Nat) :
    distDeltaP (acc.push w) 0 k =
      distDeltaP acc 0 k +
        (if w &&& ((1 : UInt32) <<< 31) = 0 then 0
         else if codeIdx (distCodeWord ((w &&& 0xFFFF).toNat)) = k then 1 else 0) := by
  rw [push_eq_append, distDeltaP_append acc #[w] 0 k (Nat.zero_le _)]
  congr 1
  rw [distDeltaP_succ #[w] 0 k (by simp), distDeltaP_of_ge #[w] 1 k (by simp), Nat.add_zero]
  simp

/-- **Push-literal correspondence (lit/len).** For a literal word, bumping the
    running lit/len histogram equals `tokenFreqsP` of the extended stream. -/
theorem bumpLitFreqP_push (acc : Array UInt32) (w : UInt32)
    (litF : {a : Array Nat // a.size = 286})
    (hc : w &&& ((1 : UInt32) <<< 31) = 0) (hlit : litF.val = (tokenFreqsP acc).1) :
    (bumpLitFreqP litF w).val = (tokenFreqsP (acc.push w)).1 := by
  have hidx : w.toUInt8.toNat < litF.val.size := by
    have := UInt8.toNat_lt w.toUInt8; rw [litF.property]; omega
  have hbump : litBumpIdxP w = w.toUInt8.toNat := by unfold litBumpIdxP; rw [if_pos hc]
  apply Array.ext
  · simp only [bumpLitFreqP, Array.size_set!]; rw [litF.property, (tokenFreqsP_size (acc.push w)).1]
  · intro k hk _
    simp only [bumpLitFreqP, Array.size_set!, litF.property] at hk
    rw [← getElem!_pos _ k (by simp only [bumpLitFreqP, Array.size_set!, litF.property]; exact hk),
      ← getElem!_pos _ k (by rw [(tokenFreqsP_size (acc.push w)).1]; exact hk)]
    rw [tokenFreqsP_lit (acc.push w) k, litDeltaP_push, ← Nat.add_assoc, ← tokenFreqsP_lit acc k,
      hbump, ← hlit]
    simp only [bumpLitFreqP]
    by_cases hk2 : k = w.toUInt8.toNat
    · subst hk2
      rw [Array.getElem!_set!_self _ _ _ hidx, ← getElem!_pos litF.val _ hidx, if_pos rfl]
    · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hk2), if_neg (fun h => hk2 h.symm), Nat.add_zero]

/-- For a literal word, the distance histogram is unchanged. -/
theorem distFreq_push_lit (acc : Array UInt32) (w : UInt32)
    (distF : {a : Array Nat // a.size = 30})
    (hc : w &&& ((1 : UInt32) <<< 31) = 0) (hdist : distF.val = (tokenFreqsP acc).2) :
    distF.val = (tokenFreqsP (acc.push w)).2 := by
  rw [hdist]
  apply Array.ext
  · rw [(tokenFreqsP_size acc).2, (tokenFreqsP_size (acc.push w)).2]
  · intro k hk _
    rw [(tokenFreqsP_size acc).2] at hk
    rw [← getElem!_pos _ k (by rw [(tokenFreqsP_size acc).2]; exact hk),
      ← getElem!_pos _ k (by rw [(tokenFreqsP_size (acc.push w)).2]; exact hk)]
    rw [tokenFreqsP_dist (acc.push w) k, distDeltaP_push, if_pos hc, Nat.add_zero,
      ← tokenFreqsP_dist acc k]

/-- **Push-reference correspondence (lit/len).** -/
theorem bumpRefLitFreqP_push (acc : Array UInt32) (w : UInt32)
    (litF : {a : Array Nat // a.size = 286})
    (hc : ¬ (w &&& ((1 : UInt32) <<< 31) = 0)) (hlit : litF.val = (tokenFreqsP acc).1) :
    (bumpRefLitFreqP litF w).val = (tokenFreqsP (acc.push w)).1 := by
  obtain ⟨⟨li, le, lv⟩, hli⟩ := Option.isSome_iff_exists.mp
    (findLengthCode_isSome (((w >>> 16) &&& 0x7FFF).toNat))
  have hbnd := nativeFindLengthCode_idx_bound _ _ _ _ hli
  have hcodeeq : codeIdx (lenCodeWord (((w >>> 16) &&& 0x7FFF).toNat)) = li :=
    codeIdx_lenCodeWord _ _ _ _ hli
  have hidx : codeIdx (lenCodeWord (((w >>> 16) &&& 0x7FFF).toNat)) + 257 < litF.val.size := by
    rw [litF.property, hcodeeq]; omega
  have hbump : litBumpIdxP w = codeIdx (lenCodeWord (((w >>> 16) &&& 0x7FFF).toNat)) + 257 := by
    unfold litBumpIdxP; rw [if_neg hc]
  apply Array.ext
  · simp only [bumpRefLitFreqP, Array.size_set!]; rw [litF.property, (tokenFreqsP_size (acc.push w)).1]
  · intro k hk _
    simp only [bumpRefLitFreqP, Array.size_set!, litF.property] at hk
    rw [← getElem!_pos _ k (by simp only [bumpRefLitFreqP, Array.size_set!, litF.property]; exact hk),
      ← getElem!_pos _ k (by rw [(tokenFreqsP_size (acc.push w)).1]; exact hk)]
    rw [tokenFreqsP_lit (acc.push w) k, litDeltaP_push, ← Nat.add_assoc, ← tokenFreqsP_lit acc k,
      hbump, ← hlit]
    simp only [bumpRefLitFreqP]
    by_cases hk2 : k = codeIdx (lenCodeWord (((w >>> 16) &&& 0x7FFF).toNat)) + 257
    · subst hk2
      rw [Array.getElem!_set!_self _ _ _ hidx, ← getElem!_pos litF.val _ hidx, if_pos rfl]
    · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hk2), if_neg (fun h => hk2 h.symm), Nat.add_zero]

/-- **Push-reference correspondence (distance).** -/
theorem bumpRefDistFreqP_push (acc : Array UInt32) (w : UInt32)
    (distF : {a : Array Nat // a.size = 30})
    (hc : ¬ (w &&& ((1 : UInt32) <<< 31) = 0)) (hdist : distF.val = (tokenFreqsP acc).2) :
    (bumpRefDistFreqP distF w).val = (tokenFreqsP (acc.push w)).2 := by
  obtain ⟨⟨di, de, dv⟩, hdi⟩ := Option.isSome_iff_exists.mp
    (findDistCode_isSome ((w &&& 0xFFFF).toNat))
  have hbnd := nativeFindDistCode_idx_bound _ _ _ _ hdi
  have hcodeeq : codeIdx (distCodeWord ((w &&& 0xFFFF).toNat)) = di :=
    codeIdx_distCodeWord _ _ _ _ hdi
  have hidx : codeIdx (distCodeWord ((w &&& 0xFFFF).toNat)) < distF.val.size := by
    rw [distF.property, hcodeeq]; omega
  apply Array.ext
  · simp only [bumpRefDistFreqP, Array.size_set!]; rw [distF.property, (tokenFreqsP_size (acc.push w)).2]
  · intro k hk _
    simp only [bumpRefDistFreqP, Array.size_set!, distF.property] at hk
    rw [← getElem!_pos _ k (by simp only [bumpRefDistFreqP, Array.size_set!, distF.property]; exact hk),
      ← getElem!_pos _ k (by rw [(tokenFreqsP_size (acc.push w)).2]; exact hk)]
    rw [tokenFreqsP_dist (acc.push w) k, distDeltaP_push, if_neg hc, ← tokenFreqsP_dist acc k, ← hdist]
    simp only [bumpRefDistFreqP]
    by_cases hk2 : k = codeIdx (distCodeWord ((w &&& 0xFFFF).toNat))
    · subst hk2
      rw [Array.getElem!_set!_self _ _ _ hidx, ← getElem!_pos distF.val _ hidx, if_pos rfl]
    · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hk2), if_neg (fun h => hk2 h.symm), Nat.add_zero]

/-- `tokenFreqsP` of the empty stream is the seed histogram (lit/len). -/
theorem tokenFreqsP_nil_fst : initLitFreqF.val = (tokenFreqsP (#[] : Array UInt32)).1 := by
  unfold tokenFreqsP tokenFreqsP.go
  rw [dif_neg (by decide)]
  simp only [initLitFreqF]

/-- `tokenFreqsP` of the empty stream is the seed histogram (distance). -/
theorem tokenFreqsP_nil_snd : initDistFreqF.val = (tokenFreqsP (#[] : Array UInt32)).2 := by
  unfold tokenFreqsP tokenFreqsP.go
  rw [dif_neg (by decide)]
  simp only [initDistFreqF]

/-- The fused trailing loop computes the plain `trailingPT` tokens and their
    `tokenFreqsP` (over the `Array UInt32` view of the accumulator), given the
    freq invariant at entry. The accumulator is now a `TokenArray` (stage 4/7);
    the boxed-model `tokenFreqsP` still reads the `.toArray` view, so its every
    `TokenArray.push` matches the boxed `Array.push` the freq lemmas are stated
    over via `TokenArray.push_toArray`. -/
theorem trailingPF_spec (data : ByteArray) (pos : Nat) (acc : TokenArray)
    (litF : {a : Array Nat // a.size = 286}) (distF : {a : Array Nat // a.size = 30})
    (hlit : litF.val = (tokenFreqsP acc.toArray).1) (hdist : distF.val = (tokenFreqsP acc.toArray).2) :
    trailingPF data pos acc litF distF =
      (trailingPT data pos acc,
       ⟨(tokenFreqsP (trailingPT data pos acc).toArray).1, (tokenFreqsP_size _).1⟩,
       ⟨(tokenFreqsP (trailingPT data pos acc).toArray).2, (tokenFreqsP_size _).2⟩) := by
  induction hn : data.size - pos using Nat.strongRecOn generalizing pos acc litF distF with
  | _ n ih =>
    unfold trailingPF trailingPT
    by_cases h : pos < data.size
    · simp only [h, ↓reduceDIte]
      have hc : packTok (.literal data[pos]) &&& ((1 : UInt32) <<< 31) = 0 :=
        packTok_literal_tag _
      refine ih (data.size - (pos + 1)) (by omega) (pos + 1) (acc.push _) _ _ ?_ ?_ rfl
      · rw [TokenArray.push_toArray]; exact bumpLitFreqP_push acc.toArray _ _ hc hlit
      · rw [TokenArray.push_toArray]; exact distFreq_push_lit acc.toArray _ _ hc hdist
    · simp only [h, ↓reduceDIte]
      exact Prod.ext rfl (Prod.ext (Subtype.ext hlit) (Subtype.ext hdist))

/-- The `Array UInt32` view of the greedy `TokenArray` trailing loop is the
    boxed-model `trailingP` on the viewed accumulator (stage 2/7 bridge). Local
    copy of `Zip.Spec.LZ77MergedCorrect.trailingPT_toArray` to avoid importing that
    module's transitive `LZ77ChainCorrect` (a name-clash source) into this file. -/
private theorem trailingPT_toArray (data : ByteArray) (pos : Nat) (acc : TokenArray) :
    (trailingPT data pos acc).toArray = trailingP data pos acc.toArray := by
  induction h : data.size - pos using Nat.strongRecOn generalizing pos acc with
  | _ n ih =>
    unfold trailingPT trailingP
    by_cases hp : pos < data.size
    · simp only [hp, ↓reduceDIte]
      rw [ih _ (by omega) _ _ rfl, TokenArray.push_toArray]
    · simp only [hp, ↓reduceDIte]

/-- The fused greedy loop computes the plain greedy loop's tokens and their
    `tokenFreqsP`, maintaining the invariant `(litF, distF) = tokenFreqsP acc.toArray`.
    Both loops now accumulate the *same* `TokenArray` (stage 4/7 of the
    token-stream unboxing), so their control flow aligns definitionally; the
    boxed-model `tokenFreqsP` reads the `.toArray` view, and each `TokenArray.push`
    matches the boxed `Array.push` the freq lemmas are stated over via
    `TokenArray.push_toArray`. -/
theorem lz77GreedyMergedLoopF_spec (data : ByteArray)
    (windowSize hashSize prevSize maxChain insertCap niceLen : Nat)
    (c : Array Nat) (pos : Nat) (acc : TokenArray)
    (litF : {a : Array Nat // a.size = 286}) (distF : {a : Array Nat // a.size = 30})
    (hlit : litF.val = (tokenFreqsP acc.toArray).1) (hdist : distF.val = (tokenFreqsP acc.toArray).2) :
    lz77GreedyMergedLoopF data windowSize hashSize prevSize maxChain insertCap niceLen c pos acc litF distF =
      (lz77GreedyMergedLoop data windowSize hashSize prevSize maxChain insertCap niceLen c pos acc,
       ⟨(tokenFreqsP (lz77GreedyMergedLoop data windowSize hashSize prevSize maxChain insertCap niceLen c pos acc).toArray).1, (tokenFreqsP_size _).1⟩,
       ⟨(tokenFreqsP (lz77GreedyMergedLoop data windowSize hashSize prevSize maxChain insertCap niceLen c pos acc).toArray).2, (tokenFreqsP_size _).2⟩) := by
  induction hn : data.size - pos using Nat.strongRecOn generalizing pos acc litF distF c with
  | _ n ih =>
    unfold lz77GreedyMergedLoopF lz77GreedyMergedLoop
    by_cases hlt : pos + 2 < data.size
    · simp only [hlt, ↓reduceDIte]
      split
      · split
        · refine ih _ (by omega) _ _ _ _ _ ?_ ?_ rfl
          · rw [TokenArray.push_toArray]
            exact bumpRefLitFreqP_push acc.toArray _ _ (packTok_reference_tag _ _) hlit
          · rw [TokenArray.push_toArray]
            exact bumpRefDistFreqP_push acc.toArray _ _ (packTok_reference_tag _ _) hdist
        · refine ih _ (by omega) _ _ _ _ _ ?_ ?_ rfl
          · rw [TokenArray.push_toArray]
            exact bumpLitFreqP_push acc.toArray _ _ (packTok_literal_tag _) hlit
          · rw [TokenArray.push_toArray]
            exact distFreq_push_lit acc.toArray _ _ (packTok_literal_tag _) hdist
      · refine ih _ (by omega) _ _ _ _ _ ?_ ?_ rfl
        · rw [TokenArray.push_toArray]
          exact bumpLitFreqP_push acc.toArray _ _ (packTok_literal_tag _) hlit
        · rw [TokenArray.push_toArray]
          exact distFreq_push_lit acc.toArray _ _ (packTok_literal_tag _) hdist
    · simp only [hlt, ↓reduceDIte]
      exact trailingPF_spec data pos acc litF distF hlit hdist

/-- **The fused greedy entry computes the merged matcher's tokens and their
    frequencies in one pass.** -/
theorem lz77ChainIterPMergedF_eq (data : ByteArray) (maxChain windowSize insertCap niceLen : Nat) :
    lz77ChainIterPMergedF data maxChain windowSize insertCap niceLen =
      (lz77ChainIterPMerged data maxChain windowSize insertCap niceLen,
       ⟨(tokenFreqsP (lz77ChainIterPMerged data maxChain windowSize insertCap niceLen).toArray).1, (tokenFreqsP_size _).1⟩,
       ⟨(tokenFreqsP (lz77ChainIterPMerged data maxChain windowSize insertCap niceLen).toArray).2, (tokenFreqsP_size _).2⟩) := by
  unfold lz77ChainIterPMergedF lz77ChainIterPMerged
  split
  · exact trailingPF_spec data 0 TokenArray.empty initLitFreqF initDistFreqF
      (by rw [TokenArray.empty_toArray]; exact tokenFreqsP_nil_fst)
      (by rw [TokenArray.empty_toArray]; exact tokenFreqsP_nil_snd)
  · exact lz77GreedyMergedLoopF_spec data windowSize 65536 (min chainWinSize data.size) maxChain
      insertCap niceLen _ 0 TokenArray.empty initLitFreqF initDistFreqF
      (by rw [TokenArray.empty_toArray]; exact tokenFreqsP_nil_fst)
      (by rw [TokenArray.empty_toArray]; exact tokenFreqsP_nil_snd)

end Zip.Native.Deflate
