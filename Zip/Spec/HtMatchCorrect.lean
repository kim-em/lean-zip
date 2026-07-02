import Zip.Spec.LZ77ChainCorrect

/-!
# Correctness of the chainless 2-way-bucket LZ77 matcher (`htMatch`)

`htMatch` (libdeflate `ht_matchfinder` style, #2738) replaces the hash-chain
walk with two bounded probes into a 2-positions-per-bucket table, minimum match
length 4, and a `niceLen` early-out. The table is only a heuristic for *finding*
candidates: validity is re-established at emission by `countMatch` + the window
guards (both in the shared `htBest`/`htProbe`), so the table contents never enter
the proof. This file proves `ValidDecomp` (→ `htMatch_resolves`), encodability
and emptiness for the recursive reference, transports them to the iterative twin
`htMatchIter` (`htMatchIter_eq_htMatch`), and proves the packed twin
`htMatchIterP` is the `packTok` image of the boxed one — the same three contracts
`lzMatch` consumes, so the level-≤1 arm of the dispatch is transparent to the
roundtrip proof.
-/

namespace Zip.Native.Deflate

open Zip.Native.Deflate (htMatch htMatchIter htMatchIterP htBest htProbe lz77Greedy)

/-! ## Probe spec: the returned match is a real in-window backward match -/

/-- The `Q` invariant on a `(bestLen, bestPos)` probe result: either empty, or a
    genuine in-window backward match whose bytes are verified equal. -/
private def ProbeOk (data : ByteArray) (windowSize pos maxLen bestLen bestPos : Nat) : Prop :=
  bestLen = 0 ∨ (bestPos < pos ∧ pos - bestPos ≤ windowSize ∧ bestPos + maxLen ≤ data.size ∧
    (∀ i, i < bestLen → data[pos + i]! = data[bestPos + i]!) ∧ bestLen ≤ maxLen)

/-- One candidate step preserves `ProbeOk`: `htBest` either keeps the running
    best or replaces it with a `countMatch`-verified guarded candidate. -/
theorem htBest_spec (data : ByteArray) (windowSize pos maxLen : Nat)
    (hpm : pos + maxLen ≤ data.size) (cand bestLen bestPos : Nat)
    (hb : ProbeOk data windowSize pos maxLen bestLen bestPos) :
    let r := htBest data windowSize pos maxLen hpm cand bestLen bestPos
    ProbeOk data windowSize pos maxLen r.1 r.2 := by
  unfold htBest ProbeOk
  split
  · rename_i hc
    have hcand : cand + maxLen ≤ data.size := by omega
    have hcm := lz77Greedy.countMatch_matches data cand pos maxLen hcand hpm
    by_cases hml : lz77Greedy.countMatch data cand pos maxLen hcand hpm > bestLen
    · simp only [hml, ↓reduceIte]
      exact Or.inr ⟨hc.1, hc.2, hcand, fun i hi => (hcm.1 i hi).symm, hcm.2⟩
    · simp only [hml, ↓reduceIte]; exact hb
  · exact hb

/-- The two-probe lookup returns a `ProbeOk` result: both probes start from the
    empty best (`ProbeOk` with `bestLen = 0`) and each `htBest` preserves it. -/
theorem htProbe_spec (data : ByteArray) (windowSize pos maxLen niceLen : Nat)
    (hpm : pos + maxLen ≤ data.size) (c0 c1 : Nat) :
    let r := htProbe data windowSize pos maxLen niceLen hpm c0 c1
    ProbeOk data windowSize pos maxLen r.1 r.2 := by
  have h0 := htBest_spec data windowSize pos maxLen hpm c0 0 0 (Or.inl rfl)
  simp only [htProbe]
  split
  · exact h0
  · exact htBest_spec data windowSize pos maxLen hpm c1 _ _ h0

/-! ## ValidDecomp for the recursive reference -/

/-- `htMatch.mainLoop` produces a valid decomposition from `pos`. Mirrors
    `lz77Chain_mainLoop_valid`; the reference case uses `htProbe_spec` (which
    holds for *any* table) in place of the chain walk, and the min-match gate is
    `≥ 4` (still `≥ 3`, so `ValidDecomp.reference` applies). -/
theorem htMatch_mainLoop_valid (data : ByteArray) (windowSize hashSize niceLen : Nat)
    (tbl : Array Nat) (pos : Nat) (hw : windowSize > 0) :
    ValidDecomp data pos (htMatch.mainLoop data windowSize hashSize niceLen tbl pos) := by
  unfold htMatch.mainLoop
  split
  · rename_i hlt
    dsimp only
    have hspec := htProbe_spec data windowSize pos (min 258 (data.size - pos)) niceLen (by omega)
      tbl[2 * lz77Greedy.hash3 data pos hashSize hlt]!
      tbl[2 * lz77Greedy.hash3 data pos hashSize hlt + 1]!
    unfold ProbeOk at hspec
    split
    · rename_i hge
      split
      · rename_i hle
        obtain h0 | hQ := hspec
        · omega
        · refine ValidDecomp.reference (by omega) (by omega) (by omega) hle ?_ ?_
          · intro i hi
            rw [Nat.sub_sub_self (Nat.le_of_lt hQ.1)]
            exact hQ.2.2.2.1 i hi
          · exact htMatch_mainLoop_valid _ _ _ _ _ _ hw
      · exact .literal (by omega) (getElem!_pos data pos (by omega))
          (htMatch_mainLoop_valid _ _ _ _ _ _ hw)
    · exact .literal (by omega) (getElem!_pos data pos (by omega))
        (htMatch_mainLoop_valid _ _ _ _ _ _ hw)
  · exact trailing_valid data pos
termination_by data.size - pos
decreasing_by all_goals omega

/-- `htMatch` produces a valid decomposition of the input data. -/
theorem htMatch_valid (data : ByteArray) (windowSize : Nat) (hw : windowSize > 0) :
    ValidDecomp data 0 (htMatch data windowSize).toList := by
  simp only [htMatch]
  split
  · simp only; exact trailing_valid data 0
  · simp only; exact htMatch_mainLoop_valid data windowSize htHashSize htNiceLen _ 0 hw

/-- Resolving the LZ77 tokens produced by `htMatch` recovers the original data. -/
theorem htMatch_resolves (data : ByteArray) (windowSize : Nat) (hw : windowSize > 0) :
    Deflate.Spec.resolveLZ77 (tokensToSymbols (htMatch data windowSize)) [] =
      some data.data.toList :=
  validDecomp_resolves data _ (htMatch_valid data windowSize hw)

/-! ## Encodability -/

/-- Inlined encoder bounds (same shape as `lz77Chain_mainLoop_encodable`). -/
private def Enc (t : LZ77Token) : Prop :=
  match t with
  | .literal _ => True
  | .reference len dist => 3 ≤ len ∧ len ≤ 258 ∧ 1 ≤ dist ∧ dist ≤ 32768

theorem htMatch_mainLoop_encodable (data : ByteArray) (windowSize hashSize niceLen : Nat)
    (tbl : Array Nat) (pos : Nat) (hw : windowSize > 0) (hws : windowSize ≤ 32768) :
    ∀ t ∈ htMatch.mainLoop data windowSize hashSize niceLen tbl pos, Enc t := by
  unfold htMatch.mainLoop
  split
  · rename_i hlt
    dsimp only
    have hspec := htProbe_spec data windowSize pos (min 258 (data.size - pos)) niceLen (by omega)
      tbl[2 * lz77Greedy.hash3 data pos hashSize hlt]!
      tbl[2 * lz77Greedy.hash3 data pos hashSize hlt + 1]!
    unfold ProbeOk at hspec
    split
    · rename_i hge
      split
      · rename_i hle
        obtain h0 | ⟨hQ1, hQ2, _, _, hQ5⟩ := hspec
        · omega
        · intro t ht
          cases ht with
          | head => exact ⟨by omega, by omega, by omega, by omega⟩
          | tail _ h => exact htMatch_mainLoop_encodable _ _ _ _ _ _ hw hws t h
      · intro t ht
        cases ht with
        | head => trivial
        | tail _ h => exact htMatch_mainLoop_encodable _ _ _ _ _ _ hw hws t h
    · intro t ht
      cases ht with
      | head => trivial
      | tail _ h => exact htMatch_mainLoop_encodable _ _ _ _ _ _ hw hws t h
  · intro t ht
    exact trailing_encodable data pos t ht
termination_by data.size - pos
decreasing_by all_goals omega

/-- Every token `htMatch` emits satisfies the encoder bounds. -/
theorem htMatch_encodable (data : ByteArray) (windowSize : Nat)
    (hw : windowSize > 0) (hws : windowSize ≤ 32768) :
    ∀ t ∈ (htMatch data windowSize).toList,
      match t with
      | .literal _ => True
      | .reference len dist => 3 ≤ len ∧ len ≤ 258 ∧ 1 ≤ dist ∧ dist ≤ 32768 := by
  simp only [htMatch]
  split
  · intro t ht; exact trailing_encodable data 0 t ht
  · intro t ht; exact htMatch_mainLoop_encodable data windowSize htHashSize htNiceLen _ 0 hw hws t ht

/-- The chainless matcher emits no tokens on empty input. -/
theorem htMatch_empty (data : ByteArray) (windowSize : Nat)
    (hzero : data.size = 0) : htMatch data windowSize = #[] := by
  simp only [htMatch, show data.size < 3 from by omega, ↓reduceIte]
  have htrail : lz77Greedy.trailing data 0 = [] := by
    unfold lz77Greedy.trailing
    simp only [show ¬(0 < data.size) from by omega, ↓reduceDIte]
  rw [htrail]

/-! ## Iterative twin equals the reference -/

/-- The iterative `mainLoop` is the accumulator form of the recursive one. The
    guarded table reads/writes rewrite to the reference's panic-checked ops
    (`headProbeGuarded_eq`/`guardedSet_eq`), so the only difference is push vs.
    cons at each emission. -/
private theorem htMatchIter_mainLoop_eq (data : ByteArray) (windowSize hashSize niceLen : Nat)
    (tbl : Array Nat) (pos : Nat) (acc : Array LZ77Token) :
    htMatchIter.mainLoop data windowSize hashSize niceLen tbl pos acc =
      acc ++ (htMatch.mainLoop data windowSize hashSize niceLen tbl pos).toArray := by
  induction h : data.size - pos using Nat.strongRecOn generalizing pos acc tbl with
  | _ n ih =>
    unfold htMatchIter.mainLoop htMatch.mainLoop
    simp only [headProbeGuarded_eq, guardedSet_eq]
    by_cases hlt : pos + 2 < data.size
    · simp only [hlt, ↓reduceDIte]
      split
      · split
        · rw [ih _ (by omega) _ _ _ rfl, List.toArray_cons, ← Array.append_assoc, Array.push_eq_append]
        · rw [ih _ (by omega) _ _ _ rfl, List.toArray_cons, ← Array.append_assoc, Array.push_eq_append]
      · rw [ih _ (by omega) _ _ _ rfl, List.toArray_cons, ← Array.append_assoc, Array.push_eq_append]
    · simp only [hlt, ↓reduceDIte]
      exact trailing_eq data pos acc

/-- `htMatchIter` produces exactly the same tokens as `htMatch`. -/
theorem htMatchIter_eq_htMatch (data : ByteArray) (windowSize : Nat) :
    htMatchIter data windowSize = htMatch data windowSize := by
  unfold htMatchIter htMatch
  split
  · rw [trailing_eq]; simp only [List.append_toArray, List.nil_append]
  · rw [htMatchIter_mainLoop_eq]; simp only [List.append_toArray, List.nil_append]

theorem htMatchIter_valid (data : ByteArray) (windowSize : Nat) (hw : windowSize > 0) :
    ValidDecomp data 0 (htMatchIter data windowSize).toList := by
  rw [htMatchIter_eq_htMatch]; exact htMatch_valid data windowSize hw

theorem htMatchIter_resolves (data : ByteArray) (windowSize : Nat) (hw : windowSize > 0) :
    Deflate.Spec.resolveLZ77 (tokensToSymbols (htMatchIter data windowSize)) [] =
      some data.data.toList := by
  rw [htMatchIter_eq_htMatch]; exact htMatch_resolves data windowSize hw

theorem htMatchIter_encodable (data : ByteArray) (windowSize : Nat)
    (hw : windowSize > 0) (hws : windowSize ≤ 32768) :
    ∀ t ∈ (htMatchIter data windowSize).toList,
      match t with
      | .literal _ => True
      | .reference len dist => 3 ≤ len ∧ len ≤ 258 ∧ 1 ≤ dist ∧ dist ≤ 32768 := by
  rw [htMatchIter_eq_htMatch]; exact htMatch_encodable data windowSize hw hws

theorem htMatchIter_empty (data : ByteArray) (windowSize : Nat)
    (hzero : data.size = 0) : htMatchIter data windowSize = #[] := by
  rw [htMatchIter_eq_htMatch]; exact htMatch_empty data windowSize hzero

/-! ## Packed twin is the `packTok` image of the boxed one -/

/-- `trailingP` is the packed image of the boxed trailing-literals loop (local
    copy of the private lemma in `LZ77PackedCorrect`, to avoid an import cycle:
    that file imports this one for the `lzMatchP` dispatch). -/
private theorem trailingP_eq (data : ByteArray) (pos : Nat) (acc : Array LZ77Token) :
    trailingP data pos (acc.map packTok) = (lz77GreedyIter.trailing data pos acc).map packTok := by
  induction h : data.size - pos using Nat.strongRecOn generalizing pos acc with
  | _ n ih =>
    unfold trailingP lz77GreedyIter.trailing
    by_cases hp : pos < data.size
    · simp only [hp, ↓reduceDIte]
      rw [← Array.map_push, ih _ (by omega) _ _ rfl]
    · simp only [hp, ↓reduceDIte]

/-- The packed `mainLoop` is the packed image of the boxed one: identical
    control flow and table state, `packTok` at each push. -/
private theorem htMatchIterP_mainLoop_eq (data : ByteArray) (windowSize hashSize niceLen : Nat)
    (tbl : Array Nat) (pos : Nat) (acc : Array LZ77Token) :
    htMatchIterP.mainLoop data windowSize hashSize niceLen tbl pos (acc.map packTok) =
      (htMatchIter.mainLoop data windowSize hashSize niceLen tbl pos acc).map packTok := by
  induction h : data.size - pos using Nat.strongRecOn generalizing pos acc tbl with
  | _ n ih =>
    unfold htMatchIterP.mainLoop htMatchIter.mainLoop
    by_cases hlt : pos + 2 < data.size
    · simp only [hlt, ↓reduceDIte]
      split
      · split
        · rw [← Array.map_push, ih _ (by omega) _ _ _ rfl]
        · rw [← Array.map_push, ih _ (by omega) _ _ _ rfl]
      · rw [← Array.map_push, ih _ (by omega) _ _ _ rfl]
    · simp only [hlt, ↓reduceDIte]
      exact trailingP_eq data pos acc

/-- `htMatchIterP` produces exactly the `packTok` image of `htMatchIter`. -/
theorem htMatchIterP_eq (data : ByteArray) (windowSize : Nat) :
    htMatchIterP data windowSize = (htMatchIter data windowSize).map packTok := by
  unfold htMatchIterP htMatchIter
  split
  · simpa only [List.map_toArray, List.map_nil] using trailingP_eq data 0 #[]
  · simpa only [List.map_toArray, List.map_nil, Array.emptyWithCapacity_eq] using
      htMatchIterP_mainLoop_eq data windowSize htHashSize htNiceLen _ 0 #[]

/-- The boxed view of the packed chainless matcher is the boxed matcher. -/
theorem htMatchIterP_map (data : ByteArray) (windowSize : Nat)
    (hw : windowSize > 0) (hws : windowSize ≤ 32768) :
    (htMatchIterP data windowSize).map unpackTok = htMatchIter data windowSize := by
  have henc := htMatchIter_encodable data windowSize hw hws
  rw [htMatchIterP_eq, Array.map_map]
  have hcongr : Array.map (unpackTok ∘ packTok) (htMatchIter data windowSize) =
      Array.map id (htMatchIter data windowSize) :=
    Array.map_congr_left fun t ht => unpackTok_packTok t (henc t (by simpa only [Array.mem_toList_iff] using ht))
  rw [hcongr, Array.map_id]

end Zip.Native.Deflate
