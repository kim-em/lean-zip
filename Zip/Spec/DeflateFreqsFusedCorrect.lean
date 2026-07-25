import Zip.Native.DeflateFreqsFused
import Zip.Spec.DeflateFreqsAdditive
import Zip.Spec.LZ77ChainCorrect

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

The wide-counter L1 path is refined separately: aligned `UInt64` stores update
exactly one logical bin, the token-count invariant rules out modular wrap under
the production addressability guard, and the wide matcher follows the same
token control flow.  `lz77ChainIterPMergedFU64Level1_eq` is the resulting entry
theorem used by the production dispatch.
-/

namespace Zip.Native.Deflate

theorem ByteArray.ugetUInt64LE_usetUInt64LE_same (a : ByteArray) (off : USize)
    (v : UInt64) (h : off.toNat + 8 ≤ a.size) :
    (a.usetUInt64LE off v h).ugetUInt64LE off (by
      rw [size_usetUInt64LE]
      exact h) = v := by
  simp [ByteArray.ugetUInt64LE, ByteArray.usetUInt64LE,
    ByteArray.getElem_eq_getElem_data, ByteArray.data_set, Array.getElem_set]
  bv_decide

theorem ByteArray.ugetUInt64LE_usetUInt64LE_disjoint (a : ByteArray)
    (writeOff readOff : USize) (v : UInt64)
    (hw : writeOff.toNat + 8 ≤ a.size) (hr : readOff.toNat + 8 ≤ a.size)
    (hdisj : writeOff.toNat + 8 ≤ readOff.toNat ∨
      readOff.toNat + 8 ≤ writeOff.toNat) :
    (a.usetUInt64LE writeOff v hw).ugetUInt64LE readOff (by
      rw [size_usetUInt64LE]
      exact hr) = a.ugetUInt64LE readOff hr := by
  simp only [ByteArray.ugetUInt64LE, ByteArray.usetUInt64LE,
    ByteArray.getElem_eq_getElem_data, ByteArray.data_set, Array.getElem_set]
  rcases hdisj with hdisj | hdisj <;>
    simp (config := { maxSteps := 100000 }) (discharger := omega) only [if_neg] <;> rfl

theorem fusedFreqOffset_toNat (idx : Nat) (hidx : idx < fusedFreqBinCount) :
    (idx * 8).toUSize.toNat = idx * 8 := by
  apply toUSize_toNat_of_lt
  exact Nat.lt_of_lt_of_le (by
    unfold fusedFreqBinCount at hidx
    omega : idx * 8 < 2 ^ 32) USize.le_size

/-- Reading the aligned bin just incremented by the wide counter store. -/
theorem getFusedFreqBytes_bump_same (f : FusedFreqBytes) (idx : Nat)
    (hidx : idx < fusedFreqBinCount)
    (hcount : getFusedFreqBytes f idx hidx + 1 < UInt64.size) :
    getFusedFreqBytes (bumpFusedFreqBytes f idx hidx) idx hidx =
      getFusedFreqBytes f idx hidx + 1 := by
  simp only [getFusedFreqBytes, bumpFusedFreqBytes]
  rw [ByteArray.ugetUInt64LE_usetUInt64LE_same, UInt64.toNat_add]
  simp only [UInt64.toNat_one]
  rw [Nat.mod_eq_of_lt]
  simpa [getFusedFreqBytes] using hcount

/-- Incrementing one aligned bin preserves every other aligned bin. -/
theorem getFusedFreqBytes_bump_ne (f : FusedFreqBytes) (idx readIdx : Nat)
    (hidx : idx < fusedFreqBinCount) (hread : readIdx < fusedFreqBinCount)
    (hne : idx ≠ readIdx) :
    getFusedFreqBytes (bumpFusedFreqBytes f idx hidx) readIdx hread =
      getFusedFreqBytes f readIdx hread := by
  simp only [getFusedFreqBytes, bumpFusedFreqBytes]
  rw [ByteArray.ugetUInt64LE_usetUInt64LE_disjoint]
  rw [fusedFreqOffset_toNat idx hidx, fusedFreqOffset_toNat readIdx hread]
  omega

theorem getFusedFreqBytes_init (idx : Nat) (hidx : idx < fusedFreqBinCount) :
    getFusedFreqBytes initFusedFreqBytes idx hidx = 0 := by
  simp only [getFusedFreqBytes, initFusedFreqBytes, ByteArray.ugetUInt64LE]
  simp [ByteArray.getElem_eq_getElem_data, fusedFreqByteCount, fusedFreqBinCount]

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

/-- A per-bin literal/length count cannot exceed the number of remaining words. -/
theorem litDeltaP_le (ws : Array UInt32) (i k : Nat) :
    litDeltaP ws i k ≤ ws.size - i := by
  induction hn : ws.size - i using Nat.strongRecOn generalizing i with
  | _ n ih =>
    unfold litDeltaP
    by_cases hi : i < ws.size
    · simp only [hi, ↓reduceDIte]
      split
      · have := ih (ws.size - (i + 1)) (by omega) (i + 1) rfl
        omega
      · have := ih (ws.size - (i + 1)) (by omega) (i + 1) rfl
        omega
    · simp only [hi, ↓reduceDIte]
      exact Nat.zero_le _

/-- A per-bin distance count cannot exceed the number of remaining words. -/
theorem distDeltaP_le (ws : Array UInt32) (i k : Nat) :
    distDeltaP ws i k ≤ ws.size - i := by
  induction hn : ws.size - i using Nat.strongRecOn generalizing i with
  | _ n ih =>
    unfold distDeltaP
    by_cases hi : i < ws.size
    · simp only [hi, ↓reduceDIte]
      have hrec := ih (ws.size - (i + 1)) (by omega) (i + 1) rfl
      by_cases hc : ws[i] &&& ((1 : UInt32) <<< 31) = 0
      · simp only [hc, ↓reduceIte]
        omega
      · simp only [hc, ↓reduceIte]
        split <;> omega
    · simp only [hi, ↓reduceDIte]
      exact Nat.zero_le _

/-- Refinement relation for the packed wide-counter buffer.  The buffer stores
    only actual token counts; the conventional EOB seed is added exactly once
    by `fusedFreqBytesToNat`. -/
def FusedFreqBytesRep (f : FusedFreqBytes) (ws : Array UInt32) : Prop :=
  (∀ (k : Nat) (hk : k < 286),
      getFusedFreqBytes f k (by unfold fusedFreqBinCount; omega) = litDeltaP ws 0 k) ∧
  (∀ (k : Nat) (hk : k < 30),
      getFusedFreqBytes f (286 + k) (by unfold fusedFreqBinCount; omega) = distDeltaP ws 0 k)

theorem initFusedFreqBytes_rep :
    FusedFreqBytesRep initFusedFreqBytes (#[] : Array UInt32) := by
  constructor
  · intro k hk
    rw [getFusedFreqBytes_init]
    simp [litDeltaP]
  · intro k hk
    rw [getFusedFreqBytes_init]
    simp [distDeltaP]

@[simp] theorem fusedFreqBytesToNat_fst_size (f : FusedFreqBytes) :
    (fusedFreqBytesToNat f).1.size = 286 := by
  simp [fusedFreqBytesToNat]

@[simp] theorem fusedFreqBytesToNat_snd_size (f : FusedFreqBytes) :
    (fusedFreqBytesToNat f).2.size = 30 := by
  simp [fusedFreqBytesToNat]

set_option maxRecDepth 2048 in
theorem fusedFreqBytesToNat_eq (f : FusedFreqBytes) (ws : Array UInt32)
    (hrep : FusedFreqBytesRep f ws) :
    fusedFreqBytesToNat f = tokenFreqsP ws := by
  apply Prod.ext
  · apply Array.ext
    · rw [fusedFreqBytesToNat_fst_size, (tokenFreqsP_size ws).1]
    · intro k hk _
      have hk286 : k < 286 := by simpa using hk
      have htok : k < (tokenFreqsP ws).1.size := by
        rw [(tokenFreqsP_size ws).1]
        exact hk286
      simp only [fusedFreqBytesToNat]
      rw [Array.getElem_ofFn, ← getElem!_pos _ k htok]
      rw [tokenFreqsP_lit]
      rw [hrep.1 k hk286]
      simp [Nat.add_comm]
  · apply Array.ext
    · rw [fusedFreqBytesToNat_snd_size, (tokenFreqsP_size ws).2]
    · intro k hk _
      have hk30 : k < 30 := by simpa using hk
      have htok : k < (tokenFreqsP ws).2.size := by
        rw [(tokenFreqsP_size ws).2]
        exact hk30
      simp only [fusedFreqBytesToNat]
      rw [Array.getElem_ofFn, ← getElem!_pos _ k htok]
      rw [tokenFreqsP_dist]
      exact hrep.2 k hk30

/-- A wide literal bump refines the corresponding mathematical single-token
    histogram update, provided the token count is below the UInt64 modulus. -/
theorem bumpLitFreqU64_rep (f : FusedFreqBytes) (ws : Array UInt32) (w : UInt32)
    (hc : w &&& ((1 : UInt32) <<< 31) = 0)
    (hrep : FusedFreqBytesRep f ws) (hcap : ws.size + 1 < UInt64.size) :
    FusedFreqBytesRep (bumpLitFreqU64 f w) (ws.push w) := by
  have hwi : w.toUInt8.toNat < 286 := by
    have := UInt8.toNat_lt w.toUInt8
    omega
  have hwfull : w.toUInt8.toNat < fusedFreqBinCount := by
    unfold fusedFreqBinCount
    omega
  have hbump : litBumpIdxP w = w.toUInt8.toNat := by
    unfold litBumpIdxP
    rw [if_pos hc]
  constructor
  · intro k hk
    rw [litDeltaP_push, hbump]
    simp only [bumpLitFreqU64]
    by_cases heq : w.toUInt8.toNat = k
    · subst k
      rw [getFusedFreqBytes_bump_same]
      · rw [hrep.1 _ hwi, if_pos rfl]
      · rw [hrep.1 _ hwi]
        have hle := litDeltaP_le ws 0 w.toUInt8.toNat
        simp only [Nat.sub_zero] at hle
        omega
    · rw [getFusedFreqBytes_bump_ne]
      rw [hrep.1 k hk, if_neg heq, Nat.add_zero]
      exact heq
  · intro k hk
    simp only [distDeltaP_push, hc, if_pos, Nat.add_zero]
    simp only [bumpLitFreqU64]
    rw [getFusedFreqBytes_bump_ne]
    · exact hrep.2 k hk
    · omega

/-- The paired wide length/distance bumps refine one packed reference token. -/
theorem bumpRefFreqU64_rep (f : FusedFreqBytes) (ws : Array UInt32) (w : UInt32)
    (hc : ¬ (w &&& ((1 : UInt32) <<< 31) = 0))
    (hrep : FusedFreqBytesRep f ws) (hcap : ws.size + 1 < UInt64.size) :
    FusedFreqBytesRep (bumpRefDistFreqU64 (bumpRefLitFreqU64 f w) w) (ws.push w) := by
  let lIdx := codeIdx (lenCodeWord (((w >>> 16) &&& 0x7FFF).toNat))
  let dIdx := codeIdx (distCodeWord ((w &&& 0xFFFF).toNat))
  have hl : lIdx + 257 < 286 := by
    obtain ⟨⟨i, e, v⟩, he⟩ := Option.isSome_iff_exists.mp
      (findLengthCode_isSome (((w >>> 16) &&& 0x7FFF).toNat))
    have hli : lIdx = i := codeIdx_lenCodeWord _ _ _ _ he
    have hi := nativeFindLengthCode_idx_bound _ _ _ _ he
    omega
  have hd : dIdx < 30 := by
    obtain ⟨⟨i, e, v⟩, he⟩ := Option.isSome_iff_exists.mp
      (findDistCode_isSome ((w &&& 0xFFFF).toNat))
    have hdi : dIdx = i := codeIdx_distCodeWord _ _ _ _ he
    have hi := nativeFindDistCode_idx_bound _ _ _ _ he
    omega
  have hlFull : lIdx + 257 < fusedFreqBinCount := by
    unfold fusedFreqBinCount
    omega
  have hdFull : 286 + dIdx < fusedFreqBinCount := by
    unfold fusedFreqBinCount
    omega
  have hbump : litBumpIdxP w = lIdx + 257 := by
    unfold litBumpIdxP
    rw [if_neg hc]
  constructor
  · intro k hk
    rw [litDeltaP_push, hbump]
    simp only [bumpRefDistFreqU64, bumpRefLitFreqU64]
    rw [getFusedFreqBytes_bump_ne]
    · by_cases heq : lIdx + 257 = k
      · subst k
        rw [getFusedFreqBytes_bump_same]
        · rw [hrep.1 _ hl, if_pos rfl]
        · rw [hrep.1 _ hl]
          have hle := litDeltaP_le ws 0 (lIdx + 257)
          simp only [Nat.sub_zero] at hle
          omega
      · rw [getFusedFreqBytes_bump_ne]
        rw [hrep.1 k hk, if_neg heq, Nat.add_zero]
        exact heq
    · omega
  · intro k hk
    simp only [distDeltaP_push]
    simp only [bumpRefDistFreqU64, bumpRefLitFreqU64]
    by_cases heq : dIdx = k
    · subst k
      rw [getFusedFreqBytes_bump_same]
      · rw [getFusedFreqBytes_bump_ne]
        · rw [hrep.2 _ hd]
          simp [hc, dIdx]
        · omega
      · rw [getFusedFreqBytes_bump_ne]
        · rw [hrep.2 _ hd]
          have hle := distDeltaP_le ws 0 dIdx
          simp only [Nat.sub_zero] at hle
          omega
        · omega
    · rw [getFusedFreqBytes_bump_ne]
      · rw [getFusedFreqBytes_bump_ne]
        · rw [hrep.2 k hk]
          have hcodeNe : ¬ codeIdx (distCodeWord (w.toNat &&& 65535)) = k := by
            intro hcode
            apply heq
            simpa [dIdx] using hcode
          simp [hc, hcodeNe]
        · omega
      · omega

theorem byteArray_size_lt_uint64 (data : ByteArray)
    (haddr : data.size.toUSize.toNat = data.size) : data.size < UInt64.size := by
  apply Nat.lt_of_lt_of_le _ USize.size_le_uint64Size
  rw [← haddr]
  exact USize.toNat_lt_two_pow_numBits _

/-- The wide-counter trailing loop has exactly the plain trailing token stream
    and preserves the counter refinement relation. -/
theorem trailingPFU64_spec (data : ByteArray) (pos : Nat) (acc : TokenArray)
    (freqs : FusedFreqBytes) (haddr : data.size.toUSize.toNat = data.size)
    (hsize : acc.toArray.size ≤ pos) (hrep : FusedFreqBytesRep freqs acc.toArray) :
    (trailingPFU64 data pos acc freqs).1 = trailingPT data pos acc ∧
      FusedFreqBytesRep (trailingPFU64 data pos acc freqs).2
        (trailingPT data pos acc).toArray := by
  induction hn : data.size - pos using Nat.strongRecOn generalizing pos acc freqs with
  | _ n ih =>
    unfold trailingPFU64 trailingPT
    by_cases h : pos < data.size
    · simp only [h, ↓reduceDIte]
      have hcap : acc.toArray.size + 1 < UInt64.size := by
        have hdata := byteArray_size_lt_uint64 data haddr
        omega
      have hrep' : FusedFreqBytesRep
          (bumpLitFreqU64 freqs (packTok (.literal data[pos])))
          (acc.push (packTok (.literal data[pos]))).toArray := by
        rw [TokenArray.push_toArray]
        exact bumpLitFreqU64_rep freqs acc.toArray _ (packTok_literal_tag _) hrep hcap
      have hsize' : (acc.push (packTok (.literal data[pos]))).toArray.size ≤ pos + 1 := by
        rw [TokenArray.push_toArray, Array.size_push]
        omega
      exact ih (data.size - (pos + 1)) (by omega) (pos + 1) _ _ hsize' hrep' rfl
    · simp only [h, ↓reduceDIte]
      exact ⟨trivial, hrep⟩

/-- The wide-counter greedy loop follows the exact plain matcher control flow,
    returns the same packed tokens, and refines their mathematical histogram. -/
theorem lz77GreedyMergedLoopFU64_spec (data : ByteArray)
    (windowSize hashSize prevSize maxChain insertCap niceLen : Nat)
    (c : Array Nat) (pos : Nat) (acc : TokenArray) (freqs : FusedFreqBytes)
    (haddr : data.size.toUSize.toNat = data.size)
    (hsize : acc.toArray.size ≤ pos) (hrep : FusedFreqBytesRep freqs acc.toArray) :
    (lz77GreedyMergedLoopFU64 data windowSize hashSize prevSize maxChain insertCap niceLen
      c pos acc freqs).1 =
      lz77GreedyMergedLoop data windowSize hashSize prevSize maxChain insertCap niceLen
        c pos acc ∧
    FusedFreqBytesRep
      (lz77GreedyMergedLoopFU64 data windowSize hashSize prevSize maxChain insertCap niceLen
        c pos acc freqs).2
      (lz77GreedyMergedLoop data windowSize hashSize prevSize maxChain insertCap niceLen
        c pos acc).toArray := by
  induction hn : data.size - pos using Nat.strongRecOn generalizing pos acc freqs c with
  | _ n ih =>
    unfold lz77GreedyMergedLoopFU64 lz77GreedyMergedLoop
    by_cases hlt : pos + 2 < data.size
    · simp only [hlt, ↓reduceDIte]
      have hcap : acc.toArray.size + 1 < UInt64.size := by
        have hdata := byteArray_size_lt_uint64 data haddr
        omega
      simp only [chainWalkPackedUUChecked_low, chainWalkPackedUUChecked_high]
      split
      all_goals
        split
        · split
          · refine ih _ (by omega) _ _ _ _ ?_ ?_ rfl
            · rw [TokenArray.push_toArray, Array.size_push]
              omega
            · rw [TokenArray.push_toArray]
              exact bumpRefFreqU64_rep freqs acc.toArray _
                (packTok_reference_tag _ _) hrep hcap
          · refine ih _ (by omega) _ _ _ _ ?_ ?_ rfl
            · rw [TokenArray.push_toArray, Array.size_push]
              omega
            · rw [TokenArray.push_toArray]
              exact bumpLitFreqU64_rep freqs acc.toArray _
                (packTok_literal_tag _) hrep hcap
        · refine ih _ (by omega) _ _ _ _ ?_ ?_ rfl
          · rw [TokenArray.push_toArray, Array.size_push]
            omega
          · rw [TokenArray.push_toArray]
            exact bumpLitFreqU64_rep freqs acc.toArray _
              (packTok_literal_tag _) hrep hcap
    · simp only [hlt, ↓reduceDIte]
      exact trailingPFU64_spec data pos acc freqs haddr hsize hrep

/-- Under the production addressability guard, the wide L1 entry returns the
    exact plain L1 token stream and its conventional `tokenFreqsP` arrays. -/
theorem lz77ChainIterPMergedFU64Level1_eq (data : ByteArray)
    (haddr : data.size.toUSize.toNat = data.size) :
    lz77ChainIterPMergedFU64Level1 data =
      let tokens := lz77ChainIterPMerged data 4 32768 2 258
      (tokens, (tokenFreqsP tokens.toArray).1, (tokenFreqsP tokens.toArray).2) := by
  unfold lz77ChainIterPMergedFU64Level1 lz77ChainIterPMerged
  by_cases hsmall : data.size < 3
  · simp only [hsmall, if_pos]
    generalize hr : trailingPFU64 data 0 TokenArray.empty initFusedFreqBytes = r
    rcases r with ⟨tokens, freqs⟩
    have hs := trailingPFU64_spec data 0 TokenArray.empty initFusedFreqBytes haddr
      (by rw [TokenArray.empty_toArray]; simp) (by
        rw [TokenArray.empty_toArray]
        exact initFusedFreqBytes_rep)
    rw [hr] at hs
    have hf := fusedFreqBytesToNat_eq freqs
      (trailingPT data 0 TokenArray.empty).toArray hs.2
    rw [hf, hs.1]
  · simp only [hsmall, if_false]
    generalize hr : lz77GreedyMergedLoopFU64 data 32768 65536
      (min chainWinSize data.size) 4 2 258
      (.replicate (min chainWinSize data.size + 65536) data.size) 0
      (TokenArray.emptyWithCapacity data.size) initFusedFreqBytes = r
    rcases r with ⟨tokens, freqs⟩
    have hs := lz77GreedyMergedLoopFU64_spec data 32768 65536
      (min chainWinSize data.size) 4 2 258
      (.replicate (min chainWinSize data.size + 65536) data.size) 0
      (TokenArray.emptyWithCapacity data.size) initFusedFreqBytes haddr
      (by rw [TokenArray.emptyWithCapacity_toArray]; simp) (by
        rw [TokenArray.emptyWithCapacity_toArray]
        exact initFusedFreqBytes_rep)
    rw [hr] at hs
    have hf := fusedFreqBytesToNat_eq freqs
      (lz77GreedyMergedLoop data 32768 65536 (min chainWinSize data.size)
        4 2 258 (.replicate (min chainWinSize data.size + 65536) data.size) 0
        (TokenArray.emptyWithCapacity data.size)).toArray hs.2
    rw [hf, hs.1]

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
    copy of `Zip.Spec.LZ77MergedCorrect.trailingPT_toArray` to avoid importing the
    broader merged-matcher correctness module solely for this bridge. -/
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
      all_goals
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
      insertCap niceLen _ 0 (TokenArray.emptyWithCapacity data.size) initLitFreqF initDistFreqF
      (by rw [TokenArray.emptyWithCapacity_toArray]; exact tokenFreqsP_nil_fst)
      (by rw [TokenArray.emptyWithCapacity_toArray]; exact tokenFreqsP_nil_snd)

end Zip.Native.Deflate
