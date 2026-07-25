import Zip.Native.Deflate

/-!
Large-input level-5 matcher specializations.

This module is deliberately separate from `Zip.Native.Deflate`: the general
matcher and the optimal-parser module retain their established native code
layout, while `Zip.Native.DeflateDynamic` imports this module after
`Zip.Native.DeflateParse`.
-/

namespace Zip.Native.Deflate

/-- Two-candidate-unrolled fully-`USize` chain walk.  Each recursive trip
    consumes two candidates; the `fuel = 1` and `fuel = 2` leaves preserve the
    reference walk's rule that the final candidate contributes without reading
    its successor link.  `chainWalkPackedUU2_eq` proves this is exactly two
    unfoldings of `chainWalkPackedUU`. -/
def chainWalkPackedUU2 (data : ByteArray) (prev : Array Nat)
    (hps : min chainWinSize data.size ≤ prev.size) (hsz : data.size < USize.size)
    (windowSizeU posU maxLenU cutoffU candU fuelU bestLenU bestPosU : USize)
    (hpm : posU.toNat + maxLenU.toNat ≤ data.size) : USize :=
  if fuelU = 0 then bestPosU * 512 + bestLenU
  else if hc : candU < posU ∧ posU - candU ≤ windowSizeU then
    have hUS : USize.size = 2 ^ System.Platform.numBits := rfl
    have hcpos : candU.toNat < posU.toNat := USize.lt_iff_toNat_lt.mp hc.1
    have hcand : candU.toNat + maxLenU.toNat ≤ data.size := by omega
    let skip : Bool := if hbl : bestLenU < maxLenU then
        have hbln : bestLenU.toNat < maxLenU.toNat := USize.lt_iff_toNat_lt.mp hbl
        have hb1 : (candU + bestLenU).toNat < data.size := by
          have e : (candU + bestLenU).toNat = candU.toNat + bestLenU.toNat := by
            rw [USize.toNat_add]; apply Nat.mod_eq_of_lt; omega
          omega
        have hb2 : (posU + bestLenU).toNat < data.size := by
          have e : (posU + bestLenU).toNat = posU.toNat + bestLenU.toNat := by
            rw [USize.toNat_add]; apply Nat.mod_eq_of_lt; omega
          omega
        data.uget (candU + bestLenU) hb1 != data.uget (posU + bestLenU) hb2
      else false
    if fuelU = 1 then
      if skip then bestPosU * 512 + bestLenU
      else
        let mlU := countMatchUCore data candU posU maxLenU hsz hcand hpm
        let blU := if mlU > bestLenU then mlU else bestLenU
        let bpU := if mlU > bestLenU then candU else bestPosU
        bpU * 512 + blU
    else
      have hidx : candU.toNat &&& 0x7FFF < prev.size := by
        have h1 := winMask_lt candU.toNat
        have h2 := Nat.and_le_left (n := candU.toNat) (m := 0x7FFF)
        simp only [chainWinSize] at h1 hps
        omega
      let nextU := (prev[candU.toNat &&& 0x7FFF]'hidx).toUSize
      let fuel1U := fuelU - 1
      if skip then
        if bestLenU ≥ cutoffU then bestPosU * 512 + bestLenU
        else if hn : nextU.toNat = (prev[candU.toNat &&& 0x7FFF]'hidx) then
          -- Candidate two, with the best state unchanged by the prefilter miss.
          if hc2 : nextU < posU ∧ posU - nextU ≤ windowSizeU then
            have hc2pos : nextU.toNat < posU.toNat := USize.lt_iff_toNat_lt.mp hc2.1
            have hcand2 : nextU.toNat + maxLenU.toNat ≤ data.size := by omega
            let skip2 : Bool := if hbl2 : bestLenU < maxLenU then
                have hbln2 : bestLenU.toNat < maxLenU.toNat :=
                  USize.lt_iff_toNat_lt.mp hbl2
                have hb21 : (nextU + bestLenU).toNat < data.size := by
                  have e : (nextU + bestLenU).toNat =
                      nextU.toNat + bestLenU.toNat := by
                    rw [USize.toNat_add]; apply Nat.mod_eq_of_lt; omega
                  omega
                have hb22 : (posU + bestLenU).toNat < data.size := by
                  have e : (posU + bestLenU).toNat =
                      posU.toNat + bestLenU.toNat := by
                    rw [USize.toNat_add]; apply Nat.mod_eq_of_lt; omega
                  omega
                data.uget (nextU + bestLenU) hb21 !=
                  data.uget (posU + bestLenU) hb22
              else false
            if fuel1U = 1 then
              if skip2 then bestPosU * 512 + bestLenU
              else
                let ml2U := countMatchUCore data nextU posU maxLenU hsz hcand2 hpm
                let bl2U := if ml2U > bestLenU then ml2U else bestLenU
                let bp2U := if ml2U > bestLenU then nextU else bestPosU
                bp2U * 512 + bl2U
            else
              have hidx2 : nextU.toNat &&& 0x7FFF < prev.size := by
                have h1 := winMask_lt nextU.toNat
                have h2 := Nat.and_le_left (n := nextU.toNat) (m := 0x7FFF)
                simp only [chainWinSize] at h1 hps
                omega
              let next2U := (prev[nextU.toNat &&& 0x7FFF]'hidx2).toUSize
              if skip2 then
                if bestLenU ≥ cutoffU then bestPosU * 512 + bestLenU
                else if hn2 : next2U.toNat =
                    (prev[nextU.toNat &&& 0x7FFF]'hidx2) then
                  chainWalkPackedUU2 data prev hps hsz windowSizeU posU maxLenU
                    cutoffU next2U (fuel1U - 1) bestLenU bestPosU hpm
                else bestPosU * 512 + bestLenU
              else
                let ml2U := countMatchUCore data nextU posU maxLenU hsz hcand2 hpm
                let bl2U := if ml2U > bestLenU then ml2U else bestLenU
                let bp2U := if ml2U > bestLenU then nextU else bestPosU
                if bl2U ≥ cutoffU then bp2U * 512 + bl2U
                else if hn2 : next2U.toNat =
                    (prev[nextU.toNat &&& 0x7FFF]'hidx2) then
                  chainWalkPackedUU2 data prev hps hsz windowSizeU posU maxLenU cutoffU
                    next2U (fuel1U - 1) bl2U bp2U hpm
                else bp2U * 512 + bl2U
          else bestPosU * 512 + bestLenU
        else bestPosU * 512 + bestLenU
      else
        let mlU := countMatchUCore data candU posU maxLenU hsz hcand hpm
        let blU := if mlU > bestLenU then mlU else bestLenU
        let bpU := if mlU > bestLenU then candU else bestPosU
        if blU ≥ cutoffU then bpU * 512 + blU
        else if hn : nextU.toNat = (prev[candU.toNat &&& 0x7FFF]'hidx) then
          -- Candidate two, seeded by the first candidate's updated best state.
          if hc2 : nextU < posU ∧ posU - nextU ≤ windowSizeU then
            have hc2pos : nextU.toNat < posU.toNat := USize.lt_iff_toNat_lt.mp hc2.1
            have hcand2 : nextU.toNat + maxLenU.toNat ≤ data.size := by omega
            let skip2 : Bool := if hbl2 : blU < maxLenU then
                have hbln2 : blU.toNat < maxLenU.toNat :=
                  USize.lt_iff_toNat_lt.mp hbl2
                have hb21 : (nextU + blU).toNat < data.size := by
                  have e : (nextU + blU).toNat = nextU.toNat + blU.toNat := by
                    rw [USize.toNat_add]; apply Nat.mod_eq_of_lt; omega
                  omega
                have hb22 : (posU + blU).toNat < data.size := by
                  have e : (posU + blU).toNat = posU.toNat + blU.toNat := by
                    rw [USize.toNat_add]; apply Nat.mod_eq_of_lt; omega
                  omega
                data.uget (nextU + blU) hb21 != data.uget (posU + blU) hb22
              else false
            if fuel1U = 1 then
              if skip2 then bpU * 512 + blU
              else
                let ml2U := countMatchUCore data nextU posU maxLenU hsz hcand2 hpm
                let bl2U := if ml2U > blU then ml2U else blU
                let bp2U := if ml2U > blU then nextU else bpU
                bp2U * 512 + bl2U
            else
              have hidx2 : nextU.toNat &&& 0x7FFF < prev.size := by
                have h1 := winMask_lt nextU.toNat
                have h2 := Nat.and_le_left (n := nextU.toNat) (m := 0x7FFF)
                simp only [chainWinSize] at h1 hps
                omega
              let next2U := (prev[nextU.toNat &&& 0x7FFF]'hidx2).toUSize
              if skip2 then
                if blU ≥ cutoffU then bpU * 512 + blU
                else if hn2 : next2U.toNat =
                    (prev[nextU.toNat &&& 0x7FFF]'hidx2) then
                  chainWalkPackedUU2 data prev hps hsz windowSizeU posU maxLenU cutoffU
                    next2U (fuel1U - 1) blU bpU hpm
                else bpU * 512 + blU
              else
                let ml2U := countMatchUCore data nextU posU maxLenU hsz hcand2 hpm
                let bl2U := if ml2U > blU then ml2U else blU
                let bp2U := if ml2U > blU then nextU else bpU
                if bl2U ≥ cutoffU then bp2U * 512 + bl2U
                else if hn2 : next2U.toNat =
                    (prev[nextU.toNat &&& 0x7FFF]'hidx2) then
                  chainWalkPackedUU2 data prev hps hsz windowSizeU posU maxLenU cutoffU
                    next2U (fuel1U - 1) bl2U bp2U hpm
                else bp2U * 512 + bl2U
          else bpU * 512 + blU
        else bpU * 512 + blU
  else bestPosU * 512 + bestLenU
termination_by fuelU.toNat
decreasing_by
  all_goals
    have hfz : ¬ fuelU = 0 := by assumption
    have hf1 : ¬ fuelU = 1 := by assumption
    have hzero : fuelU.toNat ≠ 0 := by
      intro h
      apply hfz
      exact USize.toNat_inj.mp (by rw [h, USize.toNat_zero])
    have hone : fuelU.toNat ≠ 1 := by
      intro h
      apply hf1
      exact USize.toNat_inj.mp (by rw [h, USize.toNat_one])
    have htwoNat : 2 ≤ fuelU.toNat := by omega
    have honeFuel : (1 : USize) ≤ fuelU := by
      rw [USize.le_iff_toNat_le]
      rw [USize.toNat_one]
      omega
    have hfuel1 : (fuelU - 1).toNat = fuelU.toNat - 1 := by
      rw [USize.toNat_sub_of_le _ _ honeFuel, USize.toNat_one]
    have honeFuel1 : (1 : USize) ≤ fuelU - 1 := by
      rw [USize.le_iff_toNat_le, USize.toNat_one, hfuel1]
      omega
    rw [USize.toNat_sub_of_le _ _ honeFuel1, hfuel1, USize.toNat_one]
    omega

/-- Runtime guard for entering the fully-`USize` walk with an existing best
    match.  Lazy lookahead seeds the walk with the match at the preceding
    position, unlike the zero-seeded greedy tier. -/
abbrev chainWalkPackedUUSeededSafe (data : ByteArray) (prev : Array Nat)
    (windowSize maxLen cand fuel bestLen bestPos : Nat) : Prop :=
  chainWalkPackedUUSafe data prev windowSize maxLen cand fuel ∧
    bestLen.toUSize.toNat = bestLen ∧ bestPos.toUSize.toNat = bestPos ∧
    bestLen ≤ maxLen ∧ bestPos ≤ data.size

/-- Seeded entry to the two-candidate-unrolled native walk, used by the lazy
    matcher. -/
@[inline] def chainWalkPackedUUSeededChecked (data : ByteArray) (prev : Array Nat)
    (windowSize pos maxLen niceLen : Nat) (hpm : pos + maxLen ≤ data.size)
    (cand fuel bestLen bestPos : Nat)
    (hg : chainWalkPackedUUSeededSafe data prev windowSize maxLen cand fuel bestLen bestPos) :
    USize :=
  have hsz : data.size < USize.size := by
    rw [← hg.1.2.1]
    exact USize.toNat_lt_two_pow_numBits _
  chainWalkPackedUU2 data prev hg.1.1 hsz windowSize.toUSize pos.toUSize maxLen.toUSize
    (min niceLen maxLen).toUSize cand.toUSize fuel.toUSize bestLen.toUSize bestPos.toUSize (by
      rw [toUSize_toNat_of_lt (show pos < USize.size by omega),
        toUSize_toNat_of_lt (show maxLen < USize.size by omega)]
      exact hpm)

/-- Minimum stream size for L5's speed-oriented matcher/split policy. Kept next
    to the matcher dispatch so every large-L5 specialization shares one gate. -/
def l5LargeInputMinSize : Nat := 4 * 1024 * 1024

/-- Unrolled fully-native-word chain walk for the specialized large-input L5
    loop. The native-word safety guard keeps the established guarded walk as its
    defensive fallback. General lazy loops call `chainWalkGuardedPackedU`
    directly, so they do not pay this dispatch in their hot path. -/
@[inline] def chainWalkGuardedPackedUU (data : ByteArray) (prev : Array Nat)
    (windowSize pos maxLen niceLen : Nat) (hpm : pos + maxLen ≤ data.size)
    (cand fuel bestLen bestPos : Nat) : Nat :=
  if hg : chainWalkPackedUUSeededSafe data prev windowSize maxLen cand fuel bestLen bestPos then
    (chainWalkPackedUUSeededChecked data prev windowSize pos maxLen niceLen hpm
      cand fuel bestLen bestPos hg).toNat
  else
    chainWalkGuardedPackedU data prev windowSize pos maxLen niceLen hpm
      cand fuel bestLen bestPos
/-- Specialized lazy loop for the large-input L5 no-H3, single-deferral policy.
    It is the fresh-position arm of `lz77LazyMergedLoop` with the unreachable
    rolling/H3 state erased. The existing guarded native-word chain and merged
    insertion entries remain unchanged. -/
def lz77LazyMergedLoopNoH3Single (data : ByteArray)
    (windowSize hashSize prevSize maxChain insertCap goodMatch niceLen lazyDepth : Nat)
    (c : Array Nat) (pos : Nat) (acc : TokenArray) : TokenArray :=
  if hlt : pos + 2 < data.size then
    let h := lz77Greedy.hash3 data pos hashSize hlt
    let head := headProbeGuarded c (prevSize + h)
    let c := guardedSet c (prevSize + h) pos
    let c := guardedSet c (pos &&& 0x7FFF) head
    have hmaxLenP : pos + min 258 (data.size - pos) ≤ data.size := by omega
    let r := chainWalkGuardedPackedUU data c windowSize pos
      (min 258 (data.size - pos)) niceLen hmaxLenP head maxChain 0 0
    let matchLen := r % 512
    let matchPos := r / 512
    if hge : matchLen ≥ 3 then
      if hle : pos + matchLen ≤ data.size then
        if h3lt : pos + 3 < data.size then
          if matchLen < goodMatch then
            let h2 := lz77Greedy.hash3 data (pos + 1) hashSize (by omega)
            let head2 := headProbeGuarded c (prevSize + h2)
            have hmaxLen2P :
                (pos + 1) + min 258 (data.size - (pos + 1)) ≤ data.size := by omega
            let cutoff2 := min niceLen (min 258 (data.size - (pos + 1)))
            let seed := if matchLen < cutoff2 then matchLen else 0
            let r2 := chainWalkGuardedPackedUU data c windowSize (pos + 1)
              (min 258 (data.size - (pos + 1))) niceLen hmaxLen2P
              head2 lazyDepth seed 0
            let matchLen2 := r2 % 512
            let matchPos2 := r2 / 512
            if lazyAcceptCost matchLen (pos - matchPos) matchLen2
                (pos + 1 - matchPos2) then
              if hle2 : pos + 1 + matchLen2 ≤ data.size then
                have : data.size - (pos + 1 + matchLen2) < data.size - pos := by omega
                let c := updateHashesMergedGuarded data hashSize prevSize c pos 1
                  (matchLen2 + 1) insertCap
                lz77LazyMergedLoopNoH3Single data windowSize hashSize prevSize maxChain
                  insertCap goodMatch niceLen lazyDepth c (pos + 1 + matchLen2)
                  (acc.push (packTok (.literal (data[pos]'(by omega)))) |>.push
                    (packTok (.reference matchLen2 (pos + 1 - matchPos2))))
              else
                have : data.size - (pos + matchLen) < data.size - pos := by omega
                let c := updateHashesMergedGuarded data hashSize prevSize c pos 1
                  matchLen insertCap
                lz77LazyMergedLoopNoH3Single data windowSize hashSize prevSize maxChain
                  insertCap goodMatch niceLen lazyDepth c (pos + matchLen)
                  (acc.push (packTok (.reference matchLen (pos - matchPos))))
            else
              have : data.size - (pos + matchLen) < data.size - pos := by omega
              let c := updateHashesMergedGuarded data hashSize prevSize c pos 1
                matchLen insertCap
              lz77LazyMergedLoopNoH3Single data windowSize hashSize prevSize maxChain
                insertCap goodMatch niceLen lazyDepth c (pos + matchLen)
                (acc.push (packTok (.reference matchLen (pos - matchPos))))
          else
            have : data.size - (pos + matchLen) < data.size - pos := by omega
            let c := updateHashesMergedGuarded data hashSize prevSize c pos 1
              matchLen insertCap
            lz77LazyMergedLoopNoH3Single data windowSize hashSize prevSize maxChain
              insertCap goodMatch niceLen lazyDepth c (pos + matchLen)
              (acc.push (packTok (.reference matchLen (pos - matchPos))))
        else
          have : data.size - (pos + matchLen) < data.size - pos := by omega
          lz77LazyMergedLoopNoH3Single data windowSize hashSize prevSize maxChain
            insertCap goodMatch niceLen lazyDepth c (pos + matchLen)
            (acc.push (packTok (.reference matchLen (pos - matchPos))))
      else
        have : data.size - (pos + 1) < data.size - pos := by omega
        lz77LazyMergedLoopNoH3Single data windowSize hashSize prevSize maxChain
          insertCap goodMatch niceLen lazyDepth c (pos + 1)
          (acc.push (packTok (.literal (data[pos]'(by omega)))))
    else
      have : data.size - (pos + 1) < data.size - pos := by omega
      lz77LazyMergedLoopNoH3Single data windowSize hashSize prevSize maxChain
        insertCap goodMatch niceLen lazyDepth c (pos + 1)
        (acc.push (packTok (.literal (data[pos]'(by omega)))))
  else
    trailingPT data pos acc
termination_by data.size - pos
decreasing_by all_goals assumption

/-- Large-input L5 entry: builds the combined `prevSize + hashSize` array and
    runs the no-H3/single-deferral loop at L5's fixed chain depths (22 / 5).
    `lzMatchP` selects this entry only under `useL5LargeInputPolicy`. -/
def lz77ChainLazyIterPMergedL5Large (data : ByteArray) (windowSize : Nat := 32768)
    (insertCap : Nat := 1000000000) (goodMatch : Nat := 64) (niceLen : Nat := 65) :
    TokenArray :=
  if data.size < 3 then
    trailingPT data 0 TokenArray.empty
  else
    let hashSize := 65536
    let prevSize := min chainWinSize data.size
    lz77LazyMergedLoopNoH3Single data windowSize hashSize prevSize 22
      insertCap goodMatch niceLen 5
      (.replicate (prevSize + hashSize) data.size) 0
      (TokenArray.emptyWithCapacity data.size)

end Zip.Native.Deflate
