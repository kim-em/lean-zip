import Zip.Native.DeflateFreqsFused
import Zip.Spec.DeflateFreqsAdditive
import Zip.Spec.LZ77MergedCorrect

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

/-- The fixed level-one native hash is exactly the generic 65536-bucket hash.
    Its omitted modulus is inert because the shifted `UInt32` already fits in
    16 bits. -/
private theorem hash3L1U_toNat_eq (data : ByteArray) (dataSizeU pU : USize)
    (hds : dataSizeU.toNat = data.size)
    (hfit : data.size * 512 + 511 < USize.size)
    (hp : pU.toNat + 2 < data.size) :
    (hash3L1U data dataSizeU pU hds hfit hp).toNat =
      lz77Greedy.hash3 data pU.toNat 65536 hp := by
  have hUS : USize.size = 2 ^ System.Platform.numBits := rfl
  have hsz : data.size < USize.size := by omega
  have hround : data.size.toUSize.toNat = data.size := toUSize_toNat_of_lt hsz
  have h4v : (4 : USize).toNat = 4 :=
    USize.toNat_ofNat_of_lt (Nat.lt_of_lt_of_le (by decide) USize.le_size)
  have ep4 : (pU + 4).toNat = pU.toNat + 4 := by
    rw [USize.toNat_add, h4v]
    apply Nat.mod_eq_of_lt
    omega
  have h4iff : pU + 4 ≤ dataSizeU ↔ pU.toNat + 4 ≤ data.size := by
    rw [USize.le_iff_toNat_le, ep4, hds]
  have hpUeq : pU.toNat.toUSize = pU := USize.ofNat_toNat
  have hhigh (word : UInt32) : ((word * 0x1E35A7BD) >>> 16).toNat < 65536 := by
    rw [UInt32.toNat_shiftRight, show ((16 : UInt32).toNat % 32) = 16 from rfl]
    have := UInt32.toNat_lt (word * 0x1E35A7BD)
    omega
  unfold hash3L1U lz77Greedy.hash3
  by_cases h4 : pU.toNat + 4 ≤ data.size
  · rw [dif_pos (h4iff.mpr h4), dif_pos h4, dif_pos hround]
    simp only [hpUeq, UInt32.toNat_toUSize, Nat.mod_eq_of_lt (hhigh _)]
  · rw [dif_neg (fun h => h4 (h4iff.mp h)), dif_neg h4,
      UInt32.toNat_toUSize, Nat.mod_eq_of_lt (hhigh _)]

/-- One native cap-2 insertion is the corresponding guarded `Nat` insertion
    step, before the latter's recursive call. -/
private theorem insertHashL1U_eq (data : ByteArray) (prevSize pos j : Nat)
    (dataSizeU prevSizeU posU jU : USize) (c : Array Nat)
    (hds : dataSizeU.toNat = data.size) (hpsU : prevSizeU.toNat = prevSize)
    (hposU : posU.toNat = pos) (hjU : jU.toNat = j)
    (hfit : data.size * 512 + 511 < USize.size)
    (hprev : prevSize ≤ chainWinSize)
    (hcs : prevSize + 65536 ≤ c.size) (hpos : posU.toNat ≤ data.size)
    (hj : jU.toNat ≤ 2) :
    (insertHashL1U data prevSize dataSizeU prevSizeU posU jU c
      hds hpsU hfit hprev hcs hpos hj).val =
      if h : pos + j + 2 < data.size then
        let hsh := lz77Greedy.hash3 data (pos + j) 65536 h
        let head := c[prevSize + hsh]!
        (c.set! (prevSize + hsh) (pos + j)).set! ((pos + j) &&& 0x7FFF) head
      else c := by
  have hUS : USize.size = 2 ^ System.Platform.numBits := rfl
  have h2 : (2 : USize).toNat = 2 :=
    USize.toNat_ofNat_of_lt (Nat.lt_of_lt_of_le (by decide) USize.le_size)
  have epj : (posU + jU).toNat = pos + j := by
    rw [USize.toNat_add, hposU, hjU]
    apply Nat.mod_eq_of_lt
    omega
  have epj2 : (posU + jU + 2).toNat = pos + j + 2 := by
    rw [USize.toNat_add, epj, h2]
    apply Nat.mod_eq_of_lt
    omega
  have hcond : posU + jU + 2 < dataSizeU ↔ pos + j + 2 < data.size := by
    rw [USize.lt_iff_toNat_lt, epj2, hds]
  unfold insertHashL1U
  by_cases hd : pos + j + 2 < data.size
  · rw [dif_pos (hcond.mpr hd), dif_pos hd]
    have hhash := hash3L1U_toNat_eq data dataSizeU (posU + jU) hds hfit (by rw [epj]; omega)
    have hhash' :
        (hash3L1U data dataSizeU (posU + jU) hds hfit (by rw [epj]; omega)).toNat =
          lz77Greedy.hash3 data (pos + j) 65536 hd := by
      simpa only [epj] using hhash
    have eidx :
        (prevSizeU + hash3L1U data dataSizeU (posU + jU) hds hfit (by rw [epj]; omega)).toNat =
          prevSize + lz77Greedy.hash3 data (pos + j) 65536 hd := by
      have hh := hash3L1U_toNat_lt data dataSizeU (posU + jU) hds hfit (by rw [epj]; omega)
      simp only [chainWinSize] at hprev
      have hsum : prevSize +
          (hash3L1U data dataSizeU (posU + jU) hds hfit (by rw [epj]; omega)).toNat <
          USize.size := Nat.lt_of_lt_of_le (by omega) USize.le_size
      rw [USize.toNat_add, hpsU, Nat.mod_eq_of_lt hsum, hhash']
    have emask : ((posU + jU) &&& 0x7FFF).toNat = (pos + j) &&& 0x7FFF := by
      rw [USize.toNat_and,
        USize.toNat_ofNat_of_lt (Nat.lt_of_lt_of_le (by decide) USize.le_size), epj]
    have eget : ∀ (a : Array Nat) (i : Nat) (h : i < a.size), a[i]'h = a[i]! :=
      fun a i h => (getElem!_pos a i h).symm
    have eset : ∀ (a : Array Nat) (i v : Nat) (h : i < a.size),
        a.set i v h = a.set! i v := fun a i v h => by
      rw [Array.set!_eq_setIfInBounds, Array.setIfInBounds, dif_pos h]
    simp only [Array.uget, Array.uset, eset, eget, eidx, emask, epj]
  · rw [dif_neg (fun h => hd (hcond.mp h)), dif_neg hd]

/-- For a reference (`matchLen ≥ 3`), the two fixed level-one insertions are
    exactly the generic `j = 1`, cap-2 merged update. -/
private theorem insertHashL1U_cap2_eq (data : ByteArray) (prevSize : Nat)
    (dataSizeU prevSizeU posU : USize) (c : Array Nat)
    (hds : dataSizeU.toNat = data.size) (hpsU : prevSizeU.toNat = prevSize)
    (hfit : data.size * 512 + 511 < USize.size)
    (hprev : prevSize ≤ chainWinSize)
    (hcs : prevSize + 65536 ≤ c.size) (hpos : posU.toNat ≤ data.size)
    (matchLen : Nat) (hml : 3 ≤ matchLen) :
    let c1 := insertHashL1U data prevSize dataSizeU prevSizeU posU 1 c
      hds hpsU hfit hprev hcs hpos (by rw [USize.toNat_one]; omega)
    let hc1s : prevSize + 65536 ≤ c1.val.size := by rw [c1.property]; exact hcs
    let c2 := insertHashL1U data prevSize dataSizeU prevSizeU posU 2 c1.val
      hds hpsU hfit hprev hc1s hpos (by
        rw [USize.toNat_ofNat]
        exact Nat.le_of_eq (Nat.mod_eq_of_lt
          (Nat.lt_of_lt_of_le (by decide) USize.le_size)))
    c2.val = updateHashesMergedGuarded data 65536 prevSize c posU.toNat 1 matchLen 2 := by
  let c1 := insertHashL1U data prevSize dataSizeU prevSizeU posU 1 c
    hds hpsU hfit hprev hcs hpos (by rw [USize.toNat_one]; omega)
  have hc1s : prevSize + 65536 ≤ c1.val.size := by rw [c1.property]; exact hcs
  let c2 := insertHashL1U data prevSize dataSizeU prevSizeU posU 2 c1.val
    hds hpsU hfit hprev hc1s hpos (by
      rw [USize.toNat_ofNat]
      exact Nat.le_of_eq (Nat.mod_eq_of_lt
        (Nat.lt_of_lt_of_le (by decide) USize.le_size)))
  change c2.val = _
  have hc1eq := insertHashL1U_eq data prevSize posU.toNat 1 dataSizeU prevSizeU posU 1 c
    hds hpsU rfl USize.toNat_one hfit hprev hcs hpos (by rw [USize.toNat_one]; omega)
  have h2nat : (2 : USize).toNat = 2 :=
    USize.toNat_ofNat_of_lt (Nat.lt_of_lt_of_le (by decide) USize.le_size)
  have hc2eq := insertHashL1U_eq data prevSize posU.toNat 2 dataSizeU prevSizeU posU 2 c1.val
    hds hpsU rfl h2nat hfit hprev hc1s hpos (by rw [h2nat]; omega)
  rw [updateHashesMergedGuarded_eq]
  rw [hc2eq, hc1eq]
  by_cases h1 : posU.toNat + 1 + 2 < data.size <;>
    by_cases h2 : posU.toNat + 2 + 2 < data.size <;>
      simp only [h1, h2, ↓reduceDIte]
  all_goals
    rw [updateHashesMerged, if_pos (by omega)]
    simp only [h1, ↓reduceDIte]
    rw [updateHashesMerged, if_pos (by omega)]
    simp only [h2, ↓reduceDIte]
    rw [updateHashesMerged, if_neg (by omega)]
  all_goals
    simp only [headProbeGuarded_eq, guardedSet_eq, Nat.reduceAdd]

/-- Updating an in-bounds array slot with a bounded value preserves a pointwise
    bound on every slot. -/
private theorem array_getElem_le_set! (a : Array Nat) (bound i v : Nat)
    (ha : ∀ k, k < a.size → a[k]! ≤ bound) (hi : i < a.size) (hv : v ≤ bound) :
    ∀ k, k < (a.set! i v).size → (a.set! i v)[k]! ≤ bound := by
  intro k hk
  have hk' : k < a.size := by rwa [Array.size_set!] at hk
  by_cases hki : k = i
  · subst k
    rw [Array.getElem!_set!_self _ _ _ hi]
    exact hv
  · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hki)]
    exact ha k hk'

/-- One native interior insertion preserves the invariant that every stored
    chain/hash position lies in the input. -/
private theorem insertHashL1U_bounded (data : ByteArray) (prevSize : Nat)
    (dataSizeU prevSizeU posU jU : USize) (c : Array Nat)
    (hds : dataSizeU.toNat = data.size) (hpsU : prevSizeU.toNat = prevSize)
    (hfit : data.size * 512 + 511 < USize.size)
    (hprev : prevSize ≤ chainWinSize)
    (hcs : prevSize + 65536 ≤ c.size) (hpos : posU.toNat ≤ data.size)
    (hj : jU.toNat ≤ 2)
    (hc : ∀ i, i < c.size → c[i]! ≤ data.size) :
    ∀ i, i < (insertHashL1U data prevSize dataSizeU prevSizeU posU jU c
      hds hpsU hfit hprev hcs hpos hj).val.size →
      (insertHashL1U data prevSize dataSizeU prevSizeU posU jU c
        hds hpsU hfit hprev hcs hpos hj).val[i]! ≤ data.size := by
  rw [insertHashL1U_eq data prevSize posU.toNat jU.toNat dataSizeU prevSizeU posU jU c
    hds hpsU rfl rfl hfit hprev hcs hpos hj]
  split
  · rename_i hd
    have hh : lz77Greedy.hash3 data (posU.toNat + jU.toNat) 65536 hd < 65536 :=
      Nat.mod_lt _ (by omega)
    have hidx : prevSize + lz77Greedy.hash3 data (posU.toNat + jU.toNat) 65536 hd < c.size :=
      by omega
    have hmask : (posU.toNat + jU.toNat) &&& 0x7FFF < c.size := by
      have hm := winMask_lt (posU.toNat + jU.toNat)
      simp only [chainWinSize] at hprev hm
      omega
    apply array_getElem_le_set! _ _ _ _
    · exact array_getElem_le_set! c data.size _ _ hc hidx (by omega)
    · rwa [Array.size_set!]
    · exact hc _ hidx
   · exact hc

/-- Congruence for functions whose second argument proves a bound on the first.
    Keeping this transport opaque prevents large callers from inlining the
    dependent equality proof. -/
private theorem dependentUSizeBound_congr {n : Nat} {α : Sort u}
    (f : (p : USize) → p.toNat ≤ n → α) {p q : USize}
    (hp : p.toNat ≤ n) (hq : q.toNat ≤ n) (h : p = q) :
    f p hp = f q hq := by
  subst q
  rfl

private theorem dependentArrayBound_congr {n : Nat} {α : Sort u}
    (f : (a : Array Nat) → n ≤ a.size → α) {a b : Array Nat}
    (ha : n ≤ a.size) (hb : n ≤ b.size) (h : a = b) :
    f a ha = f b hb := by
  subst b
  rfl

private theorem congrArgOpaque {α : Sort u} {β : Sort v} (f : α → β)
    {a b : α} (h : a = b) : f a = f b := by
  subst b
  rfl

private theorem eqTrans3Opaque {α : Sort u} {a b c d : α}
    (hab : a = b) (hbc : b = c) (hcd : c = d) : a = d := by
  exact hab.trans (hbc.trans hcd)

/- The reference branch is deliberately an opaque declaration of its own.
   Besides keeping the outer strong-recursion term small, this keeps the
   cap-two insertion proof and the dependent recursive-call transports out of
   the kernel term for the common one-step normalization. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 200000 in
private theorem lz77GreedyMergedLoopF1U_reference_step
    (data : ByteArray) (prevSize : Nat) (dataSizeU prevSizeU : USize)
    (hds : dataSizeU.toNat = data.size) (hpsU : prevSizeU.toNat = prevSize)
    (hsz : data.size < USize.size) (hfit : data.size * 512 + 511 < USize.size)
    (hpv : min chainWinSize data.size ≤ prevSize) (hprev : prevSize ≤ chainWinSize)
    (cRing cRingS : Array Nat) (ecRingS : cRingS = cRing)
    (hcsRing : prevSize + 65536 ≤ cRing.size)
    (hcRing : ∀ i, i < cRing.size → cRing[i]! ≤ data.size)
    (posU : USize) (hpos : posU.toNat ≤ data.size)
    (acc : TokenArray)
    (litF : {a : Array Nat // a.size = 286}) (distF : {a : Array Nat // a.size = 30})
    (maxLen head : Nat) (hmax258 : maxLen ≤ 258)
    (hpmN : posU.toNat + maxLen ≤ data.size)
    (rRaw rU : USize) (erRaw : rRaw = rU) (walk : Nat)
    (hwalkEq : walk = chainWalkGuardedPackedU data cRing 32768 posU.toNat
      maxLen 258 hpmN head 4 0 0)
    (hlow : (rU &&& 0x1FF).toNat = walk % 512)
    (hhigh : (rU >>> 9).toNat = walk / 512)
    (hgeCommon : walk % 512 ≥ 3)
    (hleCommon : posU.toNat + walk % 512 ≤ data.size)
    (hsum : (posU + (rU &&& 0x1FF)).toNat = posU.toNat + walk % 512)
    (h2 : (2 : USize).toNat = 2)
    (n : Nat) (hn : data.size - posU.toNat = n)
    (ih : ∀ (m : Nat), m < n →
      ∀ (c' : Array Nat) (hcs' : prevSize + 65536 ≤ c'.size)
        (posU' : USize) (hpos' : posU'.toNat ≤ data.size),
      (∀ i, i < c'.size → c'[i]! ≤ data.size) →
      ∀ (acc' : TokenArray)
        (litF' : {a : Array Nat // a.size = 286})
        (distF' : {a : Array Nat // a.size = 30}),
        data.size - posU'.toNat = m →
        lz77GreedyMergedLoopF1U data prevSize dataSizeU prevSizeU hds hpsU hsz hfit
            hpv hprev c' hcs' posU' hpos' acc' litF' distF' =
          lz77GreedyMergedLoopF data 32768 65536 prevSize 4 2 258
            c' posU'.toNat acc' litF' distF') :
    let hcsRingS : prevSize + 65536 ≤ cRingS.size := by
      rw [ecRingS]
      exact hcsRing
    let c1 := insertHashL1U data prevSize dataSizeU prevSizeU posU 1 cRingS
      hds hpsU hfit hprev hcsRingS hpos (by rw [USize.toNat_one]; omega)
    let hc1s : prevSize + 65536 ≤ c1.val.size := by
      rw [c1.property]
      exact hcsRingS
    let c2 := insertHashL1U data prevSize dataSizeU prevSizeU posU 2 c1.val
      hds hpsU hfit hprev hc1s hpos (by rw [h2]; omega)
    let hc2s : prevSize + 65536 ≤ c2.val.size := by
      rw [c2.property]
      exact hc1s
    let nextRaw := posU + (rRaw &&& 0x1FF)
    let hrawBound : nextRaw.toNat ≤ data.size := by
      simp only [nextRaw, erRaw]
      rw [hsum]
      exact hleCommon
    let wRaw := packTok (.reference (rRaw &&& 0x1FF).toNat
      (posU - (rRaw >>> 9)).toNat)
    let updated := updateHashesMergedGuarded data 65536 prevSize cRing
      posU.toNat 1 (walk % 512) 2
    let wN := packTok (.reference (walk % 512) (posU.toNat - walk / 512))
    lz77GreedyMergedLoopF1U data prevSize dataSizeU prevSizeU hds hpsU hsz hfit
        hpv hprev c2.val hc2s nextRaw hrawBound
        (acc.push wRaw) (bumpRefLitFreqP litF wRaw) (bumpRefDistFreqP distF wRaw) =
      lz77GreedyMergedLoopF data 32768 65536 prevSize 4 2 258 updated
        (posU.toNat + walk % 512) (acc.push wN)
        (bumpRefLitFreqP litF wN) (bumpRefDistFreqP distF wN) := by
  simp only
  let q := lz77Chain.chainWalk data cRing 32768 posU.toNat maxLen 258
    hpmN head 4 0 0
  have hq := chainWalk_spec data cRing 32768 posU.toNat maxLen 258
    hpmN head 4 0 0 (Or.inl rfl)
  have hmod : walk % 512 = q.1 := by
    rw [hwalkEq]
    unfold q
    rw [chainWalkGuardedPackedU_eq,
      chainWalkGuardedPacked_mod data cRing 32768 posU.toNat maxLen 258
        hpmN head 4 (by omega)]
  have hdiv : walk / 512 = q.2 := by
    rw [hwalkEq]
    unfold q
    rw [chainWalkGuardedPackedU_eq,
      chainWalkGuardedPacked_div data cRing 32768 posU.toNat maxLen 258
        hpmN head 4 (by omega)]
  have hposWalk : walk / 512 < posU.toNat := by
    obtain hzero | hgood := hq
    · have hz : q.1 = 0 := by simpa only [q] using hzero
      rw [hmod] at hgeCommon
      omega
    · rw [hdiv]
      exact hgood.1
  have hposHigh : rU >>> 9 ≤ posU := by
    rw [USize.le_iff_toNat_le, hhigh]
    omega
  have hdist : (posU - (rU >>> 9)).toNat = posU.toNat - walk / 512 := by
    rw [USize.toNat_sub_of_le _ _ hposHigh, hhigh]
  have hmlU : 3 ≤ (rU &&& 0x1FF).toNat := by
    rw [hlow]
    exact hgeCommon
  have hcsRingS : prevSize + 65536 ≤ cRingS.size := by
    rw [ecRingS]
    exact hcsRing
  have hcRingS : ∀ i, i < cRingS.size → cRingS[i]! ≤ data.size := by
    rw [ecRingS]
    exact hcRing
  let c1 := insertHashL1U data prevSize dataSizeU prevSizeU posU 1 cRingS
    hds hpsU hfit hprev hcsRingS hpos (by rw [USize.toNat_one]; omega)
  have hc1s : prevSize + 65536 ≤ c1.val.size := by rw [c1.property]; exact hcsRingS
  have hc1b : ∀ i, i < c1.val.size → c1.val[i]! ≤ data.size :=
    insertHashL1U_bounded data prevSize dataSizeU prevSizeU posU 1 cRingS
      hds hpsU hfit hprev hcsRingS hpos (by rw [USize.toNat_one]; omega) hcRingS
  let c2 := insertHashL1U data prevSize dataSizeU prevSizeU posU 2 c1.val
    hds hpsU hfit hprev hc1s hpos (by rw [h2]; omega)
  have hc2s : prevSize + 65536 ≤ c2.val.size := by rw [c2.property]; exact hc1s
  have hc2b : ∀ i, i < c2.val.size → c2.val[i]! ≤ data.size :=
    insertHashL1U_bounded data prevSize dataSizeU prevSizeU posU 2 c1.val
      hds hpsU hfit hprev hc1s hpos (by rw [h2]; omega) hc1b
  have hc12 : c2.val = updateHashesMergedGuarded data 65536 prevSize cRing
      posU.toNat 1 (walk % 512) 2 := by
    calc
      c2.val = updateHashesMergedGuarded data 65536 prevSize cRingS
          posU.toNat 1 (rU &&& 0x1FF).toNat 2 := by
        dsimp only [c2, c1]
        exact insertHashL1U_cap2_eq data prevSize dataSizeU prevSizeU posU cRingS
          hds hpsU hfit hprev hcsRingS hpos (rU &&& 0x1FF).toNat hmlU
      _ = updateHashesMergedGuarded data 65536 prevSize cRing
          posU.toNat 1 (rU &&& 0x1FF).toNat 2 := by rw [ecRingS]
      _ = _ := by rw [hlow]
  let nextU := posU + (rU &&& 0x1FF)
  have hnext : nextU.toNat = posU.toNat + walk % 512 := hsum
  let w := packTok (.reference (walk % 512) (posU - (rU >>> 9)).toNat)
  let wN := packTok (.reference (walk % 512) (posU.toNat - walk / 512))
  have ew : w = wN := by simp only [w, wN, hdist]
  let nextRaw := posU + (rRaw &&& 0x1FF)
  have enextRaw : nextRaw = nextU := by simp only [nextRaw, nextU, erRaw]
  let wRaw := packTok (.reference (rRaw &&& 0x1FF).toNat
    (posU - (rRaw >>> 9)).toNat)
  have ewRaw : wRaw = wN := by
    simp only [wRaw, wN, erRaw, hlow, hdist]
  have hnextBound : nextU.toNat ≤ data.size := by rw [hnext]; exact hleCommon
  have hrawBound : nextRaw.toNat ≤ data.size := by
    rw [enextRaw]
    exact hnextBound
  let updated := updateHashesMergedGuarded data 65536 prevSize cRing
    posU.toNat 1 (walk % 512) 2
  have hupdatedSize : prevSize + 65536 ≤ updated.size := by
    dsimp only [updated]
    rw [← hc12]
    exact hc2s
  have hi := ih (data.size - nextU.toNat) (by rw [hnext, ← hn]; omega)
    c2.val hc2s nextU hnextBound hc2b
    (acc.push w) (bumpRefLitFreqP litF w) (bumpRefDistFreqP distF w) rfl
  simp only [hc12, hnext, ew] at hi
  have hcall := dependentUSizeBound_congr
    (fun p hp =>
      lz77GreedyMergedLoopF1U data prevSize dataSizeU prevSizeU hds hpsU hsz
        hfit hpv hprev updated hupdatedSize p hp
        (acc.push wRaw) (bumpRefLitFreqP litF wRaw) (bumpRefDistFreqP distF wRaw))
    hrawBound hnextBound enextRaw
  change
    lz77GreedyMergedLoopF1U data prevSize dataSizeU prevSizeU hds hpsU hsz hfit
        hpv hprev updated hupdatedSize nextRaw hrawBound
        (acc.push wRaw) (bumpRefLitFreqP litF wRaw) (bumpRefDistFreqP distF wRaw) =
      lz77GreedyMergedLoopF1U data prevSize dataSizeU prevSizeU hds hpsU hsz hfit
        hpv hprev updated hupdatedSize nextU hnextBound
        (acc.push wRaw) (bumpRefLitFreqP litF wRaw) (bumpRefDistFreqP distF wRaw) at hcall
  have htoken := congrArgOpaque
    (fun z =>
      lz77GreedyMergedLoopF1U data prevSize dataSizeU prevSizeU hds hpsU hsz
        hfit hpv hprev updated hupdatedSize nextU hnextBound
        (acc.push z) (bumpRefLitFreqP litF z) (bumpRefDistFreqP distF z)) ewRaw
  change
    lz77GreedyMergedLoopF1U data prevSize dataSizeU prevSizeU hds hpsU hsz hfit
        hpv hprev updated hupdatedSize nextU hnextBound
        (acc.push wRaw) (bumpRefLitFreqP litF wRaw) (bumpRefDistFreqP distF wRaw) =
      lz77GreedyMergedLoopF1U data prevSize dataSizeU prevSizeU hds hpsU hsz hfit
        hpv hprev updated hupdatedSize nextU hnextBound
        (acc.push wN) (bumpRefLitFreqP litF wN) (bumpRefDistFreqP distF wN) at htoken
  change
    lz77GreedyMergedLoopF1U data prevSize dataSizeU prevSizeU hds hpsU hsz hfit
        hpv hprev updated hupdatedSize nextU hnextBound
        (acc.push wN) (bumpRefLitFreqP litF wN) (bumpRefDistFreqP distF wN) =
      lz77GreedyMergedLoopF data 32768 65536 prevSize 4 2 258 updated
        (posU.toNat + walk % 512) (acc.push wN)
        (bumpRefLitFreqP litF wN) (bumpRefDistFreqP distF wN) at hi
  change
    lz77GreedyMergedLoopF1U data prevSize dataSizeU prevSizeU hds hpsU hsz hfit
        hpv hprev c2.val hc2s nextRaw hrawBound
        (acc.push wRaw) (bumpRefLitFreqP litF wRaw) (bumpRefDistFreqP distF wRaw) =
      lz77GreedyMergedLoopF data 32768 65536 prevSize 4 2 258 updated
        (posU.toNat + walk % 512) (acc.push wN)
        (bumpRefLitFreqP litF wN) (bumpRefDistFreqP distF wN)
  have hcNative := dependentArrayBound_congr
    (fun z hz =>
      lz77GreedyMergedLoopF1U data prevSize dataSizeU prevSizeU hds hpsU hsz hfit
        hpv hprev z hz nextRaw hrawBound
        (acc.push wRaw) (bumpRefLitFreqP litF wRaw) (bumpRefDistFreqP distF wRaw))
    hc2s hupdatedSize hc12
  change
    lz77GreedyMergedLoopF1U data prevSize dataSizeU prevSizeU hds hpsU hsz hfit
        hpv hprev c2.val hc2s nextRaw hrawBound
        (acc.push wRaw) (bumpRefLitFreqP litF wRaw) (bumpRefDistFreqP distF wRaw) =
      lz77GreedyMergedLoopF1U data prevSize dataSizeU prevSizeU hds hpsU hsz hfit
        hpv hprev updated hupdatedSize nextRaw hrawBound
        (acc.push wRaw) (bumpRefLitFreqP litF wRaw) (bumpRefDistFreqP distF wRaw) at hcNative
  exact hcNative.trans (eqTrans3Opaque hcall htoken hi)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 200000 in
private theorem lz77GreedyMergedLoopF1U_eq_step (data : ByteArray) (prevSize : Nat)
    (dataSizeU prevSizeU : USize)
    (hds : dataSizeU.toNat = data.size) (hpsU : prevSizeU.toNat = prevSize)
    (hsz : data.size < USize.size) (hfit : data.size * 512 + 511 < USize.size)
    (hpv : min chainWinSize data.size ≤ prevSize) (hprev : prevSize ≤ chainWinSize)
    (hshift : data.size.toUSize < ((~~~(0 : USize)) >>> 9))
    (c : Array Nat) (hcs : prevSize + 65536 ≤ c.size)
    (posU : USize) (hpos : posU.toNat ≤ data.size)
    (hc : ∀ i, i < c.size → c[i]! ≤ data.size)
    (acc : TokenArray)
    (litF : {a : Array Nat // a.size = 286}) (distF : {a : Array Nat // a.size = 30})
    (n : Nat) (hn : data.size - posU.toNat = n)
    (ih : ∀ (m : Nat), m < n →
      ∀ (c' : Array Nat) (hcs' : prevSize + 65536 ≤ c'.size)
        (posU' : USize) (hpos' : posU'.toNat ≤ data.size),
      (∀ i, i < c'.size → c'[i]! ≤ data.size) →
      ∀ (acc' : TokenArray)
        (litF' : {a : Array Nat // a.size = 286})
        (distF' : {a : Array Nat // a.size = 30}),
        data.size - posU'.toNat = m →
        lz77GreedyMergedLoopF1U data prevSize dataSizeU prevSizeU hds hpsU hsz hfit
            hpv hprev c' hcs' posU' hpos' acc' litF' distF' =
          lz77GreedyMergedLoopF data 32768 65536 prevSize 4 2 258
            c' posU'.toNat acc' litF' distF') :
    lz77GreedyMergedLoopF1U data prevSize dataSizeU prevSizeU hds hpsU hsz hfit hpv hprev
        c hcs posU hpos acc litF distF =
      lz77GreedyMergedLoopF data 32768 65536 prevSize 4 2 258
        c posU.toNat acc litF distF := by
    rw [lz77GreedyMergedLoopF1U, lz77GreedyMergedLoopF]
    have hUS : USize.size = 2 ^ System.Platform.numBits := rfl
    have h2 : (2 : USize).toNat = 2 :=
      USize.toNat_ofNat_of_lt (Nat.lt_of_lt_of_le (by decide) USize.le_size)
    have ep2 : (posU + 2).toNat = posU.toNat + 2 := by
      rw [USize.toNat_add, h2]
      apply Nat.mod_eq_of_lt
      omega
    have hcond : posU + 2 < dataSizeU ↔ posU.toNat + 2 < data.size := by
      rw [USize.lt_iff_toNat_lt, ep2, hds]
    by_cases hlt : posU.toNat + 2 < data.size
    · rw [dif_pos (hcond.mpr hlt), dif_pos hlt]
      have eget : ∀ (a : Array Nat) (i : Nat) (h : i < a.size), a[i]'h = a[i]! :=
        fun a i h => (getElem!_pos a i h).symm
      have eset : ∀ (a : Array Nat) (i v : Nat) (h : i < a.size),
          a.set i v h = a.set! i v := fun a i v h => by
        rw [Array.set!_eq_setIfInBounds, Array.setIfInBounds, dif_pos h]
      have ehsh : ∀ (hp : posU.toNat + 2 < data.size),
          (hash3L1U data dataSizeU posU hds hfit hp).toNat =
            lz77Greedy.hash3 data posU.toNat 65536 hlt := by
        intro hp
        exact hash3L1U_toNat_eq data dataSizeU posU hds hfit hp
      have eidx : ∀ (hp : posU.toNat + 2 < data.size),
          (prevSizeU + hash3L1U data dataSizeU posU hds hfit hp).toNat =
            prevSize + lz77Greedy.hash3 data posU.toNat 65536 hlt := by
        intro hp
        rw [USize.toNat_add, hpsU, ehsh]
        apply Nat.mod_eq_of_lt
        have hh := hash3L1U_toNat_lt data dataSizeU posU hds hfit hp
        have hh' : lz77Greedy.hash3 data posU.toNat 65536 hlt < 65536 := by
          rw [← ehsh hp]
          exact hh
        simp only [chainWinSize] at hprev
        exact Nat.lt_of_lt_of_le (by omega) USize.le_size
      have emask : (posU &&& 0x7FFF).toNat = posU.toNat &&& 0x7FFF := by
        rw [USize.toNat_and,
          USize.toNat_ofNat_of_lt (Nat.lt_of_lt_of_le (by decide) USize.le_size)]
      let hNat := lz77Greedy.hash3 data posU.toNat 65536 hlt
      have hhNat : hNat < 65536 := Nat.mod_lt _ (by omega)
      have hiNat : prevSize + hNat < c.size := by omega
      let head := c[prevSize + hNat]!
      have hhead : head ≤ data.size := hc _ hiNat
      let cRing := (c.set! (prevSize + hNat) posU.toNat).set!
        (posU.toNat &&& 0x7FFF) head
      have hmask : posU.toNat &&& 0x7FFF < c.size := by
        have hm := winMask_lt posU.toNat
        simp only [chainWinSize] at hprev hm
        omega
      have hcHash : ∀ i, i < (c.set! (prevSize + hNat) posU.toNat).size →
          (c.set! (prevSize + hNat) posU.toNat)[i]! ≤ data.size :=
        array_getElem_le_set! c data.size _ _ hc hiNat hpos
      have hcRing : ∀ i, i < cRing.size → cRing[i]! ≤ data.size := by
        exact array_getElem_le_set! _ data.size _ _ hcHash (by rwa [Array.size_set!]) hhead
      have hcRingSize : cRing.size = c.size := by
        simp only [cRing, Array.size_set!]
      have hcsRing : prevSize + 65536 ≤ cRing.size := by rwa [hcRingSize]
      let hshU := hash3L1U data dataSizeU posU hds hfit hlt
      have hhU : hshU.toNat < 65536 :=
        hash3L1U_toNat_lt data dataSizeU posU hds hfit hlt
      have hidxU : (prevSizeU + hshU).toNat = prevSize + hNat := by
        exact eidx hlt
      have hbU : (prevSizeU + hshU).toNat < c.size := by rwa [hidxU]
      let headNative := c.uget (prevSizeU + hshU) hbU
      have eheadNative : headNative = head := by
        simp only [headNative, Array.uget, eget, hidxU, head, hNat]
      let cHashU := c.uset (prevSizeU + hshU) posU.toNat hbU
      have hmaskU : (posU &&& 0x7FFF).toNat < cHashU.size := by
        simp only [cHashU, Array.size_uset, emask]
        exact hmask
      let cRingU := cHashU.uset (posU &&& 0x7FFF) headNative hmaskU
      have ecRingU : cRingU = cRing := by
        simp only [cRingU, cHashU, Array.uset, eset, hidxU, emask,
          eheadNative, cRing]
      have eheadRaw := eheadNative
      simp only [headNative, hshU, Array.uget] at eheadRaw
      have ecRingRaw := ecRingU
      simp only [cRingU, cHashU, headNative, hshU, Array.uget, Array.uset] at ecRingRaw
      have ecRingRaw' := ecRingRaw
      simp only [eheadRaw] at ecRingRaw'
      have ecRingGuarded :
          guardedSet
              (guardedSet c (prevSize + lz77Greedy.hash3 data posU.toNat 65536 hlt)
                posU.toNat)
              (posU.toNat &&& 0x7FFF)
              c[prevSize + lz77Greedy.hash3 data posU.toNat 65536 hlt]! = cRing := by
        simp only [guardedSet_eq, cRing, hNat, head]
      have hposLe : posU ≤ dataSizeU := by
        rw [USize.le_iff_toNat_le, hds]
        exact hpos
      let remU := dataSizeU - posU
      have hremN : remU.toNat = data.size - posU.toNat := by
        unfold remU
        rw [USize.toNat_sub_of_le _ _ hposLe, hds]
      let maxLenU := if remU < 258 then remU else 258
      let maxLen := min 258 (data.size - posU.toNat)
      have h258 : (258 : USize).toNat = 258 :=
        USize.toNat_ofNat_of_lt (Nat.lt_of_lt_of_le (by decide) USize.le_size)
      have hmaxN : maxLenU.toNat = maxLen := by
        unfold maxLenU maxLen
        split
        · rename_i hr
          have hrN := USize.lt_iff_toNat_lt.mp hr
          rw [h258, hremN] at hrN
          rw [Nat.min_eq_right (by omega)]
          exact hremN
        · rename_i hr
          have hrN : 258 ≤ remU.toNat := by
            rw [← h258]
            exact Nat.le_of_not_lt (fun hh => hr (USize.lt_iff_toNat_lt.mpr hh))
          rw [hremN] at hrN
          rw [Nat.min_eq_left hrN]
          exact h258
      have hmax258 : maxLen ≤ 258 := by simp only [maxLen]; omega
      have hmaxVal : maxLen.toUSize = maxLenU := by
        apply USize.toNat_inj.mp
        rw [toUSize_toNat_of_lt (by omega), hmaxN]
      have hmaxValRev' := hmaxVal.symm
      simp only [maxLenU, remU, maxLen] at hmaxValRev'
      have hpmN : posU.toNat + maxLen ≤ data.size := by
        simp only [maxLen]
        omega
      have hwalk : min chainWinSize data.size ≤ cRing.size := by omega
      have hdataRound : data.size.toUSize.toNat = data.size :=
        toUSize_toNat_of_lt hsz
      have hwinRound : (32768 : Nat).toUSize.toNat = 32768 :=
        toUSize_toNat_of_lt (Nat.lt_of_lt_of_le (by decide) USize.le_size)
      have hheadRound : head.toUSize.toNat = head :=
        toUSize_toNat_of_lt (by omega)
      have hfourRound : (4 : Nat).toUSize.toNat = 4 :=
        toUSize_toNat_of_lt (Nat.lt_of_lt_of_le (by decide) USize.le_size)
      have hg : chainWalkPackedUUSafe data cRing 32768 maxLen head 4 :=
        ⟨hwalk, hdataRound, hwinRound, hheadRound, hfourRound, by omega, hshift⟩
      let rU := chainWalkPackedUU data cRing hwalk hsz 32768 posU maxLenU maxLenU
        head.toUSize 4 0 0 (by rw [hmaxN]; exact hpmN)
      have erUNorm : chainWalkPackedUU data cRing hwalk hsz 32768 posU
          maxLen.toUSize maxLen.toUSize head.toUSize 4 0 0
            (by rw [toUSize_toNat_of_lt (by omega)]; exact hpmN) = rU := by
        simp only [rU, hmaxVal]
      let rC := chainWalkPackedUUChecked data cRing 32768 posU.toNat maxLen 258
        hpmN head 4 hg
      have hrEq : rU = rC := by
        simp only [rU, rC, chainWalkPackedUUChecked, USize.ofNat_toNat,
          hmaxVal, Nat.min_eq_right hmax258]
        congr
      let walk := chainWalkGuardedPackedU data cRing 32768 posU.toNat maxLen 258
        hpmN head 4 0 0
      have hlow : (rU &&& 0x1FF).toNat = walk % 512 := by
        rw [hrEq]
        exact chainWalkPackedUUChecked_low data cRing 32768 posU.toNat maxLen 258
          hpmN head 4 hg
      have hhigh : (rU >>> 9).toNat = walk / 512 := by
        rw [hrEq]
        exact chainWalkPackedUUChecked_high data cRing 32768 posU.toNat maxLen 258
          hpmN head 4 hg
      have hmatchLe : walk % 512 ≤ maxLen := by
        unfold walk
        rw [chainWalkGuardedPackedU_eq,
          chainWalkGuardedPacked_mod data cRing 32768 posU.toNat maxLen 258 hpmN head 4
            (by omega)]
        exact chainWalk_fst_le data cRing 32768 posU.toNat maxLen 258 hpmN head 4
      simp only [Array.uget, Array.uset, eheadRaw, ecRingRaw', headProbeGuarded_eq,
        ecRingGuarded, hmaxValRev',
        chainWalkPackedUUChecked_low, chainWalkPackedUUChecked_high]
      have hthree : (3 : USize).toNat = 3 :=
        USize.toNat_ofNat_of_lt (Nat.lt_of_lt_of_le (by decide) USize.le_size)
      have hgeIff : (rU &&& 0x1FF) ≥ 3 ↔ walk % 512 ≥ 3 := by
        rw [ge_iff_le, USize.le_iff_toNat_le, hthree, hlow, ge_iff_le]
      split
      · rename_i hgeU
        have hgeU0 : (rU &&& 0x1FF) ≥ 3 := by
          simpa only [rU, cRing, maxLenU, remU, head, hNat, hmaxValRev'] using hgeU
        have hgeCommon : walk % 512 ≥ 3 := hgeIff.mp hgeU0
        have hleCommon : posU.toNat + walk % 512 ≤ data.size := by omega
        have hsum : (posU + (rU &&& 0x1FF)).toNat =
            posU.toNat + walk % 512 := by
          rw [USize.toNat_add, hlow]
          apply Nat.mod_eq_of_lt
          omega
        have hleU0 : posU + (rU &&& 0x1FF) ≤ dataSizeU := by
          rw [USize.le_iff_toNat_le, hsum, hds]
          omega
        have hleU' := hleU0
        simp only [rU, cRing, maxLenU, remU, head, hNat, hmaxValRev'] at hleU'
        split
        · rename_i _hleU
          have hmaskS : (posU &&& 0x7FFF).toNat <
              (c.set (prevSizeU + hshU).toNat posU.toNat hbU).size := by
            rw [Array.size_set]
            rw [emask]
            exact hmask
          let cRingS := (c.set (prevSizeU + hshU).toNat posU.toNat hbU).set
            (posU &&& 0x7FFF).toNat (c[(prevSizeU + hshU).toNat]'hbU) hmaskS
          have ecRingS : cRingS = cRing := by
            calc
              cRingS = cRingU := by rfl
              _ = cRing := ecRingU
          let rRaw := chainWalkPackedUU data
                ((c.set! (prevSize + lz77Greedy.hash3 data posU.toNat 65536 hlt)
                    posU.toNat).set! (posU.toNat &&& 0x7FFF)
                  c[prevSize + lz77Greedy.hash3 data posU.toNat 65536 hlt]!)
                hwalk hsz 32768 posU maxLen.toUSize maxLen.toUSize head.toUSize
                4 0 0 (by rw [toUSize_toNat_of_lt (by omega)]; exact hpmN)
          have erRaw : rRaw = rU := by
            simp only [rRaw]
            exact erUNorm
          exact lz77GreedyMergedLoopF1U_reference_step
            (data := data) (prevSize := prevSize) (dataSizeU := dataSizeU)
            (prevSizeU := prevSizeU) (hds := hds) (hpsU := hpsU)
            (hsz := hsz) (hfit := hfit) (hpv := hpv) (hprev := hprev)
            (cRing := cRing) (cRingS := cRingS) (ecRingS := ecRingS)
            (hcsRing := hcsRing) (hcRing := hcRing) (posU := posU) (hpos := hpos)
            (acc := acc) (litF := litF) (distF := distF) (maxLen := maxLen)
            (head := head) (hmax258 := hmax258) (hpmN := hpmN)
            (rRaw := rRaw) (rU := rU)
            (erRaw := erRaw) (walk := walk) (hwalkEq := rfl) (hlow := hlow)
            (hhigh := hhigh) (hgeCommon := hgeCommon) (hleCommon := hleCommon)
            (hsum := hsum) (h2 := h2) (n := n) (hn := hn) (ih := ih)
        · rename_i hleU
          exact absurd hleU' hleU
      · rename_i hgeU
        have hnCommon : ¬ walk % 512 ≥ 3 := by
          intro hh
          apply hgeU
          have := hgeIff.mpr hh
          simpa only [rU, cRing, maxLenU, remU, head, hNat, hmaxValRev'] using this
        split
        · rename_i hgeN
          exact absurd (by
            simpa only [walk, cRing, maxLen, head, hNat] using hgeN) hnCommon
        · simp only [uget_eq_getElem]
          have hnext : (posU + 1).toNat = posU.toNat + 1 := by
            rw [USize.toNat_add, USize.toNat_one]
            apply Nat.mod_eq_of_lt
            omega
          let w := packTok (.literal data[posU.toNat])
          have hi := ih (data.size - (posU + 1).toNat) (by rw [hnext, ← hn]; omega)
            cRing hcsRing (posU + 1) (by rw [hnext]; omega) hcRing
            (acc.push w) (bumpLitFreqP litF w) distF rfl
          simpa only [hnext] using hi
    · rw [dif_neg (fun h => hlt (hcond.mp h)), dif_neg hlt]

set_option maxRecDepth 100000 in
/-- The level-one native-word outer loop is the fixed-policy generic fused
    loop.  The pointwise state invariant is proof-only; it witnesses that every
    `Nat` chain head converted to `USize` round-trips exactly. -/
theorem lz77GreedyMergedLoopF1U_eq (data : ByteArray) (prevSize : Nat)
    (dataSizeU prevSizeU : USize)
    (hds : dataSizeU.toNat = data.size) (hpsU : prevSizeU.toNat = prevSize)
    (hsz : data.size < USize.size) (hfit : data.size * 512 + 511 < USize.size)
    (hpv : min chainWinSize data.size ≤ prevSize) (hprev : prevSize ≤ chainWinSize)
    (hshift : data.size.toUSize < ((~~~(0 : USize)) >>> 9))
    (c : Array Nat) (hcs : prevSize + 65536 ≤ c.size)
    (posU : USize) (hpos : posU.toNat ≤ data.size)
    (hc : ∀ i, i < c.size → c[i]! ≤ data.size)
    (acc : TokenArray)
    (litF : {a : Array Nat // a.size = 286}) (distF : {a : Array Nat // a.size = 30}) :
    lz77GreedyMergedLoopF1U data prevSize dataSizeU prevSizeU hds hpsU hsz hfit hpv hprev
        c hcs posU hpos acc litF distF =
      lz77GreedyMergedLoopF data 32768 65536 prevSize 4 2 258
        c posU.toNat acc litF distF := by
  induction hn : data.size - posU.toNat using Nat.strongRecOn
      generalizing c posU acc litF distF with
  | _ n ih =>
    exact lz77GreedyMergedLoopF1U_eq_step data prevSize dataSizeU prevSizeU hds hpsU
      hsz hfit hpv hprev hshift c hcs posU hpos hc acc litF distF n hn ih

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
    copy of `Zip.Spec.LZ77MergedCorrect.trailingPT_toArray` to avoid importing that
    module's transitive `LZ77ChainCorrect` (a name-clash source) into this file. -/
private theorem trailingPT_toArrayF (data : ByteArray) (pos : Nat) (acc : TokenArray) :
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

/-- A masked match length of at least three advances a native-word position
    without wrapping under the outer loop's addressability guard. -/
private theorem usize_add_progress_of_ge_three (dataSize : Nat) (pos matchLen : USize)
    (hpos : pos.toNat ≤ dataSize) (hfit : dataSize * 512 + 511 < USize.size)
    (hge : matchLen ≥ 3) (hmask : matchLen.toNat ≤ 511) :
    pos.toNat < (pos + matchLen).toNat := by
  have hUS : USize.size = 2 ^ System.Platform.numBits := rfl
  have hthree : (3 : USize).toNat = 3 :=
    USize.toNat_ofNat_of_lt (Nat.lt_of_lt_of_le (by decide) USize.le_size)
  have hgeN := USize.le_iff_toNat_le.mp hge
  rw [hthree] at hgeN
  rw [USize.toNat_add, Nat.mod_eq_of_lt (by rw [← hUS]; omega)]
  omega

/-- The specialized native-word wide loop has exactly the same token result as
    the boxed specialized loop, while its final byte buffer represents that
    token stream's mathematical histogram. -/
theorem lz77GreedyMergedLoopF1U64_spec (data : ByteArray) (prevSize : Nat)
    (dataSizeU prevSizeU : USize)
    (hds : dataSizeU.toNat = data.size) (hpsU : prevSizeU.toNat = prevSize)
    (hsz : data.size < USize.size) (hfit : data.size * 512 + 511 < USize.size)
    (hpv : min chainWinSize data.size ≤ prevSize) (hprev : prevSize ≤ chainWinSize)
    (c : Array Nat) (hcs : prevSize + 65536 ≤ c.size)
    (posU : USize) (hpos : posU.toNat ≤ data.size)
    (acc : TokenArray) (freqs : FusedFreqBytes)
    (litF : {a : Array Nat // a.size = 286}) (distF : {a : Array Nat // a.size = 30})
    (hsize : acc.toArray.size ≤ posU.toNat)
    (hrep : FusedFreqBytesRep freqs acc.toArray)
    (hlit : litF.val = (tokenFreqsP acc.toArray).1)
    (hdist : distF.val = (tokenFreqsP acc.toArray).2) :
    let wide := lz77GreedyMergedLoopF1U64 data prevSize dataSizeU prevSizeU
      hds hpsU hsz hfit hpv hprev c hcs posU hpos acc freqs
    let boxed := lz77GreedyMergedLoopF1U data prevSize dataSizeU prevSizeU
      hds hpsU hsz hfit hpv hprev c hcs posU hpos acc litF distF
    wide.1 = boxed.1 ∧ FusedFreqBytesRep wide.2 boxed.1.toArray ∧
      boxed.2.1.val = (tokenFreqsP boxed.1.toArray).1 ∧
      boxed.2.2.val = (tokenFreqsP boxed.1.toArray).2 := by
  induction hn : data.size - posU.toNat using Nat.strongRecOn
      generalizing posU c acc freqs litF distF with
  | _ n ih =>
    dsimp only
    unfold lz77GreedyMergedLoopF1U64 lz77GreedyMergedLoopF1U
    by_cases hlt : posU + 2 < dataSizeU
    · simp only [hlt, ↓reduceDIte]
      have haddr : data.size.toUSize.toNat = data.size := toUSize_toNat_of_lt hsz
      have h2v : (2 : USize).toNat = 2 :=
        USize.toNat_ofNat_of_lt (Nat.lt_of_lt_of_le (by decide) USize.le_size)
      have ep2 : (posU + 2).toNat = posU.toNat + 2 := by
        rw [USize.toNat_add, h2v]
        apply Nat.mod_eq_of_lt
        have hdata2 : data.size + 2 < USize.size := by omega
        exact Nat.lt_of_le_of_lt (Nat.add_le_add_right hpos 2) hdata2
      have hltN : posU.toNat + 2 < data.size := by
        have hh := USize.lt_iff_toNat_lt.mp hlt
        rw [ep2, hds] at hh
        exact hh
      have hnextOne : (posU + 1).toNat = posU.toNat + 1 := by
        rw [USize.toNat_add, USize.toNat_one]
        apply Nat.mod_eq_of_lt
        have hdata1 : data.size + 1 < USize.size := by omega
        exact Nat.lt_of_le_of_lt (Nat.add_le_add_right hpos 1) hdata1
      have hcap : acc.toArray.size + 1 < UInt64.size := by
        have hdata := byteArray_size_lt_uint64 data haddr
        omega
      split
      all_goals
        split
        · split
          · refine ih _ ?_ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ rfl
            · have hprogress := usize_add_progress_of_ge_three data.size posU _
                hpos hfit (by assumption) (by
                  rw [USize.toNat_and,
                    USize.toNat_ofNat_of_lt
                      (Nat.lt_of_lt_of_le (by decide) USize.le_size)]
                  exact Nat.and_le_right)
              have hnext := USize.le_iff_toNat_le.mp (by assumption)
              rw [hds] at hnext
              omega
            · rw [TokenArray.push_toArray, Array.size_push]
              have hprogress := usize_add_progress_of_ge_three data.size posU _
                hpos hfit (by assumption) (by
                  rw [USize.toNat_and,
                    USize.toNat_ofNat_of_lt
                      (Nat.lt_of_lt_of_le (by decide) USize.le_size)]
                  exact Nat.and_le_right)
              omega
            · rw [TokenArray.push_toArray]
              exact bumpRefFreqU64_rep freqs acc.toArray _
                (packTok_reference_tag _ _) hrep hcap
            · rw [TokenArray.push_toArray]
              exact bumpRefLitFreqP_push acc.toArray _ litF
                (packTok_reference_tag _ _) hlit
            · rw [TokenArray.push_toArray]
              exact bumpRefDistFreqP_push acc.toArray _ distF
                (packTok_reference_tag _ _) hdist
          · refine ih _ (by rw [hnextOne]; omega) _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ rfl
            · rw [TokenArray.push_toArray, Array.size_push, hnextOne]
              omega
            · rw [TokenArray.push_toArray]
              exact bumpLitFreqU64_rep freqs acc.toArray _
                (packTok_literal_tag _) hrep hcap
            · rw [TokenArray.push_toArray]
              exact bumpLitFreqP_push acc.toArray _ litF (packTok_literal_tag _) hlit
            · rw [TokenArray.push_toArray]
              exact distFreq_push_lit acc.toArray _ distF (packTok_literal_tag _) hdist
        · refine ih _ (by rw [hnextOne]; omega) _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ rfl
          · rw [TokenArray.push_toArray, Array.size_push]
            rw [hnextOne]
            omega
          · rw [TokenArray.push_toArray]
            exact bumpLitFreqU64_rep freqs acc.toArray _
              (packTok_literal_tag _) hrep hcap
          · rw [TokenArray.push_toArray]
            exact bumpLitFreqP_push acc.toArray _ litF (packTok_literal_tag _) hlit
          · rw [TokenArray.push_toArray]
            exact distFreq_push_lit acc.toArray _ distF (packTok_literal_tag _) hdist
    · simp only [hlt, ↓reduceDIte]
      have haddr : data.size.toUSize.toNat = data.size := toUSize_toNat_of_lt hsz
      have hw := trailingPFU64_spec data posU.toNat acc freqs haddr hsize hrep
      have hb := trailingPF_spec data posU.toNat acc litF distF hlit hdist
      rw [hb]
      exact ⟨hw.1, hw.2, rfl, rfl⟩

/-- The production specialized-wide entry is exactly the boxed specialized
    entry after its single final histogram materialization. -/
theorem lz77ChainIterPMergedF1U64_eq (data : ByteArray) :
    lz77ChainIterPMergedF1U64 data =
      let boxed := lz77ChainIterPMergedF1U data
      (boxed.1, boxed.2.1.val, boxed.2.2.val) := by
  unfold lz77ChainIterPMergedF1U64 lz77ChainIterPMergedF1U
  by_cases hsmall : data.size < 3
  · simp only [hsmall, if_pos]
    have haddr : data.size.toUSize.toNat = data.size :=
      toUSize_toNat_of_lt (Nat.lt_of_lt_of_le (by omega) USize.le_size)
    generalize hr : trailingPFU64 data 0 TokenArray.empty initFusedFreqBytes = r
    rcases r with ⟨tokens, freqs⟩
    have hw := trailingPFU64_spec data 0 TokenArray.empty initFusedFreqBytes haddr
      (by rw [TokenArray.empty_toArray]; simp) (by
        rw [TokenArray.empty_toArray]
        exact initFusedFreqBytes_rep)
    rw [hr] at hw
    have hb := trailingPF_spec data 0 TokenArray.empty initLitFreqF initDistFreqF
      (by rw [TokenArray.empty_toArray]; exact tokenFreqsP_nil_fst)
      (by rw [TokenArray.empty_toArray]; exact tokenFreqsP_nil_snd)
    have hf := fusedFreqBytesToNat_eq freqs
      (trailingPT data 0 TokenArray.empty).toArray hw.2
    rw [hb, hf, hw.1]
  · simp only [hsmall, if_false]
    by_cases hg : data.size.toUSize.toNat = data.size ∧
        data.size.toUSize < ((~~~(0 : USize)) >>> 9) ∧
        data.size * 512 + 511 < USize.size
    · simp only [dif_pos hg]
      let prevSize := min chainWinSize data.size
      let c := Array.replicate (prevSize + 65536) data.size
      have hsz : data.size < USize.size := by
        rw [← hg.1]
        exact USize.toNat_lt_two_pow_numBits _
      have hfit : data.size * 512 + 511 < USize.size := hg.2.2
      have hps : prevSize.toUSize.toNat = prevSize :=
        toUSize_toNat_of_lt (by simp only [prevSize, chainWinSize]; omega)
      have hcs : prevSize + 65536 ≤ c.size := by
        simp only [c, Array.size_replicate]
        omega
      have hw := lz77GreedyMergedLoopF1U64_spec data prevSize
        data.size.toUSize prevSize.toUSize hg.1 hps hsz hfit
        (Nat.le_refl _) (Nat.min_le_left _ _) c hcs 0 (by simp)
        (TokenArray.emptyWithCapacity data.size) initFusedFreqBytes initLitFreqF initDistFreqF
        (by rw [TokenArray.emptyWithCapacity_toArray]; simp)
        (by rw [TokenArray.emptyWithCapacity_toArray]; exact initFusedFreqBytes_rep)
        (by rw [TokenArray.emptyWithCapacity_toArray]; exact tokenFreqsP_nil_fst)
        (by rw [TokenArray.emptyWithCapacity_toArray]; exact tokenFreqsP_nil_snd)
      generalize hwide : lz77GreedyMergedLoopF1U64 data prevSize
        data.size.toUSize prevSize.toUSize hg.1 hps hsz hfit
        (Nat.le_refl _) (Nat.min_le_left _ _) c hcs 0 (by simp)
        (TokenArray.emptyWithCapacity data.size) initFusedFreqBytes = wide at hw
      generalize hboxed : lz77GreedyMergedLoopF1U data prevSize
        data.size.toUSize prevSize.toUSize hg.1 hps hsz hfit
        (Nat.le_refl _) (Nat.min_le_left _ _) c hcs 0 (by simp)
        (TokenArray.emptyWithCapacity data.size) initLitFreqF initDistFreqF = boxed at hw
      rcases wide with ⟨wideTokens, freqs⟩
      rcases boxed with ⟨boxedTokens, litF, distF⟩
      have hf := fusedFreqBytesToNat_eq freqs boxedTokens.toArray hw.2.1
      rw [hf, hw.1, hw.2.2.1, hw.2.2.2]
    · simp only [dif_neg hg]

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
