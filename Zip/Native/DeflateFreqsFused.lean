import Zip.Native.DeflateFreqs

/-!
# Fused greedy matcher: tokens and frequencies in one pass

`tokenFreqsP` is a full second walk over the packed token array (8.5% of L1
time on dickens; ~2.4% of total compress on the large Silesia binaries whose
token array spills L3 cache). The greedy merged matcher already touches every
token as it pushes it, so counting frequencies at each `acc.push` site removes
the re-read.

`lz77GreedyMergedLoopF` is the fused twin of `lz77GreedyMergedLoop`
(`Zip.Native.Deflate`): byte-for-byte the same control flow and token
accumulator, but it additionally threads the two histogram arrays, bumping at
each push site with the *same* helpers `tokenFreqsP` uses
(`bumpLitFreqP`/`bumpRefLitFreqP`/`bumpRefDistFreqP`). The histograms are seeded
exactly like `tokenFreqsP` (286 lit/len with EOB pre-counted, 30 distance), so
the running frequencies are `tokenFreqsP` of the running token accumulator at
every step — the invariant proved in `Zip/Spec/DeflateFreqsFusedCorrect.lean`.

As with `tokenFreqsP`/`emitTokensP`, the per-token frequency work lives inside
the opaque `bump*FreqP` helpers, so the well-founded-recursion body never forces
a `findTableCode` reduction (the landmine documented in `DeflateFreqs.lean`).
-/

namespace Zip.Native.Deflate

/-- Lit/len histogram seeded with the EOB pre-count, exactly `tokenFreqsP`'s
    initial `litLenFreqs` (`(replicate 286 0).set! 256 1`). -/
def initLitFreqF : {a : Array Nat // a.size = 286} :=
  ⟨(Array.replicate 286 0).set! 256 1, by rw [Array.size_set!, Array.size_replicate]⟩

/-- Distance histogram seeded to all-zero, exactly `tokenFreqsP`'s initial
    `distFreqs` (`replicate 30 0`). -/
def initDistFreqF : {a : Array Nat // a.size = 30} :=
  ⟨Array.replicate 30 0, by rw [Array.size_replicate]⟩

/-- Fused twin of `trailingPT`: pushes each remaining byte as a literal token
    into a `TokenArray` accumulator (4 B/token, stage 4/7 of the token-stream
    unboxing) and bumps the lit/len histogram at the same site (`bumpLitFreqP`). -/
def trailingPF (data : ByteArray) (pos : Nat) (acc : TokenArray)
    (litF : {a : Array Nat // a.size = 286}) (distF : {a : Array Nat // a.size = 30}) :
    TokenArray × {a : Array Nat // a.size = 286} × {a : Array Nat // a.size = 30} :=
  if h : pos < data.size then
    let w := packTok (.literal data[pos])
    trailingPF data (pos + 1) (acc.push w) (bumpLitFreqP litF w) distF
  else (acc, litF, distF)
termination_by data.size - pos

/-- Fused twin of `lz77GreedyMergedLoop` (`Zip.Native.Deflate`): identical
    control flow and token accumulator, additionally threading the two
    histograms. Every `acc.push (packTok t)` site is paired with the histogram
    bump `tokenFreqsP` performs on that packed word — literals through
    `bumpLitFreqP`, references through `bumpRefLitFreqP` + `bumpRefDistFreqP`.
    Proven equal to `(lz77GreedyMergedLoop ..., tokenFreqsP-of-tokens)` in
    `Zip/Spec/DeflateFreqsFusedCorrect.lean`. -/
def lz77GreedyMergedLoopF (data : ByteArray)
    (windowSize hashSize prevSize maxChain insertCap niceLen : Nat)
    (c : Array Nat) (pos : Nat) (acc : TokenArray)
    (litF : {a : Array Nat // a.size = 286}) (distF : {a : Array Nat // a.size = 30}) :
    TokenArray × {a : Array Nat // a.size = 286} × {a : Array Nat // a.size = 30} :=
  if hlt : pos + 2 < data.size then
    let h := lz77Greedy.hash3 data pos hashSize hlt
    let head := headProbeGuarded c (prevSize + h)
    let c := guardedSet c (prevSize + h) pos
    let c := guardedSet c (pos &&& 0x7FFF) head
    let maxLen := min 258 (data.size - pos)
    have hmaxLenP : pos + maxLen ≤ data.size := by omega
    let next (matchLen matchPos : Nat) :=
      if hge : matchLen ≥ 3 then
        if hle : pos + matchLen ≤ data.size then
          have : data.size - (pos + matchLen) < data.size - pos := by omega
          let c := updateHashesMergedGuarded data hashSize prevSize c pos 1 matchLen insertCap
          let w := packTok (.reference matchLen (pos - matchPos))
          lz77GreedyMergedLoopF data windowSize hashSize prevSize maxChain insertCap niceLen c (pos + matchLen)
            (acc.push w) (bumpRefLitFreqP litF w) (bumpRefDistFreqP distF w)
        else
          let w := packTok (.literal (data[pos]'(by omega)))
          lz77GreedyMergedLoopF data windowSize hashSize prevSize maxChain insertCap niceLen c (pos + 1)
            (acc.push w) (bumpLitFreqP litF w) distF
      else
        let w := packTok (.literal (data[pos]'(by omega)))
        lz77GreedyMergedLoopF data windowSize hashSize prevSize maxChain insertCap niceLen c (pos + 1)
          (acc.push w) (bumpLitFreqP litF w) distF
    if hg : chainWalkPackedUUSafe data c windowSize maxLen head maxChain then
      let r := chainWalkPackedUUChecked data c windowSize pos maxLen niceLen hmaxLenP head maxChain hg
      next (r &&& 0x1FF).toNat (r >>> 9).toNat
    else
      let r := chainWalkGuardedPackedU data c windowSize pos maxLen niceLen hmaxLenP head maxChain 0 0
      next (r % 512) (r / 512)
  else
    trailingPF data pos acc litF distF
termination_by data.size - pos
decreasing_by all_goals omega

/-! ## Level-one native-word outer loop

The generic fused loop keeps its outer position in `Nat` and re-enters guarded
wrappers at every byte.  Level one has fixed policy (`hashSize = 65536`, chain
depth 4, insertion cap 2, nice length 258), so its hot loop can keep the data
position, hash-table indices, match length, and chain result in `USize` after one
entry guard.  The combined chain/hash state deliberately remains `Array Nat`;
only its indices are native words.
-/

/-- Level-one four-byte hash.  The fixed 65536-bucket table means the high
    16 bits of the multiplied word are already the exact bucket; unlike the
    generic `hash3U`, no `% hashSizeU` remains in the hot path. -/
@[inline] def hash3L1U (data : ByteArray) (dataSizeU pU : USize)
    (hds : dataSizeU.toNat = data.size)
    (hfit : data.size * 512 + 511 < USize.size)
    (hp : pU.toNat + 2 < data.size) : USize :=
  let word :=
    if h4 : pU + 4 ≤ dataSizeU then
      ByteArray.ugetUInt32LE data pU (by
        have h4v : (4 : USize).toNat = 4 :=
          USize.toNat_ofNat_of_lt
            (Nat.lt_of_lt_of_le (by decide) USize.le_size)
        have ep4 : (pU + 4).toNat = pU.toNat + 4 := by
          have hUS : USize.size = 2 ^ System.Platform.numBits := rfl
          rw [USize.toNat_add, h4v]
          apply Nat.mod_eq_of_lt
          omega
        have hn := USize.le_iff_toNat_le.mp h4
        rw [ep4, hds] at hn
        exact hn)
    else
      let p := pU.toNat
      let a := (data[p]'(by omega)).toUInt32
      let b := (data[p + 1]'(by omega)).toUInt32
      let c := (data[p + 2]'(by omega)).toUInt32
      a ||| (b <<< 8) ||| (c <<< 16)
  ((word * 0x1E35A7BD) >>> 16).toUSize

theorem hash3L1U_toNat_lt (data : ByteArray) (dataSizeU pU : USize)
    (hds : dataSizeU.toNat = data.size)
    (hfit : data.size * 512 + 511 < USize.size)
    (hp : pU.toNat + 2 < data.size) :
    (hash3L1U data dataSizeU pU hds hfit hp).toNat < 65536 := by
  unfold hash3L1U
  generalize (if h4 : pU + 4 ≤ dataSizeU then _ else _ : UInt32) = word
  rw [UInt32.toNat_toUSize, UInt32.toNat_shiftRight,
    show ((16 : UInt32).toNat % 32) = 16 from rfl]
  have := UInt32.toNat_lt (word * 0x1E35A7BD)
  omega

/-- Insert one of level one's two interior positions.  Returning a subtype
    records (proof-only) that the ordinary `Array Nat` state keeps its size. -/
@[inline] def insertHashL1U (data : ByteArray) (prevSize : Nat)
    (dataSizeU prevSizeU posU jU : USize) (c : Array Nat)
    (hds : dataSizeU.toNat = data.size) (hpsU : prevSizeU.toNat = prevSize)
    (hfit : data.size * 512 + 511 < USize.size)
    (hprev : prevSize ≤ chainWinSize)
    (hcs : prevSize + 65536 ≤ c.size) (hpos : posU.toNat ≤ data.size)
    (hj : jU.toNat ≤ 2) : {a : Array Nat // a.size = c.size} :=
  if hd : posU + jU + 2 < dataSizeU then
    have hUS : USize.size = 2 ^ System.Platform.numBits := rfl
    have hj2 : (2 : USize).toNat = 2 :=
      USize.toNat_ofNat_of_lt
        (Nat.lt_of_lt_of_le (by decide) USize.le_size)
    have hpj : (posU + jU).toNat = posU.toNat + jU.toNat := by
      rw [USize.toNat_add]
      apply Nat.mod_eq_of_lt
      omega
    have hpj2 : (posU + jU + 2).toNat = posU.toNat + jU.toNat + 2 := by
      rw [USize.toNat_add, hpj, hj2]
      apply Nat.mod_eq_of_lt
      omega
    have hp2 : (posU + jU).toNat + 2 < data.size := by
      have := USize.lt_iff_toNat_lt.mp hd
      rw [hpj2, hds] at this
      omega
    let hshU := hash3L1U data dataSizeU (posU + jU) hds hfit hp2
    have hshlt : hshU.toNat < 65536 :=
      hash3L1U_toNat_lt data dataSizeU (posU + jU) hds hfit hp2
    have hidx : (prevSizeU + hshU).toNat = prevSize + hshU.toNat := by
      rw [USize.toNat_add, hpsU]
      apply Nat.mod_eq_of_lt
      simp only [chainWinSize] at hprev
      exact Nat.lt_of_lt_of_le (by omega) USize.le_size
    have hb : (prevSizeU + hshU).toNat < c.size := by rw [hidx]; omega
    let head := c.uget (prevSizeU + hshU) hb
    have hmaskb : ((posU + jU) &&& 0x7FFF).toNat < c.size := by
      rw [USize.toNat_and,
        USize.toNat_ofNat_of_lt (Nat.lt_of_lt_of_le (by decide) USize.le_size)]
      have hm := winMask_lt ((posU + jU).toNat)
      exact Nat.lt_of_lt_of_le hm
        (Nat.le_trans (by simp only [chainWinSize]; omega) hcs)
    let c1 := c.uset (prevSizeU + hshU) ((posU + jU).toNat) hb
    let c2 := c1.uset ((posU + jU) &&& 0x7FFF) head (by
      rw [Array.size_uset]
      exact hmaskb)
    ⟨c2, by simp only [c2, c1, Array.size_uset]⟩
  else ⟨c, rfl⟩

/-- Fused level-one loop with native-word outer state. -/
def lz77GreedyMergedLoopF1U (data : ByteArray) (prevSize : Nat)
    (dataSizeU prevSizeU : USize)
    (hds : dataSizeU.toNat = data.size) (hpsU : prevSizeU.toNat = prevSize)
    (hsz : data.size < USize.size) (hfit : data.size * 512 + 511 < USize.size)
    (hpv : min chainWinSize data.size ≤ prevSize) (hprev : prevSize ≤ chainWinSize)
    (c : Array Nat) (hcs : prevSize + 65536 ≤ c.size)
    (posU : USize) (hpos : posU.toNat ≤ data.size)
    (acc : TokenArray)
    (litF : {a : Array Nat // a.size = 286}) (distF : {a : Array Nat // a.size = 30}) :
    TokenArray × {a : Array Nat // a.size = 286} × {a : Array Nat // a.size = 30} :=
  if hlt : posU + 2 < dataSizeU then
    have hUS : USize.size = 2 ^ System.Platform.numBits := rfl
    have h2v : (2 : USize).toNat = 2 :=
      USize.toNat_ofNat_of_lt
        (Nat.lt_of_lt_of_le (by decide) USize.le_size)
    have ep2 : (posU + 2).toNat = posU.toNat + 2 := by
      rw [USize.toNat_add, h2v]
      apply Nat.mod_eq_of_lt
      omega
    have hltN : posU.toNat + 2 < data.size := by
      have := USize.lt_iff_toNat_lt.mp hlt
      rw [ep2, hds] at this
      exact this
    let hshU := hash3L1U data dataSizeU posU hds hfit hltN
    have hshlt : hshU.toNat < 65536 :=
      hash3L1U_toNat_lt data dataSizeU posU hds hfit hltN
    have hidx : (prevSizeU + hshU).toNat = prevSize + hshU.toNat := by
      rw [USize.toNat_add, hpsU]
      apply Nat.mod_eq_of_lt
      simp only [chainWinSize] at hprev
      exact Nat.lt_of_lt_of_le (by omega) USize.le_size
    have hb : (prevSizeU + hshU).toNat < c.size := by rw [hidx]; omega
    let head := c.uget (prevSizeU + hshU) hb
    let cHash := c.uset (prevSizeU + hshU) posU.toNat hb
    have hmaskb : (posU &&& 0x7FFF).toNat < cHash.size := by
      rw [Array.size_uset, USize.toNat_and,
        USize.toNat_ofNat_of_lt (Nat.lt_of_lt_of_le (by decide) USize.le_size)]
      have hm := winMask_lt posU.toNat
      exact Nat.lt_of_lt_of_le hm
        (Nat.le_trans (by simp only [chainWinSize]; omega) hcs)
    let cRing := cHash.uset (posU &&& 0x7FFF) head hmaskb
    have hcs' : prevSize + 65536 ≤ cRing.size := by
      simp only [cRing, cHash, Array.size_uset]
      exact hcs
    have hposLe : posU ≤ dataSizeU := by
      rw [USize.le_iff_toNat_le, hds]
      exact hpos
    let remU := dataSizeU - posU
    let maxLenU := if remU < 258 then remU else 258
    have hmaxRem : maxLenU ≤ remU := by
      unfold maxLenU
      split
      · exact USize.le_refl _
      · have hn : ¬ remU < (258 : USize) := by assumption
        rw [USize.le_iff_toNat_le]
        have h258 : (258 : USize).toNat = 258 :=
          USize.toNat_ofNat_of_lt
            (Nat.lt_of_lt_of_le (by decide) USize.le_size)
        rw [h258]
        apply Nat.le_of_not_lt
        intro hh
        exact hn (USize.lt_iff_toNat_lt.mpr (by rwa [h258]))
    have hmax258 : maxLenU.toNat ≤ 258 := by
      unfold maxLenU
      split
      · have hh := USize.lt_iff_toNat_lt.mp (by assumption)
        have h258 : (258 : USize).toNat = 258 :=
          USize.toNat_ofNat_of_lt
            (Nat.lt_of_lt_of_le (by decide) USize.le_size)
        rw [h258] at hh
        omega
      · have h258 : (258 : USize).toNat = 258 :=
          USize.toNat_ofNat_of_lt
            (Nat.lt_of_lt_of_le (by decide) USize.le_size)
        exact Nat.le_of_eq h258
    have hremN : remU.toNat = data.size - posU.toNat := by
      unfold remU
      rw [USize.toNat_sub_of_le _ _ hposLe, hds]
    have hpm : posU.toNat + maxLenU.toNat ≤ data.size := by
      have hh := USize.le_iff_toNat_le.mp hmaxRem
      rw [hremN] at hh
      omega
    have hwalkPrev : min chainWinSize data.size ≤ cRing.size := by omega
    let headU := head.toUSize
    let r := chainWalkPackedUU data cRing hwalkPrev hsz 32768 posU maxLenU maxLenU
      headU 4 0 0 hpm
    let matchLenU := r &&& 0x1FF
    let matchPosU := r >>> 9
    if hge : matchLenU ≥ 3 then
      if hle : posU + matchLenU ≤ dataSizeU then
        have hmask511 : matchLenU.toNat ≤ 511 := by
          unfold matchLenU
          rw [USize.toNat_and,
            USize.toNat_ofNat_of_lt (Nat.lt_of_lt_of_le (by decide) USize.le_size)]
          exact Nat.and_le_right
        have hsum : (posU + matchLenU).toNat = posU.toNat + matchLenU.toNat := by
          rw [USize.toNat_add]
          apply Nat.mod_eq_of_lt
          omega
        have hnextPos : (posU + matchLenU).toNat ≤ data.size := by
          have hh := USize.le_iff_toNat_le.mp hle
          rw [hds] at hh
          exact hh
        have hdec : data.size - (posU + matchLenU).toNat < data.size - posU.toNat := by
          have hgeN : 3 ≤ matchLenU.toNat := by
            have hh := USize.le_iff_toNat_le.mp hge
            rw [USize.toNat_ofNat_of_lt
              (Nat.lt_of_lt_of_le (by decide) USize.le_size)] at hh
            exact hh
          rw [hsum] at hnextPos ⊢
          omega
        let c1 := insertHashL1U data prevSize dataSizeU prevSizeU posU 1 cRing
          hds hpsU hfit hprev hcs' hpos (by rw [USize.toNat_one]; omega)
        have hc1s : prevSize + 65536 ≤ c1.val.size := by rw [c1.property]; exact hcs'
        let c2 := insertHashL1U data prevSize dataSizeU prevSizeU posU 2 c1.val
          hds hpsU hfit hprev hc1s hpos (by rw [h2v]; omega)
        have hc2s : prevSize + 65536 ≤ c2.val.size := by rw [c2.property]; exact hc1s
        let w := packTok (.reference matchLenU.toNat (posU - matchPosU).toNat)
        lz77GreedyMergedLoopF1U data prevSize dataSizeU prevSizeU hds hpsU hsz hfit hpv hprev
          c2.val hc2s (posU + matchLenU) hnextPos
          (acc.push w) (bumpRefLitFreqP litF w) (bumpRefDistFreqP distF w)
      else
        let b := data.uget posU (by omega)
        let w := packTok (.literal b)
        have hnext : (posU + 1).toNat = posU.toNat + 1 := by
          rw [USize.toNat_add, USize.toNat_one]
          apply Nat.mod_eq_of_lt
          omega
        lz77GreedyMergedLoopF1U data prevSize dataSizeU prevSizeU hds hpsU hsz hfit hpv hprev
          cRing hcs' (posU + 1) (by rw [hnext]; omega)
          (acc.push w) (bumpLitFreqP litF w) distF
    else
      let b := data.uget posU (by omega)
      let w := packTok (.literal b)
      have hnext : (posU + 1).toNat = posU.toNat + 1 := by
        rw [USize.toNat_add, USize.toNat_one]
        apply Nat.mod_eq_of_lt
        omega
      lz77GreedyMergedLoopF1U data prevSize dataSizeU prevSizeU hds hpsU hsz hfit hpv hprev
        cRing hcs' (posU + 1) (by rw [hnext]; omega)
        (acc.push w) (bumpLitFreqP litF w) distF
  else
    trailingPF data posU.toNat acc litF distF
termination_by data.size - posU.toNat
decreasing_by all_goals omega

/-- Level-one fused entry.  The sole native-word/packing guard covers the whole
    outer loop; the fallback is the existing generic fused matcher. -/
def lz77ChainIterPMergedF1U (data : ByteArray) :
    TokenArray × {a : Array Nat // a.size = 286} × {a : Array Nat // a.size = 30} :=
  if data.size < 3 then
    trailingPF data 0 TokenArray.empty initLitFreqF initDistFreqF
  else if hg : data.size.toUSize.toNat = data.size ∧
      data.size.toUSize < ((~~~(0 : USize)) >>> 9) ∧
      data.size * 512 + 511 < USize.size then
    let prevSize := min chainWinSize data.size
    let c := Array.replicate (prevSize + 65536) data.size
    have hsz : data.size < USize.size := by
      rw [← hg.1]
      exact USize.toNat_lt_two_pow_numBits _
    have hfit : data.size * 512 + 511 < USize.size := hg.2.2
    lz77GreedyMergedLoopF1U data prevSize data.size.toUSize prevSize.toUSize hg.1
      (toUSize_toNat_of_lt (by simp only [prevSize, chainWinSize]; omega)) hsz hfit
      (Nat.le_refl _) (Nat.min_le_left _ _)
      c (by simp only [c, Array.size_replicate]; omega) 0 (by simp)
      (TokenArray.emptyWithCapacity data.size) initLitFreqF initDistFreqF
  else
    let prevSize := min chainWinSize data.size
    lz77GreedyMergedLoopF data 32768 65536 prevSize 4 2 258
      (.replicate (prevSize + 65536) data.size) 0
      (TokenArray.emptyWithCapacity data.size) initLitFreqF initDistFreqF

/-- Fused entry mirroring `lz77ChainIterPMerged` (`Zip.Native.Deflate`): builds
    the combined `prevSize + hashSize` array and runs `lz77GreedyMergedLoopF`,
    returning the packed token stream and its `tokenFreqsP` histograms in one
    pass. Proven equal to `(lz77ChainIterPMerged ..., tokenFreqsP-of-tokens)` in
    `Zip/Spec/DeflateFreqsFusedCorrect.lean`. -/
def lz77ChainIterPMergedF (data : ByteArray) (maxChain : Nat) (windowSize : Nat := 32768)
    (insertCap : Nat := 1000000000) (niceLen : Nat := 258) :
    TokenArray × {a : Array Nat // a.size = 286} × {a : Array Nat // a.size = 30} :=
  if data.size < 3 then
    trailingPF data 0 TokenArray.empty initLitFreqF initDistFreqF
  else
    let hashSize := 65536
    let prevSize := min chainWinSize data.size
    lz77GreedyMergedLoopF data windowSize hashSize prevSize maxChain insertCap niceLen
      (.replicate (prevSize + hashSize) data.size) 0
      (TokenArray.emptyWithCapacity data.size) initLitFreqF initDistFreqF

/-! ## Unboxed fused histograms

`Array USize` still uses generic boxed array slots in generated C
(`lean_unbox_usize`/`lean_box_usize` around every get/set).  This candidate
therefore stores all 316 counters in one fixed-size `ByteArray`, one little-
endian `UInt64` per bin.  `ByteArray.ugetUInt64LE`/`usetUInt64LE` compile to
unboxed scalar load/store calls, while the 286+30 `Nat` arrays are materialized
only once after matching.  `Zip.Spec.DeflateFreqsFusedCorrect` proves the wide
counter representation and the guarded L1 matcher refinement. -/

def fusedFreqBinCount : Nat := 286 + 30
def fusedFreqByteCount : Nat := fusedFreqBinCount * 8

/-- All fused lit/length and distance counters in one unboxed byte buffer.
    Bins 0–285 are lit/length; bins 286–315 are distance. -/
abbrev FusedFreqBytes := {a : ByteArray // a.size = fusedFreqByteCount}

/-- A zero-filled counter buffer.  EOB is added when converting back to `Nat`,
    so the hot matcher only records actual tokens. -/
def initFusedFreqBytes : FusedFreqBytes :=
  ⟨ByteArray.mk (Array.replicate fusedFreqByteCount 0), by
    change (Array.replicate fusedFreqByteCount (0 : UInt8)).size = fusedFreqByteCount
    rw [Array.size_replicate]⟩

theorem size_usetUInt64LE (a : ByteArray) (off : USize) (v : UInt64)
    (h : off.toNat + 8 ≤ a.size) :
    (a.usetUInt64LE off v h).size = a.size := by
  simp only [ByteArray.usetUInt64LE, ByteArray.size_set]

/-- Increment one counter through genuinely unboxed `UInt64` load/store FFI. -/
@[inline] def bumpFusedFreqBytes (f : FusedFreqBytes) (idx : Nat)
    (hidx : idx < fusedFreqBinCount) : FusedFreqBytes :=
  let off := (idx * 8).toUSize
  have hofflt : idx * 8 < USize.size := by
    exact Nat.lt_of_lt_of_le (by
      unfold fusedFreqBinCount at hidx
      omega : idx * 8 < 2 ^ 32) USize.le_size
  have hoff : off.toNat + 8 ≤ f.val.size := by
    rw [show off.toNat = idx * 8 by
      unfold off
      exact toUSize_toNat_of_lt hofflt, f.property]
    unfold fusedFreqBinCount at hidx
    unfold fusedFreqByteCount fusedFreqBinCount
    omega
  let n := f.val.ugetUInt64LE off hoff
  ⟨f.val.usetUInt64LE off (n + 1) hoff, by
    rw [size_usetUInt64LE]
    exact f.property⟩

/-- Read one counter when materializing the final boxed `Nat` histograms. -/
@[inline] def getFusedFreqBytes (f : FusedFreqBytes) (idx : Nat)
    (hidx : idx < fusedFreqBinCount) : Nat :=
  let off := (idx * 8).toUSize
  have hofflt : idx * 8 < USize.size := by
    exact Nat.lt_of_lt_of_le (by
      unfold fusedFreqBinCount at hidx
      omega : idx * 8 < 2 ^ 32) USize.le_size
  have hoff : off.toNat + 8 ≤ f.val.size := by
    rw [show off.toNat = idx * 8 by
      unfold off
      exact toUSize_toNat_of_lt hofflt, f.property]
    unfold fusedFreqBinCount at hidx
    unfold fusedFreqByteCount fusedFreqBinCount
    omega
  (f.val.ugetUInt64LE off hoff).toNat

@[inline] def bumpLitFreqU64 (f : FusedFreqBytes) (w : UInt32) : FusedFreqBytes :=
  let idx := w.toUInt8.toNat
  bumpFusedFreqBytes f idx (by
    have := UInt8.toNat_lt w.toUInt8
    unfold fusedFreqBinCount
    omega)

@[inline] def bumpRefLitFreqU64 (f : FusedFreqBytes) (w : UInt32) : FusedFreqBytes :=
  let lIdx := codeIdx (lenCodeWord (((w >>> 16) &&& 0x7FFF).toNat))
  have hsym : lIdx + 257 < 286 := by
    obtain ⟨⟨i, e, v⟩, he⟩ := Option.isSome_iff_exists.mp
      (findLengthCode_isSome (((w >>> 16) &&& 0x7FFF).toNat))
    have hli : lIdx = i := codeIdx_lenCodeWord _ _ _ _ he
    have := nativeFindLengthCode_idx_bound _ _ _ _ he
    omega
  bumpFusedFreqBytes f (lIdx + 257) (by
    unfold fusedFreqBinCount
    omega)

@[inline] def bumpRefDistFreqU64 (f : FusedFreqBytes) (w : UInt32) : FusedFreqBytes :=
  let dIdx := codeIdx (distCodeWord ((w &&& 0xFFFF).toNat))
  have hd : dIdx < 30 := by
    obtain ⟨⟨i, e, v⟩, he⟩ := Option.isSome_iff_exists.mp
      (findDistCode_isSome ((w &&& 0xFFFF).toNat))
    have hdi : dIdx = i := codeIdx_distCodeWord _ _ _ _ he
    have := nativeFindDistCode_idx_bound _ _ _ _ he
    omega
  bumpFusedFreqBytes f (286 + dIdx) (by
    unfold fusedFreqBinCount
    omega)

/-- Materialize the conventional boxed histograms once, after matching. -/
def fusedFreqBytesToNat (f : FusedFreqBytes) : Array Nat × Array Nat :=
  let lit : Array Nat := Array.ofFn fun i : Fin 286 =>
    getFusedFreqBytes f i.val (by unfold fusedFreqBinCount; omega) +
      if i.val = 256 then 1 else 0
  let dist : Array Nat := Array.ofFn fun i : Fin 30 =>
    getFusedFreqBytes f (286 + i.val) (by unfold fusedFreqBinCount; omega)
  (lit, dist)

def trailingPFU64 (data : ByteArray) (pos : Nat) (acc : TokenArray)
    (freqs : FusedFreqBytes) : TokenArray × FusedFreqBytes :=
  if h : pos < data.size then
    let w := packTok (.literal data[pos])
    trailingPFU64 data (pos + 1) (acc.push w) (bumpLitFreqU64 freqs w)
  else (acc, freqs)
termination_by data.size - pos

/-- Fused greedy matcher with the exact production L1 token control flow, but
    one unboxed combined histogram instead of two boxed `Array Nat`s. -/
def lz77GreedyMergedLoopFU64 (data : ByteArray)
    (windowSize hashSize prevSize maxChain insertCap niceLen : Nat)
    (c : Array Nat) (pos : Nat) (acc : TokenArray) (freqs : FusedFreqBytes) :
    TokenArray × FusedFreqBytes :=
  if hlt : pos + 2 < data.size then
    let h := lz77Greedy.hash3 data pos hashSize hlt
    let head := headProbeGuarded c (prevSize + h)
    let c := guardedSet c (prevSize + h) pos
    let c := guardedSet c (pos &&& 0x7FFF) head
    let maxLen := min 258 (data.size - pos)
    have hmaxLenP : pos + maxLen ≤ data.size := by omega
    let next (matchLen matchPos : Nat) :=
      if hge : matchLen ≥ 3 then
        if hle : pos + matchLen ≤ data.size then
          have : data.size - (pos + matchLen) < data.size - pos := by omega
          let c := updateHashesMergedGuarded data hashSize prevSize c pos 1 matchLen insertCap
          let w := packTok (.reference matchLen (pos - matchPos))
          let freqs := bumpRefLitFreqU64 freqs w
          lz77GreedyMergedLoopFU64 data windowSize hashSize prevSize maxChain insertCap niceLen c
            (pos + matchLen) (acc.push w) (bumpRefDistFreqU64 freqs w)
        else
          let w := packTok (.literal (data[pos]'(by omega)))
          lz77GreedyMergedLoopFU64 data windowSize hashSize prevSize maxChain insertCap niceLen c
            (pos + 1) (acc.push w) (bumpLitFreqU64 freqs w)
      else
        let w := packTok (.literal (data[pos]'(by omega)))
        lz77GreedyMergedLoopFU64 data windowSize hashSize prevSize maxChain insertCap niceLen c
          (pos + 1) (acc.push w) (bumpLitFreqU64 freqs w)
    if hg : chainWalkPackedUUSafe data c windowSize maxLen head maxChain then
      let r := chainWalkPackedUUChecked data c windowSize pos maxLen niceLen hmaxLenP head maxChain hg
      next (r &&& 0x1FF).toNat (r >>> 9).toNat
    else
      let r := chainWalkGuardedPackedU data c windowSize pos maxLen niceLen hmaxLenP head maxChain 0 0
      next (r % 512) (r / 512)
  else
    trailingPFU64 data pos acc freqs
termination_by data.size - pos
decreasing_by all_goals omega

/-- Dedicated production-module L1 entry, with the same literal policy as the
    current 64K/depth-4/cap-2 matcher. -/
def lz77ChainIterPMergedFU64Level1 (data : ByteArray) :
    TokenArray × Array Nat × Array Nat :=
  let (tokens, freqs) :=
    if data.size < 3 then
      trailingPFU64 data 0 TokenArray.empty initFusedFreqBytes
    else
      let prevSize := min chainWinSize data.size
      lz77GreedyMergedLoopFU64 data 32768 65536 prevSize 4 2 258
        (.replicate (prevSize + 65536) data.size) 0
        (TokenArray.emptyWithCapacity data.size) initFusedFreqBytes
  let f := fusedFreqBytesToNat freqs
  (tokens, f.1, f.2)

end Zip.Native.Deflate
