import Zip.Spec.DeflateFreqsFusedCorrect

namespace Zip.Native.Deflate

private def directHeadEncode (dataSize head : Nat) : UInt32 :=
  if head = dataSize then 0 else head.toUInt32 + 1

private def packedHeadAtU (heads : ByteArray) (idx : USize) : UInt32 :=
  let off := (4 : USize) * idx
  if h : off.toNat + 4 ≤ heads.size then
    heads.ugetUInt32LE off h
  else 0

private structure DirectHeadTableRep (dataSize : Nat)
    (packed : ByteArray) (heads : Array Nat) : Prop where
  packed_size : packed.size = heads.size * 4
  get_eq : ∀ (idx : USize) (hi : idx.toNat < heads.size),
    packedHeadAtU packed idx = directHeadEncode dataSize heads[idx.toNat]

private theorem directHeadOffset_toNat (idx : USize) (hi : idx.toNat < 65536) :
    ((4 : USize) * idx).toNat = 4 * idx.toNat := by
  have h4 : (4 : USize).toNat = 4 :=
    USize.toNat_ofNat_of_lt
      (Nat.lt_of_lt_of_le (by decide) USize.le_size)
  rw [USize.toNat_mul, h4]
  apply Nat.mod_eq_of_lt
  exact Nat.lt_of_lt_of_le (by omega) USize.le_size

private theorem usize_toUInt32_eq (x : USize) :
    x.toNat.toUInt32 = x.toUInt32 := by
  exact UInt32.ofNat_uSizeToNat x

private theorem directHeadEncode_lt (dataSize head : Nat)
    (hhead : head < dataSize) :
    directHeadEncode dataSize head = head.toUInt32 + 1 := by
  simp only [directHeadEncode, if_neg (Nat.ne_of_lt hhead)]

private theorem directHeadEncode_ne_zero (dataSize head : Nat)
    (hdata : dataSize < UInt32.size) (hhead : head < dataSize) :
    directHeadEncode dataSize head ≠ 0 := by
  rw [directHeadEncode_lt dataSize head hhead]
  have hhead32 : head < UInt32.size := by omega
  have hsum32 : head + 1 < UInt32.size := by omega
  have htoNat : (head.toUInt32 + 1).toNat = head + 1 := by
    simp only [UInt32.toNat_add, UInt32.toNat_one, Nat.toUInt32,
      UInt32.toNat_ofNat']
    rw [Nat.mod_eq_of_lt hhead32, Nat.mod_eq_of_lt hsum32]
  intro hz
  have hh := congrArg UInt32.toNat hz
  rw [htoNat] at hh
  simp at hh

private theorem directHeadEncode_decode (dataSize head : Nat)
    (hdata : dataSize < UInt32.size) (hhead : head < dataSize) :
    (directHeadEncode dataSize head - 1).toUSize = head.toUSize := by
  rw [directHeadEncode_lt dataSize head hhead]
  have hhead32 : head < UInt32.size := by omega
  rw [UInt32.add_sub_cancel]
  exact UInt32.toUSize_ofNat' hhead32

private theorem DirectHeadTableRep.set (dataSize : Nat)
    (packed : ByteArray) (heads : Array Nat)
    (hsize : heads.size = 65536)
    (rep : DirectHeadTableRep dataSize packed heads)
    (idx : USize) (hi : idx.toNat < heads.size)
    (head : Nat) (hhead : head < dataSize) :
    let off := (4 : USize) * idx
    DirectHeadTableRep dataSize
      (packed.usetUInt32LE off (head.toUInt32 + 1) (by
        rw [directHeadOffset_toNat idx (by omega), rep.packed_size]
        omega))
      (heads.uset idx head hi) := by
  dsimp only
  let off := (4 : USize) * idx
  have hoffN : off.toNat = 4 * idx.toNat :=
    directHeadOffset_toNat idx (by omega)
  have hoff : off.toNat + 4 ≤ packed.size := by
    rw [hoffN, rep.packed_size]
    omega
  constructor
  · rw [size_usetUInt32LE, Array.size_uset, rep.packed_size]
  · intro read hread
    have hreadOld : read.toNat < heads.size := by
      simpa only [Array.size_uset] using hread
    have hread16 : read.toNat < 65536 := by omega
    have hreadOffN : ((4 : USize) * read).toNat = 4 * read.toNat :=
      directHeadOffset_toNat read hread16
    have hreadBound : ((4 : USize) * read).toNat + 4 ≤ packed.size := by
      rw [hreadOffN, rep.packed_size]
      omega
    by_cases heq : read = idx
    · subst read
      unfold packedHeadAtU
      dsimp only
      have hbound' : (4 * idx).toNat + 4 ≤
          (packed.usetUInt32LE (4 * idx) (head.toUInt32 + 1) hoff).size := by
        rw [size_usetUInt32LE]
        exact hoff
      rw [dif_pos hbound']
      rw [ByteArray.ugetUInt32LE_usetUInt32LE_same]
      simp only [Array.uset, Array.getElem_set]
      exact directHeadEncode_lt dataSize head hhead |>.symm
    · have hne : read.toNat ≠ idx.toNat := by
        intro h
        exact heq (USize.toNat_inj.mp h)
      have hdisj : off.toNat + 4 ≤ ((4 : USize) * read).toNat ∨
          ((4 : USize) * read).toNat + 4 ≤ off.toNat := by
        rw [hoffN, hreadOffN]
        omega
      simp only [packedHeadAtU, size_usetUInt32LE, hreadBound, ↓reduceDIte]
      rw [ByteArray.ugetUInt32LE_usetUInt32LE_disjoint _ _ _ _ hoff
        hreadBound hdisj]
      have hrep := rep.get_eq read hreadOld
      unfold packedHeadAtU at hrep
      dsimp only at hrep
      rw [dif_pos hreadBound] at hrep
      rw [hrep]
      simp only [Array.uset, Array.getElem_set]
      rw [if_neg (Ne.symm hne)]

private theorem directHeadInitRep (dataSize : Nat) :
    DirectHeadTableRep dataSize
      (ByteArray.mk (Array.replicate (65536 * 4) 0))
      (Array.replicate 65536 dataSize) := by
  constructor
  · change (Array.replicate (65536 * 4) (0 : UInt8)).size =
        (Array.replicate 65536 dataSize).size * 4
    simp
  · intro idx hi
    have hi16 : idx.toNat < 65536 := by simpa using hi
    have hoffN := directHeadOffset_toNat idx hi16
    have hoff : ((4 : USize) * idx).toNat + 4 ≤ 65536 * 4 := by
      rw [hoffN]
      omega
    unfold packedHeadAtU
    dsimp only
    have hbound : ((4 : USize) * idx).toNat + 4 ≤
        (ByteArray.mk (Array.replicate (65536 * 4) 0)).size := by
      change ((4 : USize) * idx).toNat + 4 ≤
        (Array.replicate (65536 * 4) (0 : UInt8)).size
      rw [Array.size_replicate]
      exact hoff
    rw [dif_pos hbound]
    simp only [ByteArray.ugetUInt32LE]
    simp [ByteArray.getElem_eq_getElem_data, directHeadEncode]

private theorem lz77GreedyDirectHeadPackedFNU64_eq_array
    (data : ByteArray) (dataSizeU : USize)
    (hds : dataSizeU.toNat = data.size)
    (hsz : data.size < USize.size)
    (hfit : data.size * 512 + 511 < USize.size)
    (hdata32 : data.size < UInt32.size)
    (packed : ByteArray) (heads : Array Nat)
    (hpackedSize : packed.size = 65536 * 4)
    (hheadsSize : heads.size = 65536)
    (hheadsBound : ∀ i, i < heads.size → heads[i]! ≤ data.size)
    (rep : DirectHeadTableRep data.size packed heads)
    (posU : USize) (hpos : posU.toNat ≤ data.size)
    (acc : TokenArray) (freqs : FusedFreqBytes) :
    lz77GreedyDirectHeadPackedFNU64 data dataSizeU hds hsz hfit hdata32
      packed hpackedSize posU hpos acc freqs =
    lz77GreedyDirectHeadFNU64 data dataSizeU hds hsz hfit 0xFFFF heads (by
      have hm : (65535 : USize).toNat = 65535 :=
        USize.toNat_ofNat_of_lt
          (Nat.lt_of_lt_of_le (by decide) USize.le_size)
      rw [hm, hheadsSize]
      omega) hheadsBound posU hpos acc freqs := by
  induction hn : data.size - posU.toNat using Nat.strongRecOn
      generalizing packed heads posU acc freqs with
  | _ n ih =>
    rw [lz77GreedyDirectHeadPackedFNU64.eq_1,
      lz77GreedyDirectHeadFNU64.eq_1]
    by_cases hlt : posU + 2 < dataSizeU
    · simp only [hlt, ↓reduceDIte]
      have hUS : USize.size = 2 ^ System.Platform.numBits := rfl
      have h2v : (2 : USize).toNat = 2 :=
        USize.toNat_ofNat_of_lt
          (Nat.lt_of_lt_of_le (by decide) USize.le_size)
      have ep2 : (posU + 2).toNat = posU.toNat + 2 := by
        rw [USize.toNat_add, h2v]
        apply Nat.mod_eq_of_lt
        omega
      have hltN : posU.toNat + 2 < data.size := by
        have hh := USize.lt_iff_toNat_lt.mp hlt
        rw [ep2, hds] at hh
        exact hh
      let hashU := hash3L1U data dataSizeU posU hds hfit hltN
      let hshU := hashU &&& (0xFFFF : USize)
      have hmaskN : (0xFFFF : USize).toNat = 65535 :=
        USize.toNat_ofNat_of_lt
          (Nat.lt_of_lt_of_le (by decide) USize.le_size)
      have hb16 : hshU.toNat < 65536 := by
        unfold hshU
        rw [USize.toNat_and]
        exact Nat.lt_of_le_of_lt Nat.and_le_right (by omega)
      have hb : hshU.toNat < heads.size := by omega
      have hoffN : ((4 : USize) * hshU).toNat = 4 * hshU.toNat :=
        directHeadOffset_toNat hshU hb16
      have hoff : ((4 : USize) * hshU).toNat + 4 ≤ packed.size := by
        rw [hoffN, hpackedSize]
        omega
      let head := heads.uget hshU hb
      let headEnc := packed.ugetUInt32LE ((4 : USize) * hshU) hoff
      have henc : headEnc = directHeadEncode data.size head := by
        have hh := rep.get_eq hshU hb
        unfold packedHeadAtU at hh
        dsimp only at hh
        rw [dif_pos hoff] at hh
        simpa only [headEnc, head, Array.uget] using hh
      dsimp only [headEnc, head, hshU, hashU] at henc
      simp only [henc]
      have hheadBound : head ≤ data.size := by
        have hh := hheadsBound hshU.toNat hb
        simpa only [head, Array.uget, getElem!_pos heads hshU.toNat hb] using hh
      let pnext := packed.usetUInt32LE ((4 : USize) * hshU)
        (posU.toUInt32 + 1) hoff
      let anext := heads.uset hshU posU.toNat hb
      have hpnextSize : pnext.size = 65536 * 4 := by
        simpa only [pnext, size_usetUInt32LE] using hpackedSize
      have hanextSize : anext.size = 65536 := by
        simpa only [anext, Array.size_uset] using hheadsSize
      have hanextBound : ∀ i, i < anext.size → anext[i]! ≤ data.size := by
        intro i hi
        have hi' : i < heads.size := by
          simpa only [anext, Array.size_uset] using hi
        have hset : heads.set! hshU.toNat posU.toNat = anext := by
          simp only [anext, Array.uset, Array.set!_eq_setIfInBounds,
            Array.setIfInBounds, dif_pos hb]
        rw [← hset]
        by_cases heq : i = hshU.toNat
        · subst i
          rw [Array.getElem!_set!_self _ _ _ hb]
          exact hpos
        · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm heq)]
          exact hheadsBound i hi'
      have hposLt : posU.toNat < data.size := by omega
      have hrepNext : DirectHeadTableRep data.size pnext anext := by
        have hh := DirectHeadTableRep.set data.size packed heads hheadsSize rep
          hshU hb posU.toNat hposLt
        dsimp only at hh
        simpa only [pnext, anext, usize_toUInt32_eq] using hh
      have hnext : (posU + 1).toNat = posU.toNat + 1 := by
        rw [USize.toNat_add, USize.toNat_one]
        apply Nat.mod_eq_of_lt
        omega
      let w := packTok (.literal (data.uget posU (by omega)))
      have hlit :
          lz77GreedyDirectHeadPackedFNU64 data dataSizeU hds hsz hfit hdata32
              pnext hpnextSize (posU + 1) (by rw [hnext]; omega)
              (acc.push w) (bumpDirectLitFreqU64 freqs w) =
            lz77GreedyDirectHeadFNU64 data dataSizeU hds hsz hfit 0xFFFF
              anext (by
                have hm : (65535 : USize).toNat = 65535 := hmaskN
                rw [hm, hanextSize]
                omega) hanextBound (posU + 1) (by rw [hnext]; omega)
              (acc.push w) (bumpDirectLitFreqU64 freqs w) := by
        exact ih (data.size - (posU + 1).toNat) (by
            rw [hnext]
            omega)
          pnext anext hpnextSize hanextSize hanextBound hrepNext
          (posU + 1) (by rw [hnext]; omega)
          (acc.push w) (bumpDirectLitFreqU64 freqs w) rfl
      by_cases hsent : head = data.size
      · have hsentRaw :
            heads.uget
                (hash3L1U data dataSizeU posU hds hfit hltN &&& 0xFFFF) hb =
              data.size := by
          simpa only [head, hshU, hashU] using hsent
        have hnotLt : ¬data.size.toUSize < posU := by
          intro hh
          have hhN := USize.lt_iff_toNat_lt.mp hh
          rw [toUSize_toNat_of_lt hsz] at hhN
          omega
        have hpackedNo : ¬(
            directHeadEncode data.size
                (heads.uget
                  (hash3L1U data dataSizeU posU hds hfit hltN &&& 0xFFFF) hb) ≠ 0 ∧
              (directHeadEncode data.size
                    (heads.uget
                      (hash3L1U data dataSizeU posU hds hfit hltN &&& 0xFFFF) hb) -
                  1).toUSize < posU ∧
              posU -
                  (directHeadEncode data.size
                      (heads.uget
                        (hash3L1U data dataSizeU posU hds hfit hltN &&& 0xFFFF) hb) -
                1).toUSize ≤ 32768) := by
          intro hc
          apply hc.1
          rw [hsentRaw]
          simp [directHeadEncode]
        have harrayNo : ¬(
            (heads.uget
                (hash3L1U data dataSizeU posU hds hfit hltN &&& 0xFFFF) hb).toUSize <
                posU ∧
              posU -
                  (heads.uget
                    (hash3L1U data dataSizeU posU hds hfit hltN &&& 0xFFFF) hb).toUSize ≤
                32768) := by
          intro hc
          apply hnotLt
          simpa only [hsentRaw] using hc.1
        rw [dif_neg hpackedNo, dif_neg harrayNo]
        simpa only [pnext, anext, w, hshU, hashU] using hlit
      · have hheadLt : head < data.size :=
          Nat.lt_of_le_of_ne hheadBound hsent
        have hneRaw :
            directHeadEncode data.size
                (heads.uget
                  (hash3L1U data dataSizeU posU hds hfit hltN &&& 0xFFFF) hb) ≠ 0 := by
          have hh := directHeadEncode_ne_zero data.size head hdata32 hheadLt
          simpa only [head, hshU, hashU] using hh
        have hdecodeRaw :
            (directHeadEncode data.size
                  (heads.uget
                    (hash3L1U data dataSizeU posU hds hfit hltN &&& 0xFFFF) hb) -
                1).toUSize =
              (heads.uget
                (hash3L1U data dataSizeU posU hds hfit hltN &&& 0xFFFF) hb).toUSize := by
          have hh := directHeadEncode_decode data.size head hdata32 hheadLt
          simpa only [head, hshU, hashU] using hh
        simp only [hdecodeRaw]
        by_cases hc :
            (heads.uget
                (hash3L1U data dataSizeU posU hds hfit hltN &&& 0xFFFF) hb).toUSize <
                posU ∧
              posU -
                  (heads.uget
                    (hash3L1U data dataSizeU posU hds hfit hltN &&& 0xFFFF) hb).toUSize ≤
                32768
        · simp only [dif_pos (And.intro hneRaw hc), dif_pos hc]
          have hposLe : posU ≤ dataSizeU := by
            rw [USize.le_iff_toNat_le, hds]
            exact hpos
          let remU := dataSizeU - posU
          let maxLenU := if remU < 258 then remU else 258
          have hmaxRem : maxLenU ≤ remU := by
            unfold maxLenU
            split
            · exact USize.le_refl _
            · rename_i hnrem
              rw [USize.le_iff_toNat_le]
              have h258 : (258 : USize).toNat = 258 :=
                USize.toNat_ofNat_of_lt
                  (Nat.lt_of_lt_of_le (by decide) USize.le_size)
              rw [h258]
              exact Nat.le_of_not_lt fun hh =>
                hnrem (USize.lt_iff_toNat_lt.mpr (by simpa [h258] using hh))
          have hremN : remU.toNat = data.size - posU.toNat := by
            unfold remU
            rw [USize.toNat_sub_of_le _ _ hposLe, hds]
          have hpm : posU.toNat + maxLenU.toNat ≤ data.size := by
            have hh := USize.le_iff_toNat_le.mp hmaxRem
            rw [hremN] at hh
            omega
          let headRaw := heads.uget
            (hash3L1U data dataSizeU posU hds hfit hltN &&& 0xFFFF) hb
          have hcRaw : headRaw.toUSize < posU ∧
              posU - headRaw.toUSize ≤ 32768 := by
            simpa only [headRaw] using hc
          have hheadPos : headRaw.toUSize.toNat < posU.toNat :=
            USize.lt_iff_toNat_lt.mp hcRaw.1
          have hheadMax : headRaw.toUSize.toNat + maxLenU.toNat ≤ data.size := by
            omega
          let matchLenU := directHeadMatchLenU data headRaw.toUSize posU maxLenU
            hsz hheadMax hpm
          by_cases hge : matchLenU ≥ 3
          · simp only [matchLenU, headRaw, maxLenU, remU, dif_pos hge]
            by_cases hle : posU.toNat + matchLenU.toNat ≤ data.size
            · simp only [matchLenU, headRaw, maxLenU, remU, dif_pos hle]
              have hsum : (posU + matchLenU).toNat =
                  posU.toNat + matchLenU.toNat := by
                rw [USize.toNat_add]
                apply Nat.mod_eq_of_lt
                exact Nat.lt_of_le_of_lt hle hsz
              have hnextPos : (posU + matchLenU).toNat ≤ data.size := by
                rw [hsum]
                exact hle
              have hgeN : 3 ≤ matchLenU.toNat := by
                have hh := USize.le_iff_toNat_le.mp hge
                rw [USize.toNat_ofNat_of_lt
                  (Nat.lt_of_lt_of_le (by decide) USize.le_size)] at hh
                exact hh
              let wr := ((1 : UInt32) <<< 31) |||
                (matchLenU.toUInt32 <<< 16) ||| (posU - headRaw.toUSize).toUInt32
              have hrec :
                  lz77GreedyDirectHeadPackedFNU64 data dataSizeU hds hsz hfit hdata32
                      pnext hpnextSize (posU + matchLenU) hnextPos
                      (acc.push wr)
                      (bumpDirectRefDistFreqU64
                        (bumpDirectRefLitFreqU64 freqs wr) wr) =
                    lz77GreedyDirectHeadFNU64 data dataSizeU hds hsz hfit 0xFFFF
                      anext (by
                        have hm : (65535 : USize).toNat = 65535 := hmaskN
                        rw [hm, hanextSize]
                        omega) hanextBound (posU + matchLenU) hnextPos
                      (acc.push wr)
                      (bumpDirectRefDistFreqU64
                        (bumpDirectRefLitFreqU64 freqs wr) wr) := by
                exact ih (data.size - (posU + matchLenU).toNat) (by
                    rw [hsum, ← hn]
                    omega)
                  pnext anext hpnextSize hanextSize hanextBound hrepNext
                  (posU + matchLenU) hnextPos
                  (acc.push wr)
                  (bumpDirectRefDistFreqU64
                    (bumpDirectRefLitFreqU64 freqs wr) wr) rfl
              simpa only [matchLenU, headRaw, maxLenU, remU, pnext, anext, wr,
                hshU, hashU] using hrec
            · simp only [matchLenU, headRaw, maxLenU, remU, dif_neg hle]
              simpa only [pnext, anext, w, hshU, hashU] using hlit
          · simp only [matchLenU, headRaw, maxLenU, remU, dif_neg hge]
            simpa only [pnext, anext, w, hshU, hashU] using hlit
        · have hpackedNo : ¬(
              directHeadEncode data.size
                  (heads.uget
                    (hash3L1U data dataSizeU posU hds hfit hltN &&& 0xFFFF) hb) ≠ 0 ∧
                (heads.uget
                    (hash3L1U data dataSizeU posU hds hfit hltN &&& 0xFFFF) hb).toUSize <
                  posU ∧
                posU -
                    (heads.uget
                      (hash3L1U data dataSizeU posU hds hfit hltN &&& 0xFFFF) hb).toUSize ≤
                  32768) := fun hp => hc hp.2
          simp only [dif_neg hpackedNo, dif_neg hc]
          simpa only [pnext, anext, w, hshU, hashU] using hlit
    · simp [hlt]

/-- The production packed 32-bit head-table entry is observationally identical
    to the full-table `Array Nat` reference, including both representation and
    addressability fallbacks. -/
theorem lz77ChainIterPMergedDirectHeadFNU64_eq_array (data : ByteArray) :
    lz77ChainIterPMergedDirectHeadFNU64 data =
      lz77ChainIterPMergedDirectHeadArrayFNU64 data := by
  unfold lz77ChainIterPMergedDirectHeadFNU64
  by_cases hsmall : data.size < 3
  · simp only [hsmall, if_pos]
  · simp only [hsmall, if_false]
    by_cases hg : data.size.toUSize.toNat = data.size ∧
        data.size * 512 + 511 < USize.size ∧ data.size < UInt32.size
    · simp only [dif_pos hg]
      unfold lz77ChainIterPMergedDirectHeadArrayFNU64
      simp only [hsmall, if_false]
      have hgArray : data.size.toUSize.toNat = data.size ∧
          data.size * 512 + 511 < USize.size := ⟨hg.1, hg.2.1⟩
      simp only [dif_pos hgArray]
      have hsz : data.size < USize.size := by
        rw [← hg.1]
        exact USize.toNat_lt_two_pow_numBits _
      let packedHeads : ByteArray :=
        ByteArray.mk (Array.replicate (65536 * 4) 0)
      let arrayHeads : Array Nat := Array.replicate 65536 data.size
      have hpackedSize : packedHeads.size = 65536 * 4 := by
        change (Array.replicate (65536 * 4) (0 : UInt8)).size = 65536 * 4
        rw [Array.size_replicate]
      have harraySize : arrayHeads.size = 65536 := by
        simp [arrayHeads]
      have harrayBound : ∀ i, i < arrayHeads.size →
          arrayHeads[i]! ≤ data.size := by
        intro i hi
        rw [getElem!_pos _ i hi, Array.getElem_replicate]
        exact Nat.le_refl _
      have hrep : DirectHeadTableRep data.size packedHeads arrayHeads := by
        simpa only [packedHeads, arrayHeads] using directHeadInitRep data.size
      have hloop := lz77GreedyDirectHeadPackedFNU64_eq_array data
        data.size.toUSize hg.1 hsz hg.2.1 hg.2.2 packedHeads arrayHeads
        hpackedSize harraySize harrayBound hrep 0 (by simp)
        (TokenArray.emptyWithCapacity data.size) initFusedFreqBytes
      have hout := congrArg
        (fun r : TokenArray × FusedFreqBytes =>
          (r.1, (fusedFreqBytesToNat r.2).1,
            (fusedFreqBytesToNat r.2).2)) hloop
      simpa only [packedHeads, arrayHeads] using hout
    · simp only [dif_neg hg]

/-- The packed production entry preserves the established depth-one matcher
    tokens and exact literal/distance histograms. -/
theorem lz77ChainIterPMergedDirectHeadFNU64_eq (data : ByteArray) :
    lz77ChainIterPMergedDirectHeadFNU64 data =
      let packed := lz77ChainIterP data 1 32768 0 258
      (packed, (tokenFreqsP packed.toArray).1,
        (tokenFreqsP packed.toArray).2) := by
  rw [lz77ChainIterPMergedDirectHeadFNU64_eq_array]
  exact lz77ChainIterPMergedDirectHeadArrayFNU64_eq data

end Zip.Native.Deflate
