import Zip.Native.DeflateDynamic

namespace Zip.Native.Deflate

theorem splitEndBlockCheckN_eq
    (o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 oldTot : Nat)
    (n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 newTot : Nat)
    (blockBytes : Nat) :
    splitEndBlockCheckN
        o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 oldTot
        n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 newTot blockBytes =
      splitEndBlockCheck #[o0, o1, o2, o3, o4, o5, o6, o7, o8, o9] oldTot
        #[n0, n1, n2, n3, n4, n5, n6, n7, n8, n9] newTot blockBytes := by
  simp [splitEndBlockCheckN, splitAbsDiffN, splitEndBlockCheck, splitNumClasses,
    List.range']

theorem splitTokenClassP_lt (w : UInt32) : splitTokenClassP w < 10 := by
  unfold splitTokenClassP splitNumLiteralClasses
  split
  · have h1 :
        (((w.toUInt8 >>> 5) &&& 6) ||| (w.toUInt8 &&& 1)) < (10 : UInt8) := by
        bv_decide
    have h2 : (10 : UInt8).toNat = 10 := by decide
    have := UInt8.lt_iff_toNat_lt.mp h1
    omega
  · split <;> omega

theorem splitTokenBytesP_lt (w : UInt32) : splitTokenBytesP w < 32768 := by
  unfold splitTokenBytesP
  split
  · omega
  · have h1 : ((w >>> 16) &&& 0x7FFF) < (32768 : UInt32) := by bv_decide
    have h2 : (32768 : UInt32).toNat = 32768 := by decide
    have := UInt32.lt_iff_toNat_lt.mp h1
    omega

theorem splitTokenClassPU_toNat (w : UInt32) :
    (splitTokenClassPU w).toNat = splitTokenClassP w := by
  unfold splitTokenClassPU splitTokenClassP splitNumLiteralClasses
  split
  · have heq :
        (((w >>> (5 : UInt32)) &&& (6 : UInt32)) ||| (w &&& (1 : UInt32))) =
          ((((w.toUInt8 >>> (5 : UInt8)) &&& (6 : UInt8)) |||
            (w.toUInt8 &&& (1 : UInt8))).toUInt32) := by
        bv_decide
    rw [heq, UInt32.toNat_toUSize, UInt8.toNat_toUInt32]
  · split <;> simp_all [UInt32.le_iff_toNat_le]

theorem splitTokenBytesPU_toNat (w : UInt32) :
    (splitTokenBytesPU w).toNat = splitTokenBytesP w := by
  unfold splitTokenBytesPU splitTokenBytesP
  split
  · exact USize.toNat_ofNat_of_lt
      (Nat.lt_of_lt_of_le (by decide) USize.le_size)
  · exact UInt32.toNat_toUSize _

theorem tokenArray_uget_eq_get (toks : TokenArray) (i : Nat) (off : USize)
    (hi : i < toks.size)
    (hoff : off.toNat = 4 * i) (hb : off.toNat + 4 ≤ toks.bytes.size) :
    toks.bytes.ugetUInt32LE off hb = toks.get i hi := by
  unfold ByteArray.ugetUInt32LE TokenArray.get
  simp only [hoff]

theorem chooseSplitsHeuristicP_go_no_remaining (toks : TokenArray)
    (minBlockBytes softMaxBlockBytes checkTokens : Nat) :
    ∀ (fuel i : Nat), toks.size - i < fuel →
      ∀ (o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 oldTot : Nat)
        (n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 newTot : Nat)
        (blockBytes remaining : Nat) (cuts : Array Nat), remaining < minBlockBytes →
        chooseSplitsHeuristicP.go toks minBlockBytes softMaxBlockBytes checkTokens i
            o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 oldTot
            n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 newTot blockBytes remaining cuts = cuts := by
  intro fuel
  induction fuel with
  | zero => intro i hf; omega
  | succ fuel ih =>
    intro i hf o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 oldTot
      n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 newTot blockBytes remaining cuts hr
    unfold chooseSplitsHeuristicP.go
    by_cases hi : i < toks.size
    · rw [dif_pos hi]
      have hr' :
          remaining - splitTokenBytesP (toks.get i hi) < minBlockBytes :=
        Nat.lt_of_le_of_lt (Nat.sub_le remaining (splitTokenBytesP (toks.get i hi))) hr
      have hstep : ∀ p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 pT
          q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 qT qb qc,
          chooseSplitsHeuristicP.go toks minBlockBytes softMaxBlockBytes checkTokens (i + 1)
            p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 pT
            q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 qT qb
            (remaining - splitTokenBytesP (toks.get i hi)) qc = qc := by
        intro p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 pT
          q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 qT qb qc
        exact ih (i + 1) (by omega)
          p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 pT
          q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 qT qb
          (remaining - splitTokenBytesP (toks.get i hi)) qc hr'
      have hnrem :
          ¬ remaining - splitTokenBytesP (toks.get i hi) ≥ minBlockBytes := by omega
      simp [hnrem, hstep]
    · rw [dif_neg hi]

private def splitSum10
    (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : Nat) : Nat :=
  a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9

private def splitBumpToNat
    (p : USize × USize × USize × USize × USize × USize × USize × USize × USize × USize) :
    Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat :=
  match p with
  | (a0, a1, a2, a3, a4, a5, a6, a7, a8, a9) =>
    (a0.toNat, a1.toNat, a2.toNat, a3.toNat, a4.toNat,
      a5.toNat, a6.toNat, a7.toNat, a8.toNat, a9.toNat)

theorem splitBumpN_sum (c n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 : Nat)
    (hc : c < 10) :
    let p := splitBumpN c n0 n1 n2 n3 n4 n5 n6 n7 n8 n9
    splitSum10 p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1
      p.2.2.2.2.2.1 p.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.1
      p.2.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2.2 =
        splitSum10 n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 + 1 := by
  by_cases h0 : c = 0
  · simp [h0, splitBumpN, splitSum10] <;> omega
  by_cases h1 : c = 1
  · simp [h1, splitBumpN, splitSum10] <;> omega
  by_cases h2 : c = 2
  · simp [h2, splitBumpN, splitSum10] <;> omega
  by_cases h3 : c = 3
  · simp [h3, splitBumpN, splitSum10] <;> omega
  by_cases h4 : c = 4
  · simp [h4, splitBumpN, splitSum10] <;> omega
  by_cases h5 : c = 5
  · simp [h5, splitBumpN, splitSum10] <;> omega
  by_cases h6 : c = 6
  · simp [h6, splitBumpN, splitSum10] <;> omega
  by_cases h7 : c = 7
  · simp [h7, splitBumpN, splitSum10] <;> omega
  by_cases h8 : c = 8
  · simp [h8, splitBumpN, splitSum10] <;> omega
  have h9 : c = 9 := by omega
  simp [h9, splitBumpN, splitSum10] <;> omega

theorem splitBumpU_toNat (c : USize)
    (n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 newTot : USize)
    (hc : c.toNat < 10)
    (hn : splitSum10 n0.toNat n1.toNat n2.toNat n3.toNat n4.toNat
      n5.toNat n6.toNat n7.toNat n8.toNat n9.toNat = newTot.toNat)
    (hfit : newTot.toNat + 1 < USize.size) :
    splitBumpToNat (splitBumpU c n0 n1 n2 n3 n4 n5 n6 n7 n8 n9) =
      splitBumpN c.toNat n0.toNat n1.toNat n2.toNat n3.toNat n4.toNat
        n5.toNat n6.toNat n7.toNat n8.toNat n9.toNat := by
  unfold splitSum10 at hn
  have hadd (x : USize) (hx : x.toNat ≤ newTot.toNat) :
      (x + 1).toNat = x.toNat + 1 := by
    rw [USize.toNat_add, USize.toNat_one]
    apply Nat.mod_eq_of_lt
    have hUS : USize.size = 2 ^ System.Platform.numBits := rfl
    rw [← hUS]
    omega
  have h0 := hadd n0 (by omega)
  have h1 := hadd n1 (by omega)
  have h2 := hadd n2 (by omega)
  have h3 := hadd n3 (by omega)
  have h4 := hadd n4 (by omega)
  have h5 := hadd n5 (by omega)
  have h6 := hadd n6 (by omega)
  have h7 := hadd n7 (by omega)
  have h8 := hadd n8 (by omega)
  have h9 := hadd n9 (by omega)
  by_cases hc0 : c.toNat = 0
  · have hcu : c = 0 := by
      apply USize.toNat_inj.mp
      rw [hc0, USize.toNat_zero]
    simp [hcu, splitBumpToNat, splitBumpU, splitBumpN, h0]
  by_cases hc1 : c.toNat = 1
  · have hcu : c = 1 := by
      apply USize.toNat_inj.mp
      rw [hc1, USize.toNat_one]
    simp [hcu, splitBumpToNat, splitBumpU, splitBumpN, h1, ← USize.toNat_inj]
  by_cases hc2 : c.toNat = 2
  · have hcu : c = 2 := by
      apply USize.toNat_inj.mp
      rw [hc2, USize.toNat_ofNat_of_lt
        (Nat.lt_of_lt_of_le (by decide) USize.le_size)]
    simp [hcu, splitBumpToNat, splitBumpU, splitBumpN, h2, ← USize.toNat_inj]
  by_cases hc3 : c.toNat = 3
  · have hcu : c = 3 := by
      apply USize.toNat_inj.mp
      rw [hc3, USize.toNat_ofNat_of_lt
        (Nat.lt_of_lt_of_le (by decide) USize.le_size)]
    simp [hcu, splitBumpToNat, splitBumpU, splitBumpN, h3, ← USize.toNat_inj]
  by_cases hc4 : c.toNat = 4
  · have hcu : c = 4 := by
      apply USize.toNat_inj.mp
      rw [hc4, USize.toNat_ofNat_of_lt
        (Nat.lt_of_lt_of_le (by decide) USize.le_size)]
    simp [hcu, splitBumpToNat, splitBumpU, splitBumpN, h4, ← USize.toNat_inj]
  by_cases hc5 : c.toNat = 5
  · have hcu : c = 5 := by
      apply USize.toNat_inj.mp
      rw [hc5, USize.toNat_ofNat_of_lt
        (Nat.lt_of_lt_of_le (by decide) USize.le_size)]
    simp [hcu, splitBumpToNat, splitBumpU, splitBumpN, h5, ← USize.toNat_inj]
  by_cases hc6 : c.toNat = 6
  · have hcu : c = 6 := by
      apply USize.toNat_inj.mp
      rw [hc6, USize.toNat_ofNat_of_lt
        (Nat.lt_of_lt_of_le (by decide) USize.le_size)]
    simp [hcu, splitBumpToNat, splitBumpU, splitBumpN, h6, ← USize.toNat_inj]
  by_cases hc7 : c.toNat = 7
  · have hcu : c = 7 := by
      apply USize.toNat_inj.mp
      rw [hc7, USize.toNat_ofNat_of_lt
        (Nat.lt_of_lt_of_le (by decide) USize.le_size)]
    simp [hcu, splitBumpToNat, splitBumpU, splitBumpN, h7, ← USize.toNat_inj]
  by_cases hc8 : c.toNat = 8
  · have hcu : c = 8 := by
      apply USize.toNat_inj.mp
      rw [hc8, USize.toNat_ofNat_of_lt
        (Nat.lt_of_lt_of_le (by decide) USize.le_size)]
    simp [hcu, splitBumpToNat, splitBumpU, splitBumpN, h8, ← USize.toNat_inj]
  have hc9 : c.toNat = 9 := by omega
  have hcu : c = 9 := by
    apply USize.toNat_inj.mp
    rw [hc9, USize.toNat_ofNat_of_lt
      (Nat.lt_of_lt_of_le (by decide) USize.le_size)]
  simp [hcu, splitBumpToNat, splitBumpU, splitBumpN, h9, ← USize.toNat_inj]

set_option maxHeartbeats 1000000 in
theorem chooseSplitsHeuristicPU_go_eq (toks : TokenArray) (endU : USize)
    (hend : endU.toNat = toks.size) (hbytes : toks.bytes.size < USize.size)
    (checkU : USize) (checkTokens : Nat)
    (hcheck : checkU.toNat = checkTokens) :
    ∀ (fuel : Nat) (i : USize), toks.size - i.toNat < fuel →
      ∀ (o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 oldTot : USize)
        (n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 newTot : USize)
        (blockBytes remaining : USize) (cuts : Array Nat),
        splitSum10 o0.toNat o1.toNat o2.toNat o3.toNat o4.toNat
            o5.toNat o6.toNat o7.toNat o8.toNat o9.toNat = oldTot.toNat →
        splitSum10 n0.toNat n1.toNat n2.toNat n3.toNat n4.toNat
            n5.toNat n6.toNat n7.toNat n8.toNat n9.toNat = newTot.toNat →
        oldTot.toNat + newTot.toNat ≤ i.toNat →
        blockBytes.toNat < splitSoftMaxBlockBytes →
        chooseSplitsHeuristicPU.go toks endU hend hbytes checkU i
            o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 oldTot
            n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 newTot blockBytes remaining cuts =
          chooseSplitsHeuristicP.go toks splitMinBlockBytes splitSoftMaxBlockBytes
            checkTokens i.toNat
            o0.toNat o1.toNat o2.toNat o3.toNat o4.toNat
            o5.toNat o6.toNat o7.toNat o8.toNat o9.toNat oldTot.toNat
            n0.toNat n1.toNat n2.toNat n3.toNat n4.toNat
            n5.toNat n6.toNat n7.toNat n8.toNat n9.toNat newTot.toNat
            blockBytes.toNat remaining.toNat cuts := by
  intro fuel
  induction fuel with
  | zero => intro i hf; omega
  | succ fuel ih =>
    intro i hf o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 oldTot
      n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 newTot blockBytes remaining cuts
      ho hn htot hblock
    unfold chooseSplitsHeuristicPU.go chooseSplitsHeuristicP.go
    by_cases hi : i < endU
    · have hiNat : i.toNat < toks.size := by
        rw [← hend]
        exact USize.lt_iff_toNat_lt.mp hi
      rw [dif_pos hi, dif_pos hiNat]
      have hbytesMul : toks.bytes.size = 4 * (toks.bytes.size / 4) := by
        have hm := Nat.mod_add_div toks.bytes.size 4
        rw [toks.aligned] at hm
        omega
      have hoff : ((4 : USize) * i).toNat = 4 * i.toNat := by
        rw [USize.toNat_mul]
        have h4 : (4 : USize).toNat = 4 := by
          exact USize.toNat_ofNat_of_lt
            (Nat.lt_of_lt_of_le (show 4 < 2 ^ 32 by omega) USize.le_size)
        rw [h4]
        apply Nat.mod_eq_of_lt
        have hUS : USize.size = 2 ^ System.Platform.numBits := rfl
        rw [← hUS]
        simp only [TokenArray.size] at hiNat
        rw [hbytesMul] at hbytes
        omega
      have ht :
          toks.bytes.ugetUInt32LE ((4 : USize) * i) (by
            rw [hoff]
            simp only [TokenArray.size] at hiNat
            rw [hbytesMul]
            omega) =
            toks.get i.toNat hiNat :=
        tokenArray_uget_eq_get toks i.toNat ((4 : USize) * i) hiNat hoff _
      simp only [ht]
      generalize htword : toks.get i.toNat hiNat = t
      have hsize : toks.size < USize.size := by
        simp only [TokenArray.size]
        omega
      have hstep : (i + 1).toNat = i.toNat + 1 := by
        rw [USize.toNat_add, USize.toNat_one]
        apply Nat.mod_eq_of_lt
        have hUS : USize.size = 2 ^ System.Platform.numBits := rfl
        rw [← hUS]
        omega
      have hfnext : toks.size - (i + 1).toNat < fuel := by
        rw [hstep]
        omega
      have hcNat : splitTokenClassP t < 10 := splitTokenClassP_lt t
      have hcU : (splitTokenClassPU t).toNat < 10 := by
        rw [splitTokenClassPU_toNat]
        exact hcNat
      have hnewFit : newTot.toNat + 1 < USize.size := by omega
      have hnew : (newTot + 1).toNat = newTot.toNat + 1 := by
        rw [USize.toNat_add, USize.toNat_one]
        apply Nat.mod_eq_of_lt
        have hUS : USize.size = 2 ^ System.Platform.numBits := rfl
        rw [← hUS]
        exact hnewFit
      generalize hbu :
        splitBumpU (splitTokenClassPU t) n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 = bu
      rcases bu with ⟨un0, un1, un2, un3, un4, un5, un6, un7, un8, un9⟩
      generalize hbn :
        splitBumpN (splitTokenClassP t) n0.toNat n1.toNat n2.toNat n3.toNat n4.toNat
          n5.toNat n6.toNat n7.toNat n8.toNat n9.toNat = bn
      rcases bn with ⟨nn0, nn1, nn2, nn3, nn4, nn5, nn6, nn7, nn8, nn9⟩
      have hbump := splitBumpU_toNat (splitTokenClassPU t)
        n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 newTot hcU hn hnewFit
      rw [hbu, splitTokenClassPU_toNat, hbn] at hbump
      simp only [splitBumpToNat, Prod.mk.injEq] at hbump
      rcases hbump with ⟨he0, he1, he2, he3, he4, he5, he6, he7, he8, he9⟩
      have hbumpSum := splitBumpN_sum (splitTokenClassP t)
        n0.toNat n1.toNat n2.toNat n3.toNat n4.toNat
        n5.toNat n6.toNat n7.toNat n8.toNat n9.toNat hcNat
      rw [hbn] at hbumpSum
      simp only at hbumpSum
      have hnsum :
          splitSum10 un0.toNat un1.toNat un2.toNat un3.toNat un4.toNat
            un5.toNat un6.toNat un7.toNat un8.toNat un9.toNat =
              (newTot + 1).toNat := by
        rw [he0, he1, he2, he3, he4, he5, he6, he7, he8, he9,
          hnew, hbumpSum, hn]
      have hblockAdd :
          (blockBytes + splitTokenBytesPU t).toNat =
            blockBytes.toNat + splitTokenBytesP t := by
        rw [USize.toNat_add, splitTokenBytesPU_toNat]
        apply Nat.mod_eq_of_lt
        have hUS : USize.size = 2 ^ System.Platform.numBits := rfl
        rw [← hUS]
        have htb := splitTokenBytesP_lt t
        simp only [splitSoftMaxBlockBytes] at hblock
        exact Nat.lt_of_lt_of_le (by omega) USize.le_size
      have hrem :
          (if splitTokenBytesPU t ≤ remaining then
              remaining - splitTokenBytesPU t else 0).toNat =
            remaining.toNat - splitTokenBytesP t := by
        split
        · rename_i hle
          rw [USize.toNat_sub_of_le _ _ hle, splitTokenBytesPU_toNat]
        · rename_i hnle
          simp only [USize.toNat_zero]
          have hnleNat : ¬ splitTokenBytesP t ≤ remaining.toNat := by
            rw [← splitTokenBytesPU_toNat]
            exact fun h => hnle (USize.le_iff_toNat_le.mpr h)
          omega
      have hconst (n : Nat) (hn32 : n < 2 ^ 32) :
          n.toUSize.toNat = n := by
        exact USize.toNat_ofNat_of_lt'
          (Nat.lt_of_lt_of_le hn32 USize.le_size)
      have hmin : splitMinBlockBytes.toUSize.toNat = splitMinBlockBytes :=
        hconst splitMinBlockBytes (by decide)
      have hsoft : splitSoftMaxBlockBytes.toUSize.toNat = splitSoftMaxBlockBytes :=
        hconst splitSoftMaxBlockBytes (by decide)
      have htotFit : oldTot.toNat + (newTot + 1).toNat < USize.size := by
        rw [hnew]
        omega
      have hmerge (a b : USize)
          (ha : a.toNat ≤ oldTot.toNat)
          (hb : b.toNat ≤ (newTot + 1).toNat) :
          (a + b).toNat = a.toNat + b.toNat := by
        rw [USize.toNat_add]
        apply Nat.mod_eq_of_lt
        have hUS : USize.size = 2 ^ System.Platform.numBits := rfl
        rw [← hUS]
        omega
      have hm0 := hmerge o0 un0 (by unfold splitSum10 at ho; omega)
        (by unfold splitSum10 at hnsum; omega)
      have hm1 := hmerge o1 un1 (by unfold splitSum10 at ho; omega)
        (by unfold splitSum10 at hnsum; omega)
      have hm2 := hmerge o2 un2 (by unfold splitSum10 at ho; omega)
        (by unfold splitSum10 at hnsum; omega)
      have hm3 := hmerge o3 un3 (by unfold splitSum10 at ho; omega)
        (by unfold splitSum10 at hnsum; omega)
      have hm4 := hmerge o4 un4 (by unfold splitSum10 at ho; omega)
        (by unfold splitSum10 at hnsum; omega)
      have hm5 := hmerge o5 un5 (by unfold splitSum10 at ho; omega)
        (by unfold splitSum10 at hnsum; omega)
      have hm6 := hmerge o6 un6 (by unfold splitSum10 at ho; omega)
        (by unfold splitSum10 at hnsum; omega)
      have hm7 := hmerge o7 un7 (by unfold splitSum10 at ho; omega)
        (by unfold splitSum10 at hnsum; omega)
      have hm8 := hmerge o8 un8 (by unfold splitSum10 at ho; omega)
        (by unfold splitSum10 at hnsum; omega)
      have hm9 := hmerge o9 un9 (by unfold splitSum10 at ho; omega)
        (by unfold splitSum10 at hnsum; omega)
      have hmtot : (oldTot + (newTot + 1)).toNat =
          oldTot.toNat + (newTot + 1).toNat := by
        rw [USize.toNat_add]
        apply Nat.mod_eq_of_lt
        have hUS : USize.size = 2 ^ System.Platform.numBits := rfl
        rw [← hUS]
        exact htotFit
      have hdiv :
          splitEndBlockCheckU
              o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 oldTot
              un0 un1 un2 un3 un4 un5 un6 un7 un8 un9 (newTot + 1)
              (blockBytes + splitTokenBytesPU t) =
            splitEndBlockCheck
              #[o0.toNat, o1.toNat, o2.toNat, o3.toNat, o4.toNat,
                o5.toNat, o6.toNat, o7.toNat, o8.toNat, o9.toNat]
              oldTot.toNat
              #[nn0, nn1, nn2, nn3, nn4, nn5, nn6, nn7, nn8, nn9]
              (newTot.toNat + 1) (blockBytes.toNat + splitTokenBytesP t) := by
        unfold splitEndBlockCheckU
        rw [he0, he1, he2, he3, he4, he5, he6, he7, he8, he9,
          hnew, hblockAdd]
        exact splitEndBlockCheckN_eq
          o0.toNat o1.toNat o2.toNat o3.toNat o4.toNat
          o5.toNat o6.toNat o7.toNat o8.toNat o9.toNat oldTot.toNat
          nn0 nn1 nn2 nn3 nn4 nn5 nn6 nn7 nn8 nn9
          (newTot.toNat + 1) (blockBytes.toNat + splitTokenBytesP t)
      generalize hremDef :
        (if splitTokenBytesPU t ≤ remaining then
          remaining - splitTokenBytesPU t else 0) = remU
      generalize hblockDef :
        blockBytes + splitTokenBytesPU t = blockU
      generalize hnewDef : newTot + 1 = newU
      have hremNat : remU.toNat = remaining.toNat - splitTokenBytesP t := by
        rw [← hremDef]
        exact hrem
      have hblockNat : blockU.toNat =
          blockBytes.toNat + splitTokenBytesP t := by
        rw [← hblockDef]
        exact hblockAdd
      have hnewNat : newU.toNat = newTot.toNat + 1 := by
        rw [← hnewDef]
        exact hnew
      have hdivGen :
          splitEndBlockCheckU
              o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 oldTot
              un0 un1 un2 un3 un4 un5 un6 un7 un8 un9 newU blockU =
            splitEndBlockCheck
              #[o0.toNat, o1.toNat, o2.toNat, o3.toNat, o4.toNat,
                o5.toNat, o6.toNat, o7.toNat, o8.toNat, o9.toNat]
              oldTot.toNat
              #[nn0, nn1, nn2, nn3, nn4, nn5, nn6, nn7, nn8, nn9]
              (newTot.toNat + 1) (blockBytes.toNat + splitTokenBytesP t) := by
        rw [← hnewDef, ← hblockDef]
        exact hdiv
      have hnsumNew :
          splitSum10 un0.toNat un1.toNat un2.toNat un3.toNat un4.toNat
            un5.toNat un6.toNat un7.toNat un8.toNat un9.toNat = newU.toNat := by
        rw [hnewNat]
        rw [hnew] at hnsum
        exact hnsum
      have htotalNew : oldTot.toNat + newU.toNat ≤ (i + 1).toNat := by
        rw [hnewNat, hstep]
        omega
      have keepEq (hb : blockU.toNat < splitSoftMaxBlockBytes) :
          chooseSplitsHeuristicPU.go toks endU hend hbytes checkU (i + 1)
              o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 oldTot
              un0 un1 un2 un3 un4 un5 un6 un7 un8 un9 newU blockU remU cuts =
            chooseSplitsHeuristicP.go toks splitMinBlockBytes splitSoftMaxBlockBytes
              checkTokens (i.toNat + 1)
              o0.toNat o1.toNat o2.toNat o3.toNat o4.toNat
              o5.toNat o6.toNat o7.toNat o8.toNat o9.toNat oldTot.toNat
              nn0 nn1 nn2 nn3 nn4 nn5 nn6 nn7 nn8 nn9
              (newTot.toNat + 1) (blockBytes.toNat + splitTokenBytesP t)
              (remaining.toNat - splitTokenBytesP t) cuts := by
        have hrec := ih (i + 1) hfnext
          o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 oldTot
          un0 un1 un2 un3 un4 un5 un6 un7 un8 un9 newU blockU remU cuts
          ho hnsumNew htotalNew hb
        simpa only [hstep, he0, he1, he2, he3, he4, he5, he6, he7, he8, he9,
          hnewNat, hblockNat, hremNat] using hrec
      simp only [USize.lt_iff_toNat_lt, USize.le_iff_toNat_le,
        hremNat, hblockNat, hnewNat, hmin, hsoft, hcheck, hdivGen]
      by_cases htail : remaining.toNat - splitTokenBytesP t < splitMinBlockBytes
      · rw [if_pos htail]
        have hnrem :
            ¬ remaining.toNat - splitTokenBytesP t ≥ splitMinBlockBytes := by omega
        simp only [hnrem, decide_false, Bool.and_false, Bool.false_eq_true, if_false]
        exact (chooseSplitsHeuristicP_go_no_remaining toks
          splitMinBlockBytes splitSoftMaxBlockBytes checkTokens
          (toks.size + 1) (i.toNat + 1) (by omega)
          o0.toNat o1.toNat o2.toNat o3.toNat o4.toNat
          o5.toNat o6.toNat o7.toNat o8.toNat o9.toNat oldTot.toNat
          nn0 nn1 nn2 nn3 nn4 nn5 nn6 nn7 nn8 nn9
          (newTot.toNat + 1) (blockBytes.toNat + splitTokenBytesP t)
          (remaining.toNat - splitTokenBytesP t) cuts htail).symm
      · rw [if_neg htail]
        have hremFloor :
            remaining.toNat - splitTokenBytesP t ≥ splitMinBlockBytes := by omega
        simp only [hremFloor, decide_true, Bool.and_true]
        by_cases hfloor :
            blockBytes.toNat + splitTokenBytesP t ≥ splitMinBlockBytes
        · rw [if_pos hfloor]
          simp only [hfloor, decide_true]
          let cutN :=
            decide (blockBytes.toNat + splitTokenBytesP t ≥ splitSoftMaxBlockBytes) ||
              decide (newTot.toNat + 1 ≥ checkTokens) &&
                decide (oldTot.toNat > 0) &&
                splitEndBlockCheck
                  #[o0.toNat, o1.toNat, o2.toNat, o3.toNat, o4.toNat,
                    o5.toNat, o6.toNat, o7.toNat, o8.toNat, o9.toNat]
                  oldTot.toNat
                  #[nn0, nn1, nn2, nn3, nn4, nn5, nn6, nn7, nn8, nn9]
                  (newTot.toNat + 1) (blockBytes.toNat + splitTokenBytesP t)
          by_cases hcut : cutN = true
          · change (if cutN = true then _ else _) = _
            rw [if_pos hcut, if_pos hcut]
            have hrec := ih (i + 1) hfnext
              0 0 0 0 0 0 0 0 0 0 0
              0 0 0 0 0 0 0 0 0 0 0
              0 remU (cuts.push (i + 1).toNat)
              (by rfl) (by rfl) (by simp) (by
                simp only [splitSoftMaxBlockBytes, USize.toNat_zero]
                omega)
            simpa only [hstep, hremNat, USize.toNat_zero, if_true] using hrec
          · change (if cutN = true then _ else _) = _
            rw [if_neg hcut, if_neg hcut]
            have hblockRec :
                blockBytes.toNat + splitTokenBytesP t < splitSoftMaxBlockBytes := by
              apply Nat.lt_of_not_ge
              intro hge'
              apply hcut
              simp [cutN, hge']
            by_cases hcad : newTot.toNat + 1 ≥ checkTokens
            · rw [if_pos hcad, if_pos hcad]
              have hmtotNew : (oldTot + newU).toNat =
                  oldTot.toNat + newU.toNat := by
                rw [← hnewDef]
                exact hmtot
              have homerge :
                  splitSum10 (o0 + un0).toNat (o1 + un1).toNat
                    (o2 + un2).toNat (o3 + un3).toNat (o4 + un4).toNat
                    (o5 + un5).toNat (o6 + un6).toNat (o7 + un7).toNat
                    (o8 + un8).toNat (o9 + un9).toNat =
                      (oldTot + newU).toNat := by
                rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9,
                  hmtotNew]
                unfold splitSum10 at ho hnsumNew ⊢
                omega
              have hrec := ih (i + 1) hfnext
                (o0 + un0) (o1 + un1) (o2 + un2) (o3 + un3) (o4 + un4)
                (o5 + un5) (o6 + un6) (o7 + un7) (o8 + un8) (o9 + un9)
                (oldTot + newU)
                0 0 0 0 0 0 0 0 0 0 0 blockU remU cuts
                homerge (by rfl) (by
                  rw [hmtotNew]
                  exact htotalNew) (by
                  rw [hblockNat]
                  exact hblockRec)
              simpa only [hstep, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8,
                hm9, he0, he1, he2, he3, he4, he5, he6, he7, he8, he9,
                hmtotNew, hnewNat, hblockNat, hremNat, USize.toNat_zero,
                if_true] using hrec
            · rw [if_neg hcad, if_neg hcad]
              exact keepEq (by
                rw [hblockNat]
                exact hblockRec)
        · rw [if_neg hfloor]
          simp only [hfloor, decide_false, Bool.false_eq_true, if_false]
          exact keepEq (by
            rw [hblockNat]
            have hsoftGt : splitMinBlockBytes < splitSoftMaxBlockBytes := by decide
            omega)
    · have hiNat : ¬ i.toNat < toks.size := by
        rw [← hend]
        exact fun h => hi (USize.lt_iff_toNat_lt.mpr h)
      rw [dif_neg hi, dif_neg hiNat]

theorem chooseSplitsHeuristicPU_eq (toks : TokenArray) (totalBytes checkTokens : Nat) :
    chooseSplitsHeuristicPU toks totalBytes checkTokens =
      chooseSplitsHeuristicP toks totalBytes splitMinBlockBytes
        splitSoftMaxBlockBytes checkTokens := by
  unfold chooseSplitsHeuristicPU chooseSplitsHeuristicP
  split
  · rename_i hg
    have hbytes : toks.bytes.size < USize.size := by
      rw [← hg.1]
      exact USize.toNat_lt_two_pow_numBits _
    have hgo := chooseSplitsHeuristicPU_go_eq toks toks.size.toUSize hg.2.1 hbytes
      checkTokens.toUSize checkTokens hg.2.2.2
      (toks.size + 1) 0 (by omega)
      0 0 0 0 0 0 0 0 0 0 0
      0 0 0 0 0 0 0 0 0 0 0
      0 totalBytes.toUSize #[]
      (by rfl) (by rfl) (by simp) (by
        simp only [splitSoftMaxBlockBytes, USize.toNat_zero]
        omega)
    have hlist := congrArg Array.toList hgo
    simpa only [hg.2.2.1, USize.toNat_zero] using hlist
  · rfl

end Zip.Native.Deflate
