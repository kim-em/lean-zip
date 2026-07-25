import Zip.Spec.SplitWalkerCorrect
import Zip.Spec.LZ77PackedCorrect
import Zip.Spec.DeflateBlockSplit

/-!
# Packed split-walker correctness

The production split walker carries its twenty observation counters in seven
`UInt64` words. This file proves that decoding a 15-bit counter after each bump
and a 20-bit counter after each merge yields the scalar `USize` state, then
lifts those local facts through the complete walk.

The generic equality is intentionally qualified by positive token lengths:
arbitrary packed reference words can encode length zero and overflow a recent
field without advancing the byte floors. `lzMatchP` cannot produce such words,
so `chooseSplitsHeuristicPUPacked_lzMatchP_eq` discharges the precondition from
the matcher contracts used by `deflateRaw`.
-/

namespace Zip.Native.Deflate

private theorem splitField15_add0 (w : UInt64)
    (h : splitField15 w 0 < 0x7FFF) :
    splitField15 (w + 1) 0 = splitField15 w 0 + 1 ∧
    splitField15 (w + 1) 15 = splitField15 w 15 ∧
    splitField15 (w + 1) 30 = splitField15 w 30 ∧
    splitField15 (w + 1) 45 = splitField15 w 45 := by
  unfold splitField15 at *
  bv_decide

private theorem splitField15_add15 (w : UInt64)
    (h : splitField15 w 15 < 0x7FFF) :
    splitField15 (w + ((1 : UInt64) <<< 15)) 0 = splitField15 w 0 ∧
    splitField15 (w + ((1 : UInt64) <<< 15)) 15 = splitField15 w 15 + 1 ∧
    splitField15 (w + ((1 : UInt64) <<< 15)) 30 = splitField15 w 30 ∧
    splitField15 (w + ((1 : UInt64) <<< 15)) 45 = splitField15 w 45 := by
  unfold splitField15 at *
  bv_decide

private theorem splitField15_add30 (w : UInt64)
    (h : splitField15 w 30 < 0x7FFF) :
    splitField15 (w + ((1 : UInt64) <<< 30)) 0 = splitField15 w 0 ∧
    splitField15 (w + ((1 : UInt64) <<< 30)) 15 = splitField15 w 15 ∧
    splitField15 (w + ((1 : UInt64) <<< 30)) 30 = splitField15 w 30 + 1 ∧
    splitField15 (w + ((1 : UInt64) <<< 30)) 45 = splitField15 w 45 := by
  unfold splitField15 at *
  bv_decide

private theorem splitField15_add45 (w : UInt64)
    (h : splitField15 w 45 < 0x7FFF) :
    splitField15 (w + ((1 : UInt64) <<< 45)) 0 = splitField15 w 0 ∧
    splitField15 (w + ((1 : UInt64) <<< 45)) 15 = splitField15 w 15 ∧
    splitField15 (w + ((1 : UInt64) <<< 45)) 30 = splitField15 w 30 ∧
    splitField15 (w + ((1 : UInt64) <<< 45)) 45 = splitField15 w 45 + 1 := by
  unfold splitField15 at *
  bv_decide

private theorem splitField20_merge3 (o q0 q1 q2 : UInt64)
    (h0 : splitField20 o 0 + q0 < 0x100000)
    (h1 : splitField20 o 20 + q1 < 0x100000)
    (h2 : splitField20 o 40 + q2 < 0x100000)
    (hq0 : q0 < 0x8000) (hq1 : q1 < 0x8000) (hq2 : q2 < 0x8000) :
    splitField20 (o + q0 + (q1 <<< 20) + (q2 <<< 40)) 0 =
        splitField20 o 0 + q0 ∧
    splitField20 (o + q0 + (q1 <<< 20) + (q2 <<< 40)) 20 =
        splitField20 o 20 + q1 ∧
    splitField20 (o + q0 + (q1 <<< 20) + (q2 <<< 40)) 40 =
        splitField20 o 40 + q2 := by
  unfold splitField20 at *
  bv_decide

private theorem splitField20_merge0 (o q : UInt64)
    (h : splitField20 o 0 + q < 0x100000) :
    splitField20 (o + q) 0 = splitField20 o 0 + q := by
  unfold splitField20 at *
  bv_decide

private theorem splitField15_toNat_lt (w shift : UInt64) :
    (splitField15 w shift).toNat < 32768 := by
  have h : splitField15 w shift < 32768 := by
    unfold splitField15
    bv_decide
  have hn := UInt64.lt_iff_toNat_lt.mp h
  have hc : (32768 : UInt64).toNat = 32768 := by decide
  rw [hc] at hn
  exact hn

private theorem splitField20_toNat_lt (w shift : UInt64) :
    (splitField20 w shift).toNat < 1048576 := by
  have h : splitField20 w shift < 1048576 := by
    unfold splitField20
    bv_decide
  have hn := UInt64.lt_iff_toNat_lt.mp h
  have hc : (1048576 : UInt64).toNat = 1048576 := by decide
  rw [hc] at hn
  exact hn

private theorem splitToUSize_add_small (x y : UInt64)
    (hx : x.toNat < 1048576) (hy : y.toNat < 32768) :
    (x + y).toUSize = x.toUSize + y.toUSize := by
  apply USize.toNat_inj.mp
  rw [UInt64.toNat_toUSize, UInt64.toNat_add, USize.toNat_add,
    UInt64.toNat_toUSize, UInt64.toNat_toUSize]
  have hsum32 : x.toNat + y.toNat < 2 ^ 32 := by omega
  have hsum64 : x.toNat + y.toNat < 2 ^ 64 :=
    Nat.lt_trans hsum32 (by decide)
  have hxfit : x.toNat < USize.size :=
    Nat.lt_of_lt_of_le (by omega) USize.le_size
  have hyfit : y.toNat < USize.size :=
    Nat.lt_of_lt_of_le (by omega) USize.le_size
  have hsumFit : x.toNat + y.toNat < USize.size :=
    Nat.lt_of_lt_of_le hsum32 USize.le_size
  rw [Nat.mod_eq_of_lt hsum64, Nat.mod_eq_of_lt hxfit,
    Nat.mod_eq_of_lt hyfit, Nat.mod_eq_of_lt hsumFit]

private theorem splitField20_sum_lt (x y : UInt64)
    (_hx : x.toNat < 1048576) (_hy : y.toNat < 32768)
    (hxy : x.toNat + y.toNat < 1048576) :
    x + y < 0x100000 := by
  apply UInt64.lt_iff_toNat_lt.mpr
  rw [UInt64.toNat_add]
  have hsum64 : x.toNat + y.toNat < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt hsum64]
  have hc : (0x100000 : UInt64).toNat = 1048576 := by decide
  rw [hc]
  exact hxy

set_option maxHeartbeats 1000000 in
private theorem splitUnpack20_merge
    (oA oB oC oD nA nB nC : UInt64)
    (h0 : (splitField20 oA 0).toNat + (splitField15 nA 0).toNat < 1048576)
    (h1 : (splitField20 oA 20).toNat + (splitField15 nA 15).toNat < 1048576)
    (h2 : (splitField20 oA 40).toNat + (splitField15 nA 30).toNat < 1048576)
    (h3 : (splitField20 oB 0).toNat + (splitField15 nA 45).toNat < 1048576)
    (h4 : (splitField20 oB 20).toNat + (splitField15 nB 0).toNat < 1048576)
    (h5 : (splitField20 oB 40).toNat + (splitField15 nB 15).toNat < 1048576)
    (h6 : (splitField20 oC 0).toNat + (splitField15 nB 30).toNat < 1048576)
    (h7 : (splitField20 oC 20).toNat + (splitField15 nB 45).toNat < 1048576)
    (h8 : (splitField20 oC 40).toNat + (splitField15 nC 0).toNat < 1048576)
    (h9 : (splitField20 oD 0).toNat + (splitField15 nC 15).toNat < 1048576) :
    let q := splitMergePacked20 oA oB oC oD nA nB nC
    splitUnpack20 q.1 q.2.1 q.2.2.1 q.2.2.2 =
      let o := splitUnpack20 oA oB oC oD
      let n := splitUnpack15 nA nB nC
      (o.1 + n.1, o.2.1 + n.2.1, o.2.2.1 + n.2.2.1,
        o.2.2.2.1 + n.2.2.2.1, o.2.2.2.2.1 + n.2.2.2.2.1,
        o.2.2.2.2.2.1 + n.2.2.2.2.2.1,
        o.2.2.2.2.2.2.1 + n.2.2.2.2.2.2.1,
        o.2.2.2.2.2.2.2.1 + n.2.2.2.2.2.2.2.1,
        o.2.2.2.2.2.2.2.2.1 + n.2.2.2.2.2.2.2.2.1,
        o.2.2.2.2.2.2.2.2.2 + n.2.2.2.2.2.2.2.2.2) := by
  have hoA0 := splitField20_toNat_lt oA 0
  have hoA20 := splitField20_toNat_lt oA 20
  have hoA40 := splitField20_toNat_lt oA 40
  have hoB0 := splitField20_toNat_lt oB 0
  have hoB20 := splitField20_toNat_lt oB 20
  have hoB40 := splitField20_toNat_lt oB 40
  have hoC0 := splitField20_toNat_lt oC 0
  have hoC20 := splitField20_toNat_lt oC 20
  have hoC40 := splitField20_toNat_lt oC 40
  have hoD0 := splitField20_toNat_lt oD 0
  have hnA0 := splitField15_toNat_lt nA 0
  have hnA15 := splitField15_toNat_lt nA 15
  have hnA30 := splitField15_toNat_lt nA 30
  have hnA45 := splitField15_toNat_lt nA 45
  have hnB0 := splitField15_toNat_lt nB 0
  have hnB15 := splitField15_toNat_lt nB 15
  have hnB30 := splitField15_toNat_lt nB 30
  have hnB45 := splitField15_toNat_lt nB 45
  have hnC0 := splitField15_toNat_lt nC 0
  have hnC15 := splitField15_toNat_lt nC 15
  have hfA := splitField20_merge3 oA (splitField15 nA 0)
    (splitField15 nA 15) (splitField15 nA 30)
    (splitField20_sum_lt _ _ hoA0 hnA0 h0)
    (splitField20_sum_lt _ _ hoA20 hnA15 h1)
    (splitField20_sum_lt _ _ hoA40 hnA30 h2)
    (by unfold splitField15; bv_decide)
    (by unfold splitField15; bv_decide)
    (by unfold splitField15; bv_decide)
  have hfB := splitField20_merge3 oB (splitField15 nA 45)
    (splitField15 nB 0) (splitField15 nB 15)
    (splitField20_sum_lt _ _ hoB0 hnA45 h3)
    (splitField20_sum_lt _ _ hoB20 hnB0 h4)
    (splitField20_sum_lt _ _ hoB40 hnB15 h5)
    (by unfold splitField15; bv_decide)
    (by unfold splitField15; bv_decide)
    (by unfold splitField15; bv_decide)
  have hfC := splitField20_merge3 oC (splitField15 nB 30)
    (splitField15 nB 45) (splitField15 nC 0)
    (splitField20_sum_lt _ _ hoC0 hnB30 h6)
    (splitField20_sum_lt _ _ hoC20 hnB45 h7)
    (splitField20_sum_lt _ _ hoC40 hnC0 h8)
    (by unfold splitField15; bv_decide)
    (by unfold splitField15; bv_decide)
    (by unfold splitField15; bv_decide)
  have hfD := splitField20_merge0 oD (splitField15 nC 15)
    (splitField20_sum_lt _ _ hoD0 hnC15 h9)
  have hu0 := splitToUSize_add_small _ _ hoA0 hnA0
  have hu1 := splitToUSize_add_small _ _ hoA20 hnA15
  have hu2 := splitToUSize_add_small _ _ hoA40 hnA30
  have hu3 := splitToUSize_add_small _ _ hoB0 hnA45
  have hu4 := splitToUSize_add_small _ _ hoB20 hnB0
  have hu5 := splitToUSize_add_small _ _ hoB40 hnB15
  have hu6 := splitToUSize_add_small _ _ hoC0 hnB30
  have hu7 := splitToUSize_add_small _ _ hoC20 hnB45
  have hu8 := splitToUSize_add_small _ _ hoC40 hnC0
  have hu9 := splitToUSize_add_small _ _ hoD0 hnC15
  simp [splitMergePacked20, splitUnpack20, splitUnpack15,
    hfA.1, hfA.2.1, hfA.2.2, hfB.1, hfB.2.1, hfB.2.2,
    hfC.1, hfC.2.1, hfC.2.2, hfD,
    hu0, hu1, hu2, hu3, hu4, hu5, hu6, hu7, hu8, hu9]

private theorem splitPackedClass_eq (w : UInt32) :
    (if w &&& ((1 : UInt32) <<< 31) = 0 then
        (((w >>> 5) &&& 6) ||| (w &&& 1)).toUInt64
      else if ((w >>> 16) &&& 0x7FFF) ≥ 9 then 9 else 8).toUSize =
      splitTokenClassPU w := by
  apply USize.toNat_inj.mp
  rw [splitTokenClassPU_toNat]
  unfold splitTokenClassP splitNumLiteralClasses
  split
  · have heq :
        (((w >>> (5 : UInt32)) &&& (6 : UInt32)) ||| (w &&& (1 : UInt32))) =
          ((((w.toUInt8 >>> (5 : UInt8)) &&& (6 : UInt8)) |||
            (w.toUInt8 &&& (1 : UInt8))).toUInt32) := by
        bv_decide
    rw [UInt64.toNat_toUSize, UInt32.toNat_toUInt64, heq,
      UInt8.toNat_toUInt32]
    apply Nat.mod_eq_of_lt
    exact Nat.lt_of_lt_of_le (UInt8.toNat_lt _)
      (Nat.le_trans (by decide) USize.le_size)
  · split <;> simp_all [UInt32.le_iff_toNat_le]

private theorem splitPackedClass_lt (w : UInt32) :
    (if w &&& ((1 : UInt32) <<< 31) = 0 then
        (((w >>> 5) &&& 6) ||| (w &&& 1)).toUInt64
      else if ((w >>> 16) &&& 0x7FFF) ≥ 9 then 9 else 8) < 10 := by
  split
  · bv_decide
  · split <;> simp_all

private theorem splitField15_toUSize_toNat (w shift : UInt64) :
    (splitField15 w shift).toUSize.toNat = (splitField15 w shift).toNat := by
  rw [UInt64.toNat_toUSize]
  apply Nat.mod_eq_of_lt
  have h := Nat.lt_of_lt_of_le (splitField15_toNat_lt w shift)
    (Nat.le_trans (by decide : 32768 ≤ 2 ^ 32) USize.le_size)
  have hUS : USize.size = 2 ^ System.Platform.numBits := rfl
  rw [← hUS]
  exact h

private theorem splitField20_toUSize_toNat (w shift : UInt64) :
    (splitField20 w shift).toUSize.toNat = (splitField20 w shift).toNat := by
  rw [UInt64.toNat_toUSize]
  apply Nat.mod_eq_of_lt
  have h := Nat.lt_of_lt_of_le (splitField20_toNat_lt w shift)
    (Nat.le_trans (by decide : 1048576 ≤ 2 ^ 32) USize.le_size)
  have hUS : USize.size = 2 ^ System.Platform.numBits := rfl
  rw [← hUS]
  exact h

private def splitPackedSum10
    (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : Nat) : Nat :=
  a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9

private theorem splitBumpU_sum (c : USize)
    (n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 newTot : USize)
    (hc : c.toNat < 10)
    (hn : splitPackedSum10 n0.toNat n1.toNat n2.toNat n3.toNat n4.toNat
      n5.toNat n6.toNat n7.toNat n8.toNat n9.toNat = newTot.toNat)
    (hfit : newTot.toNat + 1 < USize.size) :
    let p := splitBumpU c n0 n1 n2 n3 n4 n5 n6 n7 n8 n9
    splitPackedSum10 p.1.toNat p.2.1.toNat p.2.2.1.toNat p.2.2.2.1.toNat
      p.2.2.2.2.1.toNat p.2.2.2.2.2.1.toNat p.2.2.2.2.2.2.1.toNat
      p.2.2.2.2.2.2.2.1.toNat p.2.2.2.2.2.2.2.2.1.toNat
      p.2.2.2.2.2.2.2.2.2.toNat = (newTot + 1).toNat := by
  generalize hbu : splitBumpU c n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 = bu
  rcases bu with ⟨un0, un1, un2, un3, un4, un5, un6, un7, un8, un9⟩
  generalize hbn : splitBumpN c.toNat n0.toNat n1.toNat n2.toNat n3.toNat
    n4.toNat n5.toNat n6.toNat n7.toNat n8.toNat n9.toNat = bn
  rcases bn with ⟨nn0, nn1, nn2, nn3, nn4, nn5, nn6, nn7, nn8, nn9⟩
  have hbump := splitBumpU_toNat c
    n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 newTot hc hn hfit
  rw [hbu, hbn] at hbump
  change
    (un0.toNat, un1.toNat, un2.toNat, un3.toNat, un4.toNat,
      un5.toNat, un6.toNat, un7.toNat, un8.toNat, un9.toNat) =
    (nn0, nn1, nn2, nn3, nn4, nn5, nn6, nn7, nn8, nn9) at hbump
  simp only [Prod.mk.injEq] at hbump
  rcases hbump with ⟨he0, he1, he2, he3, he4, he5, he6, he7, he8, he9⟩
  have hbumpSum := splitBumpN_sum c.toNat
    n0.toNat n1.toNat n2.toNat n3.toNat n4.toNat
    n5.toNat n6.toNat n7.toNat n8.toNat n9.toNat hc
  rw [hbn] at hbumpSum
  change splitPackedSum10 nn0 nn1 nn2 nn3 nn4 nn5 nn6 nn7 nn8 nn9 =
    splitPackedSum10 n0.toNat n1.toNat n2.toNat n3.toNat n4.toNat
      n5.toNat n6.toNat n7.toNat n8.toNat n9.toNat + 1 at hbumpSum
  have hnew : (newTot + 1).toNat = newTot.toNat + 1 := by
    rw [USize.toNat_add, USize.toNat_one]
    apply Nat.mod_eq_of_lt
    have hUS : USize.size = 2 ^ System.Platform.numBits := rfl
    rw [← hUS]
    exact hfit
  change splitPackedSum10 un0.toNat un1.toNat un2.toNat un3.toNat un4.toNat
    un5.toNat un6.toNat un7.toNat un8.toNat un9.toNat = (newTot + 1).toNat
  rw [he0, he1, he2, he3, he4, he5, he6, he7, he8, he9,
    hnew, hbumpSum, hn]

private theorem splitUnpack15_fields_lt
    (nA nB nC : UInt64)
    (n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 newTot blockBytes checkU : USize)
    (hN : splitUnpack15 nA nB nC =
      (n0, n1, n2, n3, n4, n5, n6, n7, n8, n9))
    (hn : splitPackedSum10 n0.toNat n1.toNat n2.toNat n3.toNat n4.toNat
      n5.toNat n6.toNat n7.toNat n8.toNat n9.toNat = newTot.toNat)
    (htot : newTot.toNat ≤ blockBytes.toNat)
    (hcad : blockBytes.toNat < splitMinBlockBytes ∨
      newTot.toNat < checkU.toNat)
    (hcheck : checkU.toNat ≤ 32767) :
    splitField15 nA 0 < 32767 ∧ splitField15 nA 15 < 32767 ∧
    splitField15 nA 30 < 32767 ∧ splitField15 nA 45 < 32767 ∧
    splitField15 nB 0 < 32767 ∧ splitField15 nB 15 < 32767 ∧
    splitField15 nB 30 < 32767 ∧ splitField15 nB 45 < 32767 ∧
    splitField15 nC 0 < 32767 ∧ splitField15 nC 15 < 32767 := by
  have hN' := hN
  simp only [splitUnpack15, Prod.mk.injEq] at hN'
  rcases hN' with ⟨he0, he1, he2, he3, he4, he5, he6, he7, he8, he9⟩
  have hnew : newTot.toNat < 32767 := by
    rcases hcad with hfloor | hcheck'
    · simp only [splitMinBlockBytes] at hfloor
      omega
    · omega
  unfold splitPackedSum10 at hn
  have hconst : (32767 : UInt64).toNat = 32767 := by decide
  constructor
  · apply UInt64.lt_iff_toNat_lt.mpr
    rw [hconst, ← splitField15_toUSize_toNat, he0]
    omega
  constructor
  · apply UInt64.lt_iff_toNat_lt.mpr
    rw [hconst, ← splitField15_toUSize_toNat, he1]
    omega
  constructor
  · apply UInt64.lt_iff_toNat_lt.mpr
    rw [hconst, ← splitField15_toUSize_toNat, he2]
    omega
  constructor
  · apply UInt64.lt_iff_toNat_lt.mpr
    rw [hconst, ← splitField15_toUSize_toNat, he3]
    omega
  constructor
  · apply UInt64.lt_iff_toNat_lt.mpr
    rw [hconst, ← splitField15_toUSize_toNat, he4]
    omega
  constructor
  · apply UInt64.lt_iff_toNat_lt.mpr
    rw [hconst, ← splitField15_toUSize_toNat, he5]
    omega
  constructor
  · apply UInt64.lt_iff_toNat_lt.mpr
    rw [hconst, ← splitField15_toUSize_toNat, he6]
    omega
  constructor
  · apply UInt64.lt_iff_toNat_lt.mpr
    rw [hconst, ← splitField15_toUSize_toNat, he7]
    omega
  constructor
  · apply UInt64.lt_iff_toNat_lt.mpr
    rw [hconst, ← splitField15_toUSize_toNat, he8]
    omega
  · apply UInt64.lt_iff_toNat_lt.mpr
    rw [hconst, ← splitField15_toUSize_toNat, he9]
    omega

private theorem splitUnpack20_merge_bounds
    (oA oB oC oD nA nB nC : UInt64)
    (o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 oldTot : USize)
    (n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 newTot blockBytes : USize)
    (hO : splitUnpack20 oA oB oC oD =
      (o0, o1, o2, o3, o4, o5, o6, o7, o8, o9))
    (hN : splitUnpack15 nA nB nC =
      (n0, n1, n2, n3, n4, n5, n6, n7, n8, n9))
    (ho : splitPackedSum10 o0.toNat o1.toNat o2.toNat o3.toNat o4.toNat
      o5.toNat o6.toNat o7.toNat o8.toNat o9.toNat = oldTot.toNat)
    (hn : splitPackedSum10 n0.toNat n1.toNat n2.toNat n3.toNat n4.toNat
      n5.toNat n6.toNat n7.toNat n8.toNat n9.toNat = newTot.toNat)
    (htot : oldTot.toNat + newTot.toNat ≤ blockBytes.toNat)
    (hblock : blockBytes.toNat < splitSoftMaxBlockBytes) :
    (splitField20 oA 0).toNat + (splitField15 nA 0).toNat < 1048576 ∧
    (splitField20 oA 20).toNat + (splitField15 nA 15).toNat < 1048576 ∧
    (splitField20 oA 40).toNat + (splitField15 nA 30).toNat < 1048576 ∧
    (splitField20 oB 0).toNat + (splitField15 nA 45).toNat < 1048576 ∧
    (splitField20 oB 20).toNat + (splitField15 nB 0).toNat < 1048576 ∧
    (splitField20 oB 40).toNat + (splitField15 nB 15).toNat < 1048576 ∧
    (splitField20 oC 0).toNat + (splitField15 nB 30).toNat < 1048576 ∧
    (splitField20 oC 20).toNat + (splitField15 nB 45).toNat < 1048576 ∧
    (splitField20 oC 40).toNat + (splitField15 nC 0).toNat < 1048576 ∧
    (splitField20 oD 0).toNat + (splitField15 nC 15).toNat < 1048576 := by
  have hO' := hO
  have hN' := hN
  simp only [splitUnpack20, Prod.mk.injEq] at hO'
  simp only [splitUnpack15, Prod.mk.injEq] at hN'
  rcases hO' with ⟨hoe0, hoe1, hoe2, hoe3, hoe4, hoe5, hoe6, hoe7, hoe8, hoe9⟩
  rcases hN' with ⟨hne0, hne1, hne2, hne3, hne4, hne5, hne6, hne7, hne8, hne9⟩
  unfold splitPackedSum10 at ho hn
  simp only [splitSoftMaxBlockBytes] at hblock
  constructor
  · rw [← splitField20_toUSize_toNat, hoe0,
      ← splitField15_toUSize_toNat, hne0]
    omega
  constructor
  · rw [← splitField20_toUSize_toNat, hoe1,
      ← splitField15_toUSize_toNat, hne1]
    omega
  constructor
  · rw [← splitField20_toUSize_toNat, hoe2,
      ← splitField15_toUSize_toNat, hne2]
    omega
  constructor
  · rw [← splitField20_toUSize_toNat, hoe3,
      ← splitField15_toUSize_toNat, hne3]
    omega
  constructor
  · rw [← splitField20_toUSize_toNat, hoe4,
      ← splitField15_toUSize_toNat, hne4]
    omega
  constructor
  · rw [← splitField20_toUSize_toNat, hoe5,
      ← splitField15_toUSize_toNat, hne5]
    omega
  constructor
  · rw [← splitField20_toUSize_toNat, hoe6,
      ← splitField15_toUSize_toNat, hne6]
    omega
  constructor
  · rw [← splitField20_toUSize_toNat, hoe7,
      ← splitField15_toUSize_toNat, hne7]
    omega
  constructor
  · rw [← splitField20_toUSize_toNat, hoe8,
      ← splitField15_toUSize_toNat, hne8]
    omega
  · rw [← splitField20_toUSize_toNat, hoe9,
      ← splitField15_toUSize_toNat, hne9]
    omega

private theorem splitToUSize_add_one (x : UInt64) (h : x < 32767) :
    (x + 1).toUSize = x.toUSize + 1 := by
  apply USize.toNat_inj.mp
  rw [UInt64.toNat_toUSize, USize.toNat_add, USize.toNat_one,
    UInt64.toNat_toUSize, UInt64.toNat_add, UInt64.toNat_one]
  have hlt := UInt64.lt_iff_toNat_lt.mp h
  have hc : (32767 : UInt64).toNat = 32767 := by decide
  rw [hc] at hlt
  have h64 : x.toNat + 1 < 2 ^ 64 := by omega
  have hfit : x.toNat + 1 < USize.size := by
    exact Nat.lt_of_lt_of_le (by omega) USize.le_size
  have hxfit : x.toNat < USize.size := by omega
  rw [Nat.mod_eq_of_lt h64, Nat.mod_eq_of_lt hfit,
    Nat.mod_eq_of_lt hxfit, Nat.mod_eq_of_lt hfit]

set_option maxHeartbeats 1000000 in
private theorem splitUnpack15_bump (cls a b c : UInt64)
    (hc : cls < 10)
    (h0 : splitField15 a 0 < 32767) (h1 : splitField15 a 15 < 32767)
    (h2 : splitField15 a 30 < 32767) (h3 : splitField15 a 45 < 32767)
    (h4 : splitField15 b 0 < 32767) (h5 : splitField15 b 15 < 32767)
    (h6 : splitField15 b 30 < 32767) (h7 : splitField15 b 45 < 32767)
    (h8 : splitField15 c 0 < 32767) (h9 : splitField15 c 15 < 32767) :
    let q := splitBumpPacked15 cls a b c
    splitUnpack15 q.1 q.2.1 q.2.2 =
      let p := splitUnpack15 a b c
      splitBumpU cls.toUSize p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1
        p.2.2.2.2.2.1 p.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.1
        p.2.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2.2 := by
  have hu0 := splitToUSize_add_one (splitField15 a 0) h0
  have hu1 := splitToUSize_add_one (splitField15 a 15) h1
  have hu2 := splitToUSize_add_one (splitField15 a 30) h2
  have hu3 := splitToUSize_add_one (splitField15 a 45) h3
  have hu4 := splitToUSize_add_one (splitField15 b 0) h4
  have hu5 := splitToUSize_add_one (splitField15 b 15) h5
  have hu6 := splitToUSize_add_one (splitField15 b 30) h6
  have hu7 := splitToUSize_add_one (splitField15 b 45) h7
  have hu8 := splitToUSize_add_one (splitField15 c 0) h8
  have hu9 := splitToUSize_add_one (splitField15 c 15) h9
  by_cases hc0 : cls = 0
  · subst cls
    have hf := splitField15_add0 a h0
    simp [splitBumpPacked15, splitUnpack15, splitBumpU, hf.1, hf.2.1,
      hf.2.2.1, hf.2.2.2, hu0]
  by_cases hc1 : cls = 1
  · subst cls
    have hf := splitField15_add15 a h1
    simp [splitBumpPacked15, splitUnpack15, splitBumpU, hf.1, hf.2.1,
      hf.2.2.1, hf.2.2.2, hu1, ← USize.toNat_inj]
  by_cases hc2 : cls = 2
  · subst cls
    have hf := splitField15_add30 a h2
    simp [splitBumpPacked15, splitUnpack15, splitBumpU, hf.1, hf.2.1,
      hf.2.2.1, hf.2.2.2, hu2, ← USize.toNat_inj]
  by_cases hc3 : cls = 3
  · subst cls
    have hf := splitField15_add45 a h3
    simp [splitBumpPacked15, splitUnpack15, splitBumpU, hf.1, hf.2.1,
      hf.2.2.1, hf.2.2.2, hu3, ← USize.toNat_inj]
  by_cases hc4 : cls = 4
  · subst cls
    have hf := splitField15_add0 b h4
    simp [splitBumpPacked15, splitUnpack15, splitBumpU, hf.1, hf.2.1,
      hf.2.2.1, hf.2.2.2, hu4, ← USize.toNat_inj]
  by_cases hc5 : cls = 5
  · subst cls
    have hf := splitField15_add15 b h5
    simp [splitBumpPacked15, splitUnpack15, splitBumpU, hf.1, hf.2.1,
      hf.2.2.1, hf.2.2.2, hu5, ← USize.toNat_inj]
  by_cases hc6 : cls = 6
  · subst cls
    have hf := splitField15_add30 b h6
    simp [splitBumpPacked15, splitUnpack15, splitBumpU, hf.1, hf.2.1,
      hf.2.2.1, hf.2.2.2, hu6, ← USize.toNat_inj]
  by_cases hc7 : cls = 7
  · subst cls
    have hf := splitField15_add45 b h7
    simp [splitBumpPacked15, splitUnpack15, splitBumpU, hf.1, hf.2.1,
      hf.2.2.1, hf.2.2.2, hu7, ← USize.toNat_inj]
  by_cases hc8 : cls = 8
  · subst cls
    have hf := splitField15_add0 c h8
    simp [splitBumpPacked15, splitUnpack15, splitBumpU, hf.1, hf.2.1, hu8,
      ← USize.toNat_inj]
  have hc9 : cls = 9 := by bv_decide
  subst cls
  have hf := splitField15_add15 c h9
  simp [splitBumpPacked15, splitUnpack15, splitBumpU, hf.1, hf.2.1, hu9,
    ← USize.toNat_inj]

set_option maxHeartbeats 10000000 in
private theorem chooseSplitsHeuristicPUPacked_go_eq (toks : TokenArray) (endU : USize)
    (hend : endU.toNat = toks.size) (hbytes : toks.bytes.size < USize.size)
    (checkU : USize)
    (hpos : ∀ (j : Nat) (hj : j < toks.size),
      0 < splitTokenBytesP (toks.get j hj))
    (hcheckPos : 0 < checkU.toNat) (hcheckMax : checkU.toNat ≤ 32767) :
    ∀ (fuel : Nat) (i : USize), toks.size - i.toNat < fuel →
      ∀ (oA oB oC oD : UInt64) (oldTot : USize)
        (nA nB nC : UInt64) (newTot blockBytes remaining : USize)
        (cuts : Array Nat)
        (o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 : USize)
        (n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 : USize),
        splitUnpack20 oA oB oC oD =
          (o0, o1, o2, o3, o4, o5, o6, o7, o8, o9) →
        splitUnpack15 nA nB nC =
          (n0, n1, n2, n3, n4, n5, n6, n7, n8, n9) →
        splitPackedSum10 o0.toNat o1.toNat o2.toNat o3.toNat o4.toNat
          o5.toNat o6.toNat o7.toNat o8.toNat o9.toNat = oldTot.toNat →
        splitPackedSum10 n0.toNat n1.toNat n2.toNat n3.toNat n4.toNat
          n5.toNat n6.toNat n7.toNat n8.toNat n9.toNat = newTot.toNat →
        oldTot.toNat + newTot.toNat ≤ blockBytes.toNat →
        blockBytes.toNat < splitSoftMaxBlockBytes →
        (blockBytes.toNat < splitMinBlockBytes ∨
          newTot.toNat < checkU.toNat) →
        chooseSplitsHeuristicPUPacked.go toks endU hend hbytes checkU i
            oA oB oC oD oldTot nA nB nC newTot blockBytes remaining cuts =
          chooseSplitsHeuristicPU.go toks endU hend hbytes checkU i
            o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 oldTot
            n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 newTot
            blockBytes remaining cuts := by
  intro fuel
  induction fuel with
  | zero => intro i hf; omega
  | succ fuel ih =>
    intro i hf oA oB oC oD oldTot nA nB nC newTot blockBytes remaining cuts
      o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 n0 n1 n2 n3 n4 n5 n6 n7 n8 n9
      hO hN ho hn htot hblock hcad
    unfold chooseSplitsHeuristicPUPacked.go chooseSplitsHeuristicPU.go
    by_cases hi : i < endU
    · rw [dif_pos hi, dif_pos hi]
      have hiNat : i.toNat < toks.size := by
        rw [← hend]
        exact USize.lt_iff_toNat_lt.mp hi
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
      let c64 : UInt64 :=
        if t &&& ((1 : UInt32) <<< 31) = 0 then
          (((t >>> 5) &&& 6) ||| (t &&& 1)).toUInt64
        else if ((t >>> 16) &&& 0x7FFF) ≥ 9 then 9 else 8
      have hc64 : c64 < 10 := by
        exact splitPackedClass_lt t
      have hc :
          c64.toUSize = splitTokenClassPU t := by
        exact splitPackedClass_eq t
      have hfields := splitUnpack15_fields_lt nA nB nC
        n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 newTot blockBytes checkU
        hN hn (by omega) hcad hcheckMax
      rcases hfields with ⟨hnA0, hnA15, hnA30, hnA45,
        hnB0, hnB15, hnB30, hnB45, hnC0, hnC15⟩
      generalize hbq : splitBumpPacked15 c64 nA nB nC = bq
      rcases bq with ⟨unA, unB, unC⟩
      generalize hbu :
        splitBumpU (splitTokenClassPU t) n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 = bu
      rcases bu with ⟨un0, un1, un2, un3, un4, un5, un6, un7, un8, un9⟩
      have hBump := splitUnpack15_bump c64 nA nB nC hc64
        hnA0 hnA15 hnA30 hnA45 hnB0 hnB15 hnB30 hnB45 hnC0 hnC15
      rw [hbq, hc, hN, hbu] at hBump
      simp only at hBump
      have hstep : (i + 1).toNat = i.toNat + 1 := by
        rw [USize.toNat_add, USize.toNat_one]
        apply Nat.mod_eq_of_lt
        have hUS : USize.size = 2 ^ System.Platform.numBits := rfl
        rw [← hUS]
        have hEnd := USize.toNat_lt_two_pow_numBits endU
        have hiEnd := USize.lt_iff_toNat_lt.mp hi
        omega
      have hfnext : toks.size - (i + 1).toNat < fuel := by
        rw [hstep]
        omega
      have hcU : (splitTokenClassPU t).toNat < 10 := by
        rw [splitTokenClassPU_toNat]
        exact splitTokenClassP_lt t
      have hnewFit : newTot.toNat + 1 < USize.size := by
        simp only [splitSoftMaxBlockBytes] at hblock
        exact Nat.lt_of_lt_of_le (by omega) USize.le_size
      have hnew :
          (newTot + 1).toNat = newTot.toNat + 1 := by
        rw [USize.toNat_add, USize.toNat_one]
        apply Nat.mod_eq_of_lt
        have hUS : USize.size = 2 ^ System.Platform.numBits := rfl
        rw [← hUS]
        exact hnewFit
      have hnsumNew :
          splitPackedSum10 un0.toNat un1.toNat un2.toNat un3.toNat un4.toNat
            un5.toNat un6.toNat un7.toNat un8.toNat un9.toNat =
              (newTot + 1).toNat := by
        have hs := splitBumpU_sum (splitTokenClassPU t)
          n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 newTot hcU hn hnewFit
        rw [hbu] at hs
        simpa only using hs
      have htbPos : 0 < splitTokenBytesP t := by
        rw [← htword]
        exact hpos i.toNat hiNat
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
      have htotalNew :
          oldTot.toNat + (newTot + 1).toNat ≤
            (blockBytes + splitTokenBytesPU t).toNat := by
        rw [hnew, hblockAdd]
        omega
      have hdiv :
          splitEndBlockCheckPackedU oA oB oC oD oldTot
              unA unB unC (newTot + 1)
              (blockBytes + splitTokenBytesPU t) =
            splitEndBlockCheckU
              o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 oldTot
              un0 un1 un2 un3 un4 un5 un6 un7 un8 un9 (newTot + 1)
              (blockBytes + splitTokenBytesPU t) := by
        unfold splitEndBlockCheckPackedU
        rw [hO, hBump]
      have htbEq :
          (if t &&& ((1 : UInt32) <<< 31) = 0 then (1 : USize)
            else ((t >>> 16) &&& 0x7FFF).toUSize) =
            splitTokenBytesPU t := by rfl
      rw [htbEq, hdiv]
      generalize hremDef :
        (if splitTokenBytesPU t ≤ remaining then
          remaining - splitTokenBytesPU t else 0) = remU
      generalize hblockDef :
        blockBytes + splitTokenBytesPU t = blockU
      generalize hnewDef : newTot + 1 = newU
      have hblockNat :
          blockU.toNat = blockBytes.toNat + splitTokenBytesP t := by
        rw [← hblockDef]
        exact hblockAdd
      have hnewNat : newU.toNat = newTot.toNat + 1 := by
        rw [← hnewDef]
        exact hnew
      have hnsumRec :
          splitPackedSum10 un0.toNat un1.toNat un2.toNat un3.toNat un4.toNat
            un5.toNat un6.toNat un7.toNat un8.toNat un9.toNat =
              newU.toNat := by
        rw [← hnewDef]
        exact hnsumNew
      have htotalRec :
          oldTot.toNat + newU.toNat ≤ blockU.toNat := by
        rw [← hnewDef, ← hblockDef]
        exact htotalNew
      have hconst (n : Nat) (hn32 : n < 2 ^ 32) :
          n.toUSize.toNat = n := by
        exact USize.toNat_ofNat_of_lt'
          (Nat.lt_of_lt_of_le hn32 USize.le_size)
      have hmin : splitMinBlockBytes.toUSize.toNat = splitMinBlockBytes :=
        hconst splitMinBlockBytes (by decide)
      have hsoft : splitSoftMaxBlockBytes.toUSize.toNat =
          splitSoftMaxBlockBytes :=
        hconst splitSoftMaxBlockBytes (by decide)
      have keepEq (hb : blockU.toNat < splitSoftMaxBlockBytes)
          (hcadRec : blockU.toNat < splitMinBlockBytes ∨
            newU.toNat < checkU.toNat) :
          chooseSplitsHeuristicPUPacked.go toks endU hend hbytes checkU (i + 1)
              oA oB oC oD oldTot unA unB unC newU blockU remU cuts =
            chooseSplitsHeuristicPU.go toks endU hend hbytes checkU (i + 1)
              o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 oldTot
              un0 un1 un2 un3 un4 un5 un6 un7 un8 un9 newU
              blockU remU cuts :=
        ih (i + 1) hfnext oA oB oC oD oldTot unA unB unC
          newU blockU remU cuts
          o0 o1 o2 o3 o4 o5 o6 o7 o8 o9
          un0 un1 un2 un3 un4 un5 un6 un7 un8 un9
          hO hBump ho hnsumRec htotalRec hb hcadRec
      by_cases htail : remU < splitMinBlockBytes.toUSize
      · rw [if_pos htail, if_pos htail]
      · rw [if_neg htail, if_neg htail]
        by_cases hfloor : blockU ≥ splitMinBlockBytes.toUSize
        · rw [if_pos hfloor, if_pos hfloor]
          let cutU :=
            decide (blockU ≥ splitSoftMaxBlockBytes.toUSize) ||
              decide (newU ≥ checkU) && decide (oldTot > 0) &&
                splitEndBlockCheckU
                  o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 oldTot
                  un0 un1 un2 un3 un4 un5 un6 un7 un8 un9 newU blockU
          by_cases hcut : cutU = true
          · change (if cutU = true then _ else _) = _
            rw [if_pos hcut, if_pos hcut]
            exact ih (i + 1) hfnext
              0 0 0 0 0 0 0 0 0 0 remU (cuts.push (i + 1).toNat)
              0 0 0 0 0 0 0 0 0 0
              0 0 0 0 0 0 0 0 0 0
              (by rfl) (by rfl) (by rfl) (by rfl)
              (by simp) (by
                simp only [splitSoftMaxBlockBytes, USize.toNat_zero]
                omega)
              (Or.inl (by
                simp only [splitMinBlockBytes, USize.toNat_zero]
                omega))
          · change (if cutU = true then _ else _) = _
            rw [if_neg hcut, if_neg hcut]
            have hnotSoft : ¬ blockU ≥ splitSoftMaxBlockBytes.toUSize := by
              intro hs
              apply hcut
              simp [cutU, hs]
            have hblockRec : blockU.toNat < splitSoftMaxBlockBytes := by
              rw [← hsoft]
              apply Nat.lt_of_not_ge
              intro hge
              exact hnotSoft (USize.le_iff_toNat_le.mpr hge)
            by_cases hcadence : newU ≥ checkU
            · rw [if_pos hcadence, if_pos hcadence]
              have htotFit :
                  oldTot.toNat + newU.toNat < USize.size := by
                simp only [splitSoftMaxBlockBytes] at hblockRec
                exact Nat.lt_of_lt_of_le (by omega) USize.le_size
              have hmerge (a b : USize)
                  (ha : a.toNat ≤ oldTot.toNat)
                  (hb : b.toNat ≤ newU.toNat) :
                  (a + b).toNat = a.toNat + b.toNat := by
                rw [USize.toNat_add]
                apply Nat.mod_eq_of_lt
                have hUS : USize.size = 2 ^ System.Platform.numBits := rfl
                rw [← hUS]
                omega
              have hm0 := hmerge o0 un0
                (by unfold splitPackedSum10 at ho; omega)
                (by unfold splitPackedSum10 at hnsumRec; omega)
              have hm1 := hmerge o1 un1
                (by unfold splitPackedSum10 at ho; omega)
                (by unfold splitPackedSum10 at hnsumRec; omega)
              have hm2 := hmerge o2 un2
                (by unfold splitPackedSum10 at ho; omega)
                (by unfold splitPackedSum10 at hnsumRec; omega)
              have hm3 := hmerge o3 un3
                (by unfold splitPackedSum10 at ho; omega)
                (by unfold splitPackedSum10 at hnsumRec; omega)
              have hm4 := hmerge o4 un4
                (by unfold splitPackedSum10 at ho; omega)
                (by unfold splitPackedSum10 at hnsumRec; omega)
              have hm5 := hmerge o5 un5
                (by unfold splitPackedSum10 at ho; omega)
                (by unfold splitPackedSum10 at hnsumRec; omega)
              have hm6 := hmerge o6 un6
                (by unfold splitPackedSum10 at ho; omega)
                (by unfold splitPackedSum10 at hnsumRec; omega)
              have hm7 := hmerge o7 un7
                (by unfold splitPackedSum10 at ho; omega)
                (by unfold splitPackedSum10 at hnsumRec; omega)
              have hm8 := hmerge o8 un8
                (by unfold splitPackedSum10 at ho; omega)
                (by unfold splitPackedSum10 at hnsumRec; omega)
              have hm9 := hmerge o9 un9
                (by unfold splitPackedSum10 at ho; omega)
                (by unfold splitPackedSum10 at hnsumRec; omega)
              have hmtot :
                  (oldTot + newU).toNat = oldTot.toNat + newU.toNat := by
                rw [USize.toNat_add]
                apply Nat.mod_eq_of_lt
                have hUS : USize.size = 2 ^ System.Platform.numBits := rfl
                rw [← hUS]
                exact htotFit
              have homerge :
                  splitPackedSum10 (o0 + un0).toNat (o1 + un1).toNat
                    (o2 + un2).toNat (o3 + un3).toNat (o4 + un4).toNat
                    (o5 + un5).toNat (o6 + un6).toNat (o7 + un7).toNat
                    (o8 + un8).toNat (o9 + un9).toNat =
                      (oldTot + newU).toNat := by
                rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9,
                  hmtot]
                unfold splitPackedSum10 at ho hnsumRec ⊢
                omega
              have hbds := splitUnpack20_merge_bounds
                oA oB oC oD unA unB unC
                o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 oldTot
                un0 un1 un2 un3 un4 un5 un6 un7 un8 un9 newU blockU
                hO hBump ho hnsumRec htotalRec hblockRec
              rcases hbds with ⟨hb0, hb1, hb2, hb3, hb4,
                hb5, hb6, hb7, hb8, hb9⟩
              generalize hmq :
                splitMergePacked20 oA oB oC oD unA unB unC = mq
              rcases mq with ⟨moA, moB, moC, moD⟩
              have hMerge := splitUnpack20_merge oA oB oC oD unA unB unC
                hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9
              rw [hmq, hO, hBump] at hMerge
              simp only at hMerge
              exact ih (i + 1) hfnext
                moA moB moC moD (oldTot + newU) 0 0 0 0 blockU remU cuts
                (o0 + un0) (o1 + un1) (o2 + un2) (o3 + un3) (o4 + un4)
                (o5 + un5) (o6 + un6) (o7 + un7) (o8 + un8) (o9 + un9)
                0 0 0 0 0 0 0 0 0 0
                hMerge (by rfl) homerge (by rfl)
                (by
                  simp only [USize.toNat_zero, Nat.add_zero]
                  rw [hmtot]
                  exact htotalRec)
                hblockRec (Or.inr (by
                  simp only [USize.toNat_zero]
                  exact hcheckPos))
            · rw [if_neg hcadence, if_neg hcadence]
              exact keepEq hblockRec (Or.inr (by
                apply Nat.lt_of_not_ge
                intro hge
                exact hcadence (USize.le_iff_toNat_le.mpr hge)))
        · rw [if_neg hfloor, if_neg hfloor]
          have hfloorNat : blockU.toNat < splitMinBlockBytes := by
            rw [← hmin]
            apply Nat.lt_of_not_ge
            intro hge
            exact hfloor (USize.le_iff_toNat_le.mpr hge)
          exact keepEq (Nat.lt_trans hfloorNat (by decide)) (Or.inl hfloorNat)
    · rw [dif_neg hi, dif_neg hi]

/-- With positive token lengths, the guarded packed-counter entry is exactly
    the scalar native-word walker for every stream, total, and cadence. -/
theorem chooseSplitsHeuristicPUPacked_eq (toks : TokenArray) (totalBytes checkTokens : Nat)
    (hpos : ∀ (j : Nat) (hj : j < toks.size),
      0 < splitTokenBytesP (toks.get j hj)) :
    chooseSplitsHeuristicPUPacked toks totalBytes checkTokens =
      chooseSplitsHeuristicPU toks totalBytes checkTokens := by
  unfold chooseSplitsHeuristicPUPacked
  by_cases hsmall : totalBytes < 2 * splitMinBlockBytes
  · rw [if_pos hsmall]
    simp [chooseSplitsHeuristicPU, hsmall]
  · rw [if_neg hsmall]
    by_cases hc : 0 < checkTokens ∧ checkTokens ≤ 32767
    · rw [dif_pos hc]
      by_cases hg : toks.bytes.size.toUSize.toNat = toks.bytes.size ∧
          toks.size.toUSize.toNat = toks.size ∧
          totalBytes.toUSize.toNat = totalBytes ∧
          checkTokens.toUSize.toNat = checkTokens
      · rw [dif_pos hg]
        unfold chooseSplitsHeuristicPU
        rw [if_neg hsmall, dif_pos hg]
        have hbytes : toks.bytes.size < USize.size := by
          rw [← hg.1]
          exact USize.toNat_lt_two_pow_numBits _
        have hgo := chooseSplitsHeuristicPUPacked_go_eq toks toks.size.toUSize hg.2.1 hbytes
          checkTokens.toUSize hpos (by rw [hg.2.2.2]; exact hc.1)
          (by rw [hg.2.2.2]; exact hc.2)
          (toks.size + 1) 0 (by omega)
          0 0 0 0 0 0 0 0 0 0 totalBytes.toUSize #[]
          0 0 0 0 0 0 0 0 0 0
          0 0 0 0 0 0 0 0 0 0
          (by rfl) (by rfl) (by rfl) (by rfl)
          (by simp) (by
            simp only [splitSoftMaxBlockBytes, USize.toNat_zero]
            omega)
          (Or.inl (by
            simp only [splitMinBlockBytes, USize.toNat_zero]
            omega))
        exact congrArg Array.toList hgo
      · rw [dif_neg hg]
    · rw [dif_neg hc]

/-- Every packed token produced by `lzMatchP` advances the output. Literals
    contribute one byte; reference lengths inherit the matcher's `3 ≤ len`
    contract through the boxed `unpackTok` view. -/
private theorem lzMatchP_splitTokenBytes_pos (data : ByteArray) (level : UInt8) :
    ∀ (j : Nat) (hj : j < (lzMatchP data level).size),
      0 < splitTokenBytesP ((lzMatchP data level).get j hj) := by
  intro j hj
  let ta := lzMatchP data level
  have hjA : j < ta.toArray.size := by
    rw [← TokenArray.size_toArray]
    exact hj
  let w := ta.toArray[j]'hjA
  have hw : w ∈ ta.toArray := Array.getElem_mem hjA
  have hu : unpackTok w ∈ (ta.toArray.map unpackTok).toList := by
    rw [Array.mem_toList_iff]
    exact Array.mem_map.mpr ⟨w, hw, rfl⟩
  have hmap : ta.toArray.map unpackTok = lzMatch data level :=
    lzMatchP_map data level
  rw [hmap] at hu
  have henc := lzMatch_encodable data level (unpackTok w) hu
  have hget : (lzMatchP data level).get j hj = w := by
    rw [TokenArray.get_toArray]
  rw [hget, splitTokenBytesP_eq]
  cases htok : unpackTok w with
  | literal b => simp [splitTokenBytes]
  | reference len dist =>
      rw [htok] at henc
      simp only at henc
      simp only [splitTokenBytes]
      omega

/-- On the production matcher's positive token stream, the packed-counter
    walker selects exactly the reference heuristic's cut list. -/
theorem chooseSplitsHeuristicPUPacked_lzMatchP_eq
    (data : ByteArray) (level : UInt8) :
    chooseSplitsHeuristicPUPacked (lzMatchP data level) data.size
        (splitCheckTokensFor data level) =
      chooseSplitsHeuristicP (lzMatchP data level) data.size
        splitMinBlockBytes splitSoftMaxBlockBytes
        (splitCheckTokensFor data level) := by
  rw [chooseSplitsHeuristicPUPacked_eq _ _ _
    (lzMatchP_splitTokenBytes_pos data level)]
  exact chooseSplitsHeuristicPU_eq _ _ _

end Zip.Native.Deflate
