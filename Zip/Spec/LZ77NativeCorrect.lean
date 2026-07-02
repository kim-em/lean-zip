import Zip.Native.Deflate
import Zip.Spec.LZ77
import ZipForStd.ByteArray

/-! Correctness of native LZ77 matchers (`lz77Greedy` and `lz77Lazy`): proves `ValidDecomp`,
    token encodability, and length bounds against the spec-level LZ77 definitions. -/

namespace Zip.Native.Deflate

/-- Convert a native LZ77Token to a spec LZ77Symbol. -/
def LZ77Token.toLZ77Symbol : LZ77Token → Deflate.Spec.LZ77Symbol
  | .literal b => .literal b
  | .reference len dist => .reference len dist

/-- Convert native LZ77 token array to spec symbol list with end-of-block. -/
def tokensToSymbols (tokens : Array LZ77Token) : List Deflate.Spec.LZ77Symbol :=
  tokens.toList.map LZ77Token.toLZ77Symbol ++ [.endOfBlock]

/-- `toLZ77Symbol` never produces an `endOfBlock` symbol (it maps literals to
    literals and references to references). -/
theorem toLZ77Symbol_ne_endOfBlock (t : LZ77Token) :
    LZ77Token.toLZ77Symbol t ≠ Deflate.Spec.LZ77Symbol.endOfBlock := by
  cases t <;> simp only [LZ77Token.toLZ77Symbol, ne_eq, reduceCtorEq, not_false_eq_true]

/-- A list of mapped tokens contains no `endOfBlock` — the hypothesis the
    `endOfBlock`-free fold-composition lemmas require for each per-block group. -/
theorem mem_map_toLZ77Symbol_ne_endOfBlock (toks : List LZ77Token) :
    ∀ s ∈ toks.map LZ77Token.toLZ77Symbol, s ≠ Deflate.Spec.LZ77Symbol.endOfBlock := by
  intro s hs
  rw [List.mem_map] at hs
  obtain ⟨t, _, rfl⟩ := hs
  exact toLZ77Symbol_ne_endOfBlock t

/-! ## countMatch correctness -/

/-- The inner `go` loop of `countMatch` counts consecutive matching bytes
    between positions `p1+i..` and `p2+i..` in `data`. Returns a count `n`
    such that `i ≤ n ≤ maxLen` and all positions in `[i, n)` have matching
    bytes. -/
theorem lz77Greedy.go_matches (data : ByteArray) (p1 p2 i maxLen : Nat)
    (h1 : p1 + maxLen ≤ data.size) (h2 : p2 + maxLen ≤ data.size)
    (hle : i ≤ maxLen) :
    let n := lz77Greedy.go data p1 p2 i maxLen h1 h2
    (∀ j, i ≤ j → j < n → data[p1 + j]! = data[p2 + j]!) ∧
    i ≤ n ∧ n ≤ maxLen := by
  unfold lz77Greedy.go
  split
  · rename_i hlt
    split
    · rename_i heq
      have ih := lz77Greedy.go_matches data p1 p2 (i + 1) maxLen h1 h2 (by omega)
      refine ⟨fun j hj hjn => ?_, by omega, ih.2.2⟩
      by_cases hji : j = i
      · subst hji
        rw [getElem!_pos data (p1 + j) (by omega),
            getElem!_pos data (p2 + j) (by omega)]
        exact beq_iff_eq.mp heq
      · exact ih.1 j (by omega) hjn
    · exact ⟨fun j hj hjn => by omega, by omega, by omega⟩
  · exact ⟨fun j hj hjn => by omega, by omega, by omega⟩
termination_by maxLen - i

/-- P1a: the unboxed `USize` byte-compare loop computes the same count as the
    `Nat` loop `go`, whenever the buffer is `USize`-addressable. The `goU`
    bound arguments are proof-irrelevant, so any valid witnesses unify. -/
theorem lz77Greedy.goU_eq (data : ByteArray) (p1 p2 i maxLen : Nat)
    (hsz : data.size < USize.size)
    (h1 : p1 + maxLen ≤ data.size) (h2 : p2 + maxLen ≤ data.size)
    (hile : i ≤ maxLen)
    (hu1 : p1.toUSize.toNat + maxLen.toUSize.toNat ≤ data.size)
    (hu2 : p2.toUSize.toNat + maxLen.toUSize.toNat ≤ data.size) :
    (lz77Greedy.goU data p1.toUSize p2.toUSize i.toUSize maxLen.toUSize hsz hu1 hu2).toNat
      = lz77Greedy.go data p1 p2 i maxLen h1 h2 := by
  have hUS : USize.size = 2 ^ System.Platform.numBits := rfl
  have hp1 : p1.toUSize.toNat = p1 := toUSize_toNat_of_lt (by omega)
  have hp2 : p2.toUSize.toNat = p2 := toUSize_toNat_of_lt (by omega)
  have hmax : maxLen.toUSize.toNat = maxLen := toUSize_toNat_of_lt (by omega)
  have hi : i.toUSize.toNat = i := toUSize_toNat_of_lt (by omega)
  rw [lz77Greedy.goU, lz77Greedy.go]
  by_cases hlt : i < maxLen
  · have hltU : i.toUSize < maxLen.toUSize := USize.lt_iff_toNat_lt.mpr (by omega)
    rw [dif_pos hlt, dif_pos hltU]
    have hadd1 : (p1.toUSize + i.toUSize).toNat = p1 + i := by
      rw [USize.toNat_add, hp1, hi]; apply Nat.mod_eq_of_lt; omega
    have hadd2 : (p2.toUSize + i.toUSize).toNat = p2 + i := by
      rw [USize.toNat_add, hp2, hi]; apply Nat.mod_eq_of_lt; omega
    simp only [uget_eq_getElem, hadd1, hadd2]
    by_cases heq : data[p1 + i] == data[p2 + i]
    · rw [if_pos heq, if_pos heq]
      have hi1 : (i + 1).toUSize = i.toUSize + 1 := by
        apply USize.toNat_inj.mp
        rw [USize.toNat_add, USize.toNat_one, hi, toUSize_toNat_of_lt (by omega)]
        symm; apply Nat.mod_eq_of_lt; omega
      rw [← hi1]
      exact lz77Greedy.goU_eq data p1 p2 (i + 1) maxLen hsz h1 h2 (by omega) hu1 hu2
    · rw [if_neg heq, if_neg heq, hi]
  · rw [dif_neg hlt,
        dif_neg (by rw [USize.lt_iff_toNat_lt]; omega : ¬ i.toUSize < maxLen.toUSize), hi]
termination_by maxLen - i

/-! ## Word-at-a-time match extension (P1a, #2736)

`goUW` compares eight bytes per iteration by loading two little-endian
`UInt64` words and testing them for equality; on a full-word match it advances
eight. These lemmas prove it computes the same count as the per-byte `goU`
(hence `go`). The chaining happens at the `Nat` `go` level, where offsets are
plain `Nat`; the word-equality → byte-equality step is `bv_decide` over the
`ugetUInt64LE` recombination. -/

/-- Little-endian eight-byte recombination is injective in each byte: two words
    built from `a0..a7` and `b0..b7` are equal only if every byte agrees. The
    shift amounts are disjoint, so `bv_decide` closes each component. -/
theorem UInt64.recomb8LE_inj
    (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : UInt8)
    (h : (a0.toUInt64 ||| (a1.toUInt64 <<< 8) ||| (a2.toUInt64 <<< 16) |||
          (a3.toUInt64 <<< 24) ||| (a4.toUInt64 <<< 32) ||| (a5.toUInt64 <<< 40) |||
          (a6.toUInt64 <<< 48) ||| (a7.toUInt64 <<< 56))
       = (b0.toUInt64 ||| (b1.toUInt64 <<< 8) ||| (b2.toUInt64 <<< 16) |||
          (b3.toUInt64 <<< 24) ||| (b4.toUInt64 <<< 32) ||| (b5.toUInt64 <<< 40) |||
          (b6.toUInt64 <<< 48) ||| (b7.toUInt64 <<< 56))) :
    a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3 ∧
    a4 = b4 ∧ a5 = b5 ∧ a6 = b6 ∧ a7 = b7 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> bv_decide

/-- Equal `ugetUInt64LE` words at `o1` and `o2` mean the eight bytes at each
    offset agree pointwise. -/
theorem ByteArray.ugetUInt64LE_eq_bytes (data : ByteArray) (o1 o2 : USize)
    (hw1 : o1.toNat + 8 ≤ data.size) (hw2 : o2.toNat + 8 ≤ data.size)
    (hwe : data.ugetUInt64LE o1 hw1 = data.ugetUInt64LE o2 hw2) :
    ∀ k, k < 8 → data[o1.toNat + k]! = data[o2.toNat + k]! := by
  simp only [ByteArray.ugetUInt64LE] at hwe
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ :=
    UInt64.recomb8LE_inj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hwe
  intro k hk
  rw [getElem!_pos data (o1.toNat + k) (by omega), getElem!_pos data (o2.toNat + k) (by omega)]
  have hk8 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
  rcases hk8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact e0
  · exact e1
  · exact e2
  · exact e3
  · exact e4
  · exact e5
  · exact e6
  · exact e7

/-! ### Locating the first mismatching byte with count-trailing-zeros (#2736)

On a word mismatch `goUW` returns `i + (ctz (w1 ^^^ w2) >>> 3)` — the first
differing byte located directly from the trailing-zero count of the XOR, with no
re-scan. These lemmas prove that offset is exactly the first index at which the
two eight-byte windows disagree, so `go` (the per-byte loop) stops there too. The
byte-level facts are `bv_decide` over the `ugetUInt64LE` recombination and
`BitVec.ctz`. -/

/-- `ctz x >>> 3` (the byte index of the lowest set bit) is below 8 for nonzero
    `x`: `ctz x < 64`, and dividing by eight keeps it under eight. -/
theorem BitVec.ctz_ushiftRight3_lt_eight (D : BitVec 64) (h : D ≠ 0#64) :
    (BitVec.ctz D >>> 3#64).toNat < 8 := by
  have h1 : (BitVec.ctz D).toNat < 64 := by
    have hh := (BitVec.ctz_lt_iff_ne_zero (x := D)).mpr h
    simpa [BitVec.lt_def] using hh
  have h2 : (BitVec.ctz D >>> 3#64).toNat = (BitVec.ctz D).toNat >>> (3#64).toNat := by
    simp [BitVec.toNat_ushiftRight]
  have h3 : (3#64 : BitVec 64).toNat = 3 := by decide
  rw [h2, h3, Nat.shiftRight_eq_div_pow]; omega

/-- For the XOR `D` of two little-endian eight-byte recombinations, the byte index
    `ctz D >>> 3` marks the first disagreement: every byte strictly before it
    agrees (prefix conjuncts) and the byte at it differs (mismatch conjuncts).
    Each component is a `bv_decide` bit-blast of `ctz`, the shift, and the
    recombination. -/
theorem UInt64.recomb8LE_ctz
    (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) (D : BitVec 64)
    (hD : D = ((a0.toUInt64 ||| a1.toUInt64 <<< 8 ||| a2.toUInt64 <<< 16 ||| a3.toUInt64 <<< 24 |||
          a4.toUInt64 <<< 32 ||| a5.toUInt64 <<< 40 ||| a6.toUInt64 <<< 48 ||| a7.toUInt64 <<< 56) ^^^
         (b0.toUInt64 ||| b1.toUInt64 <<< 8 ||| b2.toUInt64 <<< 16 ||| b3.toUInt64 <<< 24 |||
          b4.toUInt64 <<< 32 ||| b5.toUInt64 <<< 40 ||| b6.toUInt64 <<< 48 ||| b7.toUInt64 <<< 56)).toBitVec) :
    ((0#64) < BitVec.ctz D >>> 3#64 → a0 = b0) ∧ ((1#64) < BitVec.ctz D >>> 3#64 → a1 = b1) ∧
    ((2#64) < BitVec.ctz D >>> 3#64 → a2 = b2) ∧ ((3#64) < BitVec.ctz D >>> 3#64 → a3 = b3) ∧
    ((4#64) < BitVec.ctz D >>> 3#64 → a4 = b4) ∧ ((5#64) < BitVec.ctz D >>> 3#64 → a5 = b5) ∧
    ((6#64) < BitVec.ctz D >>> 3#64 → a6 = b6) ∧
    (BitVec.ctz D >>> 3#64 = 0#64 → a0 ≠ b0) ∧ (BitVec.ctz D >>> 3#64 = 1#64 → a1 ≠ b1) ∧
    (BitVec.ctz D >>> 3#64 = 2#64 → a2 ≠ b2) ∧ (BitVec.ctz D >>> 3#64 = 3#64 → a3 ≠ b3) ∧
    (BitVec.ctz D >>> 3#64 = 4#64 → a4 ≠ b4) ∧ (BitVec.ctz D >>> 3#64 = 5#64 → a5 ≠ b5) ∧
    (BitVec.ctz D >>> 3#64 = 6#64 → a6 ≠ b6) ∧ (BitVec.ctz D >>> 3#64 = 7#64 → a7 ≠ b7) := by
  subst hD
  refine ⟨?_,?_,?_,?_,?_,?_,?_, ?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> bv_decide

/-- Cast a `Nat` `<` on `(ctz D >>> 3).toNat` to the `BitVec` order the
    `recomb8LE_ctz` prefix conjuncts expect. -/
theorem ctzD_lt_ofNat (D : BitVec 64) (m : Nat) (hm : m < 64)
    (h : m < (BitVec.ctz D >>> 3#64).toNat) : (BitVec.ofNat 64 m) < BitVec.ctz D >>> 3#64 := by
  rw [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact h

/-- Cast a `Nat` value of `(ctz D >>> 3).toNat` to the `BitVec` equation the
    `recomb8LE_ctz` mismatch conjuncts expect. -/
theorem ctzD_eq_ofNat (D : BitVec 64) (m : Nat) (hm : m < 64)
    (h : (BitVec.ctz D >>> 3#64).toNat = m) : BitVec.ctz D >>> 3#64 = BitVec.ofNat 64 m := by
  apply BitVec.eq_of_toNat_eq; rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

set_option maxHeartbeats 1600000 in
/-- The count-trailing-zeros offset `k = ctz (w1 ^^^ w2) >>> 3` of two differing
    `ugetUInt64LE` words at `o1`, `o2` is the first mismatching byte: `k < 8`,
    every byte before `k` agrees, and byte `k` differs. This is the correctness
    core of `goUW`'s word-mismatch branch. -/
theorem ByteArray.ugetUInt64LE_ctz_first_diff (data : ByteArray) (o1 o2 : USize)
    (hw1 : o1.toNat + 8 ≤ data.size) (hw2 : o2.toNat + 8 ≤ data.size)
    (hne : data.ugetUInt64LE o1 hw1 ≠ data.ugetUInt64LE o2 hw2)
    (k : Nat)
    (hk : k = (UInt64.ctz (data.ugetUInt64LE o1 hw1 ^^^ data.ugetUInt64LE o2 hw2) >>> 3).toNat) :
    k < 8 ∧ (∀ j, j < k → data[o1.toNat + j]! = data[o2.toNat + j]!) ∧
      data[o1.toNat + k]! ≠ data[o2.toNat + k]! := by
  let D := (data.ugetUInt64LE o1 hw1 ^^^ data.ugetUInt64LE o2 hw2).toBitVec
  have hDdef : D = (data.ugetUInt64LE o1 hw1 ^^^ data.ugetUInt64LE o2 hw2).toBitVec := rfl
  have hkD : k = (BitVec.ctz D >>> 3#64).toNat := hk
  have hDne : D ≠ 0#64 := by
    rw [hDdef, ne_eq, ← UInt64.toBitVec_zero, UInt64.toBitVec_inj]
    revert hne
    generalize data.ugetUInt64LE o1 hw1 = x
    generalize data.ugetUInt64LE o2 hw2 = y
    intro hne; bv_decide
  have hk8 : k < 8 := by rw [hkD]; exact BitVec.ctz_ushiftRight3_lt_eight D hDne
  have hDrec := hDdef
  simp only [ByteArray.ugetUInt64LE] at hDrec
  have hfacts := UInt64.recomb8LE_ctz _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ D hDrec
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, m0, m1, m2, m3, m4, m5, m6, m7⟩ := hfacts
  refine ⟨hk8, ?_, ?_⟩
  · intro j hj
    rw [getElem!_pos data (o1.toNat + j) (by omega), getElem!_pos data (o2.toNat + j) (by omega)]
    have hjD : j < (BitVec.ctz D >>> 3#64).toNat := hkD ▸ hj
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact p0 (ctzD_lt_ofNat D 0 (by omega) hjD)
    · exact p1 (ctzD_lt_ofNat D 1 (by omega) hjD)
    · exact p2 (ctzD_lt_ofNat D 2 (by omega) hjD)
    · exact p3 (ctzD_lt_ofNat D 3 (by omega) hjD)
    · exact p4 (ctzD_lt_ofNat D 4 (by omega) hjD)
    · exact p5 (ctzD_lt_ofNat D 5 (by omega) hjD)
    · exact p6 (ctzD_lt_ofNat D 6 (by omega) hjD)
  · have hkeq : (BitVec.ctz D >>> 3#64).toNat = k := hkD.symm
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals rw [getElem!_pos data (o1.toNat + _) (by omega), getElem!_pos data (o2.toNat + _) (by omega)]
    · exact m0 (ctzD_eq_ofNat D 0 (by omega) hkeq)
    · exact m1 (ctzD_eq_ofNat D 1 (by omega) hkeq)
    · exact m2 (ctzD_eq_ofNat D 2 (by omega) hkeq)
    · exact m3 (ctzD_eq_ofNat D 3 (by omega) hkeq)
    · exact m4 (ctzD_eq_ofNat D 4 (by omega) hkeq)
    · exact m5 (ctzD_eq_ofNat D 5 (by omega) hkeq)
    · exact m6 (ctzD_eq_ofNat D 6 (by omega) hkeq)
    · exact m7 (ctzD_eq_ofNat D 7 (by omega) hkeq)

/-- `go` advances by `n` whenever the next `n` byte pairs all match. Chaining
    this at `n = 8` is how a word match maps to eight per-byte steps. -/
theorem lz77Greedy.go_advance (data : ByteArray) (p1 p2 maxLen n : Nat)
    (h1 : p1 + maxLen ≤ data.size) (h2 : p2 + maxLen ≤ data.size) :
    ∀ i, i + n ≤ maxLen → (∀ k, k < n → data[p1 + i + k]! = data[p2 + i + k]!) →
      lz77Greedy.go data p1 p2 i maxLen h1 h2
        = lz77Greedy.go data p1 p2 (i + n) maxLen h1 h2 := by
  induction n with
  | zero => intro i _ _; rfl
  | succ m ih =>
    intro i hin hbytes
    have hstep : lz77Greedy.go data p1 p2 i maxLen h1 h2
        = lz77Greedy.go data p1 p2 (i + 1) maxLen h1 h2 := by
      rw [lz77Greedy.go, dif_pos (show i < maxLen by omega)]
      have hb0 : data[p1 + i]'(by omega) = data[p2 + i]'(by omega) := by
        have h0 := hbytes 0 (by omega)
        simp only [Nat.add_zero] at h0
        rw [getElem!_pos data (p1 + i) (by omega),
          getElem!_pos data (p2 + i) (by omega)] at h0
        exact h0
      rw [if_pos (beq_iff_eq.mpr hb0)]
    rw [hstep, ih (i + 1) (by omega) (fun k hk => by
      have h := hbytes (k + 1) (by omega)
      have e1 : p1 + i + (k + 1) = p1 + (i + 1) + k := by omega
      have e2 : p2 + i + (k + 1) = p2 + (i + 1) + k := by omega
      rw [e1, e2] at h; exact h)]
    have hidx : i + 1 + m = i + (m + 1) := by omega
    rw [hidx]

/-- `goUW` depends on its index only through the value, so equal indices give
    equal results (the in-bounds proof is proof-irrelevant). Used to bridge the
    recursion's `i.toUSize + 8` and the induction hypothesis's `(i + 8).toUSize`. -/
theorem lz77Greedy.goUW_index_congr (data : ByteArray) (p1 p2 maxLen : USize)
    (i i' : USize) (hsz : data.size < USize.size)
    (h1 : p1.toNat + maxLen.toNat ≤ data.size) (h2 : p2.toNat + maxLen.toNat ≤ data.size)
    (hile : i.toNat ≤ maxLen.toNat) (hile' : i'.toNat ≤ maxLen.toNat) (he : i = i') :
    lz77Greedy.goUW data p1 p2 i maxLen hsz h1 h2 hile
      = lz77Greedy.goUW data p1 p2 i' maxLen hsz h1 h2 hile' := by
  subst he; rfl

/-- P1a: the word-at-a-time loop `goUW` computes the same count as the per-byte
    `go`, whenever the buffer is `USize`-addressable. -/
theorem lz77Greedy.goUW_eq (data : ByteArray) (p1 p2 i maxLen : Nat)
    (hsz : data.size < USize.size)
    (h1 : p1 + maxLen ≤ data.size) (h2 : p2 + maxLen ≤ data.size)
    (hile : i ≤ maxLen)
    (hu1 : p1.toUSize.toNat + maxLen.toUSize.toNat ≤ data.size)
    (hu2 : p2.toUSize.toNat + maxLen.toUSize.toNat ≤ data.size)
    (huile : i.toUSize.toNat ≤ maxLen.toUSize.toNat) :
    (lz77Greedy.goUW data p1.toUSize p2.toUSize i.toUSize maxLen.toUSize hsz hu1 hu2 huile).toNat
      = lz77Greedy.go data p1 p2 i maxLen h1 h2 := by
  have hUS : USize.size = 2 ^ System.Platform.numBits := rfl
  have hp1 : p1.toUSize.toNat = p1 := toUSize_toNat_of_lt (by omega)
  have hp2 : p2.toUSize.toNat = p2 := toUSize_toNat_of_lt (by omega)
  have hmax : maxLen.toUSize.toNat = maxLen := toUSize_toNat_of_lt (by omega)
  have hi : i.toUSize.toNat = i := toUSize_toNat_of_lt (by omega)
  have h8v : (8 : USize).toNat = 8 := by
    rw [USize.toNat_ofNat]
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (show 8 < 2 ^ 32 by omega) USize.le_size)
  rw [lz77Greedy.goUW]
  by_cases h8 : i + 8 ≤ maxLen
  · have hle : i.toUSize ≤ maxLen.toUSize :=
      USize.le_iff_toNat_le.mpr (by rw [hmax, hi]; omega)
    have h8U : (8 : USize) ≤ maxLen.toUSize - i.toUSize := by
      rw [USize.le_iff_toNat_le, USize.toNat_sub_of_le _ _ hle, h8v, hmax, hi]
      omega
    rw [dif_pos h8U]
    have hoff1 : (p1.toUSize + i.toUSize).toNat = p1 + i := by
      rw [USize.toNat_add, hp1, hi]; apply Nat.mod_eq_of_lt; omega
    have hoff2 : (p2.toUSize + i.toUSize).toNat = p2 + i := by
      rw [USize.toNat_add, hp2, hi]; apply Nat.mod_eq_of_lt; omega
    by_cases hwe : (data.ugetUInt64LE (p1.toUSize + i.toUSize) (by omega)
        == data.ugetUInt64LE (p2.toUSize + i.toUSize) (by omega)) = true
    · rw [if_pos hwe]
      have hbytes : ∀ k, k < 8 → data[p1 + i + k]! = data[p2 + i + k]! := by
        have hb := ByteArray.ugetUInt64LE_eq_bytes data (p1.toUSize + i.toUSize)
          (p2.toUSize + i.toUSize) (by omega) (by omega) (beq_iff_eq.mp hwe)
        intro k hk
        have := hb k hk
        rwa [hoff1, hoff2] at this
      have hadv : lz77Greedy.go data p1 p2 i maxLen h1 h2
          = lz77Greedy.go data p1 p2 (i + 8) maxLen h1 h2 :=
        lz77Greedy.go_advance data p1 p2 maxLen 8 h1 h2 i h8 hbytes
      have hi8 : i.toUSize + 8 = (i + 8).toUSize := by
        apply USize.toNat_inj.mp
        rw [USize.toNat_add, h8v, hi, toUSize_toNat_of_lt (by omega)]
        apply Nat.mod_eq_of_lt; omega
      have hA : (i.toUSize + 8).toNat ≤ maxLen.toUSize.toNat := by
        rw [USize.toNat_add, h8v, hi, Nat.mod_eq_of_lt (by omega), hmax]; omega
      have hB : (i + 8).toUSize.toNat ≤ maxLen.toUSize.toNat := by
        rw [toUSize_toNat_of_lt (by omega), hmax]; omega
      rw [lz77Greedy.goUW_index_congr data p1.toUSize p2.toUSize maxLen.toUSize
        (i.toUSize + 8) ((i + 8).toUSize) hsz hu1 hu2 hA hB hi8, hadv]
      exact lz77Greedy.goUW_eq data p1 p2 (i + 8) maxLen hsz h1 h2 (by omega) hu1 hu2 hB
    · rw [if_neg hwe]
      -- The two eight-byte words differ; `ugetUInt64LE_ctz_first_diff` locates the
      -- first differing byte at `k = ctz (w1 ^^^ w2) >>> 3`, and `go` stops there.
      have hne : data.ugetUInt64LE (p1.toUSize + i.toUSize) (by omega)
          ≠ data.ugetUInt64LE (p2.toUSize + i.toUSize) (by omega) :=
        fun h => hwe (by rw [h]; simp)
      obtain ⟨hk8, hpre, hmis⟩ := ByteArray.ugetUInt64LE_ctz_first_diff data
        (p1.toUSize + i.toUSize) (p2.toUSize + i.toUSize) (by omega) (by omega) hne _ rfl
      -- re-index the byte facts from `oₙ.toNat + j` to `pₙ + i + j`
      have hprep : ∀ j, j < (UInt64.ctz (data.ugetUInt64LE (p1.toUSize + i.toUSize) (by omega)
            ^^^ data.ugetUInt64LE (p2.toUSize + i.toUSize) (by omega)) >>> 3).toNat →
          data[p1 + i + j]! = data[p2 + i + j]! := by
        intro j hj; have := hpre j hj; rwa [hoff1, hoff2] at this
      have hmisp : data[p1 + (i + (UInt64.ctz (data.ugetUInt64LE (p1.toUSize + i.toUSize) (by omega)
            ^^^ data.ugetUInt64LE (p2.toUSize + i.toUSize) (by omega)) >>> 3).toNat)]!
          ≠ data[p2 + (i + (UInt64.ctz (data.ugetUInt64LE (p1.toUSize + i.toUSize) (by omega)
            ^^^ data.ugetUInt64LE (p2.toUSize + i.toUSize) (by omega)) >>> 3).toNat)]! := by
        rw [show p1 + (i + (UInt64.ctz (data.ugetUInt64LE (p1.toUSize + i.toUSize) (by omega)
              ^^^ data.ugetUInt64LE (p2.toUSize + i.toUSize) (by omega)) >>> 3).toNat)
            = (p1.toUSize + i.toUSize).toNat + (UInt64.ctz (data.ugetUInt64LE (p1.toUSize + i.toUSize) (by omega)
              ^^^ data.ugetUInt64LE (p2.toUSize + i.toUSize) (by omega)) >>> 3).toNat from by omega,
          show p2 + (i + (UInt64.ctz (data.ugetUInt64LE (p1.toUSize + i.toUSize) (by omega)
              ^^^ data.ugetUInt64LE (p2.toUSize + i.toUSize) (by omega)) >>> 3).toNat)
            = (p2.toUSize + i.toUSize).toNat + (UInt64.ctz (data.ugetUInt64LE (p1.toUSize + i.toUSize) (by omega)
              ^^^ data.ugetUInt64LE (p2.toUSize + i.toUSize) (by omega)) >>> 3).toNat from by omega]
        exact hmis
      -- prefix matches ⇒ `go` advances to `i + k`; byte `k` differs ⇒ it stops there
      have hadv : lz77Greedy.go data p1 p2 i maxLen h1 h2
          = lz77Greedy.go data p1 p2 (i + (UInt64.ctz
              (data.ugetUInt64LE (p1.toUSize + i.toUSize) (by omega)
                ^^^ data.ugetUInt64LE (p2.toUSize + i.toUSize) (by omega)) >>> 3).toNat)
              maxLen h1 h2 :=
        lz77Greedy.go_advance data p1 p2 maxLen _ h1 h2 i (by omega) hprep
      have hstop : lz77Greedy.go data p1 p2 (i + (UInt64.ctz
            (data.ugetUInt64LE (p1.toUSize + i.toUSize) (by omega)
              ^^^ data.ugetUInt64LE (p2.toUSize + i.toUSize) (by omega)) >>> 3).toNat)
            maxLen h1 h2
          = i + (UInt64.ctz (data.ugetUInt64LE (p1.toUSize + i.toUSize) (by omega)
              ^^^ data.ugetUInt64LE (p2.toUSize + i.toUSize) (by omega)) >>> 3).toNat := by
        rw [lz77Greedy.go, dif_pos (by omega)]
        refine if_neg ?_
        intro hc
        apply hmisp
        rw [getElem!_pos data (p1 + (i + (UInt64.ctz
              (data.ugetUInt64LE (p1.toUSize + i.toUSize) (by omega)
                ^^^ data.ugetUInt64LE (p2.toUSize + i.toUSize) (by omega)) >>> 3).toNat)) (by omega),
            getElem!_pos data (p2 + (i + (UInt64.ctz
              (data.ugetUInt64LE (p1.toUSize + i.toUSize) (by omega)
                ^^^ data.ugetUInt64LE (p2.toUSize + i.toUSize) (by omega)) >>> 3).toNat)) (by omega)]
        exact beq_iff_eq.mp hc
      show (i.toUSize + (UInt64.ctz (data.ugetUInt64LE (p1.toUSize + i.toUSize) (by omega)
          ^^^ data.ugetUInt64LE (p2.toUSize + i.toUSize) (by omega)) >>> 3).toUSize).toNat
        = lz77Greedy.go data p1 p2 i maxLen h1 h2
      have hsz8 : 8 ≤ USize.size := Nat.le_of_lt (Nat.lt_of_lt_of_le (by omega : 8 < 2 ^ 32) USize.le_size)
      have hXnb : (UInt64.ctz (data.ugetUInt64LE (p1.toUSize + i.toUSize) (by omega)
          ^^^ data.ugetUInt64LE (p2.toUSize + i.toUSize) (by omega)) >>> 3).toNat
          < 2 ^ System.Platform.numBits := by rw [← hUS]; omega
      have hik : i + (UInt64.ctz (data.ugetUInt64LE (p1.toUSize + i.toUSize) (by omega)
          ^^^ data.ugetUInt64LE (p2.toUSize + i.toUSize) (by omega)) >>> 3).toNat < USize.size := by omega
      rw [hadv, hstop, USize.toNat_add, hi, UInt64.toNat_toUSize, Nat.mod_eq_of_lt hXnb,
        Nat.mod_eq_of_lt hik]
  · have hle : i.toUSize ≤ maxLen.toUSize :=
      USize.le_iff_toNat_le.mpr (by rw [hmax, hi]; omega)
    have h8U : ¬ (8 : USize) ≤ maxLen.toUSize - i.toUSize := by
      rw [USize.le_iff_toNat_le, USize.toNat_sub_of_le _ _ hle, h8v, hmax, hi]
      omega
    rw [dif_neg h8U]
    exact lz77Greedy.goU_eq data p1 p2 i maxLen hsz h1 h2 hile hu1 hu2
termination_by maxLen - i

/-- `countMatch` returns a count of consecutive matching bytes starting from
    position 0, with all counted positions verified equal. -/
theorem lz77Greedy.countMatch_matches (data : ByteArray) (p1 p2 maxLen : Nat)
    (h1 : p1 + maxLen ≤ data.size) (h2 : p2 + maxLen ≤ data.size) :
    let n := lz77Greedy.countMatch data p1 p2 maxLen h1 h2
    (∀ j, j < n → data[p1 + j]! = data[p2 + j]!) ∧ n ≤ maxLen := by
  have hgo : lz77Greedy.countMatch data p1 p2 maxLen h1 h2
      = lz77Greedy.go data p1 p2 0 maxLen h1 h2 := by
    rw [lz77Greedy.countMatch]
    split
    · rename_i hg
      exact lz77Greedy.goUW_eq data p1 p2 0 maxLen _ h1 h2 (by omega) _ _ (by simp)
    · rfl
  simp only [hgo]
  have h := lz77Greedy.go_matches data p1 p2 0 maxLen h1 h2 (by omega)
  exact ⟨fun j hj => h.1 j (by omega) hj, h.2.2⟩

/-! ## ValidDecomp predicate -/

/-- A token list is a valid decomposition of `data` starting at position `pos`.
    Each literal has the correct byte, each reference has matching bytes in the
    lookback window, and tokens cover `data[pos..]` contiguously. -/
inductive ValidDecomp (data : ByteArray) : Nat → List LZ77Token → Prop where
  | done (h : pos ≥ data.size) : ValidDecomp data pos []
  | literal {b : UInt8} {tokens : List LZ77Token}
      (hpos : pos < data.size)
      (hb : data[pos]! = b)
      (rest : ValidDecomp data (pos + 1) tokens) :
      ValidDecomp data pos (.literal b :: tokens)
  | reference {len dist : Nat} {tokens : List LZ77Token}
      (hlen : len ≥ 3) (hdist_pos : dist ≥ 1) (hdist_le : dist ≤ pos)
      (hlen_le : pos + len ≤ data.size)
      (hmatch : ∀ i, i < len → data[pos + i]! = data[pos - dist + i]!)
      (rest : ValidDecomp data (pos + len) tokens) :
      ValidDecomp data pos (.reference len dist :: tokens)

/-! ## Bridge lemma: direct match → modular copy -/

/-- If bytes at `data[pos..pos+len]` match `data[pos-dist..pos-dist+len]` directly,
    then each byte equals the modular-copy byte used by `resolveLZ77`. -/
theorem direct_match_implies_modular (data : ByteArray) (pos dist len : Nat)
    (hdist_pos : dist ≥ 1) (hdist_le : dist ≤ pos)
    (hmatch : ∀ i, i < len → data[pos + i]! = data[pos - dist + i]!) :
    ∀ i, i < len → data[pos + i]! = data[pos - dist + (i % dist)]! := by
  intro i
  induction i using Nat.strongRecOn with
  | _ i ih =>
    intro hi
    by_cases hid : i < dist
    · rw [Nat.mod_eq_of_lt hid]; exact hmatch i hi
    · rw [Nat.mod_eq_sub_mod (by omega),
        hmatch i hi, show pos - dist + i = pos + (i - dist) from by omega]
      exact ih (i - dist) (by omega) (by omega)

/-! ## validDecomp_resolves -/

/-- Generalized `validDecomp_resolves`: at position `pos` with accumulator
    `data.data.toList.take pos`, resolving the tokens recovers the full data. -/
theorem validDecomp_resolves_aux (data : ByteArray) (pos : Nat) (tokens : List LZ77Token)
    (hv : ValidDecomp data pos tokens) :
    Deflate.Spec.resolveLZ77 (tokens.map LZ77Token.toLZ77Symbol ++ [.endOfBlock])
      (data.data.toList.take pos) = some data.data.toList := by
  induction hv with
  | done h =>
    simp only [List.map_nil, List.nil_append, Deflate.Spec.resolveLZ77_endOfBlock]
    exact congrArg some (List.take_of_length_le (by rw [ByteArray.data_toList_length]; omega))
  | @literal pos b tokens hpos hb rest ih =>
    simp only [List.map_cons, List.cons_append, LZ77Token.toLZ77Symbol,
               Deflate.Spec.resolveLZ77_literal]
    suffices h : data.data.toList.take pos ++ [b] =
        data.data.toList.take (pos + 1) by rw [h]; exact ih
    rw [← hb, ByteArray.getElem!_toList data pos hpos]
    exact (List.take_succ_eq_append_getElem (by rw [ByteArray.data_toList_length]; exact hpos)).symm
  | @reference pos len dist tokens hlen hdist_pos hdist_le hlen_le hmatch rest ih =>
    simp only [List.map_cons, List.cons_append, LZ77Token.toLZ77Symbol]
    have hmod := direct_match_implies_modular data pos dist len hdist_pos hdist_le hmatch
    simp only [Deflate.Spec.resolveLZ77]
    have hdneq : dist ≠ 0 := by omega
    have hacclen : (data.data.toList.take pos).length = pos := by
      simp only [List.length_take, Array.length_toList, ByteArray.size_data]; omega
    rw [show (dist == 0 || decide ((data.data.toList.take pos).length < dist)) = false
      from by simp only [hacclen, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq, hdneq,
        not_false_eq_true, decide_eq_false_iff_not, Nat.not_lt, true_and]; omega]
    simp only [Bool.false_eq_true, ↓reduceIte, hacclen]
    suffices h : data.data.toList.take pos ++
        (List.ofFn fun (i : Fin len) =>
          (data.data.toList.take pos)[pos - dist + (↑i % dist)]!) =
        data.data.toList.take (pos + len) by rw [h]; exact ih
    have hdllen : data.data.toList.length = data.size := ByteArray.data_toList_length data
    apply List.ext_getElem
    · simp only [List.length_append, List.length_ofFn, List.length_take, hdllen]; omega
    · intro i h1 h2
      simp only [List.length_take, hdllen, Nat.min_eq_left (by omega)] at h2
      simp only [List.getElem_take]
      by_cases hip : i < pos
      · -- Element from the take pos part
        rw [List.getElem_append_left (by simp only [List.length_take, hdllen]; omega)]
        simp only [List.getElem_take]
      · -- Element from the ofFn part
        rw [List.getElem_append_right (by simp only [List.length_take, hdllen]; omega)]
        simp only [List.length_take, hdllen]
        rw [List.getElem_ofFn]
        -- Goal: (take pos dl)[pos - dist + ((i - pos) % dist)]! = dl[i]
        have hmin : min pos data.size = pos := Nat.min_eq_left (by omega)
        have hk : (i - pos) % dist < dist := Nat.mod_lt _ (by omega)
        have hm := hmod (i - pos) (by omega)
        rw [show pos + (i - pos) = i from by omega,
          ByteArray.getElem!_toList data i (by omega),
          ByteArray.getElem!_toList data (pos - dist + ((i - pos) % dist))
            (by omega)] at hm
        -- Simplify min in getElem! bounds
        show (data.data.toList.take pos)[pos - dist +
          ((i - min pos data.size) % dist)]! = data.data.toList[i]
        rw [hmin, getElem!_pos (data.data.toList.take pos) _ (by
          simp only [List.length_take, hdllen, hmin]; omega)]
        simp only [List.getElem_take]
        exact hm.symm

/-- Resolving the tokens from any valid decomposition recovers the original data. -/
theorem validDecomp_resolves (data : ByteArray) (tokens : List LZ77Token)
    (hv : ValidDecomp data 0 tokens) :
    Deflate.Spec.resolveLZ77 (tokens.map LZ77Token.toLZ77Symbol ++ [.endOfBlock]) [] =
      some data.data.toList := by
  have := validDecomp_resolves_aux data 0 tokens hv
  simp only [List.take_zero] at this; exact this

/-! ## Explicit recursion validity -/

theorem trailing_valid (data : ByteArray) (pos : Nat) :
    ValidDecomp data pos (lz77Greedy.trailing data pos) := by
  unfold lz77Greedy.trailing
  split
  · rename_i hlt
    exact .literal hlt (getElem!_pos data pos hlt) (trailing_valid data (pos + 1))
  · exact .done (by omega)
termination_by data.size - pos

theorem mainLoop_valid (data : ByteArray) (windowSize hashSize : Nat)
    (hashTable : Array Nat) (hashValid : Array Bool) (pos : Nat)
    (hw : windowSize > 0) :
    ValidDecomp data pos
      (lz77Greedy.mainLoop data windowSize hashSize hashTable hashValid pos) := by
  unfold lz77Greedy.mainLoop
  split
  · rename_i hlt
    dsimp only
    split
    · rename_i hht
      split
      · rename_i hhv
        split
        · rename_i hcond
          split
          · rename_i hge
            split
            · rename_i hle
              have hmp_lt := hcond.2.1
              have hmaxLenP : pos + min 258 (data.size - pos) ≤ data.size := by omega
              have hmaxLenM : hashTable[lz77Greedy.hash3 data pos hashSize hlt] +
                  min 258 (data.size - pos) ≤ data.size := by omega
              have hcm := lz77Greedy.countMatch_matches data
                hashTable[lz77Greedy.hash3 data pos hashSize hlt] pos
                (min 258 (data.size - pos)) hmaxLenM hmaxLenP
              apply ValidDecomp.reference hge
              · omega
              · exact Nat.sub_le _ _
              · exact hle
              · intro i hi
                rw [show pos - (pos - hashTable[lz77Greedy.hash3 data pos hashSize hlt]) =
                    hashTable[lz77Greedy.hash3 data pos hashSize hlt] from by omega]
                exact (hcm.1 i hi).symm
              · exact mainLoop_valid _ _ _ _ _ _ hw
            · exact .literal (by omega) (getElem!_pos data pos (by omega))
                (mainLoop_valid _ _ _ _ _ _ hw)
          · exact .literal (by omega) (getElem!_pos data pos (by omega))
              (mainLoop_valid _ _ _ _ _ _ hw)
        · exact .literal (by omega) (getElem!_pos data pos (by omega))
            (mainLoop_valid _ _ _ _ _ _ hw)
      · exact .literal (by omega) (getElem!_pos data pos (by omega))
          (mainLoop_valid _ _ _ _ _ _ hw)
    · exact .literal (by omega) (getElem!_pos data pos (by omega))
        (mainLoop_valid _ _ _ _ _ _ hw)
  · exact trailing_valid data pos
termination_by data.size - pos

/-! ## lz77Greedy validity -/

/-- `lz77Greedy` produces a valid decomposition of the input data. -/
theorem lz77Greedy_valid (data : ByteArray) (windowSize : Nat) (hw : windowSize > 0) :
    ValidDecomp data 0 (lz77Greedy data windowSize).toList := by
  simp only [lz77Greedy]
  split
  · simp only
    exact trailing_valid data 0
  · simp only
    exact mainLoop_valid data windowSize 65536 _ _ 0 hw

/-- Resolving the LZ77 tokens produced by `lz77Greedy` recovers the original data.
    This is the BB1 analog for the native compressor. -/
theorem lz77Greedy_resolves (data : ByteArray)
    (windowSize : Nat) (hw : windowSize > 0) :
    Deflate.Spec.resolveLZ77
      (tokensToSymbols (lz77Greedy data windowSize)) [] =
      some data.data.toList :=
  validDecomp_resolves data _ (lz77Greedy_valid data windowSize hw)

/-! ## lz77Greedy encodability -/

private def Encodable (t : LZ77Token) : Prop :=
  match t with
  | .literal _ => True
  | .reference len dist => 3 ≤ len ∧ len ≤ 258 ∧ 1 ≤ dist ∧ dist ≤ 32768

theorem trailing_encodable (data : ByteArray) (pos : Nat) :
    ∀ t ∈ lz77Greedy.trailing data pos, Encodable t := by
  unfold lz77Greedy.trailing
  split
  · intro t ht
    cases ht with
    | head => trivial
    | tail _ h => exact trailing_encodable data (pos + 1) t h
  · simp only [List.not_mem_nil, false_implies, implies_true]
termination_by data.size - pos

theorem mainLoop_encodable (data : ByteArray) (windowSize hashSize : Nat)
    (hashTable : Array Nat) (hashValid : Array Bool) (pos : Nat)
    (hw : windowSize > 0) (hws : windowSize ≤ 32768) :
    ∀ t ∈ lz77Greedy.mainLoop data windowSize hashSize hashTable hashValid pos,
      Encodable t := by
  unfold lz77Greedy.mainLoop
  split
  · rename_i hlt
    dsimp only
    split
    · rename_i hht
      split
      · rename_i hhv
        split
        · rename_i hcond
          split
          · rename_i hge
            split
            · rename_i hle
              obtain ⟨_, hmp_lt, hmp_ws⟩ := hcond
              have hmaxLenP : pos + min 258 (data.size - pos) ≤ data.size := by omega
              have hmaxLenM : hashTable[lz77Greedy.hash3 data pos hashSize hlt] +
                  min 258 (data.size - pos) ≤ data.size := by omega
              have hcm := lz77Greedy.countMatch_matches data
                hashTable[lz77Greedy.hash3 data pos hashSize hlt] pos
                (min 258 (data.size - pos)) hmaxLenM hmaxLenP
              intro t ht
              cases ht with
              | head =>
                show 3 ≤ _ ∧ _ ≤ 258 ∧ 1 ≤ _ ∧ _ ≤ 32768
                exact ⟨hge, by omega, by omega, by omega⟩
              | tail _ h => exact mainLoop_encodable _ _ _ _ _ _ hw hws t h
            · intro t ht
              cases ht with
              | head => trivial
              | tail _ h => exact mainLoop_encodable _ _ _ _ _ _ hw hws t h
          · intro t ht
            cases ht with
            | head => trivial
            | tail _ h => exact mainLoop_encodable _ _ _ _ _ _ hw hws t h
        · intro t ht
          cases ht with
          | head => trivial
          | tail _ h => exact mainLoop_encodable _ _ _ _ _ _ hw hws t h
      · intro t ht
        cases ht with
        | head => trivial
        | tail _ h => exact mainLoop_encodable _ _ _ _ _ _ hw hws t h
    · intro t ht
      cases ht with
      | head => trivial
      | tail _ h => exact mainLoop_encodable _ _ _ _ _ _ hw hws t h
  · exact trailing_encodable data pos
termination_by data.size - pos

/-! ## Length bounds -/

/-- `trailing` emits at most `data.size - pos` tokens. -/
theorem trailing_length (data : ByteArray) (pos : Nat) :
    (lz77Greedy.trailing data pos).length ≤ data.size - pos := by
  unfold lz77Greedy.trailing
  split
  · simp only [List.length_cons]
    have ih := trailing_length data (pos + 1)
    omega
  · simp only [List.length_nil, Nat.zero_le]
termination_by data.size - pos

/-- `mainLoop` emits at most `data.size - pos` tokens. -/
private theorem length_cons_le_of_advance {n k s pos : Nat}
    (ih : n ≤ s - (pos + k)) (hk : k ≥ 1) (hle : pos + k ≤ s) :
    n + 1 ≤ s - pos := by omega

theorem mainLoop_length (data : ByteArray) (windowSize hashSize : Nat)
    (hashTable : Array Nat) (hashValid : Array Bool) (pos : Nat) :
    (lz77Greedy.mainLoop data windowSize hashSize hashTable hashValid pos).length
      ≤ data.size - pos := by
  unfold lz77Greedy.mainLoop
  split
  · dsimp only
    split
    · split
      · split
        · split
          · split
            · rename_i hle
              simp only [List.length_cons]
              exact length_cons_le_of_advance (mainLoop_length _ _ _ _ _ _) (by omega) hle
            · simp only [List.length_cons]
              exact length_cons_le_of_advance (mainLoop_length _ _ _ _ _ _) (by omega) (by omega)
          · simp only [List.length_cons]
            exact length_cons_le_of_advance (mainLoop_length _ _ _ _ _ _) (by omega) (by omega)
        · simp only [List.length_cons]
          exact length_cons_le_of_advance (mainLoop_length _ _ _ _ _ _) (by omega) (by omega)
      · simp only [List.length_cons]
        exact length_cons_le_of_advance (mainLoop_length _ _ _ _ _ _) (by omega) (by omega)
    · simp only [List.length_cons]
      exact length_cons_le_of_advance (mainLoop_length _ _ _ _ _ _) (by omega) (by omega)
  · exact trailing_length data pos
termination_by data.size - pos

/-- All tokens from `lz77Greedy` have valid ranges for fixed Huffman encoding:
    lengths in 3–258 and distances in 1–32768 (so `findLengthCode`/`findDistCode`
    always succeed). -/
theorem lz77Greedy_encodable (data : ByteArray)
    (windowSize : Nat) (hw : windowSize > 0) (hws : windowSize ≤ 32768) :
    ∀ t ∈ (lz77Greedy data windowSize).toList,
      match t with
      | .literal _ => True
      | .reference len dist => 3 ≤ len ∧ len ≤ 258 ∧ 1 ≤ dist ∧ dist ≤ 32768 := by
  intro t ht
  simp only [lz77Greedy] at ht
  split at ht
  · simp only at ht; exact trailing_encodable data 0 t ht
  · simp only at ht; exact mainLoop_encodable data windowSize 65536 _ _ 0 hw hws t ht

/-! ## Lazy LZ77 correctness -/

/-! ### countMatch / trailing for lz77Lazy

These are structurally identical to the lz77Greedy versions
(defined as separate `where` functions with the same bodies). -/

theorem lz77Lazy.go_matches (data : ByteArray) (p1 p2 i maxLen : Nat)
    (h1 : p1 + maxLen ≤ data.size) (h2 : p2 + maxLen ≤ data.size)
    (hle : i ≤ maxLen) :
    let n := lz77Lazy.go data p1 p2 i maxLen h1 h2
    (∀ j, i ≤ j → j < n → data[p1 + j]! = data[p2 + j]!) ∧
    i ≤ n ∧ n ≤ maxLen := by
  unfold lz77Lazy.go
  split
  · rename_i hlt
    split
    · rename_i heq
      have ih := lz77Lazy.go_matches data p1 p2 (i + 1) maxLen h1 h2 (by omega)
      refine ⟨fun j hj hjn => ?_, by omega, ih.2.2⟩
      by_cases hji : j = i
      · subst hji
        rw [getElem!_pos data (p1 + j) (by omega),
            getElem!_pos data (p2 + j) (by omega)]
        exact beq_iff_eq.mp heq
      · exact ih.1 j (by omega) hjn
    · exact ⟨fun j hj hjn => by omega, by omega, by omega⟩
  · exact ⟨fun j hj hjn => by omega, by omega, by omega⟩
termination_by maxLen - i

theorem lz77Lazy.countMatch_matches (data : ByteArray) (p1 p2 maxLen : Nat)
    (h1 : p1 + maxLen ≤ data.size) (h2 : p2 + maxLen ≤ data.size) :
    let n := lz77Lazy.countMatch data p1 p2 maxLen h1 h2
    (∀ j, j < n → data[p1 + j]! = data[p2 + j]!) ∧ n ≤ maxLen := by
  simp only [lz77Lazy.countMatch]
  have h := lz77Lazy.go_matches data p1 p2 0 maxLen h1 h2 (by omega)
  exact ⟨fun j hj => h.1 j (by omega) hj, h.2.2⟩

theorem lz77Lazy.trailing_valid (data : ByteArray) (pos : Nat) :
    ValidDecomp data pos (lz77Lazy.trailing data pos) := by
  unfold lz77Lazy.trailing
  split
  · rename_i hlt
    exact .literal hlt (getElem!_pos data pos hlt) (lz77Lazy.trailing_valid data (pos + 1))
  · exact .done (by omega)
termination_by data.size - pos

theorem lz77Lazy.trailing_encodable (data : ByteArray) (pos : Nat) :
    ∀ t ∈ lz77Lazy.trailing data pos, Encodable t := by
  unfold lz77Lazy.trailing
  split
  · intro t ht
    cases ht with
    | head => trivial
    | tail _ h => exact lz77Lazy.trailing_encodable data (pos + 1) t h
  · simp only [List.not_mem_nil, false_implies, implies_true]
termination_by data.size - pos

theorem lz77Lazy.trailing_length (data : ByteArray) (pos : Nat) :
    (lz77Lazy.trailing data pos).length ≤ data.size - pos := by
  unfold lz77Lazy.trailing
  split
  · simp only [List.length_cons]
    have ih := lz77Lazy.trailing_length data (pos + 1)
    omega
  · simp only [List.length_nil, Nat.zero_le]
termination_by data.size - pos

/-! ### Lazy mainLoop validity

The proof follows the lazy mainLoop case structure. Helper for the recurring
"reference at pos with the first match" pattern. -/

/-- Common proof step: reference at pos with a proved countMatch. Reused by the
    chain-lazy matcher's validity proof (`LZ77ChainLazyCorrect`), sourcing the
    match hypothesis from `chainWalk_spec` instead of `countMatch_matches`. -/
theorem lazyRef_at_pos (data : ByteArray) (pos matchPos matchLen : Nat)
    (hmp_lt : matchPos < pos)
    (hge : matchLen ≥ 3) (hle : pos + matchLen ≤ data.size)
    (hcm : ∀ i, i < matchLen → data[pos + i]! = data[matchPos + i]!)
    {rest : List LZ77Token}
    (hrest : ValidDecomp data (pos + matchLen) rest) :
    ValidDecomp data pos (.reference matchLen (pos - matchPos) :: rest) :=
  .reference hge (by omega) (Nat.sub_le _ _) hle
    (fun i hi => by
      rw [show pos - (pos - matchPos) = matchPos from by omega]
      exact (hcm i hi))
    hrest

set_option backward.split false in
theorem lz77Lazy.mainLoop_valid (data : ByteArray) (windowSize hashSize : Nat)
    (hashTable : Array Nat) (hashValid : Array Bool) (pos : Nat)
    (hw : windowSize > 0) :
    ValidDecomp data pos
      (lz77Lazy.mainLoop data windowSize hashSize hashTable hashValid pos) := by
  unfold lz77Lazy.mainLoop
  split
  · rename_i hlt
    dsimp only
    split
    · rename_i hht
      split
      · rename_i hhv
        split
        · rename_i hcond
          split
          · rename_i hge
            split
            · -- pos + matchLen ≤ data.size (positive)
              rename_i hle
              have hmp_lt := hcond.2.1
              have hmaxLenP : pos + min 258 (data.size - pos) ≤ data.size := by omega
              have hmaxLenM : hashTable[lz77Lazy.hash3 data pos hashSize hlt] +
                  min 258 (data.size - pos) ≤ data.size := by omega
              have hcm := lz77Lazy.countMatch_matches data
                hashTable[lz77Lazy.hash3 data pos hashSize hlt] pos
                (min 258 (data.size - pos)) hmaxLenM hmaxLenP
              have hcm_sym : ∀ i, i < _ →
                  data[pos + i]! = data[hashTable[lz77Lazy.hash3 data pos hashSize hlt] + i]! :=
                fun i hi => (hcm.1 i hi).symm
              split
              · -- pos + 3 < data.size (positive) → lazy check
                rename_i h3lt
                split
                · rename_i hht2
                  split
                  · rename_i hhv2
                    split
                    · rename_i hcond2
                      split
                      · -- matchLen2 > matchLen → maybe pick it
                        split
                        · -- pos + 1 + matchLen2 ≤ data.size → literal + ref(matchLen2)
                          rename_i hle2
                          have hmp2_lt := hcond2.2.1
                          have hmaxLen2P : (pos + 1) + min 258 (data.size - (pos + 1))
                              ≤ data.size := by omega
                          have hmaxLen2M : (hashTable.set!
                              (lz77Lazy.hash3 data pos hashSize hlt) pos)[
                                lz77Lazy.hash3 data (pos + 1) hashSize (by omega)] +
                              min 258 (data.size - (pos + 1)) ≤ data.size := by omega
                          have hcm2 := lz77Lazy.countMatch_matches data
                            (hashTable.set! (lz77Lazy.hash3 data pos hashSize hlt) pos)[
                              lz77Lazy.hash3 data (pos + 1) hashSize (by omega)]
                            (pos + 1) (min 258 (data.size - (pos + 1)))
                            hmaxLen2M hmaxLen2P
                          exact .literal (by omega) (getElem!_pos data pos (by omega))
                            (lazyRef_at_pos data (pos + 1) _ _ hmp2_lt
                              (by omega) hle2 (fun i hi => (hcm2.1 i hi).symm)
                              (lz77Lazy.mainLoop_valid _ _ _ _ _ _ hw))
                        · -- pos + 1 + matchLen2 > data.size → ref(matchLen) at pos
                          exact lazyRef_at_pos data pos _ _ hmp_lt hge hle hcm_sym
                            (lz77Lazy.mainLoop_valid _ _ _ _ _ _ hw)
                      · -- matchLen2 ≤ matchLen → ref(matchLen) at pos
                        exact lazyRef_at_pos data pos _ _ hmp_lt hge hle hcm_sym
                          (lz77Lazy.mainLoop_valid _ _ _ _ _ _ hw)
                    · -- ¬hcond2 → ref(matchLen) at pos
                      exact lazyRef_at_pos data pos _ _ hmp_lt hge hle hcm_sym
                        (lz77Lazy.mainLoop_valid _ _ _ _ _ _ hw)
                  · -- ¬hhv2 → ref(matchLen) at pos
                    exact lazyRef_at_pos data pos _ _ hmp_lt hge hle hcm_sym
                      (lz77Lazy.mainLoop_valid _ _ _ _ _ _ hw)
                · -- ¬hht2 → ref(matchLen) at pos
                  exact lazyRef_at_pos data pos _ _ hmp_lt hge hle hcm_sym
                    (lz77Lazy.mainLoop_valid _ _ _ _ _ _ hw)
              · -- ¬h3lt → ref(matchLen) at pos (no updateHashes)
                exact lazyRef_at_pos data pos _ _ hmp_lt hge hle hcm_sym
                  (lz77Lazy.mainLoop_valid _ _ _ _ _ _ hw)
            · exact .literal (by omega) (getElem!_pos data pos (by omega))
                (lz77Lazy.mainLoop_valid _ _ _ _ _ _ hw)
          · exact .literal (by omega) (getElem!_pos data pos (by omega))
              (lz77Lazy.mainLoop_valid _ _ _ _ _ _ hw)
        · exact .literal (by omega) (getElem!_pos data pos (by omega))
            (lz77Lazy.mainLoop_valid _ _ _ _ _ _ hw)
      · exact .literal (by omega) (getElem!_pos data pos (by omega))
          (lz77Lazy.mainLoop_valid _ _ _ _ _ _ hw)
    · exact .literal (by omega) (getElem!_pos data pos (by omega))
        (lz77Lazy.mainLoop_valid _ _ _ _ _ _ hw)
  · exact lz77Lazy.trailing_valid data pos
termination_by data.size - pos
decreasing_by all_goals omega

/-- `lz77Lazy` produces a valid decomposition of the input data. -/
theorem lz77Lazy_valid (data : ByteArray) (windowSize : Nat) (hw : windowSize > 0) :
    ValidDecomp data 0 (lz77Lazy data windowSize).toList := by
  simp only [lz77Lazy]
  split
  · simp only; exact lz77Lazy.trailing_valid data 0
  · simp only; exact lz77Lazy.mainLoop_valid data windowSize 65536 _ _ 0 hw

/-- Resolving the LZ77 tokens produced by `lz77Lazy` recovers the original data. -/
theorem lz77Lazy_resolves (data : ByteArray)
    (windowSize : Nat) (hw : windowSize > 0) :
    Deflate.Spec.resolveLZ77
      (tokensToSymbols (lz77Lazy data windowSize)) [] =
      some data.data.toList :=
  validDecomp_resolves data _ (lz77Lazy_valid data windowSize hw)

/-! ### Lazy mainLoop encodability -/

set_option backward.split false in
theorem lz77Lazy.mainLoop_encodable (data : ByteArray) (windowSize hashSize : Nat)
    (hashTable : Array Nat) (hashValid : Array Bool) (pos : Nat)
    (hw : windowSize > 0) (hws : windowSize ≤ 32768) :
    ∀ t ∈ lz77Lazy.mainLoop data windowSize hashSize hashTable hashValid pos,
      Encodable t := by
  unfold lz77Lazy.mainLoop
  split
  · rename_i hlt
    dsimp only
    split
    · rename_i hht
      split
      · rename_i hhv
        split
        · rename_i hcond
          split
          · rename_i hge
            split
            · rename_i hle
              have hmp_ws := hcond.2.2
              have hmaxLenP : pos + min 258 (data.size - pos) ≤ data.size := by omega
              have hmaxLenM : hashTable[lz77Lazy.hash3 data pos hashSize hlt] +
                  min 258 (data.size - pos) ≤ data.size := by omega
              have hcm := lz77Lazy.countMatch_matches data
                hashTable[lz77Lazy.hash3 data pos hashSize hlt] pos
                (min 258 (data.size - pos)) hmaxLenM hmaxLenP
              -- Encoder for "ref(matchLen) at pos :: rest"
              have ref_at_pos : ∀ {rec : List LZ77Token},
                  (∀ t ∈ rec, Encodable t) →
                  ∀ t ∈ (LZ77Token.reference
                      (lz77Lazy.countMatch data
                        hashTable[lz77Lazy.hash3 data pos hashSize hlt] pos
                        (min 258 (data.size - pos)) hmaxLenM hmaxLenP)
                      (pos - hashTable[lz77Lazy.hash3 data pos hashSize hlt]) :: rec),
                    Encodable t := fun hrec t ht => by
                cases ht with
                | head =>
                  show 3 ≤ _ ∧ _ ≤ 258 ∧ 1 ≤ _ ∧ _ ≤ 32768
                  exact ⟨hge, by have := hcm.2; omega, by omega, by omega⟩
                | tail _ h => exact hrec t h
              split
              · rename_i h3lt
                split
                · rename_i hht2
                  split
                  · rename_i hhv2
                    split
                    · rename_i hcond2
                      have hmp2_ws := hcond2.2.2
                      have hmaxLen2P : (pos + 1) + min 258 (data.size - (pos + 1))
                          ≤ data.size := by omega
                      have hmaxLen2M : (hashTable.set!
                          (lz77Lazy.hash3 data pos hashSize hlt) pos)[
                            lz77Lazy.hash3 data (pos + 1) hashSize h3lt] +
                          min 258 (data.size - (pos + 1)) ≤ data.size := by omega
                      have hcm2 := lz77Lazy.countMatch_matches data
                        (hashTable.set! (lz77Lazy.hash3 data pos hashSize hlt) pos)[
                          lz77Lazy.hash3 data (pos + 1) hashSize h3lt]
                        (pos + 1) (min 258 (data.size - (pos + 1)))
                        hmaxLen2M hmaxLen2P
                      split
                      · split
                        · -- literal + reference(matchLen2) at pos+1 + recursive
                          rename_i hmatchLen2_gt _
                          intro t ht; cases ht with
                          | head => trivial
                          | tail _ h =>
                            cases h with
                            | head =>
                              show 3 ≤ _ ∧ _ ≤ 258 ∧ 1 ≤ _ ∧ _ ≤ 32768
                              exact ⟨by omega, by have := hcm2.2; omega,
                                by omega, by omega⟩
                            | tail _ h => exact lz77Lazy.mainLoop_encodable _ _ _ _ _ _ hw hws t h
                        · exact ref_at_pos (fun t h =>
                            lz77Lazy.mainLoop_encodable _ _ _ _ _ _ hw hws t h)
                      · exact ref_at_pos (fun t h =>
                          lz77Lazy.mainLoop_encodable _ _ _ _ _ _ hw hws t h)
                    · exact ref_at_pos (fun t h =>
                        lz77Lazy.mainLoop_encodable _ _ _ _ _ _ hw hws t h)
                  · exact ref_at_pos (fun t h =>
                      lz77Lazy.mainLoop_encodable _ _ _ _ _ _ hw hws t h)
                · exact ref_at_pos (fun t h =>
                    lz77Lazy.mainLoop_encodable _ _ _ _ _ _ hw hws t h)
              · exact ref_at_pos (fun t h =>
                  lz77Lazy.mainLoop_encodable _ _ _ _ _ _ hw hws t h)
            · intro t ht; cases ht with
              | head => trivial
              | tail _ h => exact lz77Lazy.mainLoop_encodable _ _ _ _ _ _ hw hws t h
          · intro t ht; cases ht with
            | head => trivial
            | tail _ h => exact lz77Lazy.mainLoop_encodable _ _ _ _ _ _ hw hws t h
        · intro t ht; cases ht with
          | head => trivial
          | tail _ h => exact lz77Lazy.mainLoop_encodable _ _ _ _ _ _ hw hws t h
      · intro t ht; cases ht with
        | head => trivial
        | tail _ h => exact lz77Lazy.mainLoop_encodable _ _ _ _ _ _ hw hws t h
    · intro t ht; cases ht with
      | head => trivial
      | tail _ h => exact lz77Lazy.mainLoop_encodable _ _ _ _ _ _ hw hws t h
  · exact lz77Lazy.trailing_encodable data pos
termination_by data.size - pos
decreasing_by all_goals omega

/-- All tokens from `lz77Lazy` have valid ranges for fixed Huffman encoding. -/
theorem lz77Lazy_encodable (data : ByteArray)
    (windowSize : Nat) (hw : windowSize > 0) (hws : windowSize ≤ 32768) :
    ∀ t ∈ (lz77Lazy data windowSize).toList,
      match t with
      | .literal _ => True
      | .reference len dist => 3 ≤ len ∧ len ≤ 258 ∧ 1 ≤ dist ∧ dist ≤ 32768 := by
  intro t ht
  simp only [lz77Lazy] at ht
  split at ht
  · simp only at ht; exact lz77Lazy.trailing_encodable data 0 t ht
  · simp only at ht; exact lz77Lazy.mainLoop_encodable data windowSize 65536 _ _ 0 hw hws t ht

/-! ### Lazy mainLoop length bounds -/

private theorem lazy_length_one {n s pos pos' : Nat}
    (ih : n ≤ 2 * (s - pos')) (hlt : pos < pos') (hle : pos' ≤ s) :
    n + 1 ≤ 2 * (s - pos) := by omega

private theorem lazy_length_two {n s pos pos' : Nat}
    (ih : n ≤ 2 * (s - pos')) (hlt : pos < pos') (hle : pos' ≤ s) :
    n + 2 ≤ 2 * (s - pos) := by omega

set_option backward.split false in
theorem lz77Lazy.mainLoop_length (data : ByteArray) (windowSize hashSize : Nat)
    (hashTable : Array Nat) (hashValid : Array Bool) (pos : Nat) :
    (lz77Lazy.mainLoop data windowSize hashSize hashTable hashValid pos).length
      ≤ 2 * (data.size - pos) := by
  unfold lz77Lazy.mainLoop
  split
  · dsimp only
    split
    · split
      · split
        · split
          · rename_i hge
            split
            · rename_i hle
              split
              · rename_i h3lt
                split
                · rename_i hht2
                  split
                  · rename_i hhv2
                    split
                    · rename_i hcond2
                      split
                      · rename_i hmatchLen2_gt
                        split
                        · rename_i hle2
                          exact lazy_length_two
                            (lz77Lazy.mainLoop_length _ _ _ _ _ _) (by omega) hle2
                        · exact lazy_length_one
                            (lz77Lazy.mainLoop_length _ _ _ _ _ _) (by omega) hle
                      · exact lazy_length_one
                          (lz77Lazy.mainLoop_length _ _ _ _ _ _) (by omega) hle
                    · exact lazy_length_one
                        (lz77Lazy.mainLoop_length _ _ _ _ _ _) (by omega) hle
                  · exact lazy_length_one
                      (lz77Lazy.mainLoop_length _ _ _ _ _ _) (by omega) hle
                · exact lazy_length_one
                    (lz77Lazy.mainLoop_length _ _ _ _ _ _) (by omega) hle
              · exact lazy_length_one
                  (lz77Lazy.mainLoop_length _ _ _ _ _ _) (by omega) hle
            · exact lazy_length_one
                (lz77Lazy.mainLoop_length _ _ _ _ _ _) (by omega) (by omega)
          · exact lazy_length_one
              (lz77Lazy.mainLoop_length _ _ _ _ _ _) (by omega) (by omega)
        · exact lazy_length_one
            (lz77Lazy.mainLoop_length _ _ _ _ _ _) (by omega) (by omega)
      · exact lazy_length_one
          (lz77Lazy.mainLoop_length _ _ _ _ _ _) (by omega) (by omega)
    · exact lazy_length_one
        (lz77Lazy.mainLoop_length _ _ _ _ _ _) (by omega) (by omega)
  · have := lz77Lazy.trailing_length data pos; omega
termination_by data.size - pos
decreasing_by all_goals omega

/-- The token count from `lz77Lazy` is at most `2 * data.size`. In the worst
    case every position emits a literal + reference. -/
theorem lz77Lazy_size_le (data : ByteArray) (windowSize : Nat) :
    (lz77Lazy data windowSize).size ≤ 2 * data.size := by
  simp only [lz77Lazy]
  split
  · simp only [List.size_toArray]
    have := lz77Lazy.trailing_length data 0; omega
  · simp only [List.size_toArray]
    exact lz77Lazy.mainLoop_length data windowSize 65536
      (Array.replicate 65536 0) (Array.replicate 65536 false) 0

end Zip.Native.Deflate
