import Zip.Spec.EmitPackedCorrect
import Zip.Spec.BitWriterCorrect
import Zip.Spec.DeflateDynamicEmit
import Zip.Spec.DeflateDynamicHeader
import Zip.Spec.DeflateDynamicFreqs

/-!
# Correctness of flat-state packed token emission

`emitTokensWithCodesTAPTFlat` changes when complete bytes are drained from a
`BitWriter`, so it is intentionally not structurally equal to the reference
emitter.  This file proves the observational contract needed by block emission:
the same `BitWriter.toBits` sequence and preservation of `BitWriter.wf` for
canonical packed code tables.
-/

namespace Zip.Native.Deflate

/-- `packCodeEntry` preserves the code length byte. -/
private theorem flat_packCodeEntry_len (e : UInt16 × UInt8) :
    ((packCodeEntry e >>> 16) &&& 0xFF).toNat = e.2.toNat := by
  have hlen : (packCodeEntry e >>> 16).toUInt8 = e.2 := by
    obtain ⟨c, l⟩ := e
    unfold packCodeEntry
    generalize BitWriter.reverse16 c = r
    bv_decide
  have hlow (x : UInt32) : (x &&& 0xFF).toNat = x.toUInt8.toNat := by
    rw [UInt32.toNat_and, UInt32.toNat_toUInt8]
    have h255 : (0xFF : UInt32).toNat = 255 := rfl
    rw [h255]
    have hand : x.toNat &&& 255 = x.toNat % 256 := by
      simpa using Nat.and_two_pow_sub_one_eq_mod x.toNat 8
    rw [hand]
  rw [hlow, hlen]

/-- Fixed-width form of `flat_packCodeEntry_len`, used to expose the exact
    `UInt32` field consumed by the flat emitter. -/
private theorem flat_packCodeEntry_len32 (e : UInt16 × UInt8) :
    (packCodeEntry e >>> 16) &&& 0xFF = e.2.toUInt32 := by
  apply UInt32.toNat_inj.mp
  rw [flat_packCodeEntry_len, UInt8.toNat_toUInt32]

/-- The low word of a packed entry is the pre-reversed canonical code. -/
private theorem flat_packCodeEntry_code (e : UInt16 × UInt8) :
    (packCodeEntry e).toUInt16 =
      ((BitWriter.reverse16 e.1).toUInt64 >>> (16 - e.2.toUInt64)).toUInt16 := by
  obtain ⟨c, l⟩ := e
  unfold packCodeEntry
  generalize BitWriter.reverse16 c = r
  bv_decide

/-- A packed entry whose length is at most 15 contains no live code bits above
    that length. -/
private theorem flat_packCodeEntry_bound (e : UInt16 × UInt8)
    (hlen : e.2.toNat ≤ 15) :
    (packCodeEntry e).toUInt16.toUInt64.toNat < 2 ^ e.2.toNat := by
  rw [flat_packCodeEntry_code]
  have hle : e.2.toUInt64 ≤ (16 : UInt64) := by
    rw [UInt64.le_iff_toNat_le, UInt8.toNat_toUInt64,
      show (16 : UInt64).toNat = 16 by decide]
    omega
  have hsub : (16 - e.2.toUInt64).toNat = 16 - e.2.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ hle, UInt8.toNat_toUInt64,
      show (16 : UInt64).toNat = 16 by decide]
  have hrev : (BitWriter.reverse16 e.1).toNat < 2 ^ 16 := by
    have := (BitWriter.reverse16 e.1).toNat_lt
    simpa only [UInt16.size] using this
  have hshift :
      ((BitWriter.reverse16 e.1).toUInt64 >>> (16 - e.2.toUInt64)).toNat =
        (BitWriter.reverse16 e.1).toNat / 2 ^ (16 - e.2.toNat) := by
    rw [UInt64.toNat_shiftRight, UInt16.toNat_toUInt64, hsub,
      Nat.shiftRight_eq_div_pow]
    congr 2
    omega
  rw [UInt16.toNat_toUInt64, UInt64.toNat_toUInt16, hshift]
  have hdiv :
      (BitWriter.reverse16 e.1).toNat / 2 ^ (16 - e.2.toNat) < 2 ^ e.2.toNat := by
    apply Nat.div_lt_of_lt_mul
    rw [← Nat.pow_add, show 16 - e.2.toNat + e.2.toNat = 16 from by omega]
    exact hrev
  rw [Nat.mod_eq_of_lt]
  · exact hdiv
  · exact Nat.lt_of_lt_of_le hdiv (Nat.pow_le_pow_right (by omega) (by omega))

/-- On a well-formed writer, the flat primitive applied to one packed table
    entry is structurally the ordinary Huffman-code write.  The pre-drain guard
    cannot fire because the pending count is below 32 and a DEFLATE code is at
    most 15 bits. -/
private theorem writeBits64_packCodeEntry_eq (bw : BitWriter)
    (e : UInt16 × UInt8) (hwf : bw.wf) (hlen : e.2.toNat ≤ 15) :
    bw.writeBits64 ((packCodeEntry e >>> 16) &&& 0xFF)
        (packCodeEntry e).toUInt16.toUInt64 =
      bw.writeHuffCode e.1 e.2 := by
  rw [flat_packCodeEntry_len32, flat_packCodeEntry_code]
  have hbc := hwf.1
  have hguard : ¬bw.bitCount.toUInt32 + e.2.toUInt32 ≥ (64 : UInt32) := by
    intro hge
    have hgeN := UInt32.le_iff_toNat_le.mp hge
    rw [UInt32.toNat_add, UInt8.toNat_toUInt32, UInt8.toNat_toUInt32,
      Nat.mod_eq_of_lt (by
        have hbc := UInt8.toNat_lt bw.bitCount
        have hlen8 := UInt8.toNat_lt e.2
        omega), show (64 : UInt32).toNat = 64 by decide] at hgeN
    omega
  unfold BitWriter.writeBits64
  rw [if_neg hguard]
  change bw.writeRevCode
      ((BitWriter.reverse16 e.1).toUInt64 >>> (16 - e.2.toUInt64)).toUInt16 e.2 =
    bw.writeHuffCode e.1 e.2
  exact BitWriter.writeRevCode_eq bw e.1 e.2

/-- The low-order bit list stored in one packed table entry is the canonical
    code's MSB-first bit list. -/
private theorem flat_packCodeEntry_bits (e : UInt16 × UInt8)
    (hlen : e.2.toNat ≤ 15) :
    Deflate.Spec.writeBitsLSB e.2.toNat
        (packCodeEntry e).toUInt16.toUInt64.toNat =
      Huffman.Spec.natToBits e.1.toNat e.2.toNat := by
  have heq := congrArg BitWriter.toBits
    (writeBits64_packCodeEntry_eq BitWriter.empty e BitWriter.empty_wf hlen)
  have hbound := flat_packCodeEntry_bound e hlen
  rw [BitWriter.writeBits64_toBits BitWriter.empty
      ((packCodeEntry e >>> 16) &&& 0xFF) (packCodeEntry e).toUInt16.toUInt64
      BitWriter.empty_wf (by rw [flat_packCodeEntry_len]; omega)
      (by simpa only [flat_packCodeEntry_len] using hbound),
    BitWriter.writeHuffCode_toBits BitWriter.empty e.1 e.2 BitWriter.empty_wf hlen,
    BitWriter.empty_toBits, List.nil_append, flat_packCodeEntry_len] at heq
  exact heq

/-- The extra-bit count field of a packed code word is below 256. -/
private theorem flat_codeExtra_lt_256 (w : UInt32) : codeExtra w < 256 := by
  unfold codeExtra
  have h : (w >>> 8) &&& 0xFF < 256 := by bv_decide
  simpa using UInt32.lt_iff_toNat_lt.mp h

/-- The raw byte field used by the flat loop is the `UInt32` embedding of
    `codeExtra`. -/
private theorem flat_codeExtra32 (w : UInt32) :
    (w >>> 8) &&& 0xFF = (codeExtra w).toUInt32 := by
  apply UInt32.toNat_inj.mp
  unfold codeExtra
  rw [Nat.toUInt32, UInt32.toNat_ofNat', Nat.mod_eq_of_lt]
  exact Nat.lt_trans (flat_codeExtra_lt_256 w) (by decide)

/-- A `UInt32` value and its `Nat` view have the same `UInt64` embedding. -/
private theorem uint32_toUInt64_eq_toNat (n : UInt32) :
    n.toUInt64 = n.toNat.toUInt64 := by
  apply UInt64.toNat_inj.mp
  rw [UInt32.toNat_toUInt64]
  simp only [Nat.toUInt64, UInt64.toNat_ofNat']
  symm
  apply Nat.mod_eq_of_lt
  exact Nat.lt_of_lt_of_le n.toNat_lt
    (Nat.pow_le_pow_right (by omega) (by omega))

/-- Nat value of the low-`n` mask, for shifts below the `UInt64` width. -/
private theorem uint64_lowMask_toNat (n : Nat) (hn : n < 64) :
    ((1 <<< n.toUInt64) - 1 : UInt64).toNat = 2 ^ n - 1 := by
  have hnm : n.toUInt64.toNat % 64 = n := by
    simp only [Nat.toUInt64, UInt64.toNat_ofNat']
    rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hn (by omega)), Nat.mod_eq_of_lt hn]
  have hpow : 2 ^ n < 2 ^ 64 := Nat.pow_lt_pow_right (by omega) hn
  have hshift : (1 <<< n.toUInt64 : UInt64).toNat = 2 ^ n := by
    rw [UInt64.toNat_shiftLeft, UInt64.toNat_one, hnm, Nat.shiftLeft_eq, Nat.one_mul,
      Nat.mod_eq_of_lt hpow]
  have hle : (1 : UInt64) ≤ 1 <<< n.toUInt64 := by
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_one, hshift]
    exact Nat.two_pow_pos n
  rw [UInt64.toNat_sub_of_le _ _ hle, hshift, UInt64.toNat_one]

/-- Masking a value already known to fit in `n < 64` bits is a no-op. -/
private theorem uint64_and_lowMask_eq (v : UInt64) (n : UInt32)
    (hn : n.toNat < 64) (hv : v.toNat < 2 ^ n.toNat) :
    v &&& ((1 <<< n.toUInt64) - 1) = v := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_and, uint32_toUInt64_eq_toNat,
    uint64_lowMask_toNat n.toNat hn, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_eq_of_lt hv]

/-- The low-`n` mask always produces an `n`-bit value. -/
private theorem uint64_and_lowMask_bound (v : UInt64) (n : UInt32)
    (hn : n.toNat < 64) :
    (v &&& ((1 <<< n.toUInt64) - 1)).toNat < 2 ^ n.toNat := by
  rw [UInt64.toNat_and, uint32_toUInt64_eq_toNat,
    uint64_lowMask_toNat n.toNat hn, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (Nat.two_pow_pos _)

/-- Masking does not change the low-order bit list written for that width. -/
private theorem writeBitsLSB_lowMask (v : UInt64) (n : UInt32)
    (hn : n.toNat < 64) :
    Deflate.Spec.writeBitsLSB n.toNat
        (v &&& ((1 <<< n.toUInt64) - 1)).toNat =
      Deflate.Spec.writeBitsLSB n.toNat v.toNat := by
  rw [BitWriter.writeBitsLSB_eq_map, BitWriter.writeBitsLSB_eq_map]
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_range] at hi
  rw [UInt64.toNat_and, uint32_toUInt64_eq_toNat,
    uint64_lowMask_toNat n.toNat hn, Nat.and_two_pow_sub_one_eq_mod,
    Nat.testBit_mod_two_pow]
  simp only [hi, decide_true, Bool.true_and]

/-- Packed-table `writeRevCode` of one `packCodeEntry` is the ordinary
    Huffman write for the original entry. -/
private theorem writeRevCode_packCodeEntry_eq (bw : BitWriter)
    (e : UInt16 × UInt8) :
    bw.writeRevCode (packCodeEntry e).toUInt16 (packCodeEntry e >>> 16).toUInt8 =
      bw.writeHuffCode e.1 e.2 := by
  rw [show (packCodeEntry e >>> 16).toUInt8 = e.2 from by
    obtain ⟨c, l⟩ := e
    unfold packCodeEntry
    generalize BitWriter.reverse16 c = r
    bv_decide,
    flat_packCodeEntry_code, BitWriter.writeRevCode_eq]

/-- The packed-table reference helper is the pair-table helper over the
    original tables.  Kept local so the flat-loop proof can expose its four
    sequential reference writes. -/
private theorem flat_emitRefWithCodesPT_eq (bw : BitWriter)
    (litCodes distCodes : Array (UInt16 × UInt8)) (w : UInt32) :
    emitRefWithCodesPT bw (packCodeTab litCodes) (packCodeTab distCodes) w =
      emitRefWithCodesP bw litCodes distCodes w := by
  unfold emitRefWithCodesPT emitRefWithCodesP
  simp only [packCodeTab, Array.size_map, Array.getElem_map,
    writeRevCode_packCodeEntry_eq, BitWriter.writeRevCodeExtra_eq,
    flat_codeExtra_lt_256]
  rfl

/-- A bounded shifted `UInt64` pair does not wrap, so its `toNat` view is the
    corresponding Nat shift/OR. -/
private theorem uint64_or_shift_toNat (a b : UInt64) (n m : Nat)
    (hn : n < 64) (hb : b.toNat < 2 ^ m) (hsum : n + m ≤ 64) :
    (a ||| (b <<< n.toUInt64)).toNat = a.toNat ||| (b.toNat <<< n) := by
  rw [UInt64.toNat_or, UInt64.toNat_shiftLeft]
  have hn64 : n.toUInt64.toNat % 64 = n := by
    simp only [Nat.toUInt64, UInt64.toNat_ofNat']
    rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hn (by decide : 64 ≤ 2 ^ 64)),
      Nat.mod_eq_of_lt hn]
  rw [hn64]
  congr 1
  apply Nat.mod_eq_of_lt
  rw [Nat.shiftLeft_eq]
  calc
    b.toNat * 2 ^ n < 2 ^ m * 2 ^ n :=
      Nat.mul_lt_mul_of_pos_right hb (Nat.two_pow_pos _)
    _ = 2 ^ (m + n) := (Nat.pow_add 2 _ _).symm
    _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) (by omega)

/-- Bound for a shift/OR concatenation of two bounded fields. -/
private theorem uint64_or_shift_bound (a b : UInt64) (n m : Nat)
    (ha : a.toNat < 2 ^ n) (hb : b.toNat < 2 ^ m) (hsum : n + m ≤ 64) :
    (a ||| (b <<< n.toUInt64)).toNat < 2 ^ (n + m) := by
  by_cases hm : m = 0
  · subst hm
    have : b.toNat = 0 := by simpa using hb
    have hb0 : b = 0 := UInt64.toNat_inj.mp this
    subst b
    simpa using ha
  have hn : n < 64 := by omega
  rw [uint64_or_shift_toNat a b n m hn hb hsum]
  exact BitWriter.or_shiftLeft_lt a.toNat b.toNat n m ha hb

/-- Non-wrapping `UInt32` addition viewed as `Nat`. -/
private theorem uint32_add_toNat (n m : UInt32) (h : n.toNat + m.toNat < 2 ^ 32) :
    (n + m).toNat = n.toNat + m.toNat := by
  rw [UInt32.toNat_add, Nat.mod_eq_of_lt h]

/-- `UInt32`-width wrapper around `uint64_or_shift_bound`. -/
private theorem uint64_or_shift_bound32 (a b : UInt64) (n m : UInt32)
    (ha : a.toNat < 2 ^ n.toNat) (hb : b.toNat < 2 ^ m.toNat)
    (hsum : n.toNat + m.toNat ≤ 64) :
    (a ||| (b <<< n.toUInt64)).toNat < 2 ^ (n + m).toNat := by
  rw [uint32_add_toNat n m (by omega), uint32_toUInt64_eq_toNat]
  exact uint64_or_shift_bound a b n.toNat m.toNat ha hb hsum

/-- Bit-list view of the same two-field concatenation. -/
private theorem writeBitsLSB_uint64_pair (a b : UInt64) (n m : Nat)
    (hn : n < 64) (ha : a.toNat < 2 ^ n) (hb : b.toNat < 2 ^ m)
    (hsum : n + m ≤ 64) :
    Deflate.Spec.writeBitsLSB (n + m) (a ||| (b <<< n.toUInt64)).toNat =
      Deflate.Spec.writeBitsLSB n a.toNat ++
        Deflate.Spec.writeBitsLSB m b.toNat := by
  rw [uint64_or_shift_toNat a b n m hn hb hsum]
  exact BitWriter.writeBitsLSB_or_shift a.toNat b.toNat n m ha

/-- `UInt32`-width wrapper around `writeBitsLSB_uint64_pair`. -/
private theorem writeBitsLSB_uint64_pair32 (a b : UInt64) (n m : UInt32)
    (ha : a.toNat < 2 ^ n.toNat) (hb : b.toNat < 2 ^ m.toNat)
    (hsum : n.toNat + m.toNat < 64) :
    Deflate.Spec.writeBitsLSB (n + m).toNat
        (a ||| (b <<< n.toUInt64)).toNat =
      Deflate.Spec.writeBitsLSB n.toNat a.toNat ++
        Deflate.Spec.writeBitsLSB m.toNat b.toNat := by
  rw [uint32_add_toNat n m (by omega), uint32_toUInt64_eq_toNat]
  exact writeBitsLSB_uint64_pair a b n.toNat m.toNat (by omega) ha hb (by omega)

/-- Writer-level form: one `writeBits64` of a packed pair is observationally
    the two component bit fields, and preserves well-formedness. -/
private theorem writeBits64_pair_spec (bw : BitWriter) (a b : UInt64)
    (n m : UInt32) (hwf : bw.wf)
    (ha : a.toNat < 2 ^ n.toNat) (hb : b.toNat < 2 ^ m.toNat)
    (hsum : n.toNat + m.toNat ≤ 48) :
    (bw.writeBits64 (n + m) (a ||| (b <<< n.toUInt64))).toBits =
        bw.toBits ++ Deflate.Spec.writeBitsLSB n.toNat a.toNat ++
          Deflate.Spec.writeBitsLSB m.toNat b.toNat ∧
      (bw.writeBits64 (n + m) (a ||| (b <<< n.toUInt64))).wf := by
  have hadd : (n + m).toNat = n.toNat + m.toNat := by
    rw [UInt32.toNat_add, Nat.mod_eq_of_lt]
    omega
  have hn : n.toNat < 64 := by omega
  have hcast : n.toNat.toUInt64 = n.toUInt64 := by
    apply UInt64.toNat_inj.mp
    rw [UInt32.toNat_toUInt64]
    simp only [Nat.toUInt64, UInt64.toNat_ofNat']
    rw [Nat.mod_eq_of_lt]
    have := n.toNat_lt
    simp only [UInt32.size] at this
    omega
  have hpacked : (a ||| (b <<< n.toUInt64)).toNat < 2 ^ (n + m).toNat := by
    rw [hadd, ← hcast]
    exact uint64_or_shift_bound a b n.toNat m.toNat ha hb (by omega)
  refine ⟨?_, BitWriter.writeBits64_wf bw (n + m) _ hwf (by omega) hpacked⟩
  rw [BitWriter.writeBits64_toBits bw (n + m) _ hwf (by omega) hpacked, hadd, ← hcast,
    writeBitsLSB_uint64_pair a b n.toNat m.toNat hn ha hb (by omega),
    List.append_assoc]

/-- One flat write of a complete reference-token field is observationally the
    four ordinary fields: length code, length extra, distance code, distance
    extra.  This is the central algebraic fact behind the flat loop. -/
private theorem writeBits64_ref_spec (bw : BitWriter)
    (le de : UInt16 × UInt8) (lextra dextra : UInt64)
    (lextraN dextraN : UInt32) (hwf : bw.wf)
    (hlen : le.2.toNat ≤ 15) (hdlen : de.2.toNat ≤ 15)
    (hlextraN : lextraN.toNat ≤ 5) (hdextraN : dextraN.toNat ≤ 13)
    (hlextra : lextra.toNat < 2 ^ lextraN.toNat)
    (hdextra : dextra.toNat < 2 ^ dextraN.toNat) :
    let lenBits := (packCodeEntry le).toUInt16.toUInt64 |||
      (lextra <<< le.2.toUInt32.toUInt64)
    let lenTotal := le.2.toUInt32 + lextraN
    let distBits := (packCodeEntry de).toUInt16.toUInt64 |||
      (dextra <<< de.2.toUInt32.toUInt64)
    (bw.writeBits64 (lenTotal + de.2.toUInt32 + dextraN)
      (lenBits ||| (distBits <<< lenTotal.toUInt64))).toBits =
        bw.toBits ++ Huffman.Spec.natToBits le.1.toNat le.2.toNat ++
          Deflate.Spec.writeBitsLSB lextraN.toNat lextra.toNat ++
          Huffman.Spec.natToBits de.1.toNat de.2.toNat ++
          Deflate.Spec.writeBitsLSB dextraN.toNat dextra.toNat ∧
      (bw.writeBits64 (lenTotal + de.2.toUInt32 + dextraN)
        (lenBits ||| (distBits <<< lenTotal.toUInt64))).wf := by
  dsimp only
  have hlcode := flat_packCodeEntry_bound le hlen
  have hdcode := flat_packCodeEntry_bound de hdlen
  have hlenBits := uint64_or_shift_bound32
    (packCodeEntry le).toUInt16.toUInt64 lextra le.2.toUInt32 lextraN
    (by simpa only [UInt8.toNat_toUInt32] using hlcode) hlextra
    (by rw [UInt8.toNat_toUInt32]; omega)
  have hdistBits := uint64_or_shift_bound32
    (packCodeEntry de).toUInt16.toUInt64 dextra de.2.toUInt32 dextraN
    (by simpa only [UInt8.toNat_toUInt32] using hdcode) hdextra
    (by rw [UInt8.toNat_toUInt32]; omega)
  let lenBits := (packCodeEntry le).toUInt16.toUInt64 |||
    (lextra <<< le.2.toUInt32.toUInt64)
  let lenTotal := le.2.toUInt32 + lextraN
  let distBits := (packCodeEntry de).toUInt16.toUInt64 |||
    (dextra <<< de.2.toUInt32.toUInt64)
  let distTotal := de.2.toUInt32 + dextraN
  have hlenTotal : lenTotal.toNat = le.2.toNat + lextraN.toNat := by
    dsimp only [lenTotal]
    rw [uint32_add_toNat _ _ (by rw [UInt8.toNat_toUInt32]; omega),
      UInt8.toNat_toUInt32]
  have hdistTotal : distTotal.toNat = de.2.toNat + dextraN.toNat := by
    dsimp only [distTotal]
    rw [uint32_add_toNat _ _ (by rw [UInt8.toNat_toUInt32]; omega),
      UInt8.toNat_toUInt32]
  have htotal : lenTotal.toNat + distTotal.toNat ≤ 48 := by
    rw [hlenTotal, hdistTotal]
    omega
  have hout := writeBits64_pair_spec bw lenBits distBits lenTotal distTotal hwf
    (by simpa only [lenBits, lenTotal] using hlenBits)
    (by simpa only [distBits, distTotal] using hdistBits) htotal
  have hsplitLen := writeBitsLSB_uint64_pair32
    (packCodeEntry le).toUInt16.toUInt64 lextra le.2.toUInt32 lextraN
    (by simpa only [UInt8.toNat_toUInt32] using hlcode) hlextra
    (by rw [UInt8.toNat_toUInt32]; omega)
  have hsplitDist := writeBitsLSB_uint64_pair32
    (packCodeEntry de).toUInt16.toUInt64 dextra de.2.toUInt32 dextraN
    (by simpa only [UInt8.toNat_toUInt32] using hdcode) hdextra
    (by rw [UInt8.toNat_toUInt32]; omega)
  have hassoc : lenTotal + distTotal = lenTotal + de.2.toUInt32 + dextraN := by
    simp only [distTotal, UInt32.add_assoc]
  rw [hassoc] at hout
  simpa only [lenBits, lenTotal, distBits, distTotal, hsplitLen, hsplitDist,
    UInt8.toNat_toUInt32, flat_packCodeEntry_bits le hlen,
    flat_packCodeEntry_bits de hdlen, List.append_assoc] using hout

/-- Under the production table-size and code-length invariants, the actual
    packed-word/masked flat reference step is observationally equal to the
    existing packed-table reference helper, and both outputs are well formed. -/
private theorem emitRefWithCodesPTFlatStep_spec (fbw rbw : BitWriter)
    (litCodes distCodes : Array (UInt16 × UInt8)) (w : UInt32)
    (hlit : litCodes.size ≥ 286) (hdist : distCodes.size ≥ 30)
    (hbits : fbw.toBits = rbw.toBits) (hfwf : fbw.wf) (hrwf : rbw.wf)
    (hlit_le : ∀ j, j < litCodes.size → litCodes[j]!.2.toNat ≤ 15)
    (hdist_le : ∀ j, j < distCodes.size → distCodes[j]!.2.toNat ≤ 15) :
    let fw := emitRefWithCodesPTFlat fbw
      (packCodeTab litCodes) (packCodeTab distCodes) w
    let rw := emitRefWithCodesPT rbw
      (packCodeTab litCodes) (packCodeTab distCodes) w
    fw.toBits = rw.toBits ∧ fw.wf ∧ rw.wf := by
  dsimp only
  let len := ((w >>> 16) &&& 0x7FFF).toNat
  let dist := (w &&& 0xFFFF).toNat
  obtain ⟨⟨idx, en, ev⟩, hflc⟩ := Option.isSome_iff_exists.mp
    (findLengthCode_isSome len)
  obtain ⟨⟨dIdx, den, dev⟩, hfdc⟩ := Option.isSome_iff_exists.mp
    (findDistCode_isSome dist)
  have hidx := nativeFindLengthCode_idx_bound len idx en ev hflc
  have hdidx := nativeFindDistCode_idx_bound dist dIdx den dev hfdc
  have hen := nativeFindLengthCode_extraN_bound len idx en ev hflc
  have hden := nativeFindDistCode_extraN_bound dist dIdx den dev hfdc
  have hl : idx + 257 < litCodes.size := by omega
  have hd : dIdx < distCodes.size := by omega
  have hlT : idx + 257 < (packCodeTab litCodes).size := by simpa using hl
  have hdT : dIdx < (packCodeTab distCodes).size := by simpa using hd
  have hei := codeIdx_lenCodeWord len idx en ev hflc
  have hee := codeExtra_lenCodeWord len idx en ev hflc
  have hcv := codeVal_lenCodeWord len idx en ev (by
    dsimp only [len]; exact lenField_lt w) hflc
  have hdi := codeIdx_distCodeWord dist dIdx den dev hfdc
  have hde := codeExtra_distCodeWord dist dIdx den dev hfdc
  have hdv := codeVal_distCodeWord dist dIdx den dev (by
    dsimp only [dist]; exact distField_lt w) hfdc
  have hllen := hlit_le (idx + 257) hl
  rw [getElem!_pos litCodes (idx + 257) hl] at hllen
  have hdlen := hdist_le dIdx hd
  rw [getElem!_pos distCodes dIdx hd] at hdlen
  have henNat : en.toUInt32.toNat = en := by
    simp only [Nat.toUInt32, UInt32.toNat_ofNat']
    rw [Nat.mod_eq_of_lt]
    omega
  have hdenNat : den.toUInt32.toNat = den := by
    simp only [Nat.toUInt32, UInt32.toNat_ofNat']
    rw [Nat.mod_eq_of_lt]
    omega
  have hlenMaskBound := uint64_and_lowMask_bound ev.toUInt64 en.toUInt32 (by
    rw [henNat]; omega)
  have hdistMaskBound := uint64_and_lowMask_bound dev.toUInt64 den.toUInt32 (by
    rw [hdenNat]; omega)
  let le := litCodes[idx + 257]'hl
  let de := distCodes[dIdx]'hd
  let lextra := ev.toUInt64 &&& ((1 <<< en.toUInt32.toUInt64) - 1)
  let dextra := dev.toUInt64 &&& ((1 <<< den.toUInt32.toUInt64) - 1)
  have hflat := writeBits64_ref_spec fbw le de lextra dextra en.toUInt32 den.toUInt32 hfwf
    (by simpa only [le] using hllen) (by simpa only [de] using hdlen)
    (by rw [henNat]; exact hen) (by rw [hdenNat]; exact hden)
    (by simpa only [lextra] using hlenMaskBound)
    (by simpa only [dextra] using hdistMaskBound)
  have hmaskBitsLen := writeBitsLSB_lowMask ev.toUInt64 en.toUInt32 (by
    rw [henNat]; omega)
  have hmaskBitsDist := writeBitsLSB_lowMask dev.toUInt64 den.toUInt32 (by
    rw [hdenNat]; omega)
  -- Keep the two mask equalities in the native `Nat` widths used by
  -- `writeBits`, so the final bit-list comparison is a direct rewrite.
  have hmaskBitsLen' :
      Deflate.Spec.writeBitsLSB en lextra.toNat =
        Deflate.Spec.writeBitsLSB en ev.toNat := by
    simpa only [lextra, henNat, UInt32.toNat_toUInt64] using hmaskBitsLen
  have hmaskBitsDist' :
      Deflate.Spec.writeBitsLSB den dextra.toNat =
        Deflate.Spec.writeBitsLSB den dev.toNat := by
    simpa only [dextra, hdenNat, UInt32.toNat_toUInt64] using hmaskBitsDist
  have hflatStep :
      emitRefWithCodesPTFlat fbw (packCodeTab litCodes) (packCodeTab distCodes) w =
        fbw.writeBits64
          ((le.2.toUInt32 + en.toUInt32) + de.2.toUInt32 + den.toUInt32)
          (((packCodeEntry le).toUInt16.toUInt64 |||
              (lextra <<< le.2.toUInt32.toUInt64)) |||
            (((packCodeEntry de).toUInt16.toUInt64 |||
              (dextra <<< de.2.toUInt32.toUInt64)) <<<
                (le.2.toUInt32 + en.toUInt32).toUInt64)) := by
    unfold emitRefWithCodesPTFlat
    simp only [len, dist, hei, hdi]
    rw [dif_pos hlT, dif_pos hdT]
    simp only [len, dist, packCodeTab, Array.getElem_map, flat_packCodeEntry_len32,
      flat_codeExtra32, hee, hde, hcv, hdv, le, de, lextra, dextra]
  have hrefStep :
      emitRefWithCodesPT rbw (packCodeTab litCodes) (packCodeTab distCodes) w =
        ((((rbw.writeHuffCode le.1 le.2).writeBits en ev).writeHuffCode de.1 de.2).writeBits
          den dev) := by
    rw [flat_emitRefWithCodesPT_eq]
    unfold emitRefWithCodesP
    simp only [len, dist, hei, hee, hcv, hdi, hde, hdv, hl, hd, dif_pos, le, de]
    congr
  have hw1 := BitWriter.writeHuffCode_wf rbw le.1 le.2 hrwf
    (by simpa only [le] using hllen)
  have hb1 := BitWriter.writeHuffCode_toBits rbw le.1 le.2 hrwf
    (by simpa only [le] using hllen)
  have hw2 := BitWriter.writeBits_wf _ en ev hw1 (by omega)
  have hb2 := BitWriter.writeBits_toBits _ en ev hw1 (by omega)
  have hw3 := BitWriter.writeHuffCode_wf _ de.1 de.2 hw2
    (by simpa only [de] using hdlen)
  have hb3 := BitWriter.writeHuffCode_toBits _ de.1 de.2 hw2
    (by simpa only [de] using hdlen)
  have hw4 := BitWriter.writeBits_wf _ den dev hw3 (by omega)
  have hb4 := BitWriter.writeBits_toBits _ den dev hw3 (by omega)
  rw [hflatStep, hrefStep]
  refine ⟨?_, hflat.2, hw4⟩
  rw [hflat.1, hb4, hb3, hb2, hb1]
  rw [hbits]
  simp only [henNat, hdenNat, lextra, dextra, UInt32.toNat_toUInt64,
    List.append_assoc]
  rw [hmaskBitsLen', hmaskBitsDist']

/-- The literal arm preserves observational equality between two writers. -/
private theorem emitLiteralFlatStep_spec (fbw rbw : BitWriter)
    (e : UInt16 × UInt8) (hbits : fbw.toBits = rbw.toBits)
    (hfwf : fbw.wf) (hrwf : rbw.wf) (hlen : e.2.toNat ≤ 15) :
    let fw := fbw.writeBits64 ((packCodeEntry e >>> 16) &&& 0xFF)
      (packCodeEntry e).toUInt16.toUInt64
    let rw := rbw.writeRevCode (packCodeEntry e).toUInt16
      (packCodeEntry e >>> 16).toUInt8
    fw.toBits = rw.toBits ∧ fw.wf ∧ rw.wf := by
  dsimp only
  rw [writeBits64_packCodeEntry_eq fbw e hfwf hlen,
    writeRevCode_packCodeEntry_eq rbw e]
  have hfb := BitWriter.writeHuffCode_toBits fbw e.1 e.2 hfwf hlen
  have hrb := BitWriter.writeHuffCode_toBits rbw e.1 e.2 hrwf hlen
  refine ⟨?_, BitWriter.writeHuffCode_wf fbw e.1 e.2 hfwf hlen,
    BitWriter.writeHuffCode_wf rbw e.1 e.2 hrwf hlen⟩
  rw [hfb, hrb, hbits]

/-- Reconstructing a writer after exposing the flat loop's scalar fields is
    identity; the count round-trip is `UInt8 → UInt32 → UInt8`. -/
private theorem flat_writer_reconstruct (bw : BitWriter) :
    (⟨bw.data, bw.bitBuf, bw.bitCount.toUInt32.toUInt8⟩ : BitWriter) = bw := by
  cases bw with
  | mk data bitBuf bitCount =>
    congr
    apply UInt8.toNat_inj.mp
    rw [UInt32.toNat_toUInt8, UInt8.toNat_toUInt32]
    exact Nat.mod_eq_of_lt bitCount.toNat_lt

/-- The complete flat token loop is observationally equal to the existing
    `TokenArray` packed-table loop when its tables are packed canonical entries
    of at most 15 bits.  The induction relation deliberately allows the two
    writers to have different data/pending splits. -/
private theorem emitTokensWithCodesTAPTFlatLoop_spec (fbw rbw : BitWriter)
    (tokens : TokenArray) (litCodes distCodes : Array (UInt16 × UInt8))
    (hlitT : (packCodeTab litCodes).size ≥ 286)
    (hdistT : (packCodeTab distCodes).size ≥ 30) (i : Nat)
    (hbits : fbw.toBits = rbw.toBits) (hfwf : fbw.wf) (hrwf : rbw.wf)
    (hlit_le : ∀ j, j < litCodes.size → litCodes[j]!.2.toNat ≤ 15)
    (hdist_le : ∀ j, j < distCodes.size → distCodes[j]!.2.toNat ≤ 15) :
    let fw := emitTokensWithCodesTAPTFlatLoop fbw.data fbw.bitBuf
      fbw.bitCount.toUInt32 tokens (packCodeTab litCodes) (packCodeTab distCodes)
      hlitT hdistT i
    let rw := emitTokensWithCodesTAPT rbw tokens
      (packCodeTab litCodes) (packCodeTab distCodes) hlitT hdistT i
    fw.toBits = rw.toBits ∧ fw.wf ∧ rw.wf := by
  dsimp only
  have hlit : litCodes.size ≥ 286 := by simpa using hlitT
  have hdist : distCodes.size ≥ 30 := by simpa using hdistT
  induction hrem : tokens.size - i using Nat.strongRecOn generalizing fbw rbw i with
  | _ n ih =>
    unfold emitTokensWithCodesTAPTFlatLoop emitTokensWithCodesTAPT
    by_cases hi : i < tokens.size
    · simp only [hi, dif_pos]
      let w := tokens.get i hi
      by_cases hc : w &&& ((1 : UInt32) <<< 31) = 0
      · simp only [w, hc, ↓reduceIte]
        have hj : w.toUInt8.toNat < litCodes.size := by
          have hj8 := UInt8.toNat_lt w.toUInt8
          omega
        have hlen := hlit_le w.toUInt8.toNat hj
        rw [getElem!_pos litCodes w.toUInt8.toNat hj] at hlen
        let e := litCodes[w.toUInt8.toNat]'hj
        let fw' := fbw.writeBits64 ((packCodeEntry e >>> 16) &&& 0xFF)
          (packCodeEntry e).toUInt16.toUInt64
        let rw' := rbw.writeRevCode (packCodeEntry e).toUInt16
          (packCodeEntry e >>> 16).toUInt8
        have hs := emitLiteralFlatStep_spec fbw rbw e hbits hfwf hrwf
          (by simpa only [e] using hlen)
        rw [flat_writer_reconstruct fbw]
        simp only [packCodeTab, Array.getElem_map]
        change
          let fwOut := emitTokensWithCodesTAPTFlatLoop fw'.data fw'.bitBuf
            fw'.bitCount.toUInt32 tokens (packCodeTab litCodes) (packCodeTab distCodes)
            hlitT hdistT (i + 1)
          let rwOut := emitTokensWithCodesTAPT rw' tokens
            (packCodeTab litCodes) (packCodeTab distCodes) hlitT hdistT (i + 1)
          fwOut.toBits = rwOut.toBits ∧ fwOut.wf ∧ rwOut.wf
        exact ih _ (by omega) fw' rw' (i + 1) hs.1 hs.2.1 hs.2.2 rfl
      · simp only [w, hc, ↓reduceIte]
        let fw' := emitRefWithCodesPTFlat fbw
          (packCodeTab litCodes) (packCodeTab distCodes) w
        let rw' := emitRefWithCodesPT rbw
          (packCodeTab litCodes) (packCodeTab distCodes) w
        have hs := emitRefWithCodesPTFlatStep_spec fbw rbw litCodes distCodes w
          hlit hdist hbits hfwf hrwf hlit_le hdist_le
        rw [flat_writer_reconstruct fbw]
        change
          let fwOut := emitTokensWithCodesTAPTFlatLoop fw'.data fw'.bitBuf
            fw'.bitCount.toUInt32 tokens (packCodeTab litCodes) (packCodeTab distCodes)
            hlitT hdistT (i + 1)
          let rwOut := emitTokensWithCodesTAPT rw' tokens
            (packCodeTab litCodes) (packCodeTab distCodes) hlitT hdistT (i + 1)
          fwOut.toBits = rwOut.toBits ∧ fwOut.wf ∧ rwOut.wf
        exact ih _ (by omega) fw' rw' (i + 1) hs.1 hs.2.1 hs.2.2 rfl
    · simp only [hi, dif_neg, flat_writer_reconstruct]
      exact ⟨hbits, hfwf, hrwf⟩

/-- Public observational contract for the flat emitter at canonical packed
    tables.  Structural equality is intentionally not claimed: the two loops
    may drain complete bytes at different token boundaries. -/
theorem emitTokensWithCodesTAPTFlat_spec (bw : BitWriter) (tokens : TokenArray)
    (litCodes distCodes : Array (UInt16 × UInt8))
    (hlitT : (packCodeTab litCodes).size ≥ 286)
    (hdistT : (packCodeTab distCodes).size ≥ 30) (i : Nat) (hwf : bw.wf)
    (hlit_le : ∀ j, j < litCodes.size → litCodes[j]!.2.toNat ≤ 15)
    (hdist_le : ∀ j, j < distCodes.size → distCodes[j]!.2.toNat ≤ 15) :
    let fw := emitTokensWithCodesTAPTFlat bw tokens
      (packCodeTab litCodes) (packCodeTab distCodes) hlitT hdistT i
    let rw := emitTokensWithCodesTAPT bw tokens
      (packCodeTab litCodes) (packCodeTab distCodes) hlitT hdistT i
    fw.toBits = rw.toBits ∧ fw.wf ∧ rw.wf := by
  dsimp only [emitTokensWithCodesTAPTFlat]
  exact emitTokensWithCodesTAPTFlatLoop_spec bw bw tokens litCodes distCodes
    hlitT hdistT i rfl hwf hwf hlit_le hdist_le

/-- Appending the same bounded Huffman field and flushing erases the internal
    byte-drain boundary difference between the flat and reference loops. -/
private theorem emitTokensWithCodesTAPTFlat_eob_flush_eq (bw : BitWriter)
    (tokens : TokenArray) (litCodes distCodes : Array (UInt16 × UInt8))
    (hlitT : (packCodeTab litCodes).size ≥ 286)
    (hdistT : (packCodeTab distCodes).size ≥ 30) (code : UInt16) (len : UInt8)
    (hwf : bw.wf)
    (hlit_le : ∀ j, j < litCodes.size → litCodes[j]!.2.toNat ≤ 15)
    (hdist_le : ∀ j, j < distCodes.size → distCodes[j]!.2.toNat ≤ 15)
    (hlen : len.toNat ≤ 15) :
    ((emitTokensWithCodesTAPTFlat bw tokens
        (packCodeTab litCodes) (packCodeTab distCodes) hlitT hdistT 0).writeHuffCode
      code len).flush =
    ((emitTokensWithCodesTAPT bw tokens
        (packCodeTab litCodes) (packCodeTab distCodes) hlitT hdistT 0).writeHuffCode
      code len).flush := by
  let fw := emitTokensWithCodesTAPTFlat bw tokens
    (packCodeTab litCodes) (packCodeTab distCodes) hlitT hdistT 0
  let rw := emitTokensWithCodesTAPT bw tokens
    (packCodeTab litCodes) (packCodeTab distCodes) hlitT hdistT 0
  obtain ⟨hbits, hfw, hrw⟩ := emitTokensWithCodesTAPTFlat_spec bw tokens
    litCodes distCodes hlitT hdistT 0 hwf hlit_le hdist_le
  apply BitWriter.flush_eq_of_toBits
  · exact BitWriter.writeHuffCode_wf fw code len hfw hlen
  · exact BitWriter.writeHuffCode_wf rw code len hrw hlen
  · rw [BitWriter.writeHuffCode_toBits fw code len hfw hlen,
      BitWriter.writeHuffCode_toBits rw code len hrw hlen, hbits]

/-- The proof-gated flat single-block production core is byte-identical to the
    reference packed core when supplied the canonical header plan.  Unlike the
    former broad `implemented_by`, this theorem records both the exact routed
    callsite and the code-length invariant that makes its 64-bit packing safe. -/
theorem deflateDynamicBlockCorePWithFlat_dynHeaderCodes (data : ByteArray)
    (tokens : TokenArray) (litLens distLens : List Nat)
    (hcl : (dynHeaderCodes litLens distLens).clCodes.size ≥ 19)
    (hlit : litLens.length = 286) (hdist : distLens.length = 30)
    (hlit_bound : ∀ x ∈ litLens, x ≤ 15)
    (hdist_bound : ∀ x ∈ distLens, x ≤ 15) (cap : Nat) :
    deflateDynamicBlockCorePWithFlat data tokens litLens distLens
        (dynHeaderCodes litLens distLens) hcl hlit hdist hlit_bound hdist_bound cap =
      deflateDynamicBlockCoreP data tokens litLens distLens hlit hdist := by
  let litCodes := canonicalCodes (litLens.toArray.map Nat.toUInt8)
  let distCodes := canonicalCodes (distLens.toArray.map Nat.toUInt8)
  have hlit_size : litCodes.size ≥ 286 := by
    simp only [litCodes, canonicalCodes_size, Array.size_map, List.size_toArray]
    omega
  have hdist_size : distCodes.size ≥ 30 := by
    simp only [distCodes, canonicalCodes_size, Array.size_map, List.size_toArray]
    omega
  have h256 : 256 < litCodes.size := by omega
  have hlitT_size : (packCodeTab litCodes).size ≥ 286 := by
    rw [packCodeTab_size]
    exact hlit_size
  have hdistT_size : (packCodeTab distCodes).size ≥ 30 := by
    rw [packCodeTab_size]
    exact hdist_size
  have hlit_arr_le := Deflate.toUInt8Array_le litLens hlit_bound
  have hdist_arr_le := Deflate.toUInt8Array_le distLens hdist_bound
  have hlit_le : ∀ j, j < litCodes.size → litCodes[j]!.2.toNat ≤ 15 := by
    intro j hj
    exact canonicalCodes_snd_le _ 15 hlit_arr_le j hj
  have hdist_le : ∀ j, j < distCodes.size → distCodes[j]!.2.toNat ≤ 15 := by
    intro j hj
    exact canonicalCodes_snd_le _ 15 hdist_arr_le j hj
  have heob_len : (litCodes[256]'h256).2.toNat ≤ 15 := by
    have h := hlit_le 256 h256
    rwa [getElem!_pos litCodes 256 h256] at h
  have hwf1 := BitWriter.writeBits_wf BitWriter.empty 1 1 BitWriter.empty_wf (by omega)
  have hwf2 := BitWriter.writeBits_wf (BitWriter.empty.writeBits 1 1) 2 2 hwf1 (by omega)
  have hwf_header := writeDynamicHeader_wf
    ((BitWriter.empty.writeBits 1 1).writeBits 2 2) litLens distLens hwf2
      hlit_bound hdist_bound
  unfold deflateDynamicBlockCorePWithFlat deflateDynamicBlockCoreP
  simp only [BitWriter.emptyWithCapacity_eq, writeDynamicHeaderWith_dynHeaderCodes]
  by_cases hempty : data.size == 0
  · simp only [hempty, ↓reduceIte]
  · simp only [hempty, ↓reduceIte]
    have hflat := emitTokensWithCodesTAPTFlat_eob_flush_eq
      (writeDynamicHeader ((BitWriter.empty.writeBits 1 1).writeBits 2 2) litLens distLens)
      tokens litCodes distCodes hlitT_size hdistT_size
      (litCodes[256]'h256).1 (litCodes[256]'h256).2 hwf_header hlit_le hdist_le heob_len
    exact hflat.symm.trans hflat

end Zip.Native.Deflate
