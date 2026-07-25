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

/-- Read a list-wide upper bound at a valid panic-indexed position. -/
private theorem flat_getElem!_le_of_forall_mem_le (l : List Nat) (i n : Nat)
    (hi : i < l.length) (h : ∀ x ∈ l, x ≤ n) : l[i]! ≤ n := by
  rw [getElem!_pos l i hi]
  exact h _ (List.getElem_mem hi)

/-- The dynamic-tree header encoder succeeds for the exact alphabet shapes
    used by native block emission when every input length obeys the RFC bound.
    This fact lets the writer proof use the public `writeDynamicHeader_spec`
    without tying it to one particular frequency computation. -/
private theorem encodeDynamicTrees_isSome_of_bounded
    (litLens distLens : List Nat)
    (hlit_len : litLens.length = 286) (hdist_len : distLens.length = 30)
    (hlit_bound : ∀ x ∈ litLens, x ≤ 15)
    (hdist_bound : ∀ x ∈ distLens, x ≤ 15) :
    (Deflate.Spec.encodeDynamicTrees litLens distLens).isSome = true := by
  simp only [Deflate.Spec.encodeDynamicTrees]
  simp only [guard,
    show litLens.length ≥ 257 ∧ litLens.length ≤ 288 from ⟨by omega, by omega⟩,
    show distLens.length ≥ 1 ∧ distLens.length ≤ 32 from ⟨by omega, by omega⟩,
    pure, Pure.pure, bind, Option.bind]
  let allLens := litLens ++ distLens
  let clEntries := Deflate.Spec.rlEncodeLengths allLens
  let clFreqs := Deflate.Spec.clSymbolFreqs clEntries
  let clFreqPairs :=
    (List.range clFreqs.length).map fun i => (i, clFreqs.getD i 0)
  let clLens := Huffman.Spec.computeCodeLengths clFreqPairs 19 7
  have hcl_len : clLens.length = 19 :=
    Huffman.Spec.computeCodeLengths_length clFreqPairs 19 7
  have hcl_bound : ∀ x ∈ clLens, x ≤ 7 :=
    Huffman.Spec.computeCodeLengths_bounded clFreqPairs 19 7 (by omega)
  have hentry_valid := Deflate.Spec.rlEncodeLengths_valid allLens (by
    intro x hx
    simp only [allLens, List.mem_append] at hx
    cases hx with
    | inl h => exact hlit_bound x h
    | inr h => exact hdist_bound x h)
  have hall : ∀ p ∈ clEntries,
      p.1 < clLens.length ∧ clLens[p.1]! ≠ 0 ∧ clLens[p.1]! ≤ 7 := by
    intro ⟨code, extra⟩ hp
    have hvalid := hentry_valid (code, extra) hp
    have hcode_lt : code < 19 := by
      rcases hvalid with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> omega
    refine ⟨by omega, ?_, ?_⟩
    · have hfreq_pos :=
        Deflate.Spec.clSymbolFreqs_pos clEntries code extra hp hcode_lt
      have hfreq_in : ∃ p ∈ clFreqPairs, p.1 = code ∧ p.2 > 0 := by
        refine ⟨(code, clFreqs.getD code 0), ?_, rfl, hfreq_pos⟩
        simp only [clFreqPairs, List.mem_map, List.mem_range]
        exact ⟨code, by
          rw [Deflate.Spec.clSymbolFreqs_length]
          omega, rfl⟩
      exact Huffman.Spec.computeCodeLengths_nonzero clFreqPairs 19 7 (by omega)
        code (by omega) hfreq_in
    · exact flat_getElem!_le_of_forall_mem_le clLens code 7 (by omega) hcl_bound
  have hsome := Deflate.Spec.encodeCLEntries_isSome clLens 7 clEntries hall
  change (Deflate.Spec.encodeCLEntries
    ((Huffman.Spec.allCodes clLens 7).map fun p => (p.2, p.1))
    clEntries).isSome = true at hsome
  cases hcl : Deflate.Spec.encodeCLEntries
      ((Huffman.Spec.allCodes clLens 7).map fun p => (p.2, p.1))
      clEntries with
  | none => exact nomatch hcl ▸ hsome
  | some _ => rfl

/-- `writeDynamicHeader` respects observational writer equality. -/
private theorem writeDynamicHeader_congr (fbw rbw : BitWriter)
    (litLens distLens : List Nat)
    (hlit_len : litLens.length = 286) (hdist_len : distLens.length = 30)
    (hbits : fbw.toBits = rbw.toBits) (hfwf : fbw.wf) (hrwf : rbw.wf)
    (hlit_bound : ∀ x ∈ litLens, x ≤ 15)
    (hdist_bound : ∀ x ∈ distLens, x ≤ 15) :
    let fw := writeDynamicHeader fbw litLens distLens
    let rw := writeDynamicHeader rbw litLens distLens
    fw.toBits = rw.toBits ∧ fw.wf ∧ rw.wf := by
  have hsome := encodeDynamicTrees_isSome_of_bounded litLens distLens
    hlit_len hdist_len hlit_bound hdist_bound
  cases henc : Deflate.Spec.encodeDynamicTrees litLens distLens with
  | none => exact nomatch henc ▸ hsome
  | some headerBits =>
    have hf := writeDynamicHeader_spec fbw litLens distLens headerBits hfwf
      hlit_bound hdist_bound ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ henc
    have hr := writeDynamicHeader_spec rbw litLens distLens headerBits hrwf
      hlit_bound hdist_bound ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ henc
    refine ⟨?_,
      writeDynamicHeader_wf fbw litLens distLens hfwf hlit_bound hdist_bound,
      writeDynamicHeader_wf rbw litLens distLens hrwf hlit_bound hdist_bound⟩
    rw [hf, hr, hbits]

/-- `writeBits` respects observational writer equality. -/
private theorem writeBits_congr (fbw rbw : BitWriter) (n : Nat) (val : UInt32)
    (hbits : fbw.toBits = rbw.toBits) (hfwf : fbw.wf) (hrwf : rbw.wf)
    (hn : n ≤ 25) :
    let fw := fbw.writeBits n val
    let rw := rbw.writeBits n val
    fw.toBits = rw.toBits ∧ fw.wf ∧ rw.wf := by
  have hf := BitWriter.writeBits_toBits fbw n val hfwf hn
  have hr := BitWriter.writeBits_toBits rbw n val hrwf hn
  refine ⟨?_, BitWriter.writeBits_wf fbw n val hfwf hn,
    BitWriter.writeBits_wf rbw n val hrwf hn⟩
  rw [hf, hr, hbits]

/-- `writeHuffCode` respects observational writer equality. -/
private theorem writeHuffCode_congr (fbw rbw : BitWriter)
    (code : UInt16) (len : UInt8)
    (hbits : fbw.toBits = rbw.toBits) (hfwf : fbw.wf) (hrwf : rbw.wf)
    (hlen : len.toNat ≤ 15) :
    let fw := fbw.writeHuffCode code len
    let rw := rbw.writeHuffCode code len
    fw.toBits = rw.toBits ∧ fw.wf ∧ rw.wf := by
  have hf := BitWriter.writeHuffCode_toBits fbw code len hfwf hlen
  have hr := BitWriter.writeHuffCode_toBits rbw code len hrwf hlen
  refine ⟨?_, BitWriter.writeHuffCode_wf fbw code len hfwf hlen,
    BitWriter.writeHuffCode_wf rbw code len hrwf hlen⟩
  rw [hf, hr, hbits]

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

/-- Proof model of the scalar write transition used by the production loop.
    It differs from `writeBits64` only by spelling the known-small byte drops
    as direct shifts. -/
private def flatWriteBits64Fast (bw : BitWriter) (n : UInt32) (val : UInt64) : BitWriter :=
  let bc := bw.bitCount.toUInt32
  if bc + n ≥ 64 then
    let k0 := bc >>> 3
    let data0 := BitWriter.flushBytesWideU bw.data bw.bitBuf k0
    let acc0 := bw.bitBuf >>> (k0.toUInt64 <<< 3)
    let bc0 := bc &&& 7
    let acc' := acc0 ||| (val <<< bc0.toUInt64)
    let total := bc0 + n
    if total ≥ 32 then
      let k := total >>> 3
      ⟨BitWriter.flushBytesWideU data0 acc' k,
        acc' >>> (k.toUInt64 <<< 3), (total &&& 7).toUInt8⟩
    else
      ⟨data0, acc', total.toUInt8⟩
  else
    let acc' := bw.bitBuf ||| (val <<< bc.toUInt64)
    let total := bc + n
    if total ≥ 32 then
      let k := total >>> 3
      ⟨BitWriter.flushBytesWideU bw.data acc' k,
        acc' >>> (k.toUInt64 <<< 3), (total &&& 7).toUInt8⟩
    else
      ⟨bw.data, acc', total.toUInt8⟩

/-- Under the emitter's width invariant, the hand-expanded scalar transition
    is structurally the proven `writeBits64` primitive. -/
private theorem flatWriteBits64Fast_eq (bw : BitWriter) (n : UInt32) (val : UInt64)
    (hwf : bw.wf) (hn : n.toNat ≤ 48) :
    flatWriteBits64Fast bw n val = bw.writeBits64 n val := by
  have hbc : bw.bitCount.toNat < 32 := hwf.1
  have hbc32 : bw.bitCount.toUInt32.toNat = bw.bitCount.toNat :=
    UInt8.toNat_toUInt32 _
  unfold flatWriteBits64Fast BitWriter.writeBits64
  by_cases hpre : bw.bitCount.toUInt32 + n ≥ (64 : UInt32)
  · rw [if_pos hpre, if_pos hpre]
    unfold BitWriter.drainPendingBytes BitWriter.writeBits64Small
    dsimp only
    have hk0 : bw.bitCount.toUInt32 >>> 3 < (8 : UInt32) := by
      apply UInt32.lt_iff_toNat_lt.mpr
      rw [UInt32.toNat_shiftRight, hbc32]
      have h3 : (3 : UInt32).toNat = 3 := rfl
      rw [h3, Nat.mod_eq_of_lt (by omega : (3 : Nat) < 32),
        Nat.shiftRight_eq_div_pow]
      simp only [Nat.reducePow, UInt32.reduceToNat]
      omega
    rw [show BitWriter.dropBytesU bw.bitBuf (bw.bitCount.toUInt32 >>> 3) =
        bw.bitBuf >>> ((bw.bitCount.toUInt32 >>> 3).toUInt64 <<< 3) by
      simp only [BitWriter.dropBytesU, if_pos hk0]]
    let bc0 := bw.bitCount.toUInt32 &&& 7
    have hbc0 : bc0.toNat ≤ 7 := by
      dsimp only [bc0]
      rw [UInt32.toNat_and]
      exact Nat.le_trans Nat.and_le_right (by decide)
    have hbc0cast32 : bc0.toUInt8.toUInt32 = bc0 := by
      apply UInt32.toNat_inj.mp
      rw [UInt8.toNat_toUInt32, UInt32.toNat_toUInt8, Nat.mod_eq_of_lt]
      omega
    have hbc0cast64 : bc0.toUInt8.toUInt64 = bc0.toUInt64 := by
      apply UInt64.toNat_inj.mp
      rw [UInt8.toNat_toUInt64, UInt32.toNat_toUInt64,
        UInt32.toNat_toUInt8, Nat.mod_eq_of_lt]
      omega
    rw [hbc0cast32, hbc0cast64]
    have htotal : (bc0 + n).toNat = bc0.toNat + n.toNat := by
      rw [UInt32.toNat_add, Nat.mod_eq_of_lt]
      omega
    by_cases hflush : bc0 + n ≥ (32 : UInt32)
    · rw [if_pos hflush, if_pos hflush]
      have hk : (bc0 + n) >>> 3 < (8 : UInt32) := by
        apply UInt32.lt_iff_toNat_lt.mpr
        rw [UInt32.toNat_shiftRight, htotal]
        have h3 : (3 : UInt32).toNat = 3 := rfl
        rw [h3, Nat.mod_eq_of_lt (by omega : (3 : Nat) < 32),
          Nat.shiftRight_eq_div_pow]
        simp only [Nat.reducePow, UInt32.reduceToNat]
        omega
      rw [show BitWriter.dropBytesU
          ((bw.bitBuf >>> ((bw.bitCount.toUInt32 >>> 3).toUInt64 <<< 3)) |||
            (val <<< bc0.toUInt64)) ((bc0 + n) >>> 3) =
          ((bw.bitBuf >>> ((bw.bitCount.toUInt32 >>> 3).toUInt64 <<< 3)) |||
            (val <<< bc0.toUInt64)) >>> (((bc0 + n) >>> 3).toUInt64 <<< 3) by
        simp only [BitWriter.dropBytesU, if_pos hk]]
    · rw [if_neg hflush, if_neg hflush]

  · rw [if_neg hpre, if_neg hpre]
    unfold BitWriter.writeBits64Small
    dsimp only
    have hbc64 : bw.bitCount.toUInt32.toUInt64 = bw.bitCount.toUInt64 := by
      apply UInt64.toNat_inj.mp
      rw [UInt32.toNat_toUInt64, UInt8.toNat_toUInt32, UInt8.toNat_toUInt64]
    rw [hbc64]
    have htotal : (bw.bitCount.toUInt32 + n).toNat =
        bw.bitCount.toNat + n.toNat := by
      rw [UInt32.toNat_add, hbc32, Nat.mod_eq_of_lt]
      omega
    by_cases hflush : bw.bitCount.toUInt32 + n ≥ (32 : UInt32)
    · rw [if_pos hflush, if_pos hflush]
      have hk : (bw.bitCount.toUInt32 + n) >>> 3 < (8 : UInt32) := by
        apply UInt32.lt_iff_toNat_lt.mpr
        rw [UInt32.toNat_shiftRight, htotal]
        have h3 : (3 : UInt32).toNat = 3 := rfl
        rw [h3, Nat.mod_eq_of_lt (by omega : (3 : Nat) < 32),
          Nat.shiftRight_eq_div_pow]
        simp only [Nat.reducePow, UInt32.reduceToNat]
        have hlt : (bw.bitCount.toUInt32 + n).toNat < (64 : UInt32).toNat := by
          apply Nat.lt_of_not_ge
          intro hge
          exact hpre (UInt32.le_iff_toNat_le.mpr hge)
        simp only [UInt32.reduceToNat] at hlt
        omega
      rw [show BitWriter.dropBytesU
          (bw.bitBuf ||| (val <<< bw.bitCount.toUInt64))
            ((bw.bitCount.toUInt32 + n) >>> 3) =
          (bw.bitBuf ||| (val <<< bw.bitCount.toUInt64)) >>>
            (((bw.bitCount.toUInt32 + n) >>> 3).toUInt64 <<< 3) by
        simp only [BitWriter.dropBytesU, if_pos hk]]
    · rw [if_neg hflush, if_neg hflush]

/-- No-pre-drain scalar transition used for a literal, whose at-most-15-bit
    code cannot approach bit 64 from a well-formed pending state. -/
private def flatWriteBits64FastLiteral (bw : BitWriter)
    (n : UInt32) (val : UInt64) : BitWriter :=
  let acc' := bw.bitBuf ||| (val <<< bw.bitCount.toUInt32.toUInt64)
  let total := bw.bitCount.toUInt32 + n
  if total ≥ 32 then
    let k := total >>> 3
    ⟨BitWriter.flushBytesWideU bw.data acc' k,
      acc' >>> (k.toUInt64 <<< 3), (total &&& 7).toUInt8⟩
  else
    ⟨bw.data, acc', total.toUInt8⟩

private theorem flatWriteBits64FastLiteral_eq (bw : BitWriter)
    (n : UInt32) (val : UInt64) (hwf : bw.wf) (hn : n.toNat ≤ 15) :
    flatWriteBits64FastLiteral bw n val = bw.writeBits64 n val := by
  have hbc := hwf.1
  have htotal : (bw.bitCount.toUInt32 + n).toNat =
      bw.bitCount.toNat + n.toNat := by
    rw [UInt32.toNat_add, UInt8.toNat_toUInt32, Nat.mod_eq_of_lt]
    omega
  have hpre : ¬bw.bitCount.toUInt32 + n ≥ (64 : UInt32) := by
    intro hge
    have hgeN := UInt32.le_iff_toNat_le.mp hge
    rw [htotal, show (64 : UInt32).toNat = 64 by decide] at hgeN
    omega
  calc
    flatWriteBits64FastLiteral bw n val = flatWriteBits64Fast bw n val := by
      unfold flatWriteBits64FastLiteral flatWriteBits64Fast
      rw [if_neg hpre]
    _ = bw.writeBits64 n val := flatWriteBits64Fast_eq bw n val hwf (by omega)

/-- The production reference arm flattens the distance-code and distance-extra
    shifts.  Below bit 64 this is the same packed word as shifting their
    already-concatenated field. -/
private theorem flat_ref_bits_reassoc (a b c : UInt64) (n m : UInt32)
    (h : n.toUInt64 + m.toUInt64 < (64 : UInt64)) :
    a ||| (b <<< n.toUInt64) ||| (c <<< (n.toUInt64 + m.toUInt64)) =
      a ||| ((b ||| (c <<< m.toUInt64)) <<< n.toUInt64) := by
  bv_decide

/-- One reference-token step in the exact scalar form used by the production
    loop, packaged as a writer transition for the induction proof. -/
private def emitRefWithCodesPTFlatFast (bw : BitWriter)
    (litT distT : Array UInt32) (w : UInt32) : BitWriter :=
  let lw := lenCodeWord (((w >>> 16) &&& 0x7FFF).toNat)
  let idx := codeIdx lw
  if hlitlt : idx + 257 < litT.size then
    let e := litT[idx + 257]
    let lenN : UInt32 := (e >>> 16) &&& 0xFF
    let lenExtraN : UInt32 := (lw >>> 8) &&& 0xFF
    let lenMask : UInt64 := (1 <<< lenExtraN.toUInt64) - 1
    let lenBits : UInt64 := e.toUInt16.toUInt64 |||
      (((codeVal lw).toUInt64 &&& lenMask) <<< lenN.toUInt64)
    let lenTotal := lenN + lenExtraN
    let dw := distCodeWord ((w &&& 0xFFFF).toNat)
    let dIdx := codeIdx dw
    if hdistlt : dIdx < distT.size then
      let de := distT[dIdx]
      let distN : UInt32 := (de >>> 16) &&& 0xFF
      let distExtraN : UInt32 := (dw >>> 8) &&& 0xFF
      let distMask : UInt64 := (1 <<< distExtraN.toUInt64) - 1
      let bits : UInt64 :=
        lenBits ||| (de.toUInt16.toUInt64 <<< lenTotal.toUInt64) |||
          (((codeVal dw).toUInt64 &&& distMask) <<<
            (lenTotal.toUInt64 + distN.toUInt64))
      flatWriteBits64Fast bw (lenTotal + distN + distExtraN) bits
    else
      flatWriteBits64FastLiteral bw lenTotal lenBits
  else bw

/-- For canonical bounded code tables, the production scalar reference step
    is structurally the factored flat reference step. -/
private theorem emitRefWithCodesPTFlatFast_eq (bw : BitWriter)
    (litCodes distCodes : Array (UInt16 × UInt8)) (w : UInt32)
    (hlit : litCodes.size ≥ 286) (hdist : distCodes.size ≥ 30)
    (hwf : bw.wf)
    (hlit_le : ∀ j, j < litCodes.size → litCodes[j]!.2.toNat ≤ 15)
    (hdist_le : ∀ j, j < distCodes.size → distCodes[j]!.2.toNat ≤ 15) :
    emitRefWithCodesPTFlatFast bw (packCodeTab litCodes) (packCodeTab distCodes) w =
      emitRefWithCodesPTFlat bw (packCodeTab litCodes) (packCodeTab distCodes) w := by
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
  let le := litCodes[idx + 257]'hl
  let de := distCodes[dIdx]'hd
  have hll : le.2.toNat ≤ 15 := by simpa only [le] using hllen
  have hdl : de.2.toNat ≤ 15 := by simpa only [de] using hdlen
  let lenTotal := le.2.toUInt32 + en.toUInt32
  have hlenTotal : lenTotal.toNat = le.2.toNat + en := by
    dsimp only [lenTotal]
    rw [uint32_add_toNat _ _ (by rw [UInt8.toNat_toUInt32, henNat]; omega),
      UInt8.toNat_toUInt32, henNat]
  have hmid : (lenTotal + de.2.toUInt32).toNat =
      lenTotal.toNat + de.2.toNat := by
    rw [uint32_add_toNat _ _ (by rw [UInt8.toNat_toUInt32, hlenTotal]; omega),
      UInt8.toNat_toUInt32]
  have hn : (lenTotal + de.2.toUInt32 + den.toUInt32).toNat ≤ 48 := by
    rw [uint32_add_toNat _ _ (by rw [hmid, hlenTotal, hdenNat]; omega),
      hmid, hlenTotal, hdenNat]
    omega
  have hshift : lenTotal.toUInt64 + de.2.toUInt32.toUInt64 < (64 : UInt64) := by
    apply UInt64.lt_iff_toNat_lt.mpr
    rw [UInt64.toNat_add, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64,
      Nat.mod_eq_of_lt (by rw [hlenTotal, UInt8.toNat_toUInt32]; omega),
      show (64 : UInt64).toNat = 64 by decide, hlenTotal, UInt8.toNat_toUInt32]
    omega
  unfold emitRefWithCodesPTFlatFast emitRefWithCodesPTFlat
  simp only [len, dist, hei, hdi]
  rw [dif_pos hlT, dif_pos hdT, dif_pos hlT, dif_pos hdT]
  simp only [len, dist, packCodeTab, Array.getElem_map, flat_packCodeEntry_len32,
    flat_codeExtra32, hee, hde, hcv, hdv, le, de, lenTotal]
  rw [flat_ref_bits_reassoc _ _ _ _ _ hshift]
  exact flatWriteBits64Fast_eq bw _ _ hwf (by simpa only [lenTotal] using hn)

/-- One token step, in the exact writer-valued form represented by the scalar
    production loop after its fields are regrouped. -/
private def emitTokenWithCodesPTFlatFast (bw : BitWriter) (w : UInt32)
    (litT distT : Array UInt32)
    (hlit : litT.size ≥ 286) (hdist : distT.size ≥ 30) : BitWriter :=
  if w &&& ((1 : UInt32) <<< 31) = 0 then
    have he : w.toUInt8.toNat < litT.size := by
      have := UInt8.toNat_lt w.toUInt8
      omega
    let e := litT[w.toUInt8.toNat]
    flatWriteBits64FastLiteral bw ((e >>> 16) &&& 0xFF) e.toUInt16.toUInt64
  else
    emitRefWithCodesPTFlatFast bw litT distT w

/-- Matching writer-valued step in the factored proof loop. -/
private def emitTokenWithCodesPTFlatFactored (bw : BitWriter) (w : UInt32)
    (litT distT : Array UInt32)
    (hlit : litT.size ≥ 286) (hdist : distT.size ≥ 30) : BitWriter :=
  if w &&& ((1 : UInt32) <<< 31) = 0 then
    have he : w.toUInt8.toNat < litT.size := by
      have := UInt8.toNat_lt w.toUInt8
      omega
    let e := litT[w.toUInt8.toNat]
    bw.writeBits64 ((e >>> 16) &&& 0xFF) e.toUInt16.toUInt64
  else
    emitRefWithCodesPTFlat bw litT distT w

private theorem emitTokenWithCodesPTFlatFast_eq (bw : BitWriter) (w : UInt32)
    (litCodes distCodes : Array (UInt16 × UInt8))
    (hlitT : (packCodeTab litCodes).size ≥ 286)
    (hdistT : (packCodeTab distCodes).size ≥ 30) (hwf : bw.wf)
    (hlit_le : ∀ j, j < litCodes.size → litCodes[j]!.2.toNat ≤ 15)
    (hdist_le : ∀ j, j < distCodes.size → distCodes[j]!.2.toNat ≤ 15) :
    emitTokenWithCodesPTFlatFast bw w (packCodeTab litCodes) (packCodeTab distCodes)
        hlitT hdistT =
      emitTokenWithCodesPTFlatFactored bw w (packCodeTab litCodes) (packCodeTab distCodes)
        hlitT hdistT := by
  have hlit : litCodes.size ≥ 286 := by simpa using hlitT
  have hdist : distCodes.size ≥ 30 := by simpa using hdistT
  unfold emitTokenWithCodesPTFlatFast emitTokenWithCodesPTFlatFactored
  by_cases hc : w &&& ((1 : UInt32) <<< 31) = 0
  · simp only [hc, ↓reduceIte]
    have hj : w.toUInt8.toNat < litCodes.size := by
      have hj8 := UInt8.toNat_lt w.toUInt8
      omega
    have hlen := hlit_le w.toUInt8.toNat hj
    rw [getElem!_pos litCodes w.toUInt8.toNat hj] at hlen
    simp only [packCodeTab, Array.getElem_map]
    exact flatWriteBits64FastLiteral_eq bw _ _ hwf
      (by simpa only [flat_packCodeEntry_len] using hlen)
  · simp only [hc, ↓reduceIte]
    exact emitRefWithCodesPTFlatFast_eq bw litCodes distCodes w hlit hdist hwf
      hlit_le hdist_le

private theorem emitTokenWithCodesPTFlatFactored_wf (bw : BitWriter) (w : UInt32)
    (litCodes distCodes : Array (UInt16 × UInt8))
    (hlitT : (packCodeTab litCodes).size ≥ 286)
    (hdistT : (packCodeTab distCodes).size ≥ 30) (hwf : bw.wf)
    (hlit_le : ∀ j, j < litCodes.size → litCodes[j]!.2.toNat ≤ 15)
    (hdist_le : ∀ j, j < distCodes.size → distCodes[j]!.2.toNat ≤ 15) :
    (emitTokenWithCodesPTFlatFactored bw w (packCodeTab litCodes)
      (packCodeTab distCodes) hlitT hdistT).wf := by
  have hlit : litCodes.size ≥ 286 := by simpa using hlitT
  have hdist : distCodes.size ≥ 30 := by simpa using hdistT
  unfold emitTokenWithCodesPTFlatFactored
  by_cases hc : w &&& ((1 : UInt32) <<< 31) = 0
  · simp only [hc, ↓reduceIte]
    have hj : w.toUInt8.toNat < litCodes.size := by
      have hj8 := UInt8.toNat_lt w.toUInt8
      omega
    have hlen := hlit_le w.toUInt8.toNat hj
    rw [getElem!_pos litCodes w.toUInt8.toNat hj] at hlen
    simp only [packCodeTab, Array.getElem_map]
    apply BitWriter.writeBits64_wf
    · exact hwf
    · rw [flat_packCodeEntry_len]
      omega
    · simpa only [flat_packCodeEntry_len] using
        (flat_packCodeEntry_bound _ (by simpa using hlen))
  · simp only [hc, ↓reduceIte]
    exact (emitRefWithCodesPTFlatStep_spec bw bw litCodes distCodes w hlit hdist
      rfl hwf hwf hlit_le hdist_le).2.1

/-- Regrouping a scalar step as a writer moves its branch outside the recursive
    continuation.  These two normalization lemmas bridge that harmless shape
    difference in the optimized-loop induction. -/
private theorem emitTokensWithCodesTAPTFlatFastLoop_ite (p : Prop) [Decidable p]
    (a b : BitWriter) (tokens : TokenArray) (litT distT : Array UInt32)
    (hlit : litT.size ≥ 286) (hdist : distT.size ≥ 30) (i : Nat) :
    emitTokensWithCodesTAPTFlatFastLoop (if p then a else b).data
        (if p then a else b).bitBuf (if p then a else b).bitCount.toUInt32
        tokens litT distT hlit hdist i =
      if p then
        emitTokensWithCodesTAPTFlatFastLoop a.data a.bitBuf a.bitCount.toUInt32
          tokens litT distT hlit hdist i
      else
        emitTokensWithCodesTAPTFlatFastLoop b.data b.bitBuf b.bitCount.toUInt32
          tokens litT distT hlit hdist i := by
  by_cases h : p <;> simp [h]

private theorem emitTokensWithCodesTAPTFlatFastLoop_dite (p : Prop) [Decidable p]
    (a : p → BitWriter) (b : ¬p → BitWriter)
    (tokens : TokenArray) (litT distT : Array UInt32)
    (hlit : litT.size ≥ 286) (hdist : distT.size ≥ 30) (i : Nat) :
    emitTokensWithCodesTAPTFlatFastLoop (if h : p then a h else b h).data
        (if h : p then a h else b h).bitBuf
        (if h : p then a h else b h).bitCount.toUInt32
        tokens litT distT hlit hdist i =
      if h : p then
        emitTokensWithCodesTAPTFlatFastLoop (a h).data (a h).bitBuf
          (a h).bitCount.toUInt32 tokens litT distT hlit hdist i
      else
        emitTokensWithCodesTAPTFlatFastLoop (b h).data (b h).bitBuf
          (b h).bitCount.toUInt32 tokens litT distT hlit hdist i := by
  by_cases h : p <;> simp [h]

/-- The optimized scalar loop is structurally the factored flat loop for the
    canonical bounded tables used by production. -/
theorem emitTokensWithCodesTAPTFlatFastLoop_eq (bw : BitWriter)
    (tokens : TokenArray) (litCodes distCodes : Array (UInt16 × UInt8))
    (hlitT : (packCodeTab litCodes).size ≥ 286)
    (hdistT : (packCodeTab distCodes).size ≥ 30) (i : Nat) (hwf : bw.wf)
    (hlit_le : ∀ j, j < litCodes.size → litCodes[j]!.2.toNat ≤ 15)
    (hdist_le : ∀ j, j < distCodes.size → distCodes[j]!.2.toNat ≤ 15) :
    emitTokensWithCodesTAPTFlatFastLoop bw.data bw.bitBuf bw.bitCount.toUInt32
        tokens (packCodeTab litCodes) (packCodeTab distCodes) hlitT hdistT i =
      emitTokensWithCodesTAPTFlatLoop bw.data bw.bitBuf bw.bitCount.toUInt32
        tokens (packCodeTab litCodes) (packCodeTab distCodes) hlitT hdistT i := by
  induction hrem : tokens.size - i using Nat.strongRecOn generalizing bw i with
  | _ n ih =>
    unfold emitTokensWithCodesTAPTFlatFastLoop emitTokensWithCodesTAPTFlatLoop
    by_cases hi : i < tokens.size
    · simp only [hi, dif_pos]
      let w := tokens.get i hi
      by_cases hc : w &&& ((1 : UInt32) <<< 31) = 0
      · simp only [w, hc, ↓reduceIte]
        rw [flat_writer_reconstruct bw]
        have hj : w.toUInt8.toNat < litCodes.size := by
          have hj8 := UInt8.toNat_lt w.toUInt8
          have hlit : litCodes.size ≥ 286 := by simpa using hlitT
          omega
        have hlen := hlit_le w.toUInt8.toNat hj
        rw [getElem!_pos litCodes w.toUInt8.toNat hj] at hlen
        let e := (packCodeTab litCodes)[w.toUInt8.toNat]'(by simpa using hj)
        let rw' := bw.writeBits64 ((e >>> 16) &&& 0xFF) e.toUInt16.toUInt64
        have heq := flatWriteBits64FastLiteral_eq bw
          ((e >>> 16) &&& 0xFF) e.toUInt16.toUInt64 hwf (by
            simpa only [e, packCodeTab, Array.getElem_map, flat_packCodeEntry_len]
              using hlen)
        have hw' := BitWriter.writeBits64_wf bw
          ((e >>> 16) &&& 0xFF) e.toUInt16.toUInt64 hwf
          (by
            have ht : ((e >>> 16) &&& 0xFF).toNat ≤ 15 := by
              simpa only [e, packCodeTab, Array.getElem_map, flat_packCodeEntry_len]
                using hlen
            omega)
          (by simpa only [e, packCodeTab, Array.getElem_map, flat_packCodeEntry_len]
            using (flat_packCodeEntry_bound
              (litCodes[w.toUInt8.toNat]'hj) (by simpa using hlen)))
        have hind := ih _ (by omega) rw' (i + 1) hw' rfl
        have hcont := congrArg (fun fw =>
          emitTokensWithCodesTAPTFlatFastLoop fw.data fw.bitBuf fw.bitCount.toUInt32
            tokens (packCodeTab litCodes) (packCodeTab distCodes) hlitT hdistT (i + 1)) heq
        simpa only [w, e, rw', flatWriteBits64FastLiteral,
          emitTokensWithCodesTAPTFlatFastLoop_ite] using hcont.trans hind
      · simp only [w, hc, ↓reduceIte]
        rw [flat_writer_reconstruct bw]
        let rw' := emitRefWithCodesPTFlat bw
          (packCodeTab litCodes) (packCodeTab distCodes) w
        have hlit : litCodes.size ≥ 286 := by simpa using hlitT
        have hdist : distCodes.size ≥ 30 := by simpa using hdistT
        have heq := emitRefWithCodesPTFlatFast_eq bw litCodes distCodes w
          hlit hdist hwf hlit_le hdist_le
        have hw' := (emitRefWithCodesPTFlatStep_spec bw bw litCodes distCodes w
          hlit hdist rfl hwf hwf hlit_le hdist_le).2.1
        have hind := ih _ (by omega) rw' (i + 1) hw' rfl
        have hcont := congrArg (fun fw =>
          emitTokensWithCodesTAPTFlatFastLoop fw.data fw.bitBuf fw.bitCount.toUInt32
            tokens (packCodeTab litCodes) (packCodeTab distCodes) hlitT hdistT (i + 1)) heq
        simpa only [w, rw', emitRefWithCodesPTFlatFast, flatWriteBits64Fast,
          flatWriteBits64FastLiteral, emitTokensWithCodesTAPTFlatFastLoop_ite,
          emitTokensWithCodesTAPTFlatFastLoop_dite] using hcont.trans hind
    · simp [hi, flat_writer_reconstruct]

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

/-- Direct proof contract for the scalar implementation called by the
    production block: at the zero entry it is structurally equal to the routed
    logical body, not merely observationally equal after flushing. -/
theorem emitTokensWithCodesTAPTFlatZero_eq_routed (bw : BitWriter)
    (tokens : TokenArray) (litCodes distCodes : Array (UInt16 × UInt8))
    (hlitT : (packCodeTab litCodes).size ≥ 286)
    (hdistT : (packCodeTab distCodes).size ≥ 30) (hwf : bw.wf)
    (hlit_le : ∀ j, j < litCodes.size → litCodes[j]!.2.toNat ≤ 15)
    (hdist_le : ∀ j, j < distCodes.size → distCodes[j]!.2.toNat ≤ 15) :
    emitTokensWithCodesTAPTFlatZero bw tokens
        (packCodeTab litCodes) (packCodeTab distCodes) hlitT hdistT =
      emitTokensWithCodesTAPTFlatRouted bw tokens
        (packCodeTab litCodes) (packCodeTab distCodes) hlitT hdistT := by
  unfold emitTokensWithCodesTAPTFlatZero emitTokensWithCodesTAPTFlatRouted
    emitTokensWithCodesTAPTFlat
  exact emitTokensWithCodesTAPTFlatFastLoop_eq bw tokens litCodes distCodes
    hlitT hdistT 0 hwf hlit_le hdist_le

/-- Relational form of the zero-index flat-emitter contract.  Unlike
    `emitTokensWithCodesTAPTFlat_spec`, the flat and reference loops may start
    from distinct writer representations, provided they denote the same bits.
    This is the induction invariant needed when several flat-emitted dynamic
    blocks share one bitstream. -/
theorem emitTokensWithCodesTAPTFlatZero_spec (fbw rbw : BitWriter)
    (tokens : TokenArray) (litCodes distCodes : Array (UInt16 × UInt8))
    (hlitT : (packCodeTab litCodes).size ≥ 286)
    (hdistT : (packCodeTab distCodes).size ≥ 30)
    (hbits : fbw.toBits = rbw.toBits) (hfwf : fbw.wf) (hrwf : rbw.wf)
    (hlit_le : ∀ j, j < litCodes.size → litCodes[j]!.2.toNat ≤ 15)
    (hdist_le : ∀ j, j < distCodes.size → distCodes[j]!.2.toNat ≤ 15) :
    let fw := emitTokensWithCodesTAPTFlatZero fbw tokens
      (packCodeTab litCodes) (packCodeTab distCodes) hlitT hdistT
    let rw := emitTokensWithCodesTAPT rbw tokens
      (packCodeTab litCodes) (packCodeTab distCodes) hlitT hdistT 0
    fw.toBits = rw.toBits ∧ fw.wf ∧ rw.wf := by
  rw [emitTokensWithCodesTAPTFlatZero_eq_routed fbw tokens litCodes distCodes
    hlitT hdistT hfwf hlit_le hdist_le]
  unfold emitTokensWithCodesTAPTFlatRouted emitTokensWithCodesTAPTFlat
  exact emitTokensWithCodesTAPTFlatLoop_spec fbw rbw tokens litCodes distCodes
    hlitT hdistT 0 hbits hfwf hrwf hlit_le hdist_le

/-- A bounded flat packed dynamic block is observationally equal to the
    reference packed block, even when the two blocks start from distinct
    representations of the same running bitstream.  This packages the
    relation across BFINAL/BTYPE, the dynamic header, tokens, and EOB for the
    shared multi-block induction. -/
theorem emitDynBlockPFlat_spec (fbw rbw : BitWriter) (data : ByteArray)
    (tokens : TokenArray) (litLens distLens : List Nat)
    (hlit : litLens.length = 286) (hdist : distLens.length = 30)
    (hlit_bound : ∀ x ∈ litLens, x ≤ 15)
    (hdist_bound : ∀ x ∈ distLens, x ≤ 15) (isFinal : Bool)
    (hbits : fbw.toBits = rbw.toBits) (hfwf : fbw.wf) (hrwf : rbw.wf) :
    let fw := emitDynBlockPFlat fbw data tokens litLens distLens
      hlit hdist hlit_bound hdist_bound isFinal
    let rw := emitDynBlockP rbw data tokens litLens distLens hlit hdist isFinal
    fw.toBits = rw.toBits ∧ fw.wf ∧ rw.wf := by
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

  let fbw1 := fbw.writeBits 1 (if isFinal then 1 else 0)
  let rbw1 := rbw.writeBits 1 (if isFinal then 1 else 0)
  have h1 := writeBits_congr fbw rbw 1 (if isFinal then 1 else 0)
    hbits hfwf hrwf (by omega)
  let fbw2 := fbw1.writeBits 2 2
  let rbw2 := rbw1.writeBits 2 2
  have h2 := writeBits_congr fbw1 rbw1 2 2 h1.1 h1.2.1 h1.2.2 (by omega)
  let fbw3 := writeDynamicHeader fbw2 litLens distLens
  let rbw3 := writeDynamicHeader rbw2 litLens distLens
  have h3 := writeDynamicHeader_congr fbw2 rbw2 litLens distLens hlit hdist
    h2.1 h2.2.1 h2.2.2 hlit_bound hdist_bound

  by_cases hempty : data.size == 0
  · have heob := writeHuffCode_congr fbw3 rbw3
      (litCodes[256]'h256).1 (litCodes[256]'h256).2
      h3.1 h3.2.1 h3.2.2 heob_len
    simpa only [emitDynBlockPFlat, emitDynBlockP, litCodes, distCodes,
      fbw1, rbw1, fbw2, rbw2, fbw3, rbw3, hempty, ↓reduceIte] using heob
  · let fbw4 := emitTokensWithCodesTAPTFlatZero fbw3 tokens
      (packCodeTab litCodes) (packCodeTab distCodes) hlitT_size hdistT_size
    let rbw4 := emitTokensWithCodesTAPT rbw3 tokens
      (packCodeTab litCodes) (packCodeTab distCodes) hlitT_size hdistT_size 0
    have h4 := emitTokensWithCodesTAPTFlatZero_spec fbw3 rbw3 tokens
      litCodes distCodes hlitT_size hdistT_size h3.1 h3.2.1 h3.2.2
      hlit_le hdist_le
    have heob := writeHuffCode_congr fbw4 rbw4
      (litCodes[256]'h256).1 (litCodes[256]'h256).2
      h4.1 h4.2.1 h4.2.2 heob_len
    simpa only [emitDynBlockPFlat, emitDynBlockP, litCodes, distCodes,
      fbw1, rbw1, fbw2, rbw2, fbw3, rbw3, fbw4, rbw4, hempty,
      Bool.false_eq_true, ↓reduceIte] using heob

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
  unfold deflateDynamicBlockCorePWithFlat deflateDynamicBlockCorePWithFlatBody
    deflateDynamicBlockCoreP
  simp only [BitWriter.emptyWithCapacity_eq, writeDynamicHeaderWith_dynHeaderCodes]
  by_cases hempty : data.size == 0
  · simp only [hempty, ↓reduceIte]
  · simp only [hempty, ↓reduceIte]
    rw [emitTokensWithCodesTAPTFlatZero_eq_routed
      (writeDynamicHeader ((BitWriter.empty.writeBits 1 1).writeBits 2 2) litLens distLens)
      tokens litCodes distCodes hlitT_size hdistT_size hwf_header hlit_le hdist_le]
    have hflat := emitTokensWithCodesTAPTFlat_eob_flush_eq
      (writeDynamicHeader ((BitWriter.empty.writeBits 1 1).writeBits 2 2) litLens distLens)
      tokens litCodes distCodes hlitT_size hdistT_size
      (litCodes[256]'h256).1 (litCodes[256]'h256).2 hwf_header hlit_le hdist_le heob_len
    exact hflat

end Zip.Native.Deflate
