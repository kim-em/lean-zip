import Zip.Native.DeflateDynamic
import Zip.Spec.DeflateDynamicHeader
import Zip.Spec.DeflateDynamicFreqs

/-!
# Correctness of the packed-token emitters (Wave 3b stage C)

`emitTokensP` / `emitTokensWithCodesP` are the single-block emitters walking
the `packTok`-encoded `UInt32` stream directly, with the per-token reference
work in the opaque non-recursive helpers `emitRefFixedP` /
`emitRefWithCodesP` (see the WF-elaboration landmine note in
`Zip/Native/DeflateFreqs.lean`). This file proves they equal the boxed
emitters over the `unpackTok` view:

    emitTokensP bw ws i = emitTokens bw (ws.map unpackTok) i

(and the `WithCodes` analogue with the same `hlit`/`hdist` hypotheses), then
lifts the equations to the single-block cores
(`deflateFixedBlockP_eq`/`deflateDynamicBlockCoreP_eq`).

Since the Wave 6.1 reference-token fusion (`BitWriter.writeFour`), the packed
reference arm emits one fused wide-word write where the boxed arm emits the
four-call `writeHuffCode`/`writeBits` chain; `BitWriter.writeFour_eq` proves
these BitWriter *values* equal, but only when the writer is `wf` and the
RFC 1951 field widths hold (code lengths ≤ 15, length/distance extra ≤ 5/13).
So `emitTokensP_eq` now carries a `bw.wf` hypothesis (and the `WithCodes`
loop additionally carries the `litCodes`/`distCodes` code-length ≤ 15
hypotheses); these are discharged at the single-block cores from
`empty_wf`/`writeDynamicHeader_wf` and `canonicalCodes_snd_le`.

Proof shape: per helper, one equation lemma per branch of the boxed
reference arm (`findLengthCode` none/some × lit-bound × `findDistCode`
none/some × dist-bound), each discharged by `unfold` + `simp only` with the
branch hypotheses. The loop equality is then a lockstep strong induction on
`ws.size - i` (the `tokenFreqsP_go_eq` shape): the tag-bit test reduces both
sides into the same arm; the literal arms agree definitionally, and the
reference arms agree by `split`ting the boxed side and rewriting the packed
helper with the resulting branch equations. The bit-level theory
(`Zip/Spec/EmitTokensCorrect.lean`, `DeflateDynamicEmit.lean`) stays on the
boxed emitters and transfers through these equalities.
-/

namespace Zip.Native.Deflate

/-! ## Branch equations for `emitRefFixedP` -/

/-- `emitRefFixedP` when the length field has no length code: no-op. -/
private theorem emitRefFixedP_none (bw : BitWriter) (w : UInt32)
    (h : findLengthCode (((w >>> 16) &&& 0x7FFF).toNat) = none) :
    emitRefFixedP bw w = bw := by
  unfold emitRefFixedP
  simp only [findLengthCodeFast_eq, h]

/-- `emitRefFixedP` when the length code is out of table bounds (dead code,
    kept branch-for-branch with the boxed emitter): no-op. -/
private theorem emitRefFixedP_oob (bw : BitWriter) (w : UInt32) (idx en : Nat) (ev : UInt32)
    (hflc : findLengthCode (((w >>> 16) &&& 0x7FFF).toNat) = some (idx, en, ev))
    (hl : ¬ idx + 257 < fixedLitCodes.size) :
    emitRefFixedP bw w = bw := by
  unfold emitRefFixedP
  simp only [findLengthCodeFast_eq, hflc, hl, ↓reduceDIte]

/-- `emitRefFixedP` when the distance field has no distance code: only the
    length code and its extra bits are written. -/
private theorem emitRefFixedP_distNone (bw : BitWriter) (w : UInt32) (idx en : Nat) (ev : UInt32)
    (hflc : findLengthCode (((w >>> 16) &&& 0x7FFF).toNat) = some (idx, en, ev))
    (hl : idx + 257 < fixedLitCodes.size)
    (hfdc : findDistCode ((w &&& 0xFFFF).toNat) = none) :
    emitRefFixedP bw w =
      (bw.writeHuffCode (fixedLitCodes[idx + 257]).1 (fixedLitCodes[idx + 257]).2).writeBits
        en ev := by
  unfold emitRefFixedP
  simp only [findLengthCodeFast_eq, findDistCodeFast_eq, hflc, hl, ↓reduceDIte, hfdc]
  rfl

/-- `emitRefFixedP` when the distance code is out of table bounds (dead
    code): only the length code and its extra bits are written. -/
private theorem emitRefFixedP_distOob (bw : BitWriter) (w : UInt32) (idx en : Nat) (ev : UInt32)
    (dIdx den : Nat) (dev : UInt32)
    (hflc : findLengthCode (((w >>> 16) &&& 0x7FFF).toNat) = some (idx, en, ev))
    (hl : idx + 257 < fixedLitCodes.size)
    (hfdc : findDistCode ((w &&& 0xFFFF).toNat) = some (dIdx, den, dev))
    (hd : ¬ dIdx < fixedDistCodes.size) :
    emitRefFixedP bw w =
      (bw.writeHuffCode (fixedLitCodes[idx + 257]).1 (fixedLitCodes[idx + 257]).2).writeBits
        en ev := by
  unfold emitRefFixedP
  simp only [findLengthCodeFast_eq, findDistCodeFast_eq, hflc, hl, ↓reduceDIte, hfdc, hd]
  rfl

/-- `emitRefFixedP` on the full path: length code + extra bits, then distance
    code + extra bits. -/
private theorem emitRefFixedP_distSome (bw : BitWriter) (w : UInt32) (idx en : Nat) (ev : UInt32)
    (dIdx den : Nat) (dev : UInt32) (hwf : bw.wf)
    (hflc : findLengthCode (((w >>> 16) &&& 0x7FFF).toNat) = some (idx, en, ev))
    (hl : idx + 257 < fixedLitCodes.size)
    (hfdc : findDistCode ((w &&& 0xFFFF).toNat) = some (dIdx, den, dev))
    (hd : dIdx < fixedDistCodes.size) :
    emitRefFixedP bw w =
      ((((bw.writeHuffCode (fixedLitCodes[idx + 257]).1 (fixedLitCodes[idx + 257]).2).writeBits
          en ev).writeHuffCode (fixedDistCodes[dIdx]).1 (fixedDistCodes[dIdx]).2).writeBits
        den dev) := by
  -- RFC 1951 field-width bounds for the fused `writeFour` (codes from the fixed
  -- tables, extra-bit counts from `findLengthCode`/`findDistCode`).
  have hlen : (fixedLitCodes[idx + 257]).2.toNat ≤ 15 := by
    have := fixedLitCodes_snd_le (idx + 257) hl
    rwa [getElem!_pos fixedLitCodes (idx + 257) hl] at this
  have hdlen : (fixedDistCodes[dIdx]).2.toNat ≤ 15 := by
    have := fixedDistCodes_snd_le dIdx hd
    rwa [getElem!_pos fixedDistCodes dIdx hd] at this
  have hen : en ≤ 5 := by
    have hspec := Deflate.Spec.findLengthCode_spec _ idx en ev hflc
    rw [hspec.2.2.1]; exact Deflate.lengthExtra_le_5 idx hspec.1
  have hden : den ≤ 13 := by
    have hspec := Deflate.Spec.findDistCode_spec _ dIdx den dev hfdc
    rw [hspec.2.2.1]; exact Deflate.distExtra_le_13 dIdx hspec.1
  unfold emitRefFixedP
  simp only [findLengthCodeFast_eq, findDistCodeFast_eq, hflc, hl, ↓reduceDIte, hfdc, hd]
  exact BitWriter.writeFour_eq bw _ _ en ev _ _ den dev hwf hlen hen hdlen hden

/-- `emitRefFixedP` preserves `BitWriter.wf` — needed to thread the `wf`
    hypothesis of `writeFour_eq` through the packed emit loop. -/
private theorem emitRefFixedP_wf (bw : BitWriter) (w : UInt32) (hwf : bw.wf) :
    (emitRefFixedP bw w).wf := by
  unfold emitRefFixedP
  split
  · rename_i idx en ev hflc
    rw [findLengthCodeFast_eq] at hflc
    by_cases hl : idx + 257 < fixedLitCodes.size
    · simp only [hl, ↓reduceDIte]
      have hlen : (fixedLitCodes[idx + 257]'hl).2.toNat ≤ 15 := by
        have := fixedLitCodes_snd_le (idx + 257) hl
        rwa [getElem!_pos fixedLitCodes (idx + 257) hl] at this
      have hen : en ≤ 25 := by
        have hspec := Deflate.Spec.findLengthCode_spec _ idx en ev hflc
        rw [hspec.2.2.1]
        exact Nat.le_trans (Deflate.lengthExtra_le_5 idx hspec.1) (by omega)
      have hwf2 := BitWriter.writeBits_wf _ en ev
        (BitWriter.writeHuffCode_wf bw _ _ hwf hlen) hen
      split
      · rename_i dIdx den dev hfdc
        rw [findDistCodeFast_eq] at hfdc
        by_cases hd : dIdx < fixedDistCodes.size
        · simp only [hd, ↓reduceDIte]
          have hdlen : (fixedDistCodes[dIdx]'hd).2.toNat ≤ 15 := by
            have := fixedDistCodes_snd_le dIdx hd
            rwa [getElem!_pos fixedDistCodes dIdx hd] at this
          have hen' : en ≤ 5 := by
            have hspec := Deflate.Spec.findLengthCode_spec _ idx en ev hflc
            rw [hspec.2.2.1]; exact Deflate.lengthExtra_le_5 idx hspec.1
          have hden : den ≤ 13 := by
            have hspec := Deflate.Spec.findDistCode_spec _ dIdx den dev hfdc
            rw [hspec.2.2.1]; exact Deflate.distExtra_le_13 dIdx hspec.1
          rw [BitWriter.writeFour_eq bw _ _ en ev _ _ den dev hwf hlen hen' hdlen hden]
          exact BitWriter.writeBits_wf _ den dev
            (BitWriter.writeHuffCode_wf _ _ _ hwf2 hdlen) (by omega)
        · simp only [hd, ↓reduceDIte]; exact hwf2
      · exact hwf2
    · simp only [hl, ↓reduceDIte]; exact hwf
  · exact hwf

/-! ## The packed fixed-code emitter equals the boxed one -/

/-- The packed fixed-code emit loop is the boxed one over the `unpackTok`
    view: lockstep strong induction; per word, the tag-bit test reduces both
    sides into the same arm, and the reference arms align by splitting the
    boxed side and rewriting `emitRefFixedP` with the branch equations. -/
theorem emitTokensP_eq (bw : BitWriter) (ws : Array UInt32) (i : Nat) (hwf : bw.wf) :
    emitTokensP bw ws i = emitTokens bw (ws.map unpackTok) i := by
  induction h : ws.size - i using Nat.strongRecOn generalizing bw i with
  | _ n ih =>
    unfold emitTokensP emitTokens
    by_cases hi : i < ws.size
    · simp only [Array.size_map, hi, ↓reduceDIte, Array.getElem_map, unpackTok]
      by_cases hc : ws[i] &&& ((1 : UInt32) <<< 31) = 0
      · simp only [hc, ↓reduceIte]
        -- literal: the written code length is ≤ 15 (fixed table), wf preserved
        have hb : ws[i].toUInt8.toNat < fixedLitCodes.size := by
          have := UInt8.toNat_lt ws[i].toUInt8; rw [Deflate.fixedLitCodes_size]; omega
        have hlen : (fixedLitCodes[ws[i].toUInt8.toNat]'hb).2.toNat ≤ 15 := by
          have := fixedLitCodes_snd_le ws[i].toUInt8.toNat hb
          rwa [getElem!_pos fixedLitCodes ws[i].toUInt8.toNat hb] at this
        exact ih _ (by omega) _ _ (BitWriter.writeHuffCode_wf bw _ _ hwf hlen) rfl
      · simp only [hc, ↓reduceIte]
        have hrefwf := emitRefFixedP_wf bw ws[i] hwf
        split
        · rename_i idx en ev hflc
          by_cases hl : idx + 257 < fixedLitCodes.size
          · simp only [hl, ↓reduceDIte]
            split
            · rename_i dIdx den dev hfdc
              by_cases hd : dIdx < fixedDistCodes.size
              · simp only [hd, ↓reduceDIte]
                have hrw := emitRefFixedP_distSome bw ws[i] _ _ _ _ _ _ hwf hflc hl hfdc hd
                rw [hrw] at hrefwf ⊢
                exact ih _ (by omega) _ _ hrefwf rfl
              · simp only [hd, ↓reduceDIte]
                have hrw := emitRefFixedP_distOob _ _ _ _ _ _ _ _ hflc hl hfdc hd
                rw [hrw] at hrefwf ⊢
                exact ih _ (by omega) _ _ hrefwf rfl
            · rename_i hfdc
              have hrw := emitRefFixedP_distNone _ _ _ _ _ hflc hl hfdc
              rw [hrw] at hrefwf ⊢
              exact ih _ (by omega) _ _ hrefwf rfl
          · simp only [hl, ↓reduceDIte]
            have hrw := emitRefFixedP_oob _ _ _ _ _ hflc hl
            rw [hrw] at hrefwf ⊢
            exact ih _ (by omega) _ _ hrefwf rfl
        · rename_i hflc
          have hrw := emitRefFixedP_none _ _ hflc
          rw [hrw] at hrefwf ⊢
          exact ih _ (by omega) _ _ hrefwf rfl
    · simp only [Array.size_map, hi, ↓reduceDIte]

/-! ## Branch equations for `emitRefWithCodesP` -/

/-- `emitRefWithCodesP` when the length field has no length code: no-op. -/
private theorem emitRefWithCodesP_none (bw : BitWriter)
    (litCodes distCodes : Array (UInt16 × UInt8)) (w : UInt32)
    (h : findLengthCode (((w >>> 16) &&& 0x7FFF).toNat) = none) :
    emitRefWithCodesP bw litCodes distCodes w = bw := by
  unfold emitRefWithCodesP
  simp only [findLengthCodeFast_eq, h]

/-- `emitRefWithCodesP` when the length code is out of table bounds (dead
    code under the callers' `hlit`): no-op. -/
private theorem emitRefWithCodesP_oob (bw : BitWriter)
    (litCodes distCodes : Array (UInt16 × UInt8)) (w : UInt32) (idx en : Nat) (ev : UInt32)
    (hflc : findLengthCode (((w >>> 16) &&& 0x7FFF).toNat) = some (idx, en, ev))
    (hl : ¬ idx + 257 < litCodes.size) :
    emitRefWithCodesP bw litCodes distCodes w = bw := by
  unfold emitRefWithCodesP
  simp only [findLengthCodeFast_eq, hflc, hl, ↓reduceDIte]

/-- `emitRefWithCodesP` when the distance field has no distance code: only
    the length code and its extra bits are written. -/
private theorem emitRefWithCodesP_distNone (bw : BitWriter)
    (litCodes distCodes : Array (UInt16 × UInt8)) (w : UInt32) (idx en : Nat) (ev : UInt32)
    (hflc : findLengthCode (((w >>> 16) &&& 0x7FFF).toNat) = some (idx, en, ev))
    (hl : idx + 257 < litCodes.size)
    (hfdc : findDistCode ((w &&& 0xFFFF).toNat) = none) :
    emitRefWithCodesP bw litCodes distCodes w =
      (bw.writeHuffCode (litCodes[idx + 257]).1 (litCodes[idx + 257]).2).writeBits en ev := by
  unfold emitRefWithCodesP
  simp only [findLengthCodeFast_eq, findDistCodeFast_eq, hflc, hl, ↓reduceDIte, hfdc]
  rfl

/-- `emitRefWithCodesP` when the distance code is out of table bounds (dead
    code under the callers' `hdist`): only the length code and its extra bits
    are written. -/
private theorem emitRefWithCodesP_distOob (bw : BitWriter)
    (litCodes distCodes : Array (UInt16 × UInt8)) (w : UInt32) (idx en : Nat) (ev : UInt32)
    (dIdx den : Nat) (dev : UInt32)
    (hflc : findLengthCode (((w >>> 16) &&& 0x7FFF).toNat) = some (idx, en, ev))
    (hl : idx + 257 < litCodes.size)
    (hfdc : findDistCode ((w &&& 0xFFFF).toNat) = some (dIdx, den, dev))
    (hd : ¬ dIdx < distCodes.size) :
    emitRefWithCodesP bw litCodes distCodes w =
      (bw.writeHuffCode (litCodes[idx + 257]).1 (litCodes[idx + 257]).2).writeBits en ev := by
  unfold emitRefWithCodesP
  simp only [findLengthCodeFast_eq, findDistCodeFast_eq, hflc, hl, ↓reduceDIte, hfdc, hd]
  rfl

/-- `emitRefWithCodesP` on the full path: length code + extra bits, then
    distance code + extra bits. -/
private theorem emitRefWithCodesP_distSome (bw : BitWriter)
    (litCodes distCodes : Array (UInt16 × UInt8)) (w : UInt32) (idx en : Nat) (ev : UInt32)
    (dIdx den : Nat) (dev : UInt32) (hwf : bw.wf)
    (hlit_le : ∀ j, j < litCodes.size → litCodes[j]!.2.toNat ≤ 15)
    (hdist_le : ∀ j, j < distCodes.size → distCodes[j]!.2.toNat ≤ 15)
    (hflc : findLengthCode (((w >>> 16) &&& 0x7FFF).toNat) = some (idx, en, ev))
    (hl : idx + 257 < litCodes.size)
    (hfdc : findDistCode ((w &&& 0xFFFF).toNat) = some (dIdx, den, dev))
    (hd : dIdx < distCodes.size) :
    emitRefWithCodesP bw litCodes distCodes w =
      ((((bw.writeHuffCode (litCodes[idx + 257]).1 (litCodes[idx + 257]).2).writeBits
          en ev).writeHuffCode (distCodes[dIdx]).1 (distCodes[dIdx]).2).writeBits den dev) := by
  have hlen : (litCodes[idx + 257]).2.toNat ≤ 15 := by
    have := hlit_le (idx + 257) hl; rwa [getElem!_pos litCodes (idx + 257) hl] at this
  have hdlen : (distCodes[dIdx]).2.toNat ≤ 15 := by
    have := hdist_le dIdx hd; rwa [getElem!_pos distCodes dIdx hd] at this
  have hen : en ≤ 5 := by
    have hspec := Deflate.Spec.findLengthCode_spec _ idx en ev hflc
    rw [hspec.2.2.1]; exact Deflate.lengthExtra_le_5 idx hspec.1
  have hden : den ≤ 13 := by
    have hspec := Deflate.Spec.findDistCode_spec _ dIdx den dev hfdc
    rw [hspec.2.2.1]; exact Deflate.distExtra_le_13 dIdx hspec.1
  unfold emitRefWithCodesP
  simp only [findLengthCodeFast_eq, findDistCodeFast_eq, hflc, hl, ↓reduceDIte, hfdc, hd]
  exact BitWriter.writeFour_eq bw _ _ en ev _ _ den dev hwf hlen hen hdlen hden

/-- `emitRefWithCodesP` preserves `BitWriter.wf` (codes bounded ≤ 15). -/
private theorem emitRefWithCodesP_wf (bw : BitWriter)
    (litCodes distCodes : Array (UInt16 × UInt8)) (w : UInt32) (hwf : bw.wf)
    (hlit_le : ∀ j, j < litCodes.size → litCodes[j]!.2.toNat ≤ 15)
    (hdist_le : ∀ j, j < distCodes.size → distCodes[j]!.2.toNat ≤ 15) :
    (emitRefWithCodesP bw litCodes distCodes w).wf := by
  unfold emitRefWithCodesP
  split
  · rename_i idx en ev hflc
    rw [findLengthCodeFast_eq] at hflc
    by_cases hl : idx + 257 < litCodes.size
    · simp only [hl, ↓reduceDIte]
      have hlen : (litCodes[idx + 257]'hl).2.toNat ≤ 15 := by
        have := hlit_le (idx + 257) hl; rwa [getElem!_pos litCodes (idx + 257) hl] at this
      have hen : en ≤ 25 := by
        have hspec := Deflate.Spec.findLengthCode_spec _ idx en ev hflc
        rw [hspec.2.2.1]
        exact Nat.le_trans (Deflate.lengthExtra_le_5 idx hspec.1) (by omega)
      have hwf2 := BitWriter.writeBits_wf _ en ev
        (BitWriter.writeHuffCode_wf bw _ _ hwf hlen) hen
      split
      · rename_i dIdx den dev hfdc
        rw [findDistCodeFast_eq] at hfdc
        by_cases hd : dIdx < distCodes.size
        · simp only [hd, ↓reduceDIte]
          have hdlen : (distCodes[dIdx]'hd).2.toNat ≤ 15 := by
            have := hdist_le dIdx hd; rwa [getElem!_pos distCodes dIdx hd] at this
          have hen' : en ≤ 5 := by
            have hspec := Deflate.Spec.findLengthCode_spec _ idx en ev hflc
            rw [hspec.2.2.1]; exact Deflate.lengthExtra_le_5 idx hspec.1
          have hden : den ≤ 13 := by
            have hspec := Deflate.Spec.findDistCode_spec _ dIdx den dev hfdc
            rw [hspec.2.2.1]; exact Deflate.distExtra_le_13 dIdx hspec.1
          rw [BitWriter.writeFour_eq bw _ _ en ev _ _ den dev hwf hlen hen' hdlen hden]
          exact BitWriter.writeBits_wf _ den dev
            (BitWriter.writeHuffCode_wf _ _ _ hwf2 hdlen) (by omega)
        · simp only [hd, ↓reduceDIte]; exact hwf2
      · exact hwf2
    · simp only [hl, ↓reduceDIte]; exact hwf
  · exact hwf

/-! ## The packed dynamic-code emitter equals the boxed one -/

/-- The packed dynamic-code emit loop is the boxed one over the `unpackTok`
    view (same `hlit`/`hdist` size hypotheses as the boxed emitter): the same
    lockstep induction as `emitTokensP_eq`. -/
theorem emitTokensWithCodesP_eq (bw : BitWriter) (ws : Array UInt32)
    (litCodes distCodes : Array (UInt16 × UInt8))
    (hlit : litCodes.size ≥ 286) (hdist : distCodes.size ≥ 30) (i : Nat) (hwf : bw.wf)
    (hlit_le : ∀ j, j < litCodes.size → litCodes[j]!.2.toNat ≤ 15)
    (hdist_le : ∀ j, j < distCodes.size → distCodes[j]!.2.toNat ≤ 15) :
    emitTokensWithCodesP bw ws litCodes distCodes hlit hdist i =
      emitTokensWithCodes bw (ws.map unpackTok) litCodes distCodes hlit hdist i := by
  induction h : ws.size - i using Nat.strongRecOn generalizing bw i with
  | _ n ih =>
    unfold emitTokensWithCodesP emitTokensWithCodes
    by_cases hi : i < ws.size
    · simp only [Array.size_map, hi, ↓reduceDIte, Array.getElem_map, unpackTok]
      by_cases hc : ws[i] &&& ((1 : UInt32) <<< 31) = 0
      · simp only [hc, ↓reduceIte]
        have hb : ws[i].toUInt8.toNat < litCodes.size := by
          have := UInt8.toNat_lt ws[i].toUInt8; omega
        have hlen : (litCodes[ws[i].toUInt8.toNat]'hb).2.toNat ≤ 15 := by
          have := hlit_le ws[i].toUInt8.toNat hb
          rwa [getElem!_pos litCodes ws[i].toUInt8.toNat hb] at this
        exact ih _ (by omega) _ _ (BitWriter.writeHuffCode_wf bw _ _ hwf hlen) rfl
      · simp only [hc, ↓reduceIte]
        have hrefwf := emitRefWithCodesP_wf bw litCodes distCodes ws[i] hwf hlit_le hdist_le
        split
        · rename_i idx en ev hflc
          by_cases hl : idx + 257 < litCodes.size
          · simp only [hl, ↓reduceDIte]
            split
            · rename_i dIdx den dev hfdc
              by_cases hd : dIdx < distCodes.size
              · simp only [hd, ↓reduceDIte]
                have hrw := emitRefWithCodesP_distSome bw litCodes distCodes ws[i]
                  _ _ _ _ _ _ hwf hlit_le hdist_le hflc hl hfdc hd
                rw [hrw] at hrefwf ⊢
                exact ih _ (by omega) _ _ hrefwf rfl
              · simp only [hd, ↓reduceDIte]
                have hrw := emitRefWithCodesP_distOob _ _ _ _ _ _ _ _ _ _ hflc hl hfdc hd
                rw [hrw] at hrefwf ⊢
                exact ih _ (by omega) _ _ hrefwf rfl
            · rename_i hfdc
              have hrw := emitRefWithCodesP_distNone _ _ _ _ _ _ _ hflc hl hfdc
              rw [hrw] at hrefwf ⊢
              exact ih _ (by omega) _ _ hrefwf rfl
          · simp only [hl, ↓reduceDIte]
            have hrw := emitRefWithCodesP_oob _ _ _ _ _ _ _ hflc hl
            rw [hrw] at hrefwf ⊢
            exact ih _ (by omega) _ _ hrefwf rfl
        · rename_i hflc
          have hrw := emitRefWithCodesP_none _ _ _ _ hflc
          rw [hrw] at hrefwf ⊢
          exact ih _ (by omega) _ _ hrefwf rfl
    · simp only [Array.size_map, hi, ↓reduceDIte]

/-! ## The packed single-block cores equal the boxed ones -/

/-- The packed fixed-block core is the boxed one over the `unpackTok` view:
    the bodies are identical up to `emitTokensP_eq`. -/
theorem deflateFixedBlockP_eq (data : ByteArray) (ptoks : Array UInt32) :
    deflateFixedBlockP data ptoks = deflateFixedBlock data (ptoks.map unpackTok) := by
  unfold deflateFixedBlockP deflateFixedBlock
  -- the writer reaching `emitTokensP` is wf: empty + two header `writeBits`
  have hwf : ((BitWriter.empty.writeBits 1 1).writeBits 2 1).wf :=
    BitWriter.writeBits_wf _ 2 1 (BitWriter.writeBits_wf _ 1 1 BitWriter.empty_wf (by omega))
      (by omega)
  simp only [emitTokensP_eq _ _ _ hwf]

/-- The packed dynamic-block core is the boxed one over the `unpackTok` view
    (same `hlit`/`hdist` hypotheses): the bodies are identical up to
    `emitTokensWithCodesP_eq`. -/
theorem deflateDynamicBlockCoreP_eq (data : ByteArray) (ptoks : Array UInt32)
    (litLens distLens : List Nat)
    (hlit : litLens.length = 286) (hdist : distLens.length = 30)
    (hlit15 : ∀ x ∈ litLens, x ≤ 15) (hdist15 : ∀ x ∈ distLens, x ≤ 15) :
    deflateDynamicBlockCoreP data ptoks litLens distLens hlit hdist =
      deflateDynamicBlockCore data (ptoks.map unpackTok) litLens distLens hlit hdist := by
  unfold deflateDynamicBlockCoreP deflateDynamicBlockCore
  -- table code-length bounds (canonical codes of ≤15 lengths are ≤15)
  have hlit_le : ∀ j, j < (canonicalCodes (litLens.toArray.map Nat.toUInt8)).size →
      (canonicalCodes (litLens.toArray.map Nat.toUInt8))[j]!.2.toNat ≤ 15 := fun j hj =>
    canonicalCodes_snd_le _ 15 (Deflate.toUInt8Array_le litLens hlit15) j hj
  have hdist_le : ∀ j, j < (canonicalCodes (distLens.toArray.map Nat.toUInt8)).size →
      (canonicalCodes (distLens.toArray.map Nat.toUInt8))[j]!.2.toNat ≤ 15 := fun j hj =>
    canonicalCodes_snd_le _ 15 (Deflate.toUInt8Array_le distLens hdist15) j hj
  -- the writer reaching `emitTokensWithCodesP` is wf: empty + header writes
  have hwf : (writeDynamicHeader ((BitWriter.empty.writeBits 1 1).writeBits 2 2)
      litLens distLens).wf :=
    writeDynamicHeader_wf _ litLens distLens
      (BitWriter.writeBits_wf _ 2 2 (BitWriter.writeBits_wf _ 1 1 BitWriter.empty_wf (by omega))
        (by omega)) hlit15 hdist15
  simp only [emitTokensWithCodesP_eq _ _ _ _ _ _ _ hwf hlit_le hdist_le]

end Zip.Native.Deflate
