import Zip.Native.DeflateDynamic

/-!
# Correctness of the packed-token emitters (Wave 3b stage C)

`emitTokensP` / `emitTokensWithCodesP` are the single-block emitters walking
the `packTok`-encoded `UInt32` stream directly, with the per-token reference
work in the opaque non-recursive helpers `emitRefFixedP` /
`emitRefWithCodesP` (see the WF-elaboration landmine note in
`Zip/Native/DeflateFreqs.lean`). This file proves they equal the boxed
emitters over the `unpackTok` view, for **every** word array — no
encodability side conditions:

    emitTokensP bw ws i = emitTokens bw (ws.map unpackTok) i

(and the `WithCodes` analogue with the same `hlit`/`hdist` hypotheses), then
lifts the equations to the single-block cores
(`deflateFixedBlockP_eq`/`deflateDynamicBlockCoreP_eq`).

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

/-- `emitRefFixedP` when the length field has no length code: vacuous, since
    `findLengthCode` always succeeds (`findLengthCode_isSome`). -/
private theorem emitRefFixedP_none (bw : BitWriter) (w : UInt32)
    (h : findLengthCode (((w >>> 16) &&& 0x7FFF).toNat) = none) :
    emitRefFixedP bw w = bw := by
  have hsome := findLengthCode_isSome (((w >>> 16) &&& 0x7FFF).toNat)
  rw [h] at hsome; simp at hsome

/-- `emitRefFixedP` when the length code is out of table bounds (dead code,
    kept branch-for-branch with the boxed emitter): no-op. -/
private theorem emitRefFixedP_oob (bw : BitWriter) (w : UInt32) (idx en : Nat) (ev : UInt32)
    (hflc : findLengthCode (((w >>> 16) &&& 0x7FFF).toNat) = some (idx, en, ev))
    (hl : ¬ idx + 257 < fixedLitCodes.size) :
    emitRefFixedP bw w = bw := by
  have hei := codeIdx_lenCodeWord _ _ _ _ hflc
  simp only [emitRefFixedP, hei, hl, ↓reduceDIte]

/-- `emitRefFixedP` when the distance field has no distance code: vacuous,
    since `findDistCode` always succeeds (`findDistCode_isSome`). -/
private theorem emitRefFixedP_distNone (bw : BitWriter) (w : UInt32) (idx en : Nat) (ev : UInt32)
    (_hflc : findLengthCode (((w >>> 16) &&& 0x7FFF).toNat) = some (idx, en, ev))
    (_hl : idx + 257 < fixedLitCodes.size)
    (hfdc : findDistCode ((w &&& 0xFFFF).toNat) = none) :
    emitRefFixedP bw w =
      (bw.writeHuffCode (fixedLitCodes[idx + 257]).1 (fixedLitCodes[idx + 257]).2).writeBits
        en ev := by
  have hsome := findDistCode_isSome ((w &&& 0xFFFF).toNat)
  rw [hfdc] at hsome; simp at hsome

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
  have hei := codeIdx_lenCodeWord _ _ _ _ hflc
  have hee := codeExtra_lenCodeWord _ _ _ _ hflc
  have hcv := codeVal_lenCodeWord _ _ _ _ (lenField_lt w) hflc
  have hdi := codeIdx_distCodeWord _ _ _ _ hfdc
  simp only [emitRefFixedP, hei, hee, hcv, hdi, hl, hd, ↓reduceDIte]
  rfl

/-- `emitRefFixedP` on the full path: length code + extra bits, then distance
    code + extra bits. -/
private theorem emitRefFixedP_distSome (bw : BitWriter) (w : UInt32) (idx en : Nat) (ev : UInt32)
    (dIdx den : Nat) (dev : UInt32)
    (hflc : findLengthCode (((w >>> 16) &&& 0x7FFF).toNat) = some (idx, en, ev))
    (hl : idx + 257 < fixedLitCodes.size)
    (hfdc : findDistCode ((w &&& 0xFFFF).toNat) = some (dIdx, den, dev))
    (hd : dIdx < fixedDistCodes.size) :
    emitRefFixedP bw w =
      ((((bw.writeHuffCode (fixedLitCodes[idx + 257]).1 (fixedLitCodes[idx + 257]).2).writeBits
          en ev).writeHuffCode (fixedDistCodes[dIdx]).1 (fixedDistCodes[dIdx]).2).writeBits
        den dev) := by
  have hei := codeIdx_lenCodeWord _ _ _ _ hflc
  have hee := codeExtra_lenCodeWord _ _ _ _ hflc
  have hcv := codeVal_lenCodeWord _ _ _ _ (lenField_lt w) hflc
  have hdi := codeIdx_distCodeWord _ _ _ _ hfdc
  have hde := codeExtra_distCodeWord _ _ _ _ hfdc
  have hdv := codeVal_distCodeWord _ _ _ _ (distField_lt w) hfdc
  simp only [emitRefFixedP, hei, hee, hcv, hdi, hde, hdv, hl, hd, ↓reduceDIte]
  rfl

/-! ## The packed fixed-code emitter equals the boxed one -/

/-- The packed fixed-code emit loop is the boxed one over the `unpackTok`
    view: lockstep strong induction; per word, the tag-bit test reduces both
    sides into the same arm, and the reference arms align by splitting the
    boxed side and rewriting `emitRefFixedP` with the branch equations. -/
theorem emitTokensP_eq (bw : BitWriter) (ws : Array UInt32) (i : Nat) :
    emitTokensP bw ws i = emitTokens bw (ws.map unpackTok) i := by
  induction h : ws.size - i using Nat.strongRecOn generalizing bw i with
  | _ n ih =>
    unfold emitTokensP emitTokens
    by_cases hi : i < ws.size
    · simp only [Array.size_map, hi, ↓reduceDIte, Array.getElem_map, unpackTok]
      by_cases hc : ws[i] &&& ((1 : UInt32) <<< 31) = 0
      · simp only [hc, ↓reduceIte]
        exact ih _ (by omega) _ _ rfl
      · simp only [hc, ↓reduceIte]
        split
        · rename_i idx en ev hflc
          by_cases hl : idx + 257 < fixedLitCodes.size
          · simp only [hl, ↓reduceDIte]
            split
            · rename_i dIdx den dev hfdc
              by_cases hd : dIdx < fixedDistCodes.size
              · simp only [hd, ↓reduceDIte]
                rw [emitRefFixedP_distSome _ _ _ _ _ _ _ _ hflc hl hfdc hd]
                exact ih _ (by omega) _ _ rfl
              · simp only [hd, ↓reduceDIte]
                rw [emitRefFixedP_distOob _ _ _ _ _ _ _ _ hflc hl hfdc hd]
                exact ih _ (by omega) _ _ rfl
            · rename_i hfdc
              rw [emitRefFixedP_distNone _ _ _ _ _ hflc hl hfdc]
              exact ih _ (by omega) _ _ rfl
          · simp only [hl, ↓reduceDIte]
            rw [emitRefFixedP_oob _ _ _ _ _ hflc hl]
            exact ih _ (by omega) _ _ rfl
        · rename_i hflc
          rw [emitRefFixedP_none _ _ hflc]
          exact ih _ (by omega) _ _ rfl
    · simp only [Array.size_map, hi, ↓reduceDIte]

/-- The `TokenArray` fixed-code emit loop equals the `Array UInt32` one over the
    `.toArray` view: identical control flow, each `.get` read bridged to the
    boxed slot by `TokenArray.get_toArray`. -/
theorem emitTokensTA_toArray (bw : BitWriter) (ta : TokenArray) (i : Nat) :
    emitTokensTA bw ta i = emitTokensP bw ta.toArray i := by
  induction hn : ta.size - i using Nat.strongRecOn generalizing bw i with
  | _ n ih =>
    unfold emitTokensTA emitTokensP
    by_cases hi : i < ta.size
    · have hi' : i < ta.toArray.size := by rw [← TokenArray.size_toArray]; exact hi
      rw [dif_pos hi, dif_pos hi']
      simp only [TokenArray.get_toArray]
      by_cases hc : ta.toArray[i] &&& ((1 : UInt32) <<< 31) = 0
      · rw [if_pos hc, if_pos hc]; exact ih _ (by omega) _ _ rfl
      · rw [if_neg hc, if_neg hc]; exact ih _ (by omega) _ _ rfl
    · have hi' : ¬ i < ta.toArray.size := by rw [← TokenArray.size_toArray]; exact hi
      rw [dif_neg hi, dif_neg hi']

/-! ## Branch equations for `emitRefWithCodesP` -/

/-- `emitRefWithCodesP` when the length field has no length code: no-op. -/
private theorem emitRefWithCodesP_none (bw : BitWriter)
    (litCodes distCodes : Array (UInt16 × UInt8)) (w : UInt32)
    (h : findLengthCode (((w >>> 16) &&& 0x7FFF).toNat) = none) :
    emitRefWithCodesP bw litCodes distCodes w = bw := by
  have hsome := findLengthCode_isSome (((w >>> 16) &&& 0x7FFF).toNat)
  rw [h] at hsome; simp at hsome

/-- `emitRefWithCodesP` when the length code is out of table bounds (dead
    code under the callers' `hlit`): no-op. -/
private theorem emitRefWithCodesP_oob (bw : BitWriter)
    (litCodes distCodes : Array (UInt16 × UInt8)) (w : UInt32) (idx en : Nat) (ev : UInt32)
    (hflc : findLengthCode (((w >>> 16) &&& 0x7FFF).toNat) = some (idx, en, ev))
    (hl : ¬ idx + 257 < litCodes.size) :
    emitRefWithCodesP bw litCodes distCodes w = bw := by
  have hei := codeIdx_lenCodeWord _ _ _ _ hflc
  simp only [emitRefWithCodesP, hei, hl, ↓reduceDIte]

/-- `emitRefWithCodesP` when the distance field has no distance code: vacuous,
    since `findDistCode` always succeeds (`findDistCode_isSome`). -/
private theorem emitRefWithCodesP_distNone (bw : BitWriter)
    (litCodes distCodes : Array (UInt16 × UInt8)) (w : UInt32) (idx en : Nat) (ev : UInt32)
    (_hflc : findLengthCode (((w >>> 16) &&& 0x7FFF).toNat) = some (idx, en, ev))
    (_hl : idx + 257 < litCodes.size)
    (hfdc : findDistCode ((w &&& 0xFFFF).toNat) = none) :
    emitRefWithCodesP bw litCodes distCodes w =
      (bw.writeHuffCode (litCodes[idx + 257]).1 (litCodes[idx + 257]).2).writeBits en ev := by
  have hsome := findDistCode_isSome ((w &&& 0xFFFF).toNat)
  rw [hfdc] at hsome; simp at hsome

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
  have hei := codeIdx_lenCodeWord _ _ _ _ hflc
  have hee := codeExtra_lenCodeWord _ _ _ _ hflc
  have hcv := codeVal_lenCodeWord _ _ _ _ (lenField_lt w) hflc
  have hdi := codeIdx_distCodeWord _ _ _ _ hfdc
  simp only [emitRefWithCodesP, hei, hee, hcv, hdi, hl, hd, ↓reduceDIte]
  rfl

/-- `emitRefWithCodesP` on the full path: length code + extra bits, then
    distance code + extra bits. -/
private theorem emitRefWithCodesP_distSome (bw : BitWriter)
    (litCodes distCodes : Array (UInt16 × UInt8)) (w : UInt32) (idx en : Nat) (ev : UInt32)
    (dIdx den : Nat) (dev : UInt32)
    (hflc : findLengthCode (((w >>> 16) &&& 0x7FFF).toNat) = some (idx, en, ev))
    (hl : idx + 257 < litCodes.size)
    (hfdc : findDistCode ((w &&& 0xFFFF).toNat) = some (dIdx, den, dev))
    (hd : dIdx < distCodes.size) :
    emitRefWithCodesP bw litCodes distCodes w =
      ((((bw.writeHuffCode (litCodes[idx + 257]).1 (litCodes[idx + 257]).2).writeBits
          en ev).writeHuffCode (distCodes[dIdx]).1 (distCodes[dIdx]).2).writeBits den dev) := by
  have hei := codeIdx_lenCodeWord _ _ _ _ hflc
  have hee := codeExtra_lenCodeWord _ _ _ _ hflc
  have hcv := codeVal_lenCodeWord _ _ _ _ (lenField_lt w) hflc
  have hdi := codeIdx_distCodeWord _ _ _ _ hfdc
  have hde := codeExtra_distCodeWord _ _ _ _ hfdc
  have hdv := codeVal_distCodeWord _ _ _ _ (distField_lt w) hfdc
  simp only [emitRefWithCodesP, hei, hee, hcv, hdi, hde, hdv, hl, hd, ↓reduceDIte]
  rfl

/-! ## The packed dynamic-code emitter equals the boxed one -/

/-- The packed dynamic-code emit loop is the boxed one over the `unpackTok`
    view (same `hlit`/`hdist` size hypotheses as the boxed emitter): the same
    lockstep induction as `emitTokensP_eq`. -/
theorem emitTokensWithCodesP_eq (bw : BitWriter) (ws : Array UInt32)
    (litCodes distCodes : Array (UInt16 × UInt8))
    (hlit : litCodes.size ≥ 286) (hdist : distCodes.size ≥ 30) (i : Nat) :
    emitTokensWithCodesP bw ws litCodes distCodes hlit hdist i =
      emitTokensWithCodes bw (ws.map unpackTok) litCodes distCodes hlit hdist i := by
  induction h : ws.size - i using Nat.strongRecOn generalizing bw i with
  | _ n ih =>
    unfold emitTokensWithCodesP emitTokensWithCodes
    by_cases hi : i < ws.size
    · simp only [Array.size_map, hi, ↓reduceDIte, Array.getElem_map, unpackTok]
      by_cases hc : ws[i] &&& ((1 : UInt32) <<< 31) = 0
      · simp only [hc, ↓reduceIte]
        exact ih _ (by omega) _ _ rfl
      · simp only [hc, ↓reduceIte]
        split
        · rename_i idx en ev hflc
          by_cases hl : idx + 257 < litCodes.size
          · simp only [hl, ↓reduceDIte]
            split
            · rename_i dIdx den dev hfdc
              by_cases hd : dIdx < distCodes.size
              · simp only [hd, ↓reduceDIte]
                rw [emitRefWithCodesP_distSome _ _ _ _ _ _ _ _ _ _ hflc hl hfdc hd]
                exact ih _ (by omega) _ _ rfl
              · simp only [hd, ↓reduceDIte]
                rw [emitRefWithCodesP_distOob _ _ _ _ _ _ _ _ _ _ hflc hl hfdc hd]
                exact ih _ (by omega) _ _ rfl
            · rename_i hfdc
              rw [emitRefWithCodesP_distNone _ _ _ _ _ _ _ hflc hl hfdc]
              exact ih _ (by omega) _ _ rfl
          · simp only [hl, ↓reduceDIte]
            rw [emitRefWithCodesP_oob _ _ _ _ _ _ _ hflc hl]
            exact ih _ (by omega) _ _ rfl
        · rename_i hflc
          rw [emitRefWithCodesP_none _ _ _ _ hflc]
          exact ih _ (by omega) _ _ rfl
    · simp only [Array.size_map, hi, ↓reduceDIte]

/-! ## The packed-table emitter equals the pair-table one (#2827) -/

/-- `packCodeEntry` keeps the bit length in bits 16–23. -/
private theorem packCodeEntry_len (e : UInt16 × UInt8) :
    (packCodeEntry e >>> 16).toUInt8 = e.2 := by
  obtain ⟨c, l⟩ := e
  unfold packCodeEntry
  generalize BitWriter.reverse16 c = r
  bv_decide

/-- Writing a packed entry through `writeRevCode` is `writeHuffCode` of the
    original pair: the packed code field is exactly the precomputed
    LSB-first reversal `writeRevCode` expects. -/
private theorem packCodeEntry_write (bw : BitWriter) (e : UInt16 × UInt8) :
    bw.writeRevCode (packCodeEntry e).toUInt16 ((packCodeEntry e) >>> 16).toUInt8 =
      bw.writeHuffCode e.1 e.2 := by
  obtain ⟨c, l⟩ := e
  have hcode : (packCodeEntry (c, l)).toUInt16 =
      ((BitWriter.reverse16 c).toUInt64 >>> (16 - l.toUInt64)).toUInt16 := by
    unfold packCodeEntry
    generalize BitWriter.reverse16 c = r
    bv_decide
  rw [packCodeEntry_len, hcode, BitWriter.writeRevCode_eq]

/-- The extra-bit count of any code word is a byte field (`&&& 0xFF`), so it is
    always below 256 — the bound `writeRevCodeExtra_eq` needs to stay faithful. -/
private theorem codeExtra_lt_256 (w : UInt32) : codeExtra w < 256 := by
  unfold codeExtra
  have h : (w >>> 8) &&& 0xFF < 256 := by bv_decide
  simpa using UInt32.lt_iff_toNat_lt.mp h

/-- The packed-table reference emit is the pair-table one over `packCodeTab`:
    identical branch structure, each table read recovered by
    `packCodeEntry_code`/`packCodeEntry_len`, and each fused huff+extra write
    unfused back to the two-call form (`writeRevCodeExtra_eq`, whose byte-field
    extra-count bound is `codeExtra_lt_256`). -/
private theorem emitRefWithCodesPT_eq (bw : BitWriter)
    (litCodes distCodes : Array (UInt16 × UInt8)) (w : UInt32) :
    emitRefWithCodesPT bw (packCodeTab litCodes) (packCodeTab distCodes) w =
      emitRefWithCodesP bw litCodes distCodes w := by
  unfold emitRefWithCodesPT emitRefWithCodesP
  simp only [packCodeTab, Array.size_map, Array.getElem_map, packCodeEntry_write,
    BitWriter.writeRevCodeExtra_eq, codeExtra_lt_256]
  rfl

/-- The packed-table emit loop is the pair-table one over `packCodeTab`, for
    every word array — the lockstep induction of `emitTokensWithCodesP_eq`
    with the table reads bridged per arm. -/
theorem emitTokensWithCodesPT_eq (bw : BitWriter) (ws : Array UInt32)
    (litCodes distCodes : Array (UInt16 × UInt8))
    (hlitT : (packCodeTab litCodes).size ≥ 286)
    (hdistT : (packCodeTab distCodes).size ≥ 30) (i : Nat) :
    emitTokensWithCodesPT bw ws (packCodeTab litCodes) (packCodeTab distCodes) hlitT hdistT i =
      emitTokensWithCodesP bw ws litCodes distCodes
        (by simpa using hlitT) (by simpa using hdistT) i := by
  induction h : ws.size - i using Nat.strongRecOn generalizing bw i with
  | _ n ih =>
    unfold emitTokensWithCodesPT emitTokensWithCodesP
    by_cases hi : i < ws.size
    · simp only [hi, ↓reduceDIte]
      by_cases hc : ws[i] &&& ((1 : UInt32) <<< 31) = 0
      · simp only [hc, ↓reduceIte, packCodeTab, Array.getElem_map, packCodeEntry_write]
        exact ih _ (by omega) _ _ rfl
      · simp only [hc, ↓reduceIte, emitRefWithCodesPT_eq]
        exact ih _ (by omega) _ _ rfl
    · simp only [hi, ↓reduceDIte]


/-- The USize-index emit loop is the `Nat`-index one at `i.toNat`: lockstep
    induction on the remaining tokens, with the `USize` increment aligned by
    the in-range step identity. -/
theorem emitTokensWithCodesPTU_eq (bw : BitWriter) (ws : Array UInt32)
    (litT distT : Array UInt32)
    (hlit : litT.size ≥ 286) (hdist : distT.size ≥ 30)
    (hsz : ws.size < USize.size) (i : USize) :
    emitTokensWithCodesPTU bw ws litT distT hlit hdist hsz i =
      emitTokensWithCodesPT bw ws litT distT hlit hdist i.toNat := by
  induction h : ws.size - i.toNat using Nat.strongRecOn generalizing bw i with
  | _ n ih =>
    unfold emitTokensWithCodesPTU emitTokensWithCodesPT
    by_cases hi : i.toNat < ws.size
    · have hstep : (i + 1).toNat = i.toNat + 1 := by
        have hUS : USize.size = 2 ^ System.Platform.numBits := rfl
        rw [USize.toNat_add, USize.toNat_one]; exact Nat.mod_eq_of_lt (by omega)
      simp only [hi, ↓reduceDIte, Array.uget]
      by_cases hc : ws[i.toNat] &&& ((1 : UInt32) <<< 31) = 0
      · simp only [hc, ↓reduceIte]
        rw [ih _ (by omega) _ _ rfl, hstep]
      · simp only [hc, ↓reduceIte]
        rw [ih _ (by omega) _ _ rfl, hstep]
    · simp only [hi, ↓reduceDIte]

/-- The guarded USize emit dispatch equals the `Nat` loop from `0`: the guard
    hit rewrites through `emitTokensWithCodesPTU_eq` (with `(0 : USize).toNat = 0`),
    the miss is definitional. -/
theorem emitTokensWithCodesPTG_eq (bw : BitWriter) (ws : Array UInt32)
    (litT distT : Array UInt32)
    (hlit : litT.size ≥ 286) (hdist : distT.size ≥ 30) :
    emitTokensWithCodesPTG bw ws litT distT hlit hdist =
      emitTokensWithCodesPT bw ws litT distT hlit hdist 0 := by
  unfold emitTokensWithCodesPTG
  split
  · rw [emitTokensWithCodesPTU_eq]
    simp only [USize.toNat_zero]
  · rfl

/-- The `TokenArray` packed-table emit loop equals the `Array UInt32` one over
    the `.toArray` view: identical control flow, each `.get` read bridged to the
    boxed slot by `TokenArray.get_toArray`. -/
theorem emitTokensWithCodesTAPT_toArray (bw : BitWriter) (ta : TokenArray)
    (litT distT : Array UInt32)
    (hlit : litT.size ≥ 286) (hdist : distT.size ≥ 30) (i : Nat) :
    emitTokensWithCodesTAPT bw ta litT distT hlit hdist i =
      emitTokensWithCodesPT bw ta.toArray litT distT hlit hdist i := by
  induction hn : ta.size - i using Nat.strongRecOn generalizing bw i with
  | _ n ih =>
    unfold emitTokensWithCodesTAPT emitTokensWithCodesPT
    by_cases hi : i < ta.size
    · have hi' : i < ta.toArray.size := by rw [← TokenArray.size_toArray]; exact hi
      rw [dif_pos hi, dif_pos hi']
      simp only [TokenArray.get_toArray]
      by_cases hc : ta.toArray[i] &&& ((1 : UInt32) <<< 31) = 0
      · rw [if_pos hc, if_pos hc]; exact ih _ (by omega) _ _ rfl
      · rw [if_neg hc, if_neg hc]; exact ih _ (by omega) _ _ rfl
    · have hi' : ¬ i < ta.toArray.size := by rw [← TokenArray.size_toArray]; exact hi
      rw [dif_neg hi, dif_neg hi']

/-! ## The packed single-block cores equal the boxed ones -/

/-- The packed fixed-block core is the boxed one over the `unpackTok` view:
    the bodies are identical up to `emitTokensP_eq`. -/
theorem deflateFixedBlockP_eq (data : ByteArray) (ptoks : TokenArray) (cap : Nat := 0) :
    deflateFixedBlockP data ptoks cap = deflateFixedBlock data (ptoks.toArray.map unpackTok) := by
  unfold deflateFixedBlockP deflateFixedBlock
  simp only [BitWriter.emptyWithCapacity_eq, emitTokensTA_toArray, emitTokensP_eq]

/-- The packed dynamic-block core is the boxed one over the `unpackTok` view
    (same `hlit`/`hdist` hypotheses): the bodies are identical up to
    `emitTokensWithCodesP_eq`. -/
theorem deflateDynamicBlockCoreP_eq (data : ByteArray) (ptoks : TokenArray)
    (litLens distLens : List Nat)
    (hlit : litLens.length = 286) (hdist : distLens.length = 30) :
    deflateDynamicBlockCoreP data ptoks litLens distLens hlit hdist =
      deflateDynamicBlockCore data (ptoks.toArray.map unpackTok) litLens distLens hlit hdist := by
  unfold deflateDynamicBlockCoreP deflateDynamicBlockCore
  simp only [emitTokensWithCodesTAPT_toArray, emitTokensWithCodesPT_eq, emitTokensWithCodesP_eq]

end Zip.Native.Deflate
