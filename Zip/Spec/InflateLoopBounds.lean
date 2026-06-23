import Zip.Spec.BitReaderInvariant
import Zip.Spec.DeflateRoundtrip
import Zip.Spec.InflateComplete

/-!
# inflateLoop endPos bounds and completeness

Proves that after a successful `inflateLoop` / `inflateRaw`:
- `endPos ≤ data.size` (upper bound)
- `endPos ≥ (pfx ++ deflated).size` (lower bound, when the encoder pads < 8 bits)
- `endPos = (pfx ++ deflated).size` (exactness, combining the two)

Also contains:
- `inflateLoop_complete_ext`: extended completeness exposing the final BitReader state
- `inflateRaw_complete`: completeness for `inflateRaw` at arbitrary startPos
- `alignToByte_pos_ge_of_toBits_short`: lower bound for short remaining bits
-/

namespace Zip.Native

open ZipCommon

/-! ### inflateLoop endPos bound -/

/-- After a successful `inflateLoop`, the returned endPos ≤ br.data.size.

    The proof tracks three invariants through each operation:
    data preservation, hpos (bitOff=0 ∨ pos<data.size), and pos ≤ data.size.
    Terminal case: alignToByte gives endPos ≤ data.size.
    Recursive case: chain data_eq back to the original data. -/
theorem inflateLoop_endPos_le (br : BitReader) (output : ByteArray)
    (fixedLit fixedDist : HuffTree) (maxOut dataSize : Nat)
    (result : ByteArray) (endPos : Nat)
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (hple : br.pos ≤ br.data.size)
    (hflit : HuffTree.fromLengths Inflate.fixedLitLengths = .ok fixedLit)
    (hfdist : HuffTree.fromLengths Inflate.fixedDistLengths = .ok fixedDist)
    (h : Inflate.inflateLoop br output fixedLit fixedDist maxOut dataSize =
      .ok (result, endPos)) :
    endPos ≤ br.data.size := by
  suffices ∀ k (br : BitReader) (output : ByteArray)
      (result : ByteArray) (endPos : Nat),
      dataSize * 8 - br.bitPos ≤ k →
      (br.bitOff = 0 ∨ br.pos < br.data.size) →
      br.pos ≤ br.data.size →
      Inflate.inflateLoop br output fixedLit fixedDist maxOut dataSize =
        .ok (result, endPos) →
      endPos ≤ br.data.size from
    this _ br output result endPos Nat.le.refl hpos hple h
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro br output result endPos hk hpos hple h
    rw [Inflate.inflateLoop.eq_1] at h
    simp only [bind, Except.bind] at h
    cases hbf : br.readBits 1 with
    | error e => simp only [hbf] at h; exact nomatch h
    | ok p =>
      obtain ⟨bfinal, br₁⟩ := p; simp only [hbf] at h
      have ⟨hd₁, hpos₁, hple₁⟩ := readBits_inv br br₁ 1 bfinal hbf hpos hple
      cases hbt : br₁.readBits 2 with
      | error e => simp only [hbt] at h; exact nomatch h
      | ok p =>
        obtain ⟨btype, br₂⟩ := p; simp only [hbt] at h
        have ⟨hd₂, hpos₂, hple₂⟩ := readBits_inv br₁ br₂ 2 btype hbt hpos₁ hple₁
        -- Helper: from block result + bfinal/WF guards → endPos ≤ br.data.size
        have post_block : ∀ (br' : BitReader) (output' : ByteArray),
            br'.data = br.data →
            (br'.bitOff = 0 ∨ br'.pos < br'.data.size) →
            br'.pos ≤ br'.data.size →
            -- bfinal check
            (if (bfinal == 1) = true then pure (output', br'.alignToByte.pos)
             else
               -- WF progress guard
               if _ : br'.bitPos ≤ br.bitPos then
                 Except.error "Inflate: no progress in inflate loop"
               else if _ : dataSize * 8 < br'.bitPos then
                 Except.error "Inflate: bit position out of range"
               else Inflate.inflateLoop br' output' fixedLit fixedDist maxOut dataSize) =
              .ok (result, endPos) →
            endPos ≤ br.data.size := by
          intro br' output' hd' hpos' hple' hif
          split at hif
          · -- bfinal = 1: endPos = br'.alignToByte.pos
            simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hif
            obtain ⟨_, rfl⟩ := hif
            have := alignToByte_pos_le br' hpos' hple'
            rw [hd'] at this; exact this
          · -- bfinal ≠ 1: WF guards then recursive call
            split at hif
            · exact nomatch hif
            · rename_i h_progress
              split at hif
              · exact nomatch hif
              · have hle := ih _ (by omega) br' output' result endPos Nat.le.refl hpos' hple' hif
                rw [hd'] at hle; exact hle
        -- Dispatch by block type
        split at h
        · -- btype = 0: stored
          split at h; · exact nomatch h
          · rename_i v hds; obtain ⟨out', br'⟩ := v; simp only [] at hds h
            have ⟨hd, hp, hl⟩ := decodeStored_inv br₂ br' output out' maxOut hds
            exact post_block br' out' (hd.trans (hd₂.trans hd₁)) hp hl h
        · -- btype = 1: fixed Huffman
          split at h; · exact nomatch h
          · rename_i v hdh; obtain ⟨out', br'⟩ := v; simp only [] at hdh h
            rw [Inflate.decodeHuffmanFast_eq br₂ output fixedLit fixedDist maxOut
              (Zip.Native.InflateBuf.fromLengths_depthLE hflit)
              (Zip.Native.InflateBuf.fromLengths_depthLE hfdist)
              (Zip.Native.InflateBuf.readBits_bitOff_lt_pos (by omega) hbt)
              (by
                have hbo₂ := Zip.Native.InflateBuf.readBits_bitOff_lt_pos (by omega) hbt
                simp only [ZipCommon.BitReader.bitPos]; rcases hpos₂ with h' | h' <;> omega)] at hdh
            have ⟨hd, hp, hl⟩ := decodeHuffman_inv fixedLit fixedDist br₂ br' output out'
              maxOut hdh hpos₂ hple₂
            exact post_block br' out' (hd.trans (hd₂.trans hd₁)) hp hl h
        · -- btype = 2: dynamic Huffman
          split at h; · exact nomatch h
          · rename_i v hdt; obtain ⟨litT, distT, br₃⟩ := v; simp only [] at hdt h
            have ⟨hd₃, hpos₃, hple₃⟩ := decodeDynamicTrees_inv br₂ br₃ litT distT hdt hpos₂ hple₂
            split at h; · exact nomatch h
            · rename_i v₂ hdh; obtain ⟨out', br'⟩ := v₂; simp only [] at hdh h
              rw [Inflate.decodeHuffmanFast_eq br₃ output litT distT maxOut
                (Zip.Native.InflateBuf.decodeDynamicTrees_depthLE hdt).1
                (Zip.Native.InflateBuf.decodeDynamicTrees_depthLE hdt).2
                (Zip.Native.InflateBuf.decodeDynamicTrees_bitOff_pres
                  (Zip.Native.InflateBuf.readBits_bitOff_lt_pos (by omega) hbt) hdt)
                (by
                  have hbo₃ := Zip.Native.InflateBuf.decodeDynamicTrees_bitOff_pres
                    (Zip.Native.InflateBuf.readBits_bitOff_lt_pos (by omega) hbt) hdt
                  simp only [ZipCommon.BitReader.bitPos]; rcases hpos₃ with h' | h' <;> omega)] at hdh
              unfold Inflate.decodeHuffman at hdh
              have ⟨hd, hp, hl⟩ := decodeHuffman_go_inv litT distT br₃ br' output out'
                maxOut _ hdh hpos₃ hple₃
              exact post_block br' out' (hd.trans (hd₃.trans (hd₂.trans hd₁))) hp hl h
        · -- btype ≥ 3: reserved → error
          exact nomatch h

/-! ## inflateLoop correctness with remaining bits (goR + br_final)

Helper for `inflateLoop_complete_ext`: given a successful native `inflateLoop`,
extracts the final `BitReader` state and proves `decode.goR` correspondence.
This is the "native → spec" direction extended with `goR` and invariant tracking. -/

set_option maxRecDepth 2048 in
private theorem inflateLoop_to_goR (br : BitReader) (output : ByteArray)
    (fixedLit fixedDist : HuffTree) (maxOut dataSize : Nat)
    (result : ByteArray) (endPos : Nat)
    (hwf : br.bitOff < 8)
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (hple : br.pos ≤ br.data.size)
    (hflit : HuffTree.fromLengths Inflate.fixedLitLengths = .ok fixedLit)
    (hfdist : HuffTree.fromLengths Inflate.fixedDistLengths = .ok fixedDist)
    (h : Inflate.inflateLoop br output fixedLit fixedDist maxOut dataSize =
      .ok (result, endPos)) :
    ∃ (br_final : BitReader),
      endPos = br_final.alignToByte.pos ∧
      br_final.data = br.data ∧
      br_final.bitOff < 8 ∧
      (br_final.bitOff = 0 ∨ br_final.pos < br_final.data.size) ∧
      br_final.pos ≤ br_final.data.size ∧
      Deflate.Spec.decode.goR br.toBits output.data.toList =
        some (result.data.toList, br_final.toBits) := by
  open Deflate.Correctness in
  suffices ∀ k (br : BitReader) (output : ByteArray)
      (result : ByteArray) (endPos : Nat),
      dataSize * 8 - br.bitPos ≤ k →
      br.bitOff < 8 →
      (br.bitOff = 0 ∨ br.pos < br.data.size) →
      br.pos ≤ br.data.size →
      Inflate.inflateLoop br output fixedLit fixedDist maxOut dataSize =
        .ok (result, endPos) →
      ∃ (br_final : BitReader),
        endPos = br_final.alignToByte.pos ∧
        br_final.data = br.data ∧
        br_final.bitOff < 8 ∧
        (br_final.bitOff = 0 ∨ br_final.pos < br_final.data.size) ∧
        br_final.pos ≤ br_final.data.size ∧
        Deflate.Spec.decode.goR br.toBits output.data.toList =
          some (result.data.toList, br_final.toBits) from
    this _ br output result endPos Nat.le.refl hwf hpos hple h
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro br output result endPos hk hwf hpos hple h
    rw [Inflate.inflateLoop.eq_1] at h
    simp only [bind, Except.bind] at h
    -- Read bfinal (1 bit)
    cases hbf : br.readBits 1 with
    | error e => simp only [hbf] at h; exact nomatch h
    | ok p₁ =>
      obtain ⟨bfinal, br₁⟩ := p₁; simp only [hbf] at h
      have hwf₁ := readBits_wf br 1 bfinal br₁ hwf hbf
      have hpos₁ := readBits_pos_inv br 1 bfinal br₁ hwf hpos hbf
      have ⟨bits₁, hspec_bf, hbits₁⟩ := readBits_toBits br 1 bfinal br₁ hwf (by omega) hbf
      have ⟨hd₁, _, hple₁⟩ := readBits_inv br br₁ 1 bfinal hbf hpos hple
      -- Read btype (2 bits)
      cases hbt : br₁.readBits 2 with
      | error e => simp only [hbt] at h; exact nomatch h
      | ok p₂ =>
        obtain ⟨btype, br₂⟩ := p₂; simp only [hbt] at h
        have hwf₂ := readBits_wf br₁ 2 btype br₂ hwf₁ hbt
        have hpos₂ := readBits_pos_inv br₁ 2 btype br₂ hwf₁ hpos₁ hbt
        have ⟨bits₂, hspec_bt, hbits₂⟩ := readBits_toBits br₁ 2 btype br₂ hwf₁ (by omega) hbt
        have ⟨hd₂, _, hple₂⟩ := readBits_inv br₁ br₂ 2 btype hbt hpos₁ hple₁
        have hspec_bt' : Deflate.Spec.readBitsLSB 2 bits₁ =
            some (btype.toNat, bits₂) := by rw [← hbits₁]; exact hspec_bt
        have hbr₂_bits : br₂.toBits = bits₂ := hbits₂
        -- Helper: build goR proof for a given block case
        -- We construct the goR expression by unfolding one step
        split at h
        · -- btype = 0: stored
          split at h; · exact nomatch h
          · rename_i v hds; obtain ⟨out', br'⟩ := v; simp only [] at hds h
            have ⟨storedBytes, rest, hspec_ds, hout, hrest⟩ :=
              decodeStored_correct br₂ output maxOut out' br' hwf₂ hpos₂ hds
            rw [hbr₂_bits] at hspec_ds
            have ⟨hd_s, _, hple_s⟩ := decodeStored_inv br₂ br' output out' maxOut hds
            have ⟨hwf_s, hpos_s⟩ := decodeStored_invariants br₂ output maxOut out' br' hds
            split at h
            · -- bfinal = 1: final block
              simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨hrout, hep⟩ := h
              refine ⟨br', hep.symm, hd_s.trans (hd₂.trans hd₁), hwf_s, hpos_s, hple_s, ?_⟩
              unfold Deflate.Spec.decode.goR
              simp only [hspec_bf, bind, Option.bind, hspec_bt',
                show UInt32.toNat 0 = 0 from rfl, hspec_ds]
              rw [← hout]
              have hbf_nat := bfinal_beq_nat_true bfinal ‹_›
              simp only [hbf_nat, ↓reduceIte, pure]
              rw [hrout, hrest]
            · -- bfinal ≠ 1: recursive
              split at h
              · exact nomatch h
              · rename_i h_progress
                split at h
                · exact nomatch h
                · obtain ⟨br_f, hep, hdf, hwff, hposf, hplef, hgoR⟩ :=
                    ih _ (by omega) br' out' result endPos Nat.le.refl hwf_s hpos_s hple_s h
                  refine ⟨br_f, hep, hdf.trans (hd_s.trans (hd₂.trans hd₁)),
                    hwff, hposf, hplef, ?_⟩
                  unfold Deflate.Spec.decode.goR
                  simp only [hspec_bf, bind, Option.bind, hspec_bt',
                    show UInt32.toNat 0 = 0 from rfl, hspec_ds]
                  rw [← hout]
                  have hbf_nat := bfinal_beq_nat_false bfinal ‹_›
                  simp only [hbf_nat, Bool.false_eq_true, ↓reduceIte]
                  have hlen₁ := Deflate.Spec.readBitsLSB_some_length hspec_bf
                  have hlen₂ := Deflate.Spec.readBitsLSB_some_length hspec_bt'
                  have hlen_ds := decodeStored_rest_le hspec_ds
                  simp only [show rest.length < br.toBits.length from by omega, ↓reduceDIte]
                  rw [hrest] at hgoR; exact hgoR
        · -- btype = 1: fixed Huffman
          split at h; · exact nomatch h
          · rename_i v hdh; obtain ⟨out', br'⟩ := v; simp only [] at hdh h
            rw [Inflate.decodeHuffmanFast_eq br₂ output fixedLit fixedDist maxOut
              (Zip.Native.InflateBuf.fromLengths_depthLE hflit)
              (Zip.Native.InflateBuf.fromLengths_depthLE hfdist) hwf₂
              (by simp only [ZipCommon.BitReader.bitPos]; rcases hpos₂ with h' | h' <;> omega)] at hdh
            unfold Inflate.decodeHuffman at hdh
            have ⟨syms, rest, hspec_ds, hresolve, hrest, hwf', hpos'⟩ :=
              decodeHuffman_correct
                Inflate.fixedLitLengths Inflate.fixedDistLengths
                fixedLit fixedDist maxOut br₂.data.size
                br₂ output out' br' hwf₂ hpos₂ hflit hfdist
                (by rw [Deflate.Correctness.fixedLitLengths_eq]; exact Deflate.Spec.fixedLitLengths_valid)
                (by rw [Deflate.Correctness.fixedDistLengths_eq]; exact Deflate.Spec.fixedDistLengths_valid)
                Deflate.Correctness.fixedLitLengths_size Deflate.Correctness.fixedDistLengths_size hdh
            rw [hbr₂_bits, Deflate.Correctness.fixedLitLengths_eq,
              Deflate.Correctness.fixedDistLengths_eq] at hspec_ds
            have ⟨hd_h, _, hple_h⟩ := decodeHuffman_inv fixedLit fixedDist br₂ br' output out' maxOut
              (show Inflate.decodeHuffman br₂ output fixedLit fixedDist maxOut = .ok (out', br') from by
                unfold Inflate.decodeHuffman; exact hdh) hpos₂ hple₂
            split at h
            · -- bfinal = 1: final block
              simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨hrout, hep⟩ := h
              refine ⟨br', hep.symm, hd_h.trans (hd₂.trans hd₁), hwf', hpos', hple_h, ?_⟩
              unfold Deflate.Spec.decode.goR
              simp only [hspec_bf, bind, Option.bind, hspec_bt',
                show UInt32.toNat 1 = 1 from rfl, hspec_ds, hresolve]
              have hbf_nat := bfinal_beq_nat_true bfinal ‹_›
              simp only [hbf_nat, ↓reduceIte, pure]
              rw [hrout, hrest]
            · -- bfinal ≠ 1: recursive
              split at h
              · exact nomatch h
              · rename_i h_progress
                split at h
                · exact nomatch h
                · obtain ⟨br_f, hep, hdf, hwff, hposf, hplef, hgoR⟩ :=
                    ih _ (by omega) br' out' result endPos Nat.le.refl hwf' hpos' hple_h h
                  refine ⟨br_f, hep, hdf.trans (hd_h.trans (hd₂.trans hd₁)),
                    hwff, hposf, hplef, ?_⟩
                  unfold Deflate.Spec.decode.goR
                  simp only [hspec_bf, bind, Option.bind, hspec_bt',
                    show UInt32.toNat 1 = 1 from rfl, hspec_ds, hresolve]
                  have hbf_nat := bfinal_beq_nat_false bfinal ‹_›
                  simp only [hbf_nat, Bool.false_eq_true, ↓reduceIte]
                  have hlen₁ := Deflate.Spec.readBitsLSB_some_length hspec_bf
                  have hlen₂ := Deflate.Spec.readBitsLSB_some_length hspec_bt'
                  have hlen_ds := decodeSymbols_rest_le hspec_ds
                  simp only [show rest.length < br.toBits.length from by omega, ↓reduceDIte]
                  rw [hrest] at hgoR; exact hgoR
        · -- btype = 2: dynamic Huffman
          split at h; · exact nomatch h
          · rename_i v hdt
            obtain ⟨litTree, distTree, br₃⟩ := v; simp only [] at hdt h
            have ⟨litLens, distLens, rest_dt, hspec_dt, hbr₃_bits, hwf₃, hpos₃,
                  hflit₃, hfdist₃, hvlit, hvdist, hlen_lit, hlen_dist⟩ :=
              Deflate.Correctness.decodeDynamicTrees_correct br₂ litTree distTree br₃
                hwf₂ hpos₂ hdt
            rw [hbr₂_bits] at hspec_dt
            have ⟨hd₃, _, hple₃⟩ := decodeDynamicTrees_inv br₂ br₃ litTree distTree hdt hpos₂ hple₂
            split at h; · exact nomatch h
            · rename_i v₂ hdh; obtain ⟨out', br'⟩ := v₂; simp only [] at hdh h
              rw [Inflate.decodeHuffmanFast_eq br₃ output litTree distTree maxOut
                (Zip.Native.InflateBuf.decodeDynamicTrees_depthLE hdt).1
                (Zip.Native.InflateBuf.decodeDynamicTrees_depthLE hdt).2 hwf₃
                (by simp only [ZipCommon.BitReader.bitPos]; rcases hpos₃ with h' | h' <;> omega)] at hdh
              unfold Inflate.decodeHuffman at hdh
              have ⟨syms, rest, hspec_ds, hresolve, hrest, hwf', hpos'⟩ :=
                decodeHuffman_correct litLens distLens
                  litTree distTree maxOut br₃.data.size
                  br₃ output out' br' hwf₃ hpos₃ hflit₃ hfdist₃
                  hvlit hvdist hlen_lit hlen_dist hdh
              rw [hbr₃_bits] at hspec_ds
              have ⟨hd_h, _, hple_h⟩ := decodeHuffman_inv litTree distTree br₃ br' output out' maxOut
                (show Inflate.decodeHuffman br₃ output litTree distTree maxOut = .ok (out', br') from by
                  unfold Inflate.decodeHuffman; exact hdh) hpos₃ hple₃
              split at h
              · -- bfinal = 1: final block
                simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
                obtain ⟨hrout, hep⟩ := h
                refine ⟨br', hep.symm, hd_h.trans (hd₃.trans (hd₂.trans hd₁)),
                  hwf', hpos', hple_h, ?_⟩
                unfold Deflate.Spec.decode.goR
                simp only [hspec_bf, bind, Option.bind, hspec_bt',
                  show UInt32.toNat 2 = 2 from rfl, hspec_dt, hspec_ds, hresolve]
                have hbf_nat := bfinal_beq_nat_true bfinal ‹_›
                simp only [hbf_nat, ↓reduceIte, pure]
                rw [hrout, hrest]
              · -- bfinal ≠ 1: recursive
                split at h
                · exact nomatch h
                · rename_i h_progress
                  split at h
                  · exact nomatch h
                  · obtain ⟨br_f, hep, hdf, hwff, hposf, hplef, hgoR⟩ :=
                      ih _ (by omega) br' out' result endPos Nat.le.refl hwf' hpos' hple_h h
                    refine ⟨br_f, hep,
                      hdf.trans (hd_h.trans (hd₃.trans (hd₂.trans hd₁))),
                      hwff, hposf, hplef, ?_⟩
                    unfold Deflate.Spec.decode.goR
                    simp only [hspec_bf, bind, Option.bind, hspec_bt',
                      show UInt32.toNat 2 = 2 from rfl, hspec_dt, hspec_ds, hresolve]
                    have hbf_nat := bfinal_beq_nat_false bfinal ‹_›
                    simp only [hbf_nat, Bool.false_eq_true, ↓reduceIte]
                    have hlen₁ := Deflate.Spec.readBitsLSB_some_length hspec_bf
                    have hlen₂ := Deflate.Spec.readBitsLSB_some_length hspec_bt'
                    have hlen_dt := decodeDynamicTables_rest_le hspec_dt
                    have hlen_ds := decodeSymbols_rest_le hspec_ds
                    simp only [show rest.length < br.toBits.length from by omega, ↓reduceDIte]
                    rw [hrest] at hgoR; exact hgoR
        · -- btype ≥ 3: reserved
          exact nomatch h

/-! ## inflateLoop completeness with final BitReader (extended)

The extended version of `inflateLoop_complete` that also returns the final
`BitReader` state, including `data` preservation and position bounds.
This is needed to prove `inflateRaw_endPos_ge`. -/

/-- Extended completeness for `inflateLoop`: in addition to the basic completeness
    result, this also exposes the final `BitReader` state after decompression.
    The additional properties (data preservation, position bounds) allow us to
    prove `endPos ≥ data.size` when combined with `alignToByte_pos_ge_of_toBits_short`
    and an encoder hypothesis showing remaining bits < 8.

    Composes `inflateLoop_complete` (spec → native) with `inflateLoop_to_goR`
    (native → spec properties + goR). -/
theorem inflateLoop_complete_ext (br : BitReader) (output : ByteArray)
    (fixedLit fixedDist : HuffTree) (maxOutputSize dataSize : Nat)
    (result : List UInt8)
    (hwf : br.bitOff < 8)
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (hple : br.pos ≤ br.data.size)
    (hds : br.data.size ≤ dataSize)
    (hflit : HuffTree.fromLengths Inflate.fixedLitLengths = .ok fixedLit)
    (hfdist : HuffTree.fromLengths Inflate.fixedDistLengths = .ok fixedDist)
    (hmax : result.length ≤ maxOutputSize)
    (hspec : Deflate.Spec.decode.go br.toBits output.data.toList =
        some result) :
    ∃ (br_final : BitReader) (endPos : Nat) (remaining : List Bool),
      Inflate.inflateLoop br output fixedLit fixedDist
        maxOutputSize dataSize = .ok (⟨⟨result⟩⟩, endPos) ∧
      endPos = br_final.alignToByte.pos ∧
      br_final.data = br.data ∧
      br_final.bitOff < 8 ∧
      (br_final.bitOff = 0 ∨ br_final.pos < br_final.data.size) ∧
      br_final.pos ≤ br_final.data.size ∧
      br_final.toBits = remaining ∧
      Deflate.Spec.decode.goR br.toBits output.data.toList =
        some (result, remaining) := by
  -- Step 1: get endPos and native result from inflateLoop_complete
  obtain ⟨endPos, hloop⟩ :=
    Deflate.Correctness.inflateLoop_complete br output fixedLit fixedDist
      maxOutputSize dataSize result hwf hpos hple hds hflit hfdist hmax hspec
  -- Step 2: extract br_final and goR from inflateLoop_to_goR
  obtain ⟨br_final, hep, hdf, hwff, hposf, hplef, hgoR⟩ :=
    inflateLoop_to_goR br output fixedLit fixedDist maxOutputSize dataSize
      ⟨⟨result⟩⟩ endPos hwf hpos hple hflit hfdist hloop
  exact ⟨br_final, endPos, br_final.toBits,
    hloop, hep, hdf, hwff, hposf, hplef, rfl, hgoR⟩

/-- After a successful `inflateRaw`, the returned endPos ≤ data.size. -/
theorem inflateRaw_endPos_le (data : ByteArray) (startPos maxOut : Nat)
    (result : ByteArray) (endPos : Nat)
    (h : Inflate.inflateRawReference data startPos maxOut = .ok (result, endPos)) :
    endPos ≤ data.size := by
  simp only [Inflate.inflateRawReference, bind, Except.bind] at h
  cases hflit : HuffTree.fromLengths Inflate.fixedLitLengths with
  | error e => simp only [hflit] at h; exact nomatch h
  | ok fixedLit =>
    simp only [hflit] at h
    cases hfdist : HuffTree.fromLengths Inflate.fixedDistLengths with
    | error e => simp only [hfdist] at h; exact nomatch h
    | ok fixedDist =>
      simp only [hfdist] at h
      have hple : startPos ≤ data.size := by
        by_cases hle : startPos ≤ data.size
        · exact hle
        · exfalso
          have hfail : (BitReader.mk data startPos 0).readBit =
              .error "BitReader: unexpected end of input" := by
            simp only [BitReader.readBit, show startPos ≥ data.size from by omega, ↓reduceIte]
          rw [Inflate.inflateLoop.eq_1] at h
          simp only [bind, Except.bind,
            BitReader.readBits, BitReader.readBits.go, hfail] at h
          exact nomatch h
      exact inflateLoop_endPos_le ⟨data, startPos, 0⟩ .empty fixedLit fixedDist
        maxOut data.size result endPos (Or.inl rfl) hple hflit hfdist h

/-! ## alignToByte lower bound from short remaining bits -/

/-- If the remaining bits `toBits` have length < 8, then `alignToByte.pos ≥ data.size`.
    This is because < 8 remaining bits means we're in the last byte (or past it). -/
private theorem alignToByte_pos_ge_of_toBits_short (br : BitReader)
    (hwf : br.bitOff < 8)
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (hple : br.pos ≤ br.data.size)
    (hshort : br.toBits.length < 8) :
    br.alignToByte.pos ≥ br.data.size := by
  have htl := Deflate.Correctness.toBits_length br
  simp only [BitReader.alignToByte]
  split
  · -- bitOff = 0: alignToByte is no-op, endPos = pos
    rename_i h0
    have h0' : br.bitOff = 0 := by simp only [beq_iff_eq] at h0; exact h0
    rw [h0', Nat.add_zero] at htl
    have hle8 : br.pos * 8 ≤ br.data.size * 8 := Nat.mul_le_mul_right 8 hple
    have htl_add : br.toBits.length + br.pos * 8 = br.data.size * 8 := by
      rw [htl]; exact Nat.sub_add_cancel hle8
    omega
  · -- bitOff ≠ 0: alignToByte advances pos by 1
    rename_i hne
    cases hpos with
    | inl h => exact absurd (by rw [h]; decide) hne
    | inr h =>
      have hlt8 : br.pos * 8 + br.bitOff < br.data.size * 8 := by omega
      have htl_add : br.toBits.length + (br.pos * 8 + br.bitOff) = br.data.size * 8 := by
        rw [htl]; exact Nat.sub_add_cancel (Nat.le_of_lt hlt8)
      show br.pos + 1 ≥ br.data.size
      omega

/-! ## endPos exactness: ≥ direction -/

/-- After a successful `inflateRaw` on `prefix ++ deflated` starting at
    `prefix.size`, the endPos ≥ `prefix.size + deflated.size` (i.e., the decoder
    consumes all of `deflated`). Combined with `inflateRaw_endPos_le`, this gives
    endPos = `(prefix ++ deflated).size` exactly. -/
theorem inflateRaw_endPos_ge (pfx deflated : ByteArray)
    (maxOut : Nat) (result : ByteArray) (endPos : Nat)
    (h : Inflate.inflateRawReference (pfx ++ deflated) pfx.size maxOut =
      .ok (result, endPos))
    (hspec : Deflate.Spec.decode.go
      (Deflate.Spec.bytesToBits deflated) [] =
      some result.data.toList)
    (hpad : ∃ remaining,
      Deflate.Spec.decode.goR (Deflate.Spec.bytesToBits deflated) [] =
        some (result.data.toList, remaining) ∧
      remaining.length < 8)
    (hmax : result.data.toList.length ≤ maxOut) :
    endPos ≥ (pfx ++ deflated).size := by
  obtain ⟨pad_remaining, hgoR_pad, hpadlen⟩ := hpad
  simp only [Inflate.inflateRawReference, bind, Except.bind] at h
  cases hflit : HuffTree.fromLengths Inflate.fixedLitLengths with
  | error e => simp only [hflit] at h; exact nomatch h
  | ok fixedLit =>
    simp only [hflit] at h
    cases hfdist : HuffTree.fromLengths Inflate.fixedDistLengths with
    | error e => simp only [hfdist] at h; exact nomatch h
    | ok fixedDist =>
      simp only [hfdist] at h
      have hbr_toBits : (BitReader.mk (pfx ++ deflated) pfx.size 0).toBits =
          Deflate.Spec.bytesToBits deflated := by
        simp only [BitReader.toBits]
        rw [show pfx.size * 8 + 0 = pfx.size * 8 from by omega]
        rw [show Deflate.Spec.bytesToBits (pfx ++ deflated) =
            Deflate.Spec.bytesToBits pfx ++ Deflate.Spec.bytesToBits deflated from by
          simp only [Deflate.Spec.bytesToBits, ByteArray.data_append, Array.toList_append,
            List.flatMap_append]]
        rw [← Deflate.Spec.bytesToBits_length pfx, List.drop_left]
      have hspec' : Deflate.Spec.decode.go
          (BitReader.mk (pfx ++ deflated) pfx.size 0).toBits [] =
          some result.data.toList := by rw [hbr_toBits]; exact hspec
      obtain ⟨br_final, endPos', remaining, hloop, hep, hdf, hwff, hposf, hplef, hrestf, hgoR⟩ :=
        inflateLoop_complete_ext
          ⟨pfx ++ deflated, pfx.size, 0⟩ .empty fixedLit fixedDist
          maxOut (pfx ++ deflated).size result.data.toList (by show 0 < 8; omega) (Or.inl rfl)
          (by simp only [ByteArray.size_append]; omega) Nat.le.refl
          hflit hfdist hmax hspec'
      have hloop_eq : Inflate.inflateLoop ⟨pfx ++ deflated, pfx.size, 0⟩
          .empty fixedLit fixedDist maxOut (pfx ++ deflated).size =
          .ok (result, endPos) := h
      have hep_eq : endPos = endPos' := by
        rw [show (⟨⟨result.data.toList⟩⟩ : ByteArray) = result from rfl] at hloop
        have := hloop_eq.symm.trans hloop
        simp only [Except.ok.injEq, Prod.mk.injEq] at this
        exact this.2
      rw [hep_eq, hep]
      rw [show (pfx ++ deflated).size = br_final.data.size from by
        simp only [hdf]]
      apply alignToByte_pos_ge_of_toBits_short br_final hwff hposf hplef
      rw [hrestf]
      have hgoR' : Deflate.Spec.decode.goR (Deflate.Spec.bytesToBits deflated) []
          = some (result.data.toList, remaining) := by
        rw [← hbr_toBits]; exact hgoR
      rw [(Prod.mk.inj (Option.some.inj (hgoR'.symm.trans hgoR_pad))).2]; exact hpadlen

/-- endPos exactness: combining ≤ and ≥ gives equality. -/
theorem inflateRaw_endPos_eq (pfx deflated : ByteArray)
    (maxOut : Nat) (result : ByteArray) (endPos : Nat)
    (h : Inflate.inflateRawReference (pfx ++ deflated) pfx.size maxOut =
      .ok (result, endPos))
    (hspec : Deflate.Spec.decode.go
      (Deflate.Spec.bytesToBits deflated) [] =
      some result.data.toList)
    (hpad : ∃ remaining,
      Deflate.Spec.decode.goR (Deflate.Spec.bytesToBits deflated) [] =
        some (result.data.toList, remaining) ∧
      remaining.length < 8)
    (hmax : result.data.toList.length ≤ maxOut) :
    endPos = (pfx ++ deflated).size :=
  Nat.le_antisymm
    (inflateRaw_endPos_le _ _ _ _ _ h)
    (inflateRaw_endPos_ge pfx deflated maxOut result endPos h hspec hpad hmax)

/-! ## inflateRaw completeness for non-zero startPos -/

/-- Completeness for `inflateRaw` at arbitrary `startPos`: if the spec decode
    succeeds on the bits starting at `startPos * 8`, then the native inflate
    also succeeds with the same result. -/
theorem inflateRaw_complete (data : ByteArray) (startPos maxOutputSize : Nat)
    (result : List UInt8)
    (hsize : result.length ≤ maxOutputSize)
    (hspec : Deflate.Spec.decode.go
        ((Deflate.Spec.bytesToBits data).drop (startPos * 8)) [] =
        some result) :
    ∃ endPos,
      Inflate.inflateRawReference data startPos maxOutputSize =
        .ok (⟨⟨result⟩⟩, endPos) := by
  simp only [Inflate.inflateRawReference, bind, Except.bind]
  obtain ⟨fixedLit, hflit⟩ := Zip.Spec.DeflateStoredCorrect.fromLengths_fixedLit_ok
  obtain ⟨fixedDist, hfdist⟩ := Zip.Spec.DeflateStoredCorrect.fromLengths_fixedDist_ok
  rw [hflit, hfdist]
  have hbr_wf : (BitReader.mk data startPos 0).bitOff < 8 := by show 0 < 8; omega
  have hbr_pos : (BitReader.mk data startPos 0).bitOff = 0 ∨
      (BitReader.mk data startPos 0).pos <
      (BitReader.mk data startPos 0).data.size := Or.inl rfl
  have hbr_ple : (BitReader.mk data startPos 0).pos ≤
      (BitReader.mk data startPos 0).data.size := by
    by_cases hle : startPos ≤ data.size
    · exact hle
    · exfalso
      have : (Deflate.Spec.bytesToBits data).drop (startPos * 8) = [] :=
        List.drop_eq_nil_of_le (by rw [Deflate.Spec.bytesToBits_length]; omega)
      rw [this] at hspec
      have h_none : Deflate.Spec.decode.go [] [] = none := by
        unfold Deflate.Spec.decode.go
        simp only [Deflate.Spec.readBitsLSB, bind, Option.bind]
      rw [h_none] at hspec
      exact nomatch hspec
  have hbr_bits : (BitReader.mk data startPos 0).toBits =
      (Deflate.Spec.bytesToBits data).drop (startPos * 8) := by
    simp only [BitReader.toBits, Nat.add_zero]
  have hgo : Deflate.Spec.decode.go (BitReader.mk data startPos 0).toBits
      ByteArray.empty.data.toList = some result := by
    rw [hbr_bits]; exact hspec
  exact Deflate.Correctness.inflateLoop_complete
    ⟨data, startPos, 0⟩ .empty fixedLit fixedDist maxOutputSize
    data.size result
    hbr_wf hbr_pos hbr_ple Nat.le.refl hflit hfdist hsize hgo

end Zip.Native
