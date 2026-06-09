import Zip.Spec.DeflateRoundtrip

/-!
# Self-contained block-splitting roundtrip

`deflateDynamicBlocksSC` chops the input into chunks, matches each chunk against
a *fresh* window (so its back-references stay within the chunk), and emits one
dynamic Huffman block per chunk (final flag on the last). Because each block is
self-contained, `resolveLZ77_shift` lets every block's bytes simply append to the
running output, and the blocks compose: decoding the concatenation reproduces the
whole input. This file proves `inflate (deflateDynamicBlocksSC …) = .ok data`.
-/

namespace Zip.Native.Deflate

open Deflate.Spec (decode)

/-- One self-contained chunk block: its bits append to `bw`, it preserves `wf`,
    and `decode.go` consumes it — appending the chunk's bytes and either returning
    (final block) or continuing on the trailing bits (non-final block). -/
theorem emitChunkBlock_decode (data : ByteArray) (pos j : Nat) (level : UInt8)
    (bw : BitWriter) (hbw : bw.wf) (isFinal : Bool) :
    ∃ blockBits,
      (emitChunkBlock bw data pos j level isFinal).toBits = bw.toBits ++ blockBits ∧
      (emitChunkBlock bw data pos j level isFinal).wf ∧
      ∀ (acc : List UInt8) (rest : List Bool),
        Deflate.Spec.decode.go (blockBits ++ rest) acc =
          if isFinal then some (acc ++ (data.extract pos j).data.toList)
          else Deflate.Spec.decode.go rest (acc ++ (data.extract pos j).data.toList) := by
  obtain ⟨litLens, distLens, headerBits, symBits, _hll, _hdl, hlv, hdv,
      hge1, hle1, hge2, hle2, hb1, hb2, htrees, hsyms, htoBits, hwf⟩ :=
    emitDynBlock_spec bw hbw (data.extract pos j)
      (lz77ChainIter (data.extract pos j) (chainDepth level) 32768 (insertCap level))
      (lz77ChainIter_encodable (data.extract pos j) (chainDepth level) 32768 (insertCap level)
        (by omega) (by omega))
      (fun hz => lz77ChainIter_empty (data.extract pos j) (chainDepth level) 32768 (insertCap level) hz)
      isFinal
  refine ⟨[isFinal, false, true] ++ headerBits ++ symBits, ?_, ?_, ?_⟩
  · -- toBits
    simp only [emitChunkBlock]
    rw [htoBits]; simp only [List.append_assoc]
  · -- wf
    simp only [emitChunkBlock]; exact hwf
  · -- decode
    intro acc rest
    have hheader := Deflate.Spec.encodeDynamicTrees_decodeDynamicTables
      litLens distLens headerBits (symBits ++ rest) hb1 hb2 ⟨hge1, hle1⟩ ⟨hge2, hle2⟩ hlv hdv htrees
    rw [← List.append_assoc] at hheader
    have hresolve := lz77ChainIter_resolves (data.extract pos j)
      (chainDepth level) 32768 (insertCap level) (by omega)
    have hvalid := tokensToSymbols_validSymbolList
      (lz77ChainIter (data.extract pos j) (chainDepth level) 32768 (insertCap level))
    cases isFinal
    · simp only [Bool.false_eq_true, if_false]
      exact Deflate.Spec.decode_go_dynBlock_nonfinal _ _ acc litLens distLens
        headerBits symBits rest hlv hdv hheader hsyms hresolve hvalid
    · simp only [if_true]
      exact Deflate.Spec.decode_go_dynBlock_final _ _ acc litLens distLens
        headerBits symBits rest hlv hdv hheader hsyms hresolve hvalid

/-- `M.take p ++ (M.drop p).take q = M.take (p + q)` — a contiguous prefix split. -/
private theorem take_append_take_drop {α} : ∀ (p : Nat) (M : List α) (q : Nat),
    M.take p ++ (M.drop p).take q = M.take (p + q) := by
  intro p
  induction p with
  | zero => intro M q; simp
  | succ p ih =>
    intro M q
    cases M with
    | nil => simp
    | cons a M' =>
      rw [List.take_succ_cons, List.drop_succ_cons, List.cons_append, ih M' q,
        show p + 1 + q = (p + q) + 1 from by omega, List.take_succ_cons]

/-- Two adjacent chunks of a byte array concatenate to the spanning chunk. -/
private theorem extract_data_append (data : ByteArray) (a b c : Nat)
    (hab : a ≤ b) (hbc : b ≤ c) :
    (data.extract a b).data.toList ++ (data.extract b c).data.toList =
      (data.extract a c).data.toList := by
  simp only [ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop]
  rw [show data.data.toList.drop b = (data.data.toList.drop a).drop (b - a) by
        rw [List.drop_drop]; congr 1; omega,
      show c - a = (b - a) + (c - b) by omega,
      take_append_take_drop]

/-- Decode fold over the self-contained chunk blocks: from `pos < data.size`,
    the bits emitted by `emitChunkBlocks` (with `bw`'s bits stripped as `B`)
    decode — appended to any `acc` — to the remaining input `data[pos:]`. The
    last block is final so it returns regardless of the trailing `tail`. -/
theorem emitChunkBlocks_decode (data : ByteArray) (chunkSize : Nat) (level : UInt8) :
    ∀ (fuel pos : Nat) (bw : BitWriter), data.size - pos ≤ fuel → pos < data.size → bw.wf →
      ∃ B, (emitChunkBlocks data chunkSize level pos bw).toBits = bw.toBits ++ B ∧
        (emitChunkBlocks data chunkSize level pos bw).wf ∧
        ∀ (acc : List UInt8) (tail : List Bool),
          Deflate.Spec.decode.go (B ++ tail) acc =
            some (acc ++ (data.extract pos data.size).data.toList) := by
  intro fuel
  induction fuel with
  | zero => intro pos bw hf hpos _; omega
  | succ fuel ih =>
    intro pos bw hf hpos hbw
    obtain ⟨blockBits, htoBits, hwfblk, hdecblk⟩ :=
      emitChunkBlock_decode data pos (min (pos + max chunkSize 1) data.size) level bw hbw
        (decide (min (pos + max chunkSize 1) data.size ≥ data.size))
    have hjle : min (pos + max chunkSize 1) data.size ≤ data.size := Nat.min_le_right _ _
    have hstep1 : 1 ≤ max chunkSize 1 := Nat.le_max_right _ _
    have hjgt : pos < min (pos + max chunkSize 1) data.size := by
      simp only [Nat.lt_min]; omega
    by_cases hend : min (pos + max chunkSize 1) data.size ≥ data.size
    · -- Final block: j = data.size.
      have hjeq : min (pos + max chunkSize 1) data.size = data.size := by omega
      have hstep : emitChunkBlocks data chunkSize level pos bw =
          emitChunkBlock bw data pos (min (pos + max chunkSize 1) data.size) level
            (decide (min (pos + max chunkSize 1) data.size ≥ data.size)) := by
        conv => lhs; unfold emitChunkBlocks
        simp only [if_pos hend]
      refine ⟨blockBits, ?_, ?_, ?_⟩
      · rw [hstep]; exact htoBits
      · rw [hstep]; exact hwfblk
      · intro acc tail
        have hd := hdecblk acc tail
        rw [if_pos (decide_eq_true hend), hjeq] at hd
        exact hd
    · -- Non-final block: recurse on the next chunk.
      have hbw' : (emitChunkBlock bw data pos (min (pos + max chunkSize 1) data.size) level
          (decide (min (pos + max chunkSize 1) data.size ≥ data.size))).wf := hwfblk
      have hstep : emitChunkBlocks data chunkSize level pos bw =
          emitChunkBlocks data chunkSize level (min (pos + max chunkSize 1) data.size)
            (emitChunkBlock bw data pos (min (pos + max chunkSize 1) data.size) level
              (decide (min (pos + max chunkSize 1) data.size ≥ data.size))) := by
        conv => lhs; unfold emitChunkBlocks
        simp only [if_neg hend]
      obtain ⟨B', htoBits', hwf', hdec'⟩ :=
        ih (min (pos + max chunkSize 1) data.size) _ (by omega) (by omega) hbw'
      refine ⟨blockBits ++ B', ?_, ?_, ?_⟩
      · rw [hstep, htoBits', htoBits, List.append_assoc]
      · rw [hstep]; exact hwf'
      · intro acc tail
        rw [List.append_assoc]
        have hd := hdecblk acc (B' ++ tail)
        rw [if_neg (by simp only [decide_eq_true_eq]; exact hend)] at hd
        rw [hd, hdec' (acc ++ (data.extract pos (min (pos + max chunkSize 1) data.size)).data.toList) tail,
          List.append_assoc,
          extract_data_append data pos (min (pos + max chunkSize 1) data.size) data.size
            (by omega) hjle]

end Zip.Native.Deflate
