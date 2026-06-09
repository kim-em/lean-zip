import Zip.Spec.DeflateFixedCorrect
import Zip.Spec.DeflateDynamicCorrect
import Zip.Spec.LZ77ChainCorrect
import Zip.Spec.LZ77ChainLazyCorrect

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

/-! ## Matcher-selector contracts

The three contracts the dynamic encoder consumes, lifted to the level-dispatched
`lzMatch` by casing on `4 ≤ level` and applying the lazy (`lz77ChainLazyIter_*`) or
greedy (`lz77ChainIter_*`) version. Both arms are line-for-line parallel because
the two matchers share contract signatures. Consumed here and in `DeflateRoundtrip`,
so the `7 ≤ level`/`4 ≤ level` split lives in exactly one place. -/

theorem lzMatch_encodable (data : ByteArray) (level : UInt8) :
    ∀ t ∈ (lzMatch data level).toList,
      match t with
      | .literal _ => True
      | .reference len dist => 3 ≤ len ∧ len ≤ 258 ∧ 1 ≤ dist ∧ dist ≤ 32768 := by
  unfold lzMatch
  split
  · exact lz77ChainLazyIter_encodable data (chainDepth level) 32768 (insertCap level)
      (by omega) (by omega)
  · exact lz77ChainIter_encodable data (chainDepth level) 32768 (insertCap level)
      (by omega) (by omega)

theorem lzMatch_empty (data : ByteArray) (level : UInt8) (hz : data.size = 0) :
    lzMatch data level = #[] := by
  unfold lzMatch
  split
  · exact lz77ChainLazyIter_empty data (chainDepth level) 32768 (insertCap level) hz
  · exact lz77ChainIter_empty data (chainDepth level) 32768 (insertCap level) hz

theorem lzMatch_resolves (data : ByteArray) (level : UInt8) :
    Deflate.Spec.resolveLZ77 (tokensToSymbols (lzMatch data level)) [] =
      some data.data.toList := by
  unfold lzMatch
  split
  · exact lz77ChainLazyIter_resolves data (chainDepth level) 32768 (insertCap level) (by omega)
  · exact lz77ChainIter_resolves data (chainDepth level) 32768 (insertCap level) (by omega)

set_option maxHeartbeats 800000 in
/-- One self-contained chunk block: its bits append to `bw`, it preserves `wf`,
    and `decode.go`/`decode.goR` consume it — appending the chunk's bytes and
    either returning (final block) or continuing on the trailing bits. -/
theorem emitChunkBlock_decode (data : ByteArray) (pos j : Nat) (level : UInt8)
    (bw : BitWriter) (hbw : bw.wf) (isFinal : Bool) :
    ∃ blockBits,
      (emitChunkBlock bw data pos j level isFinal).toBits = bw.toBits ++ blockBits ∧
      (emitChunkBlock bw data pos j level isFinal).wf ∧
      (∀ (acc : List UInt8) (rest : List Bool),
        Deflate.Spec.decode.go (blockBits ++ rest) acc =
          if isFinal then some (acc ++ (data.extract pos j).data.toList)
          else Deflate.Spec.decode.go rest (acc ++ (data.extract pos j).data.toList)) ∧
      (∀ (acc : List UInt8) (rest : List Bool),
        Deflate.Spec.decode.goR (blockBits ++ rest) acc =
          if isFinal then some (acc ++ (data.extract pos j).data.toList, rest)
          else Deflate.Spec.decode.goR rest (acc ++ (data.extract pos j).data.toList)) := by
  obtain ⟨litLens, distLens, headerBits, symBits, _hll, _hdl, hlv, hdv,
      hge1, hle1, hge2, hle2, hb1, hb2, htrees, hsyms, htoBits, hwf⟩ :=
    emitDynBlock_spec bw hbw (data.extract pos j)
      (lz77ChainIter (data.extract pos j) (chainDepth level) 32768 (insertCap level))
      (lz77ChainIter_encodable (data.extract pos j) (chainDepth level) 32768 (insertCap level)
        (by omega) (by omega))
      (fun hz => lz77ChainIter_empty (data.extract pos j) (chainDepth level) 32768 (insertCap level) hz)
      isFinal
  have hresolve := lz77ChainIter_resolves (data.extract pos j)
    (chainDepth level) 32768 (insertCap level) (by omega)
  have hvalid := tokensToSymbols_validSymbolList
    (lz77ChainIter (data.extract pos j) (chainDepth level) 32768 (insertCap level))
  refine ⟨[isFinal, false, true] ++ headerBits ++ symBits, ?_, ?_, ?_, ?_⟩
  · -- toBits
    simp only [emitChunkBlock]
    rw [htoBits]; simp only [List.append_assoc]
  · -- wf
    simp only [emitChunkBlock]; exact hwf
  · -- decode.go
    intro acc rest
    have hheader := Deflate.Spec.encodeDynamicTrees_decodeDynamicTables
      litLens distLens headerBits (symBits ++ rest) hb1 hb2 ⟨hge1, hle1⟩ ⟨hge2, hle2⟩ hlv hdv htrees
    rw [← List.append_assoc] at hheader
    cases isFinal
    · simp only [Bool.false_eq_true, if_false]
      exact Deflate.Spec.decode_go_dynBlock_nonfinal _ _ acc litLens distLens
        headerBits symBits rest hlv hdv hheader hsyms hresolve hvalid
    · simp only [if_true]
      exact Deflate.Spec.decode_go_dynBlock_final _ _ acc litLens distLens
        headerBits symBits rest hlv hdv hheader hsyms hresolve hvalid
  · -- decode.goR
    intro acc rest
    have hheader := Deflate.Spec.encodeDynamicTrees_decodeDynamicTables
      litLens distLens headerBits (symBits ++ rest) hb1 hb2 ⟨hge1, hle1⟩ ⟨hge2, hle2⟩ hlv hdv htrees
    rw [← List.append_assoc] at hheader
    cases isFinal
    · simp only [Bool.false_eq_true, if_false]
      exact Deflate.Spec.decode_goR_dynBlock_nonfinal _ _ acc litLens distLens
        headerBits symBits rest hlv hdv hheader hsyms hresolve hvalid
    · simp only [if_true]
      exact Deflate.Spec.decode_goR_dynBlock_final _ _ acc litLens distLens
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
    obtain ⟨blockBits, htoBits, hwfblk, hdecblk, _⟩ :=
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

/-- `decode.goR` variant of `emitChunkBlocks_decode`: the remaining bits after
    decoding all chunk blocks are exactly the trailing `tail`. -/
theorem emitChunkBlocks_decodeR (data : ByteArray) (chunkSize : Nat) (level : UInt8) :
    ∀ (fuel pos : Nat) (bw : BitWriter), data.size - pos ≤ fuel → pos < data.size → bw.wf →
      ∃ B, (emitChunkBlocks data chunkSize level pos bw).toBits = bw.toBits ++ B ∧
        (emitChunkBlocks data chunkSize level pos bw).wf ∧
        ∀ (acc : List UInt8) (tail : List Bool),
          Deflate.Spec.decode.goR (B ++ tail) acc =
            some (acc ++ (data.extract pos data.size).data.toList, tail) := by
  intro fuel
  induction fuel with
  | zero => intro pos bw hf hpos _; omega
  | succ fuel ih =>
    intro pos bw hf hpos hbw
    obtain ⟨blockBits, htoBits, hwfblk, _, hdecblk⟩ :=
      emitChunkBlock_decode data pos (min (pos + max chunkSize 1) data.size) level bw hbw
        (decide (min (pos + max chunkSize 1) data.size ≥ data.size))
    have hjle : min (pos + max chunkSize 1) data.size ≤ data.size := Nat.min_le_right _ _
    have hstep1 : 1 ≤ max chunkSize 1 := Nat.le_max_right _ _
    have hjgt : pos < min (pos + max chunkSize 1) data.size := by
      simp only [Nat.lt_min]; omega
    by_cases hend : min (pos + max chunkSize 1) data.size ≥ data.size
    · have hjeq : min (pos + max chunkSize 1) data.size = data.size := by omega
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
    · have hbw' : (emitChunkBlock bw data pos (min (pos + max chunkSize 1) data.size) level
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

/-- Block-splitting roundtrip: decoding the self-contained chunk-block stream
    reproduces the input. The empty input is a single final block; otherwise the
    chunk-block fold (`emitChunkBlocks_decode`) reconstructs `data[0:]`. -/
theorem decode_deflateDynamicBlocksSC (data : ByteArray) (chunkSize : Nat) (level : UInt8) :
    Deflate.Spec.decode
      (Deflate.Spec.bytesToBits (deflateDynamicBlocksSC data chunkSize level)) =
      some data.data.toList := by
  unfold deflateDynamicBlocksSC
  split
  · -- data.size = 0: one final block over the empty token list.
    rename_i hz
    rw [beq_iff_eq] at hz
    obtain ⟨litLens, distLens, headerBits, symBits, _, _, hlv, hdv,
        hge1, hle1, hge2, hle2, hb1, hb2, htrees, hsyms, htoBits, hwf⟩ :=
      emitDynBlock_spec BitWriter.empty BitWriter.empty_wf data #[] (by simp) (fun _ => rfl) true
    rw [BitWriter.empty_toBits, List.nil_append] at htoBits
    rw [flush_toBits_aligned _ hwf, htoBits]
    have hheader := Deflate.Spec.encodeDynamicTrees_decodeDynamicTables litLens distLens headerBits
      (symBits ++ List.replicate
        ((8 - ([true, false, true] ++ headerBits ++ symBits).length % 8) % 8) false)
      hb1 hb2 ⟨hge1, hle1⟩ ⟨hge2, hle2⟩ hlv hdv htrees
    rw [← List.append_assoc] at hheader
    have hres : Deflate.Spec.resolveLZ77 (tokensToSymbols #[]) [] = some data.data.toList := by
      have he : data.data.toList = [] :=
        List.eq_nil_of_length_eq_zero (by simp only [Array.length_toList, ByteArray.size_data, hz])
      rw [he]; rfl
    exact Deflate.Spec.encodeDynamic_decode_append (tokensToSymbols #[]) data.data.toList
      litLens distLens headerBits symBits _ hlv hdv hheader hsyms hres
      (tokensToSymbols_validSymbolList _)
  · -- data.size > 0: the chunk-block fold.
    rename_i hz
    have hpos : 0 < data.size := by
      rcases Nat.eq_zero_or_pos data.size with h | h
      · rw [h] at hz; simp at hz
      · exact h
    obtain ⟨B, htoBits, hwf, hdec⟩ :=
      emitChunkBlocks_decode data chunkSize level data.size 0 BitWriter.empty
        (by omega) hpos BitWriter.empty_wf
    rw [BitWriter.empty_toBits, List.nil_append] at htoBits
    rw [flush_toBits_aligned _ hwf, htoBits]
    have hthis := hdec [] (List.replicate ((8 - B.length % 8) % 8) false)
    rw [List.nil_append] at hthis
    have hwhole : (data.extract 0 data.size).data.toList = data.data.toList := by
      simp only [ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop,
        Nat.sub_zero, List.drop_zero]
      rw [show data.size = data.data.toList.length from by
        rw [Array.length_toList, ByteArray.size_data], List.take_length]
    rw [hwhole] at hthis
    exact hthis

/-- Block-splitting roundtrip: inflating `deflateDynamicBlocksSC` recovers the
    input, for any `maxOutputSize` large enough to hold it. -/
theorem inflate_deflateDynamicBlocksSC (data : ByteArray) (chunkSize : Nat) (level : UInt8)
    (maxOutputSize : Nat) (hsize : data.size ≤ maxOutputSize) :
    Zip.Native.Inflate.inflate (deflateDynamicBlocksSC data chunkSize level) maxOutputSize =
      .ok data := by
  have hlen : data.data.toList.length ≤ maxOutputSize := by
    simp only [Array.length_toList, ByteArray.size_data]; omega
  rw [← show ByteArray.mk ⟨data.data.toList⟩ = data from by simp only [Array.toArray_toList]]
  exact inflate_complete (deflateDynamicBlocksSC data chunkSize level) data.data.toList
    maxOutputSize hlen (decode_deflateDynamicBlocksSC data chunkSize level)

/-- The `decode.goR` of `deflateDynamicBlocksSC` returns the input and short
    (< 8-bit) trailing padding — the block-split analogue of
    `deflateDynamicBlock_goR_pad`, needed to show the native decoder consumes all
    of the deflated bytes. -/
theorem deflateDynamicBlocksSC_goR_pad (data : ByteArray) (chunkSize : Nat) (level : UInt8) :
    ∃ remaining,
      Deflate.Spec.decode.goR
          (Deflate.Spec.bytesToBits (deflateDynamicBlocksSC data chunkSize level)) []
        = some (data.data.toList, remaining) ∧ remaining.length < 8 := by
  unfold deflateDynamicBlocksSC
  split
  · -- data.size = 0
    rename_i hz
    rw [beq_iff_eq] at hz
    obtain ⟨litLens, distLens, headerBits, symBits, _, _, hlv, hdv,
        hge1, hle1, hge2, hle2, hb1, hb2, htrees, hsyms, htoBits, hwf⟩ :=
      emitDynBlock_spec BitWriter.empty BitWriter.empty_wf data #[] (by simp) (fun _ => rfl) true
    rw [BitWriter.empty_toBits, List.nil_append] at htoBits
    rw [flush_toBits_aligned _ hwf, htoBits]
    refine ⟨List.replicate
      ((8 - ([true, false, true] ++ headerBits ++ symBits).length % 8) % 8) false, ?_, ?_⟩
    · have hheader := Deflate.Spec.encodeDynamicTrees_decodeDynamicTables litLens distLens headerBits
        (symBits ++ List.replicate
          ((8 - ([true, false, true] ++ headerBits ++ symBits).length % 8) % 8) false)
        hb1 hb2 ⟨hge1, hle1⟩ ⟨hge2, hle2⟩ hlv hdv htrees
      rw [← List.append_assoc] at hheader
      have hres : Deflate.Spec.resolveLZ77 (tokensToSymbols #[]) [] = some data.data.toList := by
        have he : data.data.toList = [] :=
          List.eq_nil_of_length_eq_zero (by simp only [Array.length_toList, ByteArray.size_data, hz])
        rw [he]; rfl
      exact Deflate.Spec.encodeDynamic_goR_rest (tokensToSymbols #[]) data.data.toList
        litLens distLens headerBits symBits _ hlv hdv hheader hsyms hres
        (tokensToSymbols_validSymbolList _)
    · simp only [List.length_replicate]; omega
  · -- data.size > 0
    rename_i hz
    have hpos : 0 < data.size := by
      rcases Nat.eq_zero_or_pos data.size with h | h
      · rw [h] at hz; simp at hz
      · exact h
    obtain ⟨B, htoBits, hwf, hdec⟩ :=
      emitChunkBlocks_decodeR data chunkSize level data.size 0 BitWriter.empty
        (by omega) hpos BitWriter.empty_wf
    rw [BitWriter.empty_toBits, List.nil_append] at htoBits
    rw [flush_toBits_aligned _ hwf, htoBits]
    refine ⟨List.replicate ((8 - B.length % 8) % 8) false, ?_, ?_⟩
    · have hthis := hdec [] (List.replicate ((8 - B.length % 8) % 8) false)
      have hwhole : (data.extract 0 data.size).data.toList = data.data.toList := by
        simp only [ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop,
          Nat.sub_zero, List.drop_zero]
        rw [show data.size = data.data.toList.length from by
          rw [Array.length_toList, ByteArray.size_data], List.take_length]
      rw [List.nil_append, hwhole] at hthis
      exact hthis
    · simp only [List.length_replicate]; omega

/-- The output of `deflateDynamicBlocksSC` decomposes into content bits plus
    short (< 8-bit) padding — the block-split analogue of `deflateCompressed_pad`. -/
theorem deflateDynamicBlocksSC_pad (data : ByteArray) (chunkSize : Nat) (level : UInt8) :
    ∃ (contentBits padding : List Bool),
      Deflate.Spec.bytesToBits (deflateDynamicBlocksSC data chunkSize level) =
        contentBits ++ padding ∧ padding.length < 8 := by
  unfold deflateDynamicBlocksSC
  split
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hwf⟩ :=
      emitDynBlock_spec BitWriter.empty BitWriter.empty_wf data #[] (by simp) (fun _ => rfl) true
    exact ⟨_, _, flush_toBits_aligned _ hwf, by simp only [List.length_replicate]; omega⟩
  · rename_i hz
    have hpos : 0 < data.size := by
      rcases Nat.eq_zero_or_pos data.size with h | h
      · rw [h] at hz; simp at hz
      · exact h
    obtain ⟨B, _, hwf, _⟩ :=
      emitChunkBlocks_decode data chunkSize level data.size 0 BitWriter.empty
        (by omega) hpos BitWriter.empty_wf
    exact ⟨_, _, flush_toBits_aligned _ hwf, by simp only [List.length_replicate]; omega⟩

end Zip.Native.Deflate
