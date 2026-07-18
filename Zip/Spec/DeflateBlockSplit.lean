import Zip.Spec.DeflateFixedCorrect
import Zip.Spec.DeflateDynamicCorrect
import Zip.Spec.LZ77ChainCorrect
import Zip.Spec.LZ77ChainLazyCorrect
import Zip.Spec.LZ77OptimalCorrect

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
so the `8 ≤ level`/`4 ≤ level` split lives in exactly one place. -/

theorem lzMatch_encodable (data : ByteArray) (level : UInt8) :
    ∀ t ∈ (lzMatch data level).toList,
      match t with
      | .literal _ => True
      | .reference len dist => 3 ≤ len ∧ len ≤ 258 ∧ 1 ≤ dist ∧ dist ≤ 32768 := by
  unfold lzMatch
  split
  · exact lz77ChainLazyIter_encodable data (chainDepth level) 32768 (insertCap level) (goodMatch level) (niceLen level) (lazyDepth level) (useH3Level level) (lazy2StepsLevel level)
      (by omega) (by omega)
  · exact lz77ChainIter_encodable data (chainDepth level) 32768 (insertCap level) (niceLen level)
      (by omega) (by omega)

theorem lzMatch_empty (data : ByteArray) (level : UInt8) (hz : data.size = 0) :
    lzMatch data level = #[] := by
  unfold lzMatch
  split
  · exact lz77ChainLazyIter_empty data (chainDepth level) 32768 (insertCap level) (goodMatch level) (niceLen level) (lazyDepth level) (useH3Level level) (lazy2StepsLevel level) hz
  · exact lz77ChainIter_empty data (chainDepth level) 32768 (insertCap level) (niceLen level) hz

theorem lzMatch_resolves (data : ByteArray) (level : UInt8) :
    Deflate.Spec.resolveLZ77 (tokensToSymbols (lzMatch data level)) [] =
      some data.data.toList := by
  unfold lzMatch
  split
  · exact lz77ChainLazyIter_resolves data (chainDepth level) 32768 (insertCap level) (goodMatch level) (niceLen level) (lazyDepth level) (useH3Level level) (lazy2StepsLevel level) (by omega)
  · exact lz77ChainIter_resolves data (chainDepth level) 32768 (insertCap level) (niceLen level) (by omega)

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
      (lzMatch (data.extract pos j) level)
      (lzMatch_encodable (data.extract pos j) level)
      (fun hz => lzMatch_empty (data.extract pos j) level hz)
      isFinal
  have hresolve := lzMatch_resolves (data.extract pos j) level
  have hvalid := tokensToSymbols_validSymbolList
    (lzMatch (data.extract pos j) level)
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

/-! ## Cross-block (shared-window) block-split roundtrip

`deflateDynamicBlocksShared` matches the whole input *once* (full 32 KiB window),
then partitions the single token stream into per-block groups whose
back-references may reach into earlier blocks. Unlike the self-contained fold,
the per-tail output is *acc-dependent*, so the fold threads the concrete
accumulated output and supplies each block an acc-threaded resolve fact, peeled
off the whole-stream resolve via `resolveLZ77_append_eobFree`. -/

set_option maxHeartbeats 800000 in
/-- One shared-window block: its bits append to `bw`, it preserves `wf`, and given
    the acc-threaded resolve `resolveLZ77 (tokensToSymbols group) accOut = some out`,
    `decode.go`/`decode.goR` consume it — returning `out` (final) or continuing on
    the trailing bits from `out` (non-final). -/
theorem emitSharedBlock_decode (data : ByteArray) (group : Array LZ77Token)
    (bw : BitWriter) (hbw : bw.wf) (isFinal : Bool) (hdata : data.size ≠ 0)
    (hgenc : ∀ t ∈ group.toList,
      match t with
      | .literal _ => True
      | .reference len dist => 3 ≤ len ∧ len ≤ 258 ∧ 1 ≤ dist ∧ dist ≤ 32768)
    (accOut out : List UInt8)
    (hres : Deflate.Spec.resolveLZ77 (tokensToSymbols group) accOut = some out) :
    ∃ blockBits,
      (emitSharedBlock bw data group isFinal).toBits = bw.toBits ++ blockBits ∧
      (emitSharedBlock bw data group isFinal).wf ∧
      (∀ (rest : List Bool),
        Deflate.Spec.decode.go (blockBits ++ rest) accOut =
          if isFinal then some out else Deflate.Spec.decode.go rest out) ∧
      (∀ (rest : List Bool),
        Deflate.Spec.decode.goR (blockBits ++ rest) accOut =
          if isFinal then some (out, rest) else Deflate.Spec.decode.goR rest out) := by
  obtain ⟨litLens, distLens, headerBits, symBits, _hll, _hdl, hlv, hdv,
      hge1, hle1, hge2, hle2, hb1, hb2, htrees, hsyms, htoBits, hwf⟩ :=
    emitDynBlock_spec bw hbw data group hgenc (fun hz => absurd hz hdata) isFinal
  have hvalid := tokensToSymbols_validSymbolList group
  refine ⟨[isFinal, false, true] ++ headerBits ++ symBits, ?_, ?_, ?_, ?_⟩
  · simp only [emitSharedBlock]; rw [htoBits]; simp only [List.append_assoc]
  · simp only [emitSharedBlock]; exact hwf
  · intro rest
    have hheader := Deflate.Spec.encodeDynamicTrees_decodeDynamicTables
      litLens distLens headerBits (symBits ++ rest) hb1 hb2 ⟨hge1, hle1⟩ ⟨hge2, hle2⟩ hlv hdv htrees
    rw [← List.append_assoc] at hheader
    cases isFinal
    · simp only [Bool.false_eq_true, if_false]
      exact Deflate.Spec.decode_go_dynBlock_nonfinal_acc _ out accOut litLens distLens
        headerBits symBits rest hlv hdv hheader hsyms hres hvalid
    · simp only [if_true]
      exact Deflate.Spec.decode_go_dynBlock_final_acc _ out accOut litLens distLens
        headerBits symBits rest hlv hdv hheader hsyms hres hvalid
  · intro rest
    have hheader := Deflate.Spec.encodeDynamicTrees_decodeDynamicTables
      litLens distLens headerBits (symBits ++ rest) hb1 hb2 ⟨hge1, hle1⟩ ⟨hge2, hle2⟩ hlv hdv htrees
    rw [← List.append_assoc] at hheader
    cases isFinal
    · simp only [Bool.false_eq_true, if_false]
      exact Deflate.Spec.decode_goR_dynBlock_nonfinal_acc _ out accOut litLens distLens
        headerBits symBits rest hlv hdv hheader hsyms hres hvalid
    · simp only [if_true]
      exact Deflate.Spec.decode_goR_dynBlock_final_acc _ out accOut litLens distLens
        headerBits symBits rest hlv hdv hheader hsyms hres hvalid

/-- Membership in an extracted token array's `toList` is membership in the whole. -/
private theorem mem_extract_toList {α} (a : Array α) (s e : Nat) (x : α)
    (h : x ∈ (a.extract s e).toList) : x ∈ a.toList := by
  rw [Array.toList_extract, List.extract_eq_take_drop] at h
  exact List.mem_of_mem_drop (List.mem_of_mem_take h)

/-- Decode fold over the shared-window blocks: from token index `pos < toks.size`,
    with `accOut` the output of blocks `0..pos` and the residual resolve fact
    `resolveLZ77 (drop pos of the mapped tokens) accOut = some wholeOut`, the bits
    emitted by `emitSharedBlocks` (with `bw`'s bits stripped as `B`) decode — from
    `accOut` — to `wholeOut`. The last block is final, so it returns regardless of
    the trailing `tail`. -/
theorem emitSharedBlocks_decode (data : ByteArray) (toks : Array LZ77Token) (tokChunk : Nat)
    (hdata : data.size ≠ 0)
    (henc : ∀ t ∈ toks.toList,
      match t with
      | .literal _ => True
      | .reference len dist => 3 ≤ len ∧ len ≤ 258 ∧ 1 ≤ dist ∧ dist ≤ 32768) :
    ∀ (fuel pos : Nat) (accOut wholeOut : List UInt8) (bw : BitWriter),
      toks.size - pos ≤ fuel → pos < toks.size → bw.wf →
      Deflate.Spec.resolveLZ77 ((toks.toList.map LZ77Token.toLZ77Symbol).drop pos) accOut =
        some wholeOut →
      ∃ B, (emitSharedBlocks data toks tokChunk pos bw).toBits = bw.toBits ++ B ∧
        (emitSharedBlocks data toks tokChunk pos bw).wf ∧
        ∀ (tail : List Bool),
          Deflate.Spec.decode.go (B ++ tail) accOut = some wholeOut := by
  intro fuel
  induction fuel with
  | zero => intro pos accOut wholeOut bw hf hpos _ _; omega
  | succ fuel ih =>
    intro pos accOut wholeOut bw hf hpos hbw hres
    have hjle : min (pos + max tokChunk 1) toks.size ≤ toks.size := Nat.min_le_right _ _
    have hstep1 : 1 ≤ max tokChunk 1 := Nat.le_max_right _ _
    have hjgt : pos < min (pos + max tokChunk 1) toks.size := by simp only [Nat.lt_min]; omega
    have hMfree : ∀ s ∈ toks.toList.map LZ77Token.toLZ77Symbol,
        s ≠ Deflate.Spec.LZ77Symbol.endOfBlock := mem_map_toLZ77Symbol_ne_endOfBlock toks.toList
    have hgmfree : ∀ s ∈ ((toks.toList.map LZ77Token.toLZ77Symbol).drop pos).take
        (min (pos + max tokChunk 1) toks.size - pos), s ≠ Deflate.Spec.LZ77Symbol.endOfBlock :=
      fun s hs => hMfree s (List.mem_of_mem_drop (List.mem_of_mem_take hs))
    -- Split the residual at the partition point.
    have hsplit : (toks.toList.map LZ77Token.toLZ77Symbol).drop pos =
        ((toks.toList.map LZ77Token.toLZ77Symbol).drop pos).take
          (min (pos + max tokChunk 1) toks.size - pos)
        ++ (toks.toList.map LZ77Token.toLZ77Symbol).drop (min (pos + max tokChunk 1) toks.size) := by
      conv => lhs; rw [← List.take_append_drop (min (pos + max tokChunk 1) toks.size - pos)
        ((toks.toList.map LZ77Token.toLZ77Symbol).drop pos)]
      rw [List.drop_drop, show pos + (min (pos + max tokChunk 1) toks.size - pos)
        = min (pos + max tokChunk 1) toks.size from by omega]
    rw [hsplit, Deflate.Spec.resolveLZ77_append_eobFree _ _ accOut hgmfree] at hres
    -- Peel off the block's resolve and the recursive residual.
    obtain ⟨out', hout'1, hout'2⟩ :
        ∃ out', Deflate.Spec.resolveLZ77 (((toks.toList.map LZ77Token.toLZ77Symbol).drop pos).take
            (min (pos + max tokChunk 1) toks.size - pos)) accOut = some out' ∧
          Deflate.Spec.resolveLZ77 ((toks.toList.map LZ77Token.toLZ77Symbol).drop
            (min (pos + max tokChunk 1) toks.size)) out' = some wholeOut := by
      cases hgm : Deflate.Spec.resolveLZ77 (((toks.toList.map LZ77Token.toLZ77Symbol).drop pos).take
          (min (pos + max tokChunk 1) toks.size - pos)) accOut with
      | none => rw [hgm] at hres; simp only [Option.bind_none, reduceCtorEq] at hres
      | some o => rw [hgm] at hres; exact ⟨o, rfl, hres⟩
    -- The block's symbol list resolves against `accOut` to `out'`.
    have htts : tokensToSymbols (toks.extract pos (min (pos + max tokChunk 1) toks.size)) =
        ((toks.toList.map LZ77Token.toLZ77Symbol).drop pos).take
          (min (pos + max tokChunk 1) toks.size - pos)
        ++ [Deflate.Spec.LZ77Symbol.endOfBlock] := by
      unfold tokensToSymbols
      congr 1
      simp only [Array.toList_extract, List.extract_eq_take_drop, List.map_take, List.map_drop]
    have hblockres : Deflate.Spec.resolveLZ77
        (tokensToSymbols (toks.extract pos (min (pos + max tokChunk 1) toks.size))) accOut =
        some out' := by
      rw [htts, Deflate.Spec.resolveLZ77_eobFree_eob _ accOut hgmfree]; exact hout'1
    obtain ⟨blockBits, htoBits, hwfblk, hdecblk, _⟩ :=
      emitSharedBlock_decode data (toks.extract pos (min (pos + max tokChunk 1) toks.size)) bw hbw
        (decide (min (pos + max tokChunk 1) toks.size ≥ toks.size)) hdata
        (fun t ht => henc t (mem_extract_toList toks pos _ t ht)) accOut out' hblockres
    by_cases hend : min (pos + max tokChunk 1) toks.size ≥ toks.size
    · -- Final block: j = toks.size, so the residual forces `out' = wholeOut`.
      have hjeq : min (pos + max tokChunk 1) toks.size = toks.size := by omega
      have hdropnil : (toks.toList.map LZ77Token.toLZ77Symbol).drop
          (min (pos + max tokChunk 1) toks.size) = [] := by
        rw [hjeq, show toks.size = (toks.toList.map LZ77Token.toLZ77Symbol).length from by
          rw [List.length_map, Array.length_toList], List.drop_length]
      have hwo : out' = wholeOut := by
        rw [hdropnil, Deflate.Spec.resolveLZ77_nil, Option.some.injEq] at hout'2; exact hout'2
      have hstep : emitSharedBlocks data toks tokChunk pos bw =
          emitSharedBlock bw data (toks.extract pos (min (pos + max tokChunk 1) toks.size))
            (decide (min (pos + max tokChunk 1) toks.size ≥ toks.size)) := by
        conv => lhs; unfold emitSharedBlocks
        simp only [if_pos hend]
      refine ⟨blockBits, ?_, ?_, ?_⟩
      · rw [hstep]; exact htoBits
      · rw [hstep]; exact hwfblk
      · intro tail
        have hd := hdecblk tail
        rw [if_pos (decide_eq_true hend)] at hd
        rw [hd, hwo]
    · -- Non-final block: recurse on the next token group.
      have hbw' : (emitSharedBlock bw data (toks.extract pos (min (pos + max tokChunk 1) toks.size))
          (decide (min (pos + max tokChunk 1) toks.size ≥ toks.size))).wf := hwfblk
      have hstep : emitSharedBlocks data toks tokChunk pos bw =
          emitSharedBlocks data toks tokChunk (min (pos + max tokChunk 1) toks.size)
            (emitSharedBlock bw data (toks.extract pos (min (pos + max tokChunk 1) toks.size))
              (decide (min (pos + max tokChunk 1) toks.size ≥ toks.size))) := by
        conv => lhs; unfold emitSharedBlocks
        simp only [if_neg hend]
      obtain ⟨B', htoBits', hwf', hdec'⟩ :=
        ih (min (pos + max tokChunk 1) toks.size) out' wholeOut _ (by omega) (by omega) hbw' hout'2
      refine ⟨blockBits ++ B', ?_, ?_, ?_⟩
      · rw [hstep, htoBits', htoBits, List.append_assoc]
      · rw [hstep]; exact hwf'
      · intro tail
        rw [List.append_assoc]
        have hd := hdecblk (B' ++ tail)
        rw [if_neg (by simp only [decide_eq_true_eq]; exact hend)] at hd
        rw [hd]; exact hdec' tail

/-- `decode.goR` variant of `emitSharedBlocks_decode`: the remaining bits after
    decoding all shared blocks are exactly the trailing `tail`. -/
theorem emitSharedBlocks_decodeR (data : ByteArray) (toks : Array LZ77Token) (tokChunk : Nat)
    (hdata : data.size ≠ 0)
    (henc : ∀ t ∈ toks.toList,
      match t with
      | .literal _ => True
      | .reference len dist => 3 ≤ len ∧ len ≤ 258 ∧ 1 ≤ dist ∧ dist ≤ 32768) :
    ∀ (fuel pos : Nat) (accOut wholeOut : List UInt8) (bw : BitWriter),
      toks.size - pos ≤ fuel → pos < toks.size → bw.wf →
      Deflate.Spec.resolveLZ77 ((toks.toList.map LZ77Token.toLZ77Symbol).drop pos) accOut =
        some wholeOut →
      ∃ B, (emitSharedBlocks data toks tokChunk pos bw).toBits = bw.toBits ++ B ∧
        (emitSharedBlocks data toks tokChunk pos bw).wf ∧
        ∀ (tail : List Bool),
          Deflate.Spec.decode.goR (B ++ tail) accOut = some (wholeOut, tail) := by
  intro fuel
  induction fuel with
  | zero => intro pos accOut wholeOut bw hf hpos _ _; omega
  | succ fuel ih =>
    intro pos accOut wholeOut bw hf hpos hbw hres
    have hjle : min (pos + max tokChunk 1) toks.size ≤ toks.size := Nat.min_le_right _ _
    have hstep1 : 1 ≤ max tokChunk 1 := Nat.le_max_right _ _
    have hjgt : pos < min (pos + max tokChunk 1) toks.size := by simp only [Nat.lt_min]; omega
    have hMfree : ∀ s ∈ toks.toList.map LZ77Token.toLZ77Symbol,
        s ≠ Deflate.Spec.LZ77Symbol.endOfBlock := mem_map_toLZ77Symbol_ne_endOfBlock toks.toList
    have hgmfree : ∀ s ∈ ((toks.toList.map LZ77Token.toLZ77Symbol).drop pos).take
        (min (pos + max tokChunk 1) toks.size - pos), s ≠ Deflate.Spec.LZ77Symbol.endOfBlock :=
      fun s hs => hMfree s (List.mem_of_mem_drop (List.mem_of_mem_take hs))
    have hsplit : (toks.toList.map LZ77Token.toLZ77Symbol).drop pos =
        ((toks.toList.map LZ77Token.toLZ77Symbol).drop pos).take
          (min (pos + max tokChunk 1) toks.size - pos)
        ++ (toks.toList.map LZ77Token.toLZ77Symbol).drop (min (pos + max tokChunk 1) toks.size) := by
      conv => lhs; rw [← List.take_append_drop (min (pos + max tokChunk 1) toks.size - pos)
        ((toks.toList.map LZ77Token.toLZ77Symbol).drop pos)]
      rw [List.drop_drop, show pos + (min (pos + max tokChunk 1) toks.size - pos)
        = min (pos + max tokChunk 1) toks.size from by omega]
    rw [hsplit, Deflate.Spec.resolveLZ77_append_eobFree _ _ accOut hgmfree] at hres
    obtain ⟨out', hout'1, hout'2⟩ :
        ∃ out', Deflate.Spec.resolveLZ77 (((toks.toList.map LZ77Token.toLZ77Symbol).drop pos).take
            (min (pos + max tokChunk 1) toks.size - pos)) accOut = some out' ∧
          Deflate.Spec.resolveLZ77 ((toks.toList.map LZ77Token.toLZ77Symbol).drop
            (min (pos + max tokChunk 1) toks.size)) out' = some wholeOut := by
      cases hgm : Deflate.Spec.resolveLZ77 (((toks.toList.map LZ77Token.toLZ77Symbol).drop pos).take
          (min (pos + max tokChunk 1) toks.size - pos)) accOut with
      | none => rw [hgm] at hres; simp only [Option.bind_none, reduceCtorEq] at hres
      | some o => rw [hgm] at hres; exact ⟨o, rfl, hres⟩
    have htts : tokensToSymbols (toks.extract pos (min (pos + max tokChunk 1) toks.size)) =
        ((toks.toList.map LZ77Token.toLZ77Symbol).drop pos).take
          (min (pos + max tokChunk 1) toks.size - pos)
        ++ [Deflate.Spec.LZ77Symbol.endOfBlock] := by
      unfold tokensToSymbols
      congr 1
      simp only [Array.toList_extract, List.extract_eq_take_drop, List.map_take, List.map_drop]
    have hblockres : Deflate.Spec.resolveLZ77
        (tokensToSymbols (toks.extract pos (min (pos + max tokChunk 1) toks.size))) accOut =
        some out' := by
      rw [htts, Deflate.Spec.resolveLZ77_eobFree_eob _ accOut hgmfree]; exact hout'1
    obtain ⟨blockBits, htoBits, hwfblk, _, hdecblk⟩ :=
      emitSharedBlock_decode data (toks.extract pos (min (pos + max tokChunk 1) toks.size)) bw hbw
        (decide (min (pos + max tokChunk 1) toks.size ≥ toks.size)) hdata
        (fun t ht => henc t (mem_extract_toList toks pos _ t ht)) accOut out' hblockres
    by_cases hend : min (pos + max tokChunk 1) toks.size ≥ toks.size
    · have hjeq : min (pos + max tokChunk 1) toks.size = toks.size := by omega
      have hdropnil : (toks.toList.map LZ77Token.toLZ77Symbol).drop
          (min (pos + max tokChunk 1) toks.size) = [] := by
        rw [hjeq, show toks.size = (toks.toList.map LZ77Token.toLZ77Symbol).length from by
          rw [List.length_map, Array.length_toList], List.drop_length]
      have hwo : out' = wholeOut := by
        rw [hdropnil, Deflate.Spec.resolveLZ77_nil, Option.some.injEq] at hout'2; exact hout'2
      have hstep : emitSharedBlocks data toks tokChunk pos bw =
          emitSharedBlock bw data (toks.extract pos (min (pos + max tokChunk 1) toks.size))
            (decide (min (pos + max tokChunk 1) toks.size ≥ toks.size)) := by
        conv => lhs; unfold emitSharedBlocks
        simp only [if_pos hend]
      refine ⟨blockBits, ?_, ?_, ?_⟩
      · rw [hstep]; exact htoBits
      · rw [hstep]; exact hwfblk
      · intro tail
        have hd := hdecblk tail
        rw [if_pos (decide_eq_true hend)] at hd
        rw [hd, hwo]
    · have hbw' : (emitSharedBlock bw data (toks.extract pos (min (pos + max tokChunk 1) toks.size))
          (decide (min (pos + max tokChunk 1) toks.size ≥ toks.size))).wf := hwfblk
      have hstep : emitSharedBlocks data toks tokChunk pos bw =
          emitSharedBlocks data toks tokChunk (min (pos + max tokChunk 1) toks.size)
            (emitSharedBlock bw data (toks.extract pos (min (pos + max tokChunk 1) toks.size))
              (decide (min (pos + max tokChunk 1) toks.size ≥ toks.size))) := by
        conv => lhs; unfold emitSharedBlocks
        simp only [if_neg hend]
      obtain ⟨B', htoBits', hwf', hdec'⟩ :=
        ih (min (pos + max tokChunk 1) toks.size) out' wholeOut _ (by omega) (by omega) hbw' hout'2
      refine ⟨blockBits ++ B', ?_, ?_, ?_⟩
      · rw [hstep, htoBits', htoBits, List.append_assoc]
      · rw [hstep]; exact hwf'
      · intro tail
        rw [List.append_assoc]
        have hd := hdecblk (B' ++ tail)
        rw [if_neg (by simp only [decide_eq_true_eq]; exact hend)] at hd
        rw [hd]; exact hdec' tail

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
    Zip.Native.Inflate.inflateReference (deflateDynamicBlocksSC data chunkSize level) maxOutputSize =
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

/-! ## Cross-block (shared-window) top-level roundtrip -/

/-- Common facts for the `data.size > 0` branch of the shared-window theorems:
    the whole-stream token list is non-empty and its mapped form resolves (from
    `[]`, drop 0) to the input. Derived from `lzMatch_resolves`. -/
private theorem deflateDynamicBlocksShared_facts (data : ByteArray) (level : UInt8)
    (hpos : 0 < data.size) :
    (∀ t ∈ (lzMatch data level).toList,
        match t with
        | .literal _ => True
        | .reference len dist => 3 ≤ len ∧ len ≤ 258 ∧ 1 ≤ dist ∧ dist ≤ 32768) ∧
      0 < (lzMatch data level).size ∧
      Deflate.Spec.resolveLZ77
        (((lzMatch data level).toList.map
          LZ77Token.toLZ77Symbol).drop 0) [] = some data.data.toList := by
  have henc := lzMatch_encodable data level
  have hwhole := lzMatch_resolves data level
  have hMfree := mem_map_toLZ77Symbol_ne_endOfBlock
    (lzMatch data level).toList
  have hM : Deflate.Spec.resolveLZ77
      ((lzMatch data level).toList.map
        LZ77Token.toLZ77Symbol) [] = some data.data.toList := by
    simp only [tokensToSymbols] at hwhole
    rwa [Deflate.Spec.resolveLZ77_eobFree_eob _ [] hMfree] at hwhole
  refine ⟨henc, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos
      (lzMatch data level).size with h0 | h0
    · exfalso
      have hnil : (lzMatch data level).toList = [] :=
        List.eq_nil_of_length_eq_zero (by rw [Array.length_toList]; omega)
      rw [hnil, List.map_nil, Deflate.Spec.resolveLZ77_nil, Option.some.injEq] at hM
      have hl := congrArg List.length hM
      simp only [List.length_nil, Array.length_toList, ByteArray.size_data] at hl
      omega
    · exact h0
  · rw [List.drop_zero]; exact hM

/-- Cross-block roundtrip: decoding the shared-window block stream reproduces the
    input. The empty input is a single final block; otherwise the shared-window
    fold (`emitSharedBlocks_decode`), seeded by `lzMatch_resolves`,
    reconstructs the input. -/
theorem decode_deflateDynamicBlocksShared (data : ByteArray) (tokChunk : Nat) (level : UInt8) :
    Deflate.Spec.decode
      (Deflate.Spec.bytesToBits (deflateDynamicBlocksShared data tokChunk level)) =
      some data.data.toList := by
  unfold deflateDynamicBlocksShared
  split
  · -- data.size = 0: one final block over the empty token list (as in SC).
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
  · -- data.size > 0: the shared-window fold.
    rename_i hz
    have hpos : 0 < data.size := by
      rcases Nat.eq_zero_or_pos data.size with h | h
      · rw [h] at hz; simp at hz
      · exact h
    obtain ⟨henc, htokpos, hres0⟩ := deflateDynamicBlocksShared_facts data level hpos
    obtain ⟨B, htoBits, hwf, hdec⟩ :=
      emitSharedBlocks_decode data (lzMatch data level)
        tokChunk (by omega) henc
        (lzMatch data level).size 0 []
        data.data.toList BitWriter.empty (by omega) htokpos BitWriter.empty_wf hres0
    rw [BitWriter.empty_toBits, List.nil_append] at htoBits
    rw [flush_toBits_aligned _ hwf, htoBits]
    exact hdec (List.replicate ((8 - B.length % 8) % 8) false)

/-- Cross-block roundtrip: inflating `deflateDynamicBlocksShared` recovers the
    input, for any `maxOutputSize` large enough to hold it. -/
theorem inflate_deflateDynamicBlocksShared (data : ByteArray) (tokChunk : Nat) (level : UInt8)
    (maxOutputSize : Nat) (hsize : data.size ≤ maxOutputSize) :
    Zip.Native.Inflate.inflateReference (deflateDynamicBlocksShared data tokChunk level) maxOutputSize =
      .ok data := by
  have hlen : data.data.toList.length ≤ maxOutputSize := by
    simp only [Array.length_toList, ByteArray.size_data]; omega
  rw [← show ByteArray.mk ⟨data.data.toList⟩ = data from by simp only [Array.toArray_toList]]
  exact inflate_complete (deflateDynamicBlocksShared data tokChunk level) data.data.toList
    maxOutputSize hlen (decode_deflateDynamicBlocksShared data tokChunk level)

/-- The `decode.goR` of `deflateDynamicBlocksShared` returns the input and short
    (< 8-bit) trailing padding — needed to show the native decoder consumes all
    of the deflated bytes. -/
theorem deflateDynamicBlocksShared_goR_pad (data : ByteArray) (tokChunk : Nat) (level : UInt8) :
    ∃ remaining,
      Deflate.Spec.decode.goR
          (Deflate.Spec.bytesToBits (deflateDynamicBlocksShared data tokChunk level)) []
        = some (data.data.toList, remaining) ∧ remaining.length < 8 := by
  unfold deflateDynamicBlocksShared
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
    obtain ⟨henc, htokpos, hres0⟩ := deflateDynamicBlocksShared_facts data level hpos
    obtain ⟨B, htoBits, hwf, hdec⟩ :=
      emitSharedBlocks_decodeR data (lzMatch data level)
        tokChunk (by omega) henc
        (lzMatch data level).size 0 []
        data.data.toList BitWriter.empty (by omega) htokpos BitWriter.empty_wf hres0
    rw [BitWriter.empty_toBits, List.nil_append] at htoBits
    rw [flush_toBits_aligned _ hwf, htoBits]
    refine ⟨List.replicate ((8 - B.length % 8) % 8) false, hdec _, ?_⟩
    simp only [List.length_replicate]; omega

/-- The output of `deflateDynamicBlocksShared` decomposes into content bits plus
    short (< 8-bit) padding. -/
theorem deflateDynamicBlocksShared_pad (data : ByteArray) (tokChunk : Nat) (level : UInt8) :
    ∃ (contentBits padding : List Bool),
      Deflate.Spec.bytesToBits (deflateDynamicBlocksShared data tokChunk level) =
        contentBits ++ padding ∧ padding.length < 8 := by
  unfold deflateDynamicBlocksShared
  split
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hwf⟩ :=
      emitDynBlock_spec BitWriter.empty BitWriter.empty_wf data #[] (by simp) (fun _ => rfl) true
    exact ⟨_, _, flush_toBits_aligned _ hwf, by simp only [List.length_replicate]; omega⟩
  · rename_i hz
    have hpos : 0 < data.size := by
      rcases Nat.eq_zero_or_pos data.size with h | h
      · rw [h] at hz; simp at hz
      · exact h
    obtain ⟨henc, htokpos, hres0⟩ := deflateDynamicBlocksShared_facts data level hpos
    obtain ⟨B, _, hwf, _⟩ :=
      emitSharedBlocks_decode data (lzMatch data level)
        tokChunk (by omega) henc
        (lzMatch data level).size 0 []
        data.data.toList BitWriter.empty (by omega) htokpos BitWriter.empty_wf hres0
    exact ⟨_, _, flush_toBits_aligned _ hwf, by simp only [List.length_replicate]; omega⟩

/-! ## Cut-list (heuristic-partition) shared-window roundtrip

`emitSharedBlocksAt` consumes an explicit cut list instead of a fixed cadence;
every cut is clamped to `(pos, toks.size]`, so the theorems below hold for an
**arbitrary** `cuts : List Nat` — the boundary heuristic carries no proof
obligations. The proofs are the `emitSharedBlocks` proofs with the cut point
`min (pos + max tokChunk 1) toks.size` replaced by
`min (max (cuts.headD toks.size) (pos + 1)) toks.size` (the only facts used
about it are `pos < j ≤ toks.size` and the final-block test). -/

/-- Decode fold over the cut-list shared-window blocks: `emitSharedBlocksAt`
    analogue of `emitSharedBlocks_decode`, for an arbitrary cut list. -/
theorem emitSharedBlocksAt_decode (data : ByteArray) (toks : Array LZ77Token)
    (hdata : data.size ≠ 0)
    (henc : ∀ t ∈ toks.toList,
      match t with
      | .literal _ => True
      | .reference len dist => 3 ≤ len ∧ len ≤ 258 ∧ 1 ≤ dist ∧ dist ≤ 32768) :
    ∀ (fuel pos : Nat) (cuts : List Nat) (accOut wholeOut : List UInt8) (bw : BitWriter),
      toks.size - pos ≤ fuel → pos < toks.size → bw.wf →
      Deflate.Spec.resolveLZ77 ((toks.toList.map LZ77Token.toLZ77Symbol).drop pos) accOut =
        some wholeOut →
      ∃ B, (emitSharedBlocksAt data toks cuts pos bw).toBits = bw.toBits ++ B ∧
        (emitSharedBlocksAt data toks cuts pos bw).wf ∧
        ∀ (tail : List Bool),
          Deflate.Spec.decode.go (B ++ tail) accOut = some wholeOut := by
  intro fuel
  induction fuel with
  | zero => intro pos cuts accOut wholeOut bw hf hpos _ _; omega
  | succ fuel ih =>
    intro pos cuts accOut wholeOut bw hf hpos hbw hres
    have hjle : min (max (cuts.headD toks.size) (pos + 1)) toks.size ≤ toks.size :=
      Nat.min_le_right _ _
    have hstep1 : pos + 1 ≤ max (cuts.headD toks.size) (pos + 1) := Nat.le_max_right _ _
    have hjgt : pos < min (max (cuts.headD toks.size) (pos + 1)) toks.size := by
      simp only [Nat.lt_min]; omega
    have hMfree : ∀ s ∈ toks.toList.map LZ77Token.toLZ77Symbol,
        s ≠ Deflate.Spec.LZ77Symbol.endOfBlock := mem_map_toLZ77Symbol_ne_endOfBlock toks.toList
    have hgmfree : ∀ s ∈ ((toks.toList.map LZ77Token.toLZ77Symbol).drop pos).take
        (min (max (cuts.headD toks.size) (pos + 1)) toks.size - pos),
        s ≠ Deflate.Spec.LZ77Symbol.endOfBlock :=
      fun s hs => hMfree s (List.mem_of_mem_drop (List.mem_of_mem_take hs))
    -- Split the residual at the partition point.
    have hsplit : (toks.toList.map LZ77Token.toLZ77Symbol).drop pos =
        ((toks.toList.map LZ77Token.toLZ77Symbol).drop pos).take
          (min (max (cuts.headD toks.size) (pos + 1)) toks.size - pos)
        ++ (toks.toList.map LZ77Token.toLZ77Symbol).drop
          (min (max (cuts.headD toks.size) (pos + 1)) toks.size) := by
      conv => lhs; rw [← List.take_append_drop
        (min (max (cuts.headD toks.size) (pos + 1)) toks.size - pos)
        ((toks.toList.map LZ77Token.toLZ77Symbol).drop pos)]
      rw [List.drop_drop, show pos +
        (min (max (cuts.headD toks.size) (pos + 1)) toks.size - pos)
        = min (max (cuts.headD toks.size) (pos + 1)) toks.size from by omega]
    rw [hsplit, Deflate.Spec.resolveLZ77_append_eobFree _ _ accOut hgmfree] at hres
    -- Peel off the block's resolve and the recursive residual.
    obtain ⟨out', hout'1, hout'2⟩ :
        ∃ out', Deflate.Spec.resolveLZ77 (((toks.toList.map LZ77Token.toLZ77Symbol).drop pos).take
            (min (max (cuts.headD toks.size) (pos + 1)) toks.size - pos)) accOut = some out' ∧
          Deflate.Spec.resolveLZ77 ((toks.toList.map LZ77Token.toLZ77Symbol).drop
            (min (max (cuts.headD toks.size) (pos + 1)) toks.size)) out' = some wholeOut := by
      cases hgm : Deflate.Spec.resolveLZ77 (((toks.toList.map LZ77Token.toLZ77Symbol).drop pos).take
          (min (max (cuts.headD toks.size) (pos + 1)) toks.size - pos)) accOut with
      | none => rw [hgm] at hres; simp only [Option.bind_none, reduceCtorEq] at hres
      | some o => rw [hgm] at hres; exact ⟨o, rfl, hres⟩
    -- The block's symbol list resolves against `accOut` to `out'`.
    have htts : tokensToSymbols
        (toks.extract pos (min (max (cuts.headD toks.size) (pos + 1)) toks.size)) =
        ((toks.toList.map LZ77Token.toLZ77Symbol).drop pos).take
          (min (max (cuts.headD toks.size) (pos + 1)) toks.size - pos)
        ++ [Deflate.Spec.LZ77Symbol.endOfBlock] := by
      unfold tokensToSymbols
      congr 1
      simp only [Array.toList_extract, List.extract_eq_take_drop, List.map_take, List.map_drop]
    have hblockres : Deflate.Spec.resolveLZ77
        (tokensToSymbols
          (toks.extract pos (min (max (cuts.headD toks.size) (pos + 1)) toks.size))) accOut =
        some out' := by
      rw [htts, Deflate.Spec.resolveLZ77_eobFree_eob _ accOut hgmfree]; exact hout'1
    obtain ⟨blockBits, htoBits, hwfblk, hdecblk, _⟩ :=
      emitSharedBlock_decode data
        (toks.extract pos (min (max (cuts.headD toks.size) (pos + 1)) toks.size)) bw hbw
        (decide (min (max (cuts.headD toks.size) (pos + 1)) toks.size ≥ toks.size)) hdata
        (fun t ht => henc t (mem_extract_toList toks pos _ t ht)) accOut out' hblockres
    by_cases hend : min (max (cuts.headD toks.size) (pos + 1)) toks.size ≥ toks.size
    · -- Final block: j = toks.size, so the residual forces `out' = wholeOut`.
      have hjeq : min (max (cuts.headD toks.size) (pos + 1)) toks.size = toks.size := by omega
      have hdropnil : (toks.toList.map LZ77Token.toLZ77Symbol).drop
          (min (max (cuts.headD toks.size) (pos + 1)) toks.size) = [] := by
        rw [hjeq, show toks.size = (toks.toList.map LZ77Token.toLZ77Symbol).length from by
          rw [List.length_map, Array.length_toList], List.drop_length]
      have hwo : out' = wholeOut := by
        rw [hdropnil, Deflate.Spec.resolveLZ77_nil, Option.some.injEq] at hout'2; exact hout'2
      have hstep : emitSharedBlocksAt data toks cuts pos bw =
          emitSharedBlock bw data
            (toks.extract pos (min (max (cuts.headD toks.size) (pos + 1)) toks.size))
            (decide (min (max (cuts.headD toks.size) (pos + 1)) toks.size ≥ toks.size)) := by
        conv => lhs; unfold emitSharedBlocksAt
        simp only [if_pos hend]
      refine ⟨blockBits, ?_, ?_, ?_⟩
      · rw [hstep]; exact htoBits
      · rw [hstep]; exact hwfblk
      · intro tail
        have hd := hdecblk tail
        rw [if_pos (decide_eq_true hend)] at hd
        rw [hd, hwo]
    · -- Non-final block: recurse on the next token group.
      have hbw' : (emitSharedBlock bw data
          (toks.extract pos (min (max (cuts.headD toks.size) (pos + 1)) toks.size))
          (decide (min (max (cuts.headD toks.size) (pos + 1)) toks.size ≥ toks.size))).wf := hwfblk
      have hstep : emitSharedBlocksAt data toks cuts pos bw =
          emitSharedBlocksAt data toks cuts.tail
            (min (max (cuts.headD toks.size) (pos + 1)) toks.size)
            (emitSharedBlock bw data
              (toks.extract pos (min (max (cuts.headD toks.size) (pos + 1)) toks.size))
              (decide (min (max (cuts.headD toks.size) (pos + 1)) toks.size ≥ toks.size))) := by
        conv => lhs; unfold emitSharedBlocksAt
        simp only [if_neg hend]
      obtain ⟨B', htoBits', hwf', hdec'⟩ :=
        ih (min (max (cuts.headD toks.size) (pos + 1)) toks.size) cuts.tail out' wholeOut _
          (by omega) (by omega) hbw' hout'2
      refine ⟨blockBits ++ B', ?_, ?_, ?_⟩
      · rw [hstep, htoBits', htoBits, List.append_assoc]
      · rw [hstep]; exact hwf'
      · intro tail
        rw [List.append_assoc]
        have hd := hdecblk (B' ++ tail)
        rw [if_neg (by simp only [decide_eq_true_eq]; exact hend)] at hd
        rw [hd]; exact hdec' tail

/-- `decode.goR` variant of `emitSharedBlocksAt_decode`: the remaining bits after
    decoding all cut-list shared blocks are exactly the trailing `tail`. -/
theorem emitSharedBlocksAt_decodeR (data : ByteArray) (toks : Array LZ77Token)
    (hdata : data.size ≠ 0)
    (henc : ∀ t ∈ toks.toList,
      match t with
      | .literal _ => True
      | .reference len dist => 3 ≤ len ∧ len ≤ 258 ∧ 1 ≤ dist ∧ dist ≤ 32768) :
    ∀ (fuel pos : Nat) (cuts : List Nat) (accOut wholeOut : List UInt8) (bw : BitWriter),
      toks.size - pos ≤ fuel → pos < toks.size → bw.wf →
      Deflate.Spec.resolveLZ77 ((toks.toList.map LZ77Token.toLZ77Symbol).drop pos) accOut =
        some wholeOut →
      ∃ B, (emitSharedBlocksAt data toks cuts pos bw).toBits = bw.toBits ++ B ∧
        (emitSharedBlocksAt data toks cuts pos bw).wf ∧
        ∀ (tail : List Bool),
          Deflate.Spec.decode.goR (B ++ tail) accOut = some (wholeOut, tail) := by
  intro fuel
  induction fuel with
  | zero => intro pos cuts accOut wholeOut bw hf hpos _ _; omega
  | succ fuel ih =>
    intro pos cuts accOut wholeOut bw hf hpos hbw hres
    have hjle : min (max (cuts.headD toks.size) (pos + 1)) toks.size ≤ toks.size :=
      Nat.min_le_right _ _
    have hstep1 : pos + 1 ≤ max (cuts.headD toks.size) (pos + 1) := Nat.le_max_right _ _
    have hjgt : pos < min (max (cuts.headD toks.size) (pos + 1)) toks.size := by
      simp only [Nat.lt_min]; omega
    have hMfree : ∀ s ∈ toks.toList.map LZ77Token.toLZ77Symbol,
        s ≠ Deflate.Spec.LZ77Symbol.endOfBlock := mem_map_toLZ77Symbol_ne_endOfBlock toks.toList
    have hgmfree : ∀ s ∈ ((toks.toList.map LZ77Token.toLZ77Symbol).drop pos).take
        (min (max (cuts.headD toks.size) (pos + 1)) toks.size - pos),
        s ≠ Deflate.Spec.LZ77Symbol.endOfBlock :=
      fun s hs => hMfree s (List.mem_of_mem_drop (List.mem_of_mem_take hs))
    have hsplit : (toks.toList.map LZ77Token.toLZ77Symbol).drop pos =
        ((toks.toList.map LZ77Token.toLZ77Symbol).drop pos).take
          (min (max (cuts.headD toks.size) (pos + 1)) toks.size - pos)
        ++ (toks.toList.map LZ77Token.toLZ77Symbol).drop
          (min (max (cuts.headD toks.size) (pos + 1)) toks.size) := by
      conv => lhs; rw [← List.take_append_drop
        (min (max (cuts.headD toks.size) (pos + 1)) toks.size - pos)
        ((toks.toList.map LZ77Token.toLZ77Symbol).drop pos)]
      rw [List.drop_drop, show pos +
        (min (max (cuts.headD toks.size) (pos + 1)) toks.size - pos)
        = min (max (cuts.headD toks.size) (pos + 1)) toks.size from by omega]
    rw [hsplit, Deflate.Spec.resolveLZ77_append_eobFree _ _ accOut hgmfree] at hres
    obtain ⟨out', hout'1, hout'2⟩ :
        ∃ out', Deflate.Spec.resolveLZ77 (((toks.toList.map LZ77Token.toLZ77Symbol).drop pos).take
            (min (max (cuts.headD toks.size) (pos + 1)) toks.size - pos)) accOut = some out' ∧
          Deflate.Spec.resolveLZ77 ((toks.toList.map LZ77Token.toLZ77Symbol).drop
            (min (max (cuts.headD toks.size) (pos + 1)) toks.size)) out' = some wholeOut := by
      cases hgm : Deflate.Spec.resolveLZ77 (((toks.toList.map LZ77Token.toLZ77Symbol).drop pos).take
          (min (max (cuts.headD toks.size) (pos + 1)) toks.size - pos)) accOut with
      | none => rw [hgm] at hres; simp only [Option.bind_none, reduceCtorEq] at hres
      | some o => rw [hgm] at hres; exact ⟨o, rfl, hres⟩
    have htts : tokensToSymbols
        (toks.extract pos (min (max (cuts.headD toks.size) (pos + 1)) toks.size)) =
        ((toks.toList.map LZ77Token.toLZ77Symbol).drop pos).take
          (min (max (cuts.headD toks.size) (pos + 1)) toks.size - pos)
        ++ [Deflate.Spec.LZ77Symbol.endOfBlock] := by
      unfold tokensToSymbols
      congr 1
      simp only [Array.toList_extract, List.extract_eq_take_drop, List.map_take, List.map_drop]
    have hblockres : Deflate.Spec.resolveLZ77
        (tokensToSymbols
          (toks.extract pos (min (max (cuts.headD toks.size) (pos + 1)) toks.size))) accOut =
        some out' := by
      rw [htts, Deflate.Spec.resolveLZ77_eobFree_eob _ accOut hgmfree]; exact hout'1
    obtain ⟨blockBits, htoBits, hwfblk, _, hdecblk⟩ :=
      emitSharedBlock_decode data
        (toks.extract pos (min (max (cuts.headD toks.size) (pos + 1)) toks.size)) bw hbw
        (decide (min (max (cuts.headD toks.size) (pos + 1)) toks.size ≥ toks.size)) hdata
        (fun t ht => henc t (mem_extract_toList toks pos _ t ht)) accOut out' hblockres
    by_cases hend : min (max (cuts.headD toks.size) (pos + 1)) toks.size ≥ toks.size
    · have hjeq : min (max (cuts.headD toks.size) (pos + 1)) toks.size = toks.size := by omega
      have hdropnil : (toks.toList.map LZ77Token.toLZ77Symbol).drop
          (min (max (cuts.headD toks.size) (pos + 1)) toks.size) = [] := by
        rw [hjeq, show toks.size = (toks.toList.map LZ77Token.toLZ77Symbol).length from by
          rw [List.length_map, Array.length_toList], List.drop_length]
      have hwo : out' = wholeOut := by
        rw [hdropnil, Deflate.Spec.resolveLZ77_nil, Option.some.injEq] at hout'2; exact hout'2
      have hstep : emitSharedBlocksAt data toks cuts pos bw =
          emitSharedBlock bw data
            (toks.extract pos (min (max (cuts.headD toks.size) (pos + 1)) toks.size))
            (decide (min (max (cuts.headD toks.size) (pos + 1)) toks.size ≥ toks.size)) := by
        conv => lhs; unfold emitSharedBlocksAt
        simp only [if_pos hend]
      refine ⟨blockBits, ?_, ?_, ?_⟩
      · rw [hstep]; exact htoBits
      · rw [hstep]; exact hwfblk
      · intro tail
        have hd := hdecblk tail
        rw [if_pos (decide_eq_true hend)] at hd
        rw [hd, hwo]
    · have hbw' : (emitSharedBlock bw data
          (toks.extract pos (min (max (cuts.headD toks.size) (pos + 1)) toks.size))
          (decide (min (max (cuts.headD toks.size) (pos + 1)) toks.size ≥ toks.size))).wf := hwfblk
      have hstep : emitSharedBlocksAt data toks cuts pos bw =
          emitSharedBlocksAt data toks cuts.tail
            (min (max (cuts.headD toks.size) (pos + 1)) toks.size)
            (emitSharedBlock bw data
              (toks.extract pos (min (max (cuts.headD toks.size) (pos + 1)) toks.size))
              (decide (min (max (cuts.headD toks.size) (pos + 1)) toks.size ≥ toks.size))) := by
        conv => lhs; unfold emitSharedBlocksAt
        simp only [if_neg hend]
      obtain ⟨B', htoBits', hwf', hdec'⟩ :=
        ih (min (max (cuts.headD toks.size) (pos + 1)) toks.size) cuts.tail out' wholeOut _
          (by omega) (by omega) hbw' hout'2
      refine ⟨blockBits ++ B', ?_, ?_, ?_⟩
      · rw [hstep, htoBits', htoBits, List.append_assoc]
      · rw [hstep]; exact hwf'
      · intro tail
        rw [List.append_assoc]
        have hd := hdecblk (B' ++ tail)
        rw [if_neg (by simp only [decide_eq_true_eq]; exact hend)] at hd
        rw [hd]; exact hdec' tail

/-- Cut-list shared-window roundtrip: decoding the heuristic-partition block
    stream reproduces the input, for **any** boundary selector `choose`. -/
theorem decode_deflateDynamicBlocksSharedAt (data : ByteArray)
    (choose : Array LZ77Token → List Nat) (level : UInt8) :
    Deflate.Spec.decode
      (Deflate.Spec.bytesToBits (deflateDynamicBlocksSharedAt data choose level)) =
      some data.data.toList := by
  unfold deflateDynamicBlocksSharedAt deflateDynamicBlocksSharedAtTokens
  split
  · -- data.size = 0: one final block over the empty token list (as in SC).
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
  · -- data.size > 0: the cut-list shared-window fold.
    rename_i hz
    have hpos : 0 < data.size := by
      rcases Nat.eq_zero_or_pos data.size with h | h
      · rw [h] at hz; simp at hz
      · exact h
    obtain ⟨henc, htokpos, hres0⟩ := deflateDynamicBlocksShared_facts data level hpos
    obtain ⟨B, htoBits, hwf, hdec⟩ :=
      emitSharedBlocksAt_decode data (lzMatch data level)
        (by omega) henc
        (lzMatch data level).size 0
        (choose (lzMatch data level)) []
        data.data.toList BitWriter.empty (by omega) htokpos BitWriter.empty_wf hres0
    rw [BitWriter.empty_toBits, List.nil_append] at htoBits
    rw [flush_toBits_aligned _ hwf, htoBits]
    exact hdec (List.replicate ((8 - B.length % 8) % 8) false)

/-- Cut-list shared-window roundtrip: inflating `deflateDynamicBlocksSharedAt`
    recovers the input, for any selector `choose` and any `maxOutputSize` large
    enough to hold it. -/
theorem inflate_deflateDynamicBlocksSharedAt (data : ByteArray)
    (choose : Array LZ77Token → List Nat) (level : UInt8)
    (maxOutputSize : Nat) (hsize : data.size ≤ maxOutputSize) :
    Zip.Native.Inflate.inflateReference (deflateDynamicBlocksSharedAt data choose level) maxOutputSize =
      .ok data := by
  have hlen : data.data.toList.length ≤ maxOutputSize := by
    simp only [Array.length_toList, ByteArray.size_data]; omega
  rw [← show ByteArray.mk ⟨data.data.toList⟩ = data from by simp only [Array.toArray_toList]]
  exact inflate_complete (deflateDynamicBlocksSharedAt data choose level) data.data.toList
    maxOutputSize hlen (decode_deflateDynamicBlocksSharedAt data choose level)

/-- The `decode.goR` of `deflateDynamicBlocksSharedAt` returns the input and
    short (< 8-bit) trailing padding — needed to show the native decoder
    consumes all of the deflated bytes. -/
theorem deflateDynamicBlocksSharedAt_goR_pad (data : ByteArray)
    (choose : Array LZ77Token → List Nat) (level : UInt8) :
    ∃ remaining,
      Deflate.Spec.decode.goR
          (Deflate.Spec.bytesToBits (deflateDynamicBlocksSharedAt data choose level)) []
        = some (data.data.toList, remaining) ∧ remaining.length < 8 := by
  unfold deflateDynamicBlocksSharedAt deflateDynamicBlocksSharedAtTokens
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
    obtain ⟨henc, htokpos, hres0⟩ := deflateDynamicBlocksShared_facts data level hpos
    obtain ⟨B, htoBits, hwf, hdec⟩ :=
      emitSharedBlocksAt_decodeR data
        (lzMatch data level)
        (by omega) henc
        (lzMatch data level).size 0
        (choose (lzMatch data level)) []
        data.data.toList BitWriter.empty (by omega) htokpos BitWriter.empty_wf hres0
    rw [BitWriter.empty_toBits, List.nil_append] at htoBits
    rw [flush_toBits_aligned _ hwf, htoBits]
    refine ⟨List.replicate ((8 - B.length % 8) % 8) false, hdec _, ?_⟩
    simp only [List.length_replicate]; omega

/-- The output of `deflateDynamicBlocksSharedAt` decomposes into content bits
    plus short (< 8-bit) padding. -/
theorem deflateDynamicBlocksSharedAt_pad (data : ByteArray)
    (choose : Array LZ77Token → List Nat) (level : UInt8) :
    ∃ (contentBits padding : List Bool),
      Deflate.Spec.bytesToBits (deflateDynamicBlocksSharedAt data choose level) =
        contentBits ++ padding ∧ padding.length < 8 := by
  unfold deflateDynamicBlocksSharedAt deflateDynamicBlocksSharedAtTokens
  split
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hwf⟩ :=
      emitDynBlock_spec BitWriter.empty BitWriter.empty_wf data #[] (by simp) (fun _ => rfl) true
    exact ⟨_, _, flush_toBits_aligned _ hwf, by simp only [List.length_replicate]; omega⟩
  · rename_i hz
    have hpos : 0 < data.size := by
      rcases Nat.eq_zero_or_pos data.size with h | h
      · rw [h] at hz; simp at hz
      · exact h
    obtain ⟨henc, htokpos, hres0⟩ := deflateDynamicBlocksShared_facts data level hpos
    obtain ⟨B, _, hwf, _⟩ :=
      emitSharedBlocksAt_decode data
        (lzMatch data level)
        (by omega) henc
        (lzMatch data level).size 0
        (choose (lzMatch data level)) []
        data.data.toList BitWriter.empty (by omega) htokpos BitWriter.empty_wf hres0
    exact ⟨_, _, flush_toBits_aligned _ hwf, by simp only [List.length_replicate]; omega⟩

/-! ## Cross-block split over the near-optimal parse (`deflateDynamicBlocksOptimal`)

Verbatim adaptation of the `deflateDynamicBlocksShared` quadruple with the
matcher contracts (`lzMatch_*`) replaced by the optimal parser's
(`lz77OptimalIter_*`); the shared-window fold (`emitSharedBlocks_decode`/
`_decodeR`) is already generic over the token array. -/

private theorem deflateDynamicBlocksOptimal_facts (data : ByteArray)
    (hpos : 0 < data.size) :
    (∀ t ∈ (lz77OptimalIter data).toList,
        match t with
        | .literal _ => True
        | .reference len dist => 3 ≤ len ∧ len ≤ 258 ∧ 1 ≤ dist ∧ dist ≤ 32768) ∧
      0 < (lz77OptimalIter data).size ∧
      Deflate.Spec.resolveLZ77
        (((lz77OptimalIter data).toList.map
          LZ77Token.toLZ77Symbol).drop 0) [] = some data.data.toList := by
  have henc := lz77OptimalIter_encodable data
  have hwhole := lz77OptimalIter_resolves data
  have hMfree := mem_map_toLZ77Symbol_ne_endOfBlock
    (lz77OptimalIter data).toList
  have hM : Deflate.Spec.resolveLZ77
      ((lz77OptimalIter data).toList.map
        LZ77Token.toLZ77Symbol) [] = some data.data.toList := by
    simp only [tokensToSymbols] at hwhole
    rwa [Deflate.Spec.resolveLZ77_eobFree_eob _ [] hMfree] at hwhole
  refine ⟨henc, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos (lz77OptimalIter data).size with h0 | h0
    · exfalso
      have hnil : (lz77OptimalIter data).toList = [] :=
        List.eq_nil_of_length_eq_zero (by rw [Array.length_toList]; omega)
      rw [hnil, List.map_nil, Deflate.Spec.resolveLZ77_nil, Option.some.injEq] at hM
      have hl := congrArg List.length hM
      simp only [List.length_nil, Array.length_toList, ByteArray.size_data] at hl
      omega
    · exact h0
  · rw [List.drop_zero]; exact hM

/-- Near-optimal cross-block roundtrip: decoding the block stream over the
    DP parse reproduces the input. -/
theorem decode_deflateDynamicBlocksOptimal (data : ByteArray) (tokChunk : Nat) :
    Deflate.Spec.decode
      (Deflate.Spec.bytesToBits (deflateDynamicBlocksOptimal data tokChunk)) =
      some data.data.toList := by
  unfold deflateDynamicBlocksOptimal
  split
  · -- data.size = 0: one final block over the empty token list (as in SC).
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
  · -- data.size > 0: the shared-window fold over the optimal tokens.
    rename_i hz
    have hpos : 0 < data.size := by
      rcases Nat.eq_zero_or_pos data.size with h | h
      · rw [h] at hz; simp at hz
      · exact h
    obtain ⟨henc, htokpos, hres0⟩ := deflateDynamicBlocksOptimal_facts data hpos
    obtain ⟨B, htoBits, hwf, hdec⟩ :=
      emitSharedBlocks_decode data (lz77OptimalIter data)
        tokChunk (by omega) henc
        (lz77OptimalIter data).size 0 []
        data.data.toList BitWriter.empty (by omega) htokpos BitWriter.empty_wf hres0
    rw [BitWriter.empty_toBits, List.nil_append] at htoBits
    rw [flush_toBits_aligned _ hwf, htoBits]
    exact hdec (List.replicate ((8 - B.length % 8) % 8) false)

/-- Near-optimal cross-block roundtrip: inflating `deflateDynamicBlocksOptimal`
    recovers the input, for any `maxOutputSize` large enough to hold it. -/
theorem inflate_deflateDynamicBlocksOptimal (data : ByteArray) (tokChunk : Nat)
    (maxOutputSize : Nat) (hsize : data.size ≤ maxOutputSize) :
    Zip.Native.Inflate.inflateReference (deflateDynamicBlocksOptimal data tokChunk) maxOutputSize =
      .ok data := by
  have hlen : data.data.toList.length ≤ maxOutputSize := by
    simp only [Array.length_toList, ByteArray.size_data]; omega
  rw [← show ByteArray.mk ⟨data.data.toList⟩ = data from by simp only [Array.toArray_toList]]
  exact inflate_complete (deflateDynamicBlocksOptimal data tokChunk) data.data.toList
    maxOutputSize hlen (decode_deflateDynamicBlocksOptimal data tokChunk)

/-- The `decode.goR` of `deflateDynamicBlocksOptimal` returns the input and
    short (< 8-bit) trailing padding. -/
theorem deflateDynamicBlocksOptimal_goR_pad (data : ByteArray) (tokChunk : Nat) :
    ∃ remaining,
      Deflate.Spec.decode.goR
          (Deflate.Spec.bytesToBits (deflateDynamicBlocksOptimal data tokChunk)) []
        = some (data.data.toList, remaining) ∧ remaining.length < 8 := by
  unfold deflateDynamicBlocksOptimal
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
    obtain ⟨henc, htokpos, hres0⟩ := deflateDynamicBlocksOptimal_facts data hpos
    obtain ⟨B, htoBits, hwf, hdec⟩ :=
      emitSharedBlocks_decodeR data (lz77OptimalIter data)
        tokChunk (by omega) henc
        (lz77OptimalIter data).size 0 []
        data.data.toList BitWriter.empty (by omega) htokpos BitWriter.empty_wf hres0
    rw [BitWriter.empty_toBits, List.nil_append] at htoBits
    rw [flush_toBits_aligned _ hwf, htoBits]
    refine ⟨List.replicate ((8 - B.length % 8) % 8) false, hdec _, ?_⟩
    simp only [List.length_replicate]; omega

/-- The output of `deflateDynamicBlocksOptimal` decomposes into content bits
    plus short (< 8-bit) padding. -/
theorem deflateDynamicBlocksOptimal_pad (data : ByteArray) (tokChunk : Nat) :
    ∃ (contentBits padding : List Bool),
      Deflate.Spec.bytesToBits (deflateDynamicBlocksOptimal data tokChunk) =
        contentBits ++ padding ∧ padding.length < 8 := by
  unfold deflateDynamicBlocksOptimal
  split
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hwf⟩ :=
      emitDynBlock_spec BitWriter.empty BitWriter.empty_wf data #[] (by simp) (fun _ => rfl) true
    exact ⟨_, _, flush_toBits_aligned _ hwf, by simp only [List.length_replicate]; omega⟩
  · rename_i hz
    have hpos : 0 < data.size := by
      rcases Nat.eq_zero_or_pos data.size with h | h
      · rw [h] at hz; simp at hz
      · exact h
    obtain ⟨henc, htokpos, hres0⟩ := deflateDynamicBlocksOptimal_facts data hpos
    obtain ⟨B, _, hwf, _⟩ :=
      emitSharedBlocks_decode data (lz77OptimalIter data)
        tokChunk (by omega) henc
        (lz77OptimalIter data).size 0 []
        data.data.toList BitWriter.empty (by omega) htokpos BitWriter.empty_wf hres0
    exact ⟨_, _, flush_toBits_aligned _ hwf, by simp only [List.length_replicate]; omega⟩

/-! ## Cross-block split over the L9-fast parse (`deflateDynamicBlocksOptimalFast`, #2638)

Byte-for-byte twin of the `deflateDynamicBlocksOptimal` quadruple above with the
exact parser's contracts (`lz77OptimalIter_*`) replaced by the L9-fast parser's
(`lz77OptimalFastIter_*`); the shared-window fold is already generic over the
token array, so the proofs are identical modulo that substitution. -/

private theorem deflateDynamicBlocksOptimalFast_facts (data : ByteArray)
    (hpos : 0 < data.size) :
    (∀ t ∈ (lz77OptimalFastIter data).toList,
        match t with
        | .literal _ => True
        | .reference len dist => 3 ≤ len ∧ len ≤ 258 ∧ 1 ≤ dist ∧ dist ≤ 32768) ∧
      0 < (lz77OptimalFastIter data).size ∧
      Deflate.Spec.resolveLZ77
        (((lz77OptimalFastIter data).toList.map
          LZ77Token.toLZ77Symbol).drop 0) [] = some data.data.toList := by
  have henc := lz77OptimalFastIter_encodable data
  have hwhole := lz77OptimalFastIter_resolves data
  have hMfree := mem_map_toLZ77Symbol_ne_endOfBlock
    (lz77OptimalFastIter data).toList
  have hM : Deflate.Spec.resolveLZ77
      ((lz77OptimalFastIter data).toList.map
        LZ77Token.toLZ77Symbol) [] = some data.data.toList := by
    simp only [tokensToSymbols] at hwhole
    rwa [Deflate.Spec.resolveLZ77_eobFree_eob _ [] hMfree] at hwhole
  refine ⟨henc, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos (lz77OptimalFastIter data).size with h0 | h0
    · exfalso
      have hnil : (lz77OptimalFastIter data).toList = [] :=
        List.eq_nil_of_length_eq_zero (by rw [Array.length_toList]; omega)
      rw [hnil, List.map_nil, Deflate.Spec.resolveLZ77_nil, Option.some.injEq] at hM
      have hl := congrArg List.length hM
      simp only [List.length_nil, Array.length_toList, ByteArray.size_data] at hl
      omega
    · exact h0
  · rw [List.drop_zero]; exact hM

/-- L9-fast cross-block roundtrip: decoding the block stream over the L9-fast
    parse reproduces the input. -/
theorem decode_deflateDynamicBlocksOptimalFast (data : ByteArray) (tokChunk : Nat) :
    Deflate.Spec.decode
      (Deflate.Spec.bytesToBits (deflateDynamicBlocksOptimalFast data tokChunk)) =
      some data.data.toList := by
  unfold deflateDynamicBlocksOptimalFast
  split
  · rename_i hz
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
  · rename_i hz
    have hpos : 0 < data.size := by
      rcases Nat.eq_zero_or_pos data.size with h | h
      · rw [h] at hz; simp at hz
      · exact h
    obtain ⟨henc, htokpos, hres0⟩ := deflateDynamicBlocksOptimalFast_facts data hpos
    obtain ⟨B, htoBits, hwf, hdec⟩ :=
      emitSharedBlocks_decode data (lz77OptimalFastIter data)
        tokChunk (by omega) henc
        (lz77OptimalFastIter data).size 0 []
        data.data.toList BitWriter.empty (by omega) htokpos BitWriter.empty_wf hres0
    rw [BitWriter.empty_toBits, List.nil_append] at htoBits
    rw [flush_toBits_aligned _ hwf, htoBits]
    exact hdec (List.replicate ((8 - B.length % 8) % 8) false)

/-- L9-fast cross-block roundtrip: inflating `deflateDynamicBlocksOptimalFast`
    recovers the input, for any `maxOutputSize` large enough to hold it. -/
theorem inflate_deflateDynamicBlocksOptimalFast (data : ByteArray) (tokChunk : Nat)
    (maxOutputSize : Nat) (hsize : data.size ≤ maxOutputSize) :
    Zip.Native.Inflate.inflateReference (deflateDynamicBlocksOptimalFast data tokChunk) maxOutputSize =
      .ok data := by
  have hlen : data.data.toList.length ≤ maxOutputSize := by
    simp only [Array.length_toList, ByteArray.size_data]; omega
  rw [← show ByteArray.mk ⟨data.data.toList⟩ = data from by simp only [Array.toArray_toList]]
  exact inflate_complete (deflateDynamicBlocksOptimalFast data tokChunk) data.data.toList
    maxOutputSize hlen (decode_deflateDynamicBlocksOptimalFast data tokChunk)

/-- The `decode.goR` of `deflateDynamicBlocksOptimalFast` returns the input and
    short (< 8-bit) trailing padding. -/
theorem deflateDynamicBlocksOptimalFast_goR_pad (data : ByteArray) (tokChunk : Nat) :
    ∃ remaining,
      Deflate.Spec.decode.goR
          (Deflate.Spec.bytesToBits (deflateDynamicBlocksOptimalFast data tokChunk)) []
        = some (data.data.toList, remaining) ∧ remaining.length < 8 := by
  unfold deflateDynamicBlocksOptimalFast
  split
  · rename_i hz
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
  · rename_i hz
    have hpos : 0 < data.size := by
      rcases Nat.eq_zero_or_pos data.size with h | h
      · rw [h] at hz; simp at hz
      · exact h
    obtain ⟨henc, htokpos, hres0⟩ := deflateDynamicBlocksOptimalFast_facts data hpos
    obtain ⟨B, htoBits, hwf, hdec⟩ :=
      emitSharedBlocks_decodeR data (lz77OptimalFastIter data)
        tokChunk (by omega) henc
        (lz77OptimalFastIter data).size 0 []
        data.data.toList BitWriter.empty (by omega) htokpos BitWriter.empty_wf hres0
    rw [BitWriter.empty_toBits, List.nil_append] at htoBits
    rw [flush_toBits_aligned _ hwf, htoBits]
    refine ⟨List.replicate ((8 - B.length % 8) % 8) false, hdec _, ?_⟩
    simp only [List.length_replicate]; omega

/-- The output of `deflateDynamicBlocksOptimalFast` decomposes into content bits
    plus short (< 8-bit) padding. -/
theorem deflateDynamicBlocksOptimalFast_pad (data : ByteArray) (tokChunk : Nat) :
    ∃ (contentBits padding : List Bool),
      Deflate.Spec.bytesToBits (deflateDynamicBlocksOptimalFast data tokChunk) =
        contentBits ++ padding ∧ padding.length < 8 := by
  unfold deflateDynamicBlocksOptimalFast
  split
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hwf⟩ :=
      emitDynBlock_spec BitWriter.empty BitWriter.empty_wf data #[] (by simp) (fun _ => rfl) true
    exact ⟨_, _, flush_toBits_aligned _ hwf, by simp only [List.length_replicate]; omega⟩
  · rename_i hz
    have hpos : 0 < data.size := by
      rcases Nat.eq_zero_or_pos data.size with h | h
      · rw [h] at hz; simp at hz
      · exact h
    obtain ⟨henc, htokpos, hres0⟩ := deflateDynamicBlocksOptimalFast_facts data hpos
    obtain ⟨B, _, hwf, _⟩ :=
      emitSharedBlocks_decode data (lz77OptimalFastIter data)
        tokChunk (by omega) henc
        (lz77OptimalFastIter data).size 0 []
        data.data.toList BitWriter.empty (by omega) htokpos BitWriter.empty_wf hres0
    exact ⟨_, _, flush_toBits_aligned _ hwf, by simp only [List.length_replicate]; omega⟩

/-! ## Cross-block split over the windowed parses (`deflateDynamicBlocksOptimalWindowed`/`Fast`, #2787)

Byte-for-byte twins of the two quadruples above with the parser contracts
replaced by the windowed parsers' (`lz77OptimalWindowedIter_*` /
`lz77OptimalWindowedFastIter_*`); the shared-window fold is generic over the
token array, so the proofs are identical modulo that substitution. -/

private theorem deflateDynamicBlocksOptimalWindowed_facts (data : ByteArray)
    (hpos : 0 < data.size) :
    (∀ t ∈ (lz77OptimalWindowedIter data).toList,
        match t with
        | .literal _ => True
        | .reference len dist => 3 ≤ len ∧ len ≤ 258 ∧ 1 ≤ dist ∧ dist ≤ 32768) ∧
      0 < (lz77OptimalWindowedIter data).size ∧
      Deflate.Spec.resolveLZ77
        (((lz77OptimalWindowedIter data).toList.map
          LZ77Token.toLZ77Symbol).drop 0) [] = some data.data.toList := by
  have henc := lz77OptimalWindowedIter_encodable data
  have hwhole := lz77OptimalWindowedIter_resolves data
  have hMfree := mem_map_toLZ77Symbol_ne_endOfBlock
    (lz77OptimalWindowedIter data).toList
  have hM : Deflate.Spec.resolveLZ77
      ((lz77OptimalWindowedIter data).toList.map
        LZ77Token.toLZ77Symbol) [] = some data.data.toList := by
    simp only [tokensToSymbols] at hwhole
    rwa [Deflate.Spec.resolveLZ77_eobFree_eob _ [] hMfree] at hwhole
  refine ⟨henc, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos (lz77OptimalWindowedIter data).size with h0 | h0
    · exfalso
      have hnil : (lz77OptimalWindowedIter data).toList = [] :=
        List.eq_nil_of_length_eq_zero (by rw [Array.length_toList]; omega)
      rw [hnil, List.map_nil, Deflate.Spec.resolveLZ77_nil, Option.some.injEq] at hM
      have hl := congrArg List.length hM
      simp only [List.length_nil, Array.length_toList, ByteArray.size_data] at hl
      omega
    · exact h0
  · rw [List.drop_zero]; exact hM

/-- Near-optimal cross-block roundtrip: decoding the block stream over the
    DP parse reproduces the input. -/
theorem decode_deflateDynamicBlocksOptimalWindowed (data : ByteArray) (tokChunk : Nat) :
    Deflate.Spec.decode
      (Deflate.Spec.bytesToBits (deflateDynamicBlocksOptimalWindowed data tokChunk)) =
      some data.data.toList := by
  unfold deflateDynamicBlocksOptimalWindowed
  split
  · -- data.size = 0: one final block over the empty token list (as in SC).
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
  · -- data.size > 0: the shared-window fold over the optimal tokens.
    rename_i hz
    have hpos : 0 < data.size := by
      rcases Nat.eq_zero_or_pos data.size with h | h
      · rw [h] at hz; simp at hz
      · exact h
    obtain ⟨henc, htokpos, hres0⟩ := deflateDynamicBlocksOptimalWindowed_facts data hpos
    obtain ⟨B, htoBits, hwf, hdec⟩ :=
      emitSharedBlocks_decode data (lz77OptimalWindowedIter data)
        tokChunk (by omega) henc
        (lz77OptimalWindowedIter data).size 0 []
        data.data.toList BitWriter.empty (by omega) htokpos BitWriter.empty_wf hres0
    rw [BitWriter.empty_toBits, List.nil_append] at htoBits
    rw [flush_toBits_aligned _ hwf, htoBits]
    exact hdec (List.replicate ((8 - B.length % 8) % 8) false)

/-- Near-optimal cross-block roundtrip: inflating `deflateDynamicBlocksOptimalWindowed`
    recovers the input, for any `maxOutputSize` large enough to hold it. -/
theorem inflate_deflateDynamicBlocksOptimalWindowed (data : ByteArray) (tokChunk : Nat)
    (maxOutputSize : Nat) (hsize : data.size ≤ maxOutputSize) :
    Zip.Native.Inflate.inflateReference (deflateDynamicBlocksOptimalWindowed data tokChunk) maxOutputSize =
      .ok data := by
  have hlen : data.data.toList.length ≤ maxOutputSize := by
    simp only [Array.length_toList, ByteArray.size_data]; omega
  rw [← show ByteArray.mk ⟨data.data.toList⟩ = data from by simp only [Array.toArray_toList]]
  exact inflate_complete (deflateDynamicBlocksOptimalWindowed data tokChunk) data.data.toList
    maxOutputSize hlen (decode_deflateDynamicBlocksOptimalWindowed data tokChunk)

/-- The `decode.goR` of `deflateDynamicBlocksOptimalWindowed` returns the input and
    short (< 8-bit) trailing padding. -/
theorem deflateDynamicBlocksOptimalWindowed_goR_pad (data : ByteArray) (tokChunk : Nat) :
    ∃ remaining,
      Deflate.Spec.decode.goR
          (Deflate.Spec.bytesToBits (deflateDynamicBlocksOptimalWindowed data tokChunk)) []
        = some (data.data.toList, remaining) ∧ remaining.length < 8 := by
  unfold deflateDynamicBlocksOptimalWindowed
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
    obtain ⟨henc, htokpos, hres0⟩ := deflateDynamicBlocksOptimalWindowed_facts data hpos
    obtain ⟨B, htoBits, hwf, hdec⟩ :=
      emitSharedBlocks_decodeR data (lz77OptimalWindowedIter data)
        tokChunk (by omega) henc
        (lz77OptimalWindowedIter data).size 0 []
        data.data.toList BitWriter.empty (by omega) htokpos BitWriter.empty_wf hres0
    rw [BitWriter.empty_toBits, List.nil_append] at htoBits
    rw [flush_toBits_aligned _ hwf, htoBits]
    refine ⟨List.replicate ((8 - B.length % 8) % 8) false, hdec _, ?_⟩
    simp only [List.length_replicate]; omega

/-- The output of `deflateDynamicBlocksOptimalWindowed` decomposes into content bits
    plus short (< 8-bit) padding. -/
theorem deflateDynamicBlocksOptimalWindowed_pad (data : ByteArray) (tokChunk : Nat) :
    ∃ (contentBits padding : List Bool),
      Deflate.Spec.bytesToBits (deflateDynamicBlocksOptimalWindowed data tokChunk) =
        contentBits ++ padding ∧ padding.length < 8 := by
  unfold deflateDynamicBlocksOptimalWindowed
  split
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hwf⟩ :=
      emitDynBlock_spec BitWriter.empty BitWriter.empty_wf data #[] (by simp) (fun _ => rfl) true
    exact ⟨_, _, flush_toBits_aligned _ hwf, by simp only [List.length_replicate]; omega⟩
  · rename_i hz
    have hpos : 0 < data.size := by
      rcases Nat.eq_zero_or_pos data.size with h | h
      · rw [h] at hz; simp at hz
      · exact h
    obtain ⟨henc, htokpos, hres0⟩ := deflateDynamicBlocksOptimalWindowed_facts data hpos
    obtain ⟨B, _, hwf, _⟩ :=
      emitSharedBlocks_decode data (lz77OptimalWindowedIter data)
        tokChunk (by omega) henc
        (lz77OptimalWindowedIter data).size 0 []
        data.data.toList BitWriter.empty (by omega) htokpos BitWriter.empty_wf hres0
    exact ⟨_, _, flush_toBits_aligned _ hwf, by simp only [List.length_replicate]; omega⟩

private theorem deflateDynamicBlocksOptimalWindowedFast_facts (data : ByteArray)
    (hpos : 0 < data.size) :
    (∀ t ∈ (lz77OptimalWindowedFastIter data).toList,
        match t with
        | .literal _ => True
        | .reference len dist => 3 ≤ len ∧ len ≤ 258 ∧ 1 ≤ dist ∧ dist ≤ 32768) ∧
      0 < (lz77OptimalWindowedFastIter data).size ∧
      Deflate.Spec.resolveLZ77
        (((lz77OptimalWindowedFastIter data).toList.map
          LZ77Token.toLZ77Symbol).drop 0) [] = some data.data.toList := by
  have henc := lz77OptimalWindowedFastIter_encodable data
  have hwhole := lz77OptimalWindowedFastIter_resolves data
  have hMfree := mem_map_toLZ77Symbol_ne_endOfBlock
    (lz77OptimalWindowedFastIter data).toList
  have hM : Deflate.Spec.resolveLZ77
      ((lz77OptimalWindowedFastIter data).toList.map
        LZ77Token.toLZ77Symbol) [] = some data.data.toList := by
    simp only [tokensToSymbols] at hwhole
    rwa [Deflate.Spec.resolveLZ77_eobFree_eob _ [] hMfree] at hwhole
  refine ⟨henc, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos (lz77OptimalWindowedFastIter data).size with h0 | h0
    · exfalso
      have hnil : (lz77OptimalWindowedFastIter data).toList = [] :=
        List.eq_nil_of_length_eq_zero (by rw [Array.length_toList]; omega)
      rw [hnil, List.map_nil, Deflate.Spec.resolveLZ77_nil, Option.some.injEq] at hM
      have hl := congrArg List.length hM
      simp only [List.length_nil, Array.length_toList, ByteArray.size_data] at hl
      omega
    · exact h0
  · rw [List.drop_zero]; exact hM

/-- L9-fast cross-block roundtrip: decoding the block stream over the L9-fast
    parse reproduces the input. -/
theorem decode_deflateDynamicBlocksOptimalWindowedFast (data : ByteArray) (tokChunk : Nat) :
    Deflate.Spec.decode
      (Deflate.Spec.bytesToBits (deflateDynamicBlocksOptimalWindowedFast data tokChunk)) =
      some data.data.toList := by
  unfold deflateDynamicBlocksOptimalWindowedFast
  split
  · rename_i hz
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
  · rename_i hz
    have hpos : 0 < data.size := by
      rcases Nat.eq_zero_or_pos data.size with h | h
      · rw [h] at hz; simp at hz
      · exact h
    obtain ⟨henc, htokpos, hres0⟩ := deflateDynamicBlocksOptimalWindowedFast_facts data hpos
    obtain ⟨B, htoBits, hwf, hdec⟩ :=
      emitSharedBlocks_decode data (lz77OptimalWindowedFastIter data)
        tokChunk (by omega) henc
        (lz77OptimalWindowedFastIter data).size 0 []
        data.data.toList BitWriter.empty (by omega) htokpos BitWriter.empty_wf hres0
    rw [BitWriter.empty_toBits, List.nil_append] at htoBits
    rw [flush_toBits_aligned _ hwf, htoBits]
    exact hdec (List.replicate ((8 - B.length % 8) % 8) false)

/-- L9-fast cross-block roundtrip: inflating `deflateDynamicBlocksOptimalWindowedFast`
    recovers the input, for any `maxOutputSize` large enough to hold it. -/
theorem inflate_deflateDynamicBlocksOptimalWindowedFast (data : ByteArray) (tokChunk : Nat)
    (maxOutputSize : Nat) (hsize : data.size ≤ maxOutputSize) :
    Zip.Native.Inflate.inflateReference (deflateDynamicBlocksOptimalWindowedFast data tokChunk) maxOutputSize =
      .ok data := by
  have hlen : data.data.toList.length ≤ maxOutputSize := by
    simp only [Array.length_toList, ByteArray.size_data]; omega
  rw [← show ByteArray.mk ⟨data.data.toList⟩ = data from by simp only [Array.toArray_toList]]
  exact inflate_complete (deflateDynamicBlocksOptimalWindowedFast data tokChunk) data.data.toList
    maxOutputSize hlen (decode_deflateDynamicBlocksOptimalWindowedFast data tokChunk)

/-- The `decode.goR` of `deflateDynamicBlocksOptimalWindowedFast` returns the input and
    short (< 8-bit) trailing padding. -/
theorem deflateDynamicBlocksOptimalWindowedFast_goR_pad (data : ByteArray) (tokChunk : Nat) :
    ∃ remaining,
      Deflate.Spec.decode.goR
          (Deflate.Spec.bytesToBits (deflateDynamicBlocksOptimalWindowedFast data tokChunk)) []
        = some (data.data.toList, remaining) ∧ remaining.length < 8 := by
  unfold deflateDynamicBlocksOptimalWindowedFast
  split
  · rename_i hz
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
  · rename_i hz
    have hpos : 0 < data.size := by
      rcases Nat.eq_zero_or_pos data.size with h | h
      · rw [h] at hz; simp at hz
      · exact h
    obtain ⟨henc, htokpos, hres0⟩ := deflateDynamicBlocksOptimalWindowedFast_facts data hpos
    obtain ⟨B, htoBits, hwf, hdec⟩ :=
      emitSharedBlocks_decodeR data (lz77OptimalWindowedFastIter data)
        tokChunk (by omega) henc
        (lz77OptimalWindowedFastIter data).size 0 []
        data.data.toList BitWriter.empty (by omega) htokpos BitWriter.empty_wf hres0
    rw [BitWriter.empty_toBits, List.nil_append] at htoBits
    rw [flush_toBits_aligned _ hwf, htoBits]
    refine ⟨List.replicate ((8 - B.length % 8) % 8) false, hdec _, ?_⟩
    simp only [List.length_replicate]; omega

/-- The output of `deflateDynamicBlocksOptimalWindowedFast` decomposes into content bits
    plus short (< 8-bit) padding. -/
theorem deflateDynamicBlocksOptimalWindowedFast_pad (data : ByteArray) (tokChunk : Nat) :
    ∃ (contentBits padding : List Bool),
      Deflate.Spec.bytesToBits (deflateDynamicBlocksOptimalWindowedFast data tokChunk) =
        contentBits ++ padding ∧ padding.length < 8 := by
  unfold deflateDynamicBlocksOptimalWindowedFast
  split
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hwf⟩ :=
      emitDynBlock_spec BitWriter.empty BitWriter.empty_wf data #[] (by simp) (fun _ => rfl) true
    exact ⟨_, _, flush_toBits_aligned _ hwf, by simp only [List.length_replicate]; omega⟩
  · rename_i hz
    have hpos : 0 < data.size := by
      rcases Nat.eq_zero_or_pos data.size with h | h
      · rw [h] at hz; simp at hz
      · exact h
    obtain ⟨henc, htokpos, hres0⟩ := deflateDynamicBlocksOptimalWindowedFast_facts data hpos
    obtain ⟨B, _, hwf, _⟩ :=
      emitSharedBlocks_decode data (lz77OptimalWindowedFastIter data)
        tokChunk (by omega) henc
        (lz77OptimalWindowedFastIter data).size 0 []
        data.data.toList BitWriter.empty (by omega) htokpos BitWriter.empty_wf hres0
    exact ⟨_, _, flush_toBits_aligned _ hwf, by simp only [List.length_replicate]; omega⟩

/-! ## Sized-tree emitter equality (Wave 5, #2552)

`deflateDynamicBlocksSharedSized` reuses the per-block Huffman trees the
arbitration sizing pass already built, instead of letting `emitSharedBlocksAt`
rebuild them at emission. The lemmas below prove the sized pipeline
byte-identical to the reference
`deflateDynamicBlocksSharedAtTokens … chooseSplitsArbitrated`, so the
`deflateDynamicBlocksSharedAt` quadruple above transfers by a rewrite in
`DeflateRoundtrip` — no statement changes. Each equality is one unfolding step
per block on both sides: the trees the sizing pass stores are *definitionally*
`dynamicCodeLengths (tokenFreqs group)` of the same group the reference
emitter recomputes, so no bit-level reasoning is involved. -/

/-- Component 1 of `sharedPartitionSized` is exactly `sharedPartitionBits`
    (fuel-quantified form for the induction). -/
private theorem sharedPartitionSized_fst_fuel (toks : Array LZ77Token) :
    ∀ (fuel pos : Nat), toks.size - pos < fuel → ∀ (cuts : List Nat),
      (sharedPartitionSized toks cuts pos).1 = sharedPartitionBits toks cuts pos := by
  intro fuel
  induction fuel with
  | zero => intro pos hf; omega
  | succ fuel ih =>
    intro pos hf cuts
    conv => lhs; unfold sharedPartitionSized
    conv => rhs; unfold sharedPartitionBits
    by_cases hend : min (max (cuts.headD toks.size) (pos + 1)) toks.size ≥ toks.size
    · simp only [if_pos hend, sizedTrees]
    · simp only [if_neg hend, sizedTrees]
      rw [ih (min (max (cuts.headD toks.size) (pos + 1)) toks.size) (by omega)]

/-- Component 1 of `sharedPartitionSized` is exactly `sharedPartitionBits`. -/
theorem sharedPartitionSized_fst (toks : Array LZ77Token) (cuts : List Nat) (pos : Nat) :
    (sharedPartitionSized toks cuts pos).1 = sharedPartitionBits toks cuts pos :=
  sharedPartitionSized_fst_fuel toks (toks.size - pos + 1) pos (by omega) cuts

/-- The tree-taking emitter over the sizing pass's trees equals the reference
    emitter (fuel-quantified form): the stored trees are definitionally the
    `dynamicCodeLengths (tokenFreqs group)` the reference recomputes. -/
private theorem emitSharedBlocksAtSized_eq_fuel (data : ByteArray) (toks : Array LZ77Token) :
    ∀ (fuel pos : Nat), toks.size - pos < fuel → ∀ (cuts : List Nat) (bw : BitWriter),
      emitSharedBlocksAtSized data toks cuts (sharedPartitionSized toks cuts pos).2 pos bw
        = emitSharedBlocksAt data toks cuts pos bw := by
  intro fuel
  induction fuel with
  | zero => intro pos hf; omega
  | succ fuel ih =>
    intro pos hf cuts bw
    by_cases hend : min (max (cuts.headD toks.size) (pos + 1)) toks.size ≥ toks.size
    · have hsnd : (sharedPartitionSized toks cuts pos).2 =
          [sizedTrees
            (tokenFreqs (toks.extract pos
              (min (max (cuts.headD toks.size) (pos + 1)) toks.size))).1
            (tokenFreqs (toks.extract pos
              (min (max (cuts.headD toks.size) (pos + 1)) toks.size))).2] := by
        conv => lhs; unfold sharedPartitionSized
        simp only [if_pos hend]
      rw [hsnd]
      conv => lhs; unfold emitSharedBlocksAtSized
      conv => rhs; unfold emitSharedBlocksAt
      simp only [if_pos hend, List.headD_cons, emitSharedBlock, sizedTrees]
    · have hsnd : (sharedPartitionSized toks cuts pos).2 =
          sizedTrees
            (tokenFreqs (toks.extract pos
              (min (max (cuts.headD toks.size) (pos + 1)) toks.size))).1
            (tokenFreqs (toks.extract pos
              (min (max (cuts.headD toks.size) (pos + 1)) toks.size))).2 ::
          (sharedPartitionSized toks cuts.tail
            (min (max (cuts.headD toks.size) (pos + 1)) toks.size)).2 := by
        conv => lhs; unfold sharedPartitionSized
        simp only [if_neg hend]
      rw [hsnd]
      conv => lhs; unfold emitSharedBlocksAtSized
      conv => rhs; unfold emitSharedBlocksAt
      simp only [if_neg hend, List.headD_cons, List.tail_cons, emitSharedBlock, sizedTrees]
      exact ih (min (max (cuts.headD toks.size) (pos + 1)) toks.size) (by omega) cuts.tail _

/-- The tree-taking emitter over the sizing pass's trees equals the reference
    emitter, for any cut list and start position. -/
theorem emitSharedBlocksAtSized_eq (data : ByteArray) (toks : Array LZ77Token)
    (cuts : List Nat) (pos : Nat) (bw : BitWriter) :
    emitSharedBlocksAtSized data toks cuts (sharedPartitionSized toks cuts pos).2 pos bw
      = emitSharedBlocksAt data toks cuts pos bw :=
  emitSharedBlocksAtSized_eq_fuel data toks (toks.size - pos + 1) pos (by omega) cuts bw

/-- The sized-tree shared-window candidate is byte-identical to the reference
    arbitrated candidate: `deflateRaw`'s level ≥ 8 branches and the roundtrip
    proofs see the old `deflateDynamicBlocksSharedAtTokens … chooseSplitsArbitrated`
    through this rewrite. -/
theorem deflateDynamicBlocksSharedSized_eq (data : ByteArray) (toks : Array LZ77Token) :
    deflateDynamicBlocksSharedSized data toks =
      deflateDynamicBlocksSharedAtTokens data toks chooseSplitsArbitrated := by
  unfold deflateDynamicBlocksSharedSized deflateDynamicBlocksSharedAtTokens
  split
  · rfl
  · simp only [chooseSplitsArbitratedSized, chooseSplitsArbitrated,
      sharedPartitionSized_fst]
    by_cases hlt : sharedPartitionBits toks (chooseSplitsHeuristic toks) 0 <
        sharedPartitionBits toks (fixedCadenceCuts sharedTokChunk toks.size) 0
    · simp only [if_pos hlt, emitSharedBlocksAtSized_eq]
    · simp only [if_neg hlt, emitSharedBlocksAtSized_eq]

end Zip.Native.Deflate
