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

end Zip.Native.Deflate
