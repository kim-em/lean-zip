import Zip.Native.Inflate

/-!
  Wide-buffer DEFLATE block/entry points (Track D, #2501 approach 1).

  The wide-buffer Huffman symbol decoder primitives (`refill`, `walkTree`,
  `decodeSym`, `takeBits`, `go`, `decodeHuffmanFastBuf`) now live in
  `Zip.Native.Inflate` (namespace `InflateBuf`), so the default `Inflate.inflateLoop`
  can call them. This file provides the *parallel* block loop and entry point
  (`inflateLoopBuf`, `InflateBuf.inflate`) built directly on the buffered decoder;
  `Zip.Spec.InflateBufCorrect` proves `inflateLoopBuf = Inflate.inflateLoop` and
  `InflateBuf.inflate = Inflate.inflateReference` (the verified tree-building
  reference, of which the production `Inflate.inflate` is the tree-free counterpart),
  which (now that `inflateLoop` itself runs the buffered decoder) is essentially a
  sanity bridge between the two spellings.
-/

namespace Zip.Native
open ZipCommon (BitReader)

namespace InflateBuf

/-- Block loop (mirrors `Inflate.inflateLoop`), using the wide-buffer decoder.
    Well-founded on remaining bits, like the original. -/
def inflateLoopBuf (br : BitReader) (output : ByteArray)
    (fixedLit fixedDist : HuffTree) (maxOut dataSize : Nat) :
    Except String (ByteArray × Nat) := do
  let (bfinal, br₁) ← br.readBits 1
  let (btype, br₂) ← br₁.readBits 2
  let (output', br') ← match btype with
    | 0 => Inflate.decodeStored br₂ output maxOut
    | 1 => decodeHuffmanFastBuf br₂ output fixedLit fixedDist maxOut
    | 2 => do
      let (litTree, distTree, br₃) ← Inflate.decodeDynamicTrees br₂
      decodeHuffmanFastBuf br₃ output litTree distTree maxOut
    | _ => throw s!"Inflate: reserved block type {btype}"
  if bfinal == 1 then
    return (output', br'.alignToByte.pos)
  else
    if _h₁ : br'.bitPos ≤ br.bitPos then throw "Inflate: no progress in inflate loop"
    else if _h₂ : dataSize * 8 < br'.bitPos then throw "Inflate: bit position out of range"
    else inflateLoopBuf br' output' fixedLit fixedDist maxOut dataSize
termination_by dataSize * 8 - br.bitPos
decreasing_by all_goals omega

/-- Wide-buffer `inflate` (entry point). `sizeHint` pre-reserves output capacity
    when the decompressed size is known (`0`, the default, reserves nothing); it is
    a capacity hint only, so `InflateBuf.inflate = Inflate.inflateReference` is
    unaffected. -/
def inflate (data : ByteArray) (maxOut : Nat := 1024 * 1024 * 1024)
    (sizeHint : Nat := 0) :
    Except String ByteArray := do
  let br : BitReader := { data, pos := 0, bitOff := 0 }
  let fixedLit ← HuffTree.fromLengths Inflate.fixedLitLengths
  let fixedDist ← HuffTree.fromLengths Inflate.fixedDistLengths
  let (output, _) ← inflateLoopBuf br (ByteArray.emptyWithCapacity sizeHint)
    fixedLit fixedDist maxOut data.size
  return output

/-- The output capacity hint is computationally inert: `inflate` with any `sizeHint`
    equals `inflate` with the default `0` (`ByteArray.emptyWithCapacity n` reduces to
    `{ data := Array.empty }` for every `n`). -/
@[simp] theorem inflate_sizeHint_eq (data : ByteArray) (maxOut sizeHint : Nat) :
    inflate data maxOut sizeHint = inflate data maxOut :=
  rfl

end InflateBuf
end Zip.Native
