import Zip.Spec.BitWriterCorrect
import Zip.Spec.BitstreamWriteCorrect

/-!
# BitWriter `bitLength` accounting — foundation for the block-size model

The level-≥5 DEFLATE dispatch sizes each candidate block (stored / fixed /
dynamic) from a single token pass and emits only the predicted-smallest
(`fixedBlockBytes` / `dynBlockBytes`, `Zip/Native/DeflateDynamic.lean`).
The emitted `.size` of a block is `⌈bitLength/8⌉` of the final writer after
`flush`, and `bitLength` accumulates additively across each field write.

This file establishes that additive accounting at the `BitWriter` level —
the "natural bridge" between `BitWriter.bitLength` and the existing
`BitWriterCorrect` `toBits` lemmas (issue #2489). The key observation is that
`toBits` lists *exactly* `bitLength` bits, so every `toBits` correspondence
lemma (`writeBits_toBits`, `writeHuffCode_toBits`, …) transfers to a `bitLength`
increment by reading off the appended segment's length.

The downstream block-byte identities (`fixedBlockBytes = (deflateFixedBlock …).size`
and `dynBlockBytes = (deflateDynamicBlockCore …).size`) are built on these
lemmas plus a frequency-dot-product ↔ token-sequence counting identity; that
remaining work is tracked separately.
-/

namespace Zip.Native.BitWriter

/-- `toBits` lists exactly `bitLength` bits: `bitLength` counts `8` bits per
    flushed byte plus the `bitCount` partial bits, and `toBits` materialises
    each of those. Holds unconditionally (no well-formedness needed) — it is a
    pure length count. This is the bridge that lets every `toBits`
    correspondence lemma pin down a `bitLength` increment. -/
theorem toBits_length (bw : BitWriter) : bw.toBits.length = bw.bitLength := by
  -- `toBits = bytesToBits bw.data ++ (partial bits)`; the first segment has
  -- length `data.size * 8`, the second `bitCount`.
  show ((bw.data.data.toList.flatMap Deflate.Spec.bytesToBits.byteToBits) ++
      (List.range bw.bitCount.toNat).map (fun i => bw.bitBuf.toNat.testBit i)).length = _
  rw [List.length_append, List.length_map, List.length_range]
  have hfst : (bw.data.data.toList.flatMap Deflate.Spec.bytesToBits.byteToBits).length
      = bw.data.size * 8 := Deflate.Spec.bytesToBits_length bw.data
  rw [hfst]
  rfl

/-- `bitLength` after `writeBits` grows by exactly the field width `n`. -/
theorem bitLength_writeBits (bw : BitWriter) (n : Nat) (val : UInt32)
    (hwf : bw.wf) (hn : n ≤ 25) :
    (bw.writeBits n val).bitLength = bw.bitLength + n := by
  rw [← toBits_length, writeBits_toBits bw n val hwf hn, List.length_append,
    Deflate.Correctness.writeBitsLSB_length, toBits_length]

/-- `bitLength` after `writeHuffCode` grows by exactly the code length `len`. -/
theorem bitLength_writeHuffCode (bw : BitWriter) (code : UInt16) (len : UInt8)
    (hwf : bw.wf) (hlen : len.toNat ≤ 15) :
    (bw.writeHuffCode code len).bitLength = bw.bitLength + len.toNat := by
  rw [← toBits_length, writeHuffCode_toBits bw code len hwf hlen, List.length_append,
    Huffman.Spec.natToBits_length, toBits_length]

/-- The flushed byte size of a (well-formed) writer is `⌈bitLength/8⌉`. `flush`
    pushes one final partial byte iff `bitCount > 0`; since `bitCount < 8`, that
    is exactly the ceiling division of the total bit count. -/
theorem flush_size (bw : BitWriter) (hwf : bw.wf) :
    bw.flush.size = (bw.bitLength + 7) / 8 := by
  obtain ⟨hbc_lt, _⟩ := hwf
  unfold flush bitLength
  by_cases hbc0 : bw.bitCount.toNat = 0
  · have hcond : ¬(bw.bitCount > 0) := by show ¬(0 < bw.bitCount.toNat); omega
    rw [if_neg hcond, hbc0]; omega
  · have hcond : bw.bitCount > 0 := by show 0 < bw.bitCount.toNat; omega
    rw [if_pos hcond, ByteArray.size_push]; omega

end Zip.Native.BitWriter
