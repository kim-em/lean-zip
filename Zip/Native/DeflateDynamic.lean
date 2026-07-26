import Zip.Native.Deflate
import Zip.Native.DeflateFreqs
import Zip.Native.DeflateFreqsFused
import Zip.Spec.DeflateFreqsFusedCorrect
import Zip.Native.DeflateParse
import Zip.Native.DeflateL5
import Zip.Spec.DeflateEncodeDynamic
import Zip.Spec.DeflateStoredCorrect
import Zip.Spec.EmitTokensCorrect
import Zip.Spec.HuffmanEncode

/-!
  Native DEFLATE compressor — dynamic Huffman blocks (Level 5).

  Uses dynamic Huffman codes optimized for the input data rather than
  the fixed codes defined in RFC 1951 §3.2.6.
-/

namespace Zip.Native.Deflate

/-- Emit LZ77 tokens using the given lit/len and distance Huffman codes.
    Requires `litCodes.size ≥ 286` (for lit/length symbols 0..285) and
    `distCodes.size ≥ 30` (for distance symbols 0..29); callers discharge
    these from `canonicalCodes_size` + `computeCodeLengths_length`.

    Inner `if h : …` guards convert the Huffman table reads to proven-
    bounds access. The `else` branches are dead code (ruled out by
    `nativeFindLengthCode_idx_bound` / `nativeFindDistCode_idx_bound`
    combined with the `hlit` / `hdist` size invariants); matching the
    pattern used by `emitTokens` keeps spec proofs uniform. -/
def emitTokensWithCodes (bw : BitWriter) (tokens : Array LZ77Token)
    (litCodes distCodes : Array (UInt16 × UInt8))
    (hlit : litCodes.size ≥ 286) (hdist : distCodes.size ≥ 30)
    (i : Nat) : BitWriter :=
  if h : i < tokens.size then
    match tokens[i] with
    | .literal b =>
      have : b.toNat < litCodes.size := by
        have := UInt8.toNat_lt b; omega
      let (code, len) := litCodes[b.toNat]
      emitTokensWithCodes (bw.writeHuffCode code len) tokens litCodes distCodes hlit hdist (i + 1)
    | .reference length distance =>
      match findLengthCode length with
      | some (idx, extraCount, extraVal) =>
        if hlitlt : idx + 257 < litCodes.size then
          let (code, len) := litCodes[idx + 257]
          let bw := bw.writeHuffCode code len
          let bw := bw.writeBits extraCount extraVal
          match findDistCode distance with
          | some (dIdx, dExtraCount, dExtraVal) =>
            if hdistlt : dIdx < distCodes.size then
              let (dCode, dLen) := distCodes[dIdx]
              let bw := bw.writeHuffCode dCode dLen
              emitTokensWithCodes (bw.writeBits dExtraCount dExtraVal) tokens litCodes distCodes hlit hdist (i + 1)
            else emitTokensWithCodes bw tokens litCodes distCodes hlit hdist (i + 1)
          | none => emitTokensWithCodes bw tokens litCodes distCodes hlit hdist (i + 1)
        else emitTokensWithCodes bw tokens litCodes distCodes hlit hdist (i + 1)
      | none => emitTokensWithCodes bw tokens litCodes distCodes hlit hdist (i + 1)
  else bw
termination_by tokens.size - i

/-! ## Packed-token dynamic-code emission (Wave 3b stage C)

`emitTokensWithCodesP` walks the `packTok`-encoded `UInt32` stream directly,
so the dynamic emit path never materializes boxed `LZ77Token`s. As with
`emitTokensP`/`emitRefFixedP` (`Zip/Native/Deflate.lean`) and `tokenFreqsP`
(see the landmine note in `Zip/Native/DeflateFreqs.lean`), the reference arm
— a match scrutinee over `findLengthCode` applied to a stuck bit-extracted
word — must live in the non-recursive helper `emitRefWithCodesP`, never
inline in the well-founded loop body. `Zip/Spec/EmitPackedCorrect.lean`
proves the loop equal to `emitTokensWithCodes` over the boxed view. -/

/-- Emit one packed *reference* token (tag bit set) with the given Huffman
    codes: decode the length/distance fields with `unpackTok`'s bit
    expressions and write exactly the `writeHuffCode`/`writeBits` sequence of
    `emitTokensWithCodes`'s reference arm (including its dead-code `else`
    fallbacks, so the equality proof aligns branch-for-branch). -/
@[inline] def emitRefWithCodesP (bw : BitWriter)
    (litCodes distCodes : Array (UInt16 × UInt8)) (w : UInt32) : BitWriter :=
  let lw := lenCodeWord (((w >>> 16) &&& 0x7FFF).toNat)
  let idx := codeIdx lw
  if hlitlt : idx + 257 < litCodes.size then
    let (code, len) := litCodes[idx + 257]
    let bw := bw.writeHuffCode code len
    let bw := bw.writeBits (codeExtra lw) (codeVal lw)
    let dw := distCodeWord ((w &&& 0xFFFF).toNat)
    let dIdx := codeIdx dw
    if hdistlt : dIdx < distCodes.size then
      let (dCode, dLen) := distCodes[dIdx]
      let bw := bw.writeHuffCode dCode dLen
      bw.writeBits (codeExtra dw) (codeVal dw)
    else bw
  else bw

/-- Packed-token form of `emitTokensWithCodes` (same `hlit`/`hdist` size
    hypotheses): emit the packed `UInt32` stream with the given lit/len and
    distance Huffman codes. Literals (tag bit clear) read the byte field
    directly; references go through `emitRefWithCodesP`. Equal to
    `emitTokensWithCodes` over the boxed view for every word array
    (`emitTokensWithCodesP_eq`). -/
def emitTokensWithCodesP (bw : BitWriter) (tokens : Array UInt32)
    (litCodes distCodes : Array (UInt16 × UInt8))
    (hlit : litCodes.size ≥ 286) (hdist : distCodes.size ≥ 30)
    (i : Nat) : BitWriter :=
  if h : i < tokens.size then
    let w := tokens[i]
    if w &&& ((1 : UInt32) <<< 31) = 0 then
      have : w.toUInt8.toNat < litCodes.size := by
        have := UInt8.toNat_lt w.toUInt8; omega
      let (code, len) := litCodes[w.toUInt8.toNat]
      emitTokensWithCodesP (bw.writeHuffCode code len) tokens litCodes distCodes hlit hdist (i + 1)
    else
      emitTokensWithCodesP (emitRefWithCodesP bw litCodes distCodes w) tokens litCodes distCodes
        hlit hdist (i + 1)
  else bw
termination_by tokens.size - i

/-! ## Packed Huffman-code tables (#2827)

`litCodes`/`distCodes` are `Array (UInt16 × UInt8)`: every per-token code
lookup fetches a boxed `Prod` cell and chases it with two `lean_ctor_get`s,
and every `writeHuffCode` re-reverses the code's bits (`reverse16`, an
out-of-line call) and down-shifts them — per symbol, for values that are
table constants. Packing each entry into one `UInt32` holding the
**pre-reversed** code (`reverse16 code >>> (16 - len)`, bits 0–15) and the
bit length (bits 16–23) turns the lookup into a single tagged-scalar array
read plus two register ops, and lets the walk write through the leaner
`BitWriter.writeRevCode` (no per-symbol reversal). `emitTokensWithCodesPT`
is the packed-table twin of `emitTokensWithCodesP` (equal by
`emitTokensWithCodesPT_eq`, `Zip/Spec/EmitPackedCorrect.lean`); the block
emitters pack the tables once per block (`packCodeTab`, ≤ 316 entries)
before the token walk. -/

/-- Pack one canonical-code entry `(code, bitLength)` into a `UInt32`:
    the LSB-first packing-order reversal `reverse16 code >>> (16 - len)` in
    bits 0–15 (always < 2¹⁶, so the `UInt16` round-trip is lossless), and the
    bit length in bits 16–23. -/
@[inline] def packCodeEntry (e : UInt16 × UInt8) : UInt32 :=
  ((BitWriter.reverse16 e.1).toUInt64 >>> (16 - e.2.toUInt64)).toUInt16.toUInt32 |||
    (e.2.toUInt32 <<< 16)

/-- Pack a canonical-code table for the emit loop (one `UInt32` per entry). -/
def packCodeTab (t : Array (UInt16 × UInt8)) : Array UInt32 :=
  t.map packCodeEntry

@[simp] theorem packCodeTab_size (t : Array (UInt16 × UInt8)) :
    (packCodeTab t).size = t.size := Array.size_map ..

/-- Packed-table twin of `emitRefWithCodesP`: identical branch structure,
    with each `(code, len)` pair read replaced by one packed-word read
    (`e.toUInt16` / `(e >>> 16).toUInt8`) written through `writeRevCode`
    (the table code is pre-reversed). Equal to `emitRefWithCodesP` over
    `packCodeTab` (`emitRefWithCodesPT_eq`). -/
@[inline] def emitRefWithCodesPT (bw : BitWriter)
    (litT distT : Array UInt32) (w : UInt32) : BitWriter :=
  let lw := lenCodeWord (((w >>> 16) &&& 0x7FFF).toNat)
  let idx := codeIdx lw
  if hlitlt : idx + 257 < litT.size then
    let e := litT[idx + 257]
    let bw := bw.writeRevCodeExtra e.toUInt16 (e >>> 16).toUInt8 (codeExtra lw) (codeVal lw)
    let dw := distCodeWord ((w &&& 0xFFFF).toNat)
    let dIdx := codeIdx dw
    if hdistlt : dIdx < distT.size then
      let de := distT[dIdx]
      bw.writeRevCodeExtra de.toUInt16 (de >>> 16).toUInt8 (codeExtra dw) (codeVal dw)
    else bw
  else bw

/-- Packed-table twin of `emitTokensWithCodesP` (same size hypotheses, now on
    the packed tables): walk the packed token stream reading Huffman codes
    from `packCodeTab`-packed `UInt32` tables. Equal to `emitTokensWithCodesP`
    for every word array (`emitTokensWithCodesPT_eq`). -/
def emitTokensWithCodesPT (bw : BitWriter) (tokens : Array UInt32)
    (litT distT : Array UInt32)
    (hlit : litT.size ≥ 286) (hdist : distT.size ≥ 30)
    (i : Nat) : BitWriter :=
  if h : i < tokens.size then
    let w := tokens[i]
    if w &&& ((1 : UInt32) <<< 31) = 0 then
      have : w.toUInt8.toNat < litT.size := by
        have := UInt8.toNat_lt w.toUInt8; omega
      let e := litT[w.toUInt8.toNat]
      emitTokensWithCodesPT (bw.writeRevCode e.toUInt16 (e >>> 16).toUInt8) tokens litT distT
        hlit hdist (i + 1)
    else
      emitTokensWithCodesPT (emitRefWithCodesPT bw litT distT w) tokens litT distT
        hlit hdist (i + 1)
  else bw
termination_by tokens.size - i



/-- USize-index twin of `emitTokensWithCodesPT` (measurement candidate): same
    walk with the loop index in `USize`, `uget` token reads, and the
    addressability witness `hsz` hoisted out of the loop. Equal to
    `emitTokensWithCodesPT` at `i.toNat` (`emitTokensWithCodesPTU_eq`). -/
def emitTokensWithCodesPTU (bw : BitWriter) (tokens : Array UInt32)
    (litT distT : Array UInt32)
    (hlit : litT.size ≥ 286) (hdist : distT.size ≥ 30)
    (hsz : tokens.size < USize.size)
    (i : USize) : BitWriter :=
  if h : i.toNat < tokens.size then
    let w := tokens.uget i (by exact h)
    have hstep : (i + 1).toNat = i.toNat + 1 := by
      have hUS : USize.size = 2 ^ System.Platform.numBits := rfl
      rw [USize.toNat_add, USize.toNat_one]; exact Nat.mod_eq_of_lt (by omega)
    if w &&& ((1 : UInt32) <<< 31) = 0 then
      have : w.toUInt8.toNat < litT.size := by
        have := UInt8.toNat_lt w.toUInt8; omega
      let e := litT[w.toUInt8.toNat]
      emitTokensWithCodesPTU (bw.writeRevCode e.toUInt16 (e >>> 16).toUInt8) tokens litT distT
        hlit hdist hsz (i + 1)
    else
      emitTokensWithCodesPTU (emitRefWithCodesPT bw litT distT w) tokens litT distT
        hlit hdist hsz (i + 1)
  else bw
termination_by tokens.size - i.toNat
decreasing_by all_goals (rw [hstep]; omega)

/-- Guarded dispatch to the USize emit loop: one `USize` round-trip check per
    block unlocks the de-boxed index walk; the (never-taken) fallback is the
    `Nat` loop, so this equals `emitTokensWithCodesPT ... 0`
    (`emitTokensWithCodesPTG_eq`). -/
@[inline] def emitTokensWithCodesPTG (bw : BitWriter) (tokens : Array UInt32)
    (litT distT : Array UInt32)
    (hlit : litT.size ≥ 286) (hdist : distT.size ≥ 30) : BitWriter :=
  if hg : tokens.size.toUSize.toNat = tokens.size then
    have hsz : tokens.size < USize.size := by
      rw [← hg]; exact USize.toNat_lt_two_pow_numBits _
    emitTokensWithCodesPTU bw tokens litT distT hlit hdist hsz 0
  else
    emitTokensWithCodesPT bw tokens litT distT hlit hdist 0

/-- Flat-state runtime loop for `emitTokensWithCodesTAPT`.  It carries the
    three `BitWriter` fields separately, avoiding one writer reconstruction per
    token.  A reference token's length-code/extra and distance-code/extra bits
    are packed into one `UInt64` field before they are merged into the pending
    accumulator.  If that field would fill all 64 accumulator bits, already
    complete pending bytes are drained first; production callers always enter
    with fewer than 32 pending bits, so this leaves fewer than 8 bits and the
    at-most-48-bit reference field then fits without overflow. -/
@[inline] def emitRefWithCodesPTFlat (bw : BitWriter)
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
      let distBits : UInt64 := de.toUInt16.toUInt64 |||
        (((codeVal dw).toUInt64 &&& distMask) <<< distN.toUInt64)
      let bits : UInt64 := lenBits ||| (distBits <<< lenTotal.toUInt64)
      bw.writeBits64 (lenTotal + distN + distExtraN) bits
    else
      bw.writeBits64 lenTotal lenBits
  else bw

def emitTokensWithCodesTAPTFlatLoop (data : ByteArray) (acc : UInt64) (bc : UInt32)
    (tokens : TokenArray) (litT distT : Array UInt32)
    (hlit : litT.size ≥ 286) (hdist : distT.size ≥ 30)
    (i : Nat) : BitWriter :=
  if h : i < tokens.size then
    let w := tokens.get i h
    if w &&& ((1 : UInt32) <<< 31) = 0 then
      have he : w.toUInt8.toNat < litT.size := by
        have := UInt8.toNat_lt w.toUInt8
        omega
      let e := litT[w.toUInt8.toNat]
      let n : UInt32 := (e >>> 16) &&& 0xFF
      let bw' := BitWriter.writeBits64 ⟨data, acc, bc.toUInt8⟩ n e.toUInt16.toUInt64
      emitTokensWithCodesTAPTFlatLoop bw'.data bw'.bitBuf bw'.bitCount.toUInt32
        tokens litT distT hlit hdist (i + 1)
    else
      let bw' := emitRefWithCodesPTFlat ⟨data, acc, bc.toUInt8⟩ litT distT w
      emitTokensWithCodesTAPTFlatLoop bw'.data bw'.bitBuf bw'.bitCount.toUInt32
        tokens litT distT hlit hdist (i + 1)
  else
    ⟨data, acc, bc.toUInt8⟩
termination_by tokens.size - i

/-- Production-specialized form of the flat token loop.  This spells out the
    bounded `writeBits64` transitions so the native compiler keeps the pending
    accumulator and count in scalar registers throughout the hot loop. -/
def emitTokensWithCodesTAPTFlatFastLoop (data : ByteArray) (acc : UInt64) (bc : UInt32)
    (tokens : TokenArray) (litT distT : Array UInt32)
    (hlit : litT.size ≥ 286) (hdist : distT.size ≥ 30)
    (i : Nat) : BitWriter :=
  if h : i < tokens.size then
    let w := tokens.get i h
    if w &&& ((1 : UInt32) <<< 31) = 0 then
      have he : w.toUInt8.toNat < litT.size := by
        have := UInt8.toNat_lt w.toUInt8
        omega
      let e := litT[w.toUInt8.toNat]
      let n : UInt32 := (e >>> 16) &&& 0xFF
      let acc' := acc ||| (e.toUInt16.toUInt64 <<< bc.toUInt64)
      let total := bc + n
      if total ≥ 32 then
        let k := total >>> 3
        emitTokensWithCodesTAPTFlatFastLoop
          (BitWriter.flushBytesWideU data acc' k)
          (acc' >>> (k.toUInt64 <<< 3)) (total &&& 7).toUInt8.toUInt32
          tokens litT distT hlit hdist (i + 1)
      else
        emitTokensWithCodesTAPTFlatFastLoop data acc' total.toUInt8.toUInt32
          tokens litT distT hlit hdist (i + 1)
    else
      let lw := lenCodeWord (((w >>> 16) &&& 0x7FFF).toNat)
      let idx := codeIdx lw
      if hlitlt : idx + 257 < litT.size then
        let e := litT[idx + 257]
        let lenN : UInt32 := (e >>> 16) &&& 0xFF
        let lenExtraN : UInt32 := ((lw >>> 8) &&& 0xFF)
        let lenMask : UInt64 := (1 <<< lenExtraN.toUInt64) - 1
        let lenBits : UInt64 :=
          e.toUInt16.toUInt64 |||
            ((codeVal lw).toUInt64 &&& lenMask) <<< lenN.toUInt64
        let lenTotal := lenN + lenExtraN
        let dw := distCodeWord ((w &&& 0xFFFF).toNat)
        let dIdx := codeIdx dw
        if hdistlt : dIdx < distT.size then
          let de := distT[dIdx]
          let distN : UInt32 := (de >>> 16) &&& 0xFF
          let distExtraN : UInt32 := ((dw >>> 8) &&& 0xFF)
          let distMask : UInt64 := (1 <<< distExtraN.toUInt64) - 1
          let distOff := lenTotal
          let bits : UInt64 :=
            lenBits ||| (de.toUInt16.toUInt64 <<< distOff.toUInt64) |||
              (((codeVal dw).toUInt64 &&& distMask) <<<
                (distOff.toUInt64 + distN.toUInt64))
          let n := lenTotal + distN + distExtraN
          if bc + n ≥ 64 then
            let k0 := bc >>> 3
            let data0 := BitWriter.flushBytesWideU data acc k0
            let acc0 := acc >>> (k0.toUInt64 <<< 3)
            let bc0 := bc &&& 7
            let acc' := acc0 ||| (bits <<< bc0.toUInt64)
            let total := bc0 + n
            if total ≥ 32 then
              let k := total >>> 3
              emitTokensWithCodesTAPTFlatFastLoop
                (BitWriter.flushBytesWideU data0 acc' k)
                (acc' >>> (k.toUInt64 <<< 3)) (total &&& 7).toUInt8.toUInt32
                tokens litT distT hlit hdist (i + 1)
            else
              emitTokensWithCodesTAPTFlatFastLoop data0 acc' total.toUInt8.toUInt32
                tokens litT distT hlit hdist (i + 1)
          else
            let acc' := acc ||| (bits <<< bc.toUInt64)
            let total := bc + n
            if total ≥ 32 then
              let k := total >>> 3
              emitTokensWithCodesTAPTFlatFastLoop
                (BitWriter.flushBytesWideU data acc' k)
                (acc' >>> (k.toUInt64 <<< 3)) (total &&& 7).toUInt8.toUInt32
                tokens litT distT hlit hdist (i + 1)
            else
              emitTokensWithCodesTAPTFlatFastLoop data acc' total.toUInt8.toUInt32
                tokens litT distT hlit hdist (i + 1)
        else
          let acc' := acc ||| (lenBits <<< bc.toUInt64)
          let total := bc + lenTotal
          if total ≥ 32 then
            let k := total >>> 3
            emitTokensWithCodesTAPTFlatFastLoop
              (BitWriter.flushBytesWideU data acc' k)
              (acc' >>> (k.toUInt64 <<< 3)) (total &&& 7).toUInt8.toUInt32
              tokens litT distT hlit hdist (i + 1)
          else
            emitTokensWithCodesTAPTFlatFastLoop data acc' total.toUInt8.toUInt32
              tokens litT distT hlit hdist (i + 1)
      else
        emitTokensWithCodesTAPTFlatFastLoop data acc bc
          tokens litT distT hlit hdist (i + 1)
  else
    ⟨data, acc, bc.toUInt8⟩
termination_by tokens.size - i

/-- Flat-state packed-table emitter used by the proof-gated single-block
    production core. -/
def emitTokensWithCodesTAPTFlat (bw : BitWriter) (tokens : TokenArray)
    (litT distT : Array UInt32)
    (hlit : litT.size ≥ 286) (hdist : distT.size ≥ 30)
    (i : Nat) : BitWriter :=
  emitTokensWithCodesTAPTFlatLoop bw.data bw.bitBuf bw.bitCount.toUInt32
    tokens litT distT hlit hdist i

/-- `TokenArray` twin of `emitTokensWithCodesPT` (stage 6/7 of the token-stream
    unboxing): the packed-table dynamic emit loop reading each packed word from
    the 4-byte-per-token `TokenArray` via `.get` instead of the 8-byte
    `Array UInt32` slot, so the dynamic-block emit never materializes the boxed
    token buffer.  The Huffman code tables stay `Array UInt32` (they are the
    per-block ≤316-entry `packCodeTab` outputs, not the token stream).  Equal to
    `emitTokensWithCodesPT` over the `.toArray` view
    (`emitTokensWithCodesTAPT_toArray`). -/
def emitTokensWithCodesTAPT (bw : BitWriter) (tokens : TokenArray)
    (litT distT : Array UInt32)
    (hlit : litT.size ≥ 286) (hdist : distT.size ≥ 30)
    (i : Nat) : BitWriter :=
  if h : i < tokens.size then
    let w := tokens.get i h
    if w &&& ((1 : UInt32) <<< 31) = 0 then
      have : w.toUInt8.toNat < litT.size := by
        have := UInt8.toNat_lt w.toUInt8; omega
      let e := litT[w.toUInt8.toNat]
      emitTokensWithCodesTAPT (bw.writeRevCode e.toUInt16 (e >>> 16).toUInt8) tokens litT distT
        hlit hdist (i + 1)
    else
      emitTokensWithCodesTAPT (emitRefWithCodesPT bw litT distT w) tokens litT distT
        hlit hdist (i + 1)
  else bw
termination_by tokens.size - i

/-- Zero-index entry point for the flat implementation.  Keeping the production
    route fixed at zero lets native code specialize away the generic boxed
    starting-index path while the public proof helper remains general. -/
def emitTokensWithCodesTAPTFlatZero (bw : BitWriter) (tokens : TokenArray)
    (litT distT : Array UInt32)
    (hlit : litT.size ≥ 286) (hdist : distT.size ≥ 30) : BitWriter :=
  emitTokensWithCodesTAPTFlatFastLoop bw.data bw.bitBuf bw.bitCount.toUInt32
    tokens litT distT hlit hdist 0

/-- Logical proof helper for the flat emitter. The proof-gated single-block
    production route calls `emitTokensWithCodesTAPTFlatZero` directly and uses
    `emitTokensWithCodesTAPTFlatZero_eq_routed` to connect that implementation
    to this body under its canonical code-table bounds. -/
def emitTokensWithCodesTAPTFlatRouted (bw : BitWriter) (tokens : TokenArray)
    (litT distT : Array UInt32)
    (hlit : litT.size ≥ 286) (hdist : distT.size ≥ 30) : BitWriter :=
  emitTokensWithCodesTAPTFlat bw tokens litT distT hlit hdist 0

/-- Write the dynamic Huffman tree header via BitWriter.
    This is the native equivalent of spec `encodeDynamicTrees`, writing
    bits through BitWriter instead of producing `List Bool`.

    Takes lit/len code lengths and distance code lengths (as `List Nat`),
    writes HLIT, HDIST, HCLEN, CL code lengths, and RLE-encoded entries. -/
def writeDynamicHeader (bw : BitWriter) (litLens distLens : List Nat) : BitWriter :=
  let hlit := litLens.length - 257
  let hdist := distLens.length - 1
  -- Step 1: RLE-encode the concatenated code lengths
  let allLens := litLens ++ distLens
  let clEntries := Deflate.Spec.rlEncodeLengths allLens
  -- Step 2: Compute CL code lengths from symbol frequencies
  let clFreqs := Deflate.Spec.clSymbolFreqs clEntries
  let clFreqPairs := (List.range clFreqs.length).map fun i => (i, clFreqs.getD i 0)
  let clLens := Huffman.Spec.computeCodeLengths clFreqPairs 19 7
  -- Step 3: Build CL canonical codes
  let clLengthsArr : Array UInt8 := clLens.toArray.map Nat.toUInt8
  let clCodes := canonicalCodes clLengthsArr 7
  have hclSize : clCodes.size ≥ 19 := by
    have h1 : clCodes.size = clLengthsArr.size := canonicalCodes_size clLengthsArr 7
    have h2 : clLengthsArr.size = clLens.length := by
      simp [clLengthsArr, List.size_toArray]
    have h3 : clLens.length = 19 := Huffman.Spec.computeCodeLengths_length clFreqPairs 19 7
    omega
  -- Step 4: Determine HCLEN
  let numCodeLen := Deflate.Spec.computeHCLEN clLens
  let hclen := numCodeLen - 4
  -- Step 5: Write HLIT (5 bits), HDIST (5 bits), HCLEN (4 bits)
  let bw := bw.writeBits 5 hlit.toUInt32
  let bw := bw.writeBits 5 hdist.toUInt32
  let bw := bw.writeBits 4 hclen.toUInt32
  -- Step 6: Write CL code lengths in clPermutation order (3 bits each)
  let bw := writeCLLengths bw clLens numCodeLen 0
  -- Step 7: Write RLE entries using CL Huffman codes
  writeCLEntries bw clCodes clEntries hclSize
where
  writeCLLengths (bw : BitWriter) (clLens : List Nat) (numCodeLen i : Nat) : BitWriter :=
    if i < numCodeLen then
      let pos := Deflate.Spec.clPermutation.getD i 0
      let len := clLens.getD pos 0
      writeCLLengths (bw.writeBits 3 len.toUInt32) clLens numCodeLen (i + 1)
    else bw
  termination_by numCodeLen - i
  writeCLEntries (bw : BitWriter) (clCodes : Array (UInt16 × UInt8))
      (entries : List (Nat × Nat)) (hcl : clCodes.size ≥ 19) : BitWriter :=
    match entries with
    | [] => bw
    | (code, extra) :: rest =>
      if h : code < clCodes.size then
        let (cw, cwLen) := clCodes[code]
        let bw := bw.writeHuffCode cw cwLen
        let bw :=
          if code == 16 then bw.writeBits 2 extra.toUInt32
          else if code == 17 then bw.writeBits 3 extra.toUInt32
          else if code == 18 then bw.writeBits 7 extra.toUInt32
          else bw
        writeCLEntries bw clCodes rest hcl
      else
        writeCLEntries bw clCodes rest hcl


/-! ## Header-plan reuse across sizing and emit (#2627)

`writeDynamicHeader` does its expensive work *before* touching the `BitWriter`:
RLE-encoding the ~316 concatenated code lengths, building the CL Huffman tree
(`computeCodeLengths` over the 19-symbol alphabet), and laying out its canonical
codes. The single-block dispatch (`deflateRawBaseP`) ran all of that **twice** —
once to *size* the dynamic candidate (`dynBlockBytes`, header bits into an empty
writer) and again to *emit* it (`deflateDynamicBlockCoreP`). Measured at ~17 µs
per call, that duplicated build was 7–12% of a small-file level-6 compress.

`dynHeaderCodes` isolates the BitWriter-independent build into a reusable plan;
`writeDynamicHeaderWith` writes a header from a precomputed plan. The dispatch
computes the plan once and threads it to both the sizer (`dynBlockBytesWith`)
and the emitter (`deflateDynamicBlockCorePWith`). `writeDynamicHeader` and its
spec (`writeDynamicHeader_spec`/`_wf`) stay as the reference; the plan path is
proved equal to it (`writeDynamicHeaderWith_dynHeaderCodes`), so the size models
and roundtrip are byte-identical. -/

/-- The BitWriter-independent part of a dynamic-tree header: the CL canonical
    codes, the RLE entries over the concatenated code lengths, the CL code
    lengths, and `numCodeLen` (HCLEN + 4). Exactly the values `writeDynamicHeader`
    computes in its Steps 1–4. -/
structure DynHeaderPlan where
  /-- CL Huffman canonical codes (`(code, bitLength)` per symbol), size ≥ 19. -/
  clCodes : Array (UInt16 × UInt8)
  /-- RLE entries `(symbol, extra)` for the concatenated lit/len ++ dist lengths. -/
  clEntries : List (Nat × Nat)
  /-- CL code lengths (19 entries). -/
  clLens : List Nat
  /-- Number of CL code lengths written (HCLEN + 4), `computeHCLEN clLens`. -/
  numCodeLen : Nat

/-- Build the `DynHeaderPlan` for the given lit/len and distance code lengths.
    This is the duplicated work that `dynBlockBytes` (sizing) and
    `deflateDynamicBlockCore` (emit) each used to redo; the dispatch now runs it
    once. The body is exactly Steps 1–4 of `writeDynamicHeader`. -/
def dynHeaderCodes (litLens distLens : List Nat) : DynHeaderPlan :=
  let allLens := litLens ++ distLens
  let clEntries := Deflate.Spec.rlEncodeLengths allLens
  let clFreqs := Deflate.Spec.clSymbolFreqs clEntries
  let clFreqPairs := (List.range clFreqs.length).map fun i => (i, clFreqs.getD i 0)
  let clLens := Huffman.Spec.computeCodeLengths clFreqPairs 19 7
  let clLengthsArr : Array UInt8 := clLens.toArray.map Nat.toUInt8
  let clCodes := canonicalCodes clLengthsArr 7
  let numCodeLen := Deflate.Spec.computeHCLEN clLens
  { clCodes, clEntries, clLens, numCodeLen }

/-- `dynHeaderCodes` produces exactly 19 CL canonical codes. -/
theorem dynHeaderCodes_clCodes_size (litLens distLens : List Nat) :
    (dynHeaderCodes litLens distLens).clCodes.size = 19 := by
  unfold dynHeaderCodes
  simp only
  rw [canonicalCodes_size _ 7, Array.size_map, List.size_toArray,
    Huffman.Spec.computeCodeLengths_length]

/-- Write a dynamic Huffman tree header from a precomputed `DynHeaderPlan`
    (Steps 5–7 of `writeDynamicHeader`): HLIT/HDIST/HCLEN, then the CL code
    lengths in permutation order, then the RLE entries via the CL codes. The
    `hcl` size witness is the (phantom, proof-irrelevant) one `writeCLEntries`
    threads.

    **Invariant**: `p` must be `dynHeaderCodes litLens distLens` — only then does
    the header match the lengths (and equal `writeDynamicHeader bw litLens distLens`,
    by `writeDynamicHeaderWith_dynHeaderCodes`). Passing an unrelated plan writes a
    header for the *plan's* lengths, not `litLens`/`distLens`. The dispatch builds
    the plan from exactly these lengths; this is not a general-purpose writer. -/
def writeDynamicHeaderWith (bw : BitWriter) (litLens distLens : List Nat)
    (p : DynHeaderPlan) (hcl : p.clCodes.size ≥ 19) : BitWriter :=
  let hlit := litLens.length - 257
  let hdist := distLens.length - 1
  let hclen := p.numCodeLen - 4
  let bw := bw.writeBits 5 hlit.toUInt32
  let bw := bw.writeBits 5 hdist.toUInt32
  let bw := bw.writeBits 4 hclen.toUInt32
  let bw := writeDynamicHeader.writeCLLengths bw p.clLens p.numCodeLen 0
  writeDynamicHeader.writeCLEntries bw p.clCodes p.clEntries hcl

/-- The plan path agrees with `writeDynamicHeader`: writing from
    `dynHeaderCodes litLens distLens` reproduces `writeDynamicHeader` bit-for-bit
    (the `hcl` witness is irrelevant, as `writeCLEntries` re-checks bounds). -/
theorem writeDynamicHeaderWith_dynHeaderCodes (bw : BitWriter) (litLens distLens : List Nat)
    (hcl : (dynHeaderCodes litLens distLens).clCodes.size ≥ 19) :
    writeDynamicHeaderWith bw litLens distLens (dynHeaderCodes litLens distLens) hcl =
      writeDynamicHeader bw litLens distLens := by
  unfold writeDynamicHeaderWith writeDynamicHeader dynHeaderCodes
  rfl


/-- Helper: `canonicalCodes` of lit/len code lengths produced by
    `computeCodeLengths _ 286 15` has size exactly 286. -/
private theorem deflateDynamic.litCodes_size (litFreqPairs : List (Nat × Nat)) :
    (canonicalCodes
      ((Huffman.Spec.computeCodeLengths litFreqPairs 286 15).toArray.map Nat.toUInt8)).size
      = 286 := by
  rw [canonicalCodes_size, Array.size_map, List.size_toArray,
    Huffman.Spec.computeCodeLengths_length]

/-- Helper: 256 is in bounds for `canonicalCodes` of lit/len code lengths
    produced by `computeCodeLengths _ 286 15`. -/
private theorem deflateDynamic.lit256_lt (litFreqPairs : List (Nat × Nat)) :
    256 < (canonicalCodes
      ((Huffman.Spec.computeCodeLengths litFreqPairs 286 15).toArray.map Nat.toUInt8)).size := by
  rw [deflateDynamic.litCodes_size]; omega

/-- Helper: `canonicalCodes` of a distance length list of length 30 has size 30. -/
private theorem deflateDynamic.distCodes_size (distLens : List Nat)
    (hlen : distLens.length = 30) :
    (canonicalCodes (distLens.toArray.map Nat.toUInt8)).size = 30 := by
  rw [canonicalCodes_size, Array.size_map, List.size_toArray, hlen]


/-- Emit a dynamic Huffman DEFLATE block from precomputed LZ77 tokens **and**
    precomputed lit/len and distance code lengths (with their length invariants).
    Produces a single DEFLATE block with BFINAL=1, BTYPE=10.

    Split out of `deflateDynamicBlock` so the size-then-emit dispatch can size the
    block from the same `litLens`/`distLens` it later emits with, instead of
    recomputing the code lengths (`computeCodeLengths` over the 286/30 alphabets)
    a second time. -/
def deflateDynamicBlockCore (data : ByteArray) (tokens : Array LZ77Token)
    (litLens distLens : List Nat)
    (hlit : litLens.length = 286) (hdist : distLens.length = 30) : ByteArray :=
  -- Build canonical codes from the given lengths
  let litCodes := canonicalCodes (litLens.toArray.map Nat.toUInt8)
  let distCodes := canonicalCodes (distLens.toArray.map Nat.toUInt8)
  -- Write block header: BFINAL=1, BTYPE=10 (dynamic Huffman)
  let bw := BitWriter.empty
  let bw := bw.writeBits 1 1  -- BFINAL
  let bw := bw.writeBits 2 2  -- BTYPE = 10
  -- Write dynamic tree header
  let bw := writeDynamicHeader bw litLens distLens
  -- Size invariants from `canonicalCodes_size` + the length hypotheses.
  have hlit_size : litCodes.size ≥ 286 := by
    show (canonicalCodes (litLens.toArray.map Nat.toUInt8)).size ≥ 286
    rw [canonicalCodes_size, Array.size_map, List.size_toArray]; omega
  have hdist_size : distCodes.size ≥ 30 := by
    show (canonicalCodes (distLens.toArray.map Nat.toUInt8)).size ≥ 30
    rw [canonicalCodes_size, Array.size_map, List.size_toArray]; omega
  have h256 : 256 < litCodes.size := by
    show 256 < (canonicalCodes (litLens.toArray.map Nat.toUInt8)).size
    rw [canonicalCodes_size, Array.size_map, List.size_toArray]; omega
  -- Write tokens, then the end-of-block symbol (256, in bounds via `h256`).
  if data.size == 0 then
    -- Empty: just write end-of-block
    let (code, len) := litCodes[256]'h256
    let bw := bw.writeHuffCode code len
    bw.flush
  else
    let bw := emitTokensWithCodes bw tokens litCodes distCodes hlit_size hdist_size 0
    let (code, len) := litCodes[256]'h256
    let bw := bw.writeHuffCode code len
    bw.flush

/-- Packed-token form of `deflateDynamicBlockCore` (Wave 3b stage C): emit a
    dynamic Huffman block directly from the packed `UInt32` stream — same
    body with `emitTokensWithCodesP` in place of `emitTokensWithCodes`.
    Equal to `deflateDynamicBlockCore` over the boxed view
    (`deflateDynamicBlockCoreP_eq` in `Zip/Spec/EmitPackedCorrect.lean`). -/
def deflateDynamicBlockCoreP (data : ByteArray) (tokens : TokenArray)
    (litLens distLens : List Nat)
    (hlit : litLens.length = 286) (hdist : distLens.length = 30) : ByteArray :=
  let litCodes := canonicalCodes (litLens.toArray.map Nat.toUInt8)
  let distCodes := canonicalCodes (distLens.toArray.map Nat.toUInt8)
  let bw := BitWriter.empty
  let bw := bw.writeBits 1 1  -- BFINAL
  let bw := bw.writeBits 2 2  -- BTYPE = 10
  let bw := writeDynamicHeader bw litLens distLens
  have hlit_size : litCodes.size ≥ 286 := by
    show (canonicalCodes (litLens.toArray.map Nat.toUInt8)).size ≥ 286
    rw [canonicalCodes_size, Array.size_map, List.size_toArray]; omega
  have hdist_size : distCodes.size ≥ 30 := by
    show (canonicalCodes (distLens.toArray.map Nat.toUInt8)).size ≥ 30
    rw [canonicalCodes_size, Array.size_map, List.size_toArray]; omega
  have h256 : 256 < litCodes.size := by
    show 256 < (canonicalCodes (litLens.toArray.map Nat.toUInt8)).size
    rw [canonicalCodes_size, Array.size_map, List.size_toArray]; omega
  if data.size == 0 then
    let (code, len) := litCodes[256]'h256
    let bw := bw.writeHuffCode code len
    bw.flush
  else
    have hlitT_size : (packCodeTab litCodes).size ≥ 286 := by
      rw [packCodeTab_size]; exact hlit_size
    have hdistT_size : (packCodeTab distCodes).size ≥ 30 := by
      rw [packCodeTab_size]; exact hdist_size
    let bw := emitTokensWithCodesTAPT bw tokens (packCodeTab litCodes) (packCodeTab distCodes)
      hlitT_size hdistT_size 0
    let (code, len) := litCodes[256]'h256
    let bw := bw.writeHuffCode code len
    bw.flush

/-- `deflateDynamicBlockCoreP` with the dynamic-tree header taken from a
    precomputed `DynHeaderPlan` (#2627): identical to `deflateDynamicBlockCoreP`
    except the header write reuses the plan instead of rebuilding the CL tree.
    The dispatch (`deflateRawBaseP`) passes the same plan it sized with, so the
    expensive `dynHeaderCodes` build runs once per block instead of twice.

    **Invariant** (as for `writeDynamicHeaderWith`): `p` must be
    `dynHeaderCodes litLens distLens`; only then is the output
    `deflateDynamicBlockCoreP data tokens litLens distLens` (proved by
    `deflateDynamicBlockCorePWith_dynHeaderCodes`). -/
def deflateDynamicBlockCorePWith (data : ByteArray) (tokens : TokenArray)
    (litLens distLens : List Nat) (p : DynHeaderPlan) (hcl : p.clCodes.size ≥ 19)
    (hlit : litLens.length = 286) (hdist : distLens.length = 30) (cap : Nat := 0) : ByteArray :=
  let litCodes := canonicalCodes (litLens.toArray.map Nat.toUInt8)
  let distCodes := canonicalCodes (distLens.toArray.map Nat.toUInt8)
  let bw := BitWriter.emptyWithCapacity cap
  let bw := bw.writeBits 1 1  -- BFINAL
  let bw := bw.writeBits 2 2  -- BTYPE = 10
  let bw := writeDynamicHeaderWith bw litLens distLens p hcl
  have hlit_size : litCodes.size ≥ 286 := by
    show (canonicalCodes (litLens.toArray.map Nat.toUInt8)).size ≥ 286
    rw [canonicalCodes_size, Array.size_map, List.size_toArray]; omega
  have hdist_size : distCodes.size ≥ 30 := by
    show (canonicalCodes (distLens.toArray.map Nat.toUInt8)).size ≥ 30
    rw [canonicalCodes_size, Array.size_map, List.size_toArray]; omega
  have h256 : 256 < litCodes.size := by
    show 256 < (canonicalCodes (litLens.toArray.map Nat.toUInt8)).size
    rw [canonicalCodes_size, Array.size_map, List.size_toArray]; omega
  if data.size == 0 then
    let (code, len) := litCodes[256]'h256
    let bw := bw.writeHuffCode code len
    bw.flush
  else
    have hlitT_size : (packCodeTab litCodes).size ≥ 286 := by
      rw [packCodeTab_size]; exact hlit_size
    have hdistT_size : (packCodeTab distCodes).size ≥ 30 := by
      rw [packCodeTab_size]; exact hdist_size
    let bw := emitTokensWithCodesTAPT bw tokens (packCodeTab litCodes) (packCodeTab distCodes)
      hlitT_size hdistT_size 0
    let (code, len) := litCodes[256]'h256
    let bw := bw.writeHuffCode code len
    bw.flush

/-- Shared source body for the two proof-gated flat single-block entry points.
    It is inlined into those block-sized wrappers, not into their much larger
    base-candidate callers, so the recursive emitter remains one native helper
    without bloating `deflateRawBaseF`. -/
@[inline] def deflateDynamicBlockCorePWithFlatBody
    (data : ByteArray) (tokens : TokenArray)
    (litLens distLens : List Nat) (p : DynHeaderPlan) (hcl : p.clCodes.size ≥ 19)
    (hlit : litLens.length = 286) (hdist : distLens.length = 30)
    (_hlit_bound : ∀ x ∈ litLens, x ≤ 15) (_hdist_bound : ∀ x ∈ distLens, x ≤ 15)
    (cap : Nat := 0) : ByteArray :=
  let litCodes := canonicalCodes (litLens.toArray.map Nat.toUInt8)
  let distCodes := canonicalCodes (distLens.toArray.map Nat.toUInt8)
  let bw := BitWriter.emptyWithCapacity cap
  let bw := bw.writeBits 1 1  -- BFINAL
  let bw := bw.writeBits 2 2  -- BTYPE = 10
  let bw := writeDynamicHeaderWith bw litLens distLens p hcl
  have hlit_size : litCodes.size ≥ 286 := by
    show (canonicalCodes (litLens.toArray.map Nat.toUInt8)).size ≥ 286
    rw [canonicalCodes_size, Array.size_map, List.size_toArray]; omega
  have hdist_size : distCodes.size ≥ 30 := by
    show (canonicalCodes (distLens.toArray.map Nat.toUInt8)).size ≥ 30
    rw [canonicalCodes_size, Array.size_map, List.size_toArray]; omega
  have h256 : 256 < litCodes.size := by
    show 256 < (canonicalCodes (litLens.toArray.map Nat.toUInt8)).size
    rw [canonicalCodes_size, Array.size_map, List.size_toArray]; omega
  if data.size == 0 then
    let (code, len) := litCodes[256]'h256
    let bw := bw.writeHuffCode code len
    bw.flush

  else
    have hlitT_size : (packCodeTab litCodes).size ≥ 286 := by
      rw [packCodeTab_size]; exact hlit_size
    have hdistT_size : (packCodeTab distCodes).size ≥ 30 := by
      rw [packCodeTab_size]; exact hdist_size
    let bw := emitTokensWithCodesTAPTFlatZero bw tokens
      (packCodeTab litCodes) (packCodeTab distCodes) hlitT_size hdistT_size
    let (code, len) := litCodes[256]'h256
    let bw := bw.writeHuffCode code len
    bw.flush

/-- Flat-state single-block twin of `deflateDynamicBlockCorePWith`.  This is
    deliberately a separate production entry point rather than an
    `implemented_by` replacement for the general token emitter: only callers
    whose dynamic-tree lengths are known to be at most 15 may select it.  The
    proof arguments are erased; operationally the sole change is the narrowly
    routed flat token loop in the nonempty dynamic-block arm. -/
def deflateDynamicBlockCorePWithFlat (data : ByteArray) (tokens : TokenArray)
    (litLens distLens : List Nat) (p : DynHeaderPlan) (hcl : p.clCodes.size ≥ 19)
    (hlit : litLens.length = 286) (hdist : distLens.length = 30)
    (hlit_bound : ∀ x ∈ litLens, x ≤ 15) (hdist_bound : ∀ x ∈ distLens, x ≤ 15)
    (cap : Nat := 0) : ByteArray :=
  deflateDynamicBlockCorePWithFlatBody data tokens litLens distLens p hcl hlit hdist
    hlit_bound hdist_bound cap

/-- Frequency-taking twin kept as a second compact native caller of the shared
    flat emitter; this prevents LTO from cloning the large recursive loop into
    either block shell. -/
private def deflateDynamicBlockCorePWithFlatF (data : ByteArray) (tokens : TokenArray)
    (litLens distLens : List Nat) (p : DynHeaderPlan) (hcl : p.clCodes.size ≥ 19)
    (hlit : litLens.length = 286) (hdist : distLens.length = 30)
    (hlit_bound : ∀ x ∈ litLens, x ≤ 15) (hdist_bound : ∀ x ∈ distLens, x ≤ 15)
    (cap : Nat := 0) : ByteArray :=
  deflateDynamicBlockCorePWithFlatBody data tokens litLens distLens p hcl hlit hdist
    hlit_bound hdist_bound cap

/-- The plan-taking emitter with the canonical plan equals the original packed
    emitter: the only difference is the header write, bridged by
    `writeDynamicHeaderWith_dynHeaderCodes`. -/
theorem deflateDynamicBlockCorePWith_dynHeaderCodes (data : ByteArray) (tokens : TokenArray)
    (litLens distLens : List Nat) (hcl : (dynHeaderCodes litLens distLens).clCodes.size ≥ 19)
    (hlit : litLens.length = 286) (hdist : distLens.length = 30) (cap : Nat) :
    deflateDynamicBlockCorePWith data tokens litLens distLens (dynHeaderCodes litLens distLens)
        hcl hlit hdist cap =
      deflateDynamicBlockCoreP data tokens litLens distLens hlit hdist := by
  unfold deflateDynamicBlockCorePWith deflateDynamicBlockCoreP
  simp only [BitWriter.emptyWithCapacity_eq, writeDynamicHeaderWith_dynHeaderCodes]


/-- Write a dynamic Huffman DEFLATE block from precomputed LZ77 tokens.
    Produces a single DEFLATE block with BFINAL=1, BTYPE=10. Factored out of
    `deflateDynamic` so a caller that already has the token stream (e.g. the
    `deflateCompressed` fixed/dynamic comparison) can avoid re-running the
    matcher. Computes the code lengths (`dynamicCodeLengths`) then delegates to
    `deflateDynamicBlockCore`. -/
def deflateDynamicBlock (data : ByteArray) (tokens : Array LZ77Token) : ByteArray :=
  let (litFreqs, distFreqs) := tokenFreqs tokens
  let lens := dynamicCodeLengths litFreqs distFreqs
  deflateDynamicBlockCore data tokens lens.1 lens.2
    (dynamicCodeLengths_length litFreqs distFreqs).1
    (dynamicCodeLengths_length litFreqs distFreqs).2

/-- Emit one dynamic Huffman block into an existing `BitWriter` (no flush), with
    `BFINAL = isFinal`. Same body as `deflateDynamicBlockCore` but bit-packed onto
    a running writer so a sequence of blocks shares the bitstream. -/
def emitDynBlock (bw : BitWriter) (data : ByteArray) (tokens : Array LZ77Token)
    (litLens distLens : List Nat)
    (hlit : litLens.length = 286) (hdist : distLens.length = 30)
    (isFinal : Bool) : BitWriter :=
  let litCodes := canonicalCodes (litLens.toArray.map Nat.toUInt8)
  let distCodes := canonicalCodes (distLens.toArray.map Nat.toUInt8)
  let bw := bw.writeBits 1 (if isFinal then 1 else 0)  -- BFINAL (1 bit)
  let bw := bw.writeBits 2 2                            -- BTYPE = 10 (dynamic)
  let bw := writeDynamicHeader bw litLens distLens
  have hlit_size : litCodes.size ≥ 286 := by
    show (canonicalCodes (litLens.toArray.map Nat.toUInt8)).size ≥ 286
    rw [canonicalCodes_size, Array.size_map, List.size_toArray]; omega
  have hdist_size : distCodes.size ≥ 30 := by
    show (canonicalCodes (distLens.toArray.map Nat.toUInt8)).size ≥ 30
    rw [canonicalCodes_size, Array.size_map, List.size_toArray]; omega
  have h256 : 256 < litCodes.size := by
    show 256 < (canonicalCodes (litLens.toArray.map Nat.toUInt8)).size
    rw [canonicalCodes_size, Array.size_map, List.size_toArray]; omega
  let bw := if data.size == 0 then bw
            else emitTokensWithCodes bw tokens litCodes distCodes hlit_size hdist_size 0
  let (code, len) := litCodes[256]'h256
  bw.writeHuffCode code len

/-- Compress data using dynamic Huffman codes and greedy LZ77 (Level 5).
    Produces a single DEFLATE block with BFINAL=1, BTYPE=10. Thin wrapper over
    `deflateDynamicBlock` that runs the greedy matcher first. -/
def deflateDynamic (data : ByteArray) (windowSize : Nat := 32768) : ByteArray :=
  deflateDynamicBlock data (lz77GreedyIter data windowSize)

open Zip.Spec.DeflateStoredCorrect (deflateStoredPure storedBlockBytes storedBlockBytes_eq)

/-- Pick the smaller of two encodings by byte length (ties keep `b`). -/
def pickSmaller (a b : ByteArray) : ByteArray :=
  if a.size < b.size then a else b

/-- Lazy `pickSmaller` keyed on precomputed byte sizes: forces (emits) only the
    winning candidate. When `sa = (a ()).size` and `sb = (b ()).size` this equals
    `pickSmaller (a ()) (b ())` byte-for-byte (`a` wins iff strictly smaller, ties
    keep `b`), but the losing candidate is never emitted — the whole point of
    sizing every candidate before emitting any. Correctness of the byte-identity
    (that `sa`/`sb` are the true emitted sizes) is pinned by the `SizeHelpers`
    conformance tests, exactly as the single-block `fixedBlockBytes`/`dynBlockBytes`
    dispatch is; the roundtrip theorems only need each candidate to decode. -/
@[inline] def emitSmallerBy (sa : Nat) (a : Unit → ByteArray)
    (sb : Nat) (b : Unit → ByteArray) : ByteArray :=
  if sa < sb then a () else b ()

/-! ## Sizing a block without emitting it

A DEFLATE block's body is a *dot product* of symbol frequencies and code
lengths — `Σ_sym freq[sym]·(codeLen[sym] + extraBits[sym])` — so its exact
byte size is computable in O(#symbols) from the already-computed `tokenFreqs`,
with no bit-banging and independent of #tokens. The dispatch below sizes every
candidate this way and emits *only* the winner, instead of emitting all three
blocks and keeping the smallest. The freq·codeLen identity is not proved here:
the roundtrip theorems hold for whichever block is chosen, and `SizeHelpers`
tests pin the helpers to the emitted `.size` so the choice stays byte-identical
to the old `pickSmaller`-of-emitted-blocks behaviour. -/

/-- Extra bits carried by lit/len symbol `s`: zero for literals and the
    end-of-block symbol (0–256), the RFC 1951 §3.2.5 table for length symbols
    257–285. Reads the same `Inflate.lengthExtra` table the emitter writes. -/
@[inline] def lenExtraBits (s : Nat) : Nat :=
  if 257 ≤ s then (Inflate.lengthExtra.getD (s - 257) 0).toNat else 0

/-- Fixed-Huffman lit/len code lengths as a `Nat` array (RFC 1951 §3.2.6),
    derived from the same table `fixedLitCodes` is built from. -/
def fixedLitLenNat : Array Nat := Inflate.fixedLitLengths.map (·.toNat)

/-- Fixed-Huffman distance code lengths as a `Nat` array (all 5). -/
def fixedDistLenNat : Array Nat := Inflate.fixedDistLengths.map (·.toNat)

/-- Total body-bit count of a block over the tokens summarised by
    `(litFreqs, distFreqs)`, for the given lit/len and distance code-length
    tables: `Σ_sym freq·(codeLen + extraBits)` over the 286 lit/len and 30
    distance symbols. The end-of-block symbol (256, frequency 1) is included via
    `litFreqs`; unused symbols have frequency 0 and contribute nothing. -/
def symbolBitCount (litFreqs distFreqs litLens distLens : Array Nat) : Nat :=
  ((List.range 286).foldl (fun acc s =>
      acc + litFreqs.getD s 0 * (litLens.getD s 0 + lenExtraBits s)) 0)
  + ((List.range 30).foldl (fun acc d =>
      acc + distFreqs.getD d 0 * (distLens.getD d 0 + (Inflate.distExtra.getD d 0).toNat)) 0)

/-- Byte size of `deflateFixedBlock data tokens`, computed from frequencies
    without emitting: `⌈(3 header bits + body bits)/8⌉`. `litFreqs`/`distFreqs`
    are `tokenFreqs tokens`. -/
def fixedBlockBytes (litFreqs distFreqs : Array Nat) : Nat :=
  (3 + symbolBitCount litFreqs distFreqs fixedLitLenNat fixedDistLenNat + 7) / 8

/-- Byte size of `deflateDynamicBlock data tokens`. The tree-header bit count is
    obtained by running `writeDynamicHeader` into an empty writer (cheap — RLE
    over ~316 code lengths) and reading its `bitLength`; the symbol body is the
    freq·codeLen dot product. `litLens`/`distLens` come from
    `dynamicCodeLengths`. -/
def dynBlockBytes (litFreqs distFreqs : Array Nat) (litLens distLens : List Nat) : Nat :=
  let headerBits := (writeDynamicHeader BitWriter.empty litLens distLens).bitLength
  (3 + headerBits + symbolBitCount litFreqs distFreqs litLens.toArray distLens.toArray + 7) / 8

/-- `dynBlockBytes` with the tree-header bits taken from a precomputed
    `DynHeaderPlan` (#2627): the header bit count comes from writing the plan into
    an empty writer rather than rebuilding the CL tree. The dispatch sizes and
    emits the dynamic candidate from one shared plan.

    **Invariant** (as for `writeDynamicHeaderWith`): `p` must be
    `dynHeaderCodes litLens distLens`; only then does this equal
    `dynBlockBytes litFreqs distFreqs litLens distLens`
    (proved by `dynBlockBytesWith_dynHeaderCodes`). -/
def dynBlockBytesWith (litFreqs distFreqs : Array Nat) (litLens distLens : List Nat)
    (p : DynHeaderPlan) (hcl : p.clCodes.size ≥ 19) : Nat :=
  let headerBits := (writeDynamicHeaderWith BitWriter.empty litLens distLens p hcl).bitLength
  (3 + headerBits + symbolBitCount litFreqs distFreqs litLens.toArray distLens.toArray + 7) / 8

/-- The plan-taking sizer with the canonical plan equals `dynBlockBytes`. Proved
    before the `irreducible` attribute so both unfold; bridged by
    `writeDynamicHeaderWith_dynHeaderCodes`. -/
theorem dynBlockBytesWith_dynHeaderCodes (litFreqs distFreqs : Array Nat) (litLens distLens : List Nat)
    (hcl : (dynHeaderCodes litLens distLens).clCodes.size ≥ 19) :
    dynBlockBytesWith litFreqs distFreqs litLens distLens (dynHeaderCodes litLens distLens) hcl =
      dynBlockBytes litFreqs distFreqs litLens distLens := by
  unfold dynBlockBytesWith dynBlockBytes
  rw [writeDynamicHeaderWith_dynHeaderCodes]

-- The size helpers are opaque cost models: the dispatch only ever compares them.
-- Marking them irreducible keeps the elaborator from unfolding the 286-element
-- `symbolBitCount` fold while `split`ting the selection `if` (which would exceed
-- `maxRecDepth`); the kernel and compiled code still evaluate them, so `decide`
-- and the `SizeHelpers` conformance tests are unaffected.
attribute [irreducible] symbolBitCount fixedBlockBytes dynBlockBytes dynBlockBytesWith

/-- Hash-chain search depth per compression level. Higher levels generally
    search deeper for longer matches (better ratio on diverse input) at higher
    cost; the `chainWalk` early-stop keeps repetitive input fast at any depth.
    The ratio gain saturates around 256–512 (measured), so level 9 caps there.

    **L4 is chain 16 in the greedy tier**, paired with `insertCap = 128`.
    Pinned production median-of-5 measurements place its 0.340536 geometric-
    mean Silesia ratio above the proper L3↔L5 time-per-byte interpolation.
    The former lazy chain-64 L4 measured about 57.4 MB/s at 0.331300 and was
    strictly dominated by L5 (about 59.0 MB/s at 0.327256) in the committed
    baseline.

    **L5 = 24 since the L5 re-grid** (`gate-sweep`, run after the hash3 singleton #2824, gm/ld
    re-grid #2825, and greedy re-grid #2830 landings): the old L5 = (128,
    single-block, gate off) had fallen ~14% inside the L4↔L6 mixing line — the
    recent landings made the split tier so much cheaper that a shallow-chain
    *split* point (initially chain 24, gate 64, probe /4, no singleton) matches the old
    L5's speed while banking −0.53pp weighted-Silesia ratio (0.3302 → 0.3249),
    +4% above the blend; every deeper single-block point stayed inside it. The
    later `l5-cadence-finalists` sweep found a faster large-stream point at
    chain 22 with a 2016-token observation window. `lazyChainDepthFor` selects
    it only on large inputs; smaller streams retain this chain-24 point so the
    established small-input frontier remains available.
    **L6's depth drops back to 64 on purpose** (the split tier historically
    started there): at equal
    cycles the observation-divergence split + a shallow chain beats a deep
    chain without the split — the block-split, not the chain, is L6's budget.
    **L7 also sits at 64 since the post-singleton re-grid** (the hash3
    singleton, gate-sweep over chain × gate × probe depth): with length-3
    coverage paying the ratio bill, (chain 64, gate off, probe /2) lands at
    0.3196 weighted-Silesia ratio — beyond what the old chain-256 L7 reached —
    so the deep-chain point fell inside the new frontier and L7 adopts the old
    L6 config wholesale. L8 keeps 512; past that the chain saturates.

    **L2/L3 dropped to 8/16 in the greedy re-grid** (`l1-sweep2`, run after the
    merged-greedy-loop and packed-emit landings shifted the tier's cost
    balance): with the `niceLen` cutoff disabled (see there), (chain 8, cap 8)
    matches the old L2's weighted-Silesia ratio exactly at +12% speed, and
    (chain 16, cap 32) beats the old L3 on both axes — the old rows sat ~10%
    below the greedy-band mixing frontier. After the L4 retune, the complete
    median-of-5 refresh places L3 about 0.5% inside the direct L2↔L4 mixing
    curve on both headline corpora; other matched runs straddled zero, so L3 is
    a marginal point and the next natural ladder re-grid target.

    Level 1 is the `deflate_fast` corner (#2726): depth `4` is exactly zlib
    `-1`'s `max_chain`. A tokens-held-constant attribution on Silesia (see
    `ZipL1Attrib`/`ZipL1Sweep`) showed L1 is emit-bound — the token walk +
    `BitWriter` dominate, and fixed-only emission is *not* materially faster than
    the dynamic-arbitrated base while giving up 6.5–25% ratio, so fixed-only was
    rejected. Shallowing the chain (8→4) alongside an aggressive insert cap
    (`insertCap`, 16→2) is the precedented fast policy that keeps the normal
    stored/static/dynamic arbitration: +19% end-to-end MB/s on Silesia (56.0→66.4,
    in-binary A/B on a quiet pinned core) at a +4.2% geomean-ratio cost
    (0.347→0.361 — still *below* the 0.38–0.40 fast-band ceiling the issue targets,
    so ratio headroom remains), every file same-or-faster, worst single-file ratio
    regression +8.6% (reymont). The intermediate `insertCap = 4` is a more
    conservative point (+15% e2e at ratio 0.356, worst file +6.3%). -/
def chainDepth (level : UInt8) : Nat :=
  if level ≤ 1 then 4
  else if level ≤ 2 then 8
  else if level ≤ 4 then 16
  else if level ≤ 5 then 24
  else if level ≤ 7 then 64
  else if level ≤ 8 then 512
  else 1024

/-- Per-level interior-insertion cap (zlib's `deflate_fast`/`deflate_slow` split):
    greedy levels (1–4) defer interior `updateHashes` insertions for speed at a
    ratio cost; lazy levels ≥ 5 insert every position. Level 4 uses cap 128, the
    measured knee that places it above the L3↔L5 frontier. Level 1 uses the
    aggressive `deflate_fast` cap of `2` (#2726): a re-measured Silesia sweep
    (`ZipL1Sweep`) showed the older `cap = 16` claim ("below ~16 is
    counterproductive") no longer holds for the packed emit path — at chain depth
    4, `cap = 2` is +12% end-to-end vs `cap = 16` because the interior-insertion
    saving outweighs the slightly higher token count the worse ratio produces
    (the emit walk is the bound, not the cap). L2/L3 dropped to 8/32 with the
    greedy re-grid (`l1-sweep2`), paired with their new chain depths. The chain
    is a heuristic, so any cap stays correct (`lz77ChainIter_resolves` holds
    ∀ cap). -/
def insertCap (level : UInt8) : Nat :=
  if level ≤ 1 then 2
  else if level ≤ 2 then 8
  else if level ≤ 3 then 32
  else if level ≤ 4 then 128
  else 1000000000

/-- Lazy `good_match` threshold (zlib-style): the lazy matcher skips the
    one-byte-lookahead probe once the first match is at least this long, since a
    long first match is rarely improved by deferral. Lower → more gating (faster,
    slightly worse ratio). `259 > 258` disables gating.

    L4's table entry `8` is historical and no longer consulted now that L4 uses
    the greedy matcher. **L6 gates at 64 since the hash3-singleton re-grid** —
    with the singleton paying the ratio bill, (gate 64, ld/8)
    buys +8% weighted speed for +0.09pp, the point that strictly dominates
    miniz_oxide L6; L7 keeps the gate off and the old L6 ratio point.
    **L5 also gates at 64 since the L5 re-grid** (`gate-sweep`, see
    `chainDepth`): the winning shallow split point pairs the intermediate gate
    with its original chain-24 walk — at that depth the gate's skipped lookahead
    probes are most of the lazy tier's marginal cost. The later chain-22 cadence
    retune retains that gate. -/
def goodMatch (level : UInt8) : Nat :=
  if level ≤ 4 then 8
  else if level ≤ 6 then 64
  else 259

/-- Per-level `niceLen` cutoff (libdeflate `nice_match_length`, `deflate_compress.c`):
    the chain walk stops as soon as the best match reaches this length, since a
    match this long is already good enough — burning the rest of the depth budget
    to lengthen it further rarely pays for itself. **L2/L3 disable the cutoff
    since the greedy re-grid** (`l1-sweep2`, post merged-greedy-loop +
    packed-emit landings): the libdeflate values (10/14, #2744) were costing
    ~0.5pp weighted-Silesia ratio for speed better bought by shallowing the
    chain instead — both old mid rows sat ~10% below the greedy-band mixing
    frontier. Level 1 keeps `258` (no early-out) as before — at chain depth 4
    the walk is already short, so a cutoff buys little there.

    L4 also disables the cutoff at its greedy chain-16 point; lower cutoffs
    spend ratio that is better bought with the insertion cap. The earlier
    lazy-L4 `mid-sweep --time` reached the same conclusion: lower cutoffs only
    cost ratio. L5–L7 sit at the measured knee `65` (nl30
    gains ~3% speed for +10bp — a poor trade; nl130/258 return ≤1bp for the
    speed given up; since the post-singleton re-grid L7 runs the old L6
    config, chain 64, so the old chain-256 `130` knee no longer applies);
    L8 (the max split tier)
    disables the cutoff — nl130 times within 1% but emits more bytes, and L8's
    cadence guard promises old-L8 ratio parity. `258` (the max match length,
    ≥ every `maxLen`) disables the cutoff: the walk then stops only on the
    full-match / fuel condition, exactly as before this knob existed. The
    cutoff never enters correctness — the chain is a heuristic re-verified at
    emission — so any value keeps the encoder contracts. -/
def niceLen (level : UInt8) : Nat :=
  if level ≤ 4 then 258
  else if level ≤ 7 then 65
  else 258

/-- Lazy lookahead probe depth (libdeflate `deflate_compress.c`): the second
    `chainWalk` at `pos+1` runs at *half* the `pos` walk's `chainDepth`, not full
    depth. Since the `goodMatch` gate is disabled at L7+ (`goodMatch = 259`), every
    matched position otherwise pays two full-depth chain walks; libdeflate probes
    its first lookahead at half depth (and its second at quarter) and still holds
    better ratios than us, so the deferral quality a half-depth probe gives up is
    slack. The probe still runs — it is shallower, not skipped — so the ratio cost
    stays in the noise while the second walk's cycles roughly halve.

    **L6 probes at depth 8 (`chainDepth/8`), no rolling — the whole-tar anchor
    (#2837)**: the priority for L6 is strict domination of miniz_oxide L6 on the
    single-stream `zip silesia.tar` workload (211 MB, one `deflateRaw` call), on
    *both* size and wall time. Deeper/rolling variants (ld18 from the pre-roll
    re-pair, then ld10/cap2) each bought geomean ratio margin but spent whole-tar
    wall: lean's ~0.24s system-time fault tax (the materialized 45.9M-token,
    ~367 MB array, level-independent) means added matcher compute pushes the
    single-shot wall past miniz even when steady-state per-file throughput looks
    faster. At ld8/no-roll the whole tar compresses to 67,944,422 B in ~5.72s vs
    miniz 68,112,444 B / ~5.81s — smaller AND faster, the pinned invariant. It
    still clears miniz on both *per-file* planes too (0.31969 weighted / 0.32132
    geomean vs miniz 0.32131 / 0.32164), just by a slimmer geomean margin than the
    superseded ld10/cap2 point; recovering that margin without breaking the
    whole-tar win waits on shrinking the token footprint (fault-reserve +
    unboxing). L7 keeps its own rolling (a genuine whole-tar win at that level).
    **L5 probes at `/4` since the L5 re-grid**
    (`gate-sweep`, see `chainDepth`): the original winning (chain 24, gate 64)
    split point took its probe at 6. The later chain-22 cadence retune takes it
    at 5 — deep enough to keep the deferral wins the gate lets through, roughly
    half the cost of the `/2` default.

    Only levels ≥ 5 (the lazy `deflate_slow` tier) consult this; the greedy
    matcher (1–4) has no lookahead. Depth is a pure heuristic — the chain is
    re-verified at emission (`chainWalk_spec` holds for any fuel) — so any value
    keeps the encoder contracts. -/
def lazyDepth (level : UInt8) : Nat :=
  if level == 5 then chainDepth level / 4
  else if level == 6 then 8
  else chainDepth level / 2

/-- Whether this call uses L5's large-stream matcher/split retune. -/
def useL5LargeInputPolicy (data : ByteArray) (level : UInt8) : Bool :=
  level == 5 && l5LargeInputMinSize ≤ data.size

/-- Lazy-tier chain depth after the size-aware L5 retune. -/
def lazyChainDepthFor (data : ByteArray) (level : UInt8) : Nat :=
  if useL5LargeInputPolicy data level then 22 else chainDepth level

/-- Lazy lookahead depth paired with `lazyChainDepthFor`. -/
def lazyDepthFor (data : ByteArray) (level : UInt8) : Nat :=
  if useL5LargeInputPolicy data level then 22 / 4 else lazyDepth level

/-- Number of contiguous sample regions the pre-scan reads, spread end to end
    across the input (first at offset 0, last ending at `n`). A region that looks
    even slightly compressible short-circuits the whole scan, so a normal
    compressible file pays for at most the first region. Shared with the h3
    content gate (`h3IncompressibleScan`). -/
def prescanRegions : Nat := 4

/-- Bytes per sample region. Each region is scanned *contiguously* and every
    consecutive 4-gram is inserted, so repetition is detected densely the way the
    matcher itself finds matches. At 32 KiB a region spans two of the common
    page/block sizes (4/8/16 KiB), so a repeated block surfaces as a wall of
    4-gram collisions. ≤`prescanRegions · prescanRegionBytes` (128 KiB) bytes are
    scanned, independent of input size. -/
def prescanRegionBytes : Nat := 32768

/-- log2 of the per-region 4-gram presence-table size (2^20 slots). Sized so that,
    over the ≈32 K 4-grams of one region, the false-collision rate of genuinely
    random input is ≈1.6% (`S²/2·tableSize`) — half the repeat gate, so random data
    reads as "no repeats" with a comfortable margin while keeping the per-region
    allocation small. -/
def prescanTableBits : Nat := 20

/-- Per-region 4-gram collision-fraction cutoff (percent) below which a region is
    judged sparse in recurring 4-grams, i.e. low-compressibility. Tuned on Silesia:
    the least-compressible region of each ratio-winning binary sits below 61%
    (x-ray 9%, sao 20%, ooffice 46%, mozilla 58%) while every file where the probe
    costs ratio has all regions at ≥64% (webster 64%, dickens 68%, mr 67%, samba
    71%, xml 81%, reymont 82%, nci 94%). 61% centres that gap. -/
def h3ProbeCollThresholdPercent : Nat := 61

/-- Content-adaptive gate for the hash3 length-3 singleton probe (`useH3For`).
    Returns `true` when the input looks *low-compressibility*: at least one sampled
    region is sparse in recurring 4-grams (collision fraction below
    `h3ProbeCollThresholdPercent`%), the signal that the lazy matcher will find few
    length-≥4 matches so the length-3 singleton probe earns its cost. Shares the
    incompressible pre-scan's region layout (`prescanRegions` contiguous
    `prescanRegionBytes` windows spread end to end) and single-hash 4-gram presence
    filter, but uses only the collision signal and fires on the *least*-compressible
    region rather than requiring *every* region to be incompressible: the probe is
    an incremental parse tweak, so biasing toward "on" whenever any region is hard
    keeps the ratio-winning binaries covered. Tuned on Silesia it fires on
    x-ray/sao/ooffice/mozilla (h3 wins ratio there) and on osdb (unavoidable — its
    per-region signature dominates mozilla's on both entropy and collision, so no
    monotone cut separates them; leaving it on merely reproduces the static knob,
    which is `≤` master), and stays off for nci/webster/dickens/mr/reymont/samba/xml
    where the probe costs both ratio and matcher speed. Opaque to correctness: the
    result only selects between two encoder configs proven equivalent at the
    contract level (`lz77ChainLazyIter_*` are `∀ useH3`). -/
def h3IncompressibleScan (data : ByteArray) : Bool := Id.run do
  let n := data.size
  let tableSize := 1 <<< prescanTableBits
  let shift : UInt32 := (32 - prescanTableBits).toUInt32
  let regBytes := min prescanRegionBytes n
  let span := n - regBytes
  for r in [0:prescanRegions] do
    let start := if prescanRegions ≤ 1 then 0 else min ((r * span) / (prescanRegions - 1)) span
    let stop := min (start + regBytes) n
    let mut table : Array UInt8 := Array.replicate tableSize 0
    let mut sampled : Nat := 0       -- 4-grams hashed in this region
    let mut collisions : Nat := 0    -- 4-grams hitting an already-seen slot
    let mut p := start
    while p + 3 < stop do
      let a := data[p]!.toUInt32
      let b := data[p+1]!.toUInt32
      let c := data[p+2]!.toUInt32
      let d := data[p+3]!.toUInt32
      let word := a ||| (b <<< 8) ||| (c <<< 16) ||| (d <<< 24)
      let idx := ((word * 2654435761) >>> shift).toNat
      if table[idx]! != 0 then
        collisions := collisions + 1
      else
        table := table.set! idx 1
      sampled := sampled + 1
      p := p + 1
    -- A region sparse in recurring 4-grams: the matcher would find few usable
    -- matches here, so the length-3 singleton is worth probing. Any such region
    -- enables the gate (bias toward keeping the ratio wins).
    if sampled > 0 && collisions * 100 < sampled * h3ProbeCollThresholdPercent then
      return true
  return false

/-- Enable the hash3 length-3 singleton at the split tier (levels 6–8). Our
    lazy matcher walks hash4-keyed chains only, so length-3 matches are invisible
    below L9; on the barely-compressible Silesia binaries (x-ray/sao/ooffice)
    this is our whole weighted-ratio deficit to miniz_oxide L6. The singleton
    probe (`h3Seed`, TOO_FAR-capped) restores them at −0.28pp corpus-weighted
    Silesia ratio for ≤~5% matcher speed. L1–L5 keep the probe-free loops (the
    #2742 verdict against probing the fast band stands, and the L5 re-grid
    retested the singleton at L5's shallow split points — every h3 row fell
    below the no-h3 frontier there); L9/L10 already carry their own singleton
    in the cache build. -/
def useH3Level (level : UInt8) : Bool := decide (6 ≤ level ∧ level ≤ 8)

/-- Data-adaptive replacement for the static `useH3Level` at the L6–8 dispatch:
    enable the hash3 length-3 singleton only when the level selects it (6–8) AND
    the input is classified low-compressibility by `h3IncompressibleScan`. On the
    barely-compressible Silesia binaries (x-ray/sao/ooffice/mozilla) the probe
    restores the whole weighted-ratio deficit to miniz_oxide L6; on structured or
    text inputs (nci/webster/dickens/…) it costs both ratio (−0.3…−1.1%) and
    12–21% matcher speed, so the gate drops it there — a win on both axes. Inputs
    below `h3ProbeMinSize` keep the static decision (cheap matcher, scan not worth
    it; also leaves existing small-input output byte-identical). Pure parse
    heuristic: the matcher contracts hold for whichever Bool this returns (they are
    `∀ useH3`), so the roundtrip proof does not depend on the classification. -/
def useH3For (data : ByteArray) (level : UInt8) : Bool :=
  useH3Level level && (data.size < h3ProbeMinSize || h3IncompressibleScan data)

/-- The content-selected matcher profiles available to level 7.

    The names describe mechanisms rather than corpus members.  Keeping this
    finite selector separate from `l7MatchConfig` lets timing sweeps retune the
    matcher knobs without changing the content classifier. -/
inductive L7Profile where
  /-- The shallow, gated level-5 matcher. -/
  | shallow
  /-- The fast hash3 profile (the level-6 matcher). -/
  | h3Fast
  /-- The ratio-oriented hash3 profile (the level-7 matcher). -/
  | h3Balanced
  /-- Chain 64 with one depth-8 lazy probe. -/
  | chain64Probe8
  /-- Chain 64 with two depth-16 lazy probes. -/
  | chain64Probe16
  /-- Chain 96 with two depth-16 lazy probes. -/
  | chain96Probe16
  /-- Chain 128 with two depth-16 lazy probes. -/
  | chain128Probe16
  /-- Chain 128 with four depth-32 lazy probes. -/
  | chain128Probe32
  /-- Chain 128/depth 32 without the nice-length cutoff. -/
  | chain128LongProbe32
  /-- The deep level-8 matcher. -/
  | deep
  deriving BEq, ReflBEq, LawfulBEq, Repr

/-- Output-preparation policy for a retained level-7 content profile.

    `arbitrate` is the conservative path: size both the whole-stream base and
    observation-split candidates, then emit the smaller one.  The other two
    constructors select a candidate whose winner was stable in the large-input
    profile calibration, allowing production to skip preparation of the known
    loser. -/
inductive L7OutputRoute where
  | arbitrate
  | base
  | split
  deriving BEq, ReflBEq, LawfulBEq, Repr

/-- Upper bound for the two size-sensitive small-input profiles whose split
    winner was stable in both the calibration corpus and a held-out source-file
    audit.  At and above this boundary they retain exact size arbitration. -/
def l7SmallDirectSplitMaxSize : Nat := 160 * 1024

/-- Select level 7's output-preparation route from input size and the already
    retained content profile.

    Most inputs below the large-profile threshold keep exact size arbitration:
    that region uses a deliberately coarse adjacent-run classifier, and some
    profiles change winner between samples (notably `chain128Probe16`).  Three
    conservative exceptions were byte-identical to the arbitrated winner across
    Canterbury and 123 held-out source files: `h3Fast`, plus `chain64Probe8` and
    `shallow` below 160 KiB.  On large inputs, shallow and chain-128/depth-32
    consistently selected the whole-stream base during calibration; the
    remaining profiles selected the observation split. -/
def l7OutputRouteFor (size : Nat) (profile : L7Profile) : L7OutputRoute :=
  if size < h3ProbeMinSize then
    match profile with
    | .h3Fast => .split
    | .chain64Probe8 | .shallow =>
      if size < l7SmallDirectSplitMaxSize then .split else .arbitrate
    | _ => .arbitrate
  else
    match profile with
    | .shallow | .chain128Probe32 => .base
    | _ => .split

/-- Concrete lazy-matcher knobs selected by an `L7Profile`. -/
structure L7MatchConfig where
  chainDepth : Nat
  goodMatch : Nat
  niceLen : Nat
  lazyDepth : Nat
  useH3 : Bool
  lazy2Steps : Nat

/-- Matcher knobs for each level-7 content profile.  The shallow profile keeps
    level 5's size-aware chain-22 retune on inputs of at least 4 MiB.  Split
    cadence is intentionally separate (`l7SplitCheckTokensFor`), with its own
    measured profile-and-size policy. -/
def l7MatchConfig (data : ByteArray) : L7Profile → L7MatchConfig
  | .shallow =>
      let chain := if l5LargeInputMinSize ≤ data.size then 22 else 24
      ⟨chain, 64, 65, chain / 4, false, 1⟩
  | .h3Fast => ⟨64, 64, 65, 8, true, 1⟩
  | .h3Balanced => ⟨64, 259, 65, 32, true, 4⟩
  | .chain64Probe8 => ⟨64, 259, 65, 8, false, 1⟩
  | .chain64Probe16 => ⟨64, 259, 65, 16, false, 2⟩
  | .chain96Probe16 => ⟨96, 259, 65, 16, false, 2⟩
  | .chain128Probe16 => ⟨128, 259, 65, 16, false, 2⟩
  | .chain128Probe32 => ⟨128, 259, 65, 32, false, 4⟩
  | .chain128LongProbe32 => ⟨128, 259, 258, 32, false, 4⟩
  | .deep => ⟨512, 259, 258, 256, false, 1⟩

/-- Whether the selected profile is the large-input shallow specialization. -/
def l7UseLargeShallow (data : ByteArray) (profile : L7Profile) : Bool :=
  profile == .shallow && l5LargeInputMinSize ≤ data.size

/-- Count sampled adjacent equal bytes in the first 4 KiB.  At most 63 byte
    pairs are read (offsets 64, 128, ...), so this small-input signal costs
    about one microsecond and allocates no table. -/
def l7AdjacentRunSamples (data : ByteArray) : Nat := Id.run do
  let stop := min data.size 4096
  let mut same := 0
  let mut p := 64
  while p < stop do
    if data[p]! == data[p - 1]! then
      same := same + 1
    p := p + 64
  return same

/-- The small-input half of the level-7 classifier.  Thresholds are deliberately
    stated over the cheap signal, separately from extraction, so golden tests
    can pin the policy without running the compressor.

    This policy was fitted to Canterbury: very sparse adjacent runs and very
    easy run-heavy inputs do not repay a mid-depth chain, while the middle band
    does.  It is a measured heuristic, not a general dominance theorem. -/
def l7ClassifySmall (size adjacentRuns : Nat) : L7Profile :=
  if size < 65536 then
    if 8 ≤ adjacentRuns then .h3Fast else .chain64Probe16
  else if 56 ≤ adjacentRuns then .chain128Probe16
  else if adjacentRuns ≤ 2 || 10 ≤ adjacentRuns then .shallow
  else .chain64Probe8

/-- Mix a four-byte word before feeding it to the tiny cardinality sketch.
    The avalanche is important: the low six bits choose a register, so the
    multiplicative hash used by the match table alone would leave byte-layout
    correlations between the register index and rank bits. -/
@[inline] def l7Mix4 (x : UInt32) : UInt32 :=
  let x := x ^^^ (x >>> 16)
  let x := x * 0x7FEB352D
  let x := x ^^^ (x >>> 15)
  let x := x * 0x846CA68B
  x ^^^ (x >>> 16)

/-- Raise one packed four-bit cardinality-sketch register. -/
@[inline] def l7RaiseRegister (word : UInt64) (slot rank : Nat) : UInt64 :=
  let shift := (slot * 4).toUInt64
  let old := ((word >>> shift) &&& 0xF).toNat
  if old < rank then
    (word &&& ~~~((0xF : UInt64) <<< shift)) ||| (rank.toUInt64 <<< shift)
  else
    word

/-- Harmonic score for sixteen packed four-bit cardinality registers. -/
def l7RegisterScore (word : UInt64) : Nat := Id.run do
  let mut score := 0
  for slot in [0:16] do
    let rank := ((word >>> (slot * 4).toUInt64) &&& 0xF).toNat
    score := score + (1 <<< (15 - rank))
  return score

/-- Approximate distinct-four-gram fraction (per mille) for one 32 KiB region.

    This is a 64-register HyperLogLog-style sketch held in four `UInt64`s, not
    a heap table.  Four-grams are sampled every four bytes.  `11616000 / score`
    is the fixed-point form of the 64-register raw estimator divided by 8192
    samples; the result is only a stable classifier signal, not a public
    cardinality estimate. -/
def l7RegionUniquePermille (data : ByteArray) (start stop : Nat) : Nat := Id.run do
  let mut r0 : UInt64 := 0
  let mut r1 : UInt64 := 0
  let mut r2 : UInt64 := 0
  let mut r3 : UInt64 := 0
  let mut p := start
  while p + 3 < stop do
    let a := data[p]!.toUInt32
    let b := data[p + 1]!.toUInt32
    let c := data[p + 2]!.toUInt32
    let d := data[p + 3]!.toUInt32
    let h := l7Mix4 (a ||| (b <<< 8) ||| (c <<< 16) ||| (d <<< 24))
    let bucket := (h &&& 63).toNat
    let rank := min ((UInt64.ctz (h >>> 6).toUInt64).toNat + 1) 15
    if bucket < 16 then
      r0 := l7RaiseRegister r0 bucket rank
    else if bucket < 32 then
      r1 := l7RaiseRegister r1 (bucket - 16) rank
    else if bucket < 48 then
      r2 := l7RaiseRegister r2 (bucket - 32) rank
    else
      r3 := l7RaiseRegister r3 (bucket - 48) rank
    p := p + 4
  let score :=
    l7RegisterScore r0 + l7RegisterScore r1 +
      l7RegisterScore r2 + l7RegisterScore r3
  return min 1000 (11616000 / max score 1)

/-- The large-input half of the level-7 classifier, over the minimum, mean and
    maximum per-region approximate unique-four-gram fractions (per mille).

    These bands were fitted to the twelve Silesia files.  They express matcher
    mechanisms—hash3 on sparse-match regions, deeper chains on dense or
    heterogeneous regions—but the thresholds are corpus-trained and are not
    claimed to generalize as a dominance guarantee. -/
def l7ClassifyLarge (minUnique meanUnique maxUnique : Nat) : L7Profile :=
  if 700 ≤ maxUnique || (380 ≤ minUnique && maxUnique < 450) then
    if 950 ≤ maxUnique then .h3Fast else .h3Balanced
  else if minUnique < 480 && 600 ≤ maxUnique && 500 ≤ meanUnique then .shallow
  else if maxUnique ≤ 140 then .chain128LongProbe32
  else if meanUnique ≤ 220 then .deep
  else if 130 ≤ minUnique && meanUnique ≤ 300 then .chain128Probe16
  else if minUnique < 80 then
    if 315 ≤ meanUnique then .chain64Probe16 else .chain64Probe8
  else if meanUnique < 545 then .chain128Probe32
  else .chain96Probe16

/-- Content-selected matcher profile for level 7.

    Inputs below 1 MiB use the 63-probe adjacent-run signal.  Larger inputs use
    four spread 32 KiB regions and the allocation-free four-word cardinality
    sketch.  Only level 7 consults this selector; every other level retains its
    existing matcher and output policy. -/
def l7ProfileFor (data : ByteArray) : L7Profile := Id.run do
  if data.size < h3ProbeMinSize then
    return l7ClassifySmall data.size (l7AdjacentRunSamples data)
  let regBytes := min prescanRegionBytes data.size
  let span := data.size - regBytes
  let mut minUnique := 1000
  let mut maxUnique := 0
  let mut sumUnique := 0
  for r in [0:prescanRegions] do
    let start :=
      if prescanRegions ≤ 1 then 0
      else min ((r * span) / (prescanRegions - 1)) span
    let unique := l7RegionUniquePermille data start (min (start + regBytes) data.size)
    minUnique := min minUnique unique
    maxUnique := max maxUnique unique
    sumUnique := sumUnique + unique
  return l7ClassifyLarge minUnique (sumUnique / max prescanRegions 1) maxUnique

/-- Boxed lazy matcher at an already-selected level-7 profile. -/
def l7MatchFor (data : ByteArray) (profile : L7Profile) : Array LZ77Token :=
  let cfg := l7MatchConfig data profile
  lz77ChainLazyIter data cfg.chainDepth 32768 1000000000 cfg.goodMatch cfg.niceLen
    cfg.lazyDepth cfg.useH3 cfg.lazy2Steps

/-- Packed lazy matcher at an already-selected level-7 profile. -/
def l7MatchPFor (data : ByteArray) (profile : L7Profile) : TokenArray :=
  if l7UseLargeShallow data profile then
    lz77ChainLazyIterPMergedL5Large data 32768 1000000000 64 65
  else
    let cfg := l7MatchConfig data profile
    if cfg.useH3 then
      lz77ChainLazyIterPMergedH3 data cfg.chainDepth 32768 1000000000 cfg.goodMatch
        cfg.niceLen cfg.lazyDepth cfg.lazy2Steps
    else
      lz77ChainLazyIterPMergedNoH3 data cfg.chainDepth 32768 1000000000 cfg.goodMatch
        cfg.niceLen cfg.lazyDepth cfg.lazy2Steps

/-- Rolling lazy2 deferral steps per level (#2837): with steps > 1 the lazy
    matcher keeps deferring while each next position strictly improves
    (libdeflate `deflate_compress_lazy2`), catching cascading-improvement runs
    a single lookahead misses. L7 rolls at cap 4 (the certified spike's
    knee: cap 2 captures most of the gain, cap 64 adds nothing over 4):
    +0.053pp corpus-weighted Silesia at ~+2.4% matcher — ~5x more
    ratio-efficient than deepening toward L8. **L6 does NOT roll (cap 1)**: the
    ld10/cap2 roll won geomean ratio but cost single-stream `zip silesia.tar`
    wall time (see `lazyDepth` — the whole-tar anchor takes priority over the
    per-file geomean margin), so L6 is back at its ld8/no-roll config that
    strictly beats miniz L6 on the whole tar in both size and time. L8's deeper
    chain makes each extra probe ~8x costlier (the spike measured +7.3% matcher
    there), so it stays at 1; the fast band never rolls. Pure parse heuristic —
    the tower (`mergedLoop_eq` and the contracts) is proven for every value. -/
def lazy2StepsLevel (level : UInt8) : Nat :=
  if level == 7 then 4
  else 1

/-- The per-level LZ77 matcher: levels 1–4 use the greedy hash-chain matcher;
    levels ≥ 5 use the one-byte-lookahead
    lazy variant, which improves ratio at equal window/chain depth. Both share the
    same `(chainDepth, insertCap, niceLen)` ladder and satisfy the same encoder
    contracts (`lzMatch_{encodable,empty,resolves}` in `DeflateBlockSplit`), so the
    choice is transparent to the roundtrip proof. The lazy tier probes its `pos+1`
    lookahead at `lazyDepth` (half-depth), a heuristic knob invisible to the proof.
    Levels 6–8 additionally enable the hash3 length-3 singleton, content-gated by
    `useH3For` (on only when the input classifies as low-compressibility). -/
def lzMatch (data : ByteArray) (level : UInt8) : Array LZ77Token :=
  if level == 7 then l7MatchFor data (l7ProfileFor data)
  else if 5 ≤ level then lz77ChainLazyIter data (lazyChainDepthFor data level) 32768 (insertCap level) (goodMatch level) (niceLen level) (lazyDepthFor data level) (useH3For data level) (lazy2StepsLevel level)
  else lz77ChainIter data (chainDepth level) 32768 (insertCap level) (niceLen level)

/-- Packed-token form of `lzMatch` (Wave 3b stage A): the same per-level
    dispatch over the packed matcher twins, producing one unboxed `UInt32`
    per token instead of a boxed `LZ77Token`. The boxed view recovers
    `lzMatch` exactly (`lzMatchP_map` in `Zip/Spec/LZ77PackedCorrect.lean`);
    downstream consumers still run on `lzMatch` — stage B moves them here. -/
def lzMatchP (data : ByteArray) (level : UInt8) : TokenArray :=
  if level == 7 then l7MatchPFor data (l7ProfileFor data)
  else if 5 ≤ level then
    if useL5LargeInputPolicy data level then
      lz77ChainLazyIterPMergedL5Large data 32768
        (insertCap level) (goodMatch level) (niceLen level)
    else
      lz77ChainLazyIterPMerged data (lazyChainDepthFor data level) 32768
        (insertCap level) (goodMatch level) (niceLen level) (lazyDepthFor data level)
        (useH3For data level) (lazy2StepsLevel level)
  else lz77ChainIterPMerged data (chainDepth level) 32768 (insertCap level) (niceLen level)

/-! ## Self-contained block-split dynamic compression

Split `data` into `chunkSize`-byte chunks, match each chunk independently (fresh
32 KiB window, so its back-references stay within the chunk), and emit one dynamic
block per chunk — each with its own frequency-fit Huffman trees, `BFINAL` only on
the last — packed onto one bitstream. Because every block references only its own
chunk, the blocks decode independently and compose; the per-block trees recover
most of the ratio a single whole-file tree leaves on large/heterogeneous inputs. -/

/-- Emit one self-contained dynamic block for the chunk `data[pos, j)` onto `bw`
    (`BFINAL = isFinal`), matching the chunk in isolation. -/
def emitChunkBlock (bw : BitWriter) (data : ByteArray) (pos j : Nat) (level : UInt8)
    (isFinal : Bool) : BitWriter :=
  let chunk := data.extract pos j
  let toks := lzMatch chunk level
  let f := tokenFreqs toks
  let lens := dynamicCodeLengths f.1 f.2
  emitDynBlock bw chunk toks lens.1 lens.2
    (dynamicCodeLengths_length f.1 f.2).1 (dynamicCodeLengths_length f.1 f.2).2 isFinal

/-- Emit the block sequence for `data` from `pos` onward, one block per
    `chunkSize`-byte chunk (the last carries `BFINAL`). Well-founded on the
    remaining bytes so the roundtrip can induct through it. -/
def emitChunkBlocks (data : ByteArray) (chunkSize : Nat) (level : UInt8)
    (pos : Nat) (bw : BitWriter) : BitWriter :=
  let step := max chunkSize 1
  let j := min (pos + step) data.size
  let bw := emitChunkBlock bw data pos j level (decide (j ≥ data.size))
  if j ≥ data.size then bw
  else emitChunkBlocks data chunkSize level j bw
termination_by data.size - pos
decreasing_by simp_all only [Nat.not_le]; omega

/-- Self-contained block-split dynamic compression. See `emitChunkBlock`. -/
def deflateDynamicBlocksSC (data : ByteArray) (chunkSize : Nat) (level : UInt8) : ByteArray :=
  if data.size == 0 then
    let f := tokenFreqs #[]
    (emitDynBlock BitWriter.empty data #[] (dynamicCodeLengths f.1 f.2).1 (dynamicCodeLengths f.1 f.2).2
      (dynamicCodeLengths_length f.1 f.2).1 (dynamicCodeLengths_length f.1 f.2).2 true).flush
  else
    (emitChunkBlocks data chunkSize level 0 BitWriter.empty).flush

/-- Chunk size for block splitting in `deflateRaw`: each ~16 KiB run gets its own
    dynamic Huffman tree and a fresh match window. Large enough to keep per-block
    header overhead negligible, small enough to let the trees track local
    statistics. `pickSmaller` makes the exact value a pure ratio knob (never a
    correctness or regression concern). 16384 is the joint optimum with
    `sharedTokChunk` of a Canterbury + Silesia sweep at levels 7–9 (#2529, `lake
    exe ratio-sweep`). The joint framing matters: in isolation ever-larger chunks
    sized smaller (less window loss), but `deflateRaw` deploys this variant only
    on the files where it beats the cross-block split, and there 16384 won at
    every level. -/
def splitChunkSize : Nat := 16384

/-! ## Cross-block (shared-window) block-split dynamic compression

Unlike the self-contained variant, this matches the **whole** input *once* with
the full 32 KiB window (`lz77ChainIter`), producing one token stream whose
back-references are valid against the running output, then **partitions that
token stream** by token count into per-block groups. Each group is re-Huffman
coded with its own dynamic tree; references freely cross block boundaries
(RFC 1951 §3.2), so this recovers the cross-chunk matches the self-contained
split discards — the lever for the text-ratio gap. `pickSmaller` gates it so it
can never regress. -/

/-- Emit one shared-window dynamic block for a *slice* `group` of the
    whole-stream token array onto `bw` (`BFINAL = isFinal`). The whole (non-empty)
    `data` is passed only to satisfy `emitDynBlock`'s empty-input guard, so the
    group's tokens are always emitted; the Huffman trees fit `group`'s own
    frequencies. -/
def emitSharedBlock (bw : BitWriter) (data : ByteArray) (group : Array LZ77Token)
    (isFinal : Bool) : BitWriter :=
  let f := tokenFreqs group
  let lens := dynamicCodeLengths f.1 f.2
  emitDynBlock bw data group lens.1 lens.2
    (dynamicCodeLengths_length f.1 f.2).1 (dynamicCodeLengths_length f.1 f.2).2 isFinal

/-- Emit the shared-window block sequence for the whole-stream token array `toks`
    from token index `pos`, one block per `tokChunk` tokens (the last carries
    `BFINAL`). Well-founded on the remaining token count so the roundtrip can
    induct through it. -/
def emitSharedBlocks (data : ByteArray) (toks : Array LZ77Token) (tokChunk : Nat)
    (pos : Nat) (bw : BitWriter) : BitWriter :=
  let step := max tokChunk 1
  let j := min (pos + step) toks.size
  let bw := emitSharedBlock bw data (toks.extract pos j) (decide (j ≥ toks.size))
  if j ≥ toks.size then bw
  else emitSharedBlocks data toks tokChunk j bw
termination_by toks.size - pos
decreasing_by simp_all only [Nat.not_le]; omega

/-- Token-group size for cross-block splitting in `deflateRaw`: number of LZ77
    tokens per block. A pure ratio knob (`pickSmaller` guards regression); 8192
    is the joint optimum with `splitChunkSize` of a Canterbury + Silesia sweep at
    levels 7–9 (#2529, `lake exe ratio-sweep`) — the same value at every level,
    so a single global default suffices. Smaller groups are dominated by
    per-block header overhead, larger ones by coarser local-statistics tracking;
    the curve is shallow around the optimum (8192 beat 16384 by ~0.015% of
    corpus total) but moving off the prior single-sample 4096 was worth ~0.19%. -/
def sharedTokChunk : Nat := 8192

/-- Cross-block (shared-window) block-split dynamic compression. Matches the
    whole input once, then partitions the token stream into `tokChunk`-token
    blocks. See `emitSharedBlock`. -/
def deflateDynamicBlocksShared (data : ByteArray) (tokChunk : Nat) (level : UInt8) : ByteArray :=
  if data.size == 0 then
    let f := tokenFreqs #[]
    (emitDynBlock BitWriter.empty data #[] (dynamicCodeLengths f.1 f.2).1 (dynamicCodeLengths f.1 f.2).2
      (dynamicCodeLengths_length f.1 f.2).1 (dynamicCodeLengths_length f.1 f.2).2 true).flush
  else
    (emitSharedBlocks data (lzMatch data level)
      tokChunk 0 BitWriter.empty).flush

/-- Emit shared-window blocks at explicit cut points: each element of `cuts` is
    an absolute token index ending the current block. Every cut is clamped to
    `(pos, toks.size]`, so **any** cuts list — empty, non-monotone, or out of
    range — yields a valid total partition; an empty list emits one final block
    of the rest. The clamping is what keeps the boundary *heuristic* free of
    proof obligations: the roundtrip holds for an arbitrary partition. -/
def emitSharedBlocksAt (data : ByteArray) (toks : Array LZ77Token) (cuts : List Nat)
    (pos : Nat) (bw : BitWriter) : BitWriter :=
  let j := min (max (cuts.headD toks.size) (pos + 1)) toks.size
  let bw := emitSharedBlock bw data (toks.extract pos j) (decide (j ≥ toks.size))
  if j ≥ toks.size then bw
  else emitSharedBlocksAt data toks cuts.tail j bw
termination_by toks.size - pos
decreasing_by
  rename_i h
  simp only [Nat.not_le] at h
  omega

/-- Cross-block (shared-window) block-split dynamic compression with the
    partition chosen by `choose`: like `deflateDynamicBlocksShared`, but the
    per-block token groups come from the cut list `choose toks` instead of a
    fixed cadence. The roundtrip holds for any `choose` (the emitter clamps
    every cut), so the selector is a pure ratio heuristic. -/
def deflateDynamicBlocksSharedAtTokens (data : ByteArray) (toks : Array LZ77Token)
    (choose : Array LZ77Token → List Nat) : ByteArray :=
  if data.size == 0 then
    let f := tokenFreqs #[]
    (emitDynBlock BitWriter.empty data #[] (dynamicCodeLengths f.1 f.2).1 (dynamicCodeLengths f.1 f.2).2
      (dynamicCodeLengths_length f.1 f.2).1 (dynamicCodeLengths_length f.1 f.2).2 true).flush
  else
    (emitSharedBlocksAt data toks (choose toks) 0 BitWriter.empty).flush

/-- `deflateDynamicBlocksSharedAtTokens` over this level's `lzMatch` stream.
    Kept as a definitional wrapper so the level-9 dispatch can share one
    matcher pass across candidates (Wave 1): the spec lemmas are stated about
    this wrapper and see through it by `rfl`. -/
def deflateDynamicBlocksSharedAt (data : ByteArray)
    (choose : Array LZ77Token → List Nat) (level : UInt8) : ByteArray :=
  deflateDynamicBlocksSharedAtTokens data (lzMatch data level) choose

/-! ## Entropy-divergence boundary heuristic (libdeflate-style)

Instead of cutting the shared-window token stream at a fixed cadence, walk it
once and close a block where the symbol statistics *shift*: maintain a coarse
observation histogram for the block so far and one for a recent window, and cut
when the scaled distribution delta exceeds a threshold (libdeflate
`deflate_compress.c`, `observe_literal`/`observe_match`/`do_end_block_check`).
Every constant below is a pure ratio knob: the emitter clamps arbitrary cuts,
so none of this carries proof obligations, and `chooseSplitsArbitrated` sizes
the result against the fixed cadence in exact bits so the heuristic can never
regress the shared-window candidate. -/

/-- Number of literal observation classes (libdeflate
    `NUM_LITERAL_OBSERVATION_TYPES`): literals are bucketed by bits 7,6,0 —
    a cheap proxy separating case/digit/punctuation regimes. -/
def splitNumLiteralClasses : Nat := 8

/-- Total observation classes (libdeflate `NUM_OBSERVATION_TYPES`): 8 literal
    classes plus 2 match classes (short/long). -/
def splitNumClasses : Nat := 10

/-- New observations between divergence checks (libdeflate
    `NUM_OBSERVATIONS_PER_BLOCK_CHECK`): the recent-window size in tokens. -/
def splitCheckTokens : Nat := 512

/-- Lower edge of the shallow-profile band that benefits from a 4096-token
    split-check cadence. -/
def l7ShallowCoarseMinSize : Nat := 384 * 1024

/-- Upper edge of the shallow-profile 4096-token split-check band, and lower
    edge of its 1024-token band. -/
def l7ShallowCoarseMaxSize : Nat := 448 * 1024

/-- Upper edge of the shallow-profile 1024-token split-check band. -/
def l7ShallowMediumMaxSize : Nat := 512 * 1024

/-- Upper input-size edge for the moderate-size `h3Balanced` 1024-token
    split-check specialization. -/
def l7BalancedMediumMaxSize : Nat := 7 * 1000 * 1000

/-- Observation-window cadence paired with a selected level-7 profile and
    input size.

    This policy keeps the established 512-token default and the large-shallow
    2016-token point.  A median-of-five Canterbury + Silesia production sweep
    selected coarser checks where the saved boundary work repeated end to end:
    4096 for medium-small shallow text, small `chain128Probe16`, and
    `chain96Probe16`/`chain128LongProbe32`; 1024 for the next shallow size band,
    moderate-size `h3Balanced`, large `chain64Probe16`, and large `h3Fast`.
    The selector changes only a heuristic cut list; the emitter clamps arbitrary
    cuts, so these size/profile choices add no roundtrip proof obligation. -/
def l7SplitCheckTokensForSize (size : Nat) (profile : L7Profile) : Nat :=
  if profile == .shallow && l5LargeInputMinSize ≤ size then 2016
  else
    match profile with
    | .shallow =>
        if l7ShallowCoarseMinSize ≤ size && size < l7ShallowCoarseMaxSize then 4096
        else if l7ShallowCoarseMaxSize ≤ size && size < l7ShallowMediumMaxSize then 1024
        else splitCheckTokens
    | .h3Fast => if h3ProbeMinSize ≤ size then 1024 else splitCheckTokens
    | .h3Balanced =>
        if h3ProbeMinSize ≤ size && size < l7BalancedMediumMaxSize then 1024
        else splitCheckTokens
    | .chain64Probe16 => if h3ProbeMinSize ≤ size then 1024 else splitCheckTokens
    | .chain96Probe16 => 4096
    | .chain128LongProbe32 => 4096
    | .chain128Probe16 => if size < h3ProbeMinSize then 4096 else splitCheckTokens
    | _ => splitCheckTokens

/-- `l7SplitCheckTokensForSize` at the input's actual size. -/
def l7SplitCheckTokensFor (data : ByteArray) (profile : L7Profile) : Nat :=
  l7SplitCheckTokensForSize data.size profile

/-- Per-level observation-window cadence for the shared-block split heuristic.
    Large-stream L5 uses a coarser window: at its shallow chain, checking every
    2016 tokens preserves enough block adaptation that its 12-file geometric-mean
    ratio remains slightly smaller than the established miniz_oxide L5 Silesia
    reference (0.327237 vs 0.327302), while removing much of the entropy-check
    and tree-preparation overhead. Corpus-total bytes instead favor miniz_oxide by
    0.17%, led by `mozilla`; this is an intentional fixed-L5 ratio/speed trade.
    Small L5 streams and L6–L8 retain the established 512-token cadence, so their
    bytes are unchanged. The cadence is independent of whether the scalar or
    packed-counter walker implements the heuristic. -/
def splitCheckTokensFor (data : ByteArray) (level : UInt8) : Nat :=
  if level == 7 then l7SplitCheckTokensFor data (l7ProfileFor data)
  else if useL5LargeInputPolicy data level then 2016
  else splitCheckTokens

/-- Floor on block *output* bytes, and on bytes remaining after a cut
    (libdeflate `MIN_BLOCK_LENGTH`): per-block tree headers stop paying for
    themselves below this, per the #2527 `sharedTokChunk` sweep. -/
def splitMinBlockBytes : Nat := 10000

/-- Unconditional cut ceiling on block output bytes (libdeflate
    `SOFT_MAX_BLOCK_LENGTH`): even statistically-uniform runs get a fresh tree
    at this scale, bounding how stale the code lengths can grow. -/
def splitSoftMaxBlockBytes : Nat := 300000

/-- Divergence threshold numerator/denominator (libdeflate's `200/512`): cut
    when the sum of absolute probability deltas reaches ~39%. -/
def splitCutoffNum : Nat := 200
/-- See `splitCutoffNum`. -/
def splitCutoffDen : Nat := 512

/-- Length bias divisor (libdeflate's `block_length / 4096` term): longer
    blocks cut progressively easier, since a fresh tree amortizes better. -/
def splitBiasBytes : Nat := 4096

/-- Observation class of a token (libdeflate `observe_literal`/`observe_match`):
    literals map to 0–7 by bits 7,6,0; matches map to 8 (length < 9) or 9. -/
@[inline] def splitTokenClass : LZ77Token → Nat
  | .literal b => (((b >>> 5) &&& 6) ||| (b &&& 1)).toNat
  | .reference len _ => splitNumLiteralClasses + (if len ≥ 9 then 1 else 0)

/-- Output bytes a token contributes: 1 for a literal, the match length for a
    reference. -/
@[inline] def splitTokenBytes : LZ77Token → Nat
  | .literal _ => 1
  | .reference len _ => len

/-- The divergence test (libdeflate `do_end_block_check`): cut when
    `Σᵢ |new[i]·oldTot − old[i]·newTot| + (blockBytes/splitBiasBytes)·oldTot`
    reaches `newTot·splitCutoffNum/splitCutoffDen·oldTot` — i.e. the recent
    window's class distribution differs from the block-so-far distribution by
    at least ~39% probability mass (less for long blocks). Integer-only; the
    caller guarantees `oldTot > 0`. libdeflate additionally inflates the cutoff
    for blocks under `MIN_BLOCK_LENGTH`, but our caller (like libdeflate's
    `ready_to_check_block`) never checks such blocks, so that branch is omitted
    as dead code. -/
def splitEndBlockCheck (old : Array Nat) (oldTot : Nat) (new : Array Nat) (newTot : Nat)
    (blockBytes : Nat) : Bool := Id.run do
  let mut delta := 0
  for i in [0:splitNumClasses] do
    let a := new.getD i 0 * oldTot
    let b := old.getD i 0 * newTot
    delta := delta + (if a ≥ b then a - b else b - a)
  let cutoff := newTot * splitCutoffNum / splitCutoffDen * oldTot
  return delta + (blockBytes / splitBiasBytes) * oldTot ≥ cutoff

/-- Entropy-divergence cut points for the shared-window token stream: one pass
    over `toks`, accumulating per-class observation counts. Block-so-far
    (`old`) and recent-window (`new`) histograms are compared every
    `splitCheckTokens` tokens once the block and the remaining input are both
    at least `splitMinBlockBytes` output bytes; on divergence the block is cut
    at the next token boundary, otherwise the window merges into `old`. Blocks
    are force-cut at `splitSoftMaxBlockBytes`. Byte floor/ceiling are enforced
    per-token (a single 512-token window can span ~132 KB of output via long
    matches, so checking them only at window boundaries could overshoot). -/
def chooseSplitsHeuristic (toks : Array LZ77Token) : List Nat := Id.run do
  let mut totalBytes := 0
  for t in toks do
    totalBytes := totalBytes + splitTokenBytes t
  let mut old : Array Nat := Array.replicate splitNumClasses 0
  let mut oldTot := 0
  let mut new : Array Nat := Array.replicate splitNumClasses 0
  let mut newTot := 0
  let mut blockBytes := 0
  let mut doneBytes := 0
  let mut cuts : Array Nat := #[]
  for h : i in [0:toks.size] do
    let t := toks[i]
    let c := splitTokenClass t
    new := new.set! c (new.getD c 0 + 1)
    newTot := newTot + 1
    blockBytes := blockBytes + splitTokenBytes t
    doneBytes := doneBytes + splitTokenBytes t
    if blockBytes ≥ splitMinBlockBytes && totalBytes - doneBytes ≥ splitMinBlockBytes then
      let cut :=
        blockBytes ≥ splitSoftMaxBlockBytes ||
        (newTot ≥ splitCheckTokens && oldTot > 0 &&
          splitEndBlockCheck old oldTot new newTot blockBytes)
      if cut then
        cuts := cuts.push (i + 1)
        old := Array.replicate splitNumClasses 0
        oldTot := 0
        new := Array.replicate splitNumClasses 0
        newTot := 0
        blockBytes := 0
      else if newTot ≥ splitCheckTokens then
        for j in [0:splitNumClasses] do
          old := old.set! j (old.getD j 0 + new.getD j 0)
        oldTot := oldTot + newTot
        new := Array.replicate splitNumClasses 0
        newTot := 0
  return cuts.toList

/-- The cut list equivalent to `emitSharedBlocks`'s fixed cadence: multiples of
    `max tokChunk 1` strictly below `n`. `emitSharedBlocksAt … (fixedCadenceCuts
    tokChunk toks.size)` emits byte-for-byte what `emitSharedBlocks … tokChunk`
    emits (pinned by a conformance test). -/
def fixedCadenceCuts (tokChunk n : Nat) : List Nat :=
  let step := max tokChunk 1
  (List.range ((n + step - 1) / step)).filterMap fun k =>
    if k == 0 then none else some (k * step)

/-- Exact bit size of the shared-window block stream `emitSharedBlocksAt` would
    emit for this partition, without emitting: per group, `3` header bits plus
    the dynamic-tree header (sized by running `writeDynamicHeader` into an
    empty writer, as `dynBlockBytes` does) plus the freq·codeLen dot product
    (`symbolBitCount`, which includes the end-of-block symbol). Mirrors the
    emitter's grouping exactly — same clamped cut `j`, same final-block test —
    so `(emitSharedBlocksAt …).bitLength` equals this sum (pinned by a
    `SizeHelpers` conformance test; the flushed byte size is `⌈bits/8⌉`). -/
def sharedPartitionBits (toks : Array LZ77Token) (cuts : List Nat) (pos : Nat) : Nat :=
  let j := min (max (cuts.headD toks.size) (pos + 1)) toks.size
  let f := tokenFreqs (toks.extract pos j)
  let lens := dynamicCodeLengths f.1 f.2
  let blockBits := 3 + (writeDynamicHeader BitWriter.empty lens.1 lens.2).bitLength
    + symbolBitCount f.1 f.2 lens.1.toArray lens.2.toArray
  if j ≥ toks.size then blockBits
  else blockBits + sharedPartitionBits toks cuts.tail j
termination_by toks.size - pos
decreasing_by
  rename_i h
  simp only [Nat.not_le] at h
  omega

/-- Cost-model arbitration between the entropy-divergence cuts and the fixed
    `sharedTokChunk` cadence: size both partitions in exact unflushed bits and
    keep the smaller, **ties → fixed**. Since the emitted stream is one final
    flush of exactly those bits (byte size `⌈bits/8⌉`), heuristic bits ≤ fixed
    bits implies the emitted candidate never exceeds the old fixed-cadence one
    — any observed regression is a `sharedPartitionBits` conformance bug, not
    rounding. The sizing costs two extra `O(tokens)` passes; the matcher still
    dominates at the levels that use this. -/
def chooseSplitsArbitrated (toks : Array LZ77Token) : List Nat :=
  let h := chooseSplitsHeuristic toks
  let f := fixedCadenceCuts sharedTokChunk toks.size
  if sharedPartitionBits toks h 0 < sharedPartitionBits toks f 0 then h else f

/-! ## Sized-tree reuse for the winning partition (Wave 5, #2552)

`chooseSplitsArbitrated` already builds every block's Huffman trees
(`dynamicCodeLengths` over `tokenFreqs` of the group) while *sizing* the two
candidate partitions; `emitSharedBlocksAt` then rebuilt the same trees a third
time for the winning partition at emission. The variants below return the cuts
*together with* the winner's per-block sized trees and feed them to a
tree-taking emitter, so emission never re-runs the frequency pass or the
Huffman build. `emitSharedBlocksAt` stays as the reference emitter:
`deflateDynamicBlocksSharedSized_eq` (`Zip/Spec/DeflateBlockSplit.lean`) proves
the sized pipeline byte-identical, so the spec quadruple is untouched. -/

/-- A per-block pair of code-length lists carrying the alphabet-size facts the
    emitter needs (286 lit/len, 30 distance) — what `dynamicCodeLengths`
    produces, bundled with `dynamicCodeLengths_length`. -/
def SizedTrees : Type :=
  {p : List Nat × List Nat // p.1.length = 286 ∧ p.2.length = 30}

/-- The sized trees `dynamicCodeLengths` selects for the given frequencies. -/
@[inline] def sizedTrees (litFreqs distFreqs : Array Nat) : SizedTrees :=
  ⟨dynamicCodeLengths litFreqs distFreqs,
    (dynamicCodeLengths_length litFreqs distFreqs).1,
    (dynamicCodeLengths_length litFreqs distFreqs).2⟩

/-- The sized trees of the empty token group: the (never-reached) `headD`
    default in `emitSharedBlocksAtSized` — the trees list produced by
    `sharedPartitionSized` always covers every emitted block. -/
def emptySizedTrees : SizedTrees :=
  sizedTrees (tokenFreqs #[]).1 (tokenFreqs #[]).2

/-- `sharedPartitionBits` fused with tree collection: walk the partition once,
    returning the exact bit size **together with** each block's sized trees, so
    the winning partition's emission can reuse them instead of re-running
    `tokenFreqs` + `dynamicCodeLengths` per block. Component 1 is exactly
    `sharedPartitionBits` (`sharedPartitionSized_fst`); component 2's entries
    are definitionally `dynamicCodeLengths (tokenFreqs group)` of the emitter's
    groups (`emitSharedBlocksAtSized_eq`). -/
def sharedPartitionSized (toks : Array LZ77Token) (cuts : List Nat) (pos : Nat) :
    Nat × List SizedTrees :=
  let j := min (max (cuts.headD toks.size) (pos + 1)) toks.size
  let f := tokenFreqs (toks.extract pos j)
  let t := sizedTrees f.1 f.2
  let blockBits := 3 + (writeDynamicHeader BitWriter.empty t.val.1 t.val.2).bitLength
    + symbolBitCount f.1 f.2 t.val.1.toArray t.val.2.toArray
  if j ≥ toks.size then (blockBits, [t])
  else
    let rest := sharedPartitionSized toks cuts.tail j
    (blockBits + rest.1, t :: rest.2)
termination_by toks.size - pos
decreasing_by
  rename_i h
  simp only [Nat.not_le] at h
  omega

/-- Tree-taking twin of `emitSharedBlocksAt`: same clamped cut points, but each
    block's `(litLens, distLens)` come from the `trees` list (in lockstep with
    `cuts`) instead of being recomputed from the group. Byte-identical to
    `emitSharedBlocksAt` when `trees` is the sizing pass's output
    (`emitSharedBlocksAtSized_eq`). -/
def emitSharedBlocksAtSized (data : ByteArray) (toks : Array LZ77Token) (cuts : List Nat)
    (trees : List SizedTrees) (pos : Nat) (bw : BitWriter) : BitWriter :=
  let j := min (max (cuts.headD toks.size) (pos + 1)) toks.size
  let t := trees.headD emptySizedTrees
  let bw := emitDynBlock bw data (toks.extract pos j) t.val.1 t.val.2
    t.property.1 t.property.2 (decide (j ≥ toks.size))
  if j ≥ toks.size then bw
  else emitSharedBlocksAtSized data toks cuts.tail trees.tail j bw
termination_by toks.size - pos
decreasing_by
  rename_i h
  simp only [Nat.not_le] at h
  omega

/-- `chooseSplitsArbitrated` returning the winning cuts **with** the winner's
    per-block sized trees (component 1 is exactly `chooseSplitsArbitrated` —
    via `sharedPartitionSized_fst`, see `deflateDynamicBlocksSharedSized_eq`).
    The sizing of both candidates is inherent to arbitration; only the third
    (emission-time) tree pass is avoidable, and the returned trees are what
    avoid it. -/
def chooseSplitsArbitratedSized (toks : Array LZ77Token) : List Nat × List SizedTrees :=
  let h := chooseSplitsHeuristic toks
  let f := fixedCadenceCuts sharedTokChunk toks.size
  let sh := sharedPartitionSized toks h 0
  let sf := sharedPartitionSized toks f 0
  if sh.1 < sf.1 then (h, sh.2) else (f, sf.2)

/-- The arbitrated shared-window candidate with sized-tree reuse: byte-identical
    to `deflateDynamicBlocksSharedAtTokens data toks chooseSplitsArbitrated`
    (`deflateDynamicBlocksSharedSized_eq`), but the winning partition's
    per-block `tokenFreqs` + `dynamicCodeLengths` run once (during sizing)
    instead of twice. Retired from the `deflateRaw` dispatch by #2737 — the
    observation-divergence split (`deflateDynamicBlocksSharedAtP`) picks
    boundaries with no sizing pass at all — but kept, with its proofs and
    conformance tests, as the arbitrated reference pipeline. -/
def deflateDynamicBlocksSharedSized (data : ByteArray) (toks : Array LZ77Token) : ByteArray :=
  if data.size == 0 then
    let f := tokenFreqs #[]
    (emitDynBlock BitWriter.empty data #[] (dynamicCodeLengths f.1 f.2).1 (dynamicCodeLengths f.1 f.2).2
      (dynamicCodeLengths_length f.1 f.2).1 (dynamicCodeLengths_length f.1 f.2).2 true).flush
  else
    let c := chooseSplitsArbitratedSized toks
    (emitSharedBlocksAtSized data toks c.1 c.2 0 BitWriter.empty).flush

/-! ## Packed observation-divergence block splitting (#2737)

The libdeflate-style divergence heuristic and the shared-window block emitter,
both walking the `packTok`-encoded `UInt32` stream directly — the packed twins
of `chooseSplitsHeuristic` and `emitSharedBlocksAt`. This is what lets the
mid-band levels (5–8) afford per-block Huffman trees at all: the per-block
frequency pass runs on `tokenFreqsPTA` (dense packed tables), while the shared
emitter uses the packed `emitDynBlockP` token loop, so the split candidate never
materializes boxed `LZ77Token`s and never touches the `findTableCode` linear
scans. At level 8 the
same pipeline **replaces** the `chooseSplitsArbitrated` sizing pass: libdeflate
picks boundaries with the streaming heuristic alone (no exact-bits arbitration),
and the sizing pass — two extra boxed `tokenFreqs`+`symbolBitCount` walks over
the whole token stream — was ~18% of level-8 cycles. The heuristic stays
proof-free: the emitter clamps every cut (`emitSharedBlocksAtP` mirrors
`emitSharedBlocksAt`'s clamping exactly), and the roundtrip transfers from the
boxed reference via `deflateDynamicBlocksSharedAtP_eq`
(`Zip/Spec/LZ77PackedCorrect.lean`). -/

/-- Observation class of a packed token (`splitTokenClass` over the packed
    fields, conformance-tested in `ZipTest/PackedTokens.lean`): literals (tag
    bit clear) map to 0–7 by bits 7,6,0 of the byte field; references map to 8
    (length < 9) or 9. -/
@[inline] def splitTokenClassP (w : UInt32) : Nat :=
  if w &&& ((1 : UInt32) <<< 31) = 0 then
    (((w.toUInt8 >>> 5) &&& 6) ||| (w.toUInt8 &&& 1)).toNat
  else
    splitNumLiteralClasses + (if ((w >>> 16) &&& 0x7FFF).toNat ≥ 9 then 1 else 0)

/-- Output bytes a packed token contributes (`splitTokenBytes` over the packed
    fields): 1 for a literal, the length field for a reference. -/
@[inline] def splitTokenBytesP (w : UInt32) : Nat :=
  if w &&& ((1 : UInt32) <<< 31) = 0 then 1
  else ((w >>> 16) &&& 0x7FFF).toNat

/-- Increment the observation counter selected by a `Nat` class.  Kept as a
    named inline helper so the reference and native-word split walkers can be
    related without expanding ten nested tuple projections at every step. -/
@[inline] def splitBumpN (c : Nat)
    (n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 : Nat) :
    Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat :=
  match c with
  | 0 => (n0 + 1, n1, n2, n3, n4, n5, n6, n7, n8, n9)
  | 1 => (n0, n1 + 1, n2, n3, n4, n5, n6, n7, n8, n9)
  | 2 => (n0, n1, n2 + 1, n3, n4, n5, n6, n7, n8, n9)
  | 3 => (n0, n1, n2, n3 + 1, n4, n5, n6, n7, n8, n9)
  | 4 => (n0, n1, n2, n3, n4 + 1, n5, n6, n7, n8, n9)
  | 5 => (n0, n1, n2, n3, n4, n5 + 1, n6, n7, n8, n9)
  | 6 => (n0, n1, n2, n3, n4, n5, n6 + 1, n7, n8, n9)
  | 7 => (n0, n1, n2, n3, n4, n5, n6, n7 + 1, n8, n9)
  | 8 => (n0, n1, n2, n3, n4, n5, n6, n7, n8 + 1, n9)
  | _ => (n0, n1, n2, n3, n4, n5, n6, n7, n8, n9 + 1)

/-- The per-token core of `chooseSplitsHeuristicP`, threaded as a tail-recursive
    loop over explicit scalar state so the hot accumulators compile to register
    arithmetic instead of `Array Nat` `set!`/`getD` (#2762). The ten observation
    counters live in the `n0..n9` (recent window) and `o0..o9` (block-so-far)
    locals; `newTot`/`oldTot`/`blockBytes` are the window/block totals, and
    `remaining` is the running byte suffix `totalBytes − doneBytes` (decremented
    per token) that gates cuts against the min-block floor without a second
    pass. The full ten-counter arrays are materialized only at a divergence
    check (every `checkTokens` tokens, once the floors clear), where the shared
    boxed `splitEndBlockCheck` reads them. -/
def chooseSplitsHeuristicP.go (toks : TokenArray)
    (minBlockBytes softMaxBlockBytes checkTokens : Nat) (i : Nat)
    (o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 oldTot : Nat)
    (n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 newTot : Nat)
    (blockBytes remaining : Nat) (cuts : Array Nat) : Array Nat :=
  if h : i < toks.size then
    let t := toks.get i h
    let c := splitTokenClassP t
    let tb := splitTokenBytesP t
    let (n0, n1, n2, n3, n4, n5, n6, n7, n8, n9) :=
      splitBumpN c n0 n1 n2 n3 n4 n5 n6 n7 n8 n9
    let newTot := newTot + 1
    let blockBytes := blockBytes + tb
    let remaining := remaining - tb
    if blockBytes ≥ minBlockBytes && remaining ≥ minBlockBytes then
      let cut :=
        blockBytes ≥ softMaxBlockBytes ||
        (newTot ≥ checkTokens && oldTot > 0 &&
          splitEndBlockCheck #[o0, o1, o2, o3, o4, o5, o6, o7, o8, o9] oldTot
            #[n0, n1, n2, n3, n4, n5, n6, n7, n8, n9] newTot blockBytes)
      if cut then
        chooseSplitsHeuristicP.go toks minBlockBytes softMaxBlockBytes checkTokens (i + 1)
          0 0 0 0 0 0 0 0 0 0 0
          0 0 0 0 0 0 0 0 0 0 0
          0 remaining (cuts.push (i + 1))
      else if newTot ≥ checkTokens then
        chooseSplitsHeuristicP.go toks minBlockBytes softMaxBlockBytes checkTokens (i + 1)
          (o0 + n0) (o1 + n1) (o2 + n2) (o3 + n3) (o4 + n4) (o5 + n5) (o6 + n6) (o7 + n7)
          (o8 + n8) (o9 + n9) (oldTot + newTot)
          0 0 0 0 0 0 0 0 0 0 0
          blockBytes remaining cuts
      else
        chooseSplitsHeuristicP.go toks minBlockBytes softMaxBlockBytes checkTokens (i + 1)
          o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 oldTot
          n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 newTot
          blockBytes remaining cuts
    else
      chooseSplitsHeuristicP.go toks minBlockBytes softMaxBlockBytes checkTokens (i + 1)
        o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 oldTot
        n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 newTot
        blockBytes remaining cuts
  else cuts
termination_by toks.size - i
decreasing_by all_goals omega

/-- Packed twin of `chooseSplitsHeuristic`: entropy-divergence cut points
    computed directly from the packed token stream — same constants, same
    per-token floors/ceiling, same window-merge cadence, with
    `splitTokenClassP`/`splitTokenBytesP` in place of the boxed accessors.
    Heuristic-only (the emitter clamps arbitrary cuts), so it carries no proof
    obligations; `ZipTest/PackedTokens.lean` pins it to the boxed heuristic
    over the `unpackTok` view. The block floor/ceiling and check cadence are
    defaulted parameters so the `mid-sweep` tuning tool can grid them without
    touching the dispatch. Production normally uses those defaults; large L5
    streams explicitly pass their coarser 2016-token cadence.

    `totalBytes` is the whole-stream output byte count `Σ splitTokenBytesP t`.
    The boxed reference computes it with a leading pass over `toks`; the packed
    dispatch passes `data.size` instead (the token stream decodes to `data`, so
    the two agree — pinned by the `chooseSplitsHeuristic` conformance test),
    fusing that pass away (#2762). The main walk then tracks the running byte
    suffix in `remaining` (start `totalBytes`, minus each token's bytes) rather
    than a `doneBytes` prefix, and computes `splitTokenBytesP` once per token. -/
def chooseSplitsHeuristicP (toks : TokenArray) (totalBytes : Nat)
    (minBlockBytes : Nat := splitMinBlockBytes)
    (softMaxBlockBytes : Nat := splitSoftMaxBlockBytes)
    (checkTokens : Nat := splitCheckTokens) : List Nat :=
  -- Before an underflow, `blockBytes + remaining = totalBytes`; after one,
  -- saturated `remaining` stays below the tail floor. Thus both min-block
  -- floors cannot hold when the whole stream is below twice the floor.
  if totalBytes < 2 * minBlockBytes then []
  else
    (chooseSplitsHeuristicP.go toks minBlockBytes softMaxBlockBytes checkTokens 0
      0 0 0 0 0 0 0 0 0 0 0
      0 0 0 0 0 0 0 0 0 0 0
      0 totalBytes #[]).toList

/-- `Array UInt32` reference walker for `chooseSplitsHeuristicP.go`: the exact
    pre-`TokenArray` body, reading each packed word from an `Array UInt32` slot
    (`toks[i]`) instead of the 4-byte `TokenArray` container (`toks.get i h`).
    Kept purely as a proof reference — the split heuristic is control flow (it
    picks block cut points), so `inflate_deflateRaw` (which proves any *valid*
    output decodes, not that the output is *unchanged*) gives no cover here; the
    refinement `chooseSplitsHeuristicP.go_toArray` pins the packed walker's cut
    list to this reference's, so the boundaries the packed dispatch feeds the
    emitter are byte-for-byte the ones the `Array UInt32` implementation chose. -/
def chooseSplitsHeuristicPArray.go (toks : Array UInt32)
    (minBlockBytes softMaxBlockBytes checkTokens : Nat) (i : Nat)
    (o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 oldTot : Nat)
    (n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 newTot : Nat)
    (blockBytes remaining : Nat) (cuts : Array Nat) : Array Nat :=
  if h : i < toks.size then
    let t := toks[i]
    let c := splitTokenClassP t
    let tb := splitTokenBytesP t
    let (n0, n1, n2, n3, n4, n5, n6, n7, n8, n9) :=
      splitBumpN c n0 n1 n2 n3 n4 n5 n6 n7 n8 n9
    let newTot := newTot + 1
    let blockBytes := blockBytes + tb
    let remaining := remaining - tb
    if blockBytes ≥ minBlockBytes && remaining ≥ minBlockBytes then
      let cut :=
        blockBytes ≥ softMaxBlockBytes ||
        (newTot ≥ checkTokens && oldTot > 0 &&
          splitEndBlockCheck #[o0, o1, o2, o3, o4, o5, o6, o7, o8, o9] oldTot
            #[n0, n1, n2, n3, n4, n5, n6, n7, n8, n9] newTot blockBytes)
      if cut then
        chooseSplitsHeuristicPArray.go toks minBlockBytes softMaxBlockBytes checkTokens (i + 1)
          0 0 0 0 0 0 0 0 0 0 0
          0 0 0 0 0 0 0 0 0 0 0
          0 remaining (cuts.push (i + 1))
      else if newTot ≥ checkTokens then
        chooseSplitsHeuristicPArray.go toks minBlockBytes softMaxBlockBytes checkTokens (i + 1)
          (o0 + n0) (o1 + n1) (o2 + n2) (o3 + n3) (o4 + n4) (o5 + n5) (o6 + n6) (o7 + n7)
          (o8 + n8) (o9 + n9) (oldTot + newTot)
          0 0 0 0 0 0 0 0 0 0 0
          blockBytes remaining cuts
      else
        chooseSplitsHeuristicPArray.go toks minBlockBytes softMaxBlockBytes checkTokens (i + 1)
          o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 oldTot
          n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 newTot
          blockBytes remaining cuts
    else
      chooseSplitsHeuristicPArray.go toks minBlockBytes softMaxBlockBytes checkTokens (i + 1)
        o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 oldTot
        n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 newTot
        blockBytes remaining cuts
  else cuts
termination_by toks.size - i
decreasing_by all_goals omega

/-- Entry point for the `Array UInt32` reference walker (pre-`TokenArray` body). -/
def chooseSplitsHeuristicPArray (toks : Array UInt32) (totalBytes : Nat)
    (minBlockBytes : Nat := splitMinBlockBytes)
    (softMaxBlockBytes : Nat := splitSoftMaxBlockBytes)
    (checkTokens : Nat := splitCheckTokens) : List Nat :=
  if totalBytes < 2 * minBlockBytes then []
  else
    (chooseSplitsHeuristicPArray.go toks minBlockBytes softMaxBlockBytes checkTokens 0
      0 0 0 0 0 0 0 0 0 0 0
      0 0 0 0 0 0 0 0 0 0 0
      0 totalBytes #[]).toList

/-- **Split-walker refinement (byte-identity of the cut points).** The packed
    `TokenArray` walk equals the `Array UInt32` reference walk over the `.toArray`
    view, at every index and every scalar accumulator state threaded through the
    recursion: identical control flow, each `toks.get i h` read bridged to the
    boxed slot by `TokenArray.get_toArray` and each bound by `size_toArray`. The
    whole per-token scalar/branch logic (`splitTokenClassP`/`splitTokenBytesP`,
    the ten-counter window merge, the cut test) is then literally the same term
    on both sides, so a divergence would break this equation. -/
theorem chooseSplitsHeuristicP.go_toArray (toks : TokenArray)
    (minBlockBytes softMaxBlockBytes checkTokens : Nat) :
    ∀ (fuel i : Nat), toks.size - i < fuel →
      ∀ (o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 oldTot : Nat)
        (n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 newTot : Nat)
        (blockBytes remaining : Nat) (cuts : Array Nat),
        chooseSplitsHeuristicP.go toks minBlockBytes softMaxBlockBytes checkTokens i
            o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 oldTot
            n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 newTot blockBytes remaining cuts
          = chooseSplitsHeuristicPArray.go toks.toArray minBlockBytes softMaxBlockBytes checkTokens i
            o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 oldTot
            n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 newTot blockBytes remaining cuts := by
  intro fuel
  induction fuel with
  | zero => intro i hf; omega
  | succ fuel ih =>
    intro i hf o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 oldTot
      n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 newTot blockBytes remaining cuts
    unfold chooseSplitsHeuristicP.go chooseSplitsHeuristicPArray.go
    by_cases hi : i < toks.size
    · have hi' : i < toks.toArray.size := by rw [← TokenArray.size_toArray]; exact hi
      -- Every recursive call in the body steps `i → i + 1`; as functions of the
      -- remaining scalar state the two walkers agree there by the fuel IH, so a
      -- single `funext` + `rw` collapses both bodies to the identical term.
      have hstep : chooseSplitsHeuristicP.go toks minBlockBytes softMaxBlockBytes checkTokens (i + 1)
          = chooseSplitsHeuristicPArray.go toks.toArray minBlockBytes softMaxBlockBytes checkTokens (i + 1) := by
        funext p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 pT q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 qT qb qr qc
        exact ih (i + 1) (by omega) p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 pT
          q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 qT qb qr qc
      rw [dif_pos hi, dif_pos hi', TokenArray.get_toArray toks i hi, hstep]
    · have hi' : ¬ i < toks.toArray.size := by rw [← TokenArray.size_toArray]; exact hi
      rw [dif_neg hi, dif_neg hi']

/-- **Entry-point cut-list equality.** The packed split heuristic returns exactly
    the cut list the `Array UInt32` reference produces over the boxed view — the
    control-flow decision (which token boundaries become block cuts) is proven
    unchanged by the `TokenArray` retype, not merely corpus-tested. -/
theorem chooseSplitsHeuristicP_toArray (toks : TokenArray) (totalBytes : Nat)
    (minBlockBytes softMaxBlockBytes checkTokens : Nat) :
    chooseSplitsHeuristicP toks totalBytes minBlockBytes softMaxBlockBytes checkTokens
      = chooseSplitsHeuristicPArray toks.toArray totalBytes minBlockBytes softMaxBlockBytes checkTokens := by
  unfold chooseSplitsHeuristicP chooseSplitsHeuristicPArray
  by_cases hsmall : totalBytes < 2 * minBlockBytes
  · simp only [hsmall, if_true]
  · simp only [hsmall, if_false]
    rw [chooseSplitsHeuristicP.go_toArray toks minBlockBytes softMaxBlockBytes checkTokens
      (toks.size + 1) 0 (by omega)]

/-! ## USize-native split walker

The reference walker above deliberately stays in `Nat` so its `TokenArray`
refinement proof is nearly definitional.  Its generated code nevertheless
pays several costs per token: recomputing `TokenArray.size`, rechecking the
backing byte array's addressability in `TokenArray.get`, converting the index
for the wide load, and updating boxed `Nat` loop state.  At each 512-token
divergence check it also materializes two ten-element arrays only so
`splitEndBlockCheck` can read their scalar values back.

The scalar native-word walker below hoists the addressability checks once,
walks the token bytes and all accumulators in `USize`, and evaluates the
divergence expression directly from scalar arguments. The packed-counter
production walker later in this section refines this scalar bridge, which is
retained as its fallback and proof reference. -/

@[inline] def splitAbsDiffN (a b : Nat) : Nat :=
  if a ≥ b then a - b else b - a

/-- Scalar `Nat` form of `splitEndBlockCheck`; unlike the reference helper it
    does not allocate two ten-element arrays. -/
@[inline] def splitEndBlockCheckN
    (o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 oldTot : Nat)
    (n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 newTot : Nat)
    (blockBytes : Nat) : Bool :=
  let delta :=
    splitAbsDiffN (n0 * oldTot) (o0 * newTot) +
    splitAbsDiffN (n1 * oldTot) (o1 * newTot) +
    splitAbsDiffN (n2 * oldTot) (o2 * newTot) +
    splitAbsDiffN (n3 * oldTot) (o3 * newTot) +
    splitAbsDiffN (n4 * oldTot) (o4 * newTot) +
    splitAbsDiffN (n5 * oldTot) (o5 * newTot) +
    splitAbsDiffN (n6 * oldTot) (o6 * newTot) +
    splitAbsDiffN (n7 * oldTot) (o7 * newTot) +
    splitAbsDiffN (n8 * oldTot) (o8 * newTot) +
    splitAbsDiffN (n9 * oldTot) (o9 * newTot)
  let cutoff := newTot * splitCutoffNum / splitCutoffDen * oldTot
  delta + (blockBytes / splitBiasBytes) * oldTot ≥ cutoff

/-- Scalar, native-word twin of `splitEndBlockCheck` for the production split
    constants.  Under the walker's block/check bounds all intermediates fit
    even a 32-bit `USize`; unlike the reference it allocates no counter arrays. -/
@[inline] def splitEndBlockCheckU
    (o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 oldTot : USize)
    (n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 newTot : USize)
    (blockBytes : USize) : Bool :=
  splitEndBlockCheckN
    o0.toNat o1.toNat o2.toNat o3.toNat o4.toNat o5.toNat o6.toNat o7.toNat o8.toNat o9.toNat
    oldTot.toNat
    n0.toNat n1.toNat n2.toNat n3.toNat n4.toNat n5.toNat n6.toNat n7.toNat n8.toNat n9.toNat
    newTot.toNat blockBytes.toNat

@[inline] def splitTokenClassPU (w : UInt32) : USize :=
  if w &&& ((1 : UInt32) <<< 31) = 0 then
    (((w >>> 5) &&& 6) ||| (w &&& 1)).toUSize
  else
    if ((w >>> 16) &&& 0x7FFF) ≥ 9 then 9 else 8

@[inline] def splitTokenBytesPU (w : UInt32) : USize :=
  if w &&& ((1 : UInt32) <<< 31) = 0 then 1
  else ((w >>> 16) &&& 0x7FFF).toUSize

/-- Native-word counter update corresponding to `splitBumpN`. -/
@[inline] def splitBumpU (c : USize)
    (n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 : USize) :
    USize × USize × USize × USize × USize × USize × USize × USize × USize × USize :=
  if c == 0 then (n0 + 1, n1, n2, n3, n4, n5, n6, n7, n8, n9)
  else if c == 1 then (n0, n1 + 1, n2, n3, n4, n5, n6, n7, n8, n9)
  else if c == 2 then (n0, n1, n2 + 1, n3, n4, n5, n6, n7, n8, n9)
  else if c == 3 then (n0, n1, n2, n3 + 1, n4, n5, n6, n7, n8, n9)
  else if c == 4 then (n0, n1, n2, n3, n4 + 1, n5, n6, n7, n8, n9)
  else if c == 5 then (n0, n1, n2, n3, n4, n5 + 1, n6, n7, n8, n9)
  else if c == 6 then (n0, n1, n2, n3, n4, n5, n6 + 1, n7, n8, n9)
  else if c == 7 then (n0, n1, n2, n3, n4, n5, n6, n7 + 1, n8, n9)
  else if c == 8 then (n0, n1, n2, n3, n4, n5, n6, n7, n8 + 1, n9)
  else (n0, n1, n2, n3, n4, n5, n6, n7, n8, n9 + 1)

set_option maxHeartbeats 10000000 in
/-- Fully native-word implementation of the default split policy.  The token
    end and byte-addressability witness are loop invariants, so each iteration
    is one direct `ugetUInt32LE` plus scalar arithmetic. -/
def chooseSplitsHeuristicPU.go (toks : TokenArray) (endU : USize)
    (hend : endU.toNat = toks.size) (hbytes : toks.bytes.size < USize.size)
    (checkTokens i : USize)
    (o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 oldTot : USize)
    (n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 newTot : USize)
    (blockBytes remaining : USize) (cuts : Array Nat) : Array Nat :=
  if hi : i < endU then
    have hiNat : i.toNat < toks.size := by
      rw [← hend]
      exact USize.lt_iff_toNat_lt.mp hi
    have hbytesMul : toks.bytes.size = 4 * (toks.bytes.size / 4) := by
      have hm := Nat.mod_add_div toks.bytes.size 4
      rw [toks.aligned] at hm
      omega
    have hoff : ((4 : USize) * i).toNat = 4 * i.toNat := by
      rw [USize.toNat_mul]
      have h4 : (4 : USize).toNat = 4 := by
        exact USize.toNat_ofNat_of_lt
          (Nat.lt_of_lt_of_le (show 4 < 2 ^ 32 by omega) USize.le_size)
      rw [h4]
      apply Nat.mod_eq_of_lt
      have hUS : USize.size = 2 ^ System.Platform.numBits := rfl
      rw [← hUS]
      simp only [TokenArray.size] at hiNat
      rw [hbytesMul] at hbytes
      omega
    let t := toks.bytes.ugetUInt32LE ((4 : USize) * i) (by
      rw [hoff]
      simp only [TokenArray.size] at hiNat
      rw [hbytesMul]
      omega)
    let c := splitTokenClassPU t
    let tb := splitTokenBytesPU t
    let (n0, n1, n2, n3, n4, n5, n6, n7, n8, n9) :=
      splitBumpU c n0 n1 n2 n3 n4 n5 n6 n7 n8 n9
    let newTot := newTot + 1
    let blockBytes := blockBytes + tb
    -- `Nat.sub` in the reference saturates.  Production streams never
    -- underflow (`totalBytes = data.size`), but retain the same behavior here.
    let remaining := if tb ≤ remaining then remaining - tb else 0
    have hstep : (i + 1).toNat = i.toNat + 1 := by
      rw [USize.toNat_add, USize.toNat_one]
      apply Nat.mod_eq_of_lt
      have hiEnd : i.toNat < endU.toNat := USize.lt_iff_toNat_lt.mp hi
      have hEnd := USize.toNat_lt_two_pow_numBits endU
      omega
    if remaining < splitMinBlockBytes.toUSize then cuts
    else if blockBytes ≥ splitMinBlockBytes.toUSize then
      let cut :=
        blockBytes ≥ splitSoftMaxBlockBytes.toUSize ||
        (newTot ≥ checkTokens && oldTot > 0 &&
          splitEndBlockCheckU
            o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 oldTot
            n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 newTot blockBytes)
      if cut then
        chooseSplitsHeuristicPU.go toks endU hend hbytes checkTokens (i + 1)
          0 0 0 0 0 0 0 0 0 0 0
          0 0 0 0 0 0 0 0 0 0 0
          0 remaining (cuts.push (i + 1).toNat)
      else if newTot ≥ checkTokens then
        chooseSplitsHeuristicPU.go toks endU hend hbytes checkTokens (i + 1)
          (o0 + n0) (o1 + n1) (o2 + n2) (o3 + n3) (o4 + n4)
          (o5 + n5) (o6 + n6) (o7 + n7) (o8 + n8) (o9 + n9)
          (oldTot + newTot)
          0 0 0 0 0 0 0 0 0 0 0
          blockBytes remaining cuts
      else
        chooseSplitsHeuristicPU.go toks endU hend hbytes checkTokens (i + 1)
          o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 oldTot
          n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 newTot
          blockBytes remaining cuts
    else
      chooseSplitsHeuristicPU.go toks endU hend hbytes checkTokens (i + 1)
        o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 oldTot
        n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 newTot
        blockBytes remaining cuts
  else cuts
termination_by endU.toNat - i.toNat
decreasing_by all_goals rw [hstep]; omega

/-- Guarded entry for the scalar native-word split walker. This is the direct
    production route for small L5 and the fallback/proof bridge for the packed
    counter entry below. -/
@[inline] def chooseSplitsHeuristicPU (toks : TokenArray) (totalBytes : Nat)
    (checkTokens : Nat := splitCheckTokens) : List Nat :=
  if totalBytes < 2 * splitMinBlockBytes then []
  else
    if hg : toks.bytes.size.toUSize.toNat = toks.bytes.size ∧
        toks.size.toUSize.toNat = toks.size ∧
        totalBytes.toUSize.toNat = totalBytes ∧
        checkTokens.toUSize.toNat = checkTokens then
      have hbytes : toks.bytes.size < USize.size := by
        rw [← hg.1]
        exact USize.toNat_lt_two_pow_numBits _
      (chooseSplitsHeuristicPU.go toks toks.size.toUSize hg.2.1 hbytes
        checkTokens.toUSize 0
        0 0 0 0 0 0 0 0 0 0 0
        0 0 0 0 0 0 0 0 0 0 0
        0 totalBytes.toUSize #[]).toList
    else chooseSplitsHeuristicP toks totalBytes splitMinBlockBytes
      splitSoftMaxBlockBytes checkTokens

/-- Extract one 15-bit recent-window counter from a packed `UInt64`. -/
@[inline] def splitField15 (w shift : UInt64) : UInt64 :=
  (w >>> shift) &&& 0x7FFF

/-- Extract one 20-bit block-so-far counter from a packed `UInt64`. -/
@[inline] def splitField20 (w shift : UInt64) : UInt64 :=
  (w >>> shift) &&& 0xFFFFF

/-- Decode the ten 15-bit recent-window counters. -/
@[inline] def splitUnpack15 (a b c : UInt64) :
    USize × USize × USize × USize × USize × USize × USize × USize × USize × USize :=
  ((splitField15 a 0).toUSize, (splitField15 a 15).toUSize,
    (splitField15 a 30).toUSize, (splitField15 a 45).toUSize,
    (splitField15 b 0).toUSize, (splitField15 b 15).toUSize,
    (splitField15 b 30).toUSize, (splitField15 b 45).toUSize,
    (splitField15 c 0).toUSize, (splitField15 c 15).toUSize)

/-- Decode the ten 20-bit block-so-far counters. -/
@[inline] def splitUnpack20 (a b c d : UInt64) :
    USize × USize × USize × USize × USize × USize × USize × USize × USize × USize :=
  ((splitField20 a 0).toUSize, (splitField20 a 20).toUSize,
    (splitField20 a 40).toUSize, (splitField20 b 0).toUSize,
    (splitField20 b 20).toUSize, (splitField20 b 40).toUSize,
    (splitField20 c 0).toUSize, (splitField20 c 20).toUSize,
    (splitField20 c 40).toUSize, (splitField20 d 0).toUSize)

/-- Increment one packed 15-bit recent-window counter. -/
@[inline] def splitBumpPacked15 (cls a b c : UInt64) : UInt64 × UInt64 × UInt64 :=
  if cls < 4 then (a + ((1 : UInt64) <<< (cls * 15)), b, c)
  else if cls < 8 then (a, b + ((1 : UInt64) <<< ((cls - 4) * 15)), c)
  else (a, b, c + ((1 : UInt64) <<< ((cls - 8) * 15)))

/-- Merge packed 15-bit recent counters into packed 20-bit block counters. -/
@[inline] def splitMergePacked20 (oA oB oC oD nA nB nC : UInt64) :
    UInt64 × UInt64 × UInt64 × UInt64 :=
  let q0 := splitField15 nA 0
  let q1 := splitField15 nA 15
  let q2 := splitField15 nA 30
  let q3 := splitField15 nA 45
  let q4 := splitField15 nB 0
  let q5 := splitField15 nB 15
  let q6 := splitField15 nB 30
  let q7 := splitField15 nB 45
  let q8 := splitField15 nC 0
  let q9 := splitField15 nC 15
  (oA + q0 + (q1 <<< 20) + (q2 <<< 40),
    oB + q3 + (q4 <<< 20) + (q5 <<< 40),
    oC + q6 + (q7 <<< 20) + (q8 <<< 40),
    oD + q9)

/-- Packed-counter twin of `splitEndBlockCheckU`. Recent counters are grouped
    4+4+2 in 15-bit fields; block-so-far counters are grouped 3+3+3+1 in
    20-bit fields. -/
@[inline] def splitEndBlockCheckPackedU
    (oA oB oC oD : UInt64) (oldTot : USize)
    (nA nB nC : UInt64) (newTot blockBytes : USize) : Bool :=
  let (o0, o1, o2, o3, o4, o5, o6, o7, o8, o9) := splitUnpack20 oA oB oC oD
  let (n0, n1, n2, n3, n4, n5, n6, n7, n8, n9) := splitUnpack15 nA nB nC
  splitEndBlockCheckU
    o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 oldTot
    n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 newTot blockBytes

set_option maxHeartbeats 2000000 in
/-- Compact native split walker. The 20 observation counters occupy seven
    `UInt64` words, reducing loop-carried register pressure and replacing the
    per-token class branch chain with two range checks and one variable shift.
    This loop requires every token to contribute at least one output byte and
    `0 < checkTokens ≤ 32767`. Under those preconditions each recent field is
    below 32767 before increment, while merged old fields stay below the
    300K-byte forced-cut ceiling. The production `lzMatchP` call satisfies the
    token precondition; `chooseSplitsHeuristicPUPacked_lzMatchP_eq` proves the
    resulting cuts equal the reference walker. -/
def chooseSplitsHeuristicPUPacked.go (toks : TokenArray) (endU : USize)
    (hend : endU.toNat = toks.size) (hbytes : toks.bytes.size < USize.size)
    (checkTokens i : USize)
    (oA oB oC oD : UInt64) (oldTot : USize)
    (nA nB nC : UInt64) (newTot blockBytes remaining : USize)
    (cuts : Array Nat) : Array Nat :=
  if hi : i < endU then
    have hiNat : i.toNat < toks.size := by
      rw [← hend]
      exact USize.lt_iff_toNat_lt.mp hi
    have hbytesMul : toks.bytes.size = 4 * (toks.bytes.size / 4) := by
      have hm := Nat.mod_add_div toks.bytes.size 4
      rw [toks.aligned] at hm
      omega
    have hoff : ((4 : USize) * i).toNat = 4 * i.toNat := by
      rw [USize.toNat_mul]
      have h4 : (4 : USize).toNat = 4 := by
        exact USize.toNat_ofNat_of_lt
          (Nat.lt_of_lt_of_le (show 4 < 2 ^ 32 by omega) USize.le_size)
      rw [h4]
      apply Nat.mod_eq_of_lt
      have hUS : USize.size = 2 ^ System.Platform.numBits := rfl
      rw [← hUS]
      simp only [TokenArray.size] at hiNat
      rw [hbytesMul] at hbytes
      omega
    let t := toks.bytes.ugetUInt32LE ((4 : USize) * i) (by
      rw [hoff]
      simp only [TokenArray.size] at hiNat
      rw [hbytesMul]
      omega)
    let isLit := t &&& ((1 : UInt32) <<< 31) = 0
    let tb : USize :=
      if isLit then 1 else ((t >>> 16) &&& 0x7FFF).toUSize
    let c : UInt64 :=
      if isLit then (((t >>> 5) &&& 6) ||| (t &&& 1)).toUInt64
      else if ((t >>> 16) &&& 0x7FFF) ≥ 9 then 9 else 8
    let (nA, nB, nC) := splitBumpPacked15 c nA nB nC
    let newTot := newTot + 1
    let blockBytes := blockBytes + tb
    let remaining := if tb ≤ remaining then remaining - tb else 0
    have hstep : (i + 1).toNat = i.toNat + 1 := by
      rw [USize.toNat_add, USize.toNat_one]
      apply Nat.mod_eq_of_lt
      have hiEnd : i.toNat < endU.toNat := USize.lt_iff_toNat_lt.mp hi
      have hEnd := USize.toNat_lt_two_pow_numBits endU
      omega
    if remaining < splitMinBlockBytes.toUSize then cuts
    else if blockBytes ≥ splitMinBlockBytes.toUSize then
      let cut :=
        blockBytes ≥ splitSoftMaxBlockBytes.toUSize ||
        (newTot ≥ checkTokens && oldTot > 0 &&
          splitEndBlockCheckPackedU oA oB oC oD oldTot nA nB nC newTot blockBytes)
      if cut then
        chooseSplitsHeuristicPUPacked.go toks endU hend hbytes checkTokens (i + 1)
          0 0 0 0 0 0 0 0 0 0 remaining (cuts.push (i + 1).toNat)
      else if newTot ≥ checkTokens then
        let (oA, oB, oC, oD) := splitMergePacked20 oA oB oC oD nA nB nC
        chooseSplitsHeuristicPUPacked.go toks endU hend hbytes checkTokens (i + 1)
          oA oB oC oD (oldTot + newTot)
          0 0 0 0 blockBytes remaining cuts
      else
        chooseSplitsHeuristicPUPacked.go toks endU hend hbytes checkTokens (i + 1)
          oA oB oC oD oldTot nA nB nC newTot blockBytes remaining cuts
    else
      chooseSplitsHeuristicPUPacked.go toks endU hend hbytes checkTokens (i + 1)
        oA oB oC oD oldTot nA nB nC newTot blockBytes remaining cuts
  else cuts
termination_by endU.toNat - i.toNat
decreasing_by all_goals rw [hstep]; omega

/-- Internal packed-counter entry for positive-length token streams. The
    positivity precondition is semantic and deliberately not rescanned here;
    cadence and native-word representability are checked, with the scalar
    walker used outside those bounds. Generic `TokenArray` callers should use
    `chooseSplitsHeuristicPU`; production calls this only on `lzMatchP`. -/
@[noinline] def chooseSplitsHeuristicPUPacked (toks : TokenArray)
    (totalBytes : Nat) (checkTokens : Nat := splitCheckTokens) : List Nat :=
  if totalBytes < 2 * splitMinBlockBytes then
    []
  else if hc : 0 < checkTokens ∧ checkTokens ≤ 32767 then
    if hg : toks.bytes.size.toUSize.toNat = toks.bytes.size ∧
        toks.size.toUSize.toNat = toks.size ∧
        totalBytes.toUSize.toNat = totalBytes ∧
        checkTokens.toUSize.toNat = checkTokens then
      have hbytes : toks.bytes.size < USize.size := by
        rw [← hg.1]
        exact USize.toNat_lt_two_pow_numBits _
      (chooseSplitsHeuristicPUPacked.go toks toks.size.toUSize hg.2.1 hbytes
        checkTokens.toUSize 0
        0 0 0 0 0 0 0 0 0 0 totalBytes.toUSize #[]).toList
    else chooseSplitsHeuristicPU toks totalBytes checkTokens
  else chooseSplitsHeuristicPU toks totalBytes checkTokens

/-- Packed twin of `emitDynBlock`: one dynamic Huffman block from a packed
    token group onto a running writer, with `emitTokensWithCodesP` in place of
    `emitTokensWithCodes`. Equal to `emitDynBlock` over the boxed view
    (`emitDynBlockP_eq` in `Zip/Spec/LZ77PackedCorrect.lean`). -/
def emitDynBlockP (bw : BitWriter) (data : ByteArray) (ptoks : TokenArray)
    (litLens distLens : List Nat)
    (hlit : litLens.length = 286) (hdist : distLens.length = 30)
    (isFinal : Bool) : BitWriter :=
  let litCodes := canonicalCodes (litLens.toArray.map Nat.toUInt8)
  let distCodes := canonicalCodes (distLens.toArray.map Nat.toUInt8)
  let bw := bw.writeBits 1 (if isFinal then 1 else 0)  -- BFINAL (1 bit)
  let bw := bw.writeBits 2 2                            -- BTYPE = 10 (dynamic)
  let bw := writeDynamicHeader bw litLens distLens
  have hlit_size : litCodes.size ≥ 286 := by
    show (canonicalCodes (litLens.toArray.map Nat.toUInt8)).size ≥ 286
    rw [canonicalCodes_size, Array.size_map, List.size_toArray]; omega
  have hdist_size : distCodes.size ≥ 30 := by
    show (canonicalCodes (distLens.toArray.map Nat.toUInt8)).size ≥ 30
    rw [canonicalCodes_size, Array.size_map, List.size_toArray]; omega
  have h256 : 256 < litCodes.size := by
    show 256 < (canonicalCodes (litLens.toArray.map Nat.toUInt8)).size
    rw [canonicalCodes_size, Array.size_map, List.size_toArray]; omega
  have hlitT_size : (packCodeTab litCodes).size ≥ 286 := by
    rw [packCodeTab_size]; exact hlit_size
  have hdistT_size : (packCodeTab distCodes).size ≥ 30 := by
    rw [packCodeTab_size]; exact hdist_size
  let bw := if data.size == 0 then bw
            else emitTokensWithCodesTAPT bw ptoks (packCodeTab litCodes) (packCodeTab distCodes)
              hlitT_size hdistT_size 0
  let (code, len) := litCodes[256]'h256
  bw.writeHuffCode code len

/-- Packed twin of `emitSharedBlock`: the group's frequencies come from
    `tokenFreqsP` (dense packed tables) and the emit from `emitDynBlockP`. -/
def emitSharedBlockP (bw : BitWriter) (data : ByteArray) (group : TokenArray)
    (isFinal : Bool) : BitWriter :=
  let f := tokenFreqsPTA group
  let lens := dynamicCodeLengths f.1 f.2
  emitDynBlockP bw data group lens.1 lens.2
    (dynamicCodeLengths_length f.1 f.2).1 (dynamicCodeLengths_length f.1 f.2).2 isFinal

/-- Packed twin of `emitSharedBlocksAt`: emit shared-window blocks at explicit
    cut points directly from the packed token stream. Same clamping — every cut
    is forced into `(pos, toks.size]`, so **any** cuts list yields a valid total
    partition and the boundary heuristic stays proof-free. The clamping makes
    arbitrary cuts correctness-safe, not performance-safe: a pathological list
    (non-monotone, dense) degrades to one-token blocks, each paying a full tree
    header. `deflateRaw` feeds it the scalar native-word walker's cuts on small
    L5, or the packed-counter walker's cuts on large L5 and L6–L8; both are
    proved equal to the reference `chooseSplitsHeuristicP` cuts on the
    production token stream. -/
def emitSharedBlocksAtP (data : ByteArray) (toks : TokenArray) (cuts : List Nat)
    (pos : Nat) (bw : BitWriter) : BitWriter :=
  let j := min (max (cuts.headD toks.size) (pos + 1)) toks.size
  let bw := emitSharedBlockP bw data (toks.extract pos j) (decide (j ≥ toks.size))
  if j ≥ toks.size then bw
  else emitSharedBlocksAtP data toks cuts.tail j bw
termination_by toks.size - pos
decreasing_by
  rename_i h
  simp only [Nat.not_le] at h
  omega

/-- The packed observation-divergence shared-window split candidate: emit the
    packed token stream as shared-window dynamic blocks at the given cut points
    (in `deflateRaw`, scalar-native small-L5 or packed-counter large-L5/L6–L8
    boundaries, both proved equal to `chooseSplitsHeuristicP`). Byte-identical to
    the boxed reference
    `deflateDynamicBlocksSharedAtTokens data (toks.map unpackTok) (fun _ => cuts)`
    (`deflateDynamicBlocksSharedAtP_eq`), through which the roundtrip and padding
    theorems transfer for **any** cut list. -/
def deflateDynamicBlocksSharedAtP (data : ByteArray) (toks : TokenArray)
    (cuts : List Nat) : ByteArray :=
  if data.size == 0 then
    let f := tokenFreqs #[]
    (emitDynBlock BitWriter.empty data #[] (dynamicCodeLengths f.1 f.2).1 (dynamicCodeLengths f.1 f.2).2
      (dynamicCodeLengths_length f.1 f.2).1 (dynamicCodeLengths_length f.1 f.2).2 true).flush
  else
    (emitSharedBlocksAtP data toks cuts 0 BitWriter.empty).flush

/-- Packed twin of `sharedPartitionSized` (Wave 5, #2552): the exact unflushed
    bit size of the shared-window partition **together with** each block's sized
    trees, so the winning candidate's emission reuses them instead of rebuilding
    `tokenFreqsP` + `dynamicCodeLengths` per block. Each group's frequencies come
    from `tokenFreqsP` (dense packed tables); component 1 is the same
    `3 + header + freq·codeLen` sum the packed emitter (`emitSharedBlocksAtP`)
    flushes as `⌈bits/8⌉`, and component 2's entries are definitionally
    `dynamicCodeLengths (tokenFreqsP group)` — exactly what `emitSharedBlockP`
    would recompute (`emitSharedBlocksAtSizedP_eq`). This is what makes the
    size-arbitrated dispatch (#2753) a net win: the per-block trees are built
    **once**, during sizing, and the emit pass reuses them. -/
def sharedPartitionSizedP (toks : TokenArray) (cuts : List Nat) (pos : Nat) :
    Nat × List SizedTrees :=
  let j := min (max (cuts.headD toks.size) (pos + 1)) toks.size
  let f := tokenFreqsPTA (toks.extract pos j)
  let t := sizedTrees f.1 f.2
  let blockBits := 3 + (writeDynamicHeader BitWriter.empty t.val.1 t.val.2).bitLength
    + symbolBitCount f.1 f.2 t.val.1.toArray t.val.2.toArray
  if j ≥ toks.size then (blockBits, [t])
  else
    let rest := sharedPartitionSizedP toks cuts.tail j
    (blockBits + rest.1, t :: rest.2)
termination_by toks.size - pos
decreasing_by
  rename_i h
  simp only [Nat.not_le] at h
  omega

/-- `Array UInt32` reference walker for `sharedPartitionSizedP`: the exact
    pre-`TokenArray` body, taking each block's frequencies from
    `tokenFreqsP (toks.extract pos j)` over an `Array UInt32` slice instead of the
    packed `tokenFreqsPTA (toks.extract pos j)`. Kept purely as a proof reference:
    component 1 is the exact unflushed bit size that arbitrates the shared-window
    split candidate at levels 5–10, so `sharedPartitionSizedP_toArray` pins that
    size (and the per-block trees) to the `Array UInt32` implementation's. -/
def sharedPartitionSizedPArray (toks : Array UInt32) (cuts : List Nat) (pos : Nat) :
    Nat × List SizedTrees :=
  let j := min (max (cuts.headD toks.size) (pos + 1)) toks.size
  let f := tokenFreqsP (toks.extract pos j)
  let t := sizedTrees f.1 f.2
  let blockBits := 3 + (writeDynamicHeader BitWriter.empty t.val.1 t.val.2).bitLength
    + symbolBitCount f.1 f.2 t.val.1.toArray t.val.2.toArray
  if j ≥ toks.size then (blockBits, [t])
  else
    let rest := sharedPartitionSizedPArray toks cuts.tail j
    (blockBits + rest.1, t :: rest.2)
termination_by toks.size - pos
decreasing_by
  rename_i h
  simp only [Nat.not_le] at h
  omega

/-- Fuel form of `sharedPartitionSizedP_toArray`. -/
private theorem sharedPartitionSizedP_toArray_fuel (toks : TokenArray) :
    ∀ (fuel pos : Nat), toks.size - pos < fuel → ∀ (cuts : List Nat),
      sharedPartitionSizedP toks cuts pos = sharedPartitionSizedPArray toks.toArray cuts pos := by
  intro fuel
  induction fuel with
  | zero => intro pos hf; omega
  | succ fuel ih =>
    intro pos hf cuts
    unfold sharedPartitionSizedP sharedPartitionSizedPArray
    simp only [tokenFreqsPTA_toArray, TokenArray.extract_toArray, TokenArray.size_toArray]
    by_cases hend : min (max (cuts.headD toks.toArray.size) (pos + 1)) toks.toArray.size
        ≥ toks.toArray.size
    · rw [if_pos hend, if_pos hend]
    · rw [if_neg hend, if_neg hend,
        ih (min (max (cuts.headD toks.toArray.size) (pos + 1)) toks.toArray.size) (by
          simp only [TokenArray.size_toArray] at hf ⊢; omega) cuts.tail]

/-- **Sizing-walker refinement (byte-identity of the split size).** The packed
    `sharedPartitionSizedP` equals the `Array UInt32` reference over the `.toArray`
    view — component 1 (the exact bit size that selects the winning split
    candidate at levels 5–10) *and* component 2 (the per-block sized trees) — so
    the size decisions are proven identical to the pre-`TokenArray` implementation,
    not merely corpus-tested. Each block's `tokenFreqsPTA (toks.extract …)` read is
    bridged to `tokenFreqsP (toks.toArray.extract …)` by `tokenFreqsPTA_toArray`
    and `TokenArray.extract_toArray`; the recursion is otherwise identical. -/
theorem sharedPartitionSizedP_toArray (toks : TokenArray) (cuts : List Nat) (pos : Nat) :
    sharedPartitionSizedP toks cuts pos = sharedPartitionSizedPArray toks.toArray cuts pos :=
  sharedPartitionSizedP_toArray_fuel toks (toks.size - pos + 1) pos (by omega) cuts

/-- The split-size scalar (`.1`) the levels-5–10 arbitration compares is exactly
    the `Array UInt32` reference's. -/
theorem sharedPartitionSizedP_fst_toArray (toks : TokenArray) (cuts : List Nat) (pos : Nat) :
    (sharedPartitionSizedP toks cuts pos).1 = (sharedPartitionSizedPArray toks.toArray cuts pos).1 := by
  rw [sharedPartitionSizedP_toArray]

/-- Trees-only twin of `sharedPartitionSizedP`.

    A direct split route does not compare candidate sizes, so computing each
    block's exact bit count and folding the whole-stream frequencies is wasted
    work.  This walker retains only the per-block Huffman trees needed by
    `emitSharedBlocksAtSizedP`, with exactly the same clamped partition.  Its
    equality to `sharedPartitionSizedP`'s tree component is proved in
    `Zip.Spec.LZ77PackedCorrect`. -/
def sharedPartitionTreesP (toks : TokenArray) (cuts : List Nat) (pos : Nat) :
    List SizedTrees :=
  let j := min (max (cuts.headD toks.size) (pos + 1)) toks.size
  let f := tokenFreqsPTA (toks.extract pos j)
  let t := sizedTrees f.1 f.2
  if j ≥ toks.size then [t]
  else t :: sharedPartitionTreesP toks cuts.tail j
termination_by toks.size - pos
decreasing_by
  rename_i h
  simp only [Nat.not_le] at h
  omega

/-- Fused twin of `sharedPartitionSizedP` (#2772): one pass over the clamped
    partition yields the same `(bits, per-block trees)` **and** the whole-stream
    frequencies, accumulated as the EOB-corrected element-wise sum of the per-block
    `tokenFreqsP` (`mergeEOBFreqsP`) — the *same* histogram `sizedTrees` already
    consumes, so no extra frequency walk. Component 1 is proved equal to
    `sharedPartitionSizedP` (`sharedPartitionSizedFreqsP_fst`) and component 2 to
    `tokenFreqsP (toks.extract pos toks.size)` (`sharedPartitionSizedFreqsP_snd`),
    so the base candidate can reuse these frequencies instead of re-walking the
    whole stream (`tokenFreqsP` is 4.7% L6 dickens / 3.0% mozilla of compress). -/
def sharedPartitionSizedFreqsP (toks : TokenArray) (cuts : List Nat) (pos : Nat) :
    (Nat × List SizedTrees) × (Array Nat × Array Nat) :=
  let j := min (max (cuts.headD toks.size) (pos + 1)) toks.size
  let f := tokenFreqsPTA (toks.extract pos j)
  let t := sizedTrees f.1 f.2
  let blockBits := 3 + (writeDynamicHeader BitWriter.empty t.val.1 t.val.2).bitLength
    + symbolBitCount f.1 f.2 t.val.1.toArray t.val.2.toArray
  if j ≥ toks.size then ((blockBits, [t]), f)
  else
    let rest := sharedPartitionSizedFreqsP toks cuts.tail j
    ((blockBits + rest.1.1, t :: rest.1.2), mergeEOBFreqsP f rest.2)
termination_by toks.size - pos
decreasing_by
  rename_i h
  simp only [Nat.not_le] at h
  omega

/-- Tree-taking twin of `emitSharedBlocksAtP`: same clamped cut points, but each
    block's `(litLens, distLens)` come from the `trees` list (in lockstep with
    `cuts`) instead of being recomputed from the group via `tokenFreqsP` +
    `dynamicCodeLengths`. Byte-identical to `emitSharedBlocksAtP` when `trees` is
    `sharedPartitionSizedP`'s output (`emitSharedBlocksAtSizedP_eq`). -/
def emitSharedBlocksAtSizedP (data : ByteArray) (toks : TokenArray) (cuts : List Nat)
    (trees : List SizedTrees) (pos : Nat) (bw : BitWriter) : BitWriter :=
  let j := min (max (cuts.headD toks.size) (pos + 1)) toks.size
  let t := trees.headD emptySizedTrees
  let bw := emitDynBlockP bw data (toks.extract pos j) t.val.1 t.val.2
    t.property.1 t.property.2 (decide (j ≥ toks.size))
  if j ≥ toks.size then bw
  else emitSharedBlocksAtSizedP data toks cuts.tail trees.tail j bw
termination_by toks.size - pos
decreasing_by
  rename_i h
  simp only [Nat.not_le] at h
  omega

/-- The packed sized-tree split candidate: the flushed byte size of
    `deflateDynamicBlocksSharedAtP data toks cuts` **paired with** a thunk that
    emits it, reusing the per-block trees built during sizing (no second
    frequency/Huffman pass). The emit thunk is byte-identical to the reference
    `deflateDynamicBlocksSharedAtP` (`deflateDynamicBlocksSharedAtSizedP_emit`),
    so its roundtrip transfers for **any** cut list; component 1 equals that
    output's `.size` (`SizeHelpers` conformance). `deflateRaw` sizes every split
    candidate this way and forces only the winner's thunk. -/
def deflateDynamicBlocksSharedAtSizedP (data : ByteArray) (toks : TokenArray)
    (cuts : List Nat) : Nat × (Unit → ByteArray) :=
  if data.size == 0 then
    let out := deflateDynamicBlocksSharedAtP data toks cuts
    (out.size, fun _ => out)
  else
    let sp := sharedPartitionSizedP toks cuts 0
    ((sp.1 + 7) / 8,
      fun _ => (emitSharedBlocksAtSizedP data toks cuts sp.2 0
        (BitWriter.emptyWithCapacity ((sp.1 + 7) / 8))).flush)

/-- Emit a known-winning observation split after preparing only its per-block
    trees.  Unlike `deflateDynamicBlocksSharedAtSizedP`, this does not compute an
    exact candidate size; unlike `deflateObsSplitSizedFreqsP`, it also does not
    merge per-block histograms for a base candidate that will not be emitted.
    The emitted bytes equal `deflateDynamicBlocksSharedAtP` for every cut list
    (`deflateDynamicBlocksSharedAtTreesP_eq`). -/
def deflateDynamicBlocksSharedAtTreesP (data : ByteArray) (toks : TokenArray)
    (cuts : List Nat) : ByteArray :=
  if data.size == 0 then
    deflateDynamicBlocksSharedAtP data toks cuts
  else
    let trees := sharedPartitionTreesP toks cuts 0
    (emitSharedBlocksAtSizedP data toks cuts trees 0
      (BitWriter.emptyWithCapacity data.size)).flush

/-- The obs-split candidate prep **paired with** the whole-stream frequencies,
    both from one fused sizing pass (`sharedPartitionSizedFreqsP`, #2772).
    Component 1 is proved equal to `deflateDynamicBlocksSharedAtSizedP`
    (`deflateObsSplitSizedFreqsP_fst`), so the split candidate's roundtrip and
    byte-size conformance transfer unchanged; component 2 is `tokenFreqsP toks`
    (`deflateObsSplitSizedFreqsP_snd`), the whole-stream histogram the base
    candidate needs — derived here by folding the per-block frequencies the
    sizing pass already built, instead of a second whole-stream `tokenFreqsP`
    walk. `deflateRaw` (levels 5–8, cuts non-empty) forces this once and feeds
    component 2 to `deflateRawBasePPrepF`. -/
def deflateObsSplitSizedFreqsP (data : ByteArray) (toks : TokenArray)
    (cuts : List Nat) : (Nat × (Unit → ByteArray)) × (Array Nat × Array Nat) :=
  if data.size == 0 then
    let out := deflateDynamicBlocksSharedAtP data toks cuts
    ((out.size, fun _ => out), tokenFreqsPTA toks)
  else
    let sp := sharedPartitionSizedFreqsP toks cuts 0
    (((sp.1.1 + 7) / 8,
      fun _ => (emitSharedBlocksAtSizedP data toks cuts sp.1.2 0
        (BitWriter.emptyWithCapacity ((sp.1.1 + 7) / 8))).flush),
     sp.2)

/-- The compressed-block dispatch (no stored fallback). Every level ≥ 1 uses the
    hash-chain matcher with the level's search depth (`chainDepth`) and interior
    insertion cap (`insertCap`): low levels defer insertion + search shallowly
    (fast, lower ratio), high levels insert everything + search deeply (slower,
    best ratio). One shared token pass sizes the fixed and dynamic blocks and
    emits only the smaller (strict `<`, dynamic on a tie). -/
def deflateCompressed (data : ByteArray) (level : UInt8) : ByteArray :=
  let tokens := lzMatch data level
  let f := tokenFreqs tokens
  let lens := dynamicCodeLengths f.1 f.2
  if fixedBlockBytes f.1 f.2 < dynBlockBytes f.1 f.2 lens.1 lens.2
  then deflateFixedBlock data tokens
  -- Reuse the sized `lens` for emission (= `deflateDynamicBlock data tokens`,
  -- but without recomputing the code lengths).
  else deflateDynamicBlockCore data tokens lens.1 lens.2
    (dynamicCodeLengths_length f.1 f.2).1 (dynamicCodeLengths_length f.1 f.2).2

/-- The single-block cost-model dispatch for level ≥ 1: stored / fixed / dynamic,
    all *sized* from one shared token pass, emitting only the winner. Falls back to
    a stored block whenever that is smaller, so incompressible input never expands.
    This is the base candidate that the block-split streams are compared against. -/
def deflateRawBaseTokens (data : ByteArray) (tokens : Array LZ77Token) : ByteArray :=
  let f := tokenFreqs tokens
  let lens := dynamicCodeLengths f.1 f.2
  let fixedBytes := fixedBlockBytes f.1 f.2
  let dynBytes := dynBlockBytes f.1 f.2 lens.1 lens.2
  -- Size the stored candidate in O(⌈|data|/65535⌉) via `storedBlockBytes`
  -- (= `(deflateStoredPure data).size`, `storedBlockBytes_eq`) and *only*
  -- materialize the ~|data|-byte stored block when it actually wins — otherwise
  -- every compressible input paid to build and discard a full-size copy.
  let storedBytes := storedBlockBytes data
  if storedBytes < (if fixedBytes < dynBytes then fixedBytes else dynBytes) then deflateStoredPure data
  else if fixedBytes < dynBytes then deflateFixedBlock data tokens
  else deflateDynamicBlockCore data tokens lens.1 lens.2
    (dynamicCodeLengths_length f.1 f.2).1 (dynamicCodeLengths_length f.1 f.2).2

/-- `deflateRawBaseTokens` over a *packed* token stream (Wave 3b stages B+C):
    the frequency pass runs natively on the packed words (`tokenFreqsP`), and
    the emit branches consume the packed words directly
    (`deflateFixedBlockP`/`deflateDynamicBlockCoreP`) — no branch ever
    materializes boxed tokens. Equal to
    `deflateRawBaseTokens data (ptokens.map unpackTok)` via `tokenFreqsP_eq`
    and the packed-emitter equalities (`Zip/Spec/EmitPackedCorrect.lean`);
    `deflateRawBaseTokens` stays as the boxed reference implementation
    (conformance-tested in `ZipTest/PackedTokens.lean`).

    The dynamic-tree header plan (`dynHeaderCodes`) is built **once** and reused
    for both sizing (`dynBlockBytesWith`) and emit (`deflateDynamicBlockCorePWithFlat`)
    rather than rebuilt in each — the #2627 dedup; equal to the un-deduped form by
    `dynBlockBytesWith_dynHeaderCodes` /
    `deflateDynamicBlockCorePWithFlat_dynHeaderCodes`
    (used in `deflateRawBase_def`). -/
def deflateRawBaseP (data : ByteArray) (ptokens : TokenArray) : ByteArray :=
  let f := tokenFreqsPTA ptokens
  let lens := dynamicCodeLengths f.1 f.2
  let plan := dynHeaderCodes lens.1 lens.2
  have hcl : plan.clCodes.size ≥ 19 :=
    Nat.le_of_eq (dynHeaderCodes_clCodes_size lens.1 lens.2).symm
  let fixedBytes := fixedBlockBytes f.1 f.2
  let dynBytes := dynBlockBytesWith f.1 f.2 lens.1 lens.2 plan hcl
  let storedBytes := storedBlockBytes data
  if storedBytes < (if fixedBytes < dynBytes then fixedBytes else dynBytes) then deflateStoredPure data
  else if fixedBytes < dynBytes then deflateFixedBlockP data ptokens fixedBytes
  else deflateDynamicBlockCorePWithFlat data ptokens lens.1 lens.2 plan hcl
    (dynamicCodeLengths_length f.1 f.2).1 (dynamicCodeLengths_length f.1 f.2).2
    (dynamicCodeLengths_bounded f.1 f.2).1 (dynamicCodeLengths_bounded f.1 f.2).2 dynBytes

/-- `deflateRawBaseP` with the whole-stream frequencies supplied as a parameter
    instead of recomputed via `tokenFreqsP ptokens` — the emit twin of
    `deflateRawBasePPrepF`. Used by `deflateRawBaseF` to consume the frequencies
    the fused matcher already produced. At `f = tokenFreqsP ptokens` this is
    definitionally `deflateRawBaseP` (`deflateRawBasePF_tokenFreqsP`). -/
def deflateRawBasePF (data : ByteArray) (ptokens : TokenArray)
    (f : Array Nat × Array Nat) : ByteArray :=
  let lens := dynamicCodeLengths f.1 f.2
  let plan := dynHeaderCodes lens.1 lens.2
  have hcl : plan.clCodes.size ≥ 19 :=
    Nat.le_of_eq (dynHeaderCodes_clCodes_size lens.1 lens.2).symm
  let fixedBytes := fixedBlockBytes f.1 f.2
  let dynBytes := dynBlockBytesWith f.1 f.2 lens.1 lens.2 plan hcl
  let storedBytes := storedBlockBytes data
  if storedBytes < (if fixedBytes < dynBytes then fixedBytes else dynBytes) then deflateStoredPure data
  else if fixedBytes < dynBytes then deflateFixedBlockP data ptokens fixedBytes
  else deflateDynamicBlockCorePWithFlatF data ptokens lens.1 lens.2 plan hcl
    (dynamicCodeLengths_length f.1 f.2).1 (dynamicCodeLengths_length f.1 f.2).2
    (dynamicCodeLengths_bounded f.1 f.2).1 (dynamicCodeLengths_bounded f.1 f.2).2 dynBytes

/-- `deflateRawBasePF` at the whole-stream frequencies is `deflateRawBaseP`. -/
theorem deflateRawBasePF_tokenFreqsP (data : ByteArray) (ptokens : TokenArray) :
    deflateRawBasePF data ptokens (tokenFreqsPTA ptokens) = deflateRawBaseP data ptokens :=
  rfl

/-- The base candidate *sized and prepared* from one shared token pass: the
    winner's flushed byte size (the same stored / fixed / dynamic comparison
    `deflateRawBaseP` makes internally) **paired with** a thunk that emits it. The
    frequencies, code lengths, and dynamic-tree plan are computed once and shared
    between the size and the emit — so when the base wins, forcing the thunk pays
    no second sizing pass. The thunk is definitionally `deflateRawBaseP data
    ptokens` (`deflateRawBasePPrep_emit`) and component 1 equals its `.size`
    (`SizeHelpers` conformance), so byte-identity to the emit-then-`pickSmaller`
    dispatch is preserved. -/
def deflateRawBasePPrep (data : ByteArray) (ptokens : TokenArray) : Nat × (Unit → ByteArray) :=
  let f := tokenFreqsPTA ptokens
  let lens := dynamicCodeLengths f.1 f.2
  let plan := dynHeaderCodes lens.1 lens.2
  have hcl : plan.clCodes.size ≥ 19 :=
    Nat.le_of_eq (dynHeaderCodes_clCodes_size lens.1 lens.2).symm
  let fixedBytes := fixedBlockBytes f.1 f.2
  let dynBytes := dynBlockBytesWith f.1 f.2 lens.1 lens.2 plan hcl
  let storedBytes := storedBlockBytes data
  ((if storedBytes < (if fixedBytes < dynBytes then fixedBytes else dynBytes) then storedBytes
    else if fixedBytes < dynBytes then fixedBytes else dynBytes),
   fun _ =>
    if storedBytes < (if fixedBytes < dynBytes then fixedBytes else dynBytes) then deflateStoredPure data
    else if fixedBytes < dynBytes then deflateFixedBlockP data ptokens fixedBytes
    else deflateDynamicBlockCorePWithFlat data ptokens lens.1 lens.2 plan hcl
      (dynamicCodeLengths_length f.1 f.2).1 (dynamicCodeLengths_length f.1 f.2).2
      (dynamicCodeLengths_bounded f.1 f.2).1 (dynamicCodeLengths_bounded f.1 f.2).2 dynBytes)

/-- The prep's emit thunk is exactly `deflateRawBaseP` (same shared plan). -/
theorem deflateRawBasePPrep_emit (data : ByteArray) (ptokens : TokenArray) :
    (deflateRawBasePPrep data ptokens).2 () = deflateRawBaseP data ptokens := rfl

/-- `Array UInt32` reference for the *size* (`.1`) of `deflateRawBasePPrep`: the
    exact stored / fixed / dynamic winner size the base candidate compares against
    the split candidate at levels 5–10, computed from `tokenFreqsP ptokens` over an
    `Array UInt32` slot instead of the packed `tokenFreqsPTA ptokens`. Kept as a
    proof reference so `deflateRawBasePPrep_fst_toArray` pins that winner size to
    the pre-`TokenArray` implementation's. (Only the size is reconstructed here:
    the emit thunk `.2` consumes the packed `ptokens` directly and stays on the
    `TokenArray` fast path, its byte-identity carried by `deflateRawBasePPrep_emit`
    plus the packed-emitter equalities.) -/
def deflateRawBasePPrepSizeArray (data : ByteArray) (ptokens : Array UInt32) : Nat :=
  let f := tokenFreqsP ptokens
  let lens := dynamicCodeLengths f.1 f.2
  let plan := dynHeaderCodes lens.1 lens.2
  have hcl : plan.clCodes.size ≥ 19 :=
    Nat.le_of_eq (dynHeaderCodes_clCodes_size lens.1 lens.2).symm
  let fixedBytes := fixedBlockBytes f.1 f.2
  let dynBytes := dynBlockBytesWith f.1 f.2 lens.1 lens.2 plan hcl
  let storedBytes := storedBlockBytes data
  if storedBytes < (if fixedBytes < dynBytes then fixedBytes else dynBytes) then storedBytes
  else if fixedBytes < dynBytes then fixedBytes else dynBytes

/-- **Base-prep size refinement (byte-identity of the base-candidate size).** The
    scalar `.1` that arbitrates the base candidate at levels 5–10 equals the
    `Array UInt32` reference's over the `.toArray` view: the whole-stream
    `tokenFreqsPTA ptokens` read is bridged to `tokenFreqsP ptokens.toArray` by
    `tokenFreqsPTA_toArray`, and every downstream sizing function is already the
    pure `Array`/`Nat` implementation, so the winner size is proven identical to
    the pre-`TokenArray` code — not merely corpus-tested. (Composed with
    `deflateRawBasePPrepF_tokenFreqsP`, the frequency-taking prep's size is pinned
    too, since at `tokenFreqsPTA ptokens` it is definitionally `deflateRawBasePPrep`.) -/
theorem deflateRawBasePPrep_fst_toArray (data : ByteArray) (ptokens : TokenArray) :
    (deflateRawBasePPrep data ptokens).1 = deflateRawBasePPrepSizeArray data ptokens.toArray := by
  simp only [deflateRawBasePPrep, deflateRawBasePPrepSizeArray, tokenFreqsPTA_toArray]

/-- `deflateRawBasePPrep` with the whole-stream frequencies supplied as a
    parameter instead of recomputed via `tokenFreqsP ptokens` (#2772). When the
    levels-5–8 split has cuts, `deflateRaw` passes the frequencies the split-sizing
    pass already summed (`deflateObsSplitSizedFreqsP`'s component 2, provably
    `tokenFreqsP ptokens`), so the base candidate skips the second whole-stream
    frequency walk. At `f = tokenFreqsP ptokens` this is definitionally
    `deflateRawBasePPrep` (`deflateRawBasePPrepF_tokenFreqsP`), keeping the emit
    theorem clean. Only the frequency-derived sizing/tree work uses `f`; the emit
    branches consume `ptokens` directly, exactly as `deflateRawBasePPrep`. -/
def deflateRawBasePPrepF (data : ByteArray) (ptokens : TokenArray)
    (f : Array Nat × Array Nat) : Nat × (Unit → ByteArray) :=
  let lens := dynamicCodeLengths f.1 f.2
  let plan := dynHeaderCodes lens.1 lens.2
  have hcl : plan.clCodes.size ≥ 19 :=
    Nat.le_of_eq (dynHeaderCodes_clCodes_size lens.1 lens.2).symm
  let fixedBytes := fixedBlockBytes f.1 f.2
  let dynBytes := dynBlockBytesWith f.1 f.2 lens.1 lens.2 plan hcl
  let storedBytes := storedBlockBytes data
  ((if storedBytes < (if fixedBytes < dynBytes then fixedBytes else dynBytes) then storedBytes
    else if fixedBytes < dynBytes then fixedBytes else dynBytes),
   fun _ =>
    if storedBytes < (if fixedBytes < dynBytes then fixedBytes else dynBytes) then deflateStoredPure data
    else if fixedBytes < dynBytes then deflateFixedBlockP data ptokens fixedBytes
    else deflateDynamicBlockCorePWithFlatF data ptokens lens.1 lens.2 plan hcl
      (dynamicCodeLengths_length f.1 f.2).1 (dynamicCodeLengths_length f.1 f.2).2
      (dynamicCodeLengths_bounded f.1 f.2).1 (dynamicCodeLengths_bounded f.1 f.2).2 dynBytes)

/-- `deflateRawBasePPrepF` at the whole-stream frequencies is `deflateRawBasePPrep`. -/
theorem deflateRawBasePPrepF_tokenFreqsP (data : ByteArray) (ptokens : TokenArray) :
    deflateRawBasePPrepF data ptokens (tokenFreqsPTA ptokens) = deflateRawBasePPrep data ptokens :=
  rfl

/-- `deflateRawBaseP` over this level's *packed* `lzMatchP` stream
    (definitional wrapper, `deflateRawBaseP_def`). Equal to the boxed
    `deflateRawBaseTokens data (lzMatch data level)` — that equation is
    `deflateRawBase_def`, proven in `Zip/Spec/LZ77PackedCorrect.lean` via
    `tokenFreqsP_eq` + `lzMatchP_map`. -/
def deflateRawBase (data : ByteArray) (level : UInt8) : ByteArray :=
  deflateRawBaseP data (lzMatchP data level)

theorem deflateRawBaseP_def (data : ByteArray) (level : UInt8) :
    deflateRawBaseP data (lzMatchP data level) = deflateRawBase data level := rfl

/-- Boxed-histogram fused base path. Level one uses the specialized native-word
    outer loop; levels two through four retain the generic fused matcher. -/
def deflateRawBaseFLevel1Impl (data : ByteArray) (level : UInt8) : ByteArray :=
  let fused :=
    if level == 1 then lz77ChainIterPMergedF1U data
    else lz77ChainIterPMergedF data (chainDepth level) 32768 (insertCap level) (niceLen level)
  let (ptokens, litF, distF) := fused
  deflateRawBasePF data ptokens (litF.val, distF.val)

/-- Proven L1 path combining the native-word specialized outer loop with one
    unboxed `ByteArray` histogram. The matcher entry owns the packing guard and
    retains the boxed specialized implementation as its exact fallback. -/
def deflateRawBaseFU64Level1 (data : ByteArray) : ByteArray :=
  let (ptokens, litF, distF) := lz77ChainIterPMergedF1U64 data
  deflateRawBasePF data ptokens (litF, distF)

/-- The guarded wide-counter L1 implementation is byte-identical to the
    established boxed-histogram fused implementation. -/
theorem deflateRawBaseFU64Level1_eq (data : ByteArray) :
    deflateRawBaseFU64Level1 data = deflateRawBaseFLevel1Impl data 1 := by
  unfold deflateRawBaseFU64Level1 deflateRawBaseFLevel1Impl
  rw [lz77ChainIterPMergedF1U64_eq]
  simp

/-- The greedy-tier (levels 1–4) base candidate computed from **one fused pass**.
    Level 1 uses the guarded wide-counter matcher; levels 2–4 use the established
    boxed fused matcher.  Both produce the packed tokens and `tokenFreqsP`
    histograms together, so base sizing/emission avoids a second token walk.
    Byte-identical to `deflateRawBase` on the greedy tier (`deflateRawBaseF_eq`). -/
def deflateRawBaseF (data : ByteArray) (level : UInt8) : ByteArray :=
  if level == 1 then deflateRawBaseFU64Level1 data
  else deflateRawBaseFLevel1Impl data level

/-- On the greedy tier (`level ≤ 4`, i.e. `¬ 5 ≤ level`) the fused base candidate
    is byte-identical to `deflateRawBase`: the fused matcher returns exactly the
    plain matcher's tokens and `tokenFreqsP` (`lz77ChainIterPMergedF_eq`), and at
    those frequencies `deflateRawBasePF` is `deflateRawBaseP`. -/
theorem deflateRawBaseF_eq (data : ByteArray) (level : UInt8) (h : ¬ (5 ≤ level)) :
    deflateRawBaseF data level = deflateRawBase data level := by
  unfold deflateRawBaseF
  by_cases hlevel : level = 1
  · subst level
    simp only [beq_self_eq_true, ↓reduceIte]
    rw [deflateRawBaseFU64Level1_eq]
    unfold deflateRawBaseFLevel1Impl
    simp only [beq_self_eq_true, ↓reduceIte]
    rw [lz77ChainIterPMergedF1U_eq]
    simp only [lz77ChainIterPMergedF_eq]
    rw [← tokenFreqsPTA_toArray]
    rw [deflateRawBasePF_tokenFreqsP]
    unfold deflateRawBase lzMatchP chainDepth insertCap niceLen
    simp only [show ¬ (5 : UInt8) ≤ 1 by decide,
      show (1 : UInt8) ≤ 1 by decide, show (1 : UInt8) ≤ 4 by decide,
      show ¬((1 : UInt8) == 7) = true by decide, Bool.false_eq_true, ↓reduceIte]
  · rw [if_neg (by simpa only [beq_iff_eq] using hlevel)]
    unfold deflateRawBaseFLevel1Impl
    rw [if_neg (by simpa only [beq_iff_eq] using hlevel)]
    simp only [lz77ChainIterPMergedF_eq]
    rw [← tokenFreqsPTA_toArray]
    rw [deflateRawBasePF_tokenFreqsP]
    unfold deflateRawBase lzMatchP
    have hlevel7 : level ≠ 7 := by
      intro heq
      subst level
      exact h (by decide)
    have h7 : ¬(level == 7) = true := by
      simpa only [beq_iff_eq] using hlevel7
    simp only [h, h7, Bool.false_eq_true, ↓reduceIte]

theorem deflateDynamicBlocksSharedAt_def (data : ByteArray)
    (choose : Array LZ77Token → List Nat) (level : UInt8) :
    deflateDynamicBlocksSharedAtTokens data (lzMatch data level) choose =
      deflateDynamicBlocksSharedAt data choose level := rfl

/-! ## Near-optimal candidate (level 9) -/

/-- Input-size gate for the near-optimal candidate. Measured (#2537, GNU
    time MaxRSS of the ungated candidate on silesia/mozilla slices): 793 MB
    peak at 16 MiB input, 1.73 GB at 52 MiB — ≈27 B of transient state per
    input byte marginal (global choice arrays + per-region cache + token
    stream) over the process baseline. 64 MiB covers every Silesia file at a
    projected ~2.1 GB peak, acceptable for the max-effort tiers (levels 9–10);
    truly huge inputs still fall back to the split path. A pure dispatch knob —
    `pickSmaller` composes either way. (The L9-fast candidate at level 9 has a
    lower peak — shallower cache, single round — so the gate is conservative
    there, but a single gate for both optimal tiers keeps the dispatch simple.) -/
def optimalMaxSize : Nat := 67108864

/-- Cross-block (shared-window) block-split dynamic compression over the
    **near-optimal** token stream: like `deflateDynamicBlocksShared`, but the
    tokens come from the cost-model DP parser (`lz77OptimalIter`) instead of
    the greedy/lazy matcher. See `Zip.Native.DeflateParse`. -/
def deflateDynamicBlocksOptimal (data : ByteArray) (tokChunk : Nat) : ByteArray :=
  if data.size == 0 then
    let f := tokenFreqs #[]
    (emitDynBlock BitWriter.empty data #[] (dynamicCodeLengths f.1 f.2).1 (dynamicCodeLengths f.1 f.2).2
      (dynamicCodeLengths_length f.1 f.2).1 (dynamicCodeLengths_length f.1 f.2).2 true).flush
  else
    (emitSharedBlocks data (lz77OptimalIter data) tokChunk 0 BitWriter.empty).flush

/-- Cross-block split over the **L9-fast** approximate-optimal token stream
    (`lz77OptimalFastIter`, #2638): identical to `deflateDynamicBlocksOptimal`
    but the cheaper single-round, bounds-free, shallow-cache parser. The tokens
    satisfy the same encoder contracts, so the roundtrip proof is the exact
    twin (`decode_deflateDynamicBlocksOptimalFast` etc.). Deployed at level 9;
    the exact crown moves to level 10. -/
def deflateDynamicBlocksOptimalFast (data : ByteArray) (tokChunk : Nat) : ByteArray :=
  if data.size == 0 then
    let f := tokenFreqs #[]
    (emitDynBlock BitWriter.empty data #[] (dynamicCodeLengths f.1 f.2).1 (dynamicCodeLengths f.1 f.2).2
      (dynamicCodeLengths_length f.1 f.2).1 (dynamicCodeLengths_length f.1 f.2).2 true).flush
  else
    (emitSharedBlocks data (lz77OptimalFastIter data) tokChunk 0 BitWriter.empty).flush

/-- Windowed twin of `deflateDynamicBlocksOptimal` (#2787): identical block
    stream, but the exact-DP tokens come from `lz77OptimalWindowedIter`, whose
    live choice storage is capped to one region — so the exact crown runs in
    bounded memory past the `optimalMaxSize` gate. -/
def deflateDynamicBlocksOptimalWindowed (data : ByteArray) (tokChunk : Nat) : ByteArray :=
  if data.size == 0 then
    let f := tokenFreqs #[]
    (emitDynBlock BitWriter.empty data #[] (dynamicCodeLengths f.1 f.2).1 (dynamicCodeLengths f.1 f.2).2
      (dynamicCodeLengths_length f.1 f.2).1 (dynamicCodeLengths_length f.1 f.2).2 true).flush
  else
    (emitSharedBlocks data (lz77OptimalWindowedIter data) tokChunk 0 BitWriter.empty).flush

/-- Windowed twin of `deflateDynamicBlocksOptimalFast` (#2787): the region-capped
    L9-fast parse (`lz77OptimalWindowedFastIter`). -/
def deflateDynamicBlocksOptimalWindowedFast (data : ByteArray) (tokChunk : Nat) : ByteArray :=
  if data.size == 0 then
    let f := tokenFreqs #[]
    (emitDynBlock BitWriter.empty data #[] (dynamicCodeLengths f.1 f.2).1 (dynamicCodeLengths f.1 f.2).2
      (dynamicCodeLengths_length f.1 f.2).1 (dynamicCodeLengths_length f.1 f.2).2 true).flush
  else
    (emitSharedBlocks data (lz77OptimalWindowedFastIter data) tokChunk 0 BitWriter.empty).flush

/-! ## Incompressible pre-scan

`deflateRaw` already falls back to a stored block whenever every compressed
candidate is larger — but it only learns this *after* paying the full hash-chain
match pass (and, at level 9, the optimal-parse DP), which is essentially the
whole compress cost and finds almost nothing on incompressible input. Measured
(`bench compress-pareto`, 4 MiB PRNG): level 9 runs at ≈2.5 MB/s, all of it
wasted before the stored fallback. The pre-scan reads up to ≈128 KiB of bounded
sample and, when the input is unambiguously incompressible, routes straight to
`deflateStoredPure` so the matcher never runs; a compressible file fails the
first sampled region and falls through to the normal path almost immediately. -/

/-- Minimum input size for the incompressible pre-scan to engage. The pre-scan's
    fixed cost (one presence-table allocation + a region scan) is only worth paying
    when the matcher it might skip is the dominant cost, i.e. on large inputs; below
    1 MiB the matcher is cheap enough that the scan would be net overhead on the
    common compressible file, so small inputs always take the normal path. This is
    why the gate leaves the Canterbury/Silesia dashboard untouched — every corpus
    file is either compressible or under the size gate. -/
def prescanMinSize : Nat := 1048576

/-- Order-0 entropy (bits/byte) of a 256-bucket byte histogram with `total`
    samples; `0` when `total = 0`. Pulled out so the per-region gate can call it
    without an inline fold. -/
def histEntropy (hist : Array Nat) (total : Nat) : Float := Id.run do
  if total == 0 then return 0.0
  let t := total.toFloat
  let mut e : Float := 0.0
  for c in hist do
    if c != 0 then
      let pr := c.toFloat / t
      e := e - pr * Float.log2 pr
  return e

/-- Cheap bounded test for *genuinely* incompressible input (already-compressed,
    encrypted, or random bytes), where the full match pass is wasted work before
    `deflateRaw`'s stored fallback. Scans up to `prescanRegions` contiguous regions
    spread across the input (cost independent of input size) and returns `true`
    only when *every* region is BOTH

    * near-maximal order-0 entropy (≈8 bits/byte), so Huffman coding cannot shrink
      it; and
    * free of recurring 4-grams, so the matcher would find no usable LZ77 match
      (its 32 KiB window fits inside a region, so any match it could make shows up
      here as a collision).

    The moment a region fails either test the scan stops and returns `false`, so a
    compressible file is rejected after one region and never pays the full sample.
    Requiring both signals on every region keeps the gate conservative: text (low
    entropy), base64 and other restricted alphabets (entropy ≈ 6), run-length-y
    binary, and repeated-block data (dense within-region 4-gram repeats) all bail
    out. Self-similar data whose period exceeds the 32 KiB window (e.g. `R ++ R`
    for a 512 KiB `R`) is genuinely incompressible by DEFLATE and is correctly
    stored. The 4-gram table is a single-hash presence filter, so its false
    collisions only ever *raise* the measured repeat count — they bias toward the
    (safe) compressed path, never toward storing.

    The result is opaque to correctness: a `true` only routes to
    `deflateStoredPure`, which is valid for every input, so a false positive costs
    ratio (a stored compressible block) but never correctness. -/
def incompressiblePrescan (data : ByteArray) : Bool := Id.run do
  if data.size < prescanMinSize then
    return false
  let n := data.size
  let tableSize := 1 <<< prescanTableBits
  let shift : UInt32 := (32 - prescanTableBits).toUInt32
  let regBytes := min prescanRegionBytes n
  -- `span` is the last legal region start (so a region never runs past `n`).
  -- `r * span / (prescanRegions - 1)` puts the first region at 0 and the last at
  -- `span` (ending exactly at `n`); regions overlap harmlessly when `n` is small.
  let span := n - regBytes
  for r in [0:prescanRegions] do
    let start := if prescanRegions ≤ 1 then 0 else min ((r * span) / (prescanRegions - 1)) span
    let stop := min (start + regBytes) n
    -- Cheap test first: the byte histogram needs no big table, so most
    -- compressible data (text/source/html — low order-0 entropy) bails here, after
    -- a single histogram pass and before the per-region table is ever allocated.
    let mut hist : Array Nat := Array.replicate 256 0
    let mut bytesSeen : Nat := 0
    for i in [start:stop] do
      let b := data[i]!.toNat
      hist := hist.set! b (hist[b]! + 1)
      bytesSeen := bytesSeen + 1
    -- (1) High entropy: order-0 entropy ≥ 7.6 bits/byte (random ≈ 7.99). A region
    --     too short to judge (`bytesSeen = 0`) also bails to the safe path.
    if bytesSeen == 0 || histEntropy hist bytesSeen < 7.6 then
      return false
    -- (2) No repeats: a high-entropy region might still be repeated-block data the
    --     matcher could compress, so insert every 4-gram into a fresh presence
    --     table (window-sized region ⇒ any matcher-usable repeat collides here) and
    --     require collisions < 3.125% of sampled 4-grams (`*32 < sampled`).
    --     Genuinely random input sits at ≈1.6% (table false collisions only).
    let mut table : Array UInt8 := Array.replicate tableSize 0
    let mut sampled : Nat := 0       -- 4-grams hashed in this region
    let mut collisions : Nat := 0    -- 4-grams hitting an already-seen slot
    let mut p := start
    while p + 3 < stop do
      let a := data[p]!.toUInt32
      let b := data[p+1]!.toUInt32
      let c := data[p+2]!.toUInt32
      let d := data[p+3]!.toUInt32
      let word := a ||| (b <<< 8) ||| (c <<< 16) ||| (d <<< 24)
      let idx := ((word * 2654435761) >>> shift).toNat
      if table[idx]! != 0 then
        collisions := collisions + 1
      else
        table := table.set! idx 1
      sampled := sampled + 1
      p := p + 1
    if sampled == 0 || collisions * 32 ≥ sampled then
      return false
  -- Every region looked incompressible.
  return true

/-- Size-arbitrate a packed-token base against one observation-split candidate.
    The caller owns matcher/profile and cut selection; keeping this shared tail
    independent of those heuristics lets level 7 retain its selected profile
    once, without rescanning content before choosing the split cadence. -/
def deflateRawSplitTierP (data : ByteArray) (ptokens : TokenArray)
    (cuts : List Nat) : ByteArray :=
  let withObs : Nat × (Unit → ByteArray) :=
    if cuts.isEmpty then deflateRawBasePPrep data ptokens
    else
      let obsFreqs := deflateObsSplitSizedFreqsP data ptokens cuts
      let basePrep := deflateRawBasePPrepF data ptokens obsFreqs.2
      if basePrep.1 < obsFreqs.1.1 then basePrep else obsFreqs.1
  withObs.2 ()

/-- Level-7 output dispatch at a retained content profile.

    Ambiguous small inputs use the established exact-size arbitration.  A
    calibrated large base route skips all split preparation, while a calibrated
    large split route uses the trees-only preparation above.  An empty cut list
    is definitionally a one-block split and therefore takes the base path,
    preserving the old arbitration result without constructing redundant
    trees.  Cut selection itself is below the route match, so direct-base inputs
    also skip the observation walker entirely. -/
def deflateRawL7RouteP (data : ByteArray) (profile : L7Profile)
    (ptokens : TokenArray) : ByteArray :=
  match l7OutputRouteFor data.size profile with
  | .arbitrate =>
      let checkTokens := l7SplitCheckTokensFor data profile
      let cuts := chooseSplitsHeuristicPUPacked ptokens data.size checkTokens
      deflateRawSplitTierP data ptokens cuts
  | .base => deflateRawBaseP data ptokens
  | .split =>
      let checkTokens := l7SplitCheckTokensFor data profile
      let cuts := chooseSplitsHeuristicPUPacked ptokens data.size checkTokens
      if cuts.isEmpty then deflateRawBaseP data ptokens
      else deflateDynamicBlocksSharedAtTreesP data ptokens cuts

/-- Unified raw DEFLATE compression dispatch. The native level range is **0–10**
    (wider than zlib's 0–9). Since #2638 the top of the ladder is:

      * **level 9** — the **L9-fast** approximate-optimal parse (near-crown ratio,
        ~2× faster); this is a change from the old level-9 = exact crown;
      * **level ≥ 10** — the exact backward-DP **crown** (the max-ratio ceiling,
        the former level-9 output); 11+ alias level 10.

    So callers pinning `level = 9` for absolute best ratio should now pass 10.
    (The zlib/FFI bindings are a separate 0–9 path and are unchanged.)

    Level 0 = stored; levels 1–4 run the fused greedy single-block cost-model
    dispatch (`deflateRawBaseF`). Levels 5–8 (#2737, L5 since the L5 re-grid)
    size-arbitrate that level's packed base candidate against the cross-block
    (shared-window) split candidate — one whole-file match pass, token stream
    partitioned per block, references cross block boundaries — with the
    partition chosen by the scalar-native observation-divergence heuristic,
    using its packed-counter refinement on large L5
    (`chooseSplitsHeuristicPU` / `chooseSplitsHeuristicPUPacked`, both refining
    libdeflate's streaming boundary check): each
    block gets its own frequency-fit Huffman trees, recovering most of the
    ratio a single whole-file tree leaves on large or heterogeneous inputs
    (zlib refits trees every ~16K symbols; the whole-file tree was why the
    mid-band was dominated). When the heuristic proposes no cuts (inputs
    below ~2·`splitMinBlockBytes` output bytes, since both sides of a cut
    must clear the floor) the split candidate would be a single dynamic block
    the base already sizes, so the dispatch skips it and small inputs pay
    nothing.

    Historically, the #2737 mid-band ladder (L4–L8) was the `mid-sweep`-chosen union of the old
    single-block frontier and the split frontier, so neither trades territory
    for the other (Silesia geomean, pinned interleaved timing):

      * **L4** — single-block, chain 64, lazy gate on: 38.8 MB/s @ 0.3330
        (the old L5 point; dominates the old L4).
      * **L5** — single-block, chain 128, gate off: 29.7 @ 0.3304 (dominates
        the old L7 = single-block chain 256: gate-off buys more ratio per
        cycle than chain depth).
      * **L6** — split, chain 64, gate off: 20.1 @ 0.3245. (Since the
        post-singleton re-grid: gate 64, probe /8 — 0.3205 @ ~36.5 weighted.)
      * **L7** — split, chain 256, gate off: 17.1 @ 0.3232. (Since the
        post-singleton re-grid: the old L6 config — 0.3196 @ ~33.7 weighted.)
      * **L8** — split + emitted fixed-cadence candidate, chain 512: 11.4 @
        0.3228 — the old L8's exact geomean ratio, ~20% faster.

    Every old L4–L8 point is dominated by (or within 1% of) the new curve's
    mixing frontier, and the split points sit far outside the old one.
    L4 has since moved again: the fused greedy chain-16/cap-128 point is
    measured above the current L3↔L5 time-per-byte interpolation on both
    headline corpora.

    At level 8 this **replaces** the arbitrated split
    (`chooseSplitsArbitrated` + `deflateDynamicBlocksSharedSized`, retired
    from the dispatch by #2737 but kept as the proven reference): the
    exact-bits arbitration guarded the heuristic against sizing worse than
    the fixed `sharedTokChunk` cadence, but paid two extra boxed whole-stream
    sizing walks (`findTableCode` linear scans + boxed `tokenFreqs`, ~18% of
    level-8 cycles) for it. Instead, level 8 *emits* the fixed-cadence
    partition as a third `pickSmaller` candidate: the min over emitted
    candidates decides by the same quantity the sizing pass computed
    (⌈bits/8⌉), so level 8 is never worse than the retired arbitration on
    any input, and one packed emit pass is far cheaper than the two boxed
    sizing walks it replaces.

    At levels 9 and 10 (and within the `optimalMaxSize` memory gate) the dispatch
    switches to a cost-model DP parse (grouped into blocks on the fixed
    `sharedTokChunk` cadence, emitted as `pickSmaller(base, optimal)`), choosing
    the globally cheapest token sequence under an estimated bit cost instead of
    the locally longest match. **Level 10** runs the exact backward-DP crown
    (`deflateDynamicBlocksOptimal`) — the max-ratio ceiling. **Level 9** runs the
    cheaper **L9-fast** approximate-optimal parse (`deflateDynamicBlocksOptimalFast`,
    #2638): single round, no length-code boundary scan, shallower cache — near the
    crown's ratio at ~2× its speed, measured ~20% outside the L8↔L9 mixing frontier
    on Silesia (a genuine new Pareto point; L10 ≤ L9 < L8 in output size, L9 > L8 in
    speed). On the
    Canterbury (11) and Silesia (12) corpora this fixed-cadence optimal candidate is
    measured strictly smaller than base, the self-contained split, *and* the
    arbitrated shared-window split on every file — including the binary
    `kennedy.xls`, where the self-contained split is the best of the three
    non-optimal candidates yet still loses to optimal — so `min(base, optimal) ==
    min(base, SC, shared, optimal)` byte-for-byte across both corpora (#2640). On that measured evidence
    the SC and shared candidates are dropped at L9: each costs a full independent
    match/split pass (~24% of L9 wall-clock together) for output `pickSmaller`
    always discarded. This is a measured speed/ratio tradeoff over those corpora,
    **not** a proven dominance invariant: the optimal parse minimizes an estimated
    per-token cost, not the final DEFLATE size across block partitions, so a
    pathological input whose statistics shift badly against the 8192-token cadence
    could in principle let an arbitrated split win. `base` stays as a near-free
    safety floor (it reuses the already-computed `ptokens`), so the emitted
    `pickSmaller(base, optimal)` is never worse than the lazy single-block baseline
    on any input — the only residual risk is forfeiting a split-only win, which the
    corpus gate found nowhere. The split candidates remain at level 8, where optimal
    is not computed.

    The base-vs-split candidates are compared against the whole base via
    `pickSmaller`, *not* nested inside the dynamic branch: on large heterogeneous
    inputs a single dynamic tree loses to fixed Huffman, so a base-internal gate
    would never reach the split even though it wins by 15–19%. `pickSmaller`
    guarantees we never regress below the base. All branches are
    roundtrip-verified.

    The split tier starts at level 5 (the L5 re-grid; previously level ≥ 6 per
    #2737, before that ≥ 8, and before that ≥ 7 — see #2698 for that history):
    with the boundaries chosen by the cheap streaming heuristic and the whole
    split pipeline on packed tokens, the candidates are **sized with their
    per-block trees captured** (`deflateRawBasePPrep` /
    `deflateDynamicBlocksSharedAtSizedP`) and only the winner is emitted
    (#2753), reusing the trees the sizing pass already built — so exactly one
    emit pass runs instead of two (three at L8). Level 4 stays single-block on
    purpose — its fused greedy policy is the high-speed frontier point. L5 joined the split tier in
    the re-grid: post-#2824/#2825/#2830 the old single-block L5 sat ~14%
    inside the L4↔L6 mixing line, and a shallow split point (chain 24, gate
    64, probe /4, no singleton) matches its speed at −0.53pp weighted-Silesia
    ratio — the split's per-block trees buy more than the deep chain did.
    Inputs of at least 4 MiB subsequently move to chain 22 and a 2016-token
    split cadence; smaller L5 inputs retain the chain-24/512-token point.
    Levels 1–4 stay single-block greedy.

    Before any of that, an `incompressiblePrescan` reads a bounded sample (≤128 KiB,
    short-circuited on the first compressible region) and, on unambiguously
    incompressible input, dispatches straight to `deflateStoredPure` — skipping the
    match pass entirely (the bulk of compress time, ≈2.5 MB/s at level 9 on random
    data) for a result the cost model would have chosen anyway. The gate is
    conservative (see `incompressiblePrescan`) and opaque to correctness: it only
    ever selects the already-proven stored block. -/
def deflateRaw (data : ByteArray) (level : UInt8 := 6) : ByteArray :=
  if level == 0 then deflateStoredPure data
  else if incompressiblePrescan data then deflateStoredPure data
  else if 5 ≤ level then
    -- One *packed* matcher pass shared by the base and shared-split candidates
    -- (the matcher is 83–84% of each candidate's cost — Wave-0 profile, D-2).
    -- Both candidates consume the packed words end-to-end (freqs *and* emit):
    -- no branch materializes boxed tokens.
    --
    -- (#2782 postscript: a cheap-knobs floor matcher at L9/L10 was tried and
    -- reverted — speed-neutral on Silesia, but the floor genuinely WINS on
    -- ptt5-class Canterbury bitmaps at L9, so weakening it changes real
    -- output. The floor's cost was never the matcher; it was the full base
    -- EMIT, now a sized prep below.)
    if level == 7 then
      -- Level 7 selects one content profile and retains it through matching and
      -- split-cadence/output-route selection.  In particular, the large shallow
      -- point needs the specialized L5 matcher, its 2016-token cadence, and the
      -- direct base route; recomputing `l7ProfileFor` would pay the four-region
      -- sketch twice.  Small inputs retain size arbitration except for the
      -- held-out-safe direct-split profiles selected by `l7OutputRouteFor`.
      let profile := l7ProfileFor data
      let ptokens := l7MatchPFor data profile
      deflateRawL7RouteP data profile ptokens
    else
      let ptokens := lzMatchP data level
      if level == 9 then
        -- Level 9 (#2638): the cheaper **L9-fast** approximate-optimal parse — near
        -- the crown's ratio at ~2× its speed, measured ~20% outside the L8↔L9
        -- mixing frontier on Silesia (a genuine new Pareto point). As with the
        -- exact candidate below, the split candidates are dropped on measured
        -- evidence; keep `base` (reuses `ptokens`, ~free) as the safety floor and
        -- emit `pickSmaller(base, fast-optimal)`. Above the `optimalMaxSize` memory
        -- gate the same parse runs *windowed* (#2787): region-capped choice storage
        -- gives byte-identical tokens in bounded memory, so the crown survives on
        -- streams larger than 64 MiB instead of collapsing to the split ratio.
        -- #2782 follow-up: size the floor (`deflateRawBasePPrep`, the #2753
        -- tree-capturing prep) instead of emitting it — the optimal candidate is
        -- strictly smaller on every corpus file (#2640), so the emit-both
        -- `pickSmaller` paid a full discarded freq+tree+BitWriter pass. Same
        -- winner, same bytes (prep size = flushed size, the #2753 invariant).
        let opt := if data.size ≤ optimalMaxSize then
          deflateDynamicBlocksOptimalFast data sharedTokChunk
        else
          deflateDynamicBlocksOptimalWindowedFast data sharedTokChunk
        let bp := deflateRawBasePPrep data ptokens
        emitSmallerBy bp.1 bp.2 opt.size (fun _ => opt)
      else if 10 ≤ level then
        -- Level ≥ 10: the exact backward-DP crown (the former level-9 behaviour,
        -- #2640) — the max-ratio ceiling, kept reachable per the #2638 directive.
        -- The fixed-cadence optimal candidate measured strictly smallest on every
        -- Canterbury and Silesia file, so the split candidates are dropped here;
        -- `pickSmaller(base, optimal)` is never worse than the lazy baseline. As at
        -- level 9, above the memory gate the exact parse runs windowed (#2787).
        -- Sized floor here too — see the level-9 arm.
        let opt := if data.size ≤ optimalMaxSize then
          deflateDynamicBlocksOptimal data sharedTokChunk
        else
          deflateDynamicBlocksOptimalWindowed data sharedTokChunk
        let bp := deflateRawBasePPrep data ptokens
        emitSmallerBy bp.1 bp.2 opt.size (fun _ => opt)
      else
        -- Levels 5, 6 and 8: base vs cross-block shared-window split at the
        -- observation-divergence boundaries (#2737),
        -- **size-arbitrated** (#2753). Both candidates are *prepared* — sized to
        -- their flushed byte count with per-block trees captured
        -- (`deflateRawBasePPrep` for the base, `deflateDynamicBlocksSharedAtSizedP`
        -- for the cut list) — and only the winner is emitted, reusing the trees the
        -- sizing pass already built, instead of emitting both and discarding the
        -- larger via `pickSmaller`. The winner and its bytes are identical to the
        -- retired emit-both dispatch. The tree capture is what makes this a net
        -- win: sizing a dynamic block otherwise costs a full frequency + Huffman
        -- pass, so without reuse "size both + emit winner" would not beat "emit
        -- both" (measured — Silesia L6-L7 +5-12% with reuse). No cuts ⇒ the split
        -- would be a single dynamic block the base already sizes, so skip it
        -- entirely (every input under ~2·splitMinBlockBytes takes this path).
        --
        -- When there are cuts, the split-sizing pass already computes `tokenFreqsP`
        -- per block; `deflateObsSplitSizedFreqsP` folds those into the whole-stream
        -- frequencies (EOB-corrected, `tokenFreqsP_append`) and the base candidate
        -- reuses them via `deflateRawBasePPrepF` — replacing the base's second
        -- whole-stream `tokenFreqsP` walk with a cheap ~316-entry summation (#2772).
        -- The packed-counter walker is used for large L5 and all of L6–L8. It is
        -- exactly equal to the scalar walker on `lzMatchP` streams
        -- (`chooseSplitsHeuristicPUPacked_lzMatchP_eq`), while reducing the hot
        -- loop's twenty counters to seven words. Small L5 retains the scalar
        -- route, where setup dominates the shorter stream.
        let cuts :=
          if level == 5 then
            if useL5LargeInputPolicy data level then
              chooseSplitsHeuristicPUPacked ptokens data.size
                (splitCheckTokensFor data level)
            else
              chooseSplitsHeuristicPU ptokens data.size
                (splitCheckTokensFor data level)
          else
            chooseSplitsHeuristicPUPacked ptokens data.size
              (splitCheckTokensFor data level)
        -- `deflateRawSplitTierP`: the base, or the size-arbitrated smaller of
        -- base and obs-split, with only the winning captured-tree thunk forced.
        deflateRawSplitTierP data ptokens cuts
  else
    -- Greedy tier (levels 1–4): fuse the whole-stream `tokenFreqsP` walk into the
    -- matcher pass. `deflateRawBaseF` produces the tokens and their frequencies in
    -- one pass and sizes/emits the base candidate from them, byte-identical to
    -- `deflateRawBase data level` (`deflateRawBaseF_eq`) — it removes the separate
    -- re-read of the (possibly cache-spilling) token array (#freq-fusion).
    deflateRawBaseF data level

end Zip.Native.Deflate
