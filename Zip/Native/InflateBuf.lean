import Zip.Native.Inflate

/-!
  Wide-buffer DEFLATE Huffman decoder (Track D, #2501 approach 1).

  Threads the bit cursor as unboxed scalars `(pos, bitBuf : UInt64, cnt)` — plus
  a `bitpos` measure used for termination — through the whole Huffman symbol
  loop, refilling up to 57 bits at a time from `data` and consuming by shift,
  instead of allocating a fresh immutable `BitReader` struct on every
  symbol/field read. The `BitReader` is materialised only at block boundaries.

  This is the *implementation*; `Zip.Spec.InflateBufCorrect` proves it equal to
  the canonical `Inflate.decodeHuffmanFast`, so the verified `inflate` can adopt
  it with no trust gap (no `@[extern]`, no `@[implemented_by]`).
-/

namespace Zip.Native
open ZipCommon (BitReader)

namespace InflateBuf

/-- Load whole bytes into the high end of `bitBuf` until it holds > 56 bits or
    the input is exhausted. Preserves the consumed bit position `pos*8 - cnt`. -/
@[specialize] def refill (data : ByteArray) (pos : Nat) (bitBuf : UInt64) (cnt : Nat) :
    Nat × UInt64 × Nat :=
  if cnt ≤ 56 ∧ pos < data.size then
    refill data (pos + 1) (bitBuf ||| (data[pos]!.toUInt64 <<< cnt.toUInt64)) (cnt + 8)
  else (pos, bitBuf, cnt)
termination_by data.size - pos
decreasing_by simp_wf; omega

/-- Bit-by-bit tree walk over the buffer (fallback for codes longer than the
    9-bit table or near end-of-input). Mirrors `HuffTree.decode.go` exactly
    (same `depth > 20` guard, same error strings), so it is provably equal;
    `depth` is the tree-walk depth. Returns the symbol, the remaining buffer,
    and the number of bits consumed. -/
def walkTree (t : HuffTree) (bitBuf : UInt64) (cnt depth : Nat) :
    Except String (UInt16 × UInt64 × Nat × Nat) :=
  match t with
  | .leaf s => .ok (s, bitBuf, cnt, 0)
  | .empty => .error "Inflate: invalid Huffman code"
  | .node z o =>
    if depth > 20 then .error "Inflate: Huffman decode exceeded max depth"
    else if cnt = 0 then .error "BitReader: unexpected end of input"
    else
      match walkTree (if bitBuf &&& 1 == 0 then z else o) (bitBuf >>> 1) (cnt - 1) (depth + 1) with
      | .error e => .error e
      | .ok (s, bb, c, used) => .ok (s, bb, c, used + 1)

/-- Decode one Huffman symbol from the (refilled) buffer via the 9-bit table,
    falling back to the tree walk for long codes / near EOF. Returns the symbol,
    remaining buffer state, and bits consumed. -/
@[inline] def decodeSym (tree : HuffTree) (table : Array (UInt16 × UInt8))
    (bitBuf : UInt64) (cnt : Nat) : Except String (UInt16 × UInt64 × Nat × Nat) :=
  let idx := (bitBuf &&& 0x1FF).toNat
  let entry := table[idx]!
  let len := entry.2.toNat
  if len == 0 || len > cnt then walkTree tree bitBuf cnt 0
  else .ok (entry.1, bitBuf >>> len.toUInt64, cnt - len, len)

/-- Read `n` (≤ cnt) bits LSB-first from the buffer without refilling. -/
@[inline] def takeBits (bitBuf : UInt64) (cnt n : Nat) : Nat × UInt64 × Nat :=
  let v := (bitBuf &&& ((1 <<< n.toUInt64) - 1)).toNat
  (v, bitBuf >>> n.toUInt64, cnt - n)

set_option maxRecDepth 4096 in
/-- Wide-buffer Huffman symbol loop (mirrors `Inflate.decodeHuffmanFast.go`).
    `bitpos` is the stream bit position (`= pos*8 - cnt` under the buffer
    invariant); it carries the well-founded measure and the progress guards. -/
def go (litTable distTable : Array (UInt16 × UInt8))
    (data : ByteArray) (litTree distTree : HuffTree) (maxOut dataSize : Nat)
    (pos : Nat) (bitBuf : UInt64) (cnt bitpos : Nat) (output : ByteArray) :
    Except String (ByteArray × Nat × UInt64 × Nat × Nat) := do
  -- One refill covers a full worst case: lit(15)+lenExtra(13)+dist(15)+distExtra(13)=56.
  let (pos, bitBuf, cnt) := refill data pos bitBuf cnt
  -- `cnt0` = bits available after refill; consumed bits = `cnt0 - cnt` (plain Nats,
  -- so the termination measure carries no array-access atoms).
  let cnt0 := cnt
  match decodeSym litTree litTable bitBuf cnt with
  | .error e => .error e
  | .ok (sym, bitBuf, cnt, _used) =>
    if sym < 256 then
      if output.size ≥ maxOut then throw "Inflate: output exceeds maximum size"
      else if _h₁ : bitpos + (cnt0 - cnt) ≤ bitpos then throw "Inflate: no progress in Huffman decode"
      else if _h₂ : dataSize * 8 < bitpos + (cnt0 - cnt) then throw "Inflate: bit position out of range"
      else
        go litTable distTable data litTree distTree maxOut dataSize pos bitBuf cnt (bitpos + (cnt0 - cnt)) (output.push sym.toUInt8)
    else if sym == 256 then
      .ok (output, pos, bitBuf, cnt, bitpos + (cnt0 - cnt))
    else
      let idx := sym.toNat - 257
      if h : idx ≥ Inflate.lengthBase.size then throw s!"Inflate: invalid length code {sym}"
      else
        let base := Inflate.lengthBase[idx]
        let extra := Inflate.lengthExtra[idx]'(by simp [Inflate.lengthExtra_size, Inflate.lengthBase_size] at h ⊢; omega)
        let (extraBits, bitBuf, cnt) := takeBits bitBuf cnt extra.toNat
        let length := base.toNat + extraBits
        match decodeSym distTree distTable bitBuf cnt with
        | .error e => .error e
        | .ok (distSym, bitBuf, cnt, _dused) =>
          let dIdx := distSym.toNat
          if h : dIdx ≥ Inflate.distBase.size then throw s!"Inflate: invalid distance code {distSym}"
          else
            let dBase := Inflate.distBase[dIdx]
            let dExtra := Inflate.distExtra[dIdx]'(by simp [Inflate.distExtra_size, Inflate.distBase_size] at h ⊢; omega)
            let (dExtraBits, bitBuf, cnt) := takeBits bitBuf cnt dExtra.toNat
            let distance := dBase.toNat + dExtraBits
            if h0 : distance = 0 then throw "Inflate: zero back-reference distance"
            else if hds : distance > output.size then
              throw s!"Inflate: distance {distance} exceeds output size {output.size}"
            else if output.size + length > maxOut then throw "Inflate: output exceeds maximum size"
            else if _h₁ : bitpos + (cnt0 - cnt) ≤ bitpos then throw "Inflate: no progress in Huffman decode"
            else if _h₂ : dataSize * 8 < bitpos + (cnt0 - cnt) then throw "Inflate: bit position out of range"
            else
              let out := Inflate.copyLoop output (output.size - distance) distance 0 length
                (by omega) (by omega)
              go litTable distTable data litTree distTree maxOut dataSize pos bitBuf cnt (bitpos + (cnt0 - cnt)) out
termination_by dataSize * 8 - bitpos
decreasing_by all_goals omega

/-- Wide-buffer replacement for `Inflate.decodeHuffmanFast`: convert the
    `BitReader` to a scalar buffer, run the loop, convert back. -/
def decodeHuffmanFastBuf (br : BitReader) (output : ByteArray)
    (litTree distTree : HuffTree) (maxOut : Nat) :
    Except String (ByteArray × BitReader) := do
  let litTable := litTree.buildTable
  let distTable := distTree.buildTable
  let (pos, bitBuf, cnt) := refill br.data br.pos 0 0
  -- align: drop the bitOff bits already consumed in the first byte
  let bitBuf := bitBuf >>> br.bitOff.toUInt64
  let cnt := cnt - br.bitOff
  let bitpos := br.pos * 8 + br.bitOff
  let (out, pos', bitBuf', cnt', _bitpos') ←
    go litTable distTable br.data litTree distTree maxOut br.data.size pos bitBuf cnt bitpos output
  let _ := bitBuf'
  let endbit := pos' * 8 - cnt'
  .ok (out, { data := br.data, pos := endbit / 8, bitOff := endbit % 8 })

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

/-- Wide-buffer `inflate` (entry point). -/
def inflate (data : ByteArray) (maxOut : Nat := 1024 * 1024 * 1024) :
    Except String ByteArray := do
  let br : BitReader := { data, pos := 0, bitOff := 0 }
  let fixedLit ← HuffTree.fromLengths Inflate.fixedLitLengths
  let fixedDist ← HuffTree.fromLengths Inflate.fixedDistLengths
  let (output, _) ← inflateLoopBuf br .empty fixedLit fixedDist maxOut data.size
  return output

end InflateBuf
end Zip.Native
