import Zip.Native.Inflate

/-!
# Tree-free canonical decode (conformance/benchmark prototype)

A DEFLATE Huffman decoder that builds **no** Huffman tree: the fast ≤9-bit codes
go through the canonical 9-bit table (`buildTableCanonicalFast`), and the rare
>9-bit codes go through a canonical bit-by-bit decode keyed off the per-length
`count` / `firstCode` / sorted-symbol arrays — never a tree walk. This isolates
the *build-phase* win (skip `fromLengths`/`insertLoop`) and lets us measure the
end-to-end decode delta before investing in the formal proof.

Prototype only: `partial def` loops (no termination proof), `[i]!` indexing, and
no correctness theorems. Validated by conformance against the verified
`Inflate.inflate` on the real corpora; never on the trusted decode path.
-/

namespace Zip.Native
open ZipCommon (BitReader)

namespace HuffTree

/-- Canonical long-code decode tables (for codes longer than the 9-bit window):
    `count[len]` codes of each length, `firstCode[len]` the first canonical code
    of that length, `firstIndex[len]` the offset into `symbols` (symbols sorted by
    `(length, symbol)`). -/
structure LongDecode where
  count : Array Nat
  firstCode : Array Nat
  firstIndex : Array Nat
  symbols : Array UInt16

/-- `firstIndex[len]` = number of positive-length symbols of length `< len`
    (prefix sum of `count`). Well-founded form of the prototype loop. -/
def buildFirstIndex (count : Array Nat) (maxBits : Nat) : Array Nat :=
  go 1 0 (Array.replicate (maxBits + 2) 0)
where
  go (len idx : Nat) (fi : Array Nat) : Array Nat :=
    if len > maxBits then fi
    else go (len + 1) (idx + count[len]!) (fi.set! len idx)
  termination_by maxBits + 1 - len
  decreasing_by omega

/-- Counting sort: place each positive-length symbol at `offset[len]` (starting
    from `firstIndex`), so `symbols` lists symbols by `(length, symbol)`. -/
def buildSymbols (lengths : Array UInt8) (maxBits total : Nat) (firstIndex : Array Nat) :
    Array UInt16 :=
  go 0 firstIndex (Array.replicate total 0)
where
  go (s : Nat) (offset : Array Nat) (symbols : Array UInt16) : Array UInt16 :=
    if s ≥ lengths.size then symbols
    else
      let l := lengths[s]!.toNat
      if 0 < l ∧ l ≤ maxBits then
        go (s + 1) (offset.set! l (offset[l]! + 1)) (symbols.set! offset[l]! s.toUInt16)
      else go (s + 1) offset symbols
  termination_by lengths.size - s
  decreasing_by all_goals omega

/-- Build the canonical long-code tables from code lengths in O(n + maxBits).
    `firstCode` is the canonical first-code-per-length recurrence (RFC 1951
    §3.2.2), exactly `Huffman.Spec.nextCodes`; `firstIndex`/`symbols` are the
    prefix-sum and counting-sort over the code lengths. -/
def buildLongDecode (lengths : Array UInt8) (maxBits : Nat) : LongDecode :=
  let count := countLengthsFast lengths maxBits
  let firstCode := Huffman.Spec.nextCodes count maxBits
  let firstIndex := buildFirstIndex count maxBits
  let total := firstIndex[maxBits]! + count[maxBits]!
  let symbols := buildSymbols lengths maxBits total firstIndex
  { count, firstCode, firstIndex, symbols }

/-- Canonical bit-by-bit long-code decode: read bits MSB-first, accumulate the
    code value, and return the symbol once the code lands in some length's
    canonical range. Tree-free replacement for `walkTree`. -/
def walkCanonical (ld : LongDecode) (maxBits : Nat) (bitBuf : UInt64) (cnt : Nat) :
    Except String (UInt16 × UInt64 × Nat × Nat) :=
  go 1 0 bitBuf cnt
where
  go (len code : Nat) (bitBuf : UInt64) (cnt : Nat) :
      Except String (UInt16 × UInt64 × Nat × Nat) :=
    if hlen : len > maxBits then .error "Inflate: invalid Huffman code"
    else if cnt = 0 then .error "BitReader: unexpected end of input"
    else
      let code := code * 2 + (bitBuf &&& 1).toNat
      let bitBuf := bitBuf >>> 1
      let cnt := cnt - 1
      let fc := ld.firstCode[len]!
      let cl := ld.count[len]!
      if fc ≤ code ∧ code < fc + cl then
        .ok (ld.symbols[ld.firstIndex[len]! + (code - fc)]!, bitBuf, cnt, len)
      else go (len + 1) code bitBuf cnt
  termination_by maxBits + 1 - len
  decreasing_by omega

/-- `decodeSym` with the canonical long-code fallback (no tree). -/
@[inline] def decodeSymCanon (ld : LongDecode) (table : DecodeTable) (maxBits : Nat)
    (bitBuf : UInt64) (cnt : Nat) : Except String (UInt16 × UInt64 × Nat × Nat) :=
  let idx := (bitBuf &&& 0x1FF).toNat
  let len := (table.lenAt idx).toNat
  if len == 0 || len > cnt then walkCanonical ld maxBits bitBuf cnt
  else .ok (table.symAt idx, bitBuf >>> len.toUInt64, cnt - len, len)

end HuffTree

namespace InflateBuf
open Zip.Native.HuffTree (DecodeTable LongDecode decodeSymCanon)

/-- Tree-free copy of `goFusedP`: same wide-buffer loop, with the canonical
    long-code fallback (`decodeSymCanon`) in place of the tree walk. -/
partial def goTreeFree (litTable distTable : DecodeTable) (litLD distLD : LongDecode)
    (maxBits : Nat) (data : ByteArray) (maxOut : Nat)
    (pos : Nat) (bitBuf : UInt64) (cnt : Nat) (output : ByteArray) :
    Except String (ByteArray × Nat × UInt64 × Nat) := do
  if cnt ≤ 56 ∧ pos < data.size then
    goTreeFree litTable distTable litLD distLD maxBits data maxOut
      (pos + 1) (bitBuf ||| (data[pos]!.toUInt64 <<< cnt.toUInt64)) (cnt + 8) output
  else
  if (litTable.lenAt (bitBuf &&& 0x1FF).toNat).toNat ≠ 0
      ∧ (litTable.lenAt (bitBuf &&& 0x1FF).toNat).toNat ≤ cnt
      ∧ litTable.symAt (bitBuf &&& 0x1FF).toNat < 256 then
    if output.size ≥ maxOut then throw "Inflate: output exceeds maximum size"
    else
      goTreeFree litTable distTable litLD distLD maxBits data maxOut pos
        (bitBuf >>> ((litTable.lenAt (bitBuf &&& 0x1FF).toNat).toNat).toUInt64)
        (cnt - (litTable.lenAt (bitBuf &&& 0x1FF).toNat).toNat)
        (output.push (litTable.symAt (bitBuf &&& 0x1FF).toNat).toUInt8)
  else
  let cnt0 := cnt
  match decodeSymCanon litLD litTable maxBits bitBuf cnt with
  | .error e => .error e
  | .ok (sym, bitBuf, cnt, _used) =>
    if sym < 256 then
      if output.size ≥ maxOut then throw "Inflate: output exceeds maximum size"
      else if cnt0 ≤ cnt then throw "Inflate: no progress in Huffman decode"
      else goTreeFree litTable distTable litLD distLD maxBits data maxOut pos bitBuf cnt (output.push sym.toUInt8)
    else if sym == 256 then .ok (output, pos, bitBuf, cnt)
    else
      let idx := sym.toNat - 257
      if idx ≥ Inflate.lengthBase.size then throw s!"Inflate: invalid length code {sym}"
      else
        let base := Inflate.lengthBase[idx]!
        let extra := Inflate.lengthExtra[idx]!
        let (extraBits, bitBuf, cnt) ← takeBits bitBuf cnt extra.toNat
        let length := base.toNat + extraBits
        match decodeSymCanon distLD distTable maxBits bitBuf cnt with
        | .error e => .error e
        | .ok (distSym, bitBuf, cnt, _dused) =>
          let dIdx := distSym.toNat
          if dIdx ≥ Inflate.distBase.size then throw s!"Inflate: invalid distance code {distSym}"
          else
            let dBase := Inflate.distBase[dIdx]!
            let dExtra := Inflate.distExtra[dIdx]!
            let (dExtraBits, bitBuf, cnt) ← takeBits bitBuf cnt dExtra.toNat
            let distance := dBase.toNat + dExtraBits
            if hz : distance = 0 then throw s!"Inflate: zero back-reference distance"
            else if hds : distance > output.size then
              throw s!"Inflate: distance {distance} exceeds output size {output.size}"
            else if output.size + length > maxOut then throw "Inflate: output exceeds maximum size"
            else if cnt0 ≤ cnt then throw "Inflate: no progress in Huffman decode"
            else
              let out := Inflate.copyLoop output (output.size - distance) distance 0 length
                (by omega) (by omega)
              goTreeFree litTable distTable litLD distLD maxBits data maxOut pos bitBuf cnt out

/-- USize-scalar copy of `goTreeFree` (mirrors `goFusedPU`): `pos`/`cnt` are
    unboxed `USize`, the refill uses `data.uget`. Same canonical long-code
    fallback. `partial` (prototype — the perf measurement needs only a runnable
    loop, not a termination proof). -/
partial def goTreeFreeU (litTable distTable : DecodeTable) (litLD distLD : LongDecode)
    (maxBits : Nat) (data : ByteArray) (maxOut : Nat)
    (pos : USize) (bitBuf : UInt64) (cnt : USize)
    (hsz : data.size < USize.size) (output : ByteArray) :
    Except String (ByteArray × USize × UInt64 × USize) := do
  if hrc : cnt ≤ 56 ∧ pos < data.size.toUSize then
    goTreeFreeU litTable distTable litLD distLD maxBits data maxOut
      (pos + 1)
      (bitBuf ||| ((data.uget pos (by
          have h := USize.lt_iff_toNat_lt.mp hrc.2
          rwa [toUSize_toNat_of_lt hsz] at h)).toUInt64 <<< cnt.toUInt64))
      (cnt + 8) hsz output
  else
  if (litTable.lenAt (bitBuf &&& 0x1FF).toNat).toNat ≠ 0
      ∧ ((litTable.lenAt (bitBuf &&& 0x1FF).toNat).toNat).toUSize ≤ cnt
      ∧ litTable.symAt (bitBuf &&& 0x1FF).toNat < 256 then
    if output.size ≥ maxOut then throw "Inflate: output exceeds maximum size"
    else
      goTreeFreeU litTable distTable litLD distLD maxBits data maxOut pos
        (bitBuf >>> ((litTable.lenAt (bitBuf &&& 0x1FF).toNat).toNat).toUInt64)
        (cnt - ((litTable.lenAt (bitBuf &&& 0x1FF).toNat).toNat).toUSize)
        hsz
        (output.push (litTable.symAt (bitBuf &&& 0x1FF).toNat).toUInt8)
  else
  let cnt0 := cnt.toNat
  match decodeSymCanon litLD litTable maxBits bitBuf cnt.toNat with
  | .error e => .error e
  | .ok (sym, bitBuf, cnt', _used) =>
    if sym < 256 then
      if output.size ≥ maxOut then throw "Inflate: output exceeds maximum size"
      else if cnt0 ≤ cnt' then throw "Inflate: no progress in Huffman decode"
      else
        goTreeFreeU litTable distTable litLD distLD maxBits data maxOut pos bitBuf
          cnt'.toUSize hsz (output.push sym.toUInt8)
    else if sym == 256 then .ok (output, pos, bitBuf, cnt'.toUSize)
    else
      let idx := sym.toNat - 257
      if idx ≥ Inflate.lengthBase.size then throw s!"Inflate: invalid length code {sym}"
      else
        let base := Inflate.lengthBase[idx]!
        let extra := Inflate.lengthExtra[idx]!
        let (extraBits, bitBuf, cnt'') ← takeBits bitBuf cnt' extra.toNat
        let length := base.toNat + extraBits
        match decodeSymCanon distLD distTable maxBits bitBuf cnt'' with
        | .error e => .error e
        | .ok (distSym, bitBuf, cnt3, _dused) =>
          let dIdx := distSym.toNat
          if dIdx ≥ Inflate.distBase.size then throw s!"Inflate: invalid distance code {distSym}"
          else
            let dBase := Inflate.distBase[dIdx]!
            let dExtra := Inflate.distExtra[dIdx]!
            let (dExtraBits, bitBuf, cnt4) ← takeBits bitBuf cnt3 dExtra.toNat
            let distance := dBase.toNat + dExtraBits
            if hz : distance = 0 then throw s!"Inflate: zero back-reference distance"
            else if hds : distance > output.size then
              throw s!"Inflate: distance {distance} exceeds output size {output.size}"
            else if output.size + length > maxOut then throw "Inflate: output exceeds maximum size"
            else if cnt0 ≤ cnt4 then throw "Inflate: no progress in Huffman decode"
            else
              let out := Inflate.copyLoop output (output.size - distance) distance 0 length
                (by omega) (by omega)
              goTreeFreeU litTable distTable litLD distLD maxBits data maxOut pos bitBuf
                cnt4.toUSize hsz out

/-- Tree-free wide-buffer block decode: builds the fast tables canonically and
    the long-code tables, then runs the tree-free loop (no Huffman tree). Runs the
    unboxed `goTreeFreeU` when the input is addressable, else the boxed
    `goTreeFree` — mirroring `goFusedPDispatch`. -/
def decodeHuffmanFastBufTreeFree (br : BitReader) (output : ByteArray)
    (litLengths distLengths : Array UInt8) (maxOut : Nat) :
    Except String (ByteArray × BitReader) := do
  let litTable := HuffTree.buildTableCanonicalFast litLengths 15
  let distTable := HuffTree.buildTableCanonicalFast distLengths 15
  let litLD := HuffTree.buildLongDecode litLengths 15
  let distLD := HuffTree.buildLongDecode distLengths 15
  let (pos, bitBuf, cnt) := refill br.data br.pos 0 0
  let bitBuf := bitBuf >>> br.bitOff.toUInt64
  let cnt := cnt - br.bitOff
  let (out, pos', bitBuf', cnt') ←
    if hsz : br.data.size.toUSize.toNat = br.data.size then
      Except.map (fun x => (x.1, x.2.1.toNat, x.2.2.1, x.2.2.2.toNat))
        (goTreeFreeU litTable distTable litLD distLD 15 br.data maxOut
          pos.toUSize bitBuf cnt.toUSize (by rw [← hsz]; exact USize.toNat_lt_two_pow_numBits _) output)
    else
      goTreeFree litTable distTable litLD distLD 15 br.data maxOut pos bitBuf cnt output
  let _ := bitBuf'
  let endbit := pos' * 8 - cnt'
  .ok (out, { data := br.data, pos := endbit / 8, bitOff := endbit % 8 })

end InflateBuf

namespace Inflate

/-- Like `decodeDynamicTrees`, but returns only the code-length vectors — it never
    builds the lit/dist Huffman trees (the whole point of the tree-free path). The
    small code-length tree (`clTree`, 19 symbols) is still built to decode the
    length symbols. -/
def decodeDynamicLengthsOnly (br : BitReader) :
    Except String (Array UInt8 × Array UInt8 × BitReader) := do
  let (hlit, br) ← br.readBits 5
  let (hdist, br) ← br.readBits 5
  let (hclen, br) ← br.readBits 4
  let numLitLen := hlit.toNat + 257
  let numDist := hdist.toNat + 1
  let numCodeLen := hclen.toNat + 4
  let (clLengths, br) ← readCLCodeLengths br (.replicate 19 0) 0 numCodeLen
  let clTree ← HuffTree.fromLengths clLengths 7
  let totalCodes := numLitLen + numDist
  let (codeLengths, br) ← decodeCLSymbols clTree br (.replicate totalCodes 0) 0 totalCodes
  let litLenLengths := codeLengths.extract 0 numLitLen
  let distLengths := codeLengths.extract numLitLen totalCodes
  return (litLenLengths, distLengths, br)

/-- Tree-free block loop (mirrors `inflateLoop`): fixed and dynamic Huffman blocks
    decode through the canonical tree-free decoder; stored blocks unchanged. -/
partial def inflateLoopTreeFree (br : BitReader) (output : ByteArray) (maxOut : Nat) :
    Except String (ByteArray × Nat) := do
  let (bfinal, br₁) ← br.readBits 1
  let (btype, br₂) ← br₁.readBits 2
  let (output', br') ← match btype with
    | 0 => Inflate.decodeStored br₂ output maxOut
    | 1 => InflateBuf.decodeHuffmanFastBufTreeFree br₂ output fixedLitLengths fixedDistLengths maxOut
    | 2 => do
      let (litLens, distLens, br₃) ← decodeDynamicLengthsOnly br₂
      InflateBuf.decodeHuffmanFastBufTreeFree br₃ output litLens distLens maxOut
    | _ => throw s!"Inflate: reserved block type {btype}"
  if bfinal == 1 then
    return (output', br'.alignToByte.pos)
  else
    inflateLoopTreeFree br' output' maxOut

/-- Tree-free `inflate` (prototype): no Huffman tree built anywhere on the decode
    path. Conformance-checked against `Inflate.inflate`. -/
def inflateTreeFree (data : ByteArray) (maxOut : Nat := 1024 * 1024 * 1024) :
    Except String ByteArray := do
  let br : BitReader := { data, pos := 0, bitOff := 0 }
  let (output, _) ← inflateLoopTreeFree br ByteArray.empty maxOut
  return output

end Inflate
end Zip.Native
