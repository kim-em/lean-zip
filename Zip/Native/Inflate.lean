/-
  Pure Lean DEFLATE decompressor (RFC 1951).

  Supports all three block types:
  - Type 0: Stored (uncompressed)
  - Type 1: Fixed Huffman codes
  - Type 2: Dynamic Huffman codes

  This is a reference implementation prioritizing correctness over speed.
-/
import Zip.Native.BitReader

namespace Zip.Native

/-- A Huffman tree for decoding DEFLATE symbols.
    Leaf holds a symbol value; Node branches on 0 (left) vs 1 (right). -/
inductive HuffTree where
  | leaf (symbol : UInt16)
  | node (zero : HuffTree) (one : HuffTree)
  | empty

namespace HuffTree

/-- Insert a symbol into the tree at the given code/length. -/
def insert (tree : HuffTree) (code : UInt32) (len : Nat) (symbol : UInt16) : HuffTree :=
  go tree len
where
  go (t : HuffTree) : Nat → HuffTree
    | 0 => .leaf symbol
    | n + 1 =>
      let bit := (code >>> n.toUInt32) &&& 1
      match t with
      | .empty =>
        if bit == 0 then .node (go .empty n) .empty
        else .node .empty (go .empty n)
      | .node z o =>
        if bit == 0 then .node (go z n) o
        else .node z (go o n)
      | .leaf s => .leaf s  -- shouldn't happen in valid data

/-- Build a Huffman tree from an array of code lengths (indexed by symbol).
    Symbols with length 0 have no code. Uses the canonical Huffman algorithm
    from RFC 1951 §3.2.2. -/
def fromLengths (lengths : Array UInt8) (maxBits : Nat := 15) :
    Except String HuffTree := do
  -- Count codes of each length
  let mut blCount : Array Nat := .replicate (maxBits + 1) 0
  for len in lengths do
    let l := len.toNat
    if l > maxBits then throw "Inflate: code length exceeds maximum"
    blCount := blCount.set! l (blCount[l]! + 1)
  blCount := blCount.set! 0 0
  -- Compute first code for each length
  let mut nextCode : Array UInt32 := .replicate (maxBits + 1) 0
  let mut code : UInt32 := 0
  for bits in List.range maxBits do
    let b := bits + 1
    code := (code + blCount[bits]!.toUInt32) <<< 1
    nextCode := nextCode.set! b code
  -- Build tree by inserting each symbol
  let mut tree : HuffTree := .empty
  for h : i in [:lengths.size] do
    let len := lengths[i]
    if len > 0 then
      let c := nextCode[len.toNat]!
      nextCode := nextCode.set! len.toNat (c + 1)
      tree := tree.insert c len.toNat i.toUInt16
  return tree

/-- Decode one symbol from the bit reader using this Huffman tree. -/
def decode (tree : HuffTree) (br : BitReader) :
    Except String (UInt16 × BitReader) :=
  go tree br 0
where
  go : HuffTree → BitReader → Nat → Except String (UInt16 × BitReader)
    | .leaf s, br, _ => .ok (s, br)
    | .empty, _, _ => .error "Inflate: invalid Huffman code"
    | .node z o, br, n =>
      if n > 20 then .error "Inflate: Huffman decode exceeded max depth"
      else do
        let (bit, br') ← br.readBit
        if bit == 0 then go z br' (n + 1) else go o br' (n + 1)

end HuffTree

namespace Inflate

-- RFC 1951 §3.2.5: Fixed Huffman code lengths for lit/length (0–287)
private def fixedLitLengths : Array UInt8 := Id.run do
  let mut arr := .replicate 288 (0 : UInt8)
  for i in [:144] do arr := arr.set! i 8
  for i in [144:256] do arr := arr.set! i 9
  for i in [256:280] do arr := arr.set! i 7
  for i in [280:288] do arr := arr.set! i 8
  return arr

-- RFC 1951 §3.2.5: Fixed Huffman code lengths for distance (0–31)
private def fixedDistLengths : Array UInt8 := .replicate 32 (5 : UInt8)

-- Length base values for codes 257–285 (RFC 1951 §3.2.5)
private def lengthBase : Array UInt16 := #[
  3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31,
  35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258
]

-- Extra bits for length codes 257–285
private def lengthExtra : Array UInt8 := #[
  0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2,
  3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0
]

-- Distance base values for codes 0–29
private def distBase : Array UInt16 := #[
  1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193,
  257, 385, 513, 769, 1025, 1537, 2049, 3073, 4097, 6145, 8193, 12289,
  16385, 24577
]

-- Extra bits for distance codes 0–29
private def distExtra : Array UInt8 := #[
  0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6,
  7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13
]

-- Code length alphabet order for dynamic Huffman (RFC 1951 §3.2.7)
private def codeLengthOrder : Array Nat := #[
  16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15
]

/-- Decode dynamic Huffman trees from the bitstream (RFC 1951 §3.2.7). -/
private def decodeDynamicTrees (br : BitReader) :
    Except String (HuffTree × HuffTree × BitReader) := do
  let (hlit, br) ← br.readBits 5
  let (hdist, br) ← br.readBits 5
  let (hclen, br) ← br.readBits 4
  let numLitLen := hlit.toNat + 257
  let numDist := hdist.toNat + 1
  let numCodeLen := hclen.toNat + 4
  -- Read code length code lengths
  let mut clLengths : Array UInt8 := .replicate 19 0
  let mut br := br
  for i in [:numCodeLen] do
    let (v, br') ← br.readBits 3
    br := br'
    clLengths := clLengths.set! (codeLengthOrder[i]!) v.toUInt8
  let clTree ← HuffTree.fromLengths clLengths 7
  -- Decode literal/length + distance code lengths
  let totalCodes := numLitLen + numDist
  let mut codeLengths : Array UInt8 := .replicate totalCodes 0
  let mut idx := 0
  while idx < totalCodes do
    let (sym, br') ← clTree.decode br
    br := br'
    if sym < 16 then
      codeLengths := codeLengths.set! idx sym.toUInt8
      idx := idx + 1
    else if sym == 16 then
      if idx == 0 then throw "Inflate: repeat code at start"
      let (rep, br') ← br.readBits 2
      br := br'
      let prev := codeLengths[idx - 1]!
      for _ in [:rep.toNat + 3] do
        if idx < totalCodes then
          codeLengths := codeLengths.set! idx prev
          idx := idx + 1
    else if sym == 17 then
      let (rep, br') ← br.readBits 3
      br := br'
      for _ in [:rep.toNat + 3] do
        if idx < totalCodes then
          codeLengths := codeLengths.set! idx 0
          idx := idx + 1
    else if sym == 18 then
      let (rep, br') ← br.readBits 7
      br := br'
      for _ in [:rep.toNat + 11] do
        if idx < totalCodes then
          codeLengths := codeLengths.set! idx 0
          idx := idx + 1
    else
      throw s!"Inflate: invalid code length symbol {sym}"
  let litLenLengths := codeLengths.extract 0 numLitLen
  let distLengths := codeLengths.extract numLitLen totalCodes
  let litTree ← HuffTree.fromLengths litLenLengths
  let distTree ← HuffTree.fromLengths distLengths
  return (litTree, distTree, br)

/-- Decode a stored (uncompressed) block. -/
private def decodeStored (br : BitReader) (output : ByteArray) :
    Except String (ByteArray × BitReader) := do
  let (len, br) ← br.readUInt16LE
  let (nlen, br) ← br.readUInt16LE
  if len ^^^ nlen != 0xFFFF then
    throw "Inflate: stored block length check failed"
  let (bytes, br) ← br.readBytes len.toNat
  return (output ++ bytes, br)

/-- Decode a Huffman-coded block (fixed or dynamic).
    Uses a fuel parameter to guarantee termination. -/
private def decodeHuffman (br : BitReader) (output : ByteArray)
    (litTree distTree : HuffTree) (fuel : Nat := 10000000) :
    Except String (ByteArray × BitReader) :=
  go br output fuel
where
  go (br : BitReader) (output : ByteArray) : Nat → Except String (ByteArray × BitReader)
    | 0 => .error "Inflate: decompression exceeded size limit"
    | fuel + 1 => do
      let (sym, br) ← litTree.decode br
      if sym < 256 then
        go br (output.push sym.toUInt8) fuel
      else if sym == 256 then
        .ok (output, br)
      else
        -- Length code 257–285
        let idx := sym.toNat - 257
        if idx ≥ lengthBase.size then
          throw s!"Inflate: invalid length code {sym}"
        let base := lengthBase[idx]!
        let extra := lengthExtra[idx]!
        let (extraBits, br) ← br.readBits extra.toNat
        let length := base.toNat + extraBits.toNat
        -- Distance code
        let (distSym, br) ← distTree.decode br
        let dIdx := distSym.toNat
        if dIdx ≥ distBase.size then
          throw s!"Inflate: invalid distance code {distSym}"
        let dBase := distBase[dIdx]!
        let dExtra := distExtra[dIdx]!
        let (dExtraBits, br) ← br.readBits dExtra.toNat
        let distance := dBase.toNat + dExtraBits.toNat
        -- Copy from output buffer (LZ77 back-reference)
        if distance > output.size then
          throw s!"Inflate: distance {distance} exceeds output size {output.size}"
        let start := output.size - distance
        let mut out := output
        for i in [:length] do
          -- Must read from `out` (not `output`) for overlapping copies
          out := out.push out[start + (i % distance)]!
        go br out fuel

/-- Inflate a raw DEFLATE stream. Processes blocks until a final block is seen. -/
def inflate (data : ByteArray) : Except String ByteArray := do
  let mut br := BitReader.ofByteArray data
  let mut output : ByteArray := .empty
  let mut isFinal := false
  -- Build fixed trees once
  let fixedLit ← HuffTree.fromLengths fixedLitLengths
  let fixedDist ← HuffTree.fromLengths fixedDistLengths
  let mut blockCount := 0
  while !isFinal do
    if blockCount > 10000 then throw "Inflate: too many blocks"
    blockCount := blockCount + 1
    let (bfinal, br') ← br.readBits 1
    let (btype, br') ← br'.readBits 2
    br := br'
    isFinal := bfinal == 1
    match btype with
    | 0 => -- Stored
      let (out, br') ← decodeStored br output
      output := out; br := br'
    | 1 => -- Fixed Huffman
      let (out, br') ← decodeHuffman br output fixedLit fixedDist
      output := out; br := br'
    | 2 => -- Dynamic Huffman
      let (litTree, distTree, br') ← decodeDynamicTrees br
      let (out, br'') ← decodeHuffman br' output litTree distTree
      output := out; br := br''
    | _ => throw s!"Inflate: reserved block type {btype}"
  return output

end Inflate
end Zip.Native
