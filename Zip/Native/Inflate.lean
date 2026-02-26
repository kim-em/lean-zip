import Zip.Native.BitReader
import Zip.Spec.Huffman

/-!
  Pure Lean DEFLATE decompressor (RFC 1951).

  Supports all three block types:
  - Type 0: Stored (uncompressed)
  - Type 1: Fixed Huffman codes
  - Type 2: Dynamic Huffman codes

  This is a reference implementation prioritizing correctness over speed.
-/

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

/-- Build a Huffman tree by sequentially inserting symbols from an array of
    code lengths, starting from index `start`. Returns the tree and updated
    nextCode array. Used by `fromLengths` for the final insertion pass. -/
def insertLoop (lengths : Array UInt8) (nextCode : Array UInt32)
    (start : Nat) (tree : HuffTree) : HuffTree × Array UInt32 :=
  if h : start < lengths.size then
    let len := lengths[start]
    if len > 0 then
      let c := nextCode[len.toNat]!
      let tree' := tree.insert c len.toNat start.toUInt16
      let nextCode' := nextCode.set! len.toNat (c + 1)
      insertLoop lengths nextCode' (start + 1) tree'
    else
      insertLoop lengths nextCode (start + 1) tree
  else (tree, nextCode)
termination_by lengths.size - start

/-- The Huffman tree built by the canonical construction (RFC 1951 §3.2.2),
    without input validation. -/
def fromLengthsTree (lengths : Array UInt8) (maxBits : Nat := 15) : HuffTree :=
  let lsList := lengths.toList.map UInt8.toNat
  let blCount := Huffman.Spec.countLengths lsList maxBits
  let ncNat := Huffman.Spec.nextCodes blCount maxBits
  let nextCode : Array UInt32 := ncNat.map fun n => n.toUInt32
  (insertLoop lengths nextCode 0 .empty).1

/-- Build a Huffman tree from an array of code lengths (indexed by symbol).
    Symbols with length 0 have no code. Uses the canonical Huffman algorithm
    from RFC 1951 §3.2.2. Validates that all lengths are ≤ maxBits and the
    Kraft inequality is satisfied (codes are not oversubscribed). -/
def fromLengths (lengths : Array UInt8) (maxBits : Nat := 15) :
    Except String HuffTree :=
  if lengths.any (fun l => l.toNat > maxBits) then
    .error "Inflate: code length exceeds maximum"
  else
    let lsList := lengths.toList.map UInt8.toNat
    let kraft := (lsList.filter (· != 0)).foldl
      (fun acc l => acc + 2 ^ (maxBits - l)) 0
    if kraft > 2 ^ maxBits then
      .error "Inflate: oversubscribed Huffman code"
    else
      .ok (fromLengthsTree lengths maxBits)

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
def fixedLitLengths : Array UInt8 :=
  .replicate 144 8 ++ .replicate 112 9 ++
  .replicate 24 7 ++ .replicate 8 8

-- RFC 1951 §3.2.5: Fixed Huffman code lengths for distance (0–31)
def fixedDistLengths : Array UInt8 := .replicate 32 (5 : UInt8)

-- Length base values for codes 257–285 (RFC 1951 §3.2.5)
def lengthBase : Array UInt16 := #[
  3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31,
  35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258
]

-- Extra bits for length codes 257–285
def lengthExtra : Array UInt8 := #[
  0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2,
  3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0
]

-- Distance base values for codes 0–29
def distBase : Array UInt16 := #[
  1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193,
  257, 385, 513, 769, 1025, 1537, 2049, 3073, 4097, 6145, 8193, 12289,
  16385, 24577
]

-- Extra bits for distance codes 0–29
def distExtra : Array UInt8 := #[
  0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6,
  7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13
]

/-- Copy `length` bytes from `buf` starting at `start`, repeating every
    `distance` bytes (LZ77 back-reference copy with wrap-around).
    Defined as explicit recursion for proof tractability. -/
def copyLoop (buf : ByteArray) (start distance : Nat)
    (k length : Nat) : ByteArray :=
  if k < length then
    copyLoop (buf.push buf[start + (k % distance)]!) start distance (k + 1) length
  else buf
termination_by length - k

-- Code length alphabet order for dynamic Huffman (RFC 1951 §3.2.7)
def codeLengthOrder : Array Nat := #[
  16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15
]

/-- Fill `count` consecutive entries starting at `idx` with `val`,
    stopping when `idx ≥ bound`. Returns updated array and new index. -/
def fillEntries (arr : Array UInt8) (idx count bound : Nat) (val : UInt8) :
    Array UInt8 × Nat :=
  if count = 0 ∨ idx ≥ bound then (arr, idx)
  else fillEntries (arr.set! idx val) (idx + 1) (count - 1) bound val
termination_by count

/-- Read code length code lengths: 3 bits each at permuted positions.
    Defined as explicit recursion for proof tractability. -/
def readCLCodeLengths (br : BitReader) (clLengths : Array UInt8)
    (i numCodeLen : Nat) : Except String (Array UInt8 × BitReader) :=
  if i < numCodeLen then do
    let (v, br) ← br.readBits 3
    readCLCodeLengths br (clLengths.set! (codeLengthOrder[i]!) v.toUInt8) (i + 1) numCodeLen
  else
    .ok (clLengths, br)
termination_by numCodeLen - i

/-- Decode code lengths using the CL Huffman tree (RFC 1951 §3.2.7).
    Processes symbols: 0–15 (literal length), 16 (repeat previous),
    17 (repeat 0, short), 18 (repeat 0, long).
    Defined as explicit recursion for proof tractability. -/
def decodeCLSymbols (clTree : HuffTree) (br : BitReader)
    (codeLengths : Array UInt8) (idx totalCodes : Nat)
    (fuel : Nat) : Except String (Array UInt8 × BitReader) :=
  match fuel with
  | 0 => .error "Inflate: dynamic tree decode exceeded fuel"
  | fuel + 1 =>
    if idx ≥ totalCodes then .ok (codeLengths, br)
    else do
      let (sym, br) ← clTree.decode br
      if sym < 16 then
        decodeCLSymbols clTree br (codeLengths.set! idx sym.toUInt8) (idx + 1) totalCodes fuel
      else if sym == 16 then
        if idx == 0 then throw "Inflate: repeat code at start"
        let (rep, br) ← br.readBits 2
        let prev := codeLengths[idx - 1]!
        let count := rep.toNat + 3
        if idx + count > totalCodes then throw "Inflate: repeat code exceeds total"
        let (codeLengths, idx) := fillEntries codeLengths idx count totalCodes prev
        decodeCLSymbols clTree br codeLengths idx totalCodes fuel
      else if sym == 17 then
        let (rep, br) ← br.readBits 3
        let count := rep.toNat + 3
        if idx + count > totalCodes then throw "Inflate: repeat code exceeds total"
        let (codeLengths, idx) := fillEntries codeLengths idx count totalCodes 0
        decodeCLSymbols clTree br codeLengths idx totalCodes fuel
      else if sym == 18 then
        let (rep, br) ← br.readBits 7
        let count := rep.toNat + 11
        if idx + count > totalCodes then throw "Inflate: repeat code exceeds total"
        let (codeLengths, idx) := fillEntries codeLengths idx count totalCodes 0
        decodeCLSymbols clTree br codeLengths idx totalCodes fuel
      else
        throw s!"Inflate: invalid code length symbol {sym}"

/-- Decode dynamic Huffman trees from the bitstream (RFC 1951 §3.2.7). -/
def decodeDynamicTrees (br : BitReader) :
    Except String (HuffTree × HuffTree × BitReader) := do
  let (hlit, br) ← br.readBits 5
  let (hdist, br) ← br.readBits 5
  let (hclen, br) ← br.readBits 4
  let numLitLen := hlit.toNat + 257
  let numDist := hdist.toNat + 1
  let numCodeLen := hclen.toNat + 4
  let (clLengths, br) ← readCLCodeLengths br (.replicate 19 0) 0 numCodeLen
  let clTree ← HuffTree.fromLengths clLengths 7
  let totalCodes := numLitLen + numDist
  let (codeLengths, br) ← decodeCLSymbols clTree br (.replicate totalCodes 0)
    0 totalCodes (totalCodes + 1)
  let litLenLengths := codeLengths.extract 0 numLitLen
  let distLengths := codeLengths.extract numLitLen totalCodes
  let litTree ← HuffTree.fromLengths litLenLengths
  let distTree ← HuffTree.fromLengths distLengths
  return (litTree, distTree, br)

/-- Decode a stored (uncompressed) block. -/
protected def decodeStored (br : BitReader) (output : ByteArray)
    (maxOutputSize : Nat) : Except String (ByteArray × BitReader) := do
  let (len, br) ← br.readUInt16LE
  let (nlen, br) ← br.readUInt16LE
  if len ^^^ nlen != 0xFFFF then
    throw "Inflate: stored block length check failed"
  if output.size + len.toNat > maxOutputSize then
    throw "Inflate: output exceeds maximum size"
  let (bytes, br) ← br.readBytes len.toNat
  return (output ++ bytes, br)

/-- Decode a Huffman-coded block (fixed or dynamic).
    Uses a fuel parameter to guarantee termination. -/
protected def decodeHuffman (br : BitReader) (output : ByteArray)
    (litTree distTree : HuffTree) (maxOutputSize : Nat)
    (fuel : Nat := 1000000000000000000) : Except String (ByteArray × BitReader) :=
  go br output fuel
where
  go (br : BitReader) (output : ByteArray) : Nat → Except String (ByteArray × BitReader)
    | 0 => .error "Inflate: decompression exceeded fuel limit"
    | fuel + 1 => do
      let (sym, br) ← litTree.decode br
      if sym < 256 then
        if output.size ≥ maxOutputSize then
          throw "Inflate: output exceeds maximum size"
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
        if output.size + length > maxOutputSize then
          throw "Inflate: output exceeds maximum size"
        let start := output.size - distance
        let out := copyLoop output start distance 0 length
        go br out fuel

/-- Block loop for DEFLATE decompression. Decodes blocks until a final block
    is seen or fuel is exhausted. Defined as explicit recursion for proof
    tractability (`forIn` on `Range` cannot be unfolded). -/
def inflateLoop (br : BitReader) (output : ByteArray)
    (fixedLit fixedDist : HuffTree) (maxOutputSize : Nat) :
    Nat → Except String (ByteArray × Nat)
  | 0 => .error "Inflate: too many blocks"
  | fuel + 1 => do
    let (bfinal, br₁) ← br.readBits 1
    let (btype, br₂) ← br₁.readBits 2
    let (output', br') ← match btype with
      | 0 => Inflate.decodeStored br₂ output maxOutputSize
      | 1 => Inflate.decodeHuffman br₂ output fixedLit fixedDist maxOutputSize
      | 2 => do
        let (litTree, distTree, br₃) ← decodeDynamicTrees br₂
        Inflate.decodeHuffman br₃ output litTree distTree maxOutputSize
      | _ => throw s!"Inflate: reserved block type {btype}"
    if bfinal == 1 then
      let aligned := br'.alignToByte
      return (output', aligned.pos)
    else
      inflateLoop br' output' fixedLit fixedDist maxOutputSize fuel

/-- Inflate a raw DEFLATE stream starting at byte offset `startPos`. Returns the
    decompressed data and the byte-aligned position after the last DEFLATE block.
    `maxOutputSize` (default 1 GiB) limits decompressed output to guard against
    zip bombs. -/
def inflateRaw (data : ByteArray) (startPos : Nat := 0)
    (maxOutputSize : Nat := 1024 * 1024 * 1024) :
    Except String (ByteArray × Nat) := do
  let br : BitReader := { data, pos := startPos, bitOff := 0 }
  let fixedLit ← HuffTree.fromLengths fixedLitLengths
  let fixedDist ← HuffTree.fromLengths fixedDistLengths
  inflateLoop br .empty fixedLit fixedDist maxOutputSize 10000000000

/-- Inflate a raw DEFLATE stream. Processes blocks until a final block is seen.
    `maxOutputSize` (default 1 GiB) limits decompressed output to guard against
    zip bombs. -/
def inflate (data : ByteArray) (maxOutputSize : Nat := 1024 * 1024 * 1024) :
    Except String ByteArray := do
  let (output, _) ← inflateRaw data 0 maxOutputSize
  return output

end Inflate
end Zip.Native
