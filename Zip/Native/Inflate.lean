import ZipCommon.Spec.BitReaderInvariant
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

open ZipCommon (BitReader)

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
      if hlen : len.toNat < nextCode.size then
        let c := nextCode[len.toNat]
        let tree' := tree.insert c len.toNat start.toUInt16
        let nextCode' := nextCode.set! len.toNat (c + 1)
        insertLoop lengths nextCode' (start + 1) tree'
      else
        insertLoop lengths nextCode (start + 1) tree
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

/-! ## Table-driven fast decode (RFC 1951, "fast bits")

The bit-by-bit tree walk in `decode` descends one node per bit. The standard
DEFLATE speedup is a **lookup table**: peek `fastBits` bits and read the
`(symbol, codeLen)` directly from a `2^fastBits`-entry table, then consume
`codeLen` bits in one step. Codes longer than `fastBits` (rare; DEFLATE allows
up to 15) fall back to the tree walk. `decode` stays the canonical spec;
`decodeWithTable` is *proven equal* to it (`Zip.Spec.InflateTable`,
`decodeWithTable_eq`) and the fast block loop `decodeHuffmanFast` is proven
equal to `decodeHuffman` — there is no `@[implemented_by]` trust gap. -/

/-- Number of bits the fast decode table indexes on (the common "fast bits"). -/
def fastBits : Nat := 9

/-- Walk `tree` using the low bits of `idx` (LSB first, matching `readBit`),
    for up to `fastBits` steps. Returns `(symbol, codeLen)` if a leaf is reached
    within `fastBits` bits, or `(0, 0)` (a sentinel meaning "fall back to the
    tree walk") for the `empty` slot or a code longer than `fastBits`. -/
def tableEntry (tree : HuffTree) (idx : Nat) : UInt16 × UInt8 :=
  go tree idx 0
where
  go (t : HuffTree) (bits depth : Nat) : UInt16 × UInt8 :=
    match t with
    | .leaf s => (s, depth.toUInt8)
    | .empty => (0, 0)
    | .node z o =>
      if depth ≥ fastBits then (0, 0)
      else if bits % 2 == 0 then go z (bits / 2) (depth + 1)
      else go o (bits / 2) (depth + 1)

/-- Build the `2^fastBits`-entry decode table for `tree`: slot `i` holds the
    `(symbol, codeLen)` reached by walking `tree` on the bits of `i`. Built once
    per Huffman tree; cheap relative to the symbols decoded with it. -/
def buildTable (tree : HuffTree) : Array (UInt16 × UInt8) :=
  Array.ofFn (n := 2 ^ fastBits) (fun i : Fin (2 ^ fastBits) => tableEntry tree i.val)

/-- Bits remaining in the reader from its current `(pos, bitOff)`. -/
def bitsAvail (br : BitReader) : Nat :=
  if br.pos ≥ br.data.size then 0 else (br.data.size - br.pos) * 8 - br.bitOff

/-- Peek the next `fastBits` bits at `(pos, bitOff)`, LSB-first, without
    consuming. Bytes past the end of the stream read as zero; the caller uses
    `bitsAvail` to decide whether the looked-up code actually fits. -/
def peekFast (br : BitReader) : UInt32 :=
  let b0 : UInt32 := if br.pos < br.data.size then br.data[br.pos]!.toUInt32 else 0
  let b1 : UInt32 := if br.pos + 1 < br.data.size then br.data[br.pos + 1]!.toUInt32 else 0
  ((b0 ||| (b1 <<< 8)) >>> br.bitOff.toUInt32) &&& 0x1FF

/-- Table-driven single-symbol decode. Peeks `fastBits` bits, reads the
    `(symbol, codeLen)` from `table`, and consumes `codeLen` bits in one step.
    Falls back to the canonical `decode` tree walk for long codes (sentinel
    `codeLen = 0`) and when fewer than `codeLen` bits remain. Proven equal to
    `decode` when `table = buildTable tree` (`Zip.Spec.InflateTable`). -/
def decodeWithTable (tree : HuffTree) (table : Array (UInt16 × UInt8))
    (br : BitReader) : Except String (UInt16 × BitReader) :=
  -- `bitOff ≥ 8` is unreachable for a well-formed reader (every `readBit`
  -- leaves `bitOff < 8`); the guard makes the equality with `decode`
  -- unconditional, so the proof transfer needs no side conditions.
  if br.bitOff ≥ 8 then tree.decode br
  else
    let idx := (peekFast br).toNat
    let entry := table[idx]!
    let len := entry.2.toNat
    if len == 0 || len > bitsAvail br then
      tree.decode br
    else
      let total := br.bitOff + len
      .ok (entry.1, { br with pos := br.pos + total / 8, bitOff := total % 8 })

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

@[simp] theorem lengthBase_size : lengthBase.size = 29 := by decide
@[simp] theorem lengthExtra_size : lengthExtra.size = 29 := by decide

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

@[simp] theorem distBase_size : distBase.size = 30 := by decide
@[simp] theorem distExtra_size : distExtra.size = 30 := by decide

/-- Copy `length` bytes from `buf` starting at `start`, repeating every
    `distance` bytes (LZ77 back-reference copy with wrap-around).
    Defined as explicit recursion for proof tractability. -/
def copyLoop (buf : ByteArray) (start distance : Nat)
    (k length : Nat)
    (hd_pos : distance > 0 := by omega) (hsd : start + distance ≤ buf.size := by omega) : ByteArray :=
  if k < length then
    have hidx : start + (k % distance) < buf.size := by
      have := Nat.mod_lt k hd_pos; omega
    copyLoop (buf.push buf[start + (k % distance)]) start distance (k + 1) length
      hd_pos (by simp [ByteArray.size_push]; omega)
  else buf
termination_by length - k

-- Code length alphabet order for dynamic Huffman (RFC 1951 §3.2.7)
def codeLengthOrder : Array Nat := #[
  16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15
]

@[simp] theorem codeLengthOrder_size : codeLengthOrder.size = 19 := by decide

/-- Fill `count` consecutive entries starting at `idx` with `val`,
    stopping when `idx ≥ bound`. Returns updated array and new index. -/
def fillEntries (arr : Array UInt8) (idx count bound : Nat) (val : UInt8) :
    Array UInt8 × Nat :=
  if count = 0 ∨ idx ≥ bound then (arr, idx)
  else fillEntries (arr.set! idx val) (idx + 1) (count - 1) bound val
termination_by count

private theorem fillEntries_snd_eq (arr : Array UInt8) (idx count bound : Nat) (val : UInt8)
    (h : idx + count ≤ bound) :
    (fillEntries arr idx count bound val).snd = idx + count := by
  induction count generalizing arr idx with
  | zero => simp [fillEntries]
  | succ n ih =>
    unfold fillEntries
    simp only [Nat.succ_ne_zero, false_or, show ¬(idx ≥ bound) from by omega,
               ↓reduceIte, Nat.add_sub_cancel]
    rw [ih (arr.set! idx val) (idx + 1) (by omega)]; omega

/-- Read code length code lengths: 3 bits each at permuted positions.
    Defined as explicit recursion for proof tractability. -/
def readCLCodeLengths (br : BitReader) (clLengths : Array UInt8)
    (i numCodeLen : Nat) : Except String (Array UInt8 × BitReader) :=
  if i < numCodeLen then do
    if h_i : i < codeLengthOrder.size then
      let (v, br) ← br.readBits 3
      readCLCodeLengths br (clLengths.set! (codeLengthOrder[i]) v.toUInt8) (i + 1) numCodeLen
    else
      throw "Inflate: code length index out of bounds"
  else
    .ok (clLengths, br)
termination_by numCodeLen - i

/-- Decode code lengths using the CL Huffman tree (RFC 1951 §3.2.7).
    Processes symbols: 0–15 (literal length), 16 (repeat previous),
    17 (repeat 0, short), 18 (repeat 0, long).
    Defined as explicit recursion for proof tractability. -/
def decodeCLSymbols (clTree : HuffTree) (br : BitReader)
    (codeLengths : Array UInt8) (idx totalCodes : Nat)
    : Except String (Array UInt8 × BitReader) :=
  if idx ≥ totalCodes then .ok (codeLengths, br)
  else do
    let (sym, br) ← clTree.decode br
    if sym < 16 then
      decodeCLSymbols clTree br (codeLengths.set! idx sym.toUInt8) (idx + 1) totalCodes
    else if sym == 16 then
      if idx == 0 then throw "Inflate: repeat code at start"
      if h_cl : idx - 1 < codeLengths.size then do
        let (rep, br) ← br.readBits 2
        let prev := codeLengths[idx - 1]
        let count := rep.toNat + 3
        if idx + count > totalCodes then throw "Inflate: repeat code exceeds total"
        decodeCLSymbols clTree br (fillEntries codeLengths idx count totalCodes prev).1
          (idx + count) totalCodes
      else throw "Inflate: repeat code index out of bounds"
    else if sym == 17 then
      let (rep, br) ← br.readBits 3
      let count := rep.toNat + 3
      if idx + count > totalCodes then throw "Inflate: repeat code exceeds total"
      decodeCLSymbols clTree br (fillEntries codeLengths idx count totalCodes 0).1
        (idx + count) totalCodes
    else if sym == 18 then
      let (rep, br) ← br.readBits 7
      let count := rep.toNat + 11
      if idx + count > totalCodes then throw "Inflate: repeat code exceeds total"
      decodeCLSymbols clTree br (fillEntries codeLengths idx count totalCodes 0).1
        (idx + count) totalCodes
    else
      throw s!"Inflate: invalid code length symbol {sym}"
termination_by totalCodes - idx
decreasing_by all_goals omega

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
    0 totalCodes
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
    Uses well-founded recursion on the remaining bits in the stream. -/
protected def decodeHuffman (br : BitReader) (output : ByteArray)
    (litTree distTree : HuffTree) (maxOutputSize : Nat)
    : Except String (ByteArray × BitReader) :=
  go br.data.size br output
where
  go (dataSize : Nat) (br : BitReader) (output : ByteArray)
      : Except String (ByteArray × BitReader) := do
    let (sym, br₁) ← litTree.decode br
    if sym < 256 then
      if output.size ≥ maxOutputSize then
        throw "Inflate: output exceeds maximum size"
      -- Guard: bit position must advance for WF termination
      if _h₁ : br₁.bitPos ≤ br.bitPos then
        throw "Inflate: no progress in Huffman decode"
      else if _h₂ : dataSize * 8 < br₁.bitPos then
        throw "Inflate: bit position out of range"
      else
        go dataSize br₁ (output.push sym.toUInt8)
    else if sym == 256 then
      .ok (output, br₁)
    else
      -- Length code 257–285
      let idx := sym.toNat - 257
      if h : idx ≥ lengthBase.size then
        throw s!"Inflate: invalid length code {sym}"
      else
      let base := lengthBase[idx]
      let extra := lengthExtra[idx]'(by simp [lengthExtra_size, lengthBase_size] at h ⊢; omega)
      let (extraBits, br₂) ← br₁.readBits extra.toNat
      let length := base.toNat + extraBits.toNat
      -- Distance code
      let (distSym, br₃) ← distTree.decode br₂
      let dIdx := distSym.toNat
      if h : dIdx ≥ distBase.size then
        throw s!"Inflate: invalid distance code {distSym}"
      else
      let dBase := distBase[dIdx]
      let dExtra := distExtra[dIdx]'(by simp [distExtra_size, distBase_size] at h ⊢; omega)
      let (dExtraBits, br₄) ← br₃.readBits dExtra.toNat
      let distance := dBase.toNat + dExtraBits.toNat
      -- Copy from output buffer (LZ77 back-reference)
      if hd0 : distance = 0 then
        throw s!"Inflate: zero back-reference distance"
      else if hds : distance > output.size then
        throw s!"Inflate: distance {distance} exceeds output size {output.size}"
      else if output.size + length > maxOutputSize then
        throw "Inflate: output exceeds maximum size"
      else
      let start := output.size - distance
      let out := copyLoop output start distance 0 length
        (by omega) (by omega)
      -- Guard: bit position must advance for WF termination
      if _h₁ : br₄.bitPos ≤ br.bitPos then
        throw "Inflate: no progress in Huffman decode"
      else if _h₂ : dataSize * 8 < br₄.bitPos then
        throw "Inflate: bit position out of range"
      else
        go dataSize br₄ out
  termination_by dataSize * 8 - br.bitPos
  decreasing_by all_goals omega

/-- Table-driven variant of `decodeHuffman`: identical to it except the two
    Huffman symbol decodes go through `decodeWithTable` (fast-bits lookup table)
    instead of the bit-by-bit `HuffTree.decode` walk. The literal/length and
    distance tables are built once, up front, then reused for every symbol in
    the block. Proven equal to `decodeHuffman` symbol-by-symbol through
    `HuffTree.decodeWithTable_eq` (see `decodeHuffmanFast_eq`); the bit-by-bit
    walk stays the canonical spec, so every existing inflate correctness proof
    transfers with a single rewrite. -/
protected def decodeHuffmanFast (br : BitReader) (output : ByteArray)
    (litTree distTree : HuffTree) (maxOutputSize : Nat)
    : Except String (ByteArray × BitReader) :=
  go litTree.buildTable distTree.buildTable br.data.size br output
where
  go (litTable distTable : Array (UInt16 × UInt8))
      (dataSize : Nat) (br : BitReader) (output : ByteArray)
      : Except String (ByteArray × BitReader) := do
    let (sym, br₁) ← litTree.decodeWithTable litTable br
    if sym < 256 then
      if output.size ≥ maxOutputSize then
        throw "Inflate: output exceeds maximum size"
      else if _h₁ : br₁.bitPos ≤ br.bitPos then
        throw "Inflate: no progress in Huffman decode"
      else if _h₂ : dataSize * 8 < br₁.bitPos then
        throw "Inflate: bit position out of range"
      else
        go litTable distTable dataSize br₁ (output.push sym.toUInt8)
    else if sym == 256 then
      .ok (output, br₁)
    else
      let idx := sym.toNat - 257
      if h : idx ≥ lengthBase.size then
        throw s!"Inflate: invalid length code {sym}"
      else
      let base := lengthBase[idx]
      let extra := lengthExtra[idx]'(by simp [lengthExtra_size, lengthBase_size] at h ⊢; omega)
      let (extraBits, br₂) ← br₁.readBits extra.toNat
      let length := base.toNat + extraBits.toNat
      let (distSym, br₃) ← distTree.decodeWithTable distTable br₂
      let dIdx := distSym.toNat
      if h : dIdx ≥ distBase.size then
        throw s!"Inflate: invalid distance code {distSym}"
      else
      let dBase := distBase[dIdx]
      let dExtra := distExtra[dIdx]'(by simp [distExtra_size, distBase_size] at h ⊢; omega)
      let (dExtraBits, br₄) ← br₃.readBits dExtra.toNat
      let distance := dBase.toNat + dExtraBits.toNat
      if hd0 : distance = 0 then
        throw s!"Inflate: zero back-reference distance"
      else if hds : distance > output.size then
        throw s!"Inflate: distance {distance} exceeds output size {output.size}"
      else if output.size + length > maxOutputSize then
        throw "Inflate: output exceeds maximum size"
      else
      let start := output.size - distance
      let out := copyLoop output start distance 0 length
        (by omega) (by omega)
      if _h₁ : br₄.bitPos ≤ br.bitPos then
        throw "Inflate: no progress in Huffman decode"
      else if _h₂ : dataSize * 8 < br₄.bitPos then
        throw "Inflate: bit position out of range"
      else
        go litTable distTable dataSize br₄ out
  termination_by dataSize * 8 - br.bitPos
  decreasing_by all_goals omega

/-- Block loop for DEFLATE decompression. Decodes blocks until a final block
    is seen. Uses well-founded recursion on the remaining bits in the stream. -/
def inflateLoop (br : BitReader) (output : ByteArray)
    (fixedLit fixedDist : HuffTree) (maxOutputSize : Nat)
    (dataSize : Nat) : Except String (ByteArray × Nat) := do
    let (bfinal, br₁) ← br.readBits 1
    let (btype, br₂) ← br₁.readBits 2
    let (output', br') ← match btype with
      | 0 => Inflate.decodeStored br₂ output maxOutputSize
      | 1 => Inflate.decodeHuffmanFast br₂ output fixedLit fixedDist maxOutputSize
      | 2 => do
        let (litTree, distTree, br₃) ← decodeDynamicTrees br₂
        Inflate.decodeHuffmanFast br₃ output litTree distTree maxOutputSize
      | _ => throw s!"Inflate: reserved block type {btype}"
    if bfinal == 1 then
      let aligned := br'.alignToByte
      return (output', aligned.pos)
    else
      -- Guard: bit position must advance for WF termination
      if _h₁ : br'.bitPos ≤ br.bitPos then
        throw "Inflate: no progress in inflate loop"
      else if _h₂ : dataSize * 8 < br'.bitPos then
        throw "Inflate: bit position out of range"
      else
        inflateLoop br' output' fixedLit fixedDist maxOutputSize dataSize
termination_by dataSize * 8 - br.bitPos
decreasing_by all_goals omega

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
  inflateLoop br .empty fixedLit fixedDist maxOutputSize data.size

/-- Inflate a raw DEFLATE stream. Processes blocks until a final block is seen.
    `maxOutputSize` (default 1 GiB) caps decompressed output as a zip-bomb
    guard. Unlike the FFI path, where `maxDecompressedSize := 0` means
    unlimited, here `0` rejects any non-empty output (the comparison is
    `output.size + len > maxOutputSize`, so even a single produced byte
    exceeds the bound). Overflow raises an `Except` error containing
    `"Inflate: output exceeds maximum size"`.
    See `SECURITY_INVENTORY.md` *Decompression Limit Inventory*. -/
def inflate (data : ByteArray) (maxOutputSize : Nat := 1024 * 1024 * 1024) :
    Except String ByteArray := do
  let (output, _) ← inflateRaw data 0 maxOutputSize
  return output

end Inflate
end Zip.Native
