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

/-- Allocation-light `BitReader.readBits`: thread the cursor `(pos, bitOff)` as
    unboxed `Nat`s and build the `BitReader` struct **once** at the end, instead
    of allocating a fresh `BitReader` (+ `Except`/pair) on every bit as the
    `readBit`-looping `BitReader.readBits` does. Same per-bit byte reads, but a
    whole `n`-bit field now costs O(1) heap allocations instead of O(n). Proven
    equal to `BitReader.readBits` (`readBitsFast_eq`); used on the hot
    extra-bits path in `decodeHuffmanFast`. -/
def readBitsFast (br : BitReader) (n : Nat) : Except String (UInt32 × BitReader) :=
  go br.pos br.bitOff 0 0 n
where
  go (pos bitOff : Nat) (acc : UInt32) (shift : Nat) :
      Nat → Except String (UInt32 × BitReader)
    | 0 => .ok (acc, { br with pos := pos, bitOff := bitOff })
    | k + 1 =>
      if pos ≥ br.data.size then .error "BitReader: unexpected end of input"
      else
        let bit : UInt32 := ((br.data[pos]!.toUInt32 >>> bitOff.toUInt32) &&& 1)
        if bitOff + 1 ≥ 8 then
          go (pos + 1) 0 (acc ||| (bit <<< shift.toUInt32)) (shift + 1) k
        else
          go pos (bitOff + 1) (acc ||| (bit <<< shift.toUInt32)) (shift + 1) k

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

/-- The per-byte back-reference copy worker: copy `length` bytes from `buf`
    starting at `start`, repeating every `distance` bytes (LZ77 copy with
    wrap-around). Defined as explicit recursion for proof tractability; this is
    the reference semantics that `copyLoop` dispatches to. -/
def copyLoopGo (buf : ByteArray) (start distance : Nat)
    (k length : Nat)
    (hd_pos : distance > 0 := by omega) (hsd : start + distance ≤ buf.size := by omega) : ByteArray :=
  if k < length then
    have hidx : start + (k % distance) < buf.size := by
      have := Nat.mod_lt k hd_pos; omega
    copyLoopGo (buf.push buf[start + (k % distance)]) start distance (k + 1) length
      hd_pos (by simp [ByteArray.size_push]; omega)
  else buf
termination_by length - k

/-- Periodic extension of a non-empty `seed` window to at least `length` bytes by
    repeated doubling — each step is a `ByteArray` append (a `memcpy`), so the
    whole fill is `O(log (length / seed.size))` memcpys. `seed` is the
    `distance`-byte back-reference window; doubling it preserves the period
    (`seed.size` always divides the running size), so slot `i` of the result is
    `seed[i % seed.size]`. Used by `copyLoop` for overlapping LZ77
    back-references (`distance < length`, e.g. RLE), where a per-byte copy
    otherwise dominates decode of highly repetitive data. -/
def fillDouble (seed : ByteArray) (length : Nat) : ByteArray :=
  if seed.size ≥ length ∨ seed.size = 0 then seed
  else fillDouble (seed ++ seed) length
termination_by length - seed.size
decreasing_by
  simp only [ByteArray.size_append]
  omega

/-- Copy `length` bytes from `buf` starting at `start`, repeating every
    `distance` bytes (LZ77 back-reference copy).

    For the common **non-overlapping** back-reference (`k = 0 ∧ length ≤ distance`)
    every index `start + (k % distance)` is just `start + k`, so the whole copy is
    the contiguous slice `[start, start + length)` — one `extract` + one `append`
    (a `memcpy`) instead of `length` per-byte `push`es / bounds-checks / modular
    indices. For an **overlapping** back-reference (`k = 0 ∧ length > distance`,
    the RLE case) the copy is the periodic extension of the `distance`-byte window,
    built by `fillDouble` (a handful of memcpys) instead of `length` per-byte
    `push`es. A partial copy (`k ≠ 0`, never produced by the decoders) falls back
    to the per-byte `copyLoopGo`. All three are proven equal to `copyLoopGo` via
    `copyLoop_eq_ofFn`, so every decode correctness proof is unaffected. -/
def copyLoop (buf : ByteArray) (start distance : Nat)
    (k length : Nat)
    (hd_pos : distance > 0 := by omega) (hsd : start + distance ≤ buf.size := by omega) : ByteArray :=
  if k = 0 ∧ length ≤ distance then
    buf ++ buf.extract start (start + length)
  else if k = 0 then
    buf ++ (fillDouble (buf.extract start (start + distance)) length).extract 0 length
  else
    copyLoopGo buf start distance k length hd_pos hsd

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
    `HuffTree.decodeWithTable_eq` (see `decodeHuffmanFastBR_eq`).

    This is the **BitReader reference** decoder. The default `decodeHuffmanFast`
    (below) delegates to the faster wide-buffer `InflateBuf.decodeHuffmanFastBuf`,
    which is proven equal to *this* (`decodeHuffmanFastBuf_eq`); composing the two
    equalities gives `decodeHuffmanFast = decodeHuffman`, so the bit-by-bit walk
    stays the canonical spec and every inflate correctness proof transfers. -/
protected def decodeHuffmanFastBR (br : BitReader) (output : ByteArray)
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
      let (extraBits, br₂) ← readBitsFast br₁ extra.toNat
      let length := base.toNat + extraBits.toNat
      let (distSym, br₃) ← distTree.decodeWithTable distTable br₂
      let dIdx := distSym.toNat
      if h : dIdx ≥ distBase.size then
        throw s!"Inflate: invalid distance code {distSym}"
      else
      let dBase := distBase[dIdx]
      let dExtra := distExtra[dIdx]'(by simp [distExtra_size, distBase_size] at h ⊢; omega)
      let (dExtraBits, br₄) ← readBitsFast br₃ dExtra.toNat
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

end Inflate

/-!
## Wide-buffer Huffman decoder primitives (Track D, #2501)

Thread the bit cursor as unboxed scalars `(pos, bitBuf : UInt64, cnt)` — plus a
`bitpos` measure for termination — through the whole Huffman symbol loop,
refilling up to 57 bits at a time and consuming by shift, instead of allocating
a fresh `BitReader` per field read. `Zip.Spec.InflateBufCorrect` proves
`decodeHuffmanFastBuf` equal to the BitReader reference `Inflate.decodeHuffmanFastBR`
(for depth-≤15 trees and a well-formed reader), so the default `inflateLoop` adopts
it with no trust gap (no `@[extern]`, no `@[implemented_by]`).
-/
namespace InflateBuf
open ZipCommon (BitReader)

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

/-- Read `n` bits LSB-first from the buffer without refilling. Errors (like
    `readBitsFast`) when the buffer holds fewer than `n` bits — for a refilled
    buffer this only fires at true end-of-input on a truncated stream. -/
@[inline] def takeBits (bitBuf : UInt64) (cnt n : Nat) : Except String (Nat × UInt64 × Nat) :=
  if n > cnt then .error "BitReader: unexpected end of input"
  else
    let v := (bitBuf &&& ((1 <<< n.toUInt64) - 1)).toNat
    .ok (v, bitBuf >>> n.toUInt64, cnt - n)

set_option maxRecDepth 4096 in
/-- Wide-buffer Huffman symbol loop (mirrors `Inflate.decodeHuffmanFastBR.go`).
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
        let (extraBits, bitBuf, cnt) ← takeBits bitBuf cnt extra.toNat
        let length := base.toNat + extraBits
        match decodeSym distTree distTable bitBuf cnt with
        | .error e => .error e
        | .ok (distSym, bitBuf, cnt, _dused) =>
          let dIdx := distSym.toNat
          if h : dIdx ≥ Inflate.distBase.size then throw s!"Inflate: invalid distance code {distSym}"
          else
            let dBase := Inflate.distBase[dIdx]
            let dExtra := Inflate.distExtra[dIdx]'(by simp [Inflate.distExtra_size, Inflate.distBase_size] at h ⊢; omega)
            let (dExtraBits, bitBuf, cnt) ← takeBits bitBuf cnt dExtra.toNat
            let distance := dBase.toNat + dExtraBits
            if h0 : distance = 0 then throw s!"Inflate: zero back-reference distance"
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

/-- Wide-buffer replacement for `Inflate.decodeHuffmanFastBR`: convert the
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

end InflateBuf

namespace Inflate

/-- The fast Huffman block decoder used by `inflateLoop`: delegates to the
    wide-buffer implementation `InflateBuf.decodeHuffmanFastBuf`, which is proven
    equal to the BitReader reference `decodeHuffmanFastBR` and hence to the
    canonical `decodeHuffman` (`Zip.Spec.InflateBufCorrect.decodeHuffmanFast_eq`).
    Same signature as `decodeHuffmanFastBR`, so `inflateLoop`'s body and every
    downstream correctness proof transfer with a single (now conditional) rewrite. -/
protected def decodeHuffmanFast (br : BitReader) (output : ByteArray)
    (litTree distTree : HuffTree) (maxOutputSize : Nat)
    : Except String (ByteArray × BitReader) :=
  InflateBuf.decodeHuffmanFastBuf br output litTree distTree maxOutputSize

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
