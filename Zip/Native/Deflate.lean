/-
  Pure Lean DEFLATE compressor.

  Level 0: stored blocks (uncompressed).
  Level 1: greedy LZ77 matching with fixed Huffman codes.
-/
import Zip.Native.BitWriter
import Zip.Native.Inflate

namespace Zip.Native.Deflate

/-- Maximum data bytes per stored block (2^16 - 1). -/
private def maxBlockSize : Nat := 65535

/-- Compress data into raw DEFLATE stored blocks (level 0).
    Splits into blocks of at most 65535 bytes. Each block has:
    - 1 byte: BFINAL (bit 0) | BTYPE=00 (bits 1-2), rest zero
    - 2 bytes LE: LEN (number of data bytes)
    - 2 bytes LE: NLEN (one's complement of LEN)
    - LEN bytes: raw data

    Empty input produces one final stored block with LEN=0. -/
def deflateStored (data : ByteArray) : ByteArray := Id.run do
  let mut result := ByteArray.empty
  if data.size == 0 then
    -- Empty: one final stored block with LEN=0
    result := result.push 0x01  -- BFINAL=1, BTYPE=00
    result := result.push 0x00  -- LEN low
    result := result.push 0x00  -- LEN high
    result := result.push 0xFF  -- NLEN low
    result := result.push 0xFF  -- NLEN high
    return result
  let mut pos := 0
  while pos < data.size do
    let remaining := data.size - pos
    let blockSize := min remaining maxBlockSize
    let isFinal := pos + blockSize >= data.size
    -- Header byte: BFINAL (bit 0), BTYPE=00 (bits 1-2)
    result := result.push (if isFinal then 0x01 else 0x00)
    -- LEN (16-bit LE)
    let len := blockSize.toUInt16
    result := result.push (len &&& 0xFF).toUInt8
    result := result.push ((len >>> 8) &&& 0xFF).toUInt8
    -- NLEN (one's complement of LEN, 16-bit LE)
    let nlen := len ^^^ 0xFFFF
    result := result.push (nlen &&& 0xFF).toUInt8
    result := result.push ((nlen >>> 8) &&& 0xFF).toUInt8
    -- Raw data
    result := result ++ data.extract pos (pos + blockSize)
    pos := pos + blockSize
  return result

/-- Compute canonical Huffman codewords from code lengths (RFC 1951 §3.2.2).
    Returns array indexed by symbol of (codeword, code_length). -/
def canonicalCodes (lengths : Array UInt8) (maxBits : Nat := 15) :
    Array (UInt16 × UInt8) :=
  let lsList := lengths.toList.map UInt8.toNat
  let blCount := Huffman.Spec.countLengths lsList maxBits
  let ncNat := Huffman.Spec.nextCodes blCount maxBits
  let nextCode : Array UInt32 := ncNat.map fun n => n.toUInt32
  go lengths nextCode 0 (Array.replicate lengths.size (0, 0))
where
  go (lengths : Array UInt8) (nextCode : Array UInt32) (i : Nat)
      (result : Array (UInt16 × UInt8)) : Array (UInt16 × UInt8) :=
    if h : i < lengths.size then
      let len := lengths[i]
      if len > 0 then
        let code := nextCode[len.toNat]!
        let result' := result.set! i (code.toUInt16, len)
        let nextCode' := nextCode.set! len.toNat (code + 1)
        go lengths nextCode' (i + 1) result'
      else
        go lengths nextCode (i + 1) result
    else result
  termination_by lengths.size - i

def fixedLitCodes : Array (UInt16 × UInt8) :=
  canonicalCodes Inflate.fixedLitLengths

def fixedDistCodes : Array (UInt16 × UInt8) :=
  canonicalCodes Inflate.fixedDistLengths

/-- Find length code for length 3–258.
    Returns (code_index 0–28, extra_bits_count, extra_bits_value). -/
def findLengthCode (length : Nat) : Option (Nat × Nat × UInt32) :=
  go 0
where
  go (i : Nat) : Option (Nat × Nat × UInt32) :=
    if i + 1 < Inflate.lengthBase.size then
      if Inflate.lengthBase[i + 1]!.toNat > length then
        let extra := Inflate.lengthExtra[i]!.toNat
        let extraVal := (length - Inflate.lengthBase[i]!.toNat).toUInt32
        some (i, extra, extraVal)
      else
        go (i + 1)
    else if i < Inflate.lengthBase.size then
      -- Last entry (code 28, length 258)
      let extra := Inflate.lengthExtra[i]!.toNat
      let extraVal := (length - Inflate.lengthBase[i]!.toNat).toUInt32
      some (i, extra, extraVal)
    else
      none
  termination_by Inflate.lengthBase.size - i

/-- Find distance code for distance 1–32768.
    Returns (code 0–29, extra_bits_count, extra_bits_value). -/
def findDistCode (dist : Nat) : Option (Nat × Nat × UInt32) :=
  go 0
where
  go (i : Nat) : Option (Nat × Nat × UInt32) :=
    if i + 1 < Inflate.distBase.size then
      if Inflate.distBase[i + 1]!.toNat > dist then
        let extra := Inflate.distExtra[i]!.toNat
        let extraVal := (dist - Inflate.distBase[i]!.toNat).toUInt32
        some (i, extra, extraVal)
      else
        go (i + 1)
    else if i < Inflate.distBase.size then
      let extra := Inflate.distExtra[i]!.toNat
      let extraVal := (dist - Inflate.distBase[i]!.toNat).toUInt32
      some (i, extra, extraVal)
    else
      none
  termination_by Inflate.distBase.size - i

inductive LZ77Token where
  | literal : UInt8 → LZ77Token
  | reference : (length : Nat) → (distance : Nat) → LZ77Token

/-- Simple hash-based greedy LZ77 matcher.
    Scans input left-to-right, emitting literals or back-references. -/
def lz77Greedy (data : ByteArray) (windowSize : Nat := 32768) :
    Array LZ77Token := Id.run do
  if data.size < 3 then
    let mut tokens : Array LZ77Token := #[]
    for i in [:data.size] do
      tokens := tokens.push (.literal data[i]!)
    return tokens
  let hashSize := 65536
  let mut hashTable : Array Nat := .replicate hashSize 0
  let mut hashValid : Array Bool := .replicate hashSize false
  let mut tokens : Array LZ77Token := #[]
  let mut pos := 0
  while pos + 2 < data.size do
    let h := hash3 data pos hashSize
    let matchPos := hashTable[h]!
    let isValid := hashValid[h]!
    -- Update hash table before emitting
    hashTable := hashTable.set! h pos
    hashValid := hashValid.set! h true
    if isValid && matchPos < pos && pos - matchPos ≤ windowSize then
      -- Try to extend the match
      let maxLen := min 258 (data.size - pos)
      let matchLen := countMatch data matchPos pos maxLen
      if matchLen ≥ 3 then
        tokens := tokens.push (.reference matchLen (pos - matchPos))
        -- Advance pos, updating hash table for skipped positions
        for j in [1:matchLen] do
          if pos + j + 2 < data.size then
            let h' := hash3 data (pos + j) hashSize
            hashTable := hashTable.set! h' (pos + j)
            hashValid := hashValid.set! h' true
        pos := pos + matchLen
      else
        tokens := tokens.push (.literal data[pos]!)
        pos := pos + 1
    else
      tokens := tokens.push (.literal data[pos]!)
      pos := pos + 1
  -- Emit remaining bytes as literals
  while pos < data.size do
    tokens := tokens.push (.literal data[pos]!)
    pos := pos + 1
  return tokens
where
  hash3 (data : ByteArray) (pos : Nat) (hashSize : Nat) : Nat :=
    let a := data[pos]!.toNat
    let b := data[pos + 1]!.toNat
    let c := data[pos + 2]!.toNat
    ((a ^^^ (b <<< 5) ^^^ (c <<< 10)) % hashSize)
  countMatch (data : ByteArray) (p1 p2 maxLen : Nat) : Nat :=
    go data p1 p2 0 maxLen
  go (data : ByteArray) (p1 p2 i maxLen : Nat) : Nat :=
    if i < maxLen then
      if data[p1 + i]! == data[p2 + i]! then
        go data p1 p2 (i + 1) maxLen
      else i
    else i
  termination_by maxLen - i

/-- Compress data using fixed Huffman codes and greedy LZ77 (Level 1).
    Produces a single DEFLATE block with BFINAL=1, BTYPE=01. -/
def deflateFixed (data : ByteArray) : ByteArray :=
  let bw := BitWriter.empty
  -- BFINAL=1, BTYPE=01 (fixed Huffman)
  let bw := bw.writeBits 1 1  -- BFINAL
  let bw := bw.writeBits 2 1  -- BTYPE = 01
  if data.size == 0 then
    -- Just end-of-block symbol (256)
    let (code, len) := fixedLitCodes[256]!
    let bw := bw.writeHuffCode code len
    bw.flush
  else
    let tokens := lz77Greedy data
    let bw := emitTokens bw tokens 0
    -- End-of-block symbol (256)
    let (code, len) := fixedLitCodes[256]!
    let bw := bw.writeHuffCode code len
    bw.flush
where
  emitTokens (bw : BitWriter) (tokens : Array LZ77Token) (i : Nat) : BitWriter :=
    if h : i < tokens.size then
      match tokens[i] with
      | .literal b =>
        let (code, len) := fixedLitCodes[b.toNat]!
        emitTokens (bw.writeHuffCode code len) tokens (i + 1)
      | .reference length distance =>
        match findLengthCode length with
        | some (idx, extraCount, extraVal) =>
          let (code, len) := fixedLitCodes[idx + 257]!
          let bw := bw.writeHuffCode code len
          let bw := bw.writeBits extraCount extraVal
          match findDistCode distance with
          | some (dIdx, dExtraCount, dExtraVal) =>
            let (dCode, dLen) := fixedDistCodes[dIdx]!
            let bw := bw.writeHuffCode dCode dLen
            emitTokens (bw.writeBits dExtraCount dExtraVal) tokens (i + 1)
          | none => emitTokens bw tokens (i + 1)  -- skip invalid
        | none => emitTokens bw tokens (i + 1)  -- skip invalid
    else bw
  termination_by tokens.size - i

end Zip.Native.Deflate
