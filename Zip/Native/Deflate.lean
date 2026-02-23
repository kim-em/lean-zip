/-
  Pure Lean DEFLATE compressor.

  Level 0: stored blocks (uncompressed).
  Level 1: greedy LZ77 matching with fixed Huffman codes.
  Level 2: lazy LZ77 matching with fixed Huffman codes.
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
    Returns array indexed by symbol of (codeword, code_length).
    Assumes all non-zero lengths are ≤ `maxBits` (15 for DEFLATE). -/
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

/-- Search a base/extra table pair for the code covering `value`.
    Returns (code_index, extra_bits_count, extra_bits_value).
    Used for both length codes (RFC 1951 §3.2.5) and distance codes. -/
private def findTableCode (baseTable : Array UInt16) (extraTable : Array UInt8)
    (value : Nat) : Option (Nat × Nat × UInt32) :=
  go 0
where
  go (i : Nat) : Option (Nat × Nat × UInt32) :=
    if i + 1 < baseTable.size then
      if baseTable[i + 1]!.toNat > value then
        -- i < extraTable.size follows from baseTable/extraTable having equal size
        let extra := extraTable[i]!.toNat
        let extraVal := (value - baseTable[i]!.toNat).toUInt32
        some (i, extra, extraVal)
      else
        go (i + 1)
    else if i < baseTable.size then
      let extra := extraTable[i]!.toNat
      let extraVal := (value - baseTable[i]!.toNat).toUInt32
      some (i, extra, extraVal)
    else
      none
  termination_by baseTable.size - i

/-- Find length code for length 3–258.
    Returns (code_index 0–28, extra_bits_count, extra_bits_value). -/
def findLengthCode (length : Nat) : Option (Nat × Nat × UInt32) :=
  findTableCode Inflate.lengthBase Inflate.lengthExtra length

/-- Find distance code for distance 1–32768.
    Returns (code 0–29, extra_bits_count, extra_bits_value). -/
def findDistCode (dist : Nat) : Option (Nat × Nat × UInt32) :=
  findTableCode Inflate.distBase Inflate.distExtra dist

inductive LZ77Token where
  | literal : UInt8 → LZ77Token
  | reference : (length : Nat) → (distance : Nat) → LZ77Token

/-- Simple hash-based greedy LZ77 matcher.
    Scans input left-to-right, emitting literals or back-references. -/
def lz77Greedy (data : ByteArray) (windowSize : Nat := 32768) :
    Array LZ77Token :=
  if data.size < 3 then
    (trailing data 0).toArray
  else
    let hashSize := 65536
    (mainLoop data windowSize hashSize
      (.replicate hashSize 0) (.replicate hashSize false) 0).toArray
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
  trailing (data : ByteArray) (pos : Nat) : List LZ77Token :=
    if pos < data.size then
      .literal data[pos]! :: trailing data (pos + 1)
    else []
  termination_by data.size - pos
  updateHashes (data : ByteArray) (hashSize : Nat)
      (hashTable : Array Nat) (hashValid : Array Bool)
      (pos j matchLen : Nat) : Array Nat × Array Bool :=
    if j < matchLen then
      if pos + j + 2 < data.size then
        let h := hash3 data (pos + j) hashSize
        updateHashes data hashSize (hashTable.set! h (pos + j)) (hashValid.set! h true)
          pos (j + 1) matchLen
      else
        updateHashes data hashSize hashTable hashValid pos (j + 1) matchLen
    else
      (hashTable, hashValid)
  termination_by matchLen - j
  mainLoop (data : ByteArray) (windowSize hashSize : Nat)
      (hashTable : Array Nat) (hashValid : Array Bool) (pos : Nat) :
      List LZ77Token :=
    if hlt : pos + 2 < data.size then
      let h := hash3 data pos hashSize
      let matchPos := hashTable[h]!
      let isValid := hashValid[h]!
      let hashTable := hashTable.set! h pos
      let hashValid := hashValid.set! h true
      if isValid && matchPos < pos && pos - matchPos ≤ windowSize then
        let maxLen := min 258 (data.size - pos)
        let matchLen := countMatch data matchPos pos maxLen
        if hge : matchLen ≥ 3 then
          if hle : pos + matchLen ≤ data.size then
            have : data.size - (pos + matchLen) < data.size - pos := by omega
            let (hashTable, hashValid) :=
              updateHashes data hashSize hashTable hashValid pos 1 matchLen
            .reference matchLen (pos - matchPos) ::
              mainLoop data windowSize hashSize hashTable hashValid (pos + matchLen)
          else
            .literal data[pos]! ::
              mainLoop data windowSize hashSize hashTable hashValid (pos + 1)
        else
          .literal data[pos]! ::
            mainLoop data windowSize hashSize hashTable hashValid (pos + 1)
      else
        .literal data[pos]! ::
          mainLoop data windowSize hashSize hashTable hashValid (pos + 1)
    else
      trailing data pos
  termination_by data.size - pos
  decreasing_by all_goals omega

/-- Emit LZ77 tokens as fixed Huffman codes into a BitWriter. -/
def emitTokens (bw : BitWriter) (tokens : Array LZ77Token) (i : Nat) : BitWriter :=
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
        | none => emitTokens bw tokens (i + 1)
      | none => emitTokens bw tokens (i + 1)
  else bw
termination_by tokens.size - i

/-- Write a fixed Huffman DEFLATE block from LZ77 tokens. -/
private def deflateFixedBlock (data : ByteArray) (tokens : Array LZ77Token) : ByteArray :=
  let bw := BitWriter.empty
  let bw := bw.writeBits 1 1  -- BFINAL
  let bw := bw.writeBits 2 1  -- BTYPE = 01
  if data.size == 0 then
    let (code, len) := fixedLitCodes[256]!
    let bw := bw.writeHuffCode code len
    bw.flush
  else
    let bw := emitTokens bw tokens 0
    let (code, len) := fixedLitCodes[256]!
    let bw := bw.writeHuffCode code len
    bw.flush

/-- Compress data using fixed Huffman codes and greedy LZ77 (Level 1).
    Produces a single DEFLATE block with BFINAL=1, BTYPE=01. -/
def deflateFixed (data : ByteArray) : ByteArray :=
  deflateFixedBlock data (lz77Greedy data)

/-- Simple hash-based lazy LZ77 matcher.
    Like `lz77Greedy`, but checks if position pos+1 has a longer match
    before committing. If so, emits a literal for pos and the longer
    match at pos+1. -/
def lz77Lazy (data : ByteArray) (windowSize : Nat := 32768) :
    Array LZ77Token :=
  if data.size < 3 then
    (trailing data 0).toArray
  else
    let hashSize := 65536
    (mainLoop data windowSize hashSize
      (.replicate hashSize 0) (.replicate hashSize false) 0).toArray
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
  trailing (data : ByteArray) (pos : Nat) : List LZ77Token :=
    if pos < data.size then
      .literal data[pos]! :: trailing data (pos + 1)
    else []
  termination_by data.size - pos
  updateHashes (data : ByteArray) (hashSize : Nat)
      (hashTable : Array Nat) (hashValid : Array Bool)
      (pos j matchLen : Nat) : Array Nat × Array Bool :=
    if j < matchLen then
      if pos + j + 2 < data.size then
        let h := hash3 data (pos + j) hashSize
        updateHashes data hashSize (hashTable.set! h (pos + j)) (hashValid.set! h true)
          pos (j + 1) matchLen
      else
        updateHashes data hashSize hashTable hashValid pos (j + 1) matchLen
    else
      (hashTable, hashValid)
  termination_by matchLen - j
  mainLoop (data : ByteArray) (windowSize hashSize : Nat)
      (hashTable : Array Nat) (hashValid : Array Bool) (pos : Nat) :
      List LZ77Token :=
    if hlt : pos + 2 < data.size then
      let h := hash3 data pos hashSize
      let matchPos := hashTable[h]!
      let isValid := hashValid[h]!
      let hashTable := hashTable.set! h pos
      let hashValid := hashValid.set! h true
      if isValid && matchPos < pos && pos - matchPos ≤ windowSize then
        let maxLen := min 258 (data.size - pos)
        let matchLen := countMatch data matchPos pos maxLen
        if hge : matchLen ≥ 3 then
          if hle : pos + matchLen ≤ data.size then
            -- Lazy: check pos + 1 for a longer match
            if pos + 3 < data.size then
              let h2 := hash3 data (pos + 1) hashSize
              let matchPos2 := hashTable[h2]!
              let isValid2 := hashValid[h2]!
              if isValid2 && matchPos2 < pos + 1 && pos + 1 - matchPos2 ≤ windowSize then
                let maxLen2 := min 258 (data.size - (pos + 1))
                let matchLen2 := countMatch data matchPos2 (pos + 1) maxLen2
                if matchLen2 > matchLen then
                  if hle2 : pos + 1 + matchLen2 ≤ data.size then
                    -- Better match at pos+1: emit literal + reference
                    have : data.size - (pos + 1 + matchLen2) < data.size - pos := by omega
                    let (ht, hv) := updateHashes data hashSize hashTable hashValid pos 1 matchLen2
                    .literal data[pos]! ::
                      .reference matchLen2 (pos + 1 - matchPos2) ::
                      mainLoop data windowSize hashSize ht hv (pos + 1 + matchLen2)
                  else
                    -- matchLen2 exceeds data: fall back to match at pos
                    have : data.size - (pos + matchLen) < data.size - pos := by omega
                    let (ht, hv) := updateHashes data hashSize hashTable hashValid pos 1 matchLen
                    .reference matchLen (pos - matchPos) ::
                      mainLoop data windowSize hashSize ht hv (pos + matchLen)
                else
                  -- Keep match at pos (no better match at pos+1)
                  have : data.size - (pos + matchLen) < data.size - pos := by omega
                  let (ht, hv) := updateHashes data hashSize hashTable hashValid pos 1 matchLen
                  .reference matchLen (pos - matchPos) ::
                    mainLoop data windowSize hashSize ht hv (pos + matchLen)
              else
                -- No valid match at pos+1: keep match at pos
                have : data.size - (pos + matchLen) < data.size - pos := by omega
                let (ht, hv) := updateHashes data hashSize hashTable hashValid pos 1 matchLen
                .reference matchLen (pos - matchPos) ::
                  mainLoop data windowSize hashSize ht hv (pos + matchLen)
            else
              -- Near end of data: keep match at pos
              have : data.size - (pos + matchLen) < data.size - pos := by omega
              .reference matchLen (pos - matchPos) ::
                mainLoop data windowSize hashSize hashTable hashValid (pos + matchLen)
          else
            .literal data[pos]! ::
              mainLoop data windowSize hashSize hashTable hashValid (pos + 1)
        else
          .literal data[pos]! ::
            mainLoop data windowSize hashSize hashTable hashValid (pos + 1)
      else
        .literal data[pos]! ::
          mainLoop data windowSize hashSize hashTable hashValid (pos + 1)
    else
      trailing data pos
  termination_by data.size - pos
  decreasing_by all_goals omega

/-- Compress data using fixed Huffman codes and lazy LZ77 (Level 2).
    Produces a single DEFLATE block with BFINAL=1, BTYPE=01. -/
def deflateLazy (data : ByteArray) : ByteArray :=
  deflateFixedBlock data (lz77Lazy data)

end Zip.Native.Deflate
