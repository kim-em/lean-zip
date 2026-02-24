/-
  Native DEFLATE compressor — dynamic Huffman blocks (Level 5).

  Uses dynamic Huffman codes optimized for the input data rather than
  the fixed codes defined in RFC 1951 §3.2.6.
-/
import Zip.Native.Deflate
import Zip.Spec.DeflateEncodeDynamic
import Zip.Spec.DeflateStoredCorrect

namespace Zip.Native.Deflate

/-- Emit LZ77 tokens using the given lit/len and distance Huffman codes. -/
def emitTokensWithCodes (bw : BitWriter) (tokens : Array LZ77Token)
    (litCodes distCodes : Array (UInt16 × UInt8)) (i : Nat) : BitWriter :=
  if h : i < tokens.size then
    match tokens[i] with
    | .literal b =>
      let (code, len) := litCodes[b.toNat]!
      emitTokensWithCodes (bw.writeHuffCode code len) tokens litCodes distCodes (i + 1)
    | .reference length distance =>
      match findLengthCode length with
      | some (idx, extraCount, extraVal) =>
        let (code, len) := litCodes[idx + 257]!
        let bw := bw.writeHuffCode code len
        let bw := bw.writeBits extraCount extraVal
        match findDistCode distance with
        | some (dIdx, dExtraCount, dExtraVal) =>
          let (dCode, dLen) := distCodes[dIdx]!
          let bw := bw.writeHuffCode dCode dLen
          emitTokensWithCodes (bw.writeBits dExtraCount dExtraVal) tokens litCodes distCodes (i + 1)
        | none => emitTokensWithCodes bw tokens litCodes distCodes (i + 1)
      | none => emitTokensWithCodes bw tokens litCodes distCodes (i + 1)
  else bw
termination_by tokens.size - i

/-- Count symbol frequencies from LZ77 tokens.
    Returns `(litLenFreqs, distFreqs)` where:
    - `litLenFreqs` has 286 entries (symbols 0–285)
    - `distFreqs` has 30 entries (distance codes 0–29)
    Always includes end-of-block (symbol 256) with frequency 1. -/
def tokenFreqs (tokens : Array LZ77Token) : Array Nat × Array Nat :=
  let litLenFreqs := Array.replicate 286 0
  let distFreqs := Array.replicate 30 0
  -- Always count end-of-block
  let litLenFreqs := litLenFreqs.set! 256 1
  go tokens litLenFreqs distFreqs 0
where
  go (tokens : Array LZ77Token) (litLenFreqs distFreqs : Array Nat)
      (i : Nat) : Array Nat × Array Nat :=
    if h : i < tokens.size then
      match tokens[i] with
      | .literal b =>
        let idx := b.toNat
        let litLenFreqs := litLenFreqs.set! idx (litLenFreqs[idx]! + 1)
        go tokens litLenFreqs distFreqs (i + 1)
      | .reference length distance =>
        let litLenFreqs := match findLengthCode length with
          | some (idx, _, _) =>
            let symIdx := idx + 257
            litLenFreqs.set! symIdx (litLenFreqs[symIdx]! + 1)
          | none => litLenFreqs
        let distFreqs := match findDistCode distance with
          | some (dIdx, _, _) =>
            distFreqs.set! dIdx (distFreqs[dIdx]! + 1)
          | none => distFreqs
        go tokens litLenFreqs distFreqs (i + 1)
    else (litLenFreqs, distFreqs)
  termination_by tokens.size - i

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
  writeCLEntries bw clCodes clEntries
where
  writeCLLengths (bw : BitWriter) (clLens : List Nat) (numCodeLen i : Nat) : BitWriter :=
    if i < numCodeLen then
      let pos := Deflate.Spec.clPermutation.getD i 0
      let len := clLens.getD pos 0
      writeCLLengths (bw.writeBits 3 len.toUInt32) clLens numCodeLen (i + 1)
    else bw
  termination_by numCodeLen - i
  writeCLEntries (bw : BitWriter) (clCodes : Array (UInt16 × UInt8))
      (entries : List (Nat × Nat)) : BitWriter :=
    match entries with
    | [] => bw
    | (code, extra) :: rest =>
      let (cw, cwLen) := clCodes[code]!
      let bw := bw.writeHuffCode cw cwLen
      let bw :=
        if code == 16 then bw.writeBits 2 extra.toUInt32
        else if code == 17 then bw.writeBits 3 extra.toUInt32
        else if code == 18 then bw.writeBits 7 extra.toUInt32
        else bw
      writeCLEntries bw clCodes rest

/-- Compress data using dynamic Huffman codes and greedy LZ77 (Level 5).
    Produces a single DEFLATE block with BFINAL=1, BTYPE=10. -/
def deflateDynamic (data : ByteArray) (windowSize : Nat := 32768) : ByteArray :=
  let tokens := lz77Greedy data windowSize
  let (litFreqs, distFreqs) := tokenFreqs tokens
  -- Convert frequencies to (symbol, freq) pairs
  let litFreqPairs := (List.range litFreqs.size).map fun i => (i, litFreqs[i]!)
  let distFreqPairs := (List.range distFreqs.size).map fun i => (i, distFreqs[i]!)
  -- Compute code lengths
  let litLens := Huffman.Spec.computeCodeLengths litFreqPairs 286 15
  let distLens := Huffman.Spec.computeCodeLengths distFreqPairs 30 15
  -- Ensure at least one non-zero distance code (RFC 1951 requirement)
  let distLens :=
    if distLens.all (· == 0) then distLens.set 0 1
    else distLens
  -- Build canonical codes from computed lengths
  let litCodes := canonicalCodes (litLens.toArray.map Nat.toUInt8)
  let distCodes := canonicalCodes (distLens.toArray.map Nat.toUInt8)
  -- Write block header: BFINAL=1, BTYPE=10 (dynamic Huffman)
  let bw := BitWriter.empty
  let bw := bw.writeBits 1 1  -- BFINAL
  let bw := bw.writeBits 2 2  -- BTYPE = 10
  -- Write dynamic tree header
  let bw := writeDynamicHeader bw litLens distLens
  -- Write tokens
  if data.size == 0 then
    -- Empty: just write end-of-block
    let (code, len) := litCodes[256]!
    let bw := bw.writeHuffCode code len
    bw.flush
  else
    let bw := emitTokensWithCodes bw tokens litCodes distCodes 0
    let (code, len) := litCodes[256]!
    let bw := bw.writeHuffCode code len
    bw.flush

open Zip.Spec.DeflateStoredCorrect (deflateStoredPure)

/-- Unified raw DEFLATE compression dispatch.
    Level 0 = stored, 1 = fixed Huffman, 2-4 = lazy LZ77, 5+ = dynamic Huffman. -/
def deflateRaw (data : ByteArray) (level : UInt8 := 6) : ByteArray :=
  if level == 0 then deflateStoredPure data
  else if level == 1 then deflateFixed data
  else if level < 5 then deflateLazy data
  else deflateDynamic data

end Zip.Native.Deflate
