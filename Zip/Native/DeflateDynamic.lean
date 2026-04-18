import Zip.Native.Deflate
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

/-- Build the `(symbol, freq)` pair list for a frequency array. -/
def freqsToPairs (freqs : Array Nat) : List (Nat × Nat) :=
  (List.range freqs.size).pmap
    (fun i (h : i < freqs.size) => (i, freqs[i]'h))
    (fun _ hi => List.mem_range.mp hi)

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

/-- Compress data using dynamic Huffman codes and greedy LZ77 (Level 5).
    Produces a single DEFLATE block with BFINAL=1, BTYPE=10. -/
def deflateDynamic (data : ByteArray) (windowSize : Nat := 32768) : ByteArray :=
  let tokens := lz77GreedyIter data windowSize
  let (litFreqs, distFreqs) := tokenFreqs tokens
  -- Convert frequencies to (symbol, freq) pairs
  let litFreqPairs := freqsToPairs litFreqs
  let distFreqPairs := freqsToPairs distFreqs
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
  -- Size invariants: `litCodes.size = 286` and `distCodes.size = 30`,
  -- discharged via `canonicalCodes_size` + `computeCodeLengths_length`
  -- and the fact that the distance fixup preserves length.
  have hlit_size : litCodes.size ≥ 286 := by
    show (canonicalCodes _).size ≥ 286
    rw [deflateDynamic.litCodes_size]; omega
  have hdist_size : distCodes.size ≥ 30 := by
    have hdl : List.length distLens = 30 := by
      show List.length (if _ then _ else _) = 30
      split
      · rw [List.length_set]
        exact Huffman.Spec.computeCodeLengths_length distFreqPairs 30 15
      · exact Huffman.Spec.computeCodeLengths_length distFreqPairs 30 15
    show (canonicalCodes _).size ≥ 30
    rw [deflateDynamic.distCodes_size distLens hdl]; omega
  -- Write tokens. `litCodes` has size 286 (via `canonicalCodes_size`),
  -- so index 256 is in bounds for the end-of-block symbol.
  if data.size == 0 then
    -- Empty: just write end-of-block
    let (code, len) := litCodes[256]'(deflateDynamic.lit256_lt litFreqPairs)
    let bw := bw.writeHuffCode code len
    bw.flush
  else
    let bw := emitTokensWithCodes bw tokens litCodes distCodes hlit_size hdist_size 0
    let (code, len) := litCodes[256]'(deflateDynamic.lit256_lt litFreqPairs)
    let bw := bw.writeHuffCode code len
    bw.flush

open Zip.Spec.DeflateStoredCorrect (deflateStoredPure)

/-- Unified raw DEFLATE compression dispatch.
    Level 0 = stored, 1 = fixed Huffman, 2-4 = lazy LZ77, 5+ = dynamic Huffman. -/
def deflateRaw (data : ByteArray) (level : UInt8 := 6) : ByteArray :=
  if level == 0 then deflateStoredPure data
  else if level == 1 then deflateFixedIter data
  else if level < 5 then deflateLazyIter data
  else deflateDynamic data

end Zip.Native.Deflate
