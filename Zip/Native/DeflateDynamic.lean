import Zip.Native.Deflate
import Zip.Native.DeflateFreqs
import Zip.Native.DeflateParse
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

/-! ## Packed-token dynamic-code emission (Wave 3b stage C)

`emitTokensWithCodesP` walks the `packTok`-encoded `UInt32` stream directly,
so the dynamic emit path never materializes boxed `LZ77Token`s. As with
`emitTokensP`/`emitRefFixedP` (`Zip/Native/Deflate.lean`) and `tokenFreqsP`
(see the landmine note in `Zip/Native/DeflateFreqs.lean`), the reference arm
— a match scrutinee over `findLengthCode` applied to a stuck bit-extracted
word — must live in the non-recursive helper `emitRefWithCodesP`, never
inline in the well-founded loop body. `Zip/Spec/EmitPackedCorrect.lean`
proves the loop equal to `emitTokensWithCodes` over the boxed view. -/

/-- Emit one packed *reference* token (tag bit set) with the given Huffman
    codes: decode the length/distance fields with `unpackTok`'s bit
    expressions and write exactly the `writeHuffCode`/`writeBits` sequence of
    `emitTokensWithCodes`'s reference arm (including its dead-code `else`
    fallbacks, so the equality proof aligns branch-for-branch). -/
@[inline] def emitRefWithCodesP (bw : BitWriter)
    (litCodes distCodes : Array (UInt16 × UInt8)) (w : UInt32) : BitWriter :=
  let lw := lenCodeWord (((w >>> 16) &&& 0x7FFF).toNat)
  let idx := codeIdx lw
  if hlitlt : idx + 257 < litCodes.size then
    let (code, len) := litCodes[idx + 257]
    let bw := bw.writeHuffCode code len
    let bw := bw.writeBits (codeExtra lw) (codeVal lw)
    let dw := distCodeWord ((w &&& 0xFFFF).toNat)
    let dIdx := codeIdx dw
    if hdistlt : dIdx < distCodes.size then
      let (dCode, dLen) := distCodes[dIdx]
      let bw := bw.writeHuffCode dCode dLen
      bw.writeBits (codeExtra dw) (codeVal dw)
    else bw
  else bw

/-- Packed-token form of `emitTokensWithCodes` (same `hlit`/`hdist` size
    hypotheses): emit the packed `UInt32` stream with the given lit/len and
    distance Huffman codes. Literals (tag bit clear) read the byte field
    directly; references go through `emitRefWithCodesP`. Equal to
    `emitTokensWithCodes` over the boxed view for every word array
    (`emitTokensWithCodesP_eq`). -/
def emitTokensWithCodesP (bw : BitWriter) (tokens : Array UInt32)
    (litCodes distCodes : Array (UInt16 × UInt8))
    (hlit : litCodes.size ≥ 286) (hdist : distCodes.size ≥ 30)
    (i : Nat) : BitWriter :=
  if h : i < tokens.size then
    let w := tokens[i]
    if w &&& ((1 : UInt32) <<< 31) = 0 then
      have : w.toUInt8.toNat < litCodes.size := by
        have := UInt8.toNat_lt w.toUInt8; omega
      let (code, len) := litCodes[w.toUInt8.toNat]
      emitTokensWithCodesP (bw.writeHuffCode code len) tokens litCodes distCodes hlit hdist (i + 1)
    else
      emitTokensWithCodesP (emitRefWithCodesP bw litCodes distCodes w) tokens litCodes distCodes
        hlit hdist (i + 1)
  else bw
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


/-! ## Header-plan reuse across sizing and emit (#2627)

`writeDynamicHeader` does its expensive work *before* touching the `BitWriter`:
RLE-encoding the ~316 concatenated code lengths, building the CL Huffman tree
(`computeCodeLengths` over the 19-symbol alphabet), and laying out its canonical
codes. The single-block dispatch (`deflateRawBaseP`) ran all of that **twice** —
once to *size* the dynamic candidate (`dynBlockBytes`, header bits into an empty
writer) and again to *emit* it (`deflateDynamicBlockCoreP`). Measured at ~17 µs
per call, that duplicated build was 7–12% of a small-file level-6 compress.

`dynHeaderCodes` isolates the BitWriter-independent build into a reusable plan;
`writeDynamicHeaderWith` writes a header from a precomputed plan. The dispatch
computes the plan once and threads it to both the sizer (`dynBlockBytesWith`)
and the emitter (`deflateDynamicBlockCorePWith`). `writeDynamicHeader` and its
spec (`writeDynamicHeader_spec`/`_wf`) stay as the reference; the plan path is
proved equal to it (`writeDynamicHeaderWith_dynHeaderCodes`), so the size models
and roundtrip are byte-identical. -/

/-- The BitWriter-independent part of a dynamic-tree header: the CL canonical
    codes, the RLE entries over the concatenated code lengths, the CL code
    lengths, and `numCodeLen` (HCLEN + 4). Exactly the values `writeDynamicHeader`
    computes in its Steps 1–4. -/
structure DynHeaderPlan where
  /-- CL Huffman canonical codes (`(code, bitLength)` per symbol), size ≥ 19. -/
  clCodes : Array (UInt16 × UInt8)
  /-- RLE entries `(symbol, extra)` for the concatenated lit/len ++ dist lengths. -/
  clEntries : List (Nat × Nat)
  /-- CL code lengths (19 entries). -/
  clLens : List Nat
  /-- Number of CL code lengths written (HCLEN + 4), `computeHCLEN clLens`. -/
  numCodeLen : Nat

/-- Build the `DynHeaderPlan` for the given lit/len and distance code lengths.
    This is the duplicated work that `dynBlockBytes` (sizing) and
    `deflateDynamicBlockCore` (emit) each used to redo; the dispatch now runs it
    once. The body is exactly Steps 1–4 of `writeDynamicHeader`. -/
def dynHeaderCodes (litLens distLens : List Nat) : DynHeaderPlan :=
  let allLens := litLens ++ distLens
  let clEntries := Deflate.Spec.rlEncodeLengths allLens
  let clFreqs := Deflate.Spec.clSymbolFreqs clEntries
  let clFreqPairs := (List.range clFreqs.length).map fun i => (i, clFreqs.getD i 0)
  let clLens := Huffman.Spec.computeCodeLengths clFreqPairs 19 7
  let clLengthsArr : Array UInt8 := clLens.toArray.map Nat.toUInt8
  let clCodes := canonicalCodes clLengthsArr 7
  let numCodeLen := Deflate.Spec.computeHCLEN clLens
  { clCodes, clEntries, clLens, numCodeLen }

/-- `dynHeaderCodes` produces exactly 19 CL canonical codes. -/
theorem dynHeaderCodes_clCodes_size (litLens distLens : List Nat) :
    (dynHeaderCodes litLens distLens).clCodes.size = 19 := by
  unfold dynHeaderCodes
  simp only
  rw [canonicalCodes_size _ 7, Array.size_map, List.size_toArray,
    Huffman.Spec.computeCodeLengths_length]

/-- Write a dynamic Huffman tree header from a precomputed `DynHeaderPlan`
    (Steps 5–7 of `writeDynamicHeader`): HLIT/HDIST/HCLEN, then the CL code
    lengths in permutation order, then the RLE entries via the CL codes. The
    `hcl` size witness is the (phantom, proof-irrelevant) one `writeCLEntries`
    threads.

    **Invariant**: `p` must be `dynHeaderCodes litLens distLens` — only then does
    the header match the lengths (and equal `writeDynamicHeader bw litLens distLens`,
    by `writeDynamicHeaderWith_dynHeaderCodes`). Passing an unrelated plan writes a
    header for the *plan's* lengths, not `litLens`/`distLens`. The dispatch builds
    the plan from exactly these lengths; this is not a general-purpose writer. -/
def writeDynamicHeaderWith (bw : BitWriter) (litLens distLens : List Nat)
    (p : DynHeaderPlan) (hcl : p.clCodes.size ≥ 19) : BitWriter :=
  let hlit := litLens.length - 257
  let hdist := distLens.length - 1
  let hclen := p.numCodeLen - 4
  let bw := bw.writeBits 5 hlit.toUInt32
  let bw := bw.writeBits 5 hdist.toUInt32
  let bw := bw.writeBits 4 hclen.toUInt32
  let bw := writeDynamicHeader.writeCLLengths bw p.clLens p.numCodeLen 0
  writeDynamicHeader.writeCLEntries bw p.clCodes p.clEntries hcl

/-- The plan path agrees with `writeDynamicHeader`: writing from
    `dynHeaderCodes litLens distLens` reproduces `writeDynamicHeader` bit-for-bit
    (the `hcl` witness is irrelevant, as `writeCLEntries` re-checks bounds). -/
theorem writeDynamicHeaderWith_dynHeaderCodes (bw : BitWriter) (litLens distLens : List Nat)
    (hcl : (dynHeaderCodes litLens distLens).clCodes.size ≥ 19) :
    writeDynamicHeaderWith bw litLens distLens (dynHeaderCodes litLens distLens) hcl =
      writeDynamicHeader bw litLens distLens := by
  unfold writeDynamicHeaderWith writeDynamicHeader dynHeaderCodes
  rfl


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


/-- Emit a dynamic Huffman DEFLATE block from precomputed LZ77 tokens **and**
    precomputed lit/len and distance code lengths (with their length invariants).
    Produces a single DEFLATE block with BFINAL=1, BTYPE=10.

    Split out of `deflateDynamicBlock` so the size-then-emit dispatch can size the
    block from the same `litLens`/`distLens` it later emits with, instead of
    recomputing the code lengths (`computeCodeLengths` over the 286/30 alphabets)
    a second time. -/
def deflateDynamicBlockCore (data : ByteArray) (tokens : Array LZ77Token)
    (litLens distLens : List Nat)
    (hlit : litLens.length = 286) (hdist : distLens.length = 30) : ByteArray :=
  -- Build canonical codes from the given lengths
  let litCodes := canonicalCodes (litLens.toArray.map Nat.toUInt8)
  let distCodes := canonicalCodes (distLens.toArray.map Nat.toUInt8)
  -- Write block header: BFINAL=1, BTYPE=10 (dynamic Huffman)
  let bw := BitWriter.empty
  let bw := bw.writeBits 1 1  -- BFINAL
  let bw := bw.writeBits 2 2  -- BTYPE = 10
  -- Write dynamic tree header
  let bw := writeDynamicHeader bw litLens distLens
  -- Size invariants from `canonicalCodes_size` + the length hypotheses.
  have hlit_size : litCodes.size ≥ 286 := by
    show (canonicalCodes (litLens.toArray.map Nat.toUInt8)).size ≥ 286
    rw [canonicalCodes_size, Array.size_map, List.size_toArray]; omega
  have hdist_size : distCodes.size ≥ 30 := by
    show (canonicalCodes (distLens.toArray.map Nat.toUInt8)).size ≥ 30
    rw [canonicalCodes_size, Array.size_map, List.size_toArray]; omega
  have h256 : 256 < litCodes.size := by
    show 256 < (canonicalCodes (litLens.toArray.map Nat.toUInt8)).size
    rw [canonicalCodes_size, Array.size_map, List.size_toArray]; omega
  -- Write tokens, then the end-of-block symbol (256, in bounds via `h256`).
  if data.size == 0 then
    -- Empty: just write end-of-block
    let (code, len) := litCodes[256]'h256
    let bw := bw.writeHuffCode code len
    bw.flush
  else
    let bw := emitTokensWithCodes bw tokens litCodes distCodes hlit_size hdist_size 0
    let (code, len) := litCodes[256]'h256
    let bw := bw.writeHuffCode code len
    bw.flush

/-- Packed-token form of `deflateDynamicBlockCore` (Wave 3b stage C): emit a
    dynamic Huffman block directly from the packed `UInt32` stream — same
    body with `emitTokensWithCodesP` in place of `emitTokensWithCodes`.
    Equal to `deflateDynamicBlockCore` over the boxed view
    (`deflateDynamicBlockCoreP_eq` in `Zip/Spec/EmitPackedCorrect.lean`). -/
def deflateDynamicBlockCoreP (data : ByteArray) (tokens : Array UInt32)
    (litLens distLens : List Nat)
    (hlit : litLens.length = 286) (hdist : distLens.length = 30) : ByteArray :=
  let litCodes := canonicalCodes (litLens.toArray.map Nat.toUInt8)
  let distCodes := canonicalCodes (distLens.toArray.map Nat.toUInt8)
  let bw := BitWriter.empty
  let bw := bw.writeBits 1 1  -- BFINAL
  let bw := bw.writeBits 2 2  -- BTYPE = 10
  let bw := writeDynamicHeader bw litLens distLens
  have hlit_size : litCodes.size ≥ 286 := by
    show (canonicalCodes (litLens.toArray.map Nat.toUInt8)).size ≥ 286
    rw [canonicalCodes_size, Array.size_map, List.size_toArray]; omega
  have hdist_size : distCodes.size ≥ 30 := by
    show (canonicalCodes (distLens.toArray.map Nat.toUInt8)).size ≥ 30
    rw [canonicalCodes_size, Array.size_map, List.size_toArray]; omega
  have h256 : 256 < litCodes.size := by
    show 256 < (canonicalCodes (litLens.toArray.map Nat.toUInt8)).size
    rw [canonicalCodes_size, Array.size_map, List.size_toArray]; omega
  if data.size == 0 then
    let (code, len) := litCodes[256]'h256
    let bw := bw.writeHuffCode code len
    bw.flush
  else
    let bw := emitTokensWithCodesP bw tokens litCodes distCodes hlit_size hdist_size 0
    let (code, len) := litCodes[256]'h256
    let bw := bw.writeHuffCode code len
    bw.flush

/-- `deflateDynamicBlockCoreP` with the dynamic-tree header taken from a
    precomputed `DynHeaderPlan` (#2627): identical to `deflateDynamicBlockCoreP`
    except the header write reuses the plan instead of rebuilding the CL tree.
    The dispatch (`deflateRawBaseP`) passes the same plan it sized with, so the
    expensive `dynHeaderCodes` build runs once per block instead of twice.

    **Invariant** (as for `writeDynamicHeaderWith`): `p` must be
    `dynHeaderCodes litLens distLens`; only then is the output
    `deflateDynamicBlockCoreP data tokens litLens distLens` (proved by
    `deflateDynamicBlockCorePWith_dynHeaderCodes`). -/
def deflateDynamicBlockCorePWith (data : ByteArray) (tokens : Array UInt32)
    (litLens distLens : List Nat) (p : DynHeaderPlan) (hcl : p.clCodes.size ≥ 19)
    (hlit : litLens.length = 286) (hdist : distLens.length = 30) : ByteArray :=
  let litCodes := canonicalCodes (litLens.toArray.map Nat.toUInt8)
  let distCodes := canonicalCodes (distLens.toArray.map Nat.toUInt8)
  let bw := BitWriter.empty
  let bw := bw.writeBits 1 1  -- BFINAL
  let bw := bw.writeBits 2 2  -- BTYPE = 10
  let bw := writeDynamicHeaderWith bw litLens distLens p hcl
  have hlit_size : litCodes.size ≥ 286 := by
    show (canonicalCodes (litLens.toArray.map Nat.toUInt8)).size ≥ 286
    rw [canonicalCodes_size, Array.size_map, List.size_toArray]; omega
  have hdist_size : distCodes.size ≥ 30 := by
    show (canonicalCodes (distLens.toArray.map Nat.toUInt8)).size ≥ 30
    rw [canonicalCodes_size, Array.size_map, List.size_toArray]; omega
  have h256 : 256 < litCodes.size := by
    show 256 < (canonicalCodes (litLens.toArray.map Nat.toUInt8)).size
    rw [canonicalCodes_size, Array.size_map, List.size_toArray]; omega
  if data.size == 0 then
    let (code, len) := litCodes[256]'h256
    let bw := bw.writeHuffCode code len
    bw.flush
  else
    let bw := emitTokensWithCodesP bw tokens litCodes distCodes hlit_size hdist_size 0
    let (code, len) := litCodes[256]'h256
    let bw := bw.writeHuffCode code len
    bw.flush

/-- The plan-taking emitter with the canonical plan equals the original packed
    emitter: the only difference is the header write, bridged by
    `writeDynamicHeaderWith_dynHeaderCodes`. -/
theorem deflateDynamicBlockCorePWith_dynHeaderCodes (data : ByteArray) (tokens : Array UInt32)
    (litLens distLens : List Nat) (hcl : (dynHeaderCodes litLens distLens).clCodes.size ≥ 19)
    (hlit : litLens.length = 286) (hdist : distLens.length = 30) :
    deflateDynamicBlockCorePWith data tokens litLens distLens (dynHeaderCodes litLens distLens)
        hcl hlit hdist =
      deflateDynamicBlockCoreP data tokens litLens distLens hlit hdist := by
  unfold deflateDynamicBlockCorePWith deflateDynamicBlockCoreP
  simp only [writeDynamicHeaderWith_dynHeaderCodes]


/-- Write a dynamic Huffman DEFLATE block from precomputed LZ77 tokens.
    Produces a single DEFLATE block with BFINAL=1, BTYPE=10. Factored out of
    `deflateDynamic` so a caller that already has the token stream (e.g. the
    `deflateCompressed` fixed/dynamic comparison) can avoid re-running the
    matcher. Computes the code lengths (`dynamicCodeLengths`) then delegates to
    `deflateDynamicBlockCore`. -/
def deflateDynamicBlock (data : ByteArray) (tokens : Array LZ77Token) : ByteArray :=
  let (litFreqs, distFreqs) := tokenFreqs tokens
  let lens := dynamicCodeLengths litFreqs distFreqs
  deflateDynamicBlockCore data tokens lens.1 lens.2
    (dynamicCodeLengths_length litFreqs distFreqs).1
    (dynamicCodeLengths_length litFreqs distFreqs).2

/-- Emit one dynamic Huffman block into an existing `BitWriter` (no flush), with
    `BFINAL = isFinal`. Same body as `deflateDynamicBlockCore` but bit-packed onto
    a running writer so a sequence of blocks shares the bitstream. -/
def emitDynBlock (bw : BitWriter) (data : ByteArray) (tokens : Array LZ77Token)
    (litLens distLens : List Nat)
    (hlit : litLens.length = 286) (hdist : distLens.length = 30)
    (isFinal : Bool) : BitWriter :=
  let litCodes := canonicalCodes (litLens.toArray.map Nat.toUInt8)
  let distCodes := canonicalCodes (distLens.toArray.map Nat.toUInt8)
  let bw := bw.writeBits 1 (if isFinal then 1 else 0)  -- BFINAL (1 bit)
  let bw := bw.writeBits 2 2                            -- BTYPE = 10 (dynamic)
  let bw := writeDynamicHeader bw litLens distLens
  have hlit_size : litCodes.size ≥ 286 := by
    show (canonicalCodes (litLens.toArray.map Nat.toUInt8)).size ≥ 286
    rw [canonicalCodes_size, Array.size_map, List.size_toArray]; omega
  have hdist_size : distCodes.size ≥ 30 := by
    show (canonicalCodes (distLens.toArray.map Nat.toUInt8)).size ≥ 30
    rw [canonicalCodes_size, Array.size_map, List.size_toArray]; omega
  have h256 : 256 < litCodes.size := by
    show 256 < (canonicalCodes (litLens.toArray.map Nat.toUInt8)).size
    rw [canonicalCodes_size, Array.size_map, List.size_toArray]; omega
  let bw := if data.size == 0 then bw
            else emitTokensWithCodes bw tokens litCodes distCodes hlit_size hdist_size 0
  let (code, len) := litCodes[256]'h256
  bw.writeHuffCode code len

/-- Compress data using dynamic Huffman codes and greedy LZ77 (Level 5).
    Produces a single DEFLATE block with BFINAL=1, BTYPE=10. Thin wrapper over
    `deflateDynamicBlock` that runs the greedy matcher first. -/
def deflateDynamic (data : ByteArray) (windowSize : Nat := 32768) : ByteArray :=
  deflateDynamicBlock data (lz77GreedyIter data windowSize)

open Zip.Spec.DeflateStoredCorrect (deflateStoredPure storedBlockBytes storedBlockBytes_eq)

/-- Pick the smaller of two encodings by byte length (ties keep `b`). -/
def pickSmaller (a b : ByteArray) : ByteArray :=
  if a.size < b.size then a else b

/-! ## Sizing a block without emitting it

A DEFLATE block's body is a *dot product* of symbol frequencies and code
lengths — `Σ_sym freq[sym]·(codeLen[sym] + extraBits[sym])` — so its exact
byte size is computable in O(#symbols) from the already-computed `tokenFreqs`,
with no bit-banging and independent of #tokens. The dispatch below sizes every
candidate this way and emits *only* the winner, instead of emitting all three
blocks and keeping the smallest. The freq·codeLen identity is not proved here:
the roundtrip theorems hold for whichever block is chosen, and `SizeHelpers`
tests pin the helpers to the emitted `.size` so the choice stays byte-identical
to the old `pickSmaller`-of-emitted-blocks behaviour. -/

/-- Extra bits carried by lit/len symbol `s`: zero for literals and the
    end-of-block symbol (0–256), the RFC 1951 §3.2.5 table for length symbols
    257–285. Reads the same `Inflate.lengthExtra` table the emitter writes. -/
@[inline] def lenExtraBits (s : Nat) : Nat :=
  if 257 ≤ s then (Inflate.lengthExtra.getD (s - 257) 0).toNat else 0

/-- Fixed-Huffman lit/len code lengths as a `Nat` array (RFC 1951 §3.2.6),
    derived from the same table `fixedLitCodes` is built from. -/
def fixedLitLenNat : Array Nat := Inflate.fixedLitLengths.map (·.toNat)

/-- Fixed-Huffman distance code lengths as a `Nat` array (all 5). -/
def fixedDistLenNat : Array Nat := Inflate.fixedDistLengths.map (·.toNat)

/-- Total body-bit count of a block over the tokens summarised by
    `(litFreqs, distFreqs)`, for the given lit/len and distance code-length
    tables: `Σ_sym freq·(codeLen + extraBits)` over the 286 lit/len and 30
    distance symbols. The end-of-block symbol (256, frequency 1) is included via
    `litFreqs`; unused symbols have frequency 0 and contribute nothing. -/
def symbolBitCount (litFreqs distFreqs litLens distLens : Array Nat) : Nat :=
  ((List.range 286).foldl (fun acc s =>
      acc + litFreqs.getD s 0 * (litLens.getD s 0 + lenExtraBits s)) 0)
  + ((List.range 30).foldl (fun acc d =>
      acc + distFreqs.getD d 0 * (distLens.getD d 0 + (Inflate.distExtra.getD d 0).toNat)) 0)

/-- Byte size of `deflateFixedBlock data tokens`, computed from frequencies
    without emitting: `⌈(3 header bits + body bits)/8⌉`. `litFreqs`/`distFreqs`
    are `tokenFreqs tokens`. -/
def fixedBlockBytes (litFreqs distFreqs : Array Nat) : Nat :=
  (3 + symbolBitCount litFreqs distFreqs fixedLitLenNat fixedDistLenNat + 7) / 8

/-- Byte size of `deflateDynamicBlock data tokens`. The tree-header bit count is
    obtained by running `writeDynamicHeader` into an empty writer (cheap — RLE
    over ~316 code lengths) and reading its `bitLength`; the symbol body is the
    freq·codeLen dot product. `litLens`/`distLens` come from
    `dynamicCodeLengths`. -/
def dynBlockBytes (litFreqs distFreqs : Array Nat) (litLens distLens : List Nat) : Nat :=
  let headerBits := (writeDynamicHeader BitWriter.empty litLens distLens).bitLength
  (3 + headerBits + symbolBitCount litFreqs distFreqs litLens.toArray distLens.toArray + 7) / 8

/-- `dynBlockBytes` with the tree-header bits taken from a precomputed
    `DynHeaderPlan` (#2627): the header bit count comes from writing the plan into
    an empty writer rather than rebuilding the CL tree. The dispatch sizes and
    emits the dynamic candidate from one shared plan.

    **Invariant** (as for `writeDynamicHeaderWith`): `p` must be
    `dynHeaderCodes litLens distLens`; only then does this equal
    `dynBlockBytes litFreqs distFreqs litLens distLens`
    (proved by `dynBlockBytesWith_dynHeaderCodes`). -/
def dynBlockBytesWith (litFreqs distFreqs : Array Nat) (litLens distLens : List Nat)
    (p : DynHeaderPlan) (hcl : p.clCodes.size ≥ 19) : Nat :=
  let headerBits := (writeDynamicHeaderWith BitWriter.empty litLens distLens p hcl).bitLength
  (3 + headerBits + symbolBitCount litFreqs distFreqs litLens.toArray distLens.toArray + 7) / 8

/-- The plan-taking sizer with the canonical plan equals `dynBlockBytes`. Proved
    before the `irreducible` attribute so both unfold; bridged by
    `writeDynamicHeaderWith_dynHeaderCodes`. -/
theorem dynBlockBytesWith_dynHeaderCodes (litFreqs distFreqs : Array Nat) (litLens distLens : List Nat)
    (hcl : (dynHeaderCodes litLens distLens).clCodes.size ≥ 19) :
    dynBlockBytesWith litFreqs distFreqs litLens distLens (dynHeaderCodes litLens distLens) hcl =
      dynBlockBytes litFreqs distFreqs litLens distLens := by
  unfold dynBlockBytesWith dynBlockBytes
  rw [writeDynamicHeaderWith_dynHeaderCodes]

-- The size helpers are opaque cost models: the dispatch only ever compares them.
-- Marking them irreducible keeps the elaborator from unfolding the 286-element
-- `symbolBitCount` fold while `split`ting the selection `if` (which would exceed
-- `maxRecDepth`); the kernel and compiled code still evaluate them, so `decide`
-- and the `SizeHelpers` conformance tests are unaffected.
attribute [irreducible] symbolBitCount fixedBlockBytes dynBlockBytes dynBlockBytesWith

/-- Hash-chain search depth per compression level (levels ≥ 5). Higher levels
    search deeper for longer matches (better ratio on diverse input) at higher
    cost; the `chainWalk` early-stop keeps repetitive input fast at any depth.
    The ratio gain saturates around 256–512 (measured), so level 9 caps there. -/
def chainDepth (level : UInt8) : Nat :=
  if level ≤ 1 then 8
  else if level ≤ 2 then 16
  else if level ≤ 3 then 32
  else if level ≤ 4 then 48
  else if level ≤ 5 then 64
  else if level ≤ 6 then 128
  else if level ≤ 7 then 256
  else if level ≤ 8 then 512
  else 1024

/-- Per-level interior-insertion cap (zlib's `deflate_fast`/`deflate_slow` split):
    fast levels (1–3) defer most interior `updateHashes` insertions for speed at a
    ratio cost; levels ≥ 4 insert every position (best ratio). A `cap` below ~16
    is counterproductive end-to-end — the worse ratio inflates the token count and
    the Huffman encode dominates — so the fastest level uses `cap = 16`. The chain
    is a heuristic, so any cap stays correct (`lz77ChainIter_resolves` holds ∀ cap). -/
def insertCap (level : UInt8) : Nat :=
  if level ≤ 1 then 16
  else if level ≤ 2 then 32
  else if level ≤ 3 then 64
  else 1000000000

/-- Lazy `good_match` threshold (zlib-style): the lazy matcher skips the
    one-byte-lookahead probe once the first match is at least this long, since a
    long first match is rarely improved by deferral. Lower → more gating (faster,
    slightly worse ratio). `259 > 258` disables gating. SPIKE: uniform 8. -/
def goodMatch (level : UInt8) : Nat :=
  if level ≤ 6 then 8
  else 259

/-- The per-level LZ77 matcher (zlib-faithful): levels 1–3 (`deflate_fast`) use the
    greedy hash-chain matcher; levels ≥ 4 (`deflate_slow`) use the one-byte-lookahead
    lazy variant, which improves ratio at equal window/chain depth. Both share the
    same `(chainDepth, insertCap)` ladder and satisfy the same encoder contracts
    (`lzMatch_{encodable,empty,resolves}` in `DeflateBlockSplit`), so the choice is
    transparent to the roundtrip proof. -/
def lzMatch (data : ByteArray) (level : UInt8) : Array LZ77Token :=
  if 4 ≤ level then lz77ChainLazyIter data (chainDepth level) 32768 (insertCap level) (goodMatch level)
  else lz77ChainIter data (chainDepth level) 32768 (insertCap level)

/-- Packed-token form of `lzMatch` (Wave 3b stage A): the same per-level
    dispatch over the packed matcher twins, producing one unboxed `UInt32`
    per token instead of a boxed `LZ77Token`. The boxed view recovers
    `lzMatch` exactly (`lzMatchP_map` in `Zip/Spec/LZ77PackedCorrect.lean`);
    downstream consumers still run on `lzMatch` — stage B moves them here. -/
def lzMatchP (data : ByteArray) (level : UInt8) : Array UInt32 :=
  if 4 ≤ level then lz77ChainLazyIterP data (chainDepth level) 32768 (insertCap level) (goodMatch level)
  else lz77ChainIterP data (chainDepth level) 32768 (insertCap level)

/-! ## Self-contained block-split dynamic compression

Split `data` into `chunkSize`-byte chunks, match each chunk independently (fresh
32 KiB window, so its back-references stay within the chunk), and emit one dynamic
block per chunk — each with its own frequency-fit Huffman trees, `BFINAL` only on
the last — packed onto one bitstream. Because every block references only its own
chunk, the blocks decode independently and compose; the per-block trees recover
most of the ratio a single whole-file tree leaves on large/heterogeneous inputs. -/

/-- Emit one self-contained dynamic block for the chunk `data[pos, j)` onto `bw`
    (`BFINAL = isFinal`), matching the chunk in isolation. -/
def emitChunkBlock (bw : BitWriter) (data : ByteArray) (pos j : Nat) (level : UInt8)
    (isFinal : Bool) : BitWriter :=
  let chunk := data.extract pos j
  let toks := lzMatch chunk level
  let f := tokenFreqs toks
  let lens := dynamicCodeLengths f.1 f.2
  emitDynBlock bw chunk toks lens.1 lens.2
    (dynamicCodeLengths_length f.1 f.2).1 (dynamicCodeLengths_length f.1 f.2).2 isFinal

/-- Emit the block sequence for `data` from `pos` onward, one block per
    `chunkSize`-byte chunk (the last carries `BFINAL`). Well-founded on the
    remaining bytes so the roundtrip can induct through it. -/
def emitChunkBlocks (data : ByteArray) (chunkSize : Nat) (level : UInt8)
    (pos : Nat) (bw : BitWriter) : BitWriter :=
  let step := max chunkSize 1
  let j := min (pos + step) data.size
  let bw := emitChunkBlock bw data pos j level (decide (j ≥ data.size))
  if j ≥ data.size then bw
  else emitChunkBlocks data chunkSize level j bw
termination_by data.size - pos
decreasing_by simp_all only [Nat.not_le]; omega

/-- Self-contained block-split dynamic compression. See `emitChunkBlock`. -/
def deflateDynamicBlocksSC (data : ByteArray) (chunkSize : Nat) (level : UInt8) : ByteArray :=
  if data.size == 0 then
    let f := tokenFreqs #[]
    (emitDynBlock BitWriter.empty data #[] (dynamicCodeLengths f.1 f.2).1 (dynamicCodeLengths f.1 f.2).2
      (dynamicCodeLengths_length f.1 f.2).1 (dynamicCodeLengths_length f.1 f.2).2 true).flush
  else
    (emitChunkBlocks data chunkSize level 0 BitWriter.empty).flush

/-- Chunk size for block splitting in `deflateRaw`: each ~16 KiB run gets its own
    dynamic Huffman tree and a fresh match window. Large enough to keep per-block
    header overhead negligible, small enough to let the trees track local
    statistics. `pickSmaller` makes the exact value a pure ratio knob (never a
    correctness or regression concern). 16384 is the joint optimum with
    `sharedTokChunk` of a Canterbury + Silesia sweep at levels 7–9 (#2529, `lake
    exe ratio-sweep`). The joint framing matters: in isolation ever-larger chunks
    sized smaller (less window loss), but `deflateRaw` deploys this variant only
    on the files where it beats the cross-block split, and there 16384 won at
    every level. -/
def splitChunkSize : Nat := 16384

/-! ## Cross-block (shared-window) block-split dynamic compression

Unlike the self-contained variant, this matches the **whole** input *once* with
the full 32 KiB window (`lz77ChainIter`), producing one token stream whose
back-references are valid against the running output, then **partitions that
token stream** by token count into per-block groups. Each group is re-Huffman
coded with its own dynamic tree; references freely cross block boundaries
(RFC 1951 §3.2), so this recovers the cross-chunk matches the self-contained
split discards — the lever for the text-ratio gap. `pickSmaller` gates it so it
can never regress. -/

/-- Emit one shared-window dynamic block for a *slice* `group` of the
    whole-stream token array onto `bw` (`BFINAL = isFinal`). The whole (non-empty)
    `data` is passed only to satisfy `emitDynBlock`'s empty-input guard, so the
    group's tokens are always emitted; the Huffman trees fit `group`'s own
    frequencies. -/
def emitSharedBlock (bw : BitWriter) (data : ByteArray) (group : Array LZ77Token)
    (isFinal : Bool) : BitWriter :=
  let f := tokenFreqs group
  let lens := dynamicCodeLengths f.1 f.2
  emitDynBlock bw data group lens.1 lens.2
    (dynamicCodeLengths_length f.1 f.2).1 (dynamicCodeLengths_length f.1 f.2).2 isFinal

/-- Emit the shared-window block sequence for the whole-stream token array `toks`
    from token index `pos`, one block per `tokChunk` tokens (the last carries
    `BFINAL`). Well-founded on the remaining token count so the roundtrip can
    induct through it. -/
def emitSharedBlocks (data : ByteArray) (toks : Array LZ77Token) (tokChunk : Nat)
    (pos : Nat) (bw : BitWriter) : BitWriter :=
  let step := max tokChunk 1
  let j := min (pos + step) toks.size
  let bw := emitSharedBlock bw data (toks.extract pos j) (decide (j ≥ toks.size))
  if j ≥ toks.size then bw
  else emitSharedBlocks data toks tokChunk j bw
termination_by toks.size - pos
decreasing_by simp_all only [Nat.not_le]; omega

/-- Token-group size for cross-block splitting in `deflateRaw`: number of LZ77
    tokens per block. A pure ratio knob (`pickSmaller` guards regression); 8192
    is the joint optimum with `splitChunkSize` of a Canterbury + Silesia sweep at
    levels 7–9 (#2529, `lake exe ratio-sweep`) — the same value at every level,
    so a single global default suffices. Smaller groups are dominated by
    per-block header overhead, larger ones by coarser local-statistics tracking;
    the curve is shallow around the optimum (8192 beat 16384 by ~0.015% of
    corpus total) but moving off the prior single-sample 4096 was worth ~0.19%. -/
def sharedTokChunk : Nat := 8192

/-- Cross-block (shared-window) block-split dynamic compression. Matches the
    whole input once, then partitions the token stream into `tokChunk`-token
    blocks. See `emitSharedBlock`. -/
def deflateDynamicBlocksShared (data : ByteArray) (tokChunk : Nat) (level : UInt8) : ByteArray :=
  if data.size == 0 then
    let f := tokenFreqs #[]
    (emitDynBlock BitWriter.empty data #[] (dynamicCodeLengths f.1 f.2).1 (dynamicCodeLengths f.1 f.2).2
      (dynamicCodeLengths_length f.1 f.2).1 (dynamicCodeLengths_length f.1 f.2).2 true).flush
  else
    (emitSharedBlocks data (lzMatch data level)
      tokChunk 0 BitWriter.empty).flush

/-- Emit shared-window blocks at explicit cut points: each element of `cuts` is
    an absolute token index ending the current block. Every cut is clamped to
    `(pos, toks.size]`, so **any** cuts list — empty, non-monotone, or out of
    range — yields a valid total partition; an empty list emits one final block
    of the rest. The clamping is what keeps the boundary *heuristic* free of
    proof obligations: the roundtrip holds for an arbitrary partition. -/
def emitSharedBlocksAt (data : ByteArray) (toks : Array LZ77Token) (cuts : List Nat)
    (pos : Nat) (bw : BitWriter) : BitWriter :=
  let j := min (max (cuts.headD toks.size) (pos + 1)) toks.size
  let bw := emitSharedBlock bw data (toks.extract pos j) (decide (j ≥ toks.size))
  if j ≥ toks.size then bw
  else emitSharedBlocksAt data toks cuts.tail j bw
termination_by toks.size - pos
decreasing_by
  rename_i h
  simp only [Nat.not_le] at h
  omega

/-- Cross-block (shared-window) block-split dynamic compression with the
    partition chosen by `choose`: like `deflateDynamicBlocksShared`, but the
    per-block token groups come from the cut list `choose toks` instead of a
    fixed cadence. The roundtrip holds for any `choose` (the emitter clamps
    every cut), so the selector is a pure ratio heuristic. -/
def deflateDynamicBlocksSharedAtTokens (data : ByteArray) (toks : Array LZ77Token)
    (choose : Array LZ77Token → List Nat) : ByteArray :=
  if data.size == 0 then
    let f := tokenFreqs #[]
    (emitDynBlock BitWriter.empty data #[] (dynamicCodeLengths f.1 f.2).1 (dynamicCodeLengths f.1 f.2).2
      (dynamicCodeLengths_length f.1 f.2).1 (dynamicCodeLengths_length f.1 f.2).2 true).flush
  else
    (emitSharedBlocksAt data toks (choose toks) 0 BitWriter.empty).flush

/-- `deflateDynamicBlocksSharedAtTokens` over this level's `lzMatch` stream.
    Kept as a definitional wrapper so the level-9 dispatch can share one
    matcher pass across candidates (Wave 1): the spec lemmas are stated about
    this wrapper and see through it by `rfl`. -/
def deflateDynamicBlocksSharedAt (data : ByteArray)
    (choose : Array LZ77Token → List Nat) (level : UInt8) : ByteArray :=
  deflateDynamicBlocksSharedAtTokens data (lzMatch data level) choose

/-! ## Entropy-divergence boundary heuristic (libdeflate-style)

Instead of cutting the shared-window token stream at a fixed cadence, walk it
once and close a block where the symbol statistics *shift*: maintain a coarse
observation histogram for the block so far and one for a recent window, and cut
when the scaled distribution delta exceeds a threshold (libdeflate
`deflate_compress.c`, `observe_literal`/`observe_match`/`do_end_block_check`).
Every constant below is a pure ratio knob: the emitter clamps arbitrary cuts,
so none of this carries proof obligations, and `chooseSplitsArbitrated` sizes
the result against the fixed cadence in exact bits so the heuristic can never
regress the shared-window candidate. -/

/-- Number of literal observation classes (libdeflate
    `NUM_LITERAL_OBSERVATION_TYPES`): literals are bucketed by bits 7,6,0 —
    a cheap proxy separating case/digit/punctuation regimes. -/
def splitNumLiteralClasses : Nat := 8

/-- Total observation classes (libdeflate `NUM_OBSERVATION_TYPES`): 8 literal
    classes plus 2 match classes (short/long). -/
def splitNumClasses : Nat := 10

/-- New observations between divergence checks (libdeflate
    `NUM_OBSERVATIONS_PER_BLOCK_CHECK`): the recent-window size in tokens. -/
def splitCheckTokens : Nat := 512

/-- Floor on block *output* bytes, and on bytes remaining after a cut
    (libdeflate `MIN_BLOCK_LENGTH`): per-block tree headers stop paying for
    themselves below this, per the #2527 `sharedTokChunk` sweep. -/
def splitMinBlockBytes : Nat := 10000

/-- Unconditional cut ceiling on block output bytes (libdeflate
    `SOFT_MAX_BLOCK_LENGTH`): even statistically-uniform runs get a fresh tree
    at this scale, bounding how stale the code lengths can grow. -/
def splitSoftMaxBlockBytes : Nat := 300000

/-- Divergence threshold numerator/denominator (libdeflate's `200/512`): cut
    when the sum of absolute probability deltas reaches ~39%. -/
def splitCutoffNum : Nat := 200
/-- See `splitCutoffNum`. -/
def splitCutoffDen : Nat := 512

/-- Length bias divisor (libdeflate's `block_length / 4096` term): longer
    blocks cut progressively easier, since a fresh tree amortizes better. -/
def splitBiasBytes : Nat := 4096

/-- Observation class of a token (libdeflate `observe_literal`/`observe_match`):
    literals map to 0–7 by bits 7,6,0; matches map to 8 (length < 9) or 9. -/
@[inline] def splitTokenClass : LZ77Token → Nat
  | .literal b => (((b >>> 5) &&& 6) ||| (b &&& 1)).toNat
  | .reference len _ => splitNumLiteralClasses + (if len ≥ 9 then 1 else 0)

/-- Output bytes a token contributes: 1 for a literal, the match length for a
    reference. -/
@[inline] def splitTokenBytes : LZ77Token → Nat
  | .literal _ => 1
  | .reference len _ => len

/-- The divergence test (libdeflate `do_end_block_check`): cut when
    `Σᵢ |new[i]·oldTot − old[i]·newTot| + (blockBytes/splitBiasBytes)·oldTot`
    reaches `newTot·splitCutoffNum/splitCutoffDen·oldTot` — i.e. the recent
    window's class distribution differs from the block-so-far distribution by
    at least ~39% probability mass (less for long blocks). Integer-only; the
    caller guarantees `oldTot > 0`. libdeflate additionally inflates the cutoff
    for blocks under `MIN_BLOCK_LENGTH`, but our caller (like libdeflate's
    `ready_to_check_block`) never checks such blocks, so that branch is omitted
    as dead code. -/
def splitEndBlockCheck (old : Array Nat) (oldTot : Nat) (new : Array Nat) (newTot : Nat)
    (blockBytes : Nat) : Bool := Id.run do
  let mut delta := 0
  for i in [0:splitNumClasses] do
    let a := new.getD i 0 * oldTot
    let b := old.getD i 0 * newTot
    delta := delta + (if a ≥ b then a - b else b - a)
  let cutoff := newTot * splitCutoffNum / splitCutoffDen * oldTot
  return delta + (blockBytes / splitBiasBytes) * oldTot ≥ cutoff

/-- Entropy-divergence cut points for the shared-window token stream: one pass
    over `toks`, accumulating per-class observation counts. Block-so-far
    (`old`) and recent-window (`new`) histograms are compared every
    `splitCheckTokens` tokens once the block and the remaining input are both
    at least `splitMinBlockBytes` output bytes; on divergence the block is cut
    at the next token boundary, otherwise the window merges into `old`. Blocks
    are force-cut at `splitSoftMaxBlockBytes`. Byte floor/ceiling are enforced
    per-token (a single 512-token window can span ~132 KB of output via long
    matches, so checking them only at window boundaries could overshoot). -/
def chooseSplitsHeuristic (toks : Array LZ77Token) : List Nat := Id.run do
  let mut totalBytes := 0
  for t in toks do
    totalBytes := totalBytes + splitTokenBytes t
  let mut old : Array Nat := Array.replicate splitNumClasses 0
  let mut oldTot := 0
  let mut new : Array Nat := Array.replicate splitNumClasses 0
  let mut newTot := 0
  let mut blockBytes := 0
  let mut doneBytes := 0
  let mut cuts : Array Nat := #[]
  for h : i in [0:toks.size] do
    let t := toks[i]
    let c := splitTokenClass t
    new := new.set! c (new.getD c 0 + 1)
    newTot := newTot + 1
    blockBytes := blockBytes + splitTokenBytes t
    doneBytes := doneBytes + splitTokenBytes t
    if blockBytes ≥ splitMinBlockBytes && totalBytes - doneBytes ≥ splitMinBlockBytes then
      let cut :=
        blockBytes ≥ splitSoftMaxBlockBytes ||
        (newTot ≥ splitCheckTokens && oldTot > 0 &&
          splitEndBlockCheck old oldTot new newTot blockBytes)
      if cut then
        cuts := cuts.push (i + 1)
        old := Array.replicate splitNumClasses 0
        oldTot := 0
        new := Array.replicate splitNumClasses 0
        newTot := 0
        blockBytes := 0
      else if newTot ≥ splitCheckTokens then
        for j in [0:splitNumClasses] do
          old := old.set! j (old.getD j 0 + new.getD j 0)
        oldTot := oldTot + newTot
        new := Array.replicate splitNumClasses 0
        newTot := 0
  return cuts.toList

/-- The cut list equivalent to `emitSharedBlocks`'s fixed cadence: multiples of
    `max tokChunk 1` strictly below `n`. `emitSharedBlocksAt … (fixedCadenceCuts
    tokChunk toks.size)` emits byte-for-byte what `emitSharedBlocks … tokChunk`
    emits (pinned by a conformance test). -/
def fixedCadenceCuts (tokChunk n : Nat) : List Nat :=
  let step := max tokChunk 1
  (List.range ((n + step - 1) / step)).filterMap fun k =>
    if k == 0 then none else some (k * step)

/-- Exact bit size of the shared-window block stream `emitSharedBlocksAt` would
    emit for this partition, without emitting: per group, `3` header bits plus
    the dynamic-tree header (sized by running `writeDynamicHeader` into an
    empty writer, as `dynBlockBytes` does) plus the freq·codeLen dot product
    (`symbolBitCount`, which includes the end-of-block symbol). Mirrors the
    emitter's grouping exactly — same clamped cut `j`, same final-block test —
    so `(emitSharedBlocksAt …).bitLength` equals this sum (pinned by a
    `SizeHelpers` conformance test; the flushed byte size is `⌈bits/8⌉`). -/
def sharedPartitionBits (toks : Array LZ77Token) (cuts : List Nat) (pos : Nat) : Nat :=
  let j := min (max (cuts.headD toks.size) (pos + 1)) toks.size
  let f := tokenFreqs (toks.extract pos j)
  let lens := dynamicCodeLengths f.1 f.2
  let blockBits := 3 + (writeDynamicHeader BitWriter.empty lens.1 lens.2).bitLength
    + symbolBitCount f.1 f.2 lens.1.toArray lens.2.toArray
  if j ≥ toks.size then blockBits
  else blockBits + sharedPartitionBits toks cuts.tail j
termination_by toks.size - pos
decreasing_by
  rename_i h
  simp only [Nat.not_le] at h
  omega

/-- Cost-model arbitration between the entropy-divergence cuts and the fixed
    `sharedTokChunk` cadence: size both partitions in exact unflushed bits and
    keep the smaller, **ties → fixed**. Since the emitted stream is one final
    flush of exactly those bits (byte size `⌈bits/8⌉`), heuristic bits ≤ fixed
    bits implies the emitted candidate never exceeds the old fixed-cadence one
    — any observed regression is a `sharedPartitionBits` conformance bug, not
    rounding. The sizing costs two extra `O(tokens)` passes; the matcher still
    dominates at the levels that use this. -/
def chooseSplitsArbitrated (toks : Array LZ77Token) : List Nat :=
  let h := chooseSplitsHeuristic toks
  let f := fixedCadenceCuts sharedTokChunk toks.size
  if sharedPartitionBits toks h 0 < sharedPartitionBits toks f 0 then h else f

/-! ## Sized-tree reuse for the winning partition (Wave 5, #2552)

`chooseSplitsArbitrated` already builds every block's Huffman trees
(`dynamicCodeLengths` over `tokenFreqs` of the group) while *sizing* the two
candidate partitions; `emitSharedBlocksAt` then rebuilt the same trees a third
time for the winning partition at emission. The variants below return the cuts
*together with* the winner's per-block sized trees and feed them to a
tree-taking emitter, so emission never re-runs the frequency pass or the
Huffman build. `emitSharedBlocksAt` stays as the reference emitter:
`deflateDynamicBlocksSharedSized_eq` (`Zip/Spec/DeflateBlockSplit.lean`) proves
the sized pipeline byte-identical, so the spec quadruple is untouched. -/

/-- A per-block pair of code-length lists carrying the alphabet-size facts the
    emitter needs (286 lit/len, 30 distance) — what `dynamicCodeLengths`
    produces, bundled with `dynamicCodeLengths_length`. -/
def SizedTrees : Type :=
  {p : List Nat × List Nat // p.1.length = 286 ∧ p.2.length = 30}

/-- The sized trees `dynamicCodeLengths` selects for the given frequencies. -/
@[inline] def sizedTrees (litFreqs distFreqs : Array Nat) : SizedTrees :=
  ⟨dynamicCodeLengths litFreqs distFreqs,
    (dynamicCodeLengths_length litFreqs distFreqs).1,
    (dynamicCodeLengths_length litFreqs distFreqs).2⟩

/-- The sized trees of the empty token group: the (never-reached) `headD`
    default in `emitSharedBlocksAtSized` — the trees list produced by
    `sharedPartitionSized` always covers every emitted block. -/
def emptySizedTrees : SizedTrees :=
  sizedTrees (tokenFreqs #[]).1 (tokenFreqs #[]).2

/-- `sharedPartitionBits` fused with tree collection: walk the partition once,
    returning the exact bit size **together with** each block's sized trees, so
    the winning partition's emission can reuse them instead of re-running
    `tokenFreqs` + `dynamicCodeLengths` per block. Component 1 is exactly
    `sharedPartitionBits` (`sharedPartitionSized_fst`); component 2's entries
    are definitionally `dynamicCodeLengths (tokenFreqs group)` of the emitter's
    groups (`emitSharedBlocksAtSized_eq`). -/
def sharedPartitionSized (toks : Array LZ77Token) (cuts : List Nat) (pos : Nat) :
    Nat × List SizedTrees :=
  let j := min (max (cuts.headD toks.size) (pos + 1)) toks.size
  let f := tokenFreqs (toks.extract pos j)
  let t := sizedTrees f.1 f.2
  let blockBits := 3 + (writeDynamicHeader BitWriter.empty t.val.1 t.val.2).bitLength
    + symbolBitCount f.1 f.2 t.val.1.toArray t.val.2.toArray
  if j ≥ toks.size then (blockBits, [t])
  else
    let rest := sharedPartitionSized toks cuts.tail j
    (blockBits + rest.1, t :: rest.2)
termination_by toks.size - pos
decreasing_by
  rename_i h
  simp only [Nat.not_le] at h
  omega

/-- Tree-taking twin of `emitSharedBlocksAt`: same clamped cut points, but each
    block's `(litLens, distLens)` come from the `trees` list (in lockstep with
    `cuts`) instead of being recomputed from the group. Byte-identical to
    `emitSharedBlocksAt` when `trees` is the sizing pass's output
    (`emitSharedBlocksAtSized_eq`). -/
def emitSharedBlocksAtSized (data : ByteArray) (toks : Array LZ77Token) (cuts : List Nat)
    (trees : List SizedTrees) (pos : Nat) (bw : BitWriter) : BitWriter :=
  let j := min (max (cuts.headD toks.size) (pos + 1)) toks.size
  let t := trees.headD emptySizedTrees
  let bw := emitDynBlock bw data (toks.extract pos j) t.val.1 t.val.2
    t.property.1 t.property.2 (decide (j ≥ toks.size))
  if j ≥ toks.size then bw
  else emitSharedBlocksAtSized data toks cuts.tail trees.tail j bw
termination_by toks.size - pos
decreasing_by
  rename_i h
  simp only [Nat.not_le] at h
  omega

/-- `chooseSplitsArbitrated` returning the winning cuts **with** the winner's
    per-block sized trees (component 1 is exactly `chooseSplitsArbitrated` —
    via `sharedPartitionSized_fst`, see `deflateDynamicBlocksSharedSized_eq`).
    The sizing of both candidates is inherent to arbitration; only the third
    (emission-time) tree pass is avoidable, and the returned trees are what
    avoid it. -/
def chooseSplitsArbitratedSized (toks : Array LZ77Token) : List Nat × List SizedTrees :=
  let h := chooseSplitsHeuristic toks
  let f := fixedCadenceCuts sharedTokChunk toks.size
  let sh := sharedPartitionSized toks h 0
  let sf := sharedPartitionSized toks f 0
  if sh.1 < sf.1 then (h, sh.2) else (f, sf.2)

/-- The arbitrated shared-window candidate with sized-tree reuse: byte-identical
    to `deflateDynamicBlocksSharedAtTokens data toks chooseSplitsArbitrated`
    (`deflateDynamicBlocksSharedSized_eq`), but the winning partition's
    per-block `tokenFreqs` + `dynamicCodeLengths` run once (during sizing)
    instead of twice. -/
def deflateDynamicBlocksSharedSized (data : ByteArray) (toks : Array LZ77Token) : ByteArray :=
  if data.size == 0 then
    let f := tokenFreqs #[]
    (emitDynBlock BitWriter.empty data #[] (dynamicCodeLengths f.1 f.2).1 (dynamicCodeLengths f.1 f.2).2
      (dynamicCodeLengths_length f.1 f.2).1 (dynamicCodeLengths_length f.1 f.2).2 true).flush
  else
    let c := chooseSplitsArbitratedSized toks
    (emitSharedBlocksAtSized data toks c.1 c.2 0 BitWriter.empty).flush

/-- The compressed-block dispatch (no stored fallback). Every level ≥ 1 uses the
    hash-chain matcher with the level's search depth (`chainDepth`) and interior
    insertion cap (`insertCap`): low levels defer insertion + search shallowly
    (fast, lower ratio), high levels insert everything + search deeply (slower,
    best ratio). One shared token pass sizes the fixed and dynamic blocks and
    emits only the smaller (strict `<`, dynamic on a tie). -/
def deflateCompressed (data : ByteArray) (level : UInt8) : ByteArray :=
  let tokens := lzMatch data level
  let f := tokenFreqs tokens
  let lens := dynamicCodeLengths f.1 f.2
  if fixedBlockBytes f.1 f.2 < dynBlockBytes f.1 f.2 lens.1 lens.2
  then deflateFixedBlock data tokens
  -- Reuse the sized `lens` for emission (= `deflateDynamicBlock data tokens`,
  -- but without recomputing the code lengths).
  else deflateDynamicBlockCore data tokens lens.1 lens.2
    (dynamicCodeLengths_length f.1 f.2).1 (dynamicCodeLengths_length f.1 f.2).2

/-- The single-block cost-model dispatch for level ≥ 1: stored / fixed / dynamic,
    all *sized* from one shared token pass, emitting only the winner. Falls back to
    a stored block whenever that is smaller, so incompressible input never expands.
    This is the base candidate that the block-split streams are compared against. -/
def deflateRawBaseTokens (data : ByteArray) (tokens : Array LZ77Token) : ByteArray :=
  let f := tokenFreqs tokens
  let lens := dynamicCodeLengths f.1 f.2
  let fixedBytes := fixedBlockBytes f.1 f.2
  let dynBytes := dynBlockBytes f.1 f.2 lens.1 lens.2
  -- Size the stored candidate in O(⌈|data|/65535⌉) via `storedBlockBytes`
  -- (= `(deflateStoredPure data).size`, `storedBlockBytes_eq`) and *only*
  -- materialize the ~|data|-byte stored block when it actually wins — otherwise
  -- every compressible input paid to build and discard a full-size copy.
  let storedBytes := storedBlockBytes data
  if storedBytes < (if fixedBytes < dynBytes then fixedBytes else dynBytes) then deflateStoredPure data
  else if fixedBytes < dynBytes then deflateFixedBlock data tokens
  else deflateDynamicBlockCore data tokens lens.1 lens.2
    (dynamicCodeLengths_length f.1 f.2).1 (dynamicCodeLengths_length f.1 f.2).2

/-- `deflateRawBaseTokens` over a *packed* token stream (Wave 3b stages B+C):
    the frequency pass runs natively on the packed words (`tokenFreqsP`), and
    the emit branches consume the packed words directly
    (`deflateFixedBlockP`/`deflateDynamicBlockCoreP`) — no branch ever
    materializes boxed tokens. Equal to
    `deflateRawBaseTokens data (ptokens.map unpackTok)` via `tokenFreqsP_eq`
    and the packed-emitter equalities (`Zip/Spec/EmitPackedCorrect.lean`);
    `deflateRawBaseTokens` stays as the boxed reference implementation
    (conformance-tested in `ZipTest/PackedTokens.lean`).

    The dynamic-tree header plan (`dynHeaderCodes`) is built **once** and reused
    for both sizing (`dynBlockBytesWith`) and emit (`deflateDynamicBlockCorePWith`)
    rather than rebuilt in each — the #2627 dedup; equal to the un-deduped form by
    `dynBlockBytesWith_dynHeaderCodes` / `deflateDynamicBlockCorePWith_dynHeaderCodes`
    (used in `deflateRawBase_def`). -/
def deflateRawBaseP (data : ByteArray) (ptokens : Array UInt32) : ByteArray :=
  let f := tokenFreqsP ptokens
  let lens := dynamicCodeLengths f.1 f.2
  let plan := dynHeaderCodes lens.1 lens.2
  have hcl : plan.clCodes.size ≥ 19 :=
    Nat.le_of_eq (dynHeaderCodes_clCodes_size lens.1 lens.2).symm
  let fixedBytes := fixedBlockBytes f.1 f.2
  let dynBytes := dynBlockBytesWith f.1 f.2 lens.1 lens.2 plan hcl
  let storedBytes := storedBlockBytes data
  if storedBytes < (if fixedBytes < dynBytes then fixedBytes else dynBytes) then deflateStoredPure data
  else if fixedBytes < dynBytes then deflateFixedBlockP data ptokens
  else deflateDynamicBlockCorePWith data ptokens lens.1 lens.2 plan hcl
    (dynamicCodeLengths_length f.1 f.2).1 (dynamicCodeLengths_length f.1 f.2).2

/-- `deflateRawBaseP` over this level's *packed* `lzMatchP` stream
    (definitional wrapper, `deflateRawBaseP_def`). Equal to the boxed
    `deflateRawBaseTokens data (lzMatch data level)` — that equation is
    `deflateRawBase_def`, proven in `Zip/Spec/LZ77PackedCorrect.lean` via
    `tokenFreqsP_eq` + `lzMatchP_map`. -/
def deflateRawBase (data : ByteArray) (level : UInt8) : ByteArray :=
  deflateRawBaseP data (lzMatchP data level)

theorem deflateRawBaseP_def (data : ByteArray) (level : UInt8) :
    deflateRawBaseP data (lzMatchP data level) = deflateRawBase data level := rfl

theorem deflateDynamicBlocksSharedAt_def (data : ByteArray)
    (choose : Array LZ77Token → List Nat) (level : UInt8) :
    deflateDynamicBlocksSharedAtTokens data (lzMatch data level) choose =
      deflateDynamicBlocksSharedAt data choose level := rfl

/-! ## Near-optimal candidate (level 9) -/

/-- Input-size gate for the near-optimal candidate. Measured (#2537, GNU
    time MaxRSS of the ungated candidate on silesia/mozilla slices): 793 MB
    peak at 16 MiB input, 1.73 GB at 52 MiB — ≈27 B of transient state per
    input byte marginal (global choice arrays + per-region cache + token
    stream) over the process baseline. 64 MiB covers every Silesia file at a
    projected ~2.1 GB peak, acceptable for the max-effort tier; truly huge
    inputs still fall back to the plain level-9 path. A pure dispatch knob —
    `pickSmaller` composes either way. -/
def optimalMaxSize : Nat := 67108864

/-- Cross-block (shared-window) block-split dynamic compression over the
    **near-optimal** token stream: like `deflateDynamicBlocksShared`, but the
    tokens come from the cost-model DP parser (`lz77OptimalIter`) instead of
    the greedy/lazy matcher. See `Zip.Native.DeflateParse`. -/
def deflateDynamicBlocksOptimal (data : ByteArray) (tokChunk : Nat) : ByteArray :=
  if data.size == 0 then
    let f := tokenFreqs #[]
    (emitDynBlock BitWriter.empty data #[] (dynamicCodeLengths f.1 f.2).1 (dynamicCodeLengths f.1 f.2).2
      (dynamicCodeLengths_length f.1 f.2).1 (dynamicCodeLengths_length f.1 f.2).2 true).flush
  else
    (emitSharedBlocks data (lz77OptimalIter data) tokChunk 0 BitWriter.empty).flush

/-! ## Incompressible pre-scan

`deflateRaw` already falls back to a stored block whenever every compressed
candidate is larger — but it only learns this *after* paying the full hash-chain
match pass (and, at level 9, the optimal-parse DP), which is essentially the
whole compress cost and finds almost nothing on incompressible input. Measured
(`bench compress-pareto`, 4 MiB PRNG): level 9 runs at ≈2.5 MB/s, all of it
wasted before the stored fallback. The pre-scan reads up to ≈128 KiB of bounded
sample and, when the input is unambiguously incompressible, routes straight to
`deflateStoredPure` so the matcher never runs; a compressible file fails the
first sampled region and falls through to the normal path almost immediately. -/

/-- Minimum input size for the incompressible pre-scan to engage. The pre-scan's
    fixed cost (one presence-table allocation + a region scan) is only worth paying
    when the matcher it might skip is the dominant cost, i.e. on large inputs; below
    1 MiB the matcher is cheap enough that the scan would be net overhead on the
    common compressible file, so small inputs always take the normal path. This is
    why the gate leaves the Canterbury/Silesia dashboard untouched — every corpus
    file is either compressible or under the size gate. -/
def prescanMinSize : Nat := 1048576

/-- Number of contiguous sample regions the pre-scan reads, spread end to end
    across the input (first at offset 0, last ending at `n`). A region that looks
    even slightly compressible short-circuits the whole scan, so a normal
    compressible file pays for at most the first region. -/
def prescanRegions : Nat := 4

/-- Bytes per sample region. Each region is scanned *contiguously* and every
    consecutive 4-gram is inserted, so repetition is detected densely the way the
    matcher itself finds matches. At 32 KiB a region spans two of the common
    page/block sizes (4/8/16 KiB), so a repeated block surfaces as a wall of
    4-gram collisions. ≤`prescanRegions · prescanRegionBytes` (128 KiB) bytes are
    scanned, independent of input size. -/
def prescanRegionBytes : Nat := 32768

/-- log2 of the per-region 4-gram presence-table size (2^20 slots). Sized so that,
    over the ≈32 K 4-grams of one region, the false-collision rate of genuinely
    random input is ≈1.6% (`S²/2·tableSize`) — half the repeat gate, so random data
    reads as "no repeats" with a comfortable margin while keeping the per-region
    allocation small. -/
def prescanTableBits : Nat := 20

/-- Order-0 entropy (bits/byte) of a 256-bucket byte histogram with `total`
    samples; `0` when `total = 0`. Pulled out so the per-region gate can call it
    without an inline fold. -/
def histEntropy (hist : Array Nat) (total : Nat) : Float := Id.run do
  if total == 0 then return 0.0
  let t := total.toFloat
  let mut e : Float := 0.0
  for c in hist do
    if c != 0 then
      let pr := c.toFloat / t
      e := e - pr * Float.log2 pr
  return e

/-- Cheap bounded test for *genuinely* incompressible input (already-compressed,
    encrypted, or random bytes), where the full match pass is wasted work before
    `deflateRaw`'s stored fallback. Scans up to `prescanRegions` contiguous regions
    spread across the input (cost independent of input size) and returns `true`
    only when *every* region is BOTH

    * near-maximal order-0 entropy (≈8 bits/byte), so Huffman coding cannot shrink
      it; and
    * free of recurring 4-grams, so the matcher would find no usable LZ77 match
      (its 32 KiB window fits inside a region, so any match it could make shows up
      here as a collision).

    The moment a region fails either test the scan stops and returns `false`, so a
    compressible file is rejected after one region and never pays the full sample.
    Requiring both signals on every region keeps the gate conservative: text (low
    entropy), base64 and other restricted alphabets (entropy ≈ 6), run-length-y
    binary, and repeated-block data (dense within-region 4-gram repeats) all bail
    out. Self-similar data whose period exceeds the 32 KiB window (e.g. `R ++ R`
    for a 512 KiB `R`) is genuinely incompressible by DEFLATE and is correctly
    stored. The 4-gram table is a single-hash presence filter, so its false
    collisions only ever *raise* the measured repeat count — they bias toward the
    (safe) compressed path, never toward storing.

    The result is opaque to correctness: a `true` only routes to
    `deflateStoredPure`, which is valid for every input, so a false positive costs
    ratio (a stored compressible block) but never correctness. -/
def incompressiblePrescan (data : ByteArray) : Bool := Id.run do
  if data.size < prescanMinSize then
    return false
  let n := data.size
  let tableSize := 1 <<< prescanTableBits
  let shift : UInt32 := (32 - prescanTableBits).toUInt32
  let regBytes := min prescanRegionBytes n
  -- `span` is the last legal region start (so a region never runs past `n`).
  -- `r * span / (prescanRegions - 1)` puts the first region at 0 and the last at
  -- `span` (ending exactly at `n`); regions overlap harmlessly when `n` is small.
  let span := n - regBytes
  for r in [0:prescanRegions] do
    let start := if prescanRegions ≤ 1 then 0 else min ((r * span) / (prescanRegions - 1)) span
    let stop := min (start + regBytes) n
    -- Cheap test first: the byte histogram needs no big table, so most
    -- compressible data (text/source/html — low order-0 entropy) bails here, after
    -- a single histogram pass and before the per-region table is ever allocated.
    let mut hist : Array Nat := Array.replicate 256 0
    let mut bytesSeen : Nat := 0
    for i in [start:stop] do
      let b := data[i]!.toNat
      hist := hist.set! b (hist[b]! + 1)
      bytesSeen := bytesSeen + 1
    -- (1) High entropy: order-0 entropy ≥ 7.6 bits/byte (random ≈ 7.99). A region
    --     too short to judge (`bytesSeen = 0`) also bails to the safe path.
    if bytesSeen == 0 || histEntropy hist bytesSeen < 7.6 then
      return false
    -- (2) No repeats: a high-entropy region might still be repeated-block data the
    --     matcher could compress, so insert every 4-gram into a fresh presence
    --     table (window-sized region ⇒ any matcher-usable repeat collides here) and
    --     require collisions < 3.125% of sampled 4-grams (`*32 < sampled`).
    --     Genuinely random input sits at ≈1.6% (table false collisions only).
    let mut table : Array UInt8 := Array.replicate tableSize 0
    let mut sampled : Nat := 0       -- 4-grams hashed in this region
    let mut collisions : Nat := 0    -- 4-grams hitting an already-seen slot
    let mut p := start
    while p + 3 < stop do
      let a := data[p]!.toUInt32
      let b := data[p+1]!.toUInt32
      let c := data[p+2]!.toUInt32
      let d := data[p+3]!.toUInt32
      let word := a ||| (b <<< 8) ||| (c <<< 16) ||| (d <<< 24)
      let idx := ((word * 2654435761) >>> shift).toNat
      if table[idx]! != 0 then
        collisions := collisions + 1
      else
        table := table.set! idx 1
      sampled := sampled + 1
      p := p + 1
    if sampled == 0 || collisions * 32 ≥ sampled then
      return false
  -- Every region looked incompressible.
  return true

/-- Unified raw DEFLATE compression dispatch. Level 0 = stored; levels 1–7 run the
    single-block cost-model dispatch (`deflateRawBase`). At the max-compression
    tiers (level ≥ 8) two block-split streams are also tried, and the smallest of
    all candidates is emitted:
      * self-contained split — per-chunk Huffman trees, fresh window per chunk
        (wins on locally-varying statistics, e.g. structured binary);
      * cross-block (shared-window) split — one whole-file match pass, token stream
        partitioned per block, references cross block boundaries (wins on large
        text, where the self-contained split loses cross-chunk matches). The
        partition comes from the entropy-divergence heuristic arbitrated in
        exact bits against the fixed `sharedTokChunk` cadence
        (`chooseSplitsArbitrated`), so it cuts where the symbol statistics
        shift and never sizes worse than the fixed cadence; emission reuses
        the winner's per-block trees from the sizing pass
        (`deflateDynamicBlocksSharedSized`, = the reference candidate by
        `deflateDynamicBlocksSharedSized_eq`).
    At level 9 (and within the `optimalMaxSize` memory gate) a fourth candidate
    joins: the cross-block stream over the **near-optimal** cost-model DP parse
    (`deflateDynamicBlocksOptimal`), which chooses the globally cheapest token
    sequence under an estimated bit cost instead of the locally longest match.
    The splits are first-class candidates compared against the whole base via
    `pickSmaller`, *not* nested inside the dynamic branch: on large heterogeneous
    inputs a single dynamic tree loses to fixed Huffman, so a base-internal gate
    would never reach the split even though it wins by 15–19%. `pickSmaller`
    guarantees we never regress below the base; the default level 6 stays
    single-block so it pays no extra compress time. All branches are
    roundtrip-verified.

    The split entry sits at level ≥ 8 (was ≥ 7): the single-block → split transition is
    a hard ~2.5–3× compress-speed cliff (a second whole-file encode plus the partition
    sizing), and levels 7 and 8 both paid it, landing coincident (they differed only in
    chain depth, which saturates). Promoting level 7 to the *strongest single-block*
    point (full lazy lookahead, chain depth 256) de-collapses the pair: level 7 fills the
    empty band between level 6 and the split tier — on Canterbury outside the prior hull,
    on Silesia a distinct Pareto-efficient point on it — while level 8 still emits the
    split ratio level 7 used to carry (same candidate, deeper chain; empirically
    equal-or-better on the measured corpora). The matcher knobs cannot separate the two
    split levels (chain depth and the lazy gate are quality-for-speed tradeoffs that
    trace one frontier); pushing the frontier itself out is the work of #2696 (chain
    self-throttle) and #2638 (near-optimal parse). See #2698.

    Before any of that, an `incompressiblePrescan` reads a bounded sample (≤128 KiB,
    short-circuited on the first compressible region) and, on unambiguously
    incompressible input, dispatches straight to `deflateStoredPure` — skipping the
    match pass entirely (the bulk of compress time, ≈2.5 MB/s at level 9 on random
    data) for a result the cost model would have chosen anyway. The gate is
    conservative (see `incompressiblePrescan`) and opaque to correctness: it only
    ever selects the already-proven stored block. -/
def deflateRaw (data : ByteArray) (level : UInt8 := 6) : ByteArray :=
  if level == 0 then deflateStoredPure data
  else if incompressiblePrescan data then deflateStoredPure data
  else if 8 ≤ level then
    -- One *packed* matcher pass shared by the base and shared-split candidates
    -- (the matcher is 83–84% of each candidate's cost — Wave-0 profile, D-2).
    -- The base candidate consumes the packed words end-to-end (freqs *and*
    -- emit, stage C); the shared-split candidate still unpacks once (stage D
    -- moves it onto packed words).
    let ptokens := lzMatchP data level
    if 9 ≤ level ∧ data.size ≤ optimalMaxSize then
      pickSmaller
        (pickSmaller (deflateRawBaseP data ptokens)
          (pickSmaller (deflateDynamicBlocksSC data splitChunkSize level)
            (deflateDynamicBlocksSharedSized data (ptokens.map unpackTok))))
        (deflateDynamicBlocksOptimal data sharedTokChunk)
    else
      -- Level 8: base vs cross-block split. The self-contained split is demoted to
      -- level 9 (it wins on exactly one corpus file while paying a full per-chunk
      -- match pass). Level 7 no longer enters here — it is the top single-block
      -- point (see the dispatch docstring), so the split tier starts at level 8.
      pickSmaller (deflateRawBaseP data ptokens)
        (deflateDynamicBlocksSharedSized data (ptokens.map unpackTok))
  else deflateRawBase data level

end Zip.Native.Deflate
