import Zip.Native.Deflate
import Zip.Native.DeflateFreqs
import Zip.Native.DeflateFreqsFused
import Zip.Spec.DeflateFreqsFusedCorrect
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

/-! ## Packed Huffman-code tables (#2827)

`litCodes`/`distCodes` are `Array (UInt16 × UInt8)`: every per-token code
lookup fetches a boxed `Prod` cell and chases it with two `lean_ctor_get`s,
and every `writeHuffCode` re-reverses the code's bits (`reverse16`, an
out-of-line call) and down-shifts them — per symbol, for values that are
table constants. Packing each entry into one `UInt32` holding the
**pre-reversed** code (`reverse16 code >>> (16 - len)`, bits 0–15) and the
bit length (bits 16–23) turns the lookup into a single tagged-scalar array
read plus two register ops, and lets the walk write through the leaner
`BitWriter.writeRevCode` (no per-symbol reversal). `emitTokensWithCodesPT`
is the packed-table twin of `emitTokensWithCodesP` (equal by
`emitTokensWithCodesPT_eq`, `Zip/Spec/EmitPackedCorrect.lean`); the block
emitters pack the tables once per block (`packCodeTab`, ≤ 316 entries)
before the token walk. -/

/-- Pack one canonical-code entry `(code, bitLength)` into a `UInt32`:
    the LSB-first packing-order reversal `reverse16 code >>> (16 - len)` in
    bits 0–15 (always < 2¹⁶, so the `UInt16` round-trip is lossless), and the
    bit length in bits 16–23. -/
@[inline] def packCodeEntry (e : UInt16 × UInt8) : UInt32 :=
  ((BitWriter.reverse16 e.1).toUInt64 >>> (16 - e.2.toUInt64)).toUInt16.toUInt32 |||
    (e.2.toUInt32 <<< 16)

/-- Pack a canonical-code table for the emit loop (one `UInt32` per entry). -/
def packCodeTab (t : Array (UInt16 × UInt8)) : Array UInt32 :=
  t.map packCodeEntry

@[simp] theorem packCodeTab_size (t : Array (UInt16 × UInt8)) :
    (packCodeTab t).size = t.size := Array.size_map ..

/-- Packed-table twin of `emitRefWithCodesP`: identical branch structure,
    with each `(code, len)` pair read replaced by one packed-word read
    (`e.toUInt16` / `(e >>> 16).toUInt8`) written through `writeRevCode`
    (the table code is pre-reversed). Equal to `emitRefWithCodesP` over
    `packCodeTab` (`emitRefWithCodesPT_eq`). -/
@[inline] def emitRefWithCodesPT (bw : BitWriter)
    (litT distT : Array UInt32) (w : UInt32) : BitWriter :=
  let lw := lenCodeWord (((w >>> 16) &&& 0x7FFF).toNat)
  let idx := codeIdx lw
  if hlitlt : idx + 257 < litT.size then
    let e := litT[idx + 257]
    let bw := bw.writeRevCodeExtra e.toUInt16 (e >>> 16).toUInt8 (codeExtra lw) (codeVal lw)
    let dw := distCodeWord ((w &&& 0xFFFF).toNat)
    let dIdx := codeIdx dw
    if hdistlt : dIdx < distT.size then
      let de := distT[dIdx]
      bw.writeRevCodeExtra de.toUInt16 (de >>> 16).toUInt8 (codeExtra dw) (codeVal dw)
    else bw
  else bw

/-- Packed-table twin of `emitTokensWithCodesP` (same size hypotheses, now on
    the packed tables): walk the packed token stream reading Huffman codes
    from `packCodeTab`-packed `UInt32` tables. Equal to `emitTokensWithCodesP`
    for every word array (`emitTokensWithCodesPT_eq`). -/
def emitTokensWithCodesPT (bw : BitWriter) (tokens : Array UInt32)
    (litT distT : Array UInt32)
    (hlit : litT.size ≥ 286) (hdist : distT.size ≥ 30)
    (i : Nat) : BitWriter :=
  if h : i < tokens.size then
    let w := tokens[i]
    if w &&& ((1 : UInt32) <<< 31) = 0 then
      have : w.toUInt8.toNat < litT.size := by
        have := UInt8.toNat_lt w.toUInt8; omega
      let e := litT[w.toUInt8.toNat]
      emitTokensWithCodesPT (bw.writeRevCode e.toUInt16 (e >>> 16).toUInt8) tokens litT distT
        hlit hdist (i + 1)
    else
      emitTokensWithCodesPT (emitRefWithCodesPT bw litT distT w) tokens litT distT
        hlit hdist (i + 1)
  else bw
termination_by tokens.size - i



/-- USize-index twin of `emitTokensWithCodesPT` (measurement candidate): same
    walk with the loop index in `USize`, `uget` token reads, and the
    addressability witness `hsz` hoisted out of the loop. Equal to
    `emitTokensWithCodesPT` at `i.toNat` (`emitTokensWithCodesPTU_eq`). -/
def emitTokensWithCodesPTU (bw : BitWriter) (tokens : Array UInt32)
    (litT distT : Array UInt32)
    (hlit : litT.size ≥ 286) (hdist : distT.size ≥ 30)
    (hsz : tokens.size < USize.size)
    (i : USize) : BitWriter :=
  if h : i.toNat < tokens.size then
    let w := tokens.uget i (by exact h)
    have hstep : (i + 1).toNat = i.toNat + 1 := by
      have hUS : USize.size = 2 ^ System.Platform.numBits := rfl
      rw [USize.toNat_add, USize.toNat_one]; exact Nat.mod_eq_of_lt (by omega)
    if w &&& ((1 : UInt32) <<< 31) = 0 then
      have : w.toUInt8.toNat < litT.size := by
        have := UInt8.toNat_lt w.toUInt8; omega
      let e := litT[w.toUInt8.toNat]
      emitTokensWithCodesPTU (bw.writeRevCode e.toUInt16 (e >>> 16).toUInt8) tokens litT distT
        hlit hdist hsz (i + 1)
    else
      emitTokensWithCodesPTU (emitRefWithCodesPT bw litT distT w) tokens litT distT
        hlit hdist hsz (i + 1)
  else bw
termination_by tokens.size - i.toNat
decreasing_by all_goals (rw [hstep]; omega)

/-- Guarded dispatch to the USize emit loop: one `USize` round-trip check per
    block unlocks the de-boxed index walk; the (never-taken) fallback is the
    `Nat` loop, so this equals `emitTokensWithCodesPT ... 0`
    (`emitTokensWithCodesPTG_eq`). -/
@[inline] def emitTokensWithCodesPTG (bw : BitWriter) (tokens : Array UInt32)
    (litT distT : Array UInt32)
    (hlit : litT.size ≥ 286) (hdist : distT.size ≥ 30) : BitWriter :=
  if hg : tokens.size.toUSize.toNat = tokens.size then
    have hsz : tokens.size < USize.size := by
      rw [← hg]; exact USize.toNat_lt_two_pow_numBits _
    emitTokensWithCodesPTU bw tokens litT distT hlit hdist hsz 0
  else
    emitTokensWithCodesPT bw tokens litT distT hlit hdist 0

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
    have hlitT_size : (packCodeTab litCodes).size ≥ 286 := by
      rw [packCodeTab_size]; exact hlit_size
    have hdistT_size : (packCodeTab distCodes).size ≥ 30 := by
      rw [packCodeTab_size]; exact hdist_size
    let bw := emitTokensWithCodesPTG bw tokens (packCodeTab litCodes) (packCodeTab distCodes)
      hlitT_size hdistT_size
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
    have hlitT_size : (packCodeTab litCodes).size ≥ 286 := by
      rw [packCodeTab_size]; exact hlit_size
    have hdistT_size : (packCodeTab distCodes).size ≥ 30 := by
      rw [packCodeTab_size]; exact hdist_size
    let bw := emitTokensWithCodesPTG bw tokens (packCodeTab litCodes) (packCodeTab distCodes)
      hlitT_size hdistT_size
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

/-- Lazy `pickSmaller` keyed on precomputed byte sizes: forces (emits) only the
    winning candidate. When `sa = (a ()).size` and `sb = (b ()).size` this equals
    `pickSmaller (a ()) (b ())` byte-for-byte (`a` wins iff strictly smaller, ties
    keep `b`), but the losing candidate is never emitted — the whole point of
    sizing every candidate before emitting any. Correctness of the byte-identity
    (that `sa`/`sb` are the true emitted sizes) is pinned by the `SizeHelpers`
    conformance tests, exactly as the single-block `fixedBlockBytes`/`dynBlockBytes`
    dispatch is; the roundtrip theorems only need each candidate to decode. -/
@[inline] def emitSmallerBy (sa : Nat) (a : Unit → ByteArray)
    (sb : Nat) (b : Unit → ByteArray) : ByteArray :=
  if sa < sb then a () else b ()

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

/-- Hash-chain search depth per compression level. Higher levels generally
    search deeper for longer matches (better ratio on diverse input) at higher
    cost; the `chainWalk` early-stop keeps repetitive input fast at any depth.
    The ratio gain saturates around 256–512 (measured), so level 9 caps there.

    The mid-band values are the `mid-sweep` optimum for the #2737 ladder
    (Silesia grid over chain × `goodMatch` × split, then interleaved pinned
    timing): L4 = 64 (with the lazy gate, the old L5 point). **L5 = 24 since
    the L5 re-grid** (`gate-sweep`, run after the hash3 singleton #2824, gm/ld
    re-grid #2825, and greedy re-grid #2830 landings): the old L5 = (128,
    single-block, gate off) had fallen ~14% inside the L4↔L6 mixing line — the
    recent landings made the split tier so much cheaper that a shallow-chain
    *split* point (chain 24, gate 64, probe /4, no singleton) matches the old
    L5's speed while banking −0.53pp weighted-Silesia ratio (0.3302 → 0.3249),
    +4% above the blend; every deeper single-block point stayed inside it.
    **L6's depth drops back to 64 on purpose** (the split tier historically
    started there): at equal
    cycles the observation-divergence split + a shallow chain beats a deep
    chain without the split — the block-split, not the chain, is L6's budget.
    **L7 also sits at 64 since the post-singleton re-grid** (the hash3
    singleton, gate-sweep over chain × gate × probe depth): with length-3
    coverage paying the ratio bill, (chain 64, gate off, probe /2) lands at
    0.3196 weighted-Silesia ratio — beyond what the old chain-256 L7 reached —
    so the deep-chain point fell inside the new frontier and L7 adopts the old
    L6 config wholesale. L8 keeps 512; past that the chain saturates.

    **L2/L3 dropped to 8/16 in the greedy re-grid** (`l1-sweep2`, run after the
    merged-greedy-loop and packed-emit landings shifted the tier's cost
    balance): with the `niceLen` cutoff disabled (see there), (chain 8, cap 8)
    matches the old L2's weighted-Silesia ratio exactly at +12% speed, and
    (chain 16, cap 32) beats the old L3 on both axes — the old rows sat ~10%
    below the greedy-band mixing frontier.

    Level 1 is the `deflate_fast` corner (#2726): depth `4` is exactly zlib
    `-1`'s `max_chain`. A tokens-held-constant attribution on Silesia (see
    `ZipL1Attrib`/`ZipL1Sweep`) showed L1 is emit-bound — the token walk +
    `BitWriter` dominate, and fixed-only emission is *not* materially faster than
    the dynamic-arbitrated base while giving up 6.5–25% ratio, so fixed-only was
    rejected. Shallowing the chain (8→4) alongside an aggressive insert cap
    (`insertCap`, 16→2) is the precedented fast policy that keeps the normal
    stored/static/dynamic arbitration: +19% end-to-end MB/s on Silesia (56.0→66.4,
    in-binary A/B on a quiet pinned core) at a +4.2% geomean-ratio cost
    (0.347→0.361 — still *below* the 0.38–0.40 fast-band ceiling the issue targets,
    so ratio headroom remains), every file same-or-faster, worst single-file ratio
    regression +8.6% (reymont). The intermediate `insertCap = 4` is a more
    conservative point (+15% e2e at ratio 0.356, worst file +6.3%). -/
def chainDepth (level : UInt8) : Nat :=
  if level ≤ 1 then 4
  else if level ≤ 2 then 8
  else if level ≤ 3 then 16
  else if level ≤ 4 then 64
  else if level ≤ 5 then 24
  else if level ≤ 7 then 64
  else if level ≤ 8 then 512
  else 1024

/-- Per-level interior-insertion cap (zlib's `deflate_fast`/`deflate_slow` split):
    fast levels (1–3) defer most interior `updateHashes` insertions for speed at a
    ratio cost; levels ≥ 4 insert every position (best ratio). Level 1 uses the
    aggressive `deflate_fast` cap of `2` (#2726): a re-measured Silesia sweep
    (`ZipL1Sweep`) showed the older `cap = 16` claim ("below ~16 is
    counterproductive") no longer holds for the packed emit path — at chain depth
    4, `cap = 2` is +12% end-to-end vs `cap = 16` because the interior-insertion
    saving outweighs the slightly higher token count the worse ratio produces
    (the emit walk is the bound, not the cap). L2/L3 dropped to 8/32 with the
    greedy re-grid (`l1-sweep2`), paired with their new chain depths. The chain
    is a heuristic, so any cap stays correct (`lz77ChainIter_resolves` holds
    ∀ cap). -/
def insertCap (level : UInt8) : Nat :=
  if level ≤ 1 then 2
  else if level ≤ 2 then 8
  else if level ≤ 3 then 32
  else 1000000000

/-- Lazy `good_match` threshold (zlib-style): the lazy matcher skips the
    one-byte-lookahead probe once the first match is at least this long, since a
    long first match is rarely improved by deferral. Lower → more gating (faster,
    slightly worse ratio). `259 > 258` disables gating.

    Only L4 keeps the full gate (#2737 `mid-sweep`): disabling it gains ~16bp of
    Silesia geomean ratio at *any* chain depth — more ratio per cycle than
    deepening the chain. **Exception: L6 gates at 64 since the hash3-singleton
    re-grid** — with the singleton paying the ratio bill, (gate 64, ld/8)
    buys +8% weighted speed for +0.09pp, the point that strictly dominates
    miniz_oxide L6; L7 keeps the gate off and the old L6 ratio point.
    **L5 also gates at 64 since the L5 re-grid** (`gate-sweep`, see
    `chainDepth`): the winning shallow split point pairs the intermediate gate
    with its chain-24 walk — at that depth the gate's skipped lookahead probes
    are most of the lazy tier's marginal cost. -/
def goodMatch (level : UInt8) : Nat :=
  if level ≤ 4 then 8
  else if level ≤ 6 then 64
  else 259

/-- Per-level `niceLen` cutoff (libdeflate `nice_match_length`, `deflate_compress.c`):
    the chain walk stops as soon as the best match reaches this length, since a
    match this long is already good enough — burning the rest of the depth budget
    to lengthen it further rarely pays for itself. **L2/L3 disable the cutoff
    since the greedy re-grid** (`l1-sweep2`, post merged-greedy-loop +
    packed-emit landings): the libdeflate values (10/14, #2744) were costing
    ~0.5pp weighted-Silesia ratio for speed better bought by shallowing the
    chain instead — both old mid rows sat ~10% below the greedy-band mixing
    frontier. Level 1 keeps `258` (no early-out) as before — at chain depth 4
    the walk is already short, so a cutoff buys little there.

    The mid-band values were re-gridded for the #2737 remapped ladder
    (`mid-sweep --time`, Silesia): **L4 disables the cutoff** — at chain 64
    with the lazy gate on, every `niceLen` value times identically (the gate
    already skips the probes the cutoff would save) and lower cutoffs only
    cost ratio (nl30 +11bp, nl65 +3.5bp corpus-total), so the early-out is a
    pure loss there. L5–L7 sit at the measured knee `65` (nl30
    gains ~3% speed for +10bp — a poor trade; nl130/258 return ≤1bp for the
    speed given up; since the post-singleton re-grid L7 runs the old L6
    config, chain 64, so the old chain-256 `130` knee no longer applies);
    L8 (the max split tier)
    disables the cutoff — nl130 times within 1% but emits more bytes, and L8's
    cadence guard promises old-L8 ratio parity. `258` (the max match length,
    ≥ every `maxLen`) disables the cutoff: the walk then stops only on the
    full-match / fuel condition, exactly as before this knob existed. The
    cutoff never enters correctness — the chain is a heuristic re-verified at
    emission — so any value keeps the encoder contracts. -/
def niceLen (level : UInt8) : Nat :=
  if level ≤ 4 then 258
  else if level ≤ 7 then 65
  else 258

/-- Lazy lookahead probe depth (libdeflate `deflate_compress.c`): the second
    `chainWalk` at `pos+1` runs at *half* the `pos` walk's `chainDepth`, not full
    depth. Since the `goodMatch` gate is disabled at L7+ (`goodMatch = 259`), every
    matched position otherwise pays two full-depth chain walks; libdeflate probes
    its first lookahead at half depth (and its second at quarter) and still holds
    better ratios than us, so the deferral quality a half-depth probe gives up is
    slack. The probe still runs — it is shallower, not skipped — so the ratio cost
    stays in the noise while the second walk's cycles roughly halve.

    **L6 probes at depth 18 (the strict-dominance re-pair)**: the `/8` (= 8)
    depth chosen by the post-singleton re-grid dominated miniz_oxide L6 on the
    *weighted* plane but sat 0.8bp above it on the dashboard's per-file
    geomean; the fine `gate-sweep` ld-grid shows depth 18 (with the
    `goodMatch = 64` gate) is the shallowest probe whose geomean ratio clears
    miniz L6 with real margin (0.32153 vs 0.32164, deterministic) while
    keeping the speed edge — so the default level dominates on BOTH published
    metrics. L7 (the old L6 config) stays at `/2`. **L5 probes at `/4` since the L5 re-grid**
    (`gate-sweep`, see `chainDepth`): the winning (chain 24, gate 64) split
    point took its probe at 6 — deep enough to keep the deferral wins the
    gate lets through, half the cost of the `/2` default.

    Only levels ≥ 4 (the lazy `deflate_slow` tier) consult this; the greedy
    matcher (1–3) has no lookahead. Depth is a pure heuristic — the chain is
    re-verified at emission (`chainWalk_spec` holds for any fuel) — so any value
    keeps the encoder contracts. -/
def lazyDepth (level : UInt8) : Nat :=
  if level == 5 then chainDepth level / 4
  else if level == 6 then 18
  else chainDepth level / 2

/-- Enable the hash3 length-3 singleton at the split tier (levels 6–8). Our
    lazy matcher walks hash4-keyed chains only, so length-3 matches are invisible
    below L9; on the barely-compressible Silesia binaries (x-ray/sao/ooffice)
    this is our whole weighted-ratio deficit to miniz_oxide L6. The singleton
    probe (`h3Seed`, TOO_FAR-capped) restores them at −0.28pp corpus-weighted
    Silesia ratio for ≤~5% matcher speed. L1–L5 keep the probe-free loops (the
    #2742 verdict against probing the fast band stands, and the L5 re-grid
    retested the singleton at L5's shallow split points — every h3 row fell
    below the no-h3 frontier there); L9/L10 already carry their own singleton
    in the cache build. -/
def useH3Level (level : UInt8) : Bool := decide (6 ≤ level ∧ level ≤ 8)

/-- The per-level LZ77 matcher (zlib-faithful): levels 1–3 (`deflate_fast`) use the
    greedy hash-chain matcher; levels ≥ 4 (`deflate_slow`) use the one-byte-lookahead
    lazy variant, which improves ratio at equal window/chain depth. Both share the
    same `(chainDepth, insertCap, niceLen)` ladder and satisfy the same encoder
    contracts (`lzMatch_{encodable,empty,resolves}` in `DeflateBlockSplit`), so the
    choice is transparent to the roundtrip proof. The lazy tier probes its `pos+1`
    lookahead at `lazyDepth` (half-depth), a heuristic knob invisible to the proof.
    Levels 6–8 additionally enable the hash3 length-3 singleton (`useH3Level`). -/
def lzMatch (data : ByteArray) (level : UInt8) : Array LZ77Token :=
  if 4 ≤ level then lz77ChainLazyIter data (chainDepth level) 32768 (insertCap level) (goodMatch level) (niceLen level) (lazyDepth level) (useH3Level level)
  else lz77ChainIter data (chainDepth level) 32768 (insertCap level) (niceLen level)

/-- Packed-token form of `lzMatch` (Wave 3b stage A): the same per-level
    dispatch over the packed matcher twins, producing one unboxed `UInt32`
    per token instead of a boxed `LZ77Token`. The boxed view recovers
    `lzMatch` exactly (`lzMatchP_map` in `Zip/Spec/LZ77PackedCorrect.lean`);
    downstream consumers still run on `lzMatch` — stage B moves them here. -/
def lzMatchP (data : ByteArray) (level : UInt8) : Array UInt32 :=
  if 4 ≤ level then lz77ChainLazyIterPMerged data (chainDepth level) 32768 (insertCap level) (goodMatch level) (niceLen level) (lazyDepth level) (useH3Level level)
  else lz77ChainIterPMerged data (chainDepth level) 32768 (insertCap level) (niceLen level)

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
    instead of twice. Retired from the `deflateRaw` dispatch by #2737 — the
    observation-divergence split (`deflateDynamicBlocksSharedAtP`) picks
    boundaries with no sizing pass at all — but kept, with its proofs and
    conformance tests, as the arbitrated reference pipeline. -/
def deflateDynamicBlocksSharedSized (data : ByteArray) (toks : Array LZ77Token) : ByteArray :=
  if data.size == 0 then
    let f := tokenFreqs #[]
    (emitDynBlock BitWriter.empty data #[] (dynamicCodeLengths f.1 f.2).1 (dynamicCodeLengths f.1 f.2).2
      (dynamicCodeLengths_length f.1 f.2).1 (dynamicCodeLengths_length f.1 f.2).2 true).flush
  else
    let c := chooseSplitsArbitratedSized toks
    (emitSharedBlocksAtSized data toks c.1 c.2 0 BitWriter.empty).flush

/-! ## Packed observation-divergence block splitting (#2737)

The libdeflate-style divergence heuristic and the shared-window block emitter,
both walking the `packTok`-encoded `UInt32` stream directly — the packed twins
of `chooseSplitsHeuristic` and `emitSharedBlocksAt`. This is what lets the
mid-band levels (5–8) afford per-block Huffman trees at all: the per-block
frequency pass runs on `tokenFreqsP` (dense packed tables) and the emit on
`emitTokensWithCodesP`, so the split candidate never materializes boxed
`LZ77Token`s and never touches the `findTableCode` linear scans. At level 8 the
same pipeline **replaces** the `chooseSplitsArbitrated` sizing pass: libdeflate
picks boundaries with the streaming heuristic alone (no exact-bits arbitration),
and the sizing pass — two extra boxed `tokenFreqs`+`symbolBitCount` walks over
the whole token stream — was ~18% of level-8 cycles. The heuristic stays
proof-free: the emitter clamps every cut (`emitSharedBlocksAtP` mirrors
`emitSharedBlocksAt`'s clamping exactly), and the roundtrip transfers from the
boxed reference via `deflateDynamicBlocksSharedAtP_eq`
(`Zip/Spec/LZ77PackedCorrect.lean`). -/

/-- Observation class of a packed token (`splitTokenClass` over the packed
    fields, conformance-tested in `ZipTest/PackedTokens.lean`): literals (tag
    bit clear) map to 0–7 by bits 7,6,0 of the byte field; references map to 8
    (length < 9) or 9. -/
@[inline] def splitTokenClassP (w : UInt32) : Nat :=
  if w &&& ((1 : UInt32) <<< 31) = 0 then
    (((w.toUInt8 >>> 5) &&& 6) ||| (w.toUInt8 &&& 1)).toNat
  else
    splitNumLiteralClasses + (if ((w >>> 16) &&& 0x7FFF).toNat ≥ 9 then 1 else 0)

/-- Output bytes a packed token contributes (`splitTokenBytes` over the packed
    fields): 1 for a literal, the length field for a reference. -/
@[inline] def splitTokenBytesP (w : UInt32) : Nat :=
  if w &&& ((1 : UInt32) <<< 31) = 0 then 1
  else ((w >>> 16) &&& 0x7FFF).toNat

/-- The per-token core of `chooseSplitsHeuristicP`, threaded as a tail-recursive
    loop over explicit scalar state so the hot accumulators compile to register
    arithmetic instead of `Array Nat` `set!`/`getD` (#2762). The ten observation
    counters live in the `n0..n9` (recent window) and `o0..o9` (block-so-far)
    locals; `newTot`/`oldTot`/`blockBytes` are the window/block totals, and
    `remaining` is the running byte suffix `totalBytes − doneBytes` (decremented
    per token) that gates cuts against the min-block floor without a second
    pass. The full ten-counter arrays are materialized only at a divergence
    check (every `checkTokens` tokens, once the floors clear), where the shared
    boxed `splitEndBlockCheck` reads them. -/
def chooseSplitsHeuristicP.go (toks : Array UInt32)
    (minBlockBytes softMaxBlockBytes checkTokens : Nat) (i : Nat)
    (o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 oldTot : Nat)
    (n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 newTot : Nat)
    (blockBytes remaining : Nat) (cuts : Array Nat) : Array Nat :=
  if h : i < toks.size then
    let t := toks[i]
    let c := splitTokenClassP t
    let tb := splitTokenBytesP t
    let (n0, n1, n2, n3, n4, n5, n6, n7, n8, n9) :=
      match c with
      | 0 => (n0 + 1, n1, n2, n3, n4, n5, n6, n7, n8, n9)
      | 1 => (n0, n1 + 1, n2, n3, n4, n5, n6, n7, n8, n9)
      | 2 => (n0, n1, n2 + 1, n3, n4, n5, n6, n7, n8, n9)
      | 3 => (n0, n1, n2, n3 + 1, n4, n5, n6, n7, n8, n9)
      | 4 => (n0, n1, n2, n3, n4 + 1, n5, n6, n7, n8, n9)
      | 5 => (n0, n1, n2, n3, n4, n5 + 1, n6, n7, n8, n9)
      | 6 => (n0, n1, n2, n3, n4, n5, n6 + 1, n7, n8, n9)
      | 7 => (n0, n1, n2, n3, n4, n5, n6, n7 + 1, n8, n9)
      | 8 => (n0, n1, n2, n3, n4, n5, n6, n7, n8 + 1, n9)
      | _ => (n0, n1, n2, n3, n4, n5, n6, n7, n8, n9 + 1)
    let newTot := newTot + 1
    let blockBytes := blockBytes + tb
    let remaining := remaining - tb
    if blockBytes ≥ minBlockBytes && remaining ≥ minBlockBytes then
      let cut :=
        blockBytes ≥ softMaxBlockBytes ||
        (newTot ≥ checkTokens && oldTot > 0 &&
          splitEndBlockCheck #[o0, o1, o2, o3, o4, o5, o6, o7, o8, o9] oldTot
            #[n0, n1, n2, n3, n4, n5, n6, n7, n8, n9] newTot blockBytes)
      if cut then
        chooseSplitsHeuristicP.go toks minBlockBytes softMaxBlockBytes checkTokens (i + 1)
          0 0 0 0 0 0 0 0 0 0 0
          0 0 0 0 0 0 0 0 0 0 0
          0 remaining (cuts.push (i + 1))
      else if newTot ≥ checkTokens then
        chooseSplitsHeuristicP.go toks minBlockBytes softMaxBlockBytes checkTokens (i + 1)
          (o0 + n0) (o1 + n1) (o2 + n2) (o3 + n3) (o4 + n4) (o5 + n5) (o6 + n6) (o7 + n7)
          (o8 + n8) (o9 + n9) (oldTot + newTot)
          0 0 0 0 0 0 0 0 0 0 0
          blockBytes remaining cuts
      else
        chooseSplitsHeuristicP.go toks minBlockBytes softMaxBlockBytes checkTokens (i + 1)
          o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 oldTot
          n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 newTot
          blockBytes remaining cuts
    else
      chooseSplitsHeuristicP.go toks minBlockBytes softMaxBlockBytes checkTokens (i + 1)
        o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 oldTot
        n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 newTot
        blockBytes remaining cuts
  else cuts
termination_by toks.size - i
decreasing_by all_goals omega

/-- Packed twin of `chooseSplitsHeuristic`: entropy-divergence cut points
    computed directly from the packed token stream — same constants, same
    per-token floors/ceiling, same window-merge cadence, with
    `splitTokenClassP`/`splitTokenBytesP` in place of the boxed accessors.
    Heuristic-only (the emitter clamps arbitrary cuts), so it carries no proof
    obligations; `ZipTest/PackedTokens.lean` pins it to the boxed heuristic
    over the `unpackTok` view. The block floor/ceiling and check cadence are
    defaulted parameters so the `mid-sweep` tuning tool can grid them without
    touching the dispatch (which always calls with the tuned defaults).

    `totalBytes` is the whole-stream output byte count `Σ splitTokenBytesP t`.
    The boxed reference computes it with a leading pass over `toks`; the packed
    dispatch passes `data.size` instead (the token stream decodes to `data`, so
    the two agree — pinned by the `chooseSplitsHeuristic` conformance test),
    fusing that pass away (#2762). The main walk then tracks the running byte
    suffix in `remaining` (start `totalBytes`, minus each token's bytes) rather
    than a `doneBytes` prefix, and computes `splitTokenBytesP` once per token. -/
def chooseSplitsHeuristicP (toks : Array UInt32) (totalBytes : Nat)
    (minBlockBytes : Nat := splitMinBlockBytes)
    (softMaxBlockBytes : Nat := splitSoftMaxBlockBytes)
    (checkTokens : Nat := splitCheckTokens) : List Nat :=
  (chooseSplitsHeuristicP.go toks minBlockBytes softMaxBlockBytes checkTokens 0
    0 0 0 0 0 0 0 0 0 0 0
    0 0 0 0 0 0 0 0 0 0 0
    0 totalBytes #[]).toList

/-- Packed twin of `emitDynBlock`: one dynamic Huffman block from a packed
    token group onto a running writer, with `emitTokensWithCodesP` in place of
    `emitTokensWithCodes`. Equal to `emitDynBlock` over the boxed view
    (`emitDynBlockP_eq` in `Zip/Spec/LZ77PackedCorrect.lean`). -/
def emitDynBlockP (bw : BitWriter) (data : ByteArray) (ptoks : Array UInt32)
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
  have hlitT_size : (packCodeTab litCodes).size ≥ 286 := by
    rw [packCodeTab_size]; exact hlit_size
  have hdistT_size : (packCodeTab distCodes).size ≥ 30 := by
    rw [packCodeTab_size]; exact hdist_size
  let bw := if data.size == 0 then bw
            else emitTokensWithCodesPT bw ptoks (packCodeTab litCodes) (packCodeTab distCodes)
              hlitT_size hdistT_size 0
  let (code, len) := litCodes[256]'h256
  bw.writeHuffCode code len

/-- Packed twin of `emitSharedBlock`: the group's frequencies come from
    `tokenFreqsP` (dense packed tables) and the emit from `emitDynBlockP`. -/
def emitSharedBlockP (bw : BitWriter) (data : ByteArray) (group : Array UInt32)
    (isFinal : Bool) : BitWriter :=
  let f := tokenFreqsP group
  let lens := dynamicCodeLengths f.1 f.2
  emitDynBlockP bw data group lens.1 lens.2
    (dynamicCodeLengths_length f.1 f.2).1 (dynamicCodeLengths_length f.1 f.2).2 isFinal

/-- Packed twin of `emitSharedBlocksAt`: emit shared-window blocks at explicit
    cut points directly from the packed token stream. Same clamping — every cut
    is forced into `(pos, toks.size]`, so **any** cuts list yields a valid total
    partition and the boundary heuristic stays proof-free. The clamping makes
    arbitrary cuts correctness-safe, not performance-safe: a pathological list
    (non-monotone, dense) degrades to one-token blocks, each paying a full tree
    header. `deflateRaw` only ever feeds it `chooseSplitsHeuristicP`'s strictly
    increasing, byte-floored cuts. -/
def emitSharedBlocksAtP (data : ByteArray) (toks : Array UInt32) (cuts : List Nat)
    (pos : Nat) (bw : BitWriter) : BitWriter :=
  let j := min (max (cuts.headD toks.size) (pos + 1)) toks.size
  let bw := emitSharedBlockP bw data (toks.extract pos j) (decide (j ≥ toks.size))
  if j ≥ toks.size then bw
  else emitSharedBlocksAtP data toks cuts.tail j bw
termination_by toks.size - pos
decreasing_by
  rename_i h
  simp only [Nat.not_le] at h
  omega

/-- The packed observation-divergence shared-window split candidate: emit the
    packed token stream as shared-window dynamic blocks at the given cut points
    (in `deflateRaw`, the `chooseSplitsHeuristicP` boundaries). Byte-identical
    to the boxed reference
    `deflateDynamicBlocksSharedAtTokens data (toks.map unpackTok) (fun _ => cuts)`
    (`deflateDynamicBlocksSharedAtP_eq`), through which the roundtrip and
    padding theorems transfer for **any** cut list. -/
def deflateDynamicBlocksSharedAtP (data : ByteArray) (toks : Array UInt32)
    (cuts : List Nat) : ByteArray :=
  if data.size == 0 then
    let f := tokenFreqs #[]
    (emitDynBlock BitWriter.empty data #[] (dynamicCodeLengths f.1 f.2).1 (dynamicCodeLengths f.1 f.2).2
      (dynamicCodeLengths_length f.1 f.2).1 (dynamicCodeLengths_length f.1 f.2).2 true).flush
  else
    (emitSharedBlocksAtP data toks cuts 0 BitWriter.empty).flush

/-- Packed twin of `sharedPartitionSized` (Wave 5, #2552): the exact unflushed
    bit size of the shared-window partition **together with** each block's sized
    trees, so the winning candidate's emission reuses them instead of rebuilding
    `tokenFreqsP` + `dynamicCodeLengths` per block. Each group's frequencies come
    from `tokenFreqsP` (dense packed tables); component 1 is the same
    `3 + header + freq·codeLen` sum the packed emitter (`emitSharedBlocksAtP`)
    flushes as `⌈bits/8⌉`, and component 2's entries are definitionally
    `dynamicCodeLengths (tokenFreqsP group)` — exactly what `emitSharedBlockP`
    would recompute (`emitSharedBlocksAtSizedP_eq`). This is what makes the
    size-arbitrated dispatch (#2753) a net win: the per-block trees are built
    **once**, during sizing, and the emit pass reuses them. -/
def sharedPartitionSizedP (toks : Array UInt32) (cuts : List Nat) (pos : Nat) :
    Nat × List SizedTrees :=
  let j := min (max (cuts.headD toks.size) (pos + 1)) toks.size
  let f := tokenFreqsP (toks.extract pos j)
  let t := sizedTrees f.1 f.2
  let blockBits := 3 + (writeDynamicHeader BitWriter.empty t.val.1 t.val.2).bitLength
    + symbolBitCount f.1 f.2 t.val.1.toArray t.val.2.toArray
  if j ≥ toks.size then (blockBits, [t])
  else
    let rest := sharedPartitionSizedP toks cuts.tail j
    (blockBits + rest.1, t :: rest.2)
termination_by toks.size - pos
decreasing_by
  rename_i h
  simp only [Nat.not_le] at h
  omega

/-- Fused twin of `sharedPartitionSizedP` (#2772): one pass over the clamped
    partition yields the same `(bits, per-block trees)` **and** the whole-stream
    frequencies, accumulated as the EOB-corrected element-wise sum of the per-block
    `tokenFreqsP` (`mergeEOBFreqsP`) — the *same* histogram `sizedTrees` already
    consumes, so no extra frequency walk. Component 1 is proved equal to
    `sharedPartitionSizedP` (`sharedPartitionSizedFreqsP_fst`) and component 2 to
    `tokenFreqsP (toks.extract pos toks.size)` (`sharedPartitionSizedFreqsP_snd`),
    so the base candidate can reuse these frequencies instead of re-walking the
    whole stream (`tokenFreqsP` is 4.7% L6 dickens / 3.0% mozilla of compress). -/
def sharedPartitionSizedFreqsP (toks : Array UInt32) (cuts : List Nat) (pos : Nat) :
    (Nat × List SizedTrees) × (Array Nat × Array Nat) :=
  let j := min (max (cuts.headD toks.size) (pos + 1)) toks.size
  let f := tokenFreqsP (toks.extract pos j)
  let t := sizedTrees f.1 f.2
  let blockBits := 3 + (writeDynamicHeader BitWriter.empty t.val.1 t.val.2).bitLength
    + symbolBitCount f.1 f.2 t.val.1.toArray t.val.2.toArray
  if j ≥ toks.size then ((blockBits, [t]), f)
  else
    let rest := sharedPartitionSizedFreqsP toks cuts.tail j
    ((blockBits + rest.1.1, t :: rest.1.2), mergeEOBFreqsP f rest.2)
termination_by toks.size - pos
decreasing_by
  rename_i h
  simp only [Nat.not_le] at h
  omega

/-- Tree-taking twin of `emitSharedBlocksAtP`: same clamped cut points, but each
    block's `(litLens, distLens)` come from the `trees` list (in lockstep with
    `cuts`) instead of being recomputed from the group via `tokenFreqsP` +
    `dynamicCodeLengths`. Byte-identical to `emitSharedBlocksAtP` when `trees` is
    `sharedPartitionSizedP`'s output (`emitSharedBlocksAtSizedP_eq`). -/
def emitSharedBlocksAtSizedP (data : ByteArray) (toks : Array UInt32) (cuts : List Nat)
    (trees : List SizedTrees) (pos : Nat) (bw : BitWriter) : BitWriter :=
  let j := min (max (cuts.headD toks.size) (pos + 1)) toks.size
  let t := trees.headD emptySizedTrees
  let bw := emitDynBlockP bw data (toks.extract pos j) t.val.1 t.val.2
    t.property.1 t.property.2 (decide (j ≥ toks.size))
  if j ≥ toks.size then bw
  else emitSharedBlocksAtSizedP data toks cuts.tail trees.tail j bw
termination_by toks.size - pos
decreasing_by
  rename_i h
  simp only [Nat.not_le] at h
  omega

/-- The packed sized-tree split candidate: the flushed byte size of
    `deflateDynamicBlocksSharedAtP data toks cuts` **paired with** a thunk that
    emits it, reusing the per-block trees built during sizing (no second
    frequency/Huffman pass). The emit thunk is byte-identical to the reference
    `deflateDynamicBlocksSharedAtP` (`deflateDynamicBlocksSharedAtSizedP_emit`),
    so its roundtrip transfers for **any** cut list; component 1 equals that
    output's `.size` (`SizeHelpers` conformance). `deflateRaw` sizes every split
    candidate this way and forces only the winner's thunk. -/
def deflateDynamicBlocksSharedAtSizedP (data : ByteArray) (toks : Array UInt32)
    (cuts : List Nat) : Nat × (Unit → ByteArray) :=
  if data.size == 0 then
    let out := deflateDynamicBlocksSharedAtP data toks cuts
    (out.size, fun _ => out)
  else
    let sp := sharedPartitionSizedP toks cuts 0
    ((sp.1 + 7) / 8,
      fun _ => (emitSharedBlocksAtSizedP data toks cuts sp.2 0 BitWriter.empty).flush)

/-- The obs-split candidate prep **paired with** the whole-stream frequencies,
    both from one fused sizing pass (`sharedPartitionSizedFreqsP`, #2772).
    Component 1 is proved equal to `deflateDynamicBlocksSharedAtSizedP`
    (`deflateObsSplitSizedFreqsP_fst`), so the split candidate's roundtrip and
    byte-size conformance transfer unchanged; component 2 is `tokenFreqsP toks`
    (`deflateObsSplitSizedFreqsP_snd`), the whole-stream histogram the base
    candidate needs — derived here by folding the per-block frequencies the
    sizing pass already built, instead of a second whole-stream `tokenFreqsP`
    walk. `deflateRaw` (levels 5–8, cuts non-empty) forces this once and feeds
    component 2 to `deflateRawBasePPrepF`. -/
def deflateObsSplitSizedFreqsP (data : ByteArray) (toks : Array UInt32)
    (cuts : List Nat) : (Nat × (Unit → ByteArray)) × (Array Nat × Array Nat) :=
  if data.size == 0 then
    let out := deflateDynamicBlocksSharedAtP data toks cuts
    ((out.size, fun _ => out), tokenFreqsP toks)
  else
    let sp := sharedPartitionSizedFreqsP toks cuts 0
    (((sp.1.1 + 7) / 8,
      fun _ => (emitSharedBlocksAtSizedP data toks cuts sp.1.2 0 BitWriter.empty).flush),
     sp.2)

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

/-- `deflateRawBaseP` with the whole-stream frequencies supplied as a parameter
    instead of recomputed via `tokenFreqsP ptokens` — the emit twin of
    `deflateRawBasePPrepF`. Used by `deflateRawBaseF` to consume the frequencies
    the fused matcher already produced. At `f = tokenFreqsP ptokens` this is
    definitionally `deflateRawBaseP` (`deflateRawBasePF_tokenFreqsP`). -/
def deflateRawBasePF (data : ByteArray) (ptokens : Array UInt32)
    (f : Array Nat × Array Nat) : ByteArray :=
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

/-- `deflateRawBasePF` at the whole-stream frequencies is `deflateRawBaseP`. -/
theorem deflateRawBasePF_tokenFreqsP (data : ByteArray) (ptokens : Array UInt32) :
    deflateRawBasePF data ptokens (tokenFreqsP ptokens) = deflateRawBaseP data ptokens :=
  rfl

/-- The base candidate *sized and prepared* from one shared token pass: the
    winner's flushed byte size (the same stored / fixed / dynamic comparison
    `deflateRawBaseP` makes internally) **paired with** a thunk that emits it. The
    frequencies, code lengths, and dynamic-tree plan are computed once and shared
    between the size and the emit — so when the base wins, forcing the thunk pays
    no second sizing pass. The thunk is definitionally `deflateRawBaseP data
    ptokens` (`deflateRawBasePPrep_emit`) and component 1 equals its `.size`
    (`SizeHelpers` conformance), so byte-identity to the emit-then-`pickSmaller`
    dispatch is preserved. -/
def deflateRawBasePPrep (data : ByteArray) (ptokens : Array UInt32) : Nat × (Unit → ByteArray) :=
  let f := tokenFreqsP ptokens
  let lens := dynamicCodeLengths f.1 f.2
  let plan := dynHeaderCodes lens.1 lens.2
  have hcl : plan.clCodes.size ≥ 19 :=
    Nat.le_of_eq (dynHeaderCodes_clCodes_size lens.1 lens.2).symm
  let fixedBytes := fixedBlockBytes f.1 f.2
  let dynBytes := dynBlockBytesWith f.1 f.2 lens.1 lens.2 plan hcl
  let storedBytes := storedBlockBytes data
  ((if storedBytes < (if fixedBytes < dynBytes then fixedBytes else dynBytes) then storedBytes
    else if fixedBytes < dynBytes then fixedBytes else dynBytes),
   fun _ =>
    if storedBytes < (if fixedBytes < dynBytes then fixedBytes else dynBytes) then deflateStoredPure data
    else if fixedBytes < dynBytes then deflateFixedBlockP data ptokens
    else deflateDynamicBlockCorePWith data ptokens lens.1 lens.2 plan hcl
      (dynamicCodeLengths_length f.1 f.2).1 (dynamicCodeLengths_length f.1 f.2).2)

/-- The prep's emit thunk is exactly `deflateRawBaseP` (same shared plan). -/
theorem deflateRawBasePPrep_emit (data : ByteArray) (ptokens : Array UInt32) :
    (deflateRawBasePPrep data ptokens).2 () = deflateRawBaseP data ptokens := rfl

/-- `deflateRawBasePPrep` with the whole-stream frequencies supplied as a
    parameter instead of recomputed via `tokenFreqsP ptokens` (#2772). When the
    levels-5–8 split has cuts, `deflateRaw` passes the frequencies the split-sizing
    pass already summed (`deflateObsSplitSizedFreqsP`'s component 2, provably
    `tokenFreqsP ptokens`), so the base candidate skips the second whole-stream
    frequency walk. At `f = tokenFreqsP ptokens` this is definitionally
    `deflateRawBasePPrep` (`deflateRawBasePPrepF_tokenFreqsP`), keeping the emit
    theorem clean. Only the frequency-derived sizing/tree work uses `f`; the emit
    branches consume `ptokens` directly, exactly as `deflateRawBasePPrep`. -/
def deflateRawBasePPrepF (data : ByteArray) (ptokens : Array UInt32)
    (f : Array Nat × Array Nat) : Nat × (Unit → ByteArray) :=
  let lens := dynamicCodeLengths f.1 f.2
  let plan := dynHeaderCodes lens.1 lens.2
  have hcl : plan.clCodes.size ≥ 19 :=
    Nat.le_of_eq (dynHeaderCodes_clCodes_size lens.1 lens.2).symm
  let fixedBytes := fixedBlockBytes f.1 f.2
  let dynBytes := dynBlockBytesWith f.1 f.2 lens.1 lens.2 plan hcl
  let storedBytes := storedBlockBytes data
  ((if storedBytes < (if fixedBytes < dynBytes then fixedBytes else dynBytes) then storedBytes
    else if fixedBytes < dynBytes then fixedBytes else dynBytes),
   fun _ =>
    if storedBytes < (if fixedBytes < dynBytes then fixedBytes else dynBytes) then deflateStoredPure data
    else if fixedBytes < dynBytes then deflateFixedBlockP data ptokens
    else deflateDynamicBlockCorePWith data ptokens lens.1 lens.2 plan hcl
      (dynamicCodeLengths_length f.1 f.2).1 (dynamicCodeLengths_length f.1 f.2).2)

/-- `deflateRawBasePPrepF` at the whole-stream frequencies is `deflateRawBasePPrep`. -/
theorem deflateRawBasePPrepF_tokenFreqsP (data : ByteArray) (ptokens : Array UInt32) :
    deflateRawBasePPrepF data ptokens (tokenFreqsP ptokens) = deflateRawBasePPrep data ptokens :=
  rfl

/-- `deflateRawBaseP` over this level's *packed* `lzMatchP` stream
    (definitional wrapper, `deflateRawBaseP_def`). Equal to the boxed
    `deflateRawBaseTokens data (lzMatch data level)` — that equation is
    `deflateRawBase_def`, proven in `Zip/Spec/LZ77PackedCorrect.lean` via
    `tokenFreqsP_eq` + `lzMatchP_map`. -/
def deflateRawBase (data : ByteArray) (level : UInt8) : ByteArray :=
  deflateRawBaseP data (lzMatchP data level)

theorem deflateRawBaseP_def (data : ByteArray) (level : UInt8) :
    deflateRawBaseP data (lzMatchP data level) = deflateRawBase data level := rfl

/-- The greedy-tier (levels 1–3) base candidate computed from **one fused pass**:
    the fused matcher (`lz77ChainIterPMergedF`) produces the packed tokens and
    their `tokenFreqsP` histograms together, and the base sizing/emit consumes
    those frequencies directly (`deflateRawBasePF`) instead of re-walking the
    token array with a second `tokenFreqsP`. Byte-identical to `deflateRawBase`
    on the greedy tier (`deflateRawBaseF_eq`). -/
def deflateRawBaseF (data : ByteArray) (level : UInt8) : ByteArray :=
  let (ptokens, litF, distF) :=
    lz77ChainIterPMergedF data (chainDepth level) 32768 (insertCap level) (niceLen level)
  deflateRawBasePF data ptokens (litF.val, distF.val)

/-- On the greedy tier (`level ≤ 3`, i.e. `¬ 4 ≤ level`) the fused base candidate
    is byte-identical to `deflateRawBase`: the fused matcher returns exactly the
    plain matcher's tokens and `tokenFreqsP` (`lz77ChainIterPMergedF_eq`), and at
    those frequencies `deflateRawBasePF` is `deflateRawBaseP`. -/
theorem deflateRawBaseF_eq (data : ByteArray) (level : UInt8) (h : ¬ (4 ≤ level)) :
    deflateRawBaseF data level = deflateRawBase data level := by
  have hlz : lzMatchP data level =
      lz77ChainIterPMerged data (chainDepth level) 32768 (insertCap level) (niceLen level) := by
    unfold lzMatchP; rw [if_neg h]
  unfold deflateRawBaseF deflateRawBase
  rw [hlz, lz77ChainIterPMergedF_eq]
  exact deflateRawBasePF_tokenFreqsP data _

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
    projected ~2.1 GB peak, acceptable for the max-effort tiers (levels 9–10);
    truly huge inputs still fall back to the split path. A pure dispatch knob —
    `pickSmaller` composes either way. (The L9-fast candidate at level 9 has a
    lower peak — shallower cache, single round — so the gate is conservative
    there, but a single gate for both optimal tiers keeps the dispatch simple.) -/
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

/-- Cross-block split over the **L9-fast** approximate-optimal token stream
    (`lz77OptimalFastIter`, #2638): identical to `deflateDynamicBlocksOptimal`
    but the cheaper single-round, bounds-free, shallow-cache parser. The tokens
    satisfy the same encoder contracts, so the roundtrip proof is the exact
    twin (`decode_deflateDynamicBlocksOptimalFast` etc.). Deployed at level 9;
    the exact crown moves to level 10. -/
def deflateDynamicBlocksOptimalFast (data : ByteArray) (tokChunk : Nat) : ByteArray :=
  if data.size == 0 then
    let f := tokenFreqs #[]
    (emitDynBlock BitWriter.empty data #[] (dynamicCodeLengths f.1 f.2).1 (dynamicCodeLengths f.1 f.2).2
      (dynamicCodeLengths_length f.1 f.2).1 (dynamicCodeLengths_length f.1 f.2).2 true).flush
  else
    (emitSharedBlocks data (lz77OptimalFastIter data) tokChunk 0 BitWriter.empty).flush

/-- Windowed twin of `deflateDynamicBlocksOptimal` (#2787): identical block
    stream, but the exact-DP tokens come from `lz77OptimalWindowedIter`, whose
    live choice storage is capped to one region — so the exact crown runs in
    bounded memory past the `optimalMaxSize` gate. -/
def deflateDynamicBlocksOptimalWindowed (data : ByteArray) (tokChunk : Nat) : ByteArray :=
  if data.size == 0 then
    let f := tokenFreqs #[]
    (emitDynBlock BitWriter.empty data #[] (dynamicCodeLengths f.1 f.2).1 (dynamicCodeLengths f.1 f.2).2
      (dynamicCodeLengths_length f.1 f.2).1 (dynamicCodeLengths_length f.1 f.2).2 true).flush
  else
    (emitSharedBlocks data (lz77OptimalWindowedIter data) tokChunk 0 BitWriter.empty).flush

/-- Windowed twin of `deflateDynamicBlocksOptimalFast` (#2787): the region-capped
    L9-fast parse (`lz77OptimalWindowedFastIter`). -/
def deflateDynamicBlocksOptimalWindowedFast (data : ByteArray) (tokChunk : Nat) : ByteArray :=
  if data.size == 0 then
    let f := tokenFreqs #[]
    (emitDynBlock BitWriter.empty data #[] (dynamicCodeLengths f.1 f.2).1 (dynamicCodeLengths f.1 f.2).2
      (dynamicCodeLengths_length f.1 f.2).1 (dynamicCodeLengths_length f.1 f.2).2 true).flush
  else
    (emitSharedBlocks data (lz77OptimalWindowedFastIter data) tokChunk 0 BitWriter.empty).flush

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

/-- Unified raw DEFLATE compression dispatch. The native level range is **0–10**
    (wider than zlib's 0–9). Since #2638 the top of the ladder is:

      * **level 9** — the **L9-fast** approximate-optimal parse (near-crown ratio,
        ~2× faster); this is a change from the old level-9 = exact crown;
      * **level ≥ 10** — the exact backward-DP **crown** (the max-ratio ceiling,
        the former level-9 output); 11+ alias level 10.

    So callers pinning `level = 9` for absolute best ratio should now pass 10.
    (The zlib/FFI bindings are a separate 0–9 path and are unchanged.)

    Level 0 = stored; levels 1–5 run the single-block cost-model dispatch
    (`deflateRawBase`); levels 5–8 (#2737, L5 since the L5 re-grid) additionally try the cross-block
    (shared-window) split candidate — one whole-file match pass, token stream
    partitioned per block, references cross block boundaries — with the
    partition chosen by the packed observation-divergence heuristic
    (`chooseSplitsHeuristicP`, libdeflate's streaming boundary check): each
    block gets its own frequency-fit Huffman trees, recovering most of the
    ratio a single whole-file tree leaves on large or heterogeneous inputs
    (zlib refits trees every ~16K symbols; the whole-file tree was why the
    mid-band was dominated). When the heuristic proposes no cuts (inputs
    below ~2·`splitMinBlockBytes` output bytes, since both sides of a cut
    must clear the floor) the split candidate would be a single dynamic block
    the base already sizes, so the dispatch skips it and small inputs pay
    nothing.

    The mid-band ladder (L4–L8) is the `mid-sweep`-chosen union of the old
    single-block frontier and the split frontier, so neither trades territory
    for the other (Silesia geomean, pinned interleaved timing):

      * **L4** — single-block, chain 64, lazy gate on: 38.8 MB/s @ 0.3330
        (the old L5 point; dominates the old L4).
      * **L5** — single-block, chain 128, gate off: 29.7 @ 0.3304 (dominates
        the old L7 = single-block chain 256: gate-off buys more ratio per
        cycle than chain depth).
      * **L6** — split, chain 64, gate off: 20.1 @ 0.3245. (Since the
        post-singleton re-grid: gate 64, probe /8 — 0.3205 @ ~36.5 weighted.)
      * **L7** — split, chain 256, gate off: 17.1 @ 0.3232. (Since the
        post-singleton re-grid: the old L6 config — 0.3196 @ ~33.7 weighted.)
      * **L8** — split + emitted fixed-cadence candidate, chain 512: 11.4 @
        0.3228 — the old L8's exact geomean ratio, ~20% faster.

    Every old L4–L8 point is dominated by (or within 1% of) the new curve's
    mixing frontier, and the split points sit far outside the old one.

    At level 8 this **replaces** the arbitrated split
    (`chooseSplitsArbitrated` + `deflateDynamicBlocksSharedSized`, retired
    from the dispatch by #2737 but kept as the proven reference): the
    exact-bits arbitration guarded the heuristic against sizing worse than
    the fixed `sharedTokChunk` cadence, but paid two extra boxed whole-stream
    sizing walks (`findTableCode` linear scans + boxed `tokenFreqs`, ~18% of
    level-8 cycles) for it. Instead, level 8 *emits* the fixed-cadence
    partition as a third `pickSmaller` candidate: the min over emitted
    candidates decides by the same quantity the sizing pass computed
    (⌈bits/8⌉), so level 8 is never worse than the retired arbitration on
    any input, and one packed emit pass is far cheaper than the two boxed
    sizing walks it replaces.

    At levels 9 and 10 (and within the `optimalMaxSize` memory gate) the dispatch
    switches to a cost-model DP parse (grouped into blocks on the fixed
    `sharedTokChunk` cadence, emitted as `pickSmaller(base, optimal)`), choosing
    the globally cheapest token sequence under an estimated bit cost instead of
    the locally longest match. **Level 10** runs the exact backward-DP crown
    (`deflateDynamicBlocksOptimal`) — the max-ratio ceiling. **Level 9** runs the
    cheaper **L9-fast** approximate-optimal parse (`deflateDynamicBlocksOptimalFast`,
    #2638): single round, no length-code boundary scan, shallower cache — near the
    crown's ratio at ~2× its speed, measured ~20% outside the L8↔L9 mixing frontier
    on Silesia (a genuine new Pareto point; L10 ≤ L9 < L8 in output size, L9 > L8 in
    speed). On the
    Canterbury (11) and Silesia (12) corpora this fixed-cadence optimal candidate is
    measured strictly smaller than base, the self-contained split, *and* the
    arbitrated shared-window split on every file — including the binary
    `kennedy.xls`, where the self-contained split is the best of the three
    non-optimal candidates yet still loses to optimal — so `min(base, optimal) ==
    min(base, SC, shared, optimal)` byte-for-byte across both corpora (#2640). On that measured evidence
    the SC and shared candidates are dropped at L9: each costs a full independent
    match/split pass (~24% of L9 wall-clock together) for output `pickSmaller`
    always discarded. This is a measured speed/ratio tradeoff over those corpora,
    **not** a proven dominance invariant: the optimal parse minimizes an estimated
    per-token cost, not the final DEFLATE size across block partitions, so a
    pathological input whose statistics shift badly against the 8192-token cadence
    could in principle let an arbitrated split win. `base` stays as a near-free
    safety floor (it reuses the already-computed `ptokens`), so the emitted
    `pickSmaller(base, optimal)` is never worse than the lazy single-block baseline
    on any input — the only residual risk is forfeiting a split-only win, which the
    corpus gate found nowhere. The split candidates remain at level 8, where optimal
    is not computed.

    The base-vs-split candidates are compared against the whole base via
    `pickSmaller`, *not* nested inside the dynamic branch: on large heterogeneous
    inputs a single dynamic tree loses to fixed Huffman, so a base-internal gate
    would never reach the split even though it wins by 15–19%. `pickSmaller`
    guarantees we never regress below the base. All branches are
    roundtrip-verified.

    The split tier starts at level 5 (the L5 re-grid; previously level ≥ 6 per
    #2737, before that ≥ 8, and before that ≥ 7 — see #2698 for that history):
    with the boundaries chosen by the cheap streaming heuristic and the whole
    split pipeline on packed tokens, the candidates are **sized with their
    per-block trees captured** (`deflateRawBasePPrep` /
    `deflateDynamicBlocksSharedAtSizedP`) and only the winner is emitted
    (#2753), reusing the trees the sizing pass already built — so exactly one
    emit pass runs instead of two (three at L8). Level 4 stays single-block on
    purpose — it carries the old mid-band's high-speed point (even a size-only
    split pass would push it off that territory). L5 joined the split tier in
    the re-grid: post-#2824/#2825/#2830 the old single-block L5 sat ~14%
    inside the L4↔L6 mixing line, and a shallow split point (chain 24, gate
    64, probe /4, no singleton) matches its speed at −0.53pp weighted-Silesia
    ratio — the split's per-block trees buy more than the deep chain did.
    Levels 1–3 (`deflate_fast`, emit-bound) stay single-block greedy.

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
  else if 5 ≤ level then
    -- One *packed* matcher pass shared by the base and shared-split candidates
    -- (the matcher is 83–84% of each candidate's cost — Wave-0 profile, D-2).
    -- Both candidates consume the packed words end-to-end (freqs *and* emit):
    -- no branch materializes boxed tokens.
    --
    -- (#2782 postscript: a cheap-knobs floor matcher at L9/L10 was tried and
    -- reverted — speed-neutral on Silesia, but the floor genuinely WINS on
    -- ptt5-class Canterbury bitmaps at L9, so weakening it changes real
    -- output. The floor's cost was never the matcher; it was the full base
    -- EMIT, now a sized prep below.)
    let ptokens := lzMatchP data level
    if level == 9 then
      -- Level 9 (#2638): the cheaper **L9-fast** approximate-optimal parse — near
      -- the crown's ratio at ~2× its speed, measured ~20% outside the L8↔L9
      -- mixing frontier on Silesia (a genuine new Pareto point). As with the
      -- exact candidate below, the split candidates are dropped on measured
      -- evidence; keep `base` (reuses `ptokens`, ~free) as the safety floor and
      -- emit `pickSmaller(base, fast-optimal)`. Above the `optimalMaxSize` memory
      -- gate the same parse runs *windowed* (#2787): region-capped choice storage
      -- gives byte-identical tokens in bounded memory, so the crown survives on
      -- streams larger than 64 MiB instead of collapsing to the split ratio.
      -- #2782 follow-up: size the floor (`deflateRawBasePPrep`, the #2753
      -- tree-capturing prep) instead of emitting it — the optimal candidate is
      -- strictly smaller on every corpus file (#2640), so the emit-both
      -- `pickSmaller` paid a full discarded freq+tree+BitWriter pass. Same
      -- winner, same bytes (prep size = flushed size, the #2753 invariant).
      let opt := if data.size ≤ optimalMaxSize then
        deflateDynamicBlocksOptimalFast data sharedTokChunk
      else
        deflateDynamicBlocksOptimalWindowedFast data sharedTokChunk
      let bp := deflateRawBasePPrep data ptokens
      emitSmallerBy bp.1 bp.2 opt.size (fun _ => opt)
    else if 10 ≤ level then
      -- Level ≥ 10: the exact backward-DP crown (the former level-9 behaviour,
      -- #2640) — the max-ratio ceiling, kept reachable per the #2638 directive.
      -- The fixed-cadence optimal candidate measured strictly smallest on every
      -- Canterbury and Silesia file, so the split candidates are dropped here;
      -- `pickSmaller(base, optimal)` is never worse than the lazy baseline. As at
      -- level 9, above the memory gate the exact parse runs windowed (#2787).
      -- Sized floor here too — see the level-9 arm.
      let opt := if data.size ≤ optimalMaxSize then
        deflateDynamicBlocksOptimal data sharedTokChunk
      else
        deflateDynamicBlocksOptimalWindowed data sharedTokChunk
      let bp := deflateRawBasePPrep data ptokens
      emitSmallerBy bp.1 bp.2 opt.size (fun _ => opt)
    else
      -- Levels 5–8: base vs cross-block shared-window split at the
      -- observation-divergence boundaries (#2737),
      -- **size-arbitrated** (#2753). Both candidates are *prepared* — sized to
      -- their flushed byte count with per-block trees captured
      -- (`deflateRawBasePPrep` for the base, `deflateDynamicBlocksSharedAtSizedP`
      -- for the cut list) — and only the winner is emitted, reusing the trees the
      -- sizing pass already built, instead of emitting both and discarding the
      -- larger via `pickSmaller`. The winner and its bytes are identical to the
      -- retired emit-both dispatch. The tree capture is what makes this a net
      -- win: sizing a dynamic block otherwise costs a full frequency + Huffman
      -- pass, so without reuse "size both + emit winner" would not beat "emit
      -- both" (measured — Silesia L6-L7 +5-12% with reuse). No cuts ⇒ the split
      -- would be a single dynamic block the base already sizes, so skip it
      -- entirely (every input under ~2·splitMinBlockBytes takes this path).
      --
      -- When there are cuts, the split-sizing pass already computes `tokenFreqsP`
      -- per block; `deflateObsSplitSizedFreqsP` folds those into the whole-stream
      -- frequencies (EOB-corrected, `tokenFreqsP_append`) and the base candidate
      -- reuses them via `deflateRawBasePPrepF` — replacing the base's second
      -- whole-stream `tokenFreqsP` walk with a cheap ~316-entry summation (#2772).
      let cuts := chooseSplitsHeuristicP ptokens data.size
      -- `withObs`: the base, or the size-arbitrated smaller of base and the
      -- obs-divergence split — selected *eagerly* (the winning prep pair, tie →
      -- the split, matching `pickSmaller`), so the loser's captured per-block
      -- trees are dropped now. The winner's emit thunk stays unforced until then.
      let withObs : Nat × (Unit → ByteArray) :=
        if cuts.isEmpty then deflateRawBasePPrep data ptokens
        else
          let obsFreqs := deflateObsSplitSizedFreqsP data ptokens cuts
          let basePrep := deflateRawBasePPrepF data ptokens obsFreqs.2
          if basePrep.1 < obsFreqs.1.1 then basePrep else obsFreqs.1
      withObs.2 ()
  else if 4 ≤ level then deflateRawBase data level
  else
    -- Greedy tier (levels 1–3): fuse the whole-stream `tokenFreqsP` walk into the
    -- matcher pass. `deflateRawBaseF` produces the tokens and their frequencies in
    -- one pass and sizes/emits the base candidate from them, byte-identical to
    -- `deflateRawBase data level` (`deflateRawBaseF_eq`) — it removes the separate
    -- re-read of the (possibly cache-spilling) token array (#freq-fusion).
    deflateRawBaseF data level

end Zip.Native.Deflate
