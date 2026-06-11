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

-- The size helpers are opaque cost models: the dispatch only ever compares them.
-- Marking them irreducible keeps the elaborator from unfolding the 286-element
-- `symbolBitCount` fold while `split`ting the selection `if` (which would exceed
-- `maxRecDepth`); the kernel and compiled code still evaluate them, so `decide`
-- and the `SizeHelpers` conformance tests are unaffected.
attribute [irreducible] symbolBitCount fixedBlockBytes dynBlockBytes

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

/-- The per-level LZ77 matcher (zlib-faithful): levels 1–3 (`deflate_fast`) use the
    greedy hash-chain matcher; levels ≥ 4 (`deflate_slow`) use the one-byte-lookahead
    lazy variant, which improves ratio at equal window/chain depth. Both share the
    same `(chainDepth, insertCap)` ladder and satisfy the same encoder contracts
    (`lzMatch_{encodable,empty,resolves}` in `DeflateBlockSplit`), so the choice is
    transparent to the roundtrip proof. -/
def lzMatch (data : ByteArray) (level : UInt8) : Array LZ77Token :=
  if 4 ≤ level then lz77ChainLazyIter data (chainDepth level) 32768 (insertCap level)
  else lz77ChainIter data (chainDepth level) 32768 (insertCap level)

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

/-- `deflateRawBaseTokens` over this level's `lzMatch` stream (definitional
    wrapper; see `deflateDynamicBlocksSharedAt`). -/
def deflateRawBase (data : ByteArray) (level : UInt8) : ByteArray :=
  deflateRawBaseTokens data (lzMatch data level)

theorem deflateRawBase_def (data : ByteArray) (level : UInt8) :
    deflateRawBaseTokens data (lzMatch data level) = deflateRawBase data level := rfl

theorem deflateDynamicBlocksSharedAt_def (data : ByteArray)
    (choose : Array LZ77Token → List Nat) (level : UInt8) :
    deflateDynamicBlocksSharedAtTokens data (lzMatch data level) choose =
      deflateDynamicBlocksSharedAt data choose level := rfl

/-! ## Near-optimal candidate (level 9) -/

/-- Input-size gate for the near-optimal candidate: the DP keeps roughly
    16 bytes of transient state per input byte (global choice arrays plus the
    per-region candidate cache), so very large inputs stay on the plain
    level-9 path. A pure dispatch knob — `pickSmaller` composes either way —
    to be raised once peak memory is measured on large corpora. -/
def optimalMaxSize : Nat := 16777216

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

/-- Unified raw DEFLATE compression dispatch. Level 0 = stored; level ≥ 1 runs the
    single-block cost-model dispatch (`deflateRawBase`). At the max-compression
    tiers (level ≥ 7) two block-split streams are also tried, and the smallest of
    all candidates is emitted:
      * self-contained split — per-chunk Huffman trees, fresh window per chunk
        (wins on locally-varying statistics, e.g. structured binary);
      * cross-block (shared-window) split — one whole-file match pass, token stream
        partitioned per block, references cross block boundaries (wins on large
        text, where the self-contained split loses cross-chunk matches). The
        partition comes from the entropy-divergence heuristic arbitrated in
        exact bits against the fixed `sharedTokChunk` cadence
        (`chooseSplitsArbitrated`), so it cuts where the symbol statistics
        shift and never sizes worse than the fixed cadence.
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
    roundtrip-verified. -/
def deflateRaw (data : ByteArray) (level : UInt8 := 6) : ByteArray :=
  if level == 0 then deflateStoredPure data
  else if 7 ≤ level then
    -- One matcher pass shared by the base and shared-split candidates (the
    -- matcher is 83–84% of each candidate's cost — Wave-0 profile, D-2).
    let tokens := lzMatch data level
    if 9 ≤ level ∧ data.size ≤ optimalMaxSize then
      pickSmaller
        (pickSmaller (deflateRawBaseTokens data tokens)
          (pickSmaller (deflateDynamicBlocksSC data splitChunkSize level)
            (deflateDynamicBlocksSharedAtTokens data tokens chooseSplitsArbitrated)))
        (deflateDynamicBlocksOptimal data sharedTokChunk)
    else
      -- The self-contained split is demoted to level 9: it wins on exactly
      -- one corpus file while paying a full per-chunk match pass.
      pickSmaller (deflateRawBaseTokens data tokens)
        (deflateDynamicBlocksSharedAtTokens data tokens chooseSplitsArbitrated)
  else deflateRawBase data level

end Zip.Native.Deflate
