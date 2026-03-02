---
name: lean-zstd-patterns
description: Use when implementing or proving properties of Zstd (RFC 8878) decompression in Lean 4 — FSE table construction, backward bitstreams, sequence execution, Huffman tree descriptors, or byte position tracking across nested encodings.
allowed-tools: Read, Edit, Write, Bash, Glob, Grep
---

# Zstd Implementation Patterns for lean-zip

This skill covers patterns specific to the Zstd (RFC 8878) native
implementation in `Zip/Native/`. DEFLATE patterns are covered by other
skills; this skill addresses the unique challenges of Zstd's encoding.

## Key Files

| File | What it contains |
|------|-----------------|
| `Zip/Native/ZstdFrame.lean` | Frame/block parsing, literals, sequences, Huffman descriptors |
| `Zip/Native/Fse.lean` | FSE distribution decoding, table construction, backward bitstream |
| `Zip/Native/XxHash.lean` | XXH64 checksum (4-accumulator, 32-byte stripes) |
| `Zip/Native/BitReader.lean` | Forward (LSB-first) bitstream — shared with DEFLATE |

## Pattern 1: Backward Bitstream (MSB-first)

Zstd FSE bitstreams read **backward** from the end of the compressed
data, MSB-first per byte. This is the opposite of DEFLATE's forward
LSB-first reader.

**Structure:**
```lean
structure BackwardBitReader where
  data : ByteArray
  bytePos : Nat         -- decreases toward startPos
  bitsRemaining : Nat   -- 1-8 within current byte
  currentByte : UInt8
```

**Initialization** requires finding the sentinel bit — the highest set
bit in the last byte marks the start of the bitstream:
```lean
def init (data : ByteArray) (startPos endPos : Nat) :
    Except String BackwardBitReader := do
  let lastByte := data[endPos - 1]!
  match highBitPos lastByte with
  | none => throw "last byte is 0 (no sentinel bit)"
  | some sentinelPos => ...  -- mask below sentinel, set bitsRemaining
```

**Reading** extracts bits MSB-first and decrements `bytePos` when a
byte is exhausted:
```lean
let bitPos := br.bitsRemaining - 1
let bit := (br.currentByte >>> bitPos.toUInt8) &&& 1
let acc' := (acc <<< 1) ||| bit.toUInt32  -- MSB accumulation
```

**Key differences from forward reader:**

| Property | Forward (DEFLATE) | Backward (Zstd FSE) |
|----------|-------------------|---------------------|
| Direction | Low byte → high byte | High byte → low byte |
| Bit order | LSB-first | MSB-first |
| Accumulation | `acc \|\|\| (bit <<< shift)` | `(acc <<< 1) \|\|\| bit` |
| Initialization | Position 0, offset 0 | Sentinel bit in last byte |
| Exhaustion | Error on overrun | Error on `bitsRemaining == 0` |

**When proving backward bitstream properties:**
- The decreasing `bytePos` is the natural termination measure
- Sentinel bit detection is a key correctness property to verify
- Position tracking invariant: `bytePos * 8 + bitsRemaining` strictly
  decreases on each bit read

## Pattern 2: FSE Table Construction

FSE (Finite State Entropy) is a two-phase process: decode probability
distribution, then build the lookup table.

### Distribution Decoding

Read normalized probabilities with variable-width encoding:
```lean
def decodeFseDistribution (br : BitReader) (maxSymbols : Nat)
    (maxAccLog : Nat := 11) :
    Except String (Array Int32 × Nat × BitReader)
```

Key invariant: probabilities must sum to exactly `1 <<< accuracyLog`.
The `remaining` counter tracks this and must reach 0.

Special cases:
- **Probability 0**: triggers 2-bit repeat count for consecutive zero-probability symbols
- **Probability -1**: "less than 1" symbol — gets single cell placed at table end
- **Repeat count == 3**: means "keep reading more repeat counts"

### Table Building (3-pass)

```
Pass 1: Place -1 probability symbols at the END of the table
Pass 2: Distribute remaining symbols using position stepping:
        step = (tableSize >> 1) + (tableSize >> 3) + 3
        position = (position + step) & tableMask
Pass 3: Compute numBits and newState for each cell
```

The stepping formula produces a pseudo-random symbol distribution. The
`numBits`/`newState` computation uses a threshold to distinguish
"double-width" cells from "single-width" cells:
```lean
let doubleCells := (1 <<< (highBit + 1)) - count
if stateIdx < doubleCells then
  (accuracyLog - highBit, (stateIdx + doubleCells) <<< (accuracyLog - highBit))
else
  (accuracyLog - highBit - 1, (stateIdx - doubleCells) <<< (accuracyLog - highBit - 1))
```

**When proving FSE table properties:**
- The stepping guarantees all cells are visited exactly once (prove via
  GCD argument: step and tableSize are coprime)
- Distribution sum invariant: all positive probs + count of -1 probs = tableSize
- Each symbol's cell count equals its positive probability

## Pattern 3: Mixed Forward/Backward Reading

FSE-compressed Huffman weights use BOTH readers on the same byte range:

```
[header byte] [FSE distribution (forward)] [FSE symbols (backward)]
              ^-- BitReader (LSB)           ^-- BackwardBitReader (MSB)
              reads from rangeStart         reads from rangeEnd backward
```

The forward reader decodes the FSE probability distribution, then is
aligned to a byte boundary. The backward reader starts at `rangeEnd`
and reads symbols using the constructed FSE table.

**Position hand-off:**
```lean
let br : BitReader := { data, pos := rangeStart, bitOff := 0 }
let (probs, accuracyLog, br) ← decodeFseDistribution br 256 6
let brAligned := br.alignToByte
let fseDistEnd := brAligned.pos
let bbr ← BackwardBitReader.init data fseDistEnd rangeEnd
```

This is a critical pattern — the boundary between forward and backward
reading must be tracked precisely.

## Pattern 4: Byte Position Threading

Zstd parsing returns `(result, newPosition)` tuples throughout. The
position threads through nested parsing levels:

```
Frame: pos → [magic, header] → blockPos
  Block: blockPos → [3-byte header] → contentPos
    Literals: contentPos → [lit header] → afterLiterals
    Sequences: afterLiterals → [seq header] → afterSeqHeader
      FSE tables: → afterTables
      Interleaved decode: → (done, position at blockEnd)
```

**Key pattern:** When block size is known, use `blockEnd := pos + blockSize`
as an anchor. Even if inner parsing doesn't consume all bytes, skip to
`blockEnd` after processing:
```lean
off := blockEnd  -- skip to block boundary
```

This prevents position drift from accumulating across blocks.

## Pattern 5: Sequence Execution and Offset History

Sequences combine literal copies with back-reference matches:
```lean
structure ZstdSequence where
  literalLength : Nat    -- bytes to copy from literals
  matchLength : Nat      -- bytes to copy from back-reference
  offset : Nat           -- 1-3: repeat codes; >=4: actual offset - 3
```

**Offset resolution** has dual modes depending on `literalLength`:
- `literalLength > 0`: codes 1-3 are repeat offsets from history
- `literalLength == 0`: codes shift — code 1 means history[1], code 3
  means history[0]-1

History is always exactly 3 entries, initialized to `#[1, 4, 8]`.

**Match copying** must handle overlapping matches (offset < matchLength):
```lean
b.push b[start + (k % offset)]!  -- modular indexing handles overlap
```

**When proving sequence execution:**
- Offset history size invariant: always exactly 3 entries
- Literal position invariant: `litPos` advances by exactly `literalLength`
  per sequence, total equals `literals.size`
- Match validity: `offset <= output.size` at point of copy
- Overlap semantics: modular indexing produces RLE-like expansion

## Pattern 6: Huffman Tree Descriptors

Two encoding modes dispatched by the first byte:
- `headerByte < 128`: **Direct** — `headerByte` = number of weight bytes,
  each byte packs two 4-bit weights (high nibble, low nibble)
- `headerByte >= 128`: **FSE-compressed** — `headerByte - 127` = compressed
  size, uses Pattern 3 (mixed forward/backward reading)

After obtaining weights, both paths:
1. Trim trailing zeros
2. Derive `maxBits` from the weight array
3. Build a flat lookup table of size `2^maxBits`

**Weight-to-code mapping:** ascending weight = longer codes = more table
entries. Weight 0 means "symbol not present". Weight W occupies
`2^(W-1)` table entries.

## Pattern 7: RFC 8878 Constant Validation

Zstd uses many magic constants from the RFC. Validate them at parse-time
with descriptive errors:

```lean
def zstdMagic : UInt32 := 0xFD2FB528

-- Frame header descriptor bit fields
let fcsFlag := (desc >>> 6).toNat           -- bits 7-6
let singleSegment := (desc >>> 5) &&& 1 == 1  -- bit 5
let contentChecksum := (desc >>> 2) &&& 1 == 1 -- bit 2
let didFlag := (desc &&& 3).toNat           -- bits 1-0
```

**Size mapping tables** (RFC 8878 sections reference in comments):
- Dictionary ID size: `didFlag` → 0/1/2/4 bytes
- Frame content size: `fcsFlag` → 0/1/2/4/8 bytes (with single-segment special case)
- Window size: `10 + exponent` log, with mantissa adjustment
- 2-byte FCS has `+256` offset

**Variable-width count encoding** (used for sequence count and literal sizes):
```
byte0 == 0:        0 (no more data)
byte0 < 128:       byte0 (1-byte)
byte0 < 255:       ((byte0 - 128) << 8) + byte1 (2-byte)
byte0 == 255:      byte1 + (byte2 << 8) + 0x7F00 (3-byte)
```

**Extra bits tables** map symbol codes to (baseline, extraBitCount) pairs.
Three separate tables: literal length (36 entries), match length (53 entries),
offset (32 entries). These are pure data — define as `Array (Nat × Nat)`.

## Pattern 8: Predefined FSE Distribution Tables

RFC 8878 defines default probability distributions for literal length,
match length, and offset coding. These are used when `compressionMode =
.predefined` in the sequences header.

Define these as constants and build tables at initialization:
```lean
def defaultLitLenDistribution : Array Int32 := #[4, 3, 2, 2, 2, ...]
def defaultMatchLenDistribution : Array Int32 := #[1, 4, 3, 2, 2, ...]
def defaultOffsetDistribution : Array Int32 := #[1, 1, 1, 1, 1, ...]
```

The accuracy logs for predefined tables are fixed:
- Literal length: 6
- Match length: 6
- Offset: 5

## Implementation Checklist for New Track E Features

When adding a new Zstd parsing feature:

1. **Read the RFC section** — Zstd's format is well-specified but has many
   edge cases (single-segment, 2-byte FCS offset, repeat counts of 3, etc.)
2. **Thread byte positions** — every parser returns `(result, newPosition)`
3. **Use `Except String`** — all parsing is fallible with descriptive errors
4. **Add tests immediately** — test both valid data and error cases
5. **Reuse existing structures** — `BitReader`, `BackwardBitReader`, `FseTable`
   are shared across features
6. **Anchor to block boundaries** — use `blockEnd` to prevent position drift
