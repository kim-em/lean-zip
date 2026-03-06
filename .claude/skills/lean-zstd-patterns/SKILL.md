---
name: lean-zstd-patterns
description: Use when implementing Zstd (RFC 8878) decompression features, including FSE table construction, backward bitstream reading, sequence execution, Huffman decoding, or compression mode parsing. Also use when adding tests for Zstd features.
allowed-tools: Read, Edit, Write, Bash, Glob, Grep
---

# Zstd Implementation Patterns (RFC 8878)

Patterns distilled from 11+ Track E feature sessions implementing the Zstd
decompression pipeline in `Zip/Native/`.

## File Layout

| File | Purpose |
|------|---------|
| `Zip/Native/ZstdFrame.lean` | Frame/block parsing, literals section, sequence header, sequence execution |
| `Zip/Native/ZstdHuffman.lean` | Huffman tree descriptor parsing, weight decoding, symbol decoding |
| `Zip/Native/Fse.lean` | FSE distribution decoding, table construction, backward bitstream, symbol decoding |
| `Zip/Native/XxHash.lean` | XXH64 hash for content checksums |
| `ZipTest/ZstdNativeConformance.lean` | End-to-end conformance matrix (FFI compress + native decompress) |
| `ZipTest/ZstdNativeComponents.lean` | Unit tests for individual Zstd components |
| `ZipTest/ZstdNativeIntegration.lean` | Integration tests for Zstd pipeline |

New Zstd features go in one of these existing files. Only create a new
file if the module is genuinely independent (like XXH64 was).

## Backward Bitstream (MSB-First)

Zstd's ANS coding reads bits **MSB-first** from a backward stream — the
opposite of DEFLATE's LSB-first `BitReader`. Key differences:

| Property | DEFLATE `BitReader` | Zstd `BackwardBitReader` |
|----------|--------------------|-----------------------|
| Bit order | LSB-first | MSB-first |
| Direction | Forward (start→end) | Backward (end→start) |
| Initialization | Position 0 | Find sentinel bit in last byte |
| Sentinel | None | Highest set bit in last byte consumed on init |

### Sentinel Bit Protocol

The last byte of a Zstd bitstream has a sentinel: the highest set bit.
This bit is **consumed during initialization** (not part of data). The
remaining lower bits in that byte are the first bits to read.

```lean
-- BackwardBitReader.init finds sentinel, masks it out
let mask := (1 <<< sentinelPos.toUInt8) - 1
let maskedByte := lastByte &&& mask
```

If the sentinel is bit 0 (byte value 0x01), the entire last byte is
consumed and reading continues from the previous byte.

### MSB-First Reading

Each `readBits n` call reads `n` bits from highest-available down:

```lean
let bitPos := br.bitsRemaining - 1
let bit := (br.currentByte >>> bitPos.toUInt8) &&& 1
let acc' := (acc <<< 1) ||| bit.toUInt32
```

When `bitsRemaining` hits 0, move to the previous byte (`bytePos - 1`).

## FSE Table Construction

Three-phase algorithm (RFC 8878 §4.1.1):

### Phase 1: Distribution Decoding (`decodeFseDistribution`)

- Variable-width encoding: smaller probabilities use fewer bits
- Special value: probability -1 means "less than 1" (occupies exactly 1 cell)
- Probability 0 triggers a run-length encoding of consecutive zero-probability symbols
- Use `Int32` for probabilities to naturally represent -1

**PITFALL — `readProbValue` bit combination order**: The NCount variable-length
encoding reads a short value (bitsNeeded-1 bits) then conditionally an extra bit.
The bits are LSB-first: the first-read bits are the LOW bits, the extra bit is
the HIGH bit. The correct logic is:
- If `rawBits < lowThreshold`: value = rawBits (short path, no extra bit)
- Else read 1 extra bit:
  - If extraBit == 0: value = rawBits (no adjustment)
  - If extraBit == 1: value = rawBits + threshold - lowThreshold

**WRONG**: `combined = rawBits * 2 + extraBit` (puts rawBits in HIGH position).
The reference `FSE_readNCount_body` uses `bitStream & (threshold-1)` for the
short path and `bitStream & (2*threshold-1)` for the long path, with
`if (count >= threshold) count -= max` — which is LSB-first ordering.

### Phase 2: Position Stepping (`buildFseTable`)

```
step = (tableSize >> 1) + (tableSize >> 3) + 3
```

Three passes through the table:
1. Place -1 probability symbols at the **end** of the table
2. Distribute remaining symbols using the stepping algorithm, skipping occupied positions
3. Compute `numBits` and `newState` for each cell based on symbol frequency

**Important**: The stepping algorithm only produces coprime steps for
`tableSize >= 32`. Smaller tables may need special handling.

### buildFseTable State Assignment

Use the reference formula for computing `numBits` and `newState`:
```
nextState = count + stateIdx
numBits = accuracyLog - log2(nextState)
newState = (nextState << numBits) - tableSize
```
This is simpler than the doubleCells/highBit approach and matches the reference.

### Phase 3: Symbol Decoding (`decodeFseSymbolsAll`)

**Two interleaved states** (matching `FSE_decompress1X`):
1. Initialize state1 by reading `accuracyLog` bits, then state2
2. Loop: decode state1 (lookup, emit, read bits, update), then state2
3. Termination is **overflow-based**: when `totalBitsRemaining < cell.numBits`,
   emit the other state's symbol and break. Do NOT break on `br.isFinished`.
4. The `BackwardBitReader` needs `totalBitsRemaining` to detect this condition.

**WRONG**: Single-state decoding or breaking when the bitstream is "finished".
The reference continues reading until an overflow condition, then emits one
final symbol from the alternate state.

## Sequence Execution (Zstd's LZ77 Equivalent)

Zstd sequences are `(literalLength, matchLength, offset)` triples. The
execution engine (`executeSequences`) is Zstd's equivalent of DEFLATE's
`resolveLZ77`/`copyLoop`.

### Repeat Offset History

Zstd maintains a 3-entry offset history `[off1, off2, off3]`. Raw offset
values 1-3 are **repeat offset codes**, not actual offsets:

| `literalLength > 0` | Code 1 | Code 2 | Code 3 |
|---------------------|--------|--------|--------|
| Yes (normal) | `history[0]` (no update) | `history[1]` (rotate) | `history[2]` (rotate) |
| No (shifted) | `history[1]` (rotate) | `history[2]` (rotate) | `history[0] - 1` (replace) |

Raw offset values >= 4 are actual offsets (value - 3).

### Overlapping Match Copy

`copyMatch` must handle the case where `matchLength > offset` (the match
overlaps with bytes being produced). Copy byte-by-byte from the back:

```lean
for i in [:length] do
  let srcIdx := buf.size - offset
  buf := buf.push buf[srcIdx]!
```

This naturally handles overlap because `buf.size` grows with each push.

## Extra Bits Tables (RFC 8878 §3.1.1.3.2.1)

Literal lengths and match lengths use baseline + extra bits encoding.
Tables are defined as constant arrays (`litLenExtraBits`, `matchLenExtraBits`)
following RFC 8878 Table 15 and Table 17.

`parseSequencesHeader` returns `(numSeq, compressionModes, posAfterHeader)`.
When `numSeq == 0`, modes default to `predefined`. The compression modes
are needed by `resolveSequenceFseTables` to construct FSE decode tables.

## Huffman Tree Descriptor

**CRITICAL: Follow the reference implementation, not the RFC text.**
The RFC 8878 §4.2.1 table describes headerByte < 128 as direct and >= 128
as FSE-compressed. The **actual reference zstd implementation** does the
opposite: headerByte >= 128 means direct (numWeights = headerByte - 127),
headerByte < 128 means FSE-compressed (compressedSize = headerByte).
Always match the implementation for interoperability.

Two modes for Huffman weight tables:
- **Direct representation** (headerByte >= 128): numWeights = headerByte - 127,
  weights packed as 4-bit nibbles (high nibble first). The function takes
  `numWeights` (symbol count), NOT `numWeightBytes` (byte count).
  Bytes consumed = `ceil(numWeights / 2)`.
- **FSE-compressed** (headerByte < 128, headerByte > 0): compressedSize = headerByte bytes

For the flat lookup table, use `Array.replicate (1 <<< maxBits) default`
and fill entries. Trim trailing zero weights from packed representation
for odd symbol counts.

## Implementation Idioms

### `Id.run do` for Pure Mutable State

For algorithms with mutable accumulators in non-monadic contexts:

```lean
def processRemaining (acc : UInt64) (data : ByteArray) (off len : Nat) : UInt64 := Id.run do
  let mut h := acc
  let mut pos := off
  -- loop body using h and pos
  return h
```

Used in XXH64 (`processRemaining`) and elsewhere. Avoids wrapping
everything in `IO` or `Except` when no errors are possible.

### `Inhabited` Instead of `Repr` for ByteArray-Containing Structs

`ByteArray` does not derive `Repr`. For structs containing `ByteArray`,
use `Inhabited` for default values:

```lean
structure BackwardBitReader where
  data : ByteArray
  ...
  deriving Inhabited  -- NOT Repr
```

### Inductive Types for Fixed Enumerations

Use inductives rather than numeric encoding for type safety:

```lean
inductive ZstdBlockType where
  | raw | rle | compressed | reserved
  deriving Repr, BEq
```

This gives pattern matching exhaustiveness and prevents invalid values
from propagating silently.

### Compression Mode Enum Pattern

RFC 8878 defines compression modes as 2-bit values. Parse with a
helper function returning the enum:

```lean
inductive SequenceCompressionMode where
  | predefined | rle | fseCompressed | repeat
  deriving Repr, BEq
```

### Error Messages with RFC Section References

Include RFC section numbers in error messages for debugging:

```lean
throw s!"Zstd: accuracy log {accuracyLog} exceeds maximum {maxAccLog}"
throw "Zstd: compressed literals not yet supported"  -- RFC 8878 §3.1.1.3.1
```

## Testing Patterns

### Sequential Test Numbering

Tests in `ZipTest/ZstdFrame.lean` are numbered sequentially (test1,
test2, ... test73+). Continue the sequence when adding new tests.

### FFI Behavior Variability

FFI-compressed data may use compressed blocks even for simple/constant
input. Tests must accept multiple error messages:

```lean
-- Accept either success or "compressed blocks not yet implemented"
match result with
| .ok data => assert (data == expected)
| .error msg => assert (msg.containsSubstr "compressed blocks" || msg.containsSubstr "sequence decoding")
```

### Test With Hardcoded Data

FSE and sequence execution can be tested independently with hardcoded
inputs — no need to wire up the full compression pipeline:

```lean
-- Test sequence execution with known sequences
let seqs := #[{ literalLength := 4, matchLength := 3, offset := 5 }]
let result := executeSequences literals seqs history
```

### Test Vectors from Reference Implementations

For hash functions (XXH64), compute test vectors independently via a
reference implementation (e.g., Python's `xxhash` package) rather than
depending on FFI round-trips.

## Cross-References

- **DEFLATE BitReader**: `Zip/Native/BitReader.lean` (LSB-first, forward)
- **DEFLATE LZ77**: `Zip/Native/Inflate.lean` (`resolveLZ77`, `copyLoop`)
- **RFC 8878**: https://www.rfc-editor.org/rfc/rfc8878
