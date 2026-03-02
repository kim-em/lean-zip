---
name: lean-zstd-patterns
description: Use when implementing Zstd (RFC 8878) features in Track E, working with FSE tables, backward bitstreams, Huffman tree descriptors, sequence execution, or any Zstd-specific data structures and algorithms.
allowed-tools: Read, Edit, Bash, Grep, Glob
---

# Zstd (RFC 8878) Implementation Patterns

Patterns specific to the Track E Zstd decompressor in `Zip/Native/`.

## Architecture: Incremental Layered Decompression

The decompressor is built layer by layer, with each layer returning
descriptive errors for unimplemented deeper layers:

```
decompressZstd          → frame dispatch (multi-frame, skippable)
  decompressFrame       → frame header + block loop + checksum
    decompressBlocks    → block header dispatch (raw/RLE/compressed)
      parseLiteralsSection  → raw/RLE/Huffman/treeless literals
      parseSequencesHeader  → count + compression modes
      decodeSequences       → FSE bitstream → ZstdSequence array
      executeSequences      → literal copy + match copy → output
```

Each layer can be tested independently. Tests handle both success and
"not yet implemented" errors gracefully (e.g., test accepts both
checksum mismatch and "compressed blocks not yet supported").

**When adding a new layer**: implement the function, return `throw`
for sub-layers not yet built, add tests that exercise your layer with
inputs that don't hit the unimplemented sub-layers.

## Key Data Structures

### FseCell / FseTable (Fse.lean)

Flat array lookup table for O(1) FSE decoding:

```lean
structure FseCell where
  symbol : UInt16 := 0
  numBits : UInt8 := 0
  newState : UInt16 := 0

structure FseTable where
  accuracyLog : Nat
  cells : Array FseCell  -- size = 1 <<< accuracyLog
```

**Decoding loop**: `state → cells[state] → read numBits bits →
newState + readBits → next state`. The table is pre-computed so
each symbol decode is O(1).

### BackwardBitReader (Fse.lean)

Reads bits MSB-first, right-to-left through bytes. Contrast with
DEFLATE's `BitReader` which reads LSB-first, left-to-right.

```lean
structure BackwardBitReader where
  data : ByteArray
  bytePos : Nat        -- decrements toward 0
  bitsRemaining : Nat   -- 1-8, counts bits left in currentByte
  currentByte : UInt8
```

**Initialization**: Find sentinel bit (highest set bit) in last byte.
Bits below the sentinel are the first data bits. If only the sentinel
bit is set, move to the previous byte.

**Key difference from DEFLATE BitReader**:
- DEFLATE: `pos` increments, `bitOff` counts from LSB
- Zstd: `bytePos` decrements, `bitsRemaining` counts from MSB

### HuffmanEntry / ZstdHuffmanTable (ZstdFrame.lean)

Same flat-array pattern as FSE but simpler (no state machine):

```lean
structure HuffmanEntry where
  symbol : UInt8 := 0
  numBits : UInt8 := 0
```

Table size = `2^maxBits`. Multiple entries per symbol (stride =
`2^(weight-1)`), enabling O(1) lookup by reading maxBits bits and
indexing directly.

### ZstdSequence (ZstdFrame.lean)

```lean
structure ZstdSequence where
  literalLength : Nat
  matchLength : Nat
  offset : Nat  -- raw: 1-3 = repeat codes, >=4 = actual offset - 3
```

## Byte Position Tracking

All parsing functions return `Except String (Result x Nat)` where
the `Nat` is the updated byte position:

```lean
def parseXxx (data : ByteArray) (pos : Nat) :
    Except String (Result x Nat) := do
  if data.size < pos + N then
    throw "Zstd: not enough data for xxx"
  -- ... parsing ...
  return (result, newPos)
```

Each layer tracks its own `pos`/`off`, updates it incrementally, and
passes the returned position as input to the next function call. This
avoids global mutable state and makes each function independently
testable.

## Variable-Width Header Parsing

Zstd uses variable-width encodings extensively. The pattern is
if/else chains on format bits rather than `match` expressions,
because error handling in the `Except` monad works more cleanly
with conditional branches:

```lean
let sizeFormat := ((byte0 >>> 2) &&& 3).toNat
let (regenSize, headerBytes) ←
  if sizeFormat == 0 || sizeFormat == 2 then
    pure ((byte0 >>> 3).toNat, 1)           -- 1-byte header
  else if sizeFormat == 1 then
    pure ((byte0 >>> 4).toNat ||| (byte1.toNat <<< 4), 2)  -- 2-byte
  else
    pure ((byte0 >>> 4).toNat ||| (byte1.toNat <<< 4)
      ||| (byte2.toNat <<< 12), 3)          -- 3-byte
```

This pattern appears in: literals section headers, sequence count
encoding, frame content size, and FSE probability distribution.

## RFC 8878 Constants

### Magic Numbers

```lean
def zstdMagic : UInt32 := 0xFD2FB528
-- Skippable frames: 0x184D2A50 through 0x184D2A5F
```

### Extra Bits Tables (RFC Tables 14-15)

Literal length (36 entries) and match length (53 entries) are
`Array (Nat x Nat)` giving `(baseline, numExtraBits)` pairs:

```lean
def litLenExtraBits : Array (Nat x Nat) := #[
  (0, 0), (1, 0), ..., (15, 0),        -- codes 0-15: direct
  (16, 1), (18, 1), ...,               -- codes 16+: extra bits
  (65536, 16)                           -- code 35: max
]
```

Offset decoding is formula-based: `(1 <<< code) + extraBits`.

### FSE Accuracy Log

Raw value is 4 bits; actual `accuracyLog = rawValue + 5`.
Maximum varies by table type (default 11 for most).

### FSE Probability Distribution Encoding

Probabilities are variable-width with adaptive bit count based on
remaining space. Special values:
- `-1` (as `Int32`): "less than 1" probability, occupies exactly 1 cell
- `0`: symbol not present; triggers repeat-count reading (2-bit chunks,
  repeat while chunk == 3)

### Offset History

Initialized to `[1, 4, 8]` at start of each block. Raw offset codes:
- `1-3`: repeat codes (index into history)
- `>=4`: actual offset = code - 3

When `literalLength == 0`, repeat codes shift: code 1 -> history[1],
code 2 -> history[2], code 3 -> history[0] - 1.

## FSE Table Building Algorithm

The position-stepping algorithm (RFC 8878 Section 4.1):

```
step = (tableSize >>> 1) + (tableSize >>> 3) + 3
position starts at 0
for each symbol with probability > 0:
  place symbol at position
  advance: position = (position + step) % tableSize
  skip positions already occupied by "less than 1" symbols
```

After placement, compute `numBits` and `newState` for each cell
based on the symbol's probability and table size.

**Important**: The step formula is only coprime with `tableSize` for
`accuracyLog >= 5` (tableSize >= 32). Smaller tables need special
handling.

## Overlapping Match Copy

Byte-by-byte copy using modulo indexing allows overlapping matches:

```lean
private def copyMatch (buf : ByteArray) (offset length : Nat) : ByteArray :=
  let start := buf.size - offset
  let rec loop (b : ByteArray) (k : Nat) : ByteArray :=
    if k < length then
      loop (b.push b[start + (k % offset)]!) (k + 1)
    else b
  termination_by length - k
  loop buf 0
```

Same semantics as DEFLATE's `copyLoop` but parameterized differently.

## Checksum Integration

Zstd uses the upper 32 bits of XXH64 (seed 0):

```lean
def xxHash64Upper32 (data : ByteArray) : UInt32 :=
  (xxHash64 data 0 >>> 32).toUInt32
```

The checksum covers the uncompressed content of the entire frame,
verified after all blocks are decompressed.

## Testing Patterns

### Round-trip via FFI

Compress with FFI (`Zstd.compress`), decompress with native code,
compare output. This tests the native implementation against the
reference C implementation.

### Progressive test numbering

Tests are numbered sequentially in `ZipTest/ZstdNative.lean` and
`ZipTest/FseNative.lean`. When adding tests, continue the sequence.

### Graceful incomplete-feature testing

Tests for partially-implemented features accept both success and
the specific "not yet implemented" error string:

```lean
match result with
| .ok bytes => -- verify output
| .error e =>
  if e.containsSubstr "not yet" then pure ()  -- expected
  else throw (IO.userError s!"unexpected error: {e}")
```

## Cross-References

- **DEFLATE BitReader**: `Zip/Native/BitReader.lean` — forward, LSB-first
- **DEFLATE Inflate**: `Zip/Native/Inflate.lean` — comparison architecture
- **RFC 8878**: The canonical Zstd specification
- **`lean-uint-bitvec` skill**: For UInt8/UInt16/UInt32 conversion patterns
  common in byte-level parsing
