# Track C1: Fuel-Dependent Bounds Audit

## Summary

Only **one file** in the entire Zstd codebase uses fuel: `Zip/Native/Fse.lean`.
It contains **3 fuel-parameterized functions**. All other Zstd native
implementations already use well-founded recursion (`termination_by`).

The Zstd spec files (`Spec/Zstd.lean`, `Spec/ZstdFrame.lean`,
`Spec/ZstdTwoBlock.lean`, `Spec/ZstdBase.lean`, `Spec/ZstdBlockLoop.lean`,
`Spec/ZstdSequence.lean`, `Spec/ZstdHuffman.lean`) contain **zero** fuel
references. Only `Spec/Fse.lean` references fuel — in 8 theorems that
prove properties of the native fuel-based functions via `induction fuel`.

## Fuel-Parameterized Functions

### 1. `decodeZeroRepeats` (Native/Fse.lean:58-69)

```
def decodeZeroRepeats (br : BitReader) (probs : Array Int32)
    (symbolNum : Nat) (maxSymbols : Nat) : Nat →
    Except String (Array Int32 × Nat × BitReader)
```

**Purpose**: Inner loop for zero-repeat sequences in FSE distribution
decoding. Reads 2-bit repeat counts and pushes zeros until repeatCount < 3.

**Recursive structure**: Pattern matches on fuel. Recurses only when
`repeatCount == 3` (read from bitstream).

**Natural decreasing measure**: Bits remaining in the bitstream. Each
iteration consumes exactly 2 bits via `readBits 2`. The loop terminates
when `repeatCount < 3`.

**Conversion difficulty**: **Moderate**. The decreasing measure (`br.data.size * 8 -
br.bitPos`-like quantity) is well-defined but requires proving that
`readBits` strictly advances the bit position. The BitReader invariant
proofs for this already exist in Spec/Fse.lean (see
`decodeZeroRepeats_bitPos_ge` at line 1309).

**Fuel bound**: Called with fuel = 1000 (line 111). Actual iterations
bounded by bitstream length / 2.

### 2. `decodeFseLoop` (Native/Fse.lean:98-122)

```
def decodeFseLoop (br : BitReader) (remaining : Nat) (probs : Array Int32)
    (symbolNum : Nat) (maxSymbols : Nat) : Nat →
    Except String (Nat × Array Int32 × Nat × BitReader)
```

**Purpose**: Main loop for FSE distribution decoding. Processes symbols
one at a time, reading probability values and handling zero-repeat sequences.

**Recursive structure**: Pattern matches on fuel. Three recursive call sites:
- Line 114: After `decodeZeroRepeats` (prob == 0) — `remaining` unchanged,
  `symbolNum` increased by `decodeZeroRepeats`
- Line 116: prob == -1 — `remaining - 1`, `symbolNum + 1`
- Line 122: general case — `remaining - probNat`, `symbolNum + 1`

**Natural decreasing measure**: `remaining + (maxSymbols - symbolNum)`.
On each iteration:
- prob == 0: `symbolNum` increases (via `decodeZeroRepeats` pushing zeros),
  so `maxSymbols - symbolNum` decreases while `remaining` stays same
- prob == -1: `remaining` decreases by 1, `symbolNum` increases by 1
- general: `remaining` decreases by `probNat ≥ 1`, `symbolNum` increases by 1

**Conversion difficulty**: **Moderate-Hard**. The tricky case is prob == 0:
we need to prove that `decodeZeroRepeats` strictly increases `symbolNum`.
The existing `decodeZeroRepeats_cellCount` theorem (Spec/Fse.lean:112)
proves `cellCount probs' - cellCount probs = sym' - sym`, which is
related but not exactly the inequality needed. A new lemma
`decodeZeroRepeats_sym_gt` (sym' > sym on success) would be needed.

**Fuel bound**: Called with fuel = 10000 (line 140). Actual iterations
bounded by `remaining + maxSymbols`.

### 3. `decodeFseSymbolsAll` (Native/Fse.lean:389-434)

```
def decodeFseSymbolsAll (table : FseTable) (br : BackwardBitReader)
    (fuel : Nat := 4096) : Except String (Array UInt8 × BackwardBitReader)
```

**Purpose**: Decode FSE symbols until the backward bitstream is fully
consumed. Used for Huffman weight decoding (RFC 8878 §4.2.1). Uses
interleaved two-state FSE decoding.

**Recursive structure**: Uses `for _ in [:fuel]` loop with `break`
conditions. NOT pattern-matched recursion — uses opaque `forIn` loop.

**Natural decreasing measure**: Bits remaining in `BackwardBitReader`.
Each iteration reads `cell.numBits` bits for state1 and `cell.numBits`
bits for state2. The loop breaks when insufficient bits remain.

**Conversion difficulty**: **Hard**. Two issues:
1. The `for _ in [:fuel]` generates an opaque `loop✝` that cannot be
   unfolded in proofs (per CLAUDE.md guidance).
2. The function uses mutable state (`state1`, `state2`, `br`, `result`)
   which would need to be threaded through explicit recursion.
3. The interleaved two-state decoding makes the recursive structure
   more complex than single-state functions.

**Fuel bound**: Default fuel = 4096. Actual iterations bounded by
`br.totalBitsRemaining / min(cell.numBits)`.

## Theorems Affected by Fuel (in Spec/Fse.lean)

All 8 theorems use `induction fuel generalizing ...` as their proof strategy:

| Line | Theorem | About |
|------|---------|-------|
| 112 | `decodeZeroRepeats_cellCount` | Cell count preservation |
| 138 | `decodeFseLoop_invariant` | remaining + cellCount invariant |
| 236 | `decodeZeroRepeats_probs_ge_neg1` | Probability lower bound |
| 391 | `decodeFseLoop_probs_ge_neg1` | Probability lower bound |
| 1309 | `decodeZeroRepeats_bitPos_ge` (private) | Bit position advances |
| 1337 | `decodeFseLoop_bitPos_ge` (private) | Bit position advances |
| 1434 | `decodeZeroRepeats_pos_le_size` (private) | Buffer bounds |
| 1457 | `decodeFseLoop_pos_le_size` (private) | Buffer bounds |

Plus 1 theorem in Spec/ZstdHuffman.lean (line 1593) about `decodeFseSymbolsAll`.

## Already-Converted Native Functions (for reference)

All other Zstd native recursive functions use `termination_by`:

| File | Function | Measure |
|------|----------|---------|
| ZstdFrame.lean | `decompressBlocksWF` | `data.size - off` |
| ZstdFrame.lean | `decompressZstdWF` | `data.size - pos` |
| ZstdHuffman.lean | `findMaxBitsWF` | `weightSum - power` |
| ZstdHuffman.lean | `fillHuffmanTableInnerWF` | `stride - j` |
| ZstdHuffman.lean | `fillHuffmanTableWF` | `numSymbols - sym` |
| ZstdSequence.lean | `copyBytes` | `count` |
| ZstdSequence.lean | `copyMatch.loop` | `length - k` |

## Conversion Priority

### Priority 1: `decodeZeroRepeats` → WF recursion
- **Difficulty**: Moderate
- **Impact**: Unblocks `decodeFseLoop` conversion (which calls it)
- **Measure**: Bit position in bitstream (advances by 2 each iteration)
- **Existing support**: `decodeZeroRepeats_bitPos_ge` already proves
  the bit position advances

### Priority 2: `decodeFseLoop` → WF recursion
- **Difficulty**: Moderate-Hard
- **Impact**: Eliminates fuel from the main FSE decoding path; simplifies
  all 4 loop-level theorems
- **Measure**: `remaining + (maxSymbols - symbolNum)` or similar composite
- **Prerequisite**: Needs `decodeZeroRepeats` converted first (or at least
  a lemma proving `sym' > sym` on success)

### Priority 3: `decodeFseSymbolsAll` → WF recursion
- **Difficulty**: Hard
- **Impact**: Eliminates the last fuel usage; enables proof reasoning
  about Huffman weight decoding
- **Measure**: Bits remaining in BackwardBitReader
- **Blockers**: Requires refactoring from `for` loop to explicit recursion
  with mutable state threaded through parameters

## Recommendation

Start with Priority 1 (`decodeZeroRepeats`) as an easy win that builds
the pattern. Then tackle Priority 2 (`decodeFseLoop`). Priority 3
(`decodeFseSymbolsAll`) is the hardest and least urgent — it has only
1 spec theorem depending on it and uses a default fuel of 4096 which is
more than sufficient for any real input.
