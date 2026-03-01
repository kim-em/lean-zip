# Track C2: Fuel Usage Audit

## Overview

This document inventories all fuel-based recursion in the spec and native
layers, identifies decreasing measures for well-founded recursion, and
proposes a conversion order.

## Spec Layer (`Zip/Spec/Deflate.lean`)

### 1. `decodeSymbols`

| Field | Value |
|-------|-------|
| **File** | `Zip/Spec/Deflate.lean:186` |
| **Signature** | `decodeSymbols (litLengths distLengths : List Nat) (bits : List Bool) (fuel : Nat := 1e18)` |
| **Bounds** | One Huffman symbol per recursion step |
| **Fuel callees** | None (leaf) |
| **Fuel independence** | `decodeSymbols_fuel_independent` in `DeflateFuelIndep.lean` |
| **Decreasing measure** | `bits.length` — each step calls `decodeLitLen` which consumes ≥1 bit via `Huffman.Spec.decode` |
| **Difficulty** | Medium — need to prove `decodeLitLen` strictly reduces `bits.length` |

### 2. `decodeDynamicTables.decodeCLSymbols`

| Field | Value |
|-------|-------|
| **File** | `Zip/Spec/Deflate.lean:337` (nested `where` in `decodeDynamicTables`) |
| **Signature** | `decodeCLSymbols (clTable) (totalCodes : Nat) (acc : List Nat) (bits : List Bool) : Nat → Option (...)` |
| **Bounds** | One CL symbol per recursion step |
| **Fuel callees** | None (leaf) |
| **Fuel independence** | `decodeCLSymbols_fuel_independent` in `DeflateFuelIndep.lean` |
| **Decreasing measure** | `totalCodes - acc.length` — acc grows by ≥1 per step (sym<16: +1, sym 16: +3..+6, sym 17: +3..+10, sym 18: +11..+74), and `acc.length < totalCodes` is guarded |
| **Difficulty** | Easy — clear bounded counter, guard ensures termination condition |

### 3. `decode.go` / `decode.goR`

| Field | Value |
|-------|-------|
| **File** | `Zip/Spec/Deflate.lean:379` (`go`), `402` (`goR`) |
| **Signature** | `go (bits : List Bool) (acc : List UInt8) : Nat → Option (List UInt8)` |
| **Bounds** | One DEFLATE block per recursion step |
| **Fuel callees** | `decodeSymbols` (uses default fuel, independent), `decodeDynamicTables` (contains `decodeCLSymbols`) |
| **Fuel independence** | `decode_go_fuel_independent` in `DeflateFuelIndep.lean` |
| **Decreasing measure** | `bits.length` — each block consumes ≥3 bits (BFINAL + BTYPE) plus block payload |
| **Difficulty** | Hard — need to show each block type strictly reduces bit length, which depends on `decodeStored`, `decodeSymbols`, and `decodeDynamicTables` all consuming bits |

## Native Layer (`Zip/Native/Inflate.lean`)

### 4. `Inflate.decodeCLSymbols`

| Field | Value |
|-------|-------|
| **File** | `Zip/Native/Inflate.lean:175` |
| **Signature** | `decodeCLSymbols (clTree : HuffTree) (br : BitReader) (codeLengths : Array UInt8) (idx totalCodes : Nat) (fuel : Nat)` |
| **Bounds** | One CL symbol per step |
| **Fuel callees** | None (leaf) |
| **Decreasing measure** | `totalCodes - idx` — idx increases by ≥1 per step |
| **Difficulty** | Easy — same structure as spec version |

### 5. `Inflate.decodeHuffman.go`

| Field | Value |
|-------|-------|
| **File** | `Zip/Native/Inflate.lean:253` |
| **Signature** | `go (br : BitReader) (output : ByteArray) : Nat → Except String (ByteArray × BitReader)` |
| **Bounds** | One symbol per step |
| **Fuel callees** | None (leaf) |
| **Decreasing measure** | `br.remaining` or similar BitReader position — each symbol consumes ≥1 bit |
| **Difficulty** | Medium — need BitReader consumption lemma |

### 6. `Inflate.inflateLoop`

| Field | Value |
|-------|-------|
| **File** | `Zip/Native/Inflate.lean:288` |
| **Signature** | `inflateLoop (br : BitReader) (output : ByteArray) (fixedLit fixedDist : HuffTree) (maxOutputSize : Nat) : Nat → Except String (ByteArray × Nat)` |
| **Bounds** | One block per step |
| **Fuel callees** | `decodeHuffman` (uses default fuel, independent) |
| **Decreasing measure** | `br.remaining` — each block consumes bits |
| **Difficulty** | Hard — same reasons as spec `decode.go` |

### Functions Already Using Well-Founded Recursion (No Fuel)

These native-layer functions already use `termination_by` — no conversion needed:

| Function | File | Measure |
|----------|------|---------|
| `HuffTree.insertLoop` | `Native/Inflate.lean:46` | `lengths.size - start` |
| `fillEntries` | `Native/Inflate.lean:154` | `count` |
| `readCLCodeLengths` | `Native/Inflate.lean:162` | `numCodeLen - i` |
| `copyLoop` | `Native/Inflate.lean:140` | `length - k` |
| `bitsToBytes.go` | `Spec/Deflate.lean:239` | `bits.length` |

## Fuel Flow Graph

```
decode.go ─────┬──▶ decodeSymbols         (independent fuel, leaf)
  │            └──▶ decodeDynamicTables
  │                   └──▶ decodeCLSymbols  (independent fuel, leaf)
  │
decode.goR ────┬──▶ decodeSymbols         (independent fuel, leaf)
               └──▶ decodeDynamicTables
                      └──▶ decodeCLSymbols  (independent fuel, leaf)

inflateLoop ───┬──▶ decodeHuffman.go      (independent fuel, leaf)
               └──▶ decodeDynamicTrees
                      └──▶ decodeCLSymbols  (independent fuel, leaf)
```

Key observation: fuel is **never passed between functions** — each function
has its own independent fuel pool. This means they can be converted
independently.

## Conversion Order

### Phase 1: Leaf functions (independent, no circular dependencies)

**Order within phase doesn't matter — these are independent.**

1. **`decodeDynamicTables.decodeCLSymbols`** (spec) — Easiest. Clear
   bounded counter (`totalCodes - acc.length`). Guards ensure progress.
   Nested `where` clause needs to be lifted to a standalone `def` first.

2. **`Inflate.decodeCLSymbols`** (native) — Same structure as spec version.
   `totalCodes - idx` decreases each step.

3. **`decodeSymbols`** (spec) — Medium. Needs a lemma that
   `decodeLitLen` strictly reduces `bits.length`. The Huffman decode
   always consumes ≥1 bit, and extra-bits fields consume more.

4. **`Inflate.decodeHuffman.go`** (native) — Similar to `decodeSymbols`
   but operates on `BitReader` instead of `List Bool`.

### Phase 2: Block-level functions (depend on Phase 1 for bit-consumption proofs)

5. **`decode.go` / `decode.goR`** (spec) — Needs to show each block type
   (stored, fixed, dynamic) strictly reduces `bits.length`. After Phase 1
   establishes bit-consumption for `decodeSymbols` and `decodeDynamicTables`,
   this becomes tractable.

6. **`Inflate.inflateLoop`** (native) — Same as `decode.go` but for
   `BitReader`.

### Phase 3: Proof updates

After converting the functions, update:
- `DeflateFuelIndep.lean` — fuel independence theorems become trivial
  (or can be removed since fuel no longer exists)
- `DeflateEncode.lean` — roundtrip proofs that mention fuel hypotheses
- `DeflateRoundtrip.lean` — main roundtrip theorem
- `LZ77Lazy.lean` — lazy encoding roundtrip

## Prototype Candidate

**`decodeDynamicTables.decodeCLSymbols`** is the best prototype because:
- Simplest decreasing measure (`totalCodes - acc.length`)
- No dependencies on other fuel functions
- Guard `acc.length ≥ totalCodes` directly provides termination
- Each branch increases `acc.length` by a known positive amount
- Success validates the approach for the rest of the conversion

**Approach**: Lift `decodeCLSymbols` out of the `where` clause into a
standalone `def`, add `termination_by totalCodes - acc.length`, prove
the `decreasing_by` obligations, and verify that all existing proofs
still compile.
