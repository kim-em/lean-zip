# Current Plan

## Status: In progress

## Session type: implementation

## Goal: Refactor decodeDynamicTrees for provability + prove decodeDynamicTrees_correct

### Background

The `decodeDynamicTrees_correct` theorem is the only remaining sorry (2 occurrences).
It requires proving that the native `decodeDynamicTrees` corresponds to the spec's
`decodeDynamicTables`. Several obstacles prevent direct proof:

1. **`fromLengths` lacks Kraft check**: Can't derive `ValidLengths` from success.
   Fix: add Kraft inequality check alongside existing length validation.

2. **`for`/`while` loops**: `decodeDynamicTrees` uses `for i in [:n]` and
   `while idx < total`, which use `forIn`/well-founded recursion that can't
   be unfolded. Fix: extract into explicit recursive functions (same pattern
   as `inflateLoop` and `copyLoop` from previous sessions).

3. **Native/spec overshoot handling**: When a repeat code would exceed
   `totalCodes`, native truncates silently while spec rejects via guard.
   Fix: add overshoot checks to native (matches zlib behavior and aligns
   with spec).

### Steps

1. [x] Refactor `fromLengths`:
   - Remove `validateLengths` (uses `for` loop, hard to unfold)
   - Inline as `Array.any` check (has clean API lemmas)
   - Add Kraft inequality check
   - Result: `fromLengths` succeeding implies `ValidLengths`

2. [x] Prove `fromLengths_valid`:
   - If `fromLengths lengths maxBits = .ok tree`, then
     `ValidLengths (lengths.toList.map UInt8.toNat) maxBits`

3. [x] Extract loops from `decodeDynamicTrees`:
   - `fillEntries`: fill consecutive array entries (replaces inner for loops)
   - `readCLCodeLengths`: read 3-bit CL code lengths (replaces for loop)
   - `decodeCLSymbols`: decode code lengths using CL tree (replaces while loop)
   - Add overshoot checks to `decodeCLSymbols` for repeat codes
   - Make `codeLengthOrder` public (needed cross-file for proofs)
   - Rewrite `decodeDynamicTrees` using extracted functions

4. [x] Build + test to verify refactoring is correct

5. [ ] Start correspondence proofs (may continue in next session):
   - `readCLCodeLengths_correct`: native ↔ spec `readCLLengths`
   - `decodeCLSymbols_correct`: native ↔ spec `decodeCLSymbols`
   - Wire into `decodeDynamicTrees_correct`

### Rationale for implementation changes

- **Kraft check in `fromLengths`**: Real decoders (zlib) reject oversubscribed
  Huffman codes. Adding this check is a robustness improvement AND enables
  deriving `ValidLengths` in the proof.

- **Overshoot checks**: RFC 1951 §3.2.7 says code lengths "shall not exceed"
  the specified counts. Real decoders reject this. Adding checks aligns native
  with spec behavior.

- **Loop extraction**: Established pattern from `inflateLoop` and `copyLoop`.
  Required for any proof work on the function.
