# Session State

<!-- Overwritten at the end of each work session. -->
<!-- Records current working state for the next session to pick up. -->

## Sorry count: 3

All in `Zip/Spec/InflateCorrect.lean`:
- `readCLCodeLengths_correct` (line ~294): CL reading correspondence
- `decodeCLSymbols_correct` (line ~317): CL symbol decode correspondence
- `decodeDynamicTrees_correct` (line ~339): main dynamic tree theorem

## Known good commit

`770fe1b` — `lake build && lake exe test` succeeds, all tests pass.

## What was accomplished this session

### Implementation: decodeDynamicTrees infrastructure

Refactored native code for proof tractability and proved helper lemmas:

1. **`fromLengths` refactored** (Inflate.lean):
   - Added Kraft inequality check (was missing; needed to derive `ValidLengths`)
   - Replaced `validateLengths` (which used unproof-friendly `for` loop)
   - `fromLengths_valid` theorem: derives `ValidLengths` from `fromLengths` success

2. **Loop extraction** (Inflate.lean):
   - `readCLCodeLengths`: explicit recursion replacing `for` loop
   - `decodeCLSymbols`: explicit fuel-based recursion replacing `while` loop
   - `fillEntries`: helper for repeat codes (16/17/18)
   - Added overshoot checks to align native with spec rejection behavior

3. **Well-formedness/position invariant lemmas** (InflateCorrect.lean):
   - `readCLCodeLengths_wf` / `readCLCodeLengths_pos_inv`
   - `decodeCLSymbols_wf` / `decodeCLSymbols_pos_inv`
   - These required `decode_wf`/`decode_pos_inv` to be made public in DecodeCorrect.lean

4. **Correspondence lemma stubs** (InflateCorrect.lean):
   - `readCLCodeLengths_correct`: native Array-based ↔ spec List-based CL reading
   - `decodeCLSymbols_correct`: native Array-based ↔ spec List-based CL decoding
   - Both are sorry'd; define the right interfaces for `decodeDynamicTrees_correct`

5. **Visibility changes** (Deflate.lean, DecodeCorrect.lean):
   - `readCLLengths`: private → protected (needed for cross-file proofs)
   - `decode_wf`/`decode_pos_inv`: private → public

### Key proof patterns discovered

- `induction hd : numCodeLen - i generalizing ...` needed (not bare `induction
  numCodeLen - i`) to capture the `hd` hypothesis for omega in the zero case
- `simp only [pure, Except.pure] at h` needed to reduce `match pure PUnit.unit with
  | Except.error ... | Except.ok ...` patterns from do-notation guards
- `Array.toList_setIfInBounds` + `List.map_set` for Array.set!/List.set correspondence

## Next action

Priority for next session:

1. **Prove `readCLCodeLengths_correct`**: correspondence between native and spec
   CL code length reading. Needs:
   - `readBits_toBits` for each 3-bit read
   - `Array.toList_setIfInBounds` + `List.map_set` for Array/List correspondence
   - `v.toUInt8.toNat = v.toNat % 256` (which is `rfl`)
   - Bound that readBits 3 produces value < 8 (so % 256 = identity)
   - Show `Inflate.codeLengthOrder = Deflate.Spec.codeLengthOrder`

2. **Prove `decodeCLSymbols_correct`**: correspondence between native and spec
   CL symbol decoding. Needs:
   - `huffTree_decode_correct` (but with maxBits=7 for CL tree, existing
     theorem uses maxBits=15)
   - `fillEntries` ↔ `List.replicate` correspondence
   - Careful tracking of Array idx vs List acc.length

3. **Wire into `decodeDynamicTrees_correct`**: use the two correspondence lemmas
   plus header reads to complete the main theorem.

## Architecture

```
inflate_correct (DONE — depends on decodeDynamicTrees_correct sorry)
  ├── decodeStored_correct (DONE, in DecodeCorrect.lean)
  ├── decodeHuffman_correct (DONE, in DecodeCorrect.lean)
  │   ├── huffTree_decode_correct (DONE)
  │   ├── literal case (DONE)
  │   ├── end-of-block case (DONE)
  │   └── length/distance case (DONE)
  │       └── copyLoop_eq_ofFn (DONE)
  ├── decodeDynamicTrees_correct (sorry — REMAINING WORK)
  │   ├── readCLCodeLengths_correct (sorry)
  │   ├── decodeCLSymbols_correct (sorry)
  │   ├── fromLengths_valid (DONE)
  │   ├── readCLCodeLengths_wf/pos_inv (DONE)
  │   └── decodeCLSymbols_wf/pos_inv (DONE)
  └── inflateLoop_correct (DONE, in InflateCorrect.lean)
```

## Notes

- Toolchain v4.29.0-rc1 is current
- Sorry count increased from 2 to 3 (added 2 intermediate sorries,
  but these decompose the problem into manageable pieces)
- All tests pass
- `huffTree_decode_correct` currently hardcoded for maxBits=15;
  will need a version for maxBits=7 for the CL tree
