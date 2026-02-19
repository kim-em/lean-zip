# Current Plan

<!-- Rewritten at the start of each work session. -->
<!-- If a session ends with unchecked items, the next session continues here. -->

## Status: Completed (first session)

## Session type: implementation

## Objective

Begin Phase 1: native checksums. Implement Adler32 (spec, native, tests,
proofs) and start CRC32 (spec, native, tests, partial proofs).

## Deliverables

- [x] Create `Zip/Spec/Adler32.lean` — formal spec of Adler32
- [x] Create `Zip/Native/Adler32.lean` — pure Lean implementation
- [x] Create conformance tests: native vs FFI Adler32
- [x] Prove equivalence of native impl to spec (via Array.foldl_toList)
- [x] Create `Zip/Spec/Crc32.lean` — formal spec of CRC32
- [x] Create `Zip/Native/Crc32.lean` — table-driven CRC32
- [x] Create conformance tests: native vs FFI CRC32
- [x] Prove CRC linearity lemma (crcBit_xor_high) via bv_decide
- [ ] Prove `crcByteTable_eq_crcByte` — table equals bit-by-bit spec

## Decision Log

- Used `data.data.foldl` (Array.foldl) instead of `ByteArray.foldl` because
  `Array.foldl_toList` exists but `ByteArray.foldl_eq_foldl_toList` does not.
  This made the equivalence proof straightforward.
- Used `data.data.toList` in theorem statements rather than `data.toList`
  because `ByteArray.toList` has its own loop implementation unrelated to
  `Array.toList`.
- CRC32 linearity proved via `bv_decide` — clean and efficient for BitVec
  reasoning on UInt32.

## Failed Approaches

- Tried `ByteArray.foldl` in native Adler32: no lemma connecting it to
  `List.foldl`, had to switch to `Array.foldl` on `.data`.
- Tried `data.toList` in theorem statements: `ByteArray.toList` uses a
  custom loop, not `data.data.toList`, causing proof friction.
- Tried `simp` to unfold CRC32 table lookup: hit max steps/recursion depth.
- Tried `bv_decide` directly on `crcByteTable_eq_crcByte`: failed because
  `UInt32.ofNat byte.toNat` is abstracted as opaque.

## Notes

### Remaining for crcByteTable_eq_crcByte proof:
The proof strategy is clear:
1. `crcBit_xor_high` (DONE): `a &&& 1 = 0 → crcBit(a ^^^ b) = (a >>> 1) ^^^ crcBit(b)`
2. Iterate 8 times: `a &&& 0xFF = 0 → crcBit^8(a ^^^ b) = (a >>> 8) ^^^ crcBit^8(b)`
3. Split `crc ^^^ byte` into high/low parts
4. Apply step 2 with `a = crc &&& 0xFFFFFF00`
5. Connect table lookup to `crcBit^8` on the low byte

Challenge: step 2 requires unfolding `crcBit8` (an abbreviation) in a way that
lets `rw [crcBit_xor_high]` match. Step 5 requires reducing `Array.ofFn`
lookups. Consider using `decide` or `cbv` for step 5 (256 finite cases).
