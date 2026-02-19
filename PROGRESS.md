# Progress

Session-by-session log for lean-zip development. Most recent first.

## 2026-02-19: Phase 1 complete — CRC-32 table equivalence proved

**Type**: implementation + review
**Phase**: Phase 1 (Checksums) — COMPLETE
**Sorry count**: 1 → 0

**Accomplished**:
- Proved `crcByteTable_eq_crcByte`: table-driven CRC-32 byte update equals
  bit-by-bit specification. This was the last sorry in Phase 1.
- Key technique: `crcBits8_split` lemma (8-fold `crcBit` linearity over
  high/low byte split) proved directly by `bv_decide`, avoiding the need
  to iterate the single-step `crcBit_xor_high` lemma manually
- Helper lemmas for UInt8→UInt32 conversion: rewrite via
  `BitVec.ofNat_toNat` to `BitVec.setWidth`, enabling `bv_decide`
- Updated ARCHITECTURE.md with native implementation and spec sections
- Reviewed all Phase 1 code: clean, no issues found

**Decisions**:
- Proved `crcBits8_split` directly by `bv_decide` instead of iterating
  `crcBit_xor_high` 8 times. The direct approach is simpler and avoids
  intermediate goal management
- Pattern for `UInt32.ofNat byte.toNat` opacity: rewrite to
  `⟨byte.toBitVec.setWidth 32⟩` via `BitVec.ofNat_toNat`, then use
  `show` + `congr 1` to expose `BitVec` for `bv_decide`

**Next**:
- Review session (no reviews done yet)
- Begin Phase 2 (DEFLATE decompressor) per VERIFICATION.md

## 2026-02-19: Phase 1 kickoff — native checksums

**Type**: implementation
**Phase**: Phase 1 (Checksums)
**Sorry count**: 0 → 1

**Accomplished**:
- Created `Zip/Spec/Adler32.lean`: formal Adler-32 spec using `List.foldl`
  with compositionality theorem (`updateList_append`)
- Created `Zip/Native/Adler32.lean`: pure Lean implementation using
  `Array.foldl`, with proved equivalence to spec via `Array.foldl_toList`
- Created `Zip/Spec/Crc32.lean`: formal CRC-32 spec with bit-by-bit
  polynomial definition, lookup table construction, and compositionality
- Created `Zip/Native/Crc32.lean`: table-driven CRC-32, with the key
  linearity lemma proved (`crcBit_xor_high`) via `bv_decide`
- Created `ZipTest/NativeChecksum.lean`: comprehensive conformance tests
  for both native checksums against FFI (known values, large data,
  incremental, empty, single byte)

**Decisions**:
- Use `Array.foldl` on `data.data` instead of `ByteArray.foldl` because
  `Array.foldl_toList` exists in the standard library
- Use `data.data.toList` in theorem statements instead of `data.toList`
  because `ByteArray.toList` has an unrelated loop implementation
- `bv_decide` is effective for UInt32/BitVec reasoning (proved CRC
  linearity in one line)

**Next**:
- Complete `crcByteTable_eq_crcByte` proof (see PLAN.md for strategy)
- Consider Adler32 bounds proofs (state components < MOD_ADLER)
- Continue Phase 1 or do a review session
