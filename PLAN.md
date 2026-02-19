# Current Plan

<!-- Rewritten at the start of each work session. -->
<!-- If a session ends with unchecked items, the next session continues here. -->

## Status: Completed

## Session type: implementation + review

## Objective

Complete the `crcByteTable_eq_crcByte` proof — the remaining sorry in
Phase 1 (Checksums). Then review and clean up.

## Deliverables

- [x] Prove `crcByteTable_eq_crcByte` — table lookup equals bit-by-bit spec
- [x] Review and clean up Phase 1 code
- [x] Update ARCHITECTURE.md

## Proof Strategy (for reference)

The proof of `crcByteTable_eq_crcByte` decomposes into:

1. `crcBits8_split`: `crcBit^8(v) = (v >>> 8) ^^^ crcBit^8(v &&& 0xFF)`
   — proved directly by `bv_decide` after unfolding `crcBit` and `POLY`

2. `xor_byte_shr8`: `(crc ^^^ byte) >>> 8 = crc >>> 8`
   — byte only affects low 8 bits; proved by rewriting to `BitVec.setWidth`
   then `bv_decide`

3. `table_getElem` + `UInt32.ofNat_toNat`: table lookup reduces to
   `crcBit^8((crc ^^^ byte) &&& 0xFF)`

4. Main proof: unfold `crcByteTable`, resolve bounds, apply (3), then
   rewrite with (1) and (2).
