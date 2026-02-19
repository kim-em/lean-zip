# Current Plan

<!-- Rewritten at the start of each work session. -->
<!-- If a session ends with unchecked items, the next session continues here. -->

## Status: In progress

## Session type: implementation

## Objective

Complete the `crcByteTable_eq_crcByte` proof — the remaining sorry in
Phase 1 (Checksums). Then review and clean up.

## Deliverables

- [ ] Prove `crcByteTable_eq_crcByte` — table lookup equals bit-by-bit spec
- [ ] Review and clean up Phase 1 code

## Proof Strategy

The goal: `Spec.crcByteTable table crc byte = Spec.crcByte crc byte`

After unfolding, this reduces to:
```
(crc >>> 8) ^^^ crcBits8(UInt32.ofNat ((crc ^^^ byte) &&& 0xFF).toNat)
  = crcBits8(crc ^^^ byte)
```

Approach:
1. Introduce `crcBits8` abbreviation for the 8-fold `crcBit` application
2. Prove iterated linearity via `bv_decide`:
   `a &&& 0xFF = 0 → crcBits8(a ^^^ b) = (a >>> 8) ^^^ crcBits8(b)`
3. Prove bitvector helpers:
   - `UInt32.ofNat (x &&& 0xFF).toNat = x &&& 0xFF`
   - `x = (x &&& 0xFFFFFF00) ^^^ (x &&& 0xFF)` (high/low split)
   - `(x ^^^ y) >>> 8 = x >>> 8` when `y &&& 0xFFFFFF00 = 0`
4. Combine: split `crc ^^^ byte`, apply linearity, simplify

## Failed Approaches (from previous session)

- `bv_decide` directly on `crcByteTable_eq_crcByte`: `UInt32.ofNat byte.toNat` opaque
- `simp` on table lookup: hits max steps
