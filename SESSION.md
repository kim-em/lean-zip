# Session State

<!-- Overwritten at the end of each work session. -->
<!-- Records current working state for the next session to pick up. -->

## Sorry count: 4

All in `Zip/Spec/InflateCorrect.lean` — staged theorem statements for
future sessions:
- `readBits_toBits` (line 184): multi-bit read correspondence
- `huffTree_decode_correct` (line 196): Huffman decode correspondence
- `inflate_correct` (line 225): main correctness theorem
- `inflate_correct'` (line 237): corollary for position-0 inflate

## Known good commit

`f010cd2` — `lake build && lake exe test` passes

## Completed this session (implementation)

### resolveLZ77 properties (Deflate.lean)

Proved 8 theorems about `resolveLZ77`:
- `resolveLZ77_nil`, `resolveLZ77_endOfBlock`, `resolveLZ77_literal` (@[simp])
- `resolveLZ77_reference_dist_zero`, `resolveLZ77_reference_dist_too_large`
- `resolveLZ77_literals`: compositionality for literal sequences
- `resolveLZ77_literal_cons`, `resolveLZ77_endOfBlock_empty`
- `resolveLZ77_reference_valid`: valid back-reference unfolds correctly
- `resolveLZ77_extends`: successful resolution extends accumulator

### Main correctness theorem structure (InflateCorrect.lean — new file)

Created `Zip/Spec/InflateCorrect.lean` with layered theorem decomposition:
- `Zip.Native.BitReader.toBits`: bridge definition
- `readBit_toBits`: **fully proved** — single bit correspondence
- `readBit_wf`: **fully proved** — readBit preserves bitOff < 8
- `readBits_toBits`: stated (sorry'd) — multi-bit correspondence
- `huffTree_decode_correct`: stated (sorry'd) — Huffman layer
- `inflate_correct`: stated (sorry'd) — main theorem
- `inflate_correct'`: stated (sorry'd) — corollary

### Proved infrastructure lemmas (InflateCorrect.lean)

- `flatMap_drop_mul`: drop n*k from uniform-length flatMap
- `flatMap_cons_drop`: drop within first segment
- `ofFn_drop_head`: List.ofFn element access via drop
- `byteToBits_drop_head`, `bytesToBits_drop_testBit`: bit extraction
- `shift_and_one_eq_testBit`: Nat bit operation correspondence
- `uint32_bit_eq_testBit`: UInt32 → Nat.testBit bridge
- `list_drop_cons_tail`: drop-cons-tail structural lemma

### Key proof techniques discovered

- `UInt32.toNat_inj.mp`: convert UInt32 equality to Nat equality
- `UInt32.toNat_and`, `UInt32.toNat_shiftRight`, `UInt8.toNat_toUInt32`:
  standard decomposition for UInt32 bit operations
- `Nat.testBit` unfolds to `1 &&& m >>> n != 0`; use `Nat.and_comm` +
  `Nat.one_and_eq_mod_two` + `split <;> omega` for the bridge
- `split at h` for case analysis on if-then-else in hypotheses
- `simp only [Zip.Native.BitReader.readBit] at h` then `split at h`
  for unfolding native function definitions

## Next action

Priority order for next implementation session:
1. Prove `readBits_toBits` using `readBit_toBits` + induction on n
2. Start on `huffTree_decode_correct` (most complex layer)
3. If time: prove `inflate_correct'` from `inflate_correct`

## Notes

- Toolchain v4.29.0-rc1 is current
- `bitOff < 8` well-formedness invariant is needed for bitstream proofs;
  initial BitReader at `{ bitOff := 0 }` satisfies it, and `readBit_wf`
  shows it's preserved
- `data[pos]!` vs `data[pos]` resolved by `simp [hpos']`
- `data.data[pos] = data[pos]` is `rfl` for ByteArray
