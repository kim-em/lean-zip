# Session State

<!-- Overwritten at the end of each work session. -->
<!-- Records current working state for the next session to pick up. -->

## Sorry count: 2

All in `Zip/Spec/InflateCorrect.lean`:
- `inflate_correct` (line 126): main correctness theorem
- `inflate_correct'` (line 138): corollary for position-0 inflate

## Known good commit

`c8201d0` — `lake build && lake exe test` passes
(Note: test exe linker error on macOS with v4.29.0-rc1 is pre-existing,
Lean compilation succeeds.)

## Completed this session (review)

### Split InflateCorrect.lean (1282 → 268+833+146)

Split the over-limit file into three files along natural boundaries:

- **`Zip/Spec/BitstreamCorrect.lean`** (268 lines): BitReader ↔ bytesToBits
  correspondence. Contains `toBits`, flatMap helpers, `readBit_toBits`,
  `readBits_toBits`, accumulator arithmetic.

- **`Zip/Spec/HuffmanCorrect.lean`** (833 lines): HuffTree ↔ Huffman.Spec
  correspondence. Contains `decodeBits`, `TreeHasLeaf`, insert proofs,
  `fromLengths_hasLeaf`, `fromLengths_leaf_spec`, `decode_some_mem`.

- **`Zip/Spec/InflateCorrect.lean`** (146 lines): Final connection theorems.
  Contains `decodeBits_eq_spec_decode`, `huffTree_decode_correct`,
  `inflate_correct`, `inflate_correct'`.

### Dead code removal

- Removed `insert_go_complete` (58 lines) — superseded by `insert_go_complete'`
- Fixed unused simp argument `beq_iff_eq` (linter warning)

### Visibility changes

- `private` → `protected` for cross-file access: `decode_go_decodeBits`,
  `decodeBits_of_hasLeaf`, `hasLeaf_of_decodeBits`, `decode_some_mem`,
  `fromLengths_hasLeaf`, `fromLengths_leaf_spec`
- `private` → unqualified: `uint32_testBit` (used by both BitstreamCorrect
  and HuffmanCorrect)
- `insert_bit_zero`/`insert_bit_one` moved from bitstream section to
  HuffmanCorrect (private)

## Next action

Priority order for next implementation session:
1. Prove `inflate_correct'` from `inflate_correct` (straightforward corollary)
2. Make progress on `inflate_correct` — this is the top-level theorem
   connecting `inflateRaw` to `Deflate.Spec.decode`. Requires:
   - Block-level correspondence (stored, fixed, dynamic blocks)
   - Stream-level loop correspondence (multiple blocks → fuel)
   - LZ77 back-reference resolution correspondence

## Notes

- Toolchain v4.29.0-rc1 is current
- Sorry count unchanged at 2
- Pre-existing linker error for test:exe on macOS with v4.29.0-rc1
  (zstd -Bstatic/-Bdynamic flags not recognized by lld on macOS)
